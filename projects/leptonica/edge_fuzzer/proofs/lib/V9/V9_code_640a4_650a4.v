(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_640ac : bv 32 := 0xfd010113.
Lemma F_640ac : fetch_word Ubsan.M.loaded_segments (0x64104 : word) = Some W_640ac.
Proof. vm_refl. Qed.
Lemma D_640ac : decode_any W_640ac = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640b0 : bv 32 := 0x02113423.
Lemma F_640b0 : fetch_word Ubsan.M.loaded_segments (0x64108 : word) = Some W_640b0.
Proof. vm_refl. Qed.
Lemma D_640b0 : decode_any W_640b0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640b4 : bv 32 := 0x02813023.
Lemma F_640b4 : fetch_word Ubsan.M.loaded_segments (0x6410c : word) = Some W_640b4.
Proof. vm_refl. Qed.
Lemma D_640b4 : decode_any W_640b4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640b8 : bv 32 := 0x00913c23.
Lemma F_640b8 : fetch_word Ubsan.M.loaded_segments (0x64110 : word) = Some W_640b8.
Proof. vm_refl. Qed.
Lemma D_640b8 : decode_any W_640b8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640bc : bv 32 := 0x01213823.
Lemma F_640bc : fetch_word Ubsan.M.loaded_segments (0x64114 : word) = Some W_640bc.
Proof. vm_refl. Qed.
Lemma D_640bc : decode_any W_640bc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640c0 : bv 32 := 0x01313423.
Lemma F_640c0 : fetch_word Ubsan.M.loaded_segments (0x64118 : word) = Some W_640c0.
Proof. vm_refl. Qed.
Lemma D_640c0 : decode_any W_640c0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640c4 : bv 32 := 0x00050413.
Lemma F_640c4 : fetch_word Ubsan.M.loaded_segments (0x6411c : word) = Some W_640c4.
Proof. vm_refl. Qed.
Lemma D_640c4 : decode_any W_640c4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640c8 : bv 32 := 0x08058063.
Lemma F_640c8 : fetch_word Ubsan.M.loaded_segments (0x64120 : word) = Some W_640c8.
Proof. vm_refl. Qed.
Lemma D_640c8 : decode_any W_640c8 = Some (Branch BC_EQ 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640cc : bv 32 := 0x00058493.
Lemma F_640cc : fetch_word Ubsan.M.loaded_segments (0x64124 : word) = Some W_640cc.
Proof. vm_refl. Qed.
Lemma D_640cc : decode_any W_640cc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640d0 : bv 32 := 0x1e858e63.
Lemma F_640d0 : fetch_word Ubsan.M.loaded_segments (0x64128 : word) = Some W_640d0.
Proof. vm_refl. Qed.
Lemma D_640d0 : decode_any W_640d0 = Some (Branch BC_EQ 11 8 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640d4 : bv 32 := 0x0074f513.
Lemma F_640d4 : fetch_word Ubsan.M.loaded_segments (0x6412c : word) = Some W_640d4.
Proof. vm_refl. Qed.
Lemma D_640d4 : decode_any W_640d4 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640d8 : bv 32 := 0x20051a63.
Lemma F_640d8 : fetch_word Ubsan.M.loaded_segments (0x64130 : word) = Some W_640d8.
Proof. vm_refl. Qed.
Lemma D_640d8 : decode_any W_640d8 = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640dc : bv 32 := 0x0104a503.
Lemma F_640dc : fetch_word Ubsan.M.loaded_segments (0x64134 : word) = Some W_640dc.
Proof. vm_refl. Qed.
Lemma D_640dc : decode_any W_640dc = Some (Load SZ4 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640e0 : bv 32 := 0x200005b7.
Lemma F_640e0 : fetch_word Ubsan.M.loaded_segments (0x64138 : word) = Some W_640e0.
Proof. vm_refl. Qed.
Lemma D_640e0 : decode_any W_640e0 = Some (Lui 11 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640e4 : bv 32 := 0x00b505b3.
Lemma F_640e4 : fetch_word Ubsan.M.loaded_segments (0x6413c : word) = Some W_640e4.
Proof. vm_refl. Qed.
Lemma D_640e4 : decode_any W_640e4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640e8 : bv 32 := 0x01e5d59b.
Lemma F_640e8 : fetch_word Ubsan.M.loaded_segments (0x64140 : word) = Some W_640e8.
Proof. vm_refl. Qed.
Lemma D_640e8 : decode_any W_640e8 = Some (ShiftImm32 ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640ec : bv 32 := 0x20059063.
Lemma F_640ec : fetch_word Ubsan.M.loaded_segments (0x64144 : word) = Some W_640ec.
Proof. vm_refl. Qed.
Lemma D_640ec : decode_any W_640ec = Some (Branch BC_NE 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640f0 : bv 32 := 0x0044a583.
Lemma F_640f0 : fetch_word Ubsan.M.loaded_segments (0x64148 : word) = Some W_640f0.
Proof. vm_refl. Qed.
Lemma D_640f0 : decode_any W_640f0 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640f4 : bv 32 := 0x0025151b.
Lemma F_640f4 : fetch_word Ubsan.M.loaded_segments (0x6414c : word) = Some W_640f4.
Proof. vm_refl. Qed.
Lemma D_640f4 : decode_any W_640f4 = Some (ShiftImm32 ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640f8 : bv 32 := 0x02b50933.
Lemma F_640f8 : fetch_word Ubsan.M.loaded_segments (0x64150 : word) = Some W_640f8.
Proof. vm_refl. Qed.
Lemma D_640f8 : decode_any W_640f8 = Some (Mul M_MUL 18 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_640fc : bv 32 := 0x02b5053b.
Lemma F_640fc : fetch_word Ubsan.M.loaded_segments (0x64154 : word) = Some W_640fc.
Proof. vm_refl. Qed.
Lemma D_640fc : decode_any W_640fc = Some (Mul32 M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64100 : bv 32 := 0x1f251663.
Lemma F_64100 : fetch_word Ubsan.M.loaded_segments (0x64158 : word) = Some W_64100.
Proof. vm_refl. Qed.
Lemma D_64100 : decode_any W_64100 = Some (Branch BC_NE 10 18 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64104 : bv 32 := 0x08040463.
Lemma F_64104 : fetch_word Ubsan.M.loaded_segments (0x6415c : word) = Some W_64104.
Proof. vm_refl. Qed.
Lemma D_64104 : decode_any W_64104 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64140 : bv 32 := 0x00000613.
Lemma F_64140 : fetch_word Ubsan.M.loaded_segments (0x64198 : word) = Some W_64140.
Proof. vm_refl. Qed.
Lemma D_64140 : decode_any W_64140 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64144 : bv 32 := 0x02c0006f.
Lemma F_64144 : fetch_word Ubsan.M.loaded_segments (0x6419c : word) = Some W_64144.
Proof. vm_refl. Qed.
Lemma D_64144 : decode_any W_64144 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64170 : bv 32 := 0x02813083.
Lemma F_64170 : fetch_word Ubsan.M.loaded_segments (0x641c8 : word) = Some W_64170.
Proof. vm_refl. Qed.
Lemma D_64170 : decode_any W_64170 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64174 : bv 32 := 0x02013403.
Lemma F_64174 : fetch_word Ubsan.M.loaded_segments (0x641cc : word) = Some W_64174.
Proof. vm_refl. Qed.
Lemma D_64174 : decode_any W_64174 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64178 : bv 32 := 0x01813483.
Lemma F_64178 : fetch_word Ubsan.M.loaded_segments (0x641d0 : word) = Some W_64178.
Proof. vm_refl. Qed.
Lemma D_64178 : decode_any W_64178 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6417c : bv 32 := 0x01013903.
Lemma F_6417c : fetch_word Ubsan.M.loaded_segments (0x641d4 : word) = Some W_6417c.
Proof. vm_refl. Qed.
Lemma D_6417c : decode_any W_6417c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64180 : bv 32 := 0x00813983.
Lemma F_64180 : fetch_word Ubsan.M.loaded_segments (0x641d8 : word) = Some W_64180.
Proof. vm_refl. Qed.
Lemma D_64180 : decode_any W_64180 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64184 : bv 32 := 0x03010113.
Lemma F_64184 : fetch_word Ubsan.M.loaded_segments (0x641dc : word) = Some W_64184.
Proof. vm_refl. Qed.
Lemma D_64184 : decode_any W_64184 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64188 : bv 32 := 0x8b4f906f.
Lemma F_64188 : fetch_word Ubsan.M.loaded_segments (0x641e0 : word) = Some W_64188.
Proof. vm_refl. Qed.
Lemma D_64188 : decode_any W_64188 = Some (Jal 0 2068660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6418c : bv 32 := 0x00048513.
Lemma F_6418c : fetch_word Ubsan.M.loaded_segments (0x641e4 : word) = Some W_6418c.
Proof. vm_refl. Qed.
Lemma D_6418c : decode_any W_6418c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64190 : bv 32 := 0xe90ff0ef.
Lemma F_64190 : fetch_word Ubsan.M.loaded_segments (0x641e8 : word) = Some W_64190.
Proof. vm_refl. Qed.
Lemma D_64190 : decode_any W_64190 = Some (Jal 1 2094736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64194 : bv 32 := 0x06050463.
Lemma F_64194 : fetch_word Ubsan.M.loaded_segments (0x641ec : word) = Some W_64194.
Proof. vm_refl. Qed.
Lemma D_64194 : decode_any W_64194 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64198 : bv 32 := 0x00050413.
Lemma F_64198 : fetch_word Ubsan.M.loaded_segments (0x641f0 : word) = Some W_64198.
Proof. vm_refl. Qed.
Lemma D_64198 : decode_any W_64198 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6419c : bv 32 := 0x00757513.
Lemma F_6419c : fetch_word Ubsan.M.loaded_segments (0x641f4 : word) = Some W_6419c.
Proof. vm_refl. Qed.
Lemma D_6419c : decode_any W_6419c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641a0 : bv 32 := 0x14051663.
Lemma F_641a0 : fetch_word Ubsan.M.loaded_segments (0x641f8 : word) = Some W_641a0.
Proof. vm_refl. Qed.
Lemma D_641a0 : decode_any W_641a0 = Some (Branch BC_NE 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641a4 : bv 32 := 0x01046503.
Lemma F_641a4 : fetch_word Ubsan.M.loaded_segments (0x641fc : word) = Some W_641a4.
Proof. vm_refl. Qed.
Lemma D_641a4 : decode_any W_641a4 = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641a8 : bv 32 := 0x00446583.
Lemma F_641a8 : fetch_word Ubsan.M.loaded_segments (0x64200 : word) = Some W_641a8.
Proof. vm_refl. Qed.
Lemma D_641a8 : decode_any W_641a8 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641ac : bv 32 := 0x00251513.
Lemma F_641ac : fetch_word Ubsan.M.loaded_segments (0x64204 : word) = Some W_641ac.
Proof. vm_refl. Qed.
Lemma D_641ac : decode_any W_641ac = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641b0 : bv 32 := 0x02b516b3.
Lemma F_641b0 : fetch_word Ubsan.M.loaded_segments (0x64208 : word) = Some W_641b0.
Proof. vm_refl. Qed.
Lemma D_641b0 : decode_any W_641b0 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641b4 : bv 32 := 0x02b50633.
Lemma F_641b4 : fetch_word Ubsan.M.loaded_segments (0x6420c : word) = Some W_641b4.
Proof. vm_refl. Qed.
Lemma D_641b4 : decode_any W_641b4 = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641b8 : bv 32 := 0x43f65513.
Lemma F_641b8 : fetch_word Ubsan.M.loaded_segments (0x64210 : word) = Some W_641b8.
Proof. vm_refl. Qed.
Lemma D_641b8 : decode_any W_641b8 = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641bc : bv 32 := 0x12a69863.
Lemma F_641bc : fetch_word Ubsan.M.loaded_segments (0x64214 : word) = Some W_641bc.
Proof. vm_refl. Qed.
Lemma D_641bc : decode_any W_641bc = Some (Branch BC_NE 13 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641c0 : bv 32 := 0x03843503.
Lemma F_641c0 : fetch_word Ubsan.M.loaded_segments (0x64218 : word) = Some W_641c0.
Proof. vm_refl. Qed.
Lemma D_641c0 : decode_any W_641c0 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641c4 : bv 32 := 0x00000593.
Lemma F_641c4 : fetch_word Ubsan.M.loaded_segments (0x6421c : word) = Some W_641c4.
Proof. vm_refl. Qed.
Lemma D_641c4 : decode_any W_641c4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641c8 : bv 32 := 0x5e98c0ef.
Lemma F_641c8 : fetch_word Ubsan.M.loaded_segments (0x64220 : word) = Some W_641c8.
Proof. vm_refl. Qed.
Lemma D_641c8 : decode_any W_641c8 = Some (Jal 1 577000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641cc : bv 32 := 0x00747513.
Lemma F_641cc : fetch_word Ubsan.M.loaded_segments (0x64224 : word) = Some W_641cc.
Proof. vm_refl. Qed.
Lemma D_641cc : decode_any W_641cc = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641d0 : bv 32 := 0x0a050c63.
Lemma F_641d0 : fetch_word Ubsan.M.loaded_segments (0x64228 : word) = Some W_641d0.
Proof. vm_refl. Qed.
Lemma D_641d0 : decode_any W_641d0 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_641fc : bv 32 := 0x00095517.
Lemma F_641fc : fetch_word Ubsan.M.loaded_segments (0x64254 : word) = Some W_641fc.
Proof. vm_refl. Qed.
Lemma D_641fc : decode_any W_641fc = Some (Auipc 10 149, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64200 : bv 32 := 0xecc53983.
Lemma F_64200 : fetch_word Ubsan.M.loaded_segments (0x64258 : word) = Some W_64200.
Proof. vm_refl. Qed.
Lemma D_64200 : decode_any W_64200 = Some (Load SZ8 true 19 10 3788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64204 : bv 32 := 0x0009a503.
Lemma F_64204 : fetch_word Ubsan.M.loaded_segments (0x6425c : word) = Some W_64204.
Proof. vm_refl. Qed.
Lemma D_64204 : decode_any W_64204 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64208 : bv 32 := 0x00600593.
Lemma F_64208 : fetch_word Ubsan.M.loaded_segments (0x64260 : word) = Some W_64208.
Proof. vm_refl. Qed.
Lemma D_64208 : decode_any W_64208 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6420c : bv 32 := 0x0ab55e63.
Lemma F_6420c : fetch_word Ubsan.M.loaded_segments (0x64264 : word) = Some W_6420c.
Proof. vm_refl. Qed.
Lemma D_6420c : decode_any W_6420c = Some (Branch BC_GE 10 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64210 : bv 32 := 0xfffae517.
Lemma F_64210 : fetch_word Ubsan.M.loaded_segments (0x64268 : word) = Some W_64210.
Proof. vm_refl. Qed.
Lemma D_64210 : decode_any W_64210 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64214 : bv 32 := 0xfffb3597.
Lemma F_64214 : fetch_word Ubsan.M.loaded_segments (0x6426c : word) = Some W_64214.
Proof. vm_refl. Qed.
Lemma D_64214 : decode_any W_64214 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64218 : bv 32 := 0xdfa50513.
Lemma F_64218 : fetch_word Ubsan.M.loaded_segments (0x64270 : word) = Some W_64218.
Proof. vm_refl. Qed.
Lemma D_64218 : decode_any W_64218 = Some (OpImm ALU_ADD 10 10 3578, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6421c : bv 32 := 0x7f358593.
Lemma F_6421c : fetch_word Ubsan.M.loaded_segments (0x64274 : word) = Some W_6421c.
Proof. vm_refl. Qed.
Lemma D_6421c : decode_any W_6421c = Some (OpImm ALU_ADD 11 11 2035, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64220 : bv 32 := 0x00000613.
Lemma F_64220 : fetch_word Ubsan.M.loaded_segments (0x64278 : word) = Some W_64220.
Proof. vm_refl. Qed.
Lemma D_64220 : decode_any W_64220 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64224 : bv 32 := 0x818f90ef.
Lemma F_64224 : fetch_word Ubsan.M.loaded_segments (0x6427c : word) = Some W_64224.
Proof. vm_refl. Qed.
Lemma D_64224 : decode_any W_64224 = Some (Jal 1 2068504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64228 : bv 32 := 0x08050063.
Lemma F_64228 : fetch_word Ubsan.M.loaded_segments (0x64280 : word) = Some W_64228.
Proof. vm_refl. Qed.
Lemma D_64228 : decode_any W_64228 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64288 : bv 32 := 0x03843503.
Lemma F_64288 : fetch_word Ubsan.M.loaded_segments (0x642e0 : word) = Some W_64288.
Proof. vm_refl. Qed.
Lemma D_64288 : decode_any W_64288 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6428c : bv 32 := 0x0384b583.
Lemma F_6428c : fetch_word Ubsan.M.loaded_segments (0x642e4 : word) = Some W_6428c.
Proof. vm_refl. Qed.
Lemma D_6428c : decode_any W_6428c = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64290 : bv 32 := 0x00b56633.
Lemma F_64290 : fetch_word Ubsan.M.loaded_segments (0x642e8 : word) = Some W_64290.
Proof. vm_refl. Qed.
Lemma D_64290 : decode_any W_64290 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64294 : bv 32 := 0x00367613.
Lemma F_64294 : fetch_word Ubsan.M.loaded_segments (0x642ec : word) = Some W_64294.
Proof. vm_refl. Qed.
Lemma D_64294 : decode_any W_64294 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64298 : bv 32 := 0x04061a63.
Lemma F_64298 : fetch_word Ubsan.M.loaded_segments (0x642f0 : word) = Some W_64298.
Proof. vm_refl. Qed.
Lemma D_64298 : decode_any W_64298 = Some (Branch BC_NE 12 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6429c : bv 32 := 0x0009061b.
Lemma F_6429c : fetch_word Ubsan.M.loaded_segments (0x642f4 : word) = Some W_6429c.
Proof. vm_refl. Qed.
Lemma D_6429c : decode_any W_6429c = Some (OpImm32 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642a0 : bv 32 := 0x7908c0ef.
Lemma F_642a0 : fetch_word Ubsan.M.loaded_segments (0x642f8 : word) = Some W_642a0.
Proof. vm_refl. Qed.
Lemma D_642a0 : decode_any W_642a0 = Some (Jal 1 575376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642a4 : bv 32 := 0x0280006f.
Lemma F_642a4 : fetch_word Ubsan.M.loaded_segments (0x642fc : word) = Some W_642a4.
Proof. vm_refl. Qed.
Lemma D_642a4 : decode_any W_642a4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642a8 : bv 32 := 0x0009a503.
Lemma F_642a8 : fetch_word Ubsan.M.loaded_segments (0x64300 : word) = Some W_642a8.
Proof. vm_refl. Qed.
Lemma D_642a8 : decode_any W_642a8 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642ac : bv 32 := 0x00500593.
Lemma F_642ac : fetch_word Ubsan.M.loaded_segments (0x64304 : word) = Some W_642ac.
Proof. vm_refl. Qed.
Lemma D_642ac : decode_any W_642ac = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642b0 : bv 32 := 0x00a5cc63.
Lemma F_642b0 : fetch_word Ubsan.M.loaded_segments (0x64308 : word) = Some W_642b0.
Proof. vm_refl. Qed.
Lemma D_642b0 : decode_any W_642b0 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642b4 : bv 32 := 0xfffae517.
Lemma F_642b4 : fetch_word Ubsan.M.loaded_segments (0x6430c : word) = Some W_642b4.
Proof. vm_refl. Qed.
Lemma D_642b4 : decode_any W_642b4 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642b8 : bv 32 := 0xfffb3597.
Lemma F_642b8 : fetch_word Ubsan.M.loaded_segments (0x64310 : word) = Some W_642b8.
Proof. vm_refl. Qed.
Lemma D_642b8 : decode_any W_642b8 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642bc : bv 32 := 0xd5650513.
Lemma F_642bc : fetch_word Ubsan.M.loaded_segments (0x64314 : word) = Some W_642bc.
Proof. vm_refl. Qed.
Lemma D_642bc : decode_any W_642bc = Some (OpImm ALU_ADD 10 10 3414, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642c0 : bv 32 := 0x1c858593.
Lemma F_642c0 : fetch_word Ubsan.M.loaded_segments (0x64318 : word) = Some W_642c0.
Proof. vm_refl. Qed.
Lemma D_642c0 : decode_any W_642c0 = Some (OpImm ALU_ADD 11 11 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642c4 : bv 32 := 0xe7dff06f.
Lemma F_642c4 : fetch_word Ubsan.M.loaded_segments (0x6431c : word) = Some W_642c4.
Proof. vm_refl. Qed.
Lemma D_642c4 : decode_any W_642c4 = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642cc : bv 32 := 0x00040513.
Lemma F_642cc : fetch_word Ubsan.M.loaded_segments (0x64324 : word) = Some W_642cc.
Proof. vm_refl. Qed.
Lemma D_642cc : decode_any W_642cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642d0 : bv 32 := 0x02813083.
Lemma F_642d0 : fetch_word Ubsan.M.loaded_segments (0x64328 : word) = Some W_642d0.
Proof. vm_refl. Qed.
Lemma D_642d0 : decode_any W_642d0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642d4 : bv 32 := 0x02013403.
Lemma F_642d4 : fetch_word Ubsan.M.loaded_segments (0x6432c : word) = Some W_642d4.
Proof. vm_refl. Qed.
Lemma D_642d4 : decode_any W_642d4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642d8 : bv 32 := 0x01813483.
Lemma F_642d8 : fetch_word Ubsan.M.loaded_segments (0x64330 : word) = Some W_642d8.
Proof. vm_refl. Qed.
Lemma D_642d8 : decode_any W_642d8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642dc : bv 32 := 0x01013903.
Lemma F_642dc : fetch_word Ubsan.M.loaded_segments (0x64334 : word) = Some W_642dc.
Proof. vm_refl. Qed.
Lemma D_642dc : decode_any W_642dc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642e0 : bv 32 := 0x00813983.
Lemma F_642e0 : fetch_word Ubsan.M.loaded_segments (0x64338 : word) = Some W_642e0.
Proof. vm_refl. Qed.
Lemma D_642e0 : decode_any W_642e0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642e4 : bv 32 := 0x03010113.
Lemma F_642e4 : fetch_word Ubsan.M.loaded_segments (0x6433c : word) = Some W_642e4.
Proof. vm_refl. Qed.
Lemma D_642e4 : decode_any W_642e4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_642e8 : bv 32 := 0x00008067.
Lemma F_642e8 : fetch_word Ubsan.M.loaded_segments (0x64340 : word) = Some W_642e8.
Proof. vm_refl. Qed.
Lemma D_642e8 : decode_any W_642e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

