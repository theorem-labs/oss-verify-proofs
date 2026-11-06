(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91f9c : bv 32 := 0xf9010113.
Lemma F_91f9c : fetch_word Plain.M.loaded_segments (0x91ff4 : word) = Some W_91f9c.
Proof. vm_refl. Qed.
Lemma D_91f9c : decode_any W_91f9c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fa0 : bv 32 := 0x06113423.
Lemma F_91fa0 : fetch_word Plain.M.loaded_segments (0x91ff8 : word) = Some W_91fa0.
Proof. vm_refl. Qed.
Lemma D_91fa0 : decode_any W_91fa0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fa4 : bv 32 := 0x06813023.
Lemma F_91fa4 : fetch_word Plain.M.loaded_segments (0x91ffc : word) = Some W_91fa4.
Proof. vm_refl. Qed.
Lemma D_91fa4 : decode_any W_91fa4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fa8 : bv 32 := 0x04913c23.
Lemma F_91fa8 : fetch_word Plain.M.loaded_segments (0x92000 : word) = Some W_91fa8.
Proof. vm_refl. Qed.
Lemma D_91fa8 : decode_any W_91fa8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fac : bv 32 := 0x05213823.
Lemma F_91fac : fetch_word Plain.M.loaded_segments (0x92004 : word) = Some W_91fac.
Proof. vm_refl. Qed.
Lemma D_91fac : decode_any W_91fac = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fb0 : bv 32 := 0x05313423.
Lemma F_91fb0 : fetch_word Plain.M.loaded_segments (0x92008 : word) = Some W_91fb0.
Proof. vm_refl. Qed.
Lemma D_91fb0 : decode_any W_91fb0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fb4 : bv 32 := 0x05413023.
Lemma F_91fb4 : fetch_word Plain.M.loaded_segments (0x9200c : word) = Some W_91fb4.
Proof. vm_refl. Qed.
Lemma D_91fb4 : decode_any W_91fb4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fb8 : bv 32 := 0x00050413.
Lemma F_91fb8 : fetch_word Plain.M.loaded_segments (0x92010 : word) = Some W_91fb8.
Proof. vm_refl. Qed.
Lemma D_91fb8 : decode_any W_91fb8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fbc : bv 32 := 0x02013023.
Lemma F_91fbc : fetch_word Plain.M.loaded_segments (0x92014 : word) = Some W_91fbc.
Proof. vm_refl. Qed.
Lemma D_91fbc : decode_any W_91fbc = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc0 : bv 32 := 0x00013c23.
Lemma F_91fc0 : fetch_word Plain.M.loaded_segments (0x92018 : word) = Some W_91fc0.
Proof. vm_refl. Qed.
Lemma D_91fc0 : decode_any W_91fc0 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc4 : bv 32 := 0x00013823.
Lemma F_91fc4 : fetch_word Plain.M.loaded_segments (0x9201c : word) = Some W_91fc4.
Proof. vm_refl. Qed.
Lemma D_91fc4 : decode_any W_91fc4 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc8 : bv 32 := 0x00013423.
Lemma F_91fc8 : fetch_word Plain.M.loaded_segments (0x92020 : word) = Some W_91fc8.
Proof. vm_refl. Qed.
Lemma D_91fc8 : decode_any W_91fc8 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fcc : bv 32 := 0x04058e63.
Lemma F_91fcc : fetch_word Plain.M.loaded_segments (0x92024 : word) = Some W_91fcc.
Proof. vm_refl. Qed.
Lemma D_91fcc : decode_any W_91fcc = Some (Branch BC_EQ 11 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fd0 : bv 32 := 0x00068993.
Lemma F_91fd0 : fetch_word Plain.M.loaded_segments (0x92028 : word) = Some W_91fd0.
Proof. vm_refl. Qed.
Lemma D_91fd0 : decode_any W_91fd0 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fd4 : bv 32 := 0x00060913.
Lemma F_91fd4 : fetch_word Plain.M.loaded_segments (0x9202c : word) = Some W_91fd4.
Proof. vm_refl. Qed.
Lemma D_91fd4 : decode_any W_91fd4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fd8 : bv 32 := 0x00058a13.
Lemma F_91fd8 : fetch_word Plain.M.loaded_segments (0x92030 : word) = Some W_91fd8.
Proof. vm_refl. Qed.
Lemma D_91fd8 : decode_any W_91fd8 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fdc : bv 32 := 0x00058513.
Lemma F_91fdc : fetch_word Plain.M.loaded_segments (0x92034 : word) = Some W_91fdc.
Proof. vm_refl. Qed.
Lemma D_91fdc : decode_any W_91fdc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fe0 : bv 32 := 0x949db0ef.
Lemma F_91fe0 : fetch_word Plain.M.loaded_segments (0x92038 : word) = Some W_91fe0.
Proof. vm_refl. Qed.
Lemma D_91fe0 : decode_any W_91fe0 = Some (Jal 1 1947976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fe4 : bv 32 := 0x00100593.
Lemma F_91fe4 : fetch_word Plain.M.loaded_segments (0x9203c : word) = Some W_91fe4.
Proof. vm_refl. Qed.
Lemma D_91fe4 : decode_any W_91fe4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fe8 : bv 32 := 0x06b51463.
Lemma F_91fe8 : fetch_word Plain.M.loaded_segments (0x92040 : word) = Some W_91fe8.
Proof. vm_refl. Qed.
Lemma D_91fe8 : decode_any W_91fe8 = Some (Branch BC_NE 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fec : bv 32 := 0x09205663.
Lemma F_91fec : fetch_word Plain.M.loaded_segments (0x92044 : word) = Some W_91fec.
Proof. vm_refl. Qed.
Lemma D_91fec : decode_any W_91fec = Some (Branch BC_GE 0 18 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91ff0 : bv 32 := 0x09305463.
Lemma F_91ff0 : fetch_word Plain.M.loaded_segments (0x92048 : word) = Some W_91ff0.
Proof. vm_refl. Qed.
Lemma D_91ff0 : decode_any W_91ff0 = Some (Branch BC_GE 0 19 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91ff4 : bv 32 := 0x00100513.
Lemma F_91ff4 : fetch_word Plain.M.loaded_segments (0x9204c : word) = Some W_91ff4.
Proof. vm_refl. Qed.
Lemma D_91ff4 : decode_any W_91ff4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91ff8 : bv 32 := 0x0ca91463.
Lemma F_91ff8 : fetch_word Plain.M.loaded_segments (0x92050 : word) = Some W_91ff8.
Proof. vm_refl. Qed.
Lemma D_91ff8 : decode_any W_91ff8 = Some (Branch BC_NE 18 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91ffc : bv 32 := 0x0ca99263.
Lemma F_91ffc : fetch_word Plain.M.loaded_segments (0x92054 : word) = Some W_91ffc.
Proof. vm_refl. Qed.
Lemma D_91ffc : decode_any W_91ffc = Some (Branch BC_NE 19 10 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920c0 : bv 32 := 0x00081517.
Lemma F_920c0 : fetch_word Plain.M.loaded_segments (0x92118 : word) = Some W_920c0.
Proof. vm_refl. Qed.
Lemma D_920c0 : decode_any W_920c0 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920c4 : bv 32 := 0x6d052503.
Lemma F_920c4 : fetch_word Plain.M.loaded_segments (0x9211c : word) = Some W_920c4.
Proof. vm_refl. Qed.
Lemma D_920c4 : decode_any W_920c4 = Some (Load SZ4 true 10 10 1744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920c8 : bv 32 := 0x0c050663.
Lemma F_920c8 : fetch_word Plain.M.loaded_segments (0x92120 : word) = Some W_920c8.
Proof. vm_refl. Qed.
Lemma D_920c8 : decode_any W_920c8 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920cc : bv 32 := 0x00200493.
Lemma F_920cc : fetch_word Plain.M.loaded_segments (0x92124 : word) = Some W_920cc.
Proof. vm_refl. Qed.
Lemma D_920cc : decode_any W_920cc = Some (OpImm ALU_ADD 9 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920d0 : bv 32 := 0x04996a63.
Lemma F_920d0 : fetch_word Plain.M.loaded_segments (0x92128 : word) = Some W_920d0.
Proof. vm_refl. Qed.
Lemma D_920d0 : decode_any W_920d0 = Some (Branch BC_LTU 18 9 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920d4 : bv 32 := 0x00100593.
Lemma F_920d4 : fetch_word Plain.M.loaded_segments (0x9212c : word) = Some W_920d4.
Proof. vm_refl. Qed.
Lemma D_920d4 : decode_any W_920d4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920d8 : bv 32 := 0x02010613.
Lemma F_920d8 : fetch_word Plain.M.loaded_segments (0x92130 : word) = Some W_920d8.
Proof. vm_refl. Qed.
Lemma D_920d8 : decode_any W_920d8 = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920dc : bv 32 := 0x01810693.
Lemma F_920dc : fetch_word Plain.M.loaded_segments (0x92134 : word) = Some W_920dc.
Proof. vm_refl. Qed.
Lemma D_920dc : decode_any W_920dc = Some (OpImm ALU_ADD 13 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920e0 : bv 32 := 0x00090513.
Lemma F_920e0 : fetch_word Plain.M.loaded_segments (0x92138 : word) = Some W_920e0.
Proof. vm_refl. Qed.
Lemma D_920e0 : decode_any W_920e0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920e4 : bv 32 := 0xde1fe0ef.
Lemma F_920e4 : fetch_word Plain.M.loaded_segments (0x9213c : word) = Some W_920e4.
Proof. vm_refl. Qed.
Lemma D_920e4 : decode_any W_920e4 = Some (Jal 1 2092512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_920e8 : bv 32 := 0x02050e63.
Lemma F_920e8 : fetch_word Plain.M.loaded_segments (0x92140 : word) = Some W_920e8.
Proof. vm_refl. Qed.
Lemma D_920e8 : decode_any W_920e8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92124 : bv 32 := 0x0a99e063.
Lemma F_92124 : fetch_word Plain.M.loaded_segments (0x9217c : word) = Some W_92124.
Proof. vm_refl. Qed.
Lemma D_92124 : decode_any W_92124 = Some (Branch BC_LTU 19 9 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92128 : bv 32 := 0x00200593.
Lemma F_92128 : fetch_word Plain.M.loaded_segments (0x92180 : word) = Some W_92128.
Proof. vm_refl. Qed.
Lemma D_92128 : decode_any W_92128 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9212c : bv 32 := 0x01010613.
Lemma F_9212c : fetch_word Plain.M.loaded_segments (0x92184 : word) = Some W_9212c.
Proof. vm_refl. Qed.
Lemma D_9212c : decode_any W_9212c = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92130 : bv 32 := 0x00810693.
Lemma F_92130 : fetch_word Plain.M.loaded_segments (0x92188 : word) = Some W_92130.
Proof. vm_refl. Qed.
Lemma D_92130 : decode_any W_92130 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92134 : bv 32 := 0x00098513.
Lemma F_92134 : fetch_word Plain.M.loaded_segments (0x9218c : word) = Some W_92134.
Proof. vm_refl. Qed.
Lemma D_92134 : decode_any W_92134 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92138 : bv 32 := 0xd8dfe0ef.
Lemma F_92138 : fetch_word Plain.M.loaded_segments (0x92190 : word) = Some W_92138.
Proof. vm_refl. Qed.
Lemma D_92138 : decode_any W_92138 = Some (Jal 1 2092428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9213c : bv 32 := 0x08050463.
Lemma F_9213c : fetch_word Plain.M.loaded_segments (0x92194 : word) = Some W_9213c.
Proof. vm_refl. Qed.
Lemma D_9213c : decode_any W_9213c = Some (Branch BC_EQ 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921c4 : bv 32 := 0x0019551b.
Lemma F_921c4 : fetch_word Plain.M.loaded_segments (0x9221c : word) = Some W_921c4.
Proof. vm_refl. Qed.
Lemma D_921c4 : decode_any W_921c4 = Some (ShiftImm32 ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921c8 : bv 32 := 0x0019d59b.
Lemma F_921c8 : fetch_word Plain.M.loaded_segments (0x92220 : word) = Some W_921c8.
Proof. vm_refl. Qed.
Lemma D_921c8 : decode_any W_921c8 = Some (ShiftImm32 ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921cc : bv 32 := 0x00a5e463.
Lemma F_921cc : fetch_word Plain.M.loaded_segments (0x92224 : word) = Some W_921cc.
Proof. vm_refl. Qed.
Lemma D_921cc : decode_any W_921cc = Some (Branch BC_LTU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921d0 : bv 32 := 0x00058513.
Lemma F_921d0 : fetch_word Plain.M.loaded_segments (0x92228 : word) = Some W_921d0.
Proof. vm_refl. Qed.
Lemma D_921d0 : decode_any W_921d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921d4 : bv 32 := 0x01f50513.
Lemma F_921d4 : fetch_word Plain.M.loaded_segments (0x9222c : word) = Some W_921d4.
Proof. vm_refl. Qed.
Lemma D_921d4 : decode_any W_921d4 = Some (OpImm ALU_ADD 10 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921d8 : bv 32 := 0x800005b7.
Lemma F_921d8 : fetch_word Plain.M.loaded_segments (0x92230 : word) = Some W_921d8.
Proof. vm_refl. Qed.
Lemma D_921d8 : decode_any W_921d8 = Some (Lui 11 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921dc : bv 32 := 0xfe05859b.
Lemma F_921dc : fetch_word Plain.M.loaded_segments (0x92234 : word) = Some W_921dc.
Proof. vm_refl. Qed.
Lemma D_921dc : decode_any W_921dc = Some (OpImm32 11 11 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921e0 : bv 32 := 0x00b574b3.
Lemma F_921e0 : fetch_word Plain.M.loaded_segments (0x92238 : word) = Some W_921e0.
Proof. vm_refl. Qed.
Lemma D_921e0 : decode_any W_921e0 = Some (Op ALU_AND 9 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921e4 : bv 32 := 0x000a0513.
Lemma F_921e4 : fetch_word Plain.M.loaded_segments (0x9223c : word) = Some W_921e4.
Proof. vm_refl. Qed.
Lemma D_921e4 : decode_any W_921e4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921e8 : bv 32 := 0x00048593.
Lemma F_921e8 : fetch_word Plain.M.loaded_segments (0x92240 : word) = Some W_921e8.
Proof. vm_refl. Qed.
Lemma D_921e8 : decode_any W_921e8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921ec : bv 32 := 0x00000613.
Lemma F_921ec : fetch_word Plain.M.loaded_segments (0x92244 : word) = Some W_921ec.
Proof. vm_refl. Qed.
Lemma D_921ec : decode_any W_921ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921f0 : bv 32 := 0xe75dc0ef.
Lemma F_921f0 : fetch_word Plain.M.loaded_segments (0x92248 : word) = Some W_921f0.
Proof. vm_refl. Qed.
Lemma D_921f0 : decode_any W_921f0 = Some (Jal 1 1953396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921f4 : bv 32 := 0x00050593.
Lemma F_921f4 : fetch_word Plain.M.loaded_segments (0x9224c : word) = Some W_921f4.
Proof. vm_refl. Qed.
Lemma D_921f4 : decode_any W_921f4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921f8 : bv 32 := 0x00100513.
Lemma F_921f8 : fetch_word Plain.M.loaded_segments (0x92250 : word) = Some W_921f8.
Proof. vm_refl. Qed.
Lemma D_921f8 : decode_any W_921f8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_921fc : bv 32 := 0x02b13c23.
Lemma F_921fc : fetch_word Plain.M.loaded_segments (0x92254 : word) = Some W_921fc.
Proof. vm_refl. Qed.
Lemma D_921fc : decode_any W_921fc = Some (Store SZ8 2 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92200 : bv 32 := 0x04a99463.
Lemma F_92200 : fetch_word Plain.M.loaded_segments (0x92258 : word) = Some W_92200.
Proof. vm_refl. Qed.
Lemma D_92200 : decode_any W_92200 = Some (Branch BC_NE 19 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92204 : bv 32 := 0x02013603.
Lemma F_92204 : fetch_word Plain.M.loaded_segments (0x9225c : word) = Some W_92204.
Proof. vm_refl. Qed.
Lemma D_92204 : decode_any W_92204 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92208 : bv 32 := 0x00000513.
Lemma F_92208 : fetch_word Plain.M.loaded_segments (0x92260 : word) = Some W_92208.
Proof. vm_refl. Qed.
Lemma D_92208 : decode_any W_92208 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9220c : bv 32 := 0xaccfd0ef.
Lemma F_9220c : fetch_word Plain.M.loaded_segments (0x92264 : word) = Some W_9220c.
Proof. vm_refl. Qed.
Lemma D_9220c : decode_any W_9220c = Some (Jal 1 2085580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92210 : bv 32 := 0x01813603.
Lemma F_92210 : fetch_word Plain.M.loaded_segments (0x92268 : word) = Some W_92210.
Proof. vm_refl. Qed.
Lemma D_92210 : decode_any W_92210 = Some (Load SZ8 true 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92214 : bv 32 := 0x00050993.
Lemma F_92214 : fetch_word Plain.M.loaded_segments (0x9226c : word) = Some W_92214.
Proof. vm_refl. Qed.
Lemma D_92214 : decode_any W_92214 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92218 : bv 32 := 0x02a13823.
Lemma F_92218 : fetch_word Plain.M.loaded_segments (0x92270 : word) = Some W_92218.
Proof. vm_refl. Qed.
Lemma D_92218 : decode_any W_92218 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9221c : bv 32 := 0x00000513.
Lemma F_9221c : fetch_word Plain.M.loaded_segments (0x92274 : word) = Some W_9221c.
Proof. vm_refl. Qed.
Lemma D_9221c : decode_any W_9221c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92220 : bv 32 := 0x00098593.
Lemma F_92220 : fetch_word Plain.M.loaded_segments (0x92278 : word) = Some W_92220.
Proof. vm_refl. Qed.
Lemma D_92220 : decode_any W_92220 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92224 : bv 32 := 0xab4fd0ef.
Lemma F_92224 : fetch_word Plain.M.loaded_segments (0x9227c : word) = Some W_92224.
Proof. vm_refl. Qed.
Lemma D_92224 : decode_any W_92224 = Some (Jal 1 2085556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92228 : bv 32 := 0x02013603.
Lemma F_92228 : fetch_word Plain.M.loaded_segments (0x92280 : word) = Some W_92228.
Proof. vm_refl. Qed.
Lemma D_92228 : decode_any W_92228 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9222c : bv 32 := 0x00050913.
Lemma F_9222c : fetch_word Plain.M.loaded_segments (0x92284 : word) = Some W_9222c.
Proof. vm_refl. Qed.
Lemma D_9222c : decode_any W_9222c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92230 : bv 32 := 0x02a13423.
Lemma F_92230 : fetch_word Plain.M.loaded_segments (0x92288 : word) = Some W_92230.
Proof. vm_refl. Qed.
Lemma D_92230 : decode_any W_92230 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92234 : bv 32 := 0x00098513.
Lemma F_92234 : fetch_word Plain.M.loaded_segments (0x9228c : word) = Some W_92234.
Proof. vm_refl. Qed.
Lemma D_92234 : decode_any W_92234 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92238 : bv 32 := 0x00090593.
Lemma F_92238 : fetch_word Plain.M.loaded_segments (0x92290 : word) = Some W_92238.
Proof. vm_refl. Qed.
Lemma D_92238 : decode_any W_92238 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9223c : bv 32 := 0xe34fd0ef.
Lemma F_9223c : fetch_word Plain.M.loaded_segments (0x92294 : word) = Some W_9223c.
Proof. vm_refl. Qed.
Lemma D_9223c : decode_any W_9223c = Some (Jal 1 2086452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92240 : bv 32 := 0x01813603.
Lemma F_92240 : fetch_word Plain.M.loaded_segments (0x92298 : word) = Some W_92240.
Proof. vm_refl. Qed.
Lemma D_92240 : decode_any W_92240 = Some (Load SZ8 true 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92244 : bv 32 := 0x0bc0006f.
Lemma F_92244 : fetch_word Plain.M.loaded_segments (0x9229c : word) = Some W_92244.
Proof. vm_refl. Qed.
Lemma D_92244 : decode_any W_92244 = Some (Jal 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92248 : bv 32 := 0x02a91c63.
Lemma F_92248 : fetch_word Plain.M.loaded_segments (0x922a0 : word) = Some W_92248.
Proof. vm_refl. Qed.
Lemma D_92248 : decode_any W_92248 = Some (Branch BC_NE 18 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9224c : bv 32 := 0x01013603.
Lemma F_9224c : fetch_word Plain.M.loaded_segments (0x922a4 : word) = Some W_9224c.
Proof. vm_refl. Qed.
Lemma D_9224c : decode_any W_9224c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92250 : bv 32 := 0x00000513.
Lemma F_92250 : fetch_word Plain.M.loaded_segments (0x922a8 : word) = Some W_92250.
Proof. vm_refl. Qed.
Lemma D_92250 : decode_any W_92250 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92254 : bv 32 := 0xa84fd0ef.
Lemma F_92254 : fetch_word Plain.M.loaded_segments (0x922ac : word) = Some W_92254.
Proof. vm_refl. Qed.
Lemma D_92254 : decode_any W_92254 = Some (Jal 1 2085508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92258 : bv 32 := 0x00813603.
Lemma F_92258 : fetch_word Plain.M.loaded_segments (0x922b0 : word) = Some W_92258.
Proof. vm_refl. Qed.
Lemma D_92258 : decode_any W_92258 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9225c : bv 32 := 0x00050993.
Lemma F_9225c : fetch_word Plain.M.loaded_segments (0x922b4 : word) = Some W_9225c.
Proof. vm_refl. Qed.
Lemma D_9225c : decode_any W_9225c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92260 : bv 32 := 0x02a13823.
Lemma F_92260 : fetch_word Plain.M.loaded_segments (0x922b8 : word) = Some W_92260.
Proof. vm_refl. Qed.
Lemma D_92260 : decode_any W_92260 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92264 : bv 32 := 0x00000513.
Lemma F_92264 : fetch_word Plain.M.loaded_segments (0x922bc : word) = Some W_92264.
Proof. vm_refl. Qed.
Lemma D_92264 : decode_any W_92264 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92268 : bv 32 := 0x00098593.
Lemma F_92268 : fetch_word Plain.M.loaded_segments (0x922c0 : word) = Some W_92268.
Proof. vm_refl. Qed.
Lemma D_92268 : decode_any W_92268 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9226c : bv 32 := 0xa6cfd0ef.
Lemma F_9226c : fetch_word Plain.M.loaded_segments (0x922c4 : word) = Some W_9226c.
Proof. vm_refl. Qed.
Lemma D_9226c : decode_any W_9226c = Some (Jal 1 2085484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92270 : bv 32 := 0x01013603.
Lemma F_92270 : fetch_word Plain.M.loaded_segments (0x922c8 : word) = Some W_92270.
Proof. vm_refl. Qed.
Lemma D_92270 : decode_any W_92270 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92274 : bv 32 := 0x00050913.
Lemma F_92274 : fetch_word Plain.M.loaded_segments (0x922cc : word) = Some W_92274.
Proof. vm_refl. Qed.
Lemma D_92274 : decode_any W_92274 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92278 : bv 32 := 0x02a13423.
Lemma F_92278 : fetch_word Plain.M.loaded_segments (0x922d0 : word) = Some W_92278.
Proof. vm_refl. Qed.
Lemma D_92278 : decode_any W_92278 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9227c : bv 32 := 0x0740006f.
Lemma F_9227c : fetch_word Plain.M.loaded_segments (0x922d4 : word) = Some W_9227c.
Proof. vm_refl. Qed.
Lemma D_9227c : decode_any W_9227c = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_922f0 : bv 32 := 0x00098513.
Lemma F_922f0 : fetch_word Plain.M.loaded_segments (0x92348 : word) = Some W_922f0.
Proof. vm_refl. Qed.
Lemma D_922f0 : decode_any W_922f0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_922f4 : bv 32 := 0x00090593.
Lemma F_922f4 : fetch_word Plain.M.loaded_segments (0x9234c : word) = Some W_922f4.
Proof. vm_refl. Qed.
Lemma D_922f4 : decode_any W_922f4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_922f8 : bv 32 := 0xd78fd0ef.
Lemma F_922f8 : fetch_word Plain.M.loaded_segments (0x92350 : word) = Some W_922f8.
Proof. vm_refl. Qed.
Lemma D_922f8 : decode_any W_922f8 = Some (Jal 1 2086264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_922fc : bv 32 := 0x00813603.
Lemma F_922fc : fetch_word Plain.M.loaded_segments (0x92354 : word) = Some W_922fc.
Proof. vm_refl. Qed.
Lemma D_922fc : decode_any W_922fc = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92300 : bv 32 := 0x00090513.
Lemma F_92300 : fetch_word Plain.M.loaded_segments (0x92358 : word) = Some W_92300.
Proof. vm_refl. Qed.
Lemma D_92300 : decode_any W_92300 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92304 : bv 32 := 0x00098593.
Lemma F_92304 : fetch_word Plain.M.loaded_segments (0x9235c : word) = Some W_92304.
Proof. vm_refl. Qed.
Lemma D_92304 : decode_any W_92304 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92308 : bv 32 := 0xd68fd0ef.
Lemma F_92308 : fetch_word Plain.M.loaded_segments (0x92360 : word) = Some W_92308.
Proof. vm_refl. Qed.
Lemma D_92308 : decode_any W_92308 = Some (Jal 1 2086248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9230c : bv 32 := 0x03010513.
Lemma F_9230c : fetch_word Plain.M.loaded_segments (0x92364 : word) = Some W_9230c.
Proof. vm_refl. Qed.
Lemma D_9230c : decode_any W_9230c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92310 : bv 32 := 0xfd4da0ef.
Lemma F_92310 : fetch_word Plain.M.loaded_segments (0x92368 : word) = Some W_92310.
Proof. vm_refl. Qed.
Lemma D_92310 : decode_any W_92310 = Some (Jal 1 1943508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92314 : bv 32 := 0x00090513.
Lemma F_92314 : fetch_word Plain.M.loaded_segments (0x9236c : word) = Some W_92314.
Proof. vm_refl. Qed.
Lemma D_92314 : decode_any W_92314 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92318 : bv 32 := 0x00048593.
Lemma F_92318 : fetch_word Plain.M.loaded_segments (0x92370 : word) = Some W_92318.
Proof. vm_refl. Qed.
Lemma D_92318 : decode_any W_92318 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9231c : bv 32 := 0x858dd0ef.
Lemma F_9231c : fetch_word Plain.M.loaded_segments (0x92374 : word) = Some W_9231c.
Proof. vm_refl. Qed.
Lemma D_9231c : decode_any W_9231c = Some (Jal 1 1953880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92320 : bv 32 := 0x02a13823.
Lemma F_92320 : fetch_word Plain.M.loaded_segments (0x92378 : word) = Some W_92320.
Proof. vm_refl. Qed.
Lemma D_92320 : decode_any W_92320 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92324 : bv 32 := 0x03810513.
Lemma F_92324 : fetch_word Plain.M.loaded_segments (0x9237c : word) = Some W_92324.
Proof. vm_refl. Qed.
Lemma D_92324 : decode_any W_92324 = Some (OpImm ALU_ADD 10 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92328 : bv 32 := 0xfbcda0ef.
Lemma F_92328 : fetch_word Plain.M.loaded_segments (0x92380 : word) = Some W_92328.
Proof. vm_refl. Qed.
Lemma D_92328 : decode_any W_92328 = Some (Jal 1 1943484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9232c : bv 32 := 0x02810513.
Lemma F_9232c : fetch_word Plain.M.loaded_segments (0x92384 : word) = Some W_9232c.
Proof. vm_refl. Qed.
Lemma D_9232c : decode_any W_9232c = Some (OpImm ALU_ADD 10 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92330 : bv 32 := 0xfb4da0ef.
Lemma F_92330 : fetch_word Plain.M.loaded_segments (0x92388 : word) = Some W_92330.
Proof. vm_refl. Qed.
Lemma D_92330 : decode_any W_92330 = Some (Jal 1 1943476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92334 : bv 32 := 0x03013583.
Lemma F_92334 : fetch_word Plain.M.loaded_segments (0x9238c : word) = Some W_92334.
Proof. vm_refl. Qed.
Lemma D_92334 : decode_any W_92334 = Some (Load SZ8 true 11 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92338 : bv 32 := 0x00040c63.
Lemma F_92338 : fetch_word Plain.M.loaded_segments (0x92390 : word) = Some W_92338.
Proof. vm_refl. Qed.
Lemma D_92338 : decode_any W_92338 = Some (Branch BC_EQ 8 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9233c : bv 32 := 0x00040513.
Lemma F_9233c : fetch_word Plain.M.loaded_segments (0x92394 : word) = Some W_9233c.
Proof. vm_refl. Qed.
Lemma D_9233c : decode_any W_9233c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92340 : bv 32 := 0x8e8db0ef.
Lemma F_92340 : fetch_word Plain.M.loaded_segments (0x92398 : word) = Some W_92340.
Proof. vm_refl. Qed.
Lemma D_92340 : decode_any W_92340 = Some (Jal 1 1945832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92344 : bv 32 := 0x03010513.
Lemma F_92344 : fetch_word Plain.M.loaded_segments (0x9239c : word) = Some W_92344.
Proof. vm_refl. Qed.
Lemma D_92344 : decode_any W_92344 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92348 : bv 32 := 0xf9cda0ef.
Lemma F_92348 : fetch_word Plain.M.loaded_segments (0x923a0 : word) = Some W_92348.
Proof. vm_refl. Qed.
Lemma D_92348 : decode_any W_92348 = Some (Jal 1 1943452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9234c : bv 32 := 0x0080006f.
Lemma F_9234c : fetch_word Plain.M.loaded_segments (0x923a4 : word) = Some W_9234c.
Proof. vm_refl. Qed.
Lemma D_9234c : decode_any W_9234c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92354 : bv 32 := 0x02010513.
Lemma F_92354 : fetch_word Plain.M.loaded_segments (0x923ac : word) = Some W_92354.
Proof. vm_refl. Qed.
Lemma D_92354 : decode_any W_92354 = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92358 : bv 32 := 0x040000ef.
Lemma F_92358 : fetch_word Plain.M.loaded_segments (0x923b0 : word) = Some W_92358.
Proof. vm_refl. Qed.
Lemma D_92358 : decode_any W_92358 = Some (Jal 1 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9235c : bv 32 := 0x01810513.
Lemma F_9235c : fetch_word Plain.M.loaded_segments (0x923b4 : word) = Some W_9235c.
Proof. vm_refl. Qed.
Lemma D_9235c : decode_any W_9235c = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92360 : bv 32 := 0x038000ef.
Lemma F_92360 : fetch_word Plain.M.loaded_segments (0x923b8 : word) = Some W_92360.
Proof. vm_refl. Qed.
Lemma D_92360 : decode_any W_92360 = Some (Jal 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92364 : bv 32 := 0x01010513.
Lemma F_92364 : fetch_word Plain.M.loaded_segments (0x923bc : word) = Some W_92364.
Proof. vm_refl. Qed.
Lemma D_92364 : decode_any W_92364 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92368 : bv 32 := 0x030000ef.
Lemma F_92368 : fetch_word Plain.M.loaded_segments (0x923c0 : word) = Some W_92368.
Proof. vm_refl. Qed.
Lemma D_92368 : decode_any W_92368 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9236c : bv 32 := 0x00810513.
Lemma F_9236c : fetch_word Plain.M.loaded_segments (0x923c4 : word) = Some W_9236c.
Proof. vm_refl. Qed.
Lemma D_9236c : decode_any W_9236c = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92370 : bv 32 := 0x028000ef.
Lemma F_92370 : fetch_word Plain.M.loaded_segments (0x923c8 : word) = Some W_92370.
Proof. vm_refl. Qed.
Lemma D_92370 : decode_any W_92370 = Some (Jal 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92374 : bv 32 := 0x00040513.
Lemma F_92374 : fetch_word Plain.M.loaded_segments (0x923cc : word) = Some W_92374.
Proof. vm_refl. Qed.
Lemma D_92374 : decode_any W_92374 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92378 : bv 32 := 0x06813083.
Lemma F_92378 : fetch_word Plain.M.loaded_segments (0x923d0 : word) = Some W_92378.
Proof. vm_refl. Qed.
Lemma D_92378 : decode_any W_92378 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9237c : bv 32 := 0x06013403.
Lemma F_9237c : fetch_word Plain.M.loaded_segments (0x923d4 : word) = Some W_9237c.
Proof. vm_refl. Qed.
Lemma D_9237c : decode_any W_9237c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92380 : bv 32 := 0x05813483.
Lemma F_92380 : fetch_word Plain.M.loaded_segments (0x923d8 : word) = Some W_92380.
Proof. vm_refl. Qed.
Lemma D_92380 : decode_any W_92380 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92384 : bv 32 := 0x05013903.
Lemma F_92384 : fetch_word Plain.M.loaded_segments (0x923dc : word) = Some W_92384.
Proof. vm_refl. Qed.
Lemma D_92384 : decode_any W_92384 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92388 : bv 32 := 0x04813983.
Lemma F_92388 : fetch_word Plain.M.loaded_segments (0x923e0 : word) = Some W_92388.
Proof. vm_refl. Qed.
Lemma D_92388 : decode_any W_92388 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9238c : bv 32 := 0x04013a03.
Lemma F_9238c : fetch_word Plain.M.loaded_segments (0x923e4 : word) = Some W_9238c.
Proof. vm_refl. Qed.
Lemma D_9238c : decode_any W_9238c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92390 : bv 32 := 0x07010113.
Lemma F_92390 : fetch_word Plain.M.loaded_segments (0x923e8 : word) = Some W_92390.
Proof. vm_refl. Qed.
Lemma D_92390 : decode_any W_92390 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92394 : bv 32 := 0x00008067.
Lemma F_92394 : fetch_word Plain.M.loaded_segments (0x923ec : word) = Some W_92394.
Proof. vm_refl. Qed.
Lemma D_92394 : decode_any W_92394 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
