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
Definition W_882d0 : bv 32 := 0xfe010113.
Lemma F_882d0 : fetch_word Plain.M.loaded_segments (0x88328 : word) = Some W_882d0.
Proof. vm_refl. Qed.
Lemma D_882d0 : decode_any W_882d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882d4 : bv 32 := 0x00113c23.
Lemma F_882d4 : fetch_word Plain.M.loaded_segments (0x8832c : word) = Some W_882d4.
Proof. vm_refl. Qed.
Lemma D_882d4 : decode_any W_882d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882d8 : bv 32 := 0x00813823.
Lemma F_882d8 : fetch_word Plain.M.loaded_segments (0x88330 : word) = Some W_882d8.
Proof. vm_refl. Qed.
Lemma D_882d8 : decode_any W_882d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882dc : bv 32 := 0x00913423.
Lemma F_882dc : fetch_word Plain.M.loaded_segments (0x88334 : word) = Some W_882dc.
Proof. vm_refl. Qed.
Lemma D_882dc : decode_any W_882dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882e0 : bv 32 := 0x06058063.
Lemma F_882e0 : fetch_word Plain.M.loaded_segments (0x88338 : word) = Some W_882e0.
Proof. vm_refl. Qed.
Lemma D_882e0 : decode_any W_882e0 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882e4 : bv 32 := 0x00058413.
Lemma F_882e4 : fetch_word Plain.M.loaded_segments (0x8833c : word) = Some W_882e4.
Proof. vm_refl. Qed.
Lemma D_882e4 : decode_any W_882e4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882e8 : bv 32 := 0x00050493.
Lemma F_882e8 : fetch_word Plain.M.loaded_segments (0x88340 : word) = Some W_882e8.
Proof. vm_refl. Qed.
Lemma D_882e8 : decode_any W_882e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882ec : bv 32 := 0x00058513.
Lemma F_882ec : fetch_word Plain.M.loaded_segments (0x88344 : word) = Some W_882ec.
Proof. vm_refl. Qed.
Lemma D_882ec : decode_any W_882ec = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882f0 : bv 32 := 0xe38e50ef.
Lemma F_882f0 : fetch_word Plain.M.loaded_segments (0x88348 : word) = Some W_882f0.
Proof. vm_refl. Qed.
Lemma D_882f0 : decode_any W_882f0 = Some (Jal 1 1988152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882f4 : bv 32 := 0x02000593.
Lemma F_882f4 : fetch_word Plain.M.loaded_segments (0x8834c : word) = Some W_882f4.
Proof. vm_refl. Qed.
Lemma D_882f4 : decode_any W_882f4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882f8 : bv 32 := 0x08a5ec63.
Lemma F_882f8 : fetch_word Plain.M.loaded_segments (0x88350 : word) = Some W_882f8.
Proof. vm_refl. Qed.
Lemma D_882f8 : decode_any W_882f8 = Some (Branch BC_LTU 11 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882fc : bv 32 := 0x100015b7.
Lemma F_882fc : fetch_word Plain.M.loaded_segments (0x88354 : word) = Some W_882fc.
Proof. vm_refl. Qed.
Lemma D_882fc : decode_any W_882fc = Some (Lui 11 65537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88300 : bv 32 := 0x00459593.
Lemma F_88300 : fetch_word Plain.M.loaded_segments (0x88358 : word) = Some W_88300.
Proof. vm_refl. Qed.
Lemma D_88300 : decode_any W_88300 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88304 : bv 32 := 0x11658593.
Lemma F_88304 : fetch_word Plain.M.loaded_segments (0x8835c : word) = Some W_88304.
Proof. vm_refl. Qed.
Lemma D_88304 : decode_any W_88304 = Some (OpImm ALU_ADD 11 11 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88308 : bv 32 := 0x00a5d533.
Lemma F_88308 : fetch_word Plain.M.loaded_segments (0x88360 : word) = Some W_88308.
Proof. vm_refl. Qed.
Lemma D_88308 : decode_any W_88308 = Some (Op ALU_SRL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8830c : bv 32 := 0x00157513.
Lemma F_8830c : fetch_word Plain.M.loaded_segments (0x88364 : word) = Some W_8830c.
Proof. vm_refl. Qed.
Lemma D_8830c : decode_any W_8830c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88310 : bv 32 := 0x08050063.
Lemma F_88310 : fetch_word Plain.M.loaded_segments (0x88368 : word) = Some W_88310.
Proof. vm_refl. Qed.
Lemma D_88310 : decode_any W_88310 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88314 : bv 32 := 0x00048513.
Lemma F_88314 : fetch_word Plain.M.loaded_segments (0x8836c : word) = Some W_88314.
Proof. vm_refl. Qed.
Lemma D_88314 : decode_any W_88314 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88318 : bv 32 := 0x00040593.
Lemma F_88318 : fetch_word Plain.M.loaded_segments (0x88370 : word) = Some W_88318.
Proof. vm_refl. Qed.
Lemma D_88318 : decode_any W_88318 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8831c : bv 32 := 0x90ce50ef.
Lemma F_8831c : fetch_word Plain.M.loaded_segments (0x88374 : word) = Some W_8831c.
Proof. vm_refl. Qed.
Lemma D_8831c : decode_any W_8831c = Some (Jal 1 1986828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88320 : bv 32 := 0x04050463.
Lemma F_88320 : fetch_word Plain.M.loaded_segments (0x88378 : word) = Some W_88320.
Proof. vm_refl. Qed.
Lemma D_88320 : decode_any W_88320 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88324 : bv 32 := 0x00050413.
Lemma F_88324 : fetch_word Plain.M.loaded_segments (0x8837c : word) = Some W_88324.
Proof. vm_refl. Qed.
Lemma D_88324 : decode_any W_88324 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88328 : bv 32 := 0x00050593.
Lemma F_88328 : fetch_word Plain.M.loaded_segments (0x88380 : word) = Some W_88328.
Proof. vm_refl. Qed.
Lemma D_88328 : decode_any W_88328 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8832c : bv 32 := 0x0bc000ef.
Lemma F_8832c : fetch_word Plain.M.loaded_segments (0x88384 : word) = Some W_8832c.
Proof. vm_refl. Qed.
Lemma D_8832c : decode_any W_8832c = Some (Jal 1 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88330 : bv 32 := 0x00040513.
Lemma F_88330 : fetch_word Plain.M.loaded_segments (0x88388 : word) = Some W_88330.
Proof. vm_refl. Qed.
Lemma D_88330 : decode_any W_88330 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88334 : bv 32 := 0x00040593.
Lemma F_88334 : fetch_word Plain.M.loaded_segments (0x8838c : word) = Some W_88334.
Proof. vm_refl. Qed.
Lemma D_88334 : decode_any W_88334 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88338 : bv 32 := 0x06d000ef.
Lemma F_88338 : fetch_word Plain.M.loaded_segments (0x88390 : word) = Some W_88338.
Proof. vm_refl. Qed.
Lemma D_88338 : decode_any W_88338 = Some (Jal 1 2156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8833c : bv 32 := 0x0940006f.
Lemma F_8833c : fetch_word Plain.M.loaded_segments (0x88394 : word) = Some W_8833c.
Proof. vm_refl. Qed.
Lemma D_8833c : decode_any W_8833c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88368 : bv 32 := 0x0008a517.
Lemma F_88368 : fetch_word Plain.M.loaded_segments (0x883c0 : word) = Some W_88368.
Proof. vm_refl. Qed.
Lemma D_88368 : decode_any W_88368 = Some (Auipc 10 138, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8836c : bv 32 := 0x20853503.
Lemma F_8836c : fetch_word Plain.M.loaded_segments (0x883c4 : word) = Some W_8836c.
Proof. vm_refl. Qed.
Lemma D_8836c : decode_any W_8836c = Some (Load SZ8 true 10 10 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88370 : bv 32 := 0x00052503.
Lemma F_88370 : fetch_word Plain.M.loaded_segments (0x883c8 : word) = Some W_88370.
Proof. vm_refl. Qed.
Lemma D_88370 : decode_any W_88370 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88374 : bv 32 := 0x00500593.
Lemma F_88374 : fetch_word Plain.M.loaded_segments (0x883cc : word) = Some W_88374.
Proof. vm_refl. Qed.
Lemma D_88374 : decode_any W_88374 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88378 : bv 32 := 0x04a5ca63.
Lemma F_88378 : fetch_word Plain.M.loaded_segments (0x883d0 : word) = Some W_88378.
Proof. vm_refl. Qed.
Lemma D_88378 : decode_any W_88378 = Some (Branch BC_LT 11 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8837c : bv 32 := 0xfff8a517.
Lemma F_8837c : fetch_word Plain.M.loaded_segments (0x883d4 : word) = Some W_8837c.
Proof. vm_refl. Qed.
Lemma D_8837c : decode_any W_8837c = Some (Auipc 10 1048458, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88380 : bv 32 := 0xfff8c597.
Lemma F_88380 : fetch_word Plain.M.loaded_segments (0x883d8 : word) = Some W_88380.
Proof. vm_refl. Qed.
Lemma D_88380 : decode_any W_88380 = Some (Auipc 11 1048460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88384 : bv 32 := 0x30650513.
Lemma F_88384 : fetch_word Plain.M.loaded_segments (0x883dc : word) = Some W_88384.
Proof. vm_refl. Qed.
Lemma D_88384 : decode_any W_88384 = Some (OpImm ALU_ADD 10 10 774, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88388 : bv 32 := 0xa1458593.
Lemma F_88388 : fetch_word Plain.M.loaded_segments (0x883e0 : word) = Some W_88388.
Proof. vm_refl. Qed.
Lemma D_88388 : decode_any W_88388 = Some (OpImm ALU_ADD 11 11 2580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8838c : bv 32 := 0x0280006f.
Lemma F_8838c : fetch_word Plain.M.loaded_segments (0x883e4 : word) = Some W_8838c.
Proof. vm_refl. Qed.
Lemma D_8838c : decode_any W_8838c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883b4 : bv 32 := 0x00000613.
Lemma F_883b4 : fetch_word Plain.M.loaded_segments (0x8840c : word) = Some W_883b4.
Proof. vm_refl. Qed.
Lemma D_883b4 : decode_any W_883b4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883b8 : bv 32 := 0x01813083.
Lemma F_883b8 : fetch_word Plain.M.loaded_segments (0x88410 : word) = Some W_883b8.
Proof. vm_refl. Qed.
Lemma D_883b8 : decode_any W_883b8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883bc : bv 32 := 0x01013403.
Lemma F_883bc : fetch_word Plain.M.loaded_segments (0x88414 : word) = Some W_883bc.
Proof. vm_refl. Qed.
Lemma D_883bc : decode_any W_883bc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883c0 : bv 32 := 0x00813483.
Lemma F_883c0 : fetch_word Plain.M.loaded_segments (0x88418 : word) = Some W_883c0.
Proof. vm_refl. Qed.
Lemma D_883c0 : decode_any W_883c0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883c4 : bv 32 := 0x02010113.
Lemma F_883c4 : fetch_word Plain.M.loaded_segments (0x8841c : word) = Some W_883c4.
Proof. vm_refl. Qed.
Lemma D_883c4 : decode_any W_883c4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883c8 : bv 32 := 0xcfdda06f.
Lemma F_883c8 : fetch_word Plain.M.loaded_segments (0x88420 : word) = Some W_883c8.
Proof. vm_refl. Qed.
Lemma D_883c8 : decode_any W_883c8 = Some (Jal 0 1944828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883d0 : bv 32 := 0x00040513.
Lemma F_883d0 : fetch_word Plain.M.loaded_segments (0x88428 : word) = Some W_883d0.
Proof. vm_refl. Qed.
Lemma D_883d0 : decode_any W_883d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883d4 : bv 32 := 0x01813083.
Lemma F_883d4 : fetch_word Plain.M.loaded_segments (0x8842c : word) = Some W_883d4.
Proof. vm_refl. Qed.
Lemma D_883d4 : decode_any W_883d4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883d8 : bv 32 := 0x01013403.
Lemma F_883d8 : fetch_word Plain.M.loaded_segments (0x88430 : word) = Some W_883d8.
Proof. vm_refl. Qed.
Lemma D_883d8 : decode_any W_883d8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883dc : bv 32 := 0x00813483.
Lemma F_883dc : fetch_word Plain.M.loaded_segments (0x88434 : word) = Some W_883dc.
Proof. vm_refl. Qed.
Lemma D_883dc : decode_any W_883dc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883e0 : bv 32 := 0x02010113.
Lemma F_883e0 : fetch_word Plain.M.loaded_segments (0x88438 : word) = Some W_883e0.
Proof. vm_refl. Qed.
Lemma D_883e0 : decode_any W_883e0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883e4 : bv 32 := 0x00008067.
Lemma F_883e4 : fetch_word Plain.M.loaded_segments (0x8843c : word) = Some W_883e4.
Proof. vm_refl. Qed.
Lemma D_883e4 : decode_any W_883e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
