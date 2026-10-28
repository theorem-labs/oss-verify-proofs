(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_85548 : bv 32 := 0xfd010113.
Lemma F_85548 : fetch_word AsanUbsan.M.loaded_segments (0x85960 : word) = Some W_85548.
Proof. vm_refl. Qed.
Lemma D_85548 : decode_any W_85548 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8554c : bv 32 := 0x02113423.
Lemma F_8554c : fetch_word AsanUbsan.M.loaded_segments (0x85964 : word) = Some W_8554c.
Proof. vm_refl. Qed.
Lemma D_8554c : decode_any W_8554c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85550 : bv 32 := 0x02813023.
Lemma F_85550 : fetch_word AsanUbsan.M.loaded_segments (0x85968 : word) = Some W_85550.
Proof. vm_refl. Qed.
Lemma D_85550 : decode_any W_85550 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85554 : bv 32 := 0x00913c23.
Lemma F_85554 : fetch_word AsanUbsan.M.loaded_segments (0x8596c : word) = Some W_85554.
Proof. vm_refl. Qed.
Lemma D_85554 : decode_any W_85554 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85558 : bv 32 := 0x01213823.
Lemma F_85558 : fetch_word AsanUbsan.M.loaded_segments (0x85970 : word) = Some W_85558.
Proof. vm_refl. Qed.
Lemma D_85558 : decode_any W_85558 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8555c : bv 32 := 0x01313423.
Lemma F_8555c : fetch_word AsanUbsan.M.loaded_segments (0x85974 : word) = Some W_8555c.
Proof. vm_refl. Qed.
Lemma D_8555c : decode_any W_8555c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85560 : bv 32 := 0x0014a517.
Lemma F_85560 : fetch_word AsanUbsan.M.loaded_segments (0x85978 : word) = Some W_85560.
Proof. vm_refl. Qed.
Lemma D_85560 : decode_any W_85560 = Some (Auipc 10 330, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85564 : bv 32 := 0xd5050413.
Lemma F_85564 : fetch_word AsanUbsan.M.loaded_segments (0x8597c : word) = Some W_85564.
Proof. vm_refl. Qed.
Lemma D_85564 : decode_any W_85564 = Some (OpImm ALU_ADD 8 10 3408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85568 : bv 32 := 0x00040503.
Lemma F_85568 : fetch_word AsanUbsan.M.loaded_segments (0x85980 : word) = Some W_85568.
Proof. vm_refl. Qed.
Lemma D_85568 : decode_any W_85568 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8556c : bv 32 := 0x0230000f.
Lemma F_8556c : fetch_word AsanUbsan.M.loaded_segments (0x85984 : word) = Some W_8556c.
Proof. vm_refl. Qed.
Lemma D_8556c : decode_any W_8556c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85570 : bv 32 := 0x0e051e63.
Lemma F_85570 : fetch_word AsanUbsan.M.loaded_segments (0x85988 : word) = Some W_85570.
Proof. vm_refl. Qed.
Lemma D_85570 : decode_any W_85570 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85574 : bv 32 := 0x00140513.
Lemma F_85574 : fetch_word AsanUbsan.M.loaded_segments (0x8598c : word) = Some W_85574.
Proof. vm_refl. Qed.
Lemma D_85574 : decode_any W_85574 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85578 : bv 32 := 0x0ff00593.
Lemma F_85578 : fetch_word AsanUbsan.M.loaded_segments (0x85990 : word) = Some W_85578.
Proof. vm_refl. Qed.
Lemma D_85578 : decode_any W_85578 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8557c : bv 32 := 0x00100613.
Lemma F_8557c : fetch_word AsanUbsan.M.loaded_segments (0x85994 : word) = Some W_8557c.
Proof. vm_refl. Qed.
Lemma D_8557c : decode_any W_8557c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85580 : bv 32 := 0xffc57693.
Lemma F_85580 : fetch_word AsanUbsan.M.loaded_segments (0x85998 : word) = Some W_85580.
Proof. vm_refl. Qed.
Lemma D_85580 : decode_any W_85580 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85584 : bv 32 := 0x00357713.
Lemma F_85584 : fetch_word AsanUbsan.M.loaded_segments (0x8599c : word) = Some W_85584.
Proof. vm_refl. Qed.
Lemma D_85584 : decode_any W_85584 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85588 : bv 32 := 0x00371713.
Lemma F_85588 : fetch_word AsanUbsan.M.loaded_segments (0x859a0 : word) = Some W_85588.
Proof. vm_refl. Qed.
Lemma D_85588 : decode_any W_85588 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8558c : bv 32 := 0x00e595bb.
Lemma F_8558c : fetch_word AsanUbsan.M.loaded_segments (0x859a4 : word) = Some W_8558c.
Proof. vm_refl. Qed.
Lemma D_8558c : decode_any W_8558c = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85590 : bv 32 := 0x00e6163b.
Lemma F_85590 : fetch_word AsanUbsan.M.loaded_segments (0x859a8 : word) = Some W_85590.
Proof. vm_refl. Qed.
Lemma D_85590 : decode_any W_85590 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85594 : bv 32 := 0x1406a7af.
Lemma F_85594 : fetch_word AsanUbsan.M.loaded_segments (0x859ac : word) = Some W_85594.
Proof. vm_refl. Qed.
Lemma D_85594 : decode_any W_85594 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85598 : bv 32 := 0x00060813.
Lemma F_85598 : fetch_word AsanUbsan.M.loaded_segments (0x859b0 : word) = Some W_85598.
Proof. vm_refl. Qed.
Lemma D_85598 : decode_any W_85598 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8559c : bv 32 := 0x0107c833.
Lemma F_8559c : fetch_word AsanUbsan.M.loaded_segments (0x859b4 : word) = Some W_8559c.
Proof. vm_refl. Qed.
Lemma D_8559c : decode_any W_8559c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855a0 : bv 32 := 0x00b87833.
Lemma F_855a0 : fetch_word AsanUbsan.M.loaded_segments (0x859b8 : word) = Some W_855a0.
Proof. vm_refl. Qed.
Lemma D_855a0 : decode_any W_855a0 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855a4 : bv 32 := 0x0107c833.
Lemma F_855a4 : fetch_word AsanUbsan.M.loaded_segments (0x859bc : word) = Some W_855a4.
Proof. vm_refl. Qed.
Lemma D_855a4 : decode_any W_855a4 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855a8 : bv 32 := 0x1906a82f.
Lemma F_855a8 : fetch_word AsanUbsan.M.loaded_segments (0x859c0 : word) = Some W_855a8.
Proof. vm_refl. Qed.
Lemma D_855a8 : decode_any W_855a8 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855ac : bv 32 := 0xfe0814e3.
Lemma F_855ac : fetch_word AsanUbsan.M.loaded_segments (0x859c4 : word) = Some W_855ac.
Proof. vm_refl. Qed.
Lemma D_855ac : decode_any W_855ac = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855b0 : bv 32 := 0x00e7d5bb.
Lemma F_855b0 : fetch_word AsanUbsan.M.loaded_segments (0x859c8 : word) = Some W_855b0.
Proof. vm_refl. Qed.
Lemma D_855b0 : decode_any W_855b0 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855b4 : bv 32 := 0x0ff5f593.
Lemma F_855b4 : fetch_word AsanUbsan.M.loaded_segments (0x859cc : word) = Some W_855b4.
Proof. vm_refl. Qed.
Lemma D_855b4 : decode_any W_855b4 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855b8 : bv 32 := 0x0c059c63.
Lemma F_855b8 : fetch_word AsanUbsan.M.loaded_segments (0x859d0 : word) = Some W_855b8.
Proof. vm_refl. Qed.
Lemma D_855b8 : decode_any W_855b8 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855bc : bv 32 := 0x00040503.
Lemma F_855bc : fetch_word AsanUbsan.M.loaded_segments (0x859d4 : word) = Some W_855bc.
Proof. vm_refl. Qed.
Lemma D_855bc : decode_any W_855bc = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855c0 : bv 32 := 0x0a051263.
Lemma F_855c0 : fetch_word AsanUbsan.M.loaded_segments (0x859d8 : word) = Some W_855c0.
Proof. vm_refl. Qed.
Lemma D_855c0 : decode_any W_855c0 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855c4 : bv 32 := 0x000bb517.
Lemma F_855c4 : fetch_word AsanUbsan.M.loaded_segments (0x859dc : word) = Some W_855c4.
Proof. vm_refl. Qed.
Lemma D_855c4 : decode_any W_855c4 = Some (Auipc 10 187, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855c8 : bv 32 := 0x000815b7.
Lemma F_855c8 : fetch_word AsanUbsan.M.loaded_segments (0x859e0 : word) = Some W_855c8.
Proof. vm_refl. Qed.
Lemma D_855c8 : decode_any W_855c8 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855cc : bv 32 := 0x46450493.
Lemma F_855cc : fetch_word AsanUbsan.M.loaded_segments (0x859e4 : word) = Some W_855cc.
Proof. vm_refl. Qed.
Lemma D_855cc : decode_any W_855cc = Some (OpImm ALU_ADD 9 10 1124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855d0 : bv 32 := 0x0085851b.
Lemma F_855d0 : fetch_word AsanUbsan.M.loaded_segments (0x859e8 : word) = Some W_855d0.
Proof. vm_refl. Qed.
Lemma D_855d0 : decode_any W_855d0 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855d4 : bv 32 := 0x00a48533.
Lemma F_855d4 : fetch_word AsanUbsan.M.loaded_segments (0x859ec : word) = Some W_855d4.
Proof. vm_refl. Qed.
Lemma D_855d4 : decode_any W_855d4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855d8 : bv 32 := 0x02800613.
Lemma F_855d8 : fetch_word AsanUbsan.M.loaded_segments (0x859f0 : word) = Some W_855d8.
Proof. vm_refl. Qed.
Lemma D_855d8 : decode_any W_855d8 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855dc : bv 32 := 0x00000593.
Lemma F_855dc : fetch_word AsanUbsan.M.loaded_segments (0x859f4 : word) = Some W_855dc.
Proof. vm_refl. Qed.
Lemma D_855dc : decode_any W_855dc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e0 : bv 32 := 0x269050ef.
Lemma F_855e0 : fetch_word AsanUbsan.M.loaded_segments (0x859f8 : word) = Some W_855e0.
Proof. vm_refl. Qed.
Lemma D_855e0 : decode_any W_855e0 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e4 : bv 32 := 0x00048023.
Lemma F_855e4 : fetch_word AsanUbsan.M.loaded_segments (0x859fc : word) = Some W_855e4.
Proof. vm_refl. Qed.
Lemma D_855e4 : decode_any W_855e4 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e8 : bv 32 := 0x00848513.
Lemma F_855e8 : fetch_word AsanUbsan.M.loaded_segments (0x85a00 : word) = Some W_855e8.
Proof. vm_refl. Qed.
Lemma D_855e8 : decode_any W_855e8 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855ec : bv 32 := 0x00040637.
Lemma F_855ec : fetch_word AsanUbsan.M.loaded_segments (0x85a04 : word) = Some W_855ec.
Proof. vm_refl. Qed.
Lemma D_855ec : decode_any W_855ec = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f0 : bv 32 := 0x000409b7.
Lemma F_855f0 : fetch_word AsanUbsan.M.loaded_segments (0x85a08 : word) = Some W_855f0.
Proof. vm_refl. Qed.
Lemma D_855f0 : decode_any W_855f0 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f4 : bv 32 := 0x00000593.
Lemma F_855f4 : fetch_word AsanUbsan.M.loaded_segments (0x85a0c : word) = Some W_855f4.
Proof. vm_refl. Qed.
Lemma D_855f4 : decode_any W_855f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f8 : bv 32 := 0x251050ef.
Lemma F_855f8 : fetch_word AsanUbsan.M.loaded_segments (0x85a10 : word) = Some W_855f8.
Proof. vm_refl. Qed.
Lemma D_855f8 : decode_any W_855f8 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855fc : bv 32 := 0x0409851b.
Lemma F_855fc : fetch_word AsanUbsan.M.loaded_segments (0x85a14 : word) = Some W_855fc.
Proof. vm_refl. Qed.
Lemma D_855fc : decode_any W_855fc = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85600 : bv 32 := 0x00a48533.
Lemma F_85600 : fetch_word AsanUbsan.M.loaded_segments (0x85a18 : word) = Some W_85600.
Proof. vm_refl. Qed.
Lemma D_85600 : decode_any W_85600 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85604 : bv 32 := 0x01b00613.
Lemma F_85604 : fetch_word AsanUbsan.M.loaded_segments (0x85a1c : word) = Some W_85604.
Proof. vm_refl. Qed.
Lemma D_85604 : decode_any W_85604 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85608 : bv 32 := 0x00761613.
Lemma F_85608 : fetch_word AsanUbsan.M.loaded_segments (0x85a20 : word) = Some W_85608.
Proof. vm_refl. Qed.
Lemma D_85608 : decode_any W_85608 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8560c : bv 32 := 0x00000593.
Lemma F_8560c : fetch_word AsanUbsan.M.loaded_segments (0x85a24 : word) = Some W_8560c.
Proof. vm_refl. Qed.
Lemma D_8560c : decode_any W_8560c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85610 : bv 32 := 0x239050ef.
Lemma F_85610 : fetch_word AsanUbsan.M.loaded_segments (0x85a28 : word) = Some W_85610.
Proof. vm_refl. Qed.
Lemma D_85610 : decode_any W_85610 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85614 : bv 32 := 0x00041937.
Lemma F_85614 : fetch_word AsanUbsan.M.loaded_segments (0x85a2c : word) = Some W_85614.
Proof. vm_refl. Qed.
Lemma D_85614 : decode_any W_85614 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85618 : bv 32 := 0xdc09051b.
Lemma F_85618 : fetch_word AsanUbsan.M.loaded_segments (0x85a30 : word) = Some W_85618.
Proof. vm_refl. Qed.
Lemma D_85618 : decode_any W_85618 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8561c : bv 32 := 0x00a48533.
Lemma F_8561c : fetch_word AsanUbsan.M.loaded_segments (0x85a34 : word) = Some W_8561c.
Proof. vm_refl. Qed.
Lemma D_8561c : decode_any W_8561c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85620 : bv 32 := 0x2489861b.
Lemma F_85620 : fetch_word AsanUbsan.M.loaded_segments (0x85a38 : word) = Some W_85620.
Proof. vm_refl. Qed.
Lemma D_85620 : decode_any W_85620 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85624 : bv 32 := 0x00000593.
Lemma F_85624 : fetch_word AsanUbsan.M.loaded_segments (0x85a3c : word) = Some W_85624.
Proof. vm_refl. Qed.
Lemma D_85624 : decode_any W_85624 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85628 : bv 32 := 0x221050ef.
Lemma F_85628 : fetch_word AsanUbsan.M.loaded_segments (0x85a40 : word) = Some W_85628.
Proof. vm_refl. Qed.
Lemma D_85628 : decode_any W_85628 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8562c : bv 32 := 0x000b2517.
Lemma F_8562c : fetch_word AsanUbsan.M.loaded_segments (0x85a44 : word) = Some W_8562c.
Proof. vm_refl. Qed.
Lemma D_8562c : decode_any W_8562c = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85630 : bv 32 := 0xa5c53983.
Lemma F_85630 : fetch_word AsanUbsan.M.loaded_segments (0x85a48 : word) = Some W_85630.
Proof. vm_refl. Qed.
Lemma D_85630 : decode_any W_85630 = Some (Load SZ8 true 19 10 2652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85634 : bv 32 := 0x0009b503.
Lemma F_85634 : fetch_word AsanUbsan.M.loaded_segments (0x85a4c : word) = Some W_85634.
Proof. vm_refl. Qed.
Lemma D_85634 : decode_any W_85634 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85638 : bv 32 := 0x00051663.
Lemma F_85638 : fetch_word AsanUbsan.M.loaded_segments (0x85a50 : word) = Some W_85638.
Proof. vm_refl. Qed.
Lemma D_85638 : decode_any W_85638 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85644 : bv 32 := 0x012485b3.
Lemma F_85644 : fetch_word AsanUbsan.M.loaded_segments (0x85a5c : word) = Some W_85644.
Proof. vm_refl. Qed.
Lemma D_85644 : decode_any W_85644 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85648 : bv 32 := 0xdd09061b.
Lemma F_85648 : fetch_word AsanUbsan.M.loaded_segments (0x85a60 : word) = Some W_85648.
Proof. vm_refl. Qed.
Lemma D_85648 : decode_any W_85648 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8564c : bv 32 := 0x00c48633.
Lemma F_8564c : fetch_word AsanUbsan.M.loaded_segments (0x85a64 : word) = Some W_8564c.
Proof. vm_refl. Qed.
Lemma D_8564c : decode_any W_8564c = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85650 : bv 32 := 0x00100693.
Lemma F_85650 : fetch_word AsanUbsan.M.loaded_segments (0x85a68 : word) = Some W_85650.
Proof. vm_refl. Qed.
Lemma D_85650 : decode_any W_85650 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85654 : bv 32 := 0xdca5b023.
Lemma F_85654 : fetch_word AsanUbsan.M.loaded_segments (0x85a6c : word) = Some W_85654.
Proof. vm_refl. Qed.
Lemma D_85654 : decode_any W_85654 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85658 : bv 32 := 0xdcc5b423.
Lemma F_85658 : fetch_word AsanUbsan.M.loaded_segments (0x85a70 : word) = Some W_85658.
Proof. vm_refl. Qed.
Lemma D_85658 : decode_any W_85658 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8565c : bv 32 := 0x0310000f.
Lemma F_8565c : fetch_word AsanUbsan.M.loaded_segments (0x85a74 : word) = Some W_8565c.
Proof. vm_refl. Qed.
Lemma D_8565c : decode_any W_8565c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85660 : bv 32 := 0x00d40023.
Lemma F_85660 : fetch_word AsanUbsan.M.loaded_segments (0x85a78 : word) = Some W_85660.
Proof. vm_refl. Qed.
Lemma D_85660 : decode_any W_85660 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85664 : bv 32 := 0x0310000f.
Lemma F_85664 : fetch_word AsanUbsan.M.loaded_segments (0x85a7c : word) = Some W_85664.
Proof. vm_refl. Qed.
Lemma D_85664 : decode_any W_85664 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85668 : bv 32 := 0x000400a3.
Lemma F_85668 : fetch_word AsanUbsan.M.loaded_segments (0x85a80 : word) = Some W_85668.
Proof. vm_refl. Qed.
Lemma D_85668 : decode_any W_85668 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8566c : bv 32 := 0x000bb517.
Lemma F_8566c : fetch_word AsanUbsan.M.loaded_segments (0x85a84 : word) = Some W_8566c.
Proof. vm_refl. Qed.
Lemma D_8566c : decode_any W_8566c = Some (Auipc 10 187, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85670 : bv 32 := 0x3bc50513.
Lemma F_85670 : fetch_word AsanUbsan.M.loaded_segments (0x85a88 : word) = Some W_85670.
Proof. vm_refl. Qed.
Lemma D_85670 : decode_any W_85670 = Some (OpImm ALU_ADD 10 10 956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85674 : bv 32 := 0x02813083.
Lemma F_85674 : fetch_word AsanUbsan.M.loaded_segments (0x85a8c : word) = Some W_85674.
Proof. vm_refl. Qed.
Lemma D_85674 : decode_any W_85674 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85678 : bv 32 := 0x02013403.
Lemma F_85678 : fetch_word AsanUbsan.M.loaded_segments (0x85a90 : word) = Some W_85678.
Proof. vm_refl. Qed.
Lemma D_85678 : decode_any W_85678 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8567c : bv 32 := 0x01813483.
Lemma F_8567c : fetch_word AsanUbsan.M.loaded_segments (0x85a94 : word) = Some W_8567c.
Proof. vm_refl. Qed.
Lemma D_8567c : decode_any W_8567c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85680 : bv 32 := 0x01013903.
Lemma F_85680 : fetch_word AsanUbsan.M.loaded_segments (0x85a98 : word) = Some W_85680.
Proof. vm_refl. Qed.
Lemma D_85680 : decode_any W_85680 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85684 : bv 32 := 0x00813983.
Lemma F_85684 : fetch_word AsanUbsan.M.loaded_segments (0x85a9c : word) = Some W_85684.
Proof. vm_refl. Qed.
Lemma D_85684 : decode_any W_85684 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85688 : bv 32 := 0x03010113.
Lemma F_85688 : fetch_word AsanUbsan.M.loaded_segments (0x85aa0 : word) = Some W_85688.
Proof. vm_refl. Qed.
Lemma D_85688 : decode_any W_85688 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8568c : bv 32 := 0x00008067.
Lemma F_8568c : fetch_word AsanUbsan.M.loaded_segments (0x85aa4 : word) = Some W_8568c.
Proof. vm_refl. Qed.
Lemma D_8568c : decode_any W_8568c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
