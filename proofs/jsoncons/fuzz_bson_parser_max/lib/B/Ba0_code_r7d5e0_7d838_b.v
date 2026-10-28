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
Definition W_975b0 : bv 32 := 0xfc010113.
Lemma F_975b0 : fetch_word AsanUbsan.M.loaded_segments (0x979c8 : word) = Some W_975b0.
Proof. vm_refl. Qed.
Lemma D_975b0 : decode_any W_975b0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975b4 : bv 32 := 0x02113c23.
Lemma F_975b4 : fetch_word AsanUbsan.M.loaded_segments (0x979cc : word) = Some W_975b4.
Proof. vm_refl. Qed.
Lemma D_975b4 : decode_any W_975b4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975b8 : bv 32 := 0x02813823.
Lemma F_975b8 : fetch_word AsanUbsan.M.loaded_segments (0x979d0 : word) = Some W_975b8.
Proof. vm_refl. Qed.
Lemma D_975b8 : decode_any W_975b8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975bc : bv 32 := 0x02913423.
Lemma F_975bc : fetch_word AsanUbsan.M.loaded_segments (0x979d4 : word) = Some W_975bc.
Proof. vm_refl. Qed.
Lemma D_975bc : decode_any W_975bc = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975c0 : bv 32 := 0x03213023.
Lemma F_975c0 : fetch_word AsanUbsan.M.loaded_segments (0x979d8 : word) = Some W_975c0.
Proof. vm_refl. Qed.
Lemma D_975c0 : decode_any W_975c0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975c4 : bv 32 := 0x01313c23.
Lemma F_975c4 : fetch_word AsanUbsan.M.loaded_segments (0x979dc : word) = Some W_975c4.
Proof. vm_refl. Qed.
Lemma D_975c4 : decode_any W_975c4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975c8 : bv 32 := 0x01413823.
Lemma F_975c8 : fetch_word AsanUbsan.M.loaded_segments (0x979e0 : word) = Some W_975c8.
Proof. vm_refl. Qed.
Lemma D_975c8 : decode_any W_975c8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975cc : bv 32 := 0x01513423.
Lemma F_975cc : fetch_word AsanUbsan.M.loaded_segments (0x979e4 : word) = Some W_975cc.
Proof. vm_refl. Qed.
Lemma D_975cc : decode_any W_975cc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975d0 : bv 32 := 0x00058993.
Lemma F_975d0 : fetch_word AsanUbsan.M.loaded_segments (0x979e8 : word) = Some W_975d0.
Proof. vm_refl. Qed.
Lemma D_975d0 : decode_any W_975d0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975d4 : bv 32 := 0x0085aa03.
Lemma F_975d4 : fetch_word AsanUbsan.M.loaded_segments (0x979ec : word) = Some W_975d4.
Proof. vm_refl. Qed.
Lemma D_975d4 : decode_any W_975d4 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975d8 : bv 32 := 0x00c5aa83.
Lemma F_975d8 : fetch_word AsanUbsan.M.loaded_segments (0x979f0 : word) = Some W_975d8.
Proof. vm_refl. Qed.
Lemma D_975d8 : decode_any W_975d8 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975dc : bv 32 := 0x015a65b3.
Lemma F_975dc : fetch_word AsanUbsan.M.loaded_segments (0x979f4 : word) = Some W_975dc.
Proof. vm_refl. Qed.
Lemma D_975dc : decode_any W_975dc = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975e0 : bv 32 := 0x00059663.
Lemma F_975e0 : fetch_word AsanUbsan.M.loaded_segments (0x979f8 : word) = Some W_975e0.
Proof. vm_refl. Qed.
Lemma D_975e0 : decode_any W_975e0 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975ec : bv 32 := 0x00050493.
Lemma F_975ec : fetch_word AsanUbsan.M.loaded_segments (0x97a04 : word) = Some W_975ec.
Proof. vm_refl. Qed.
Lemma D_975ec : decode_any W_975ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975f0 : bv 32 := 0x10000513.
Lemma F_975f0 : fetch_word AsanUbsan.M.loaded_segments (0x97a08 : word) = Some W_975f0.
Proof. vm_refl. Qed.
Lemma D_975f0 : decode_any W_975f0 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975f4 : bv 32 := 0x0aaafe63.
Lemma F_975f4 : fetch_word AsanUbsan.M.loaded_segments (0x97a0c : word) = Some W_975f4.
Proof. vm_refl. Qed.
Lemma D_975f4 : decode_any W_975f4 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975f8 : bv 32 := 0x00060413.
Lemma F_975f8 : fetch_word AsanUbsan.M.loaded_segments (0x97a10 : word) = Some W_975f8.
Proof. vm_refl. Qed.
Lemma D_975f8 : decode_any W_975f8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_975fc : bv 32 := 0x0ff00513.
Lemma F_975fc : fetch_word AsanUbsan.M.loaded_segments (0x97a14 : word) = Some W_975fc.
Proof. vm_refl. Qed.
Lemma D_975fc : decode_any W_975fc = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97600 : bv 32 := 0x00aa6463.
Lemma F_97600 : fetch_word AsanUbsan.M.loaded_segments (0x97a18 : word) = Some W_97600.
Proof. vm_refl. Qed.
Lemma D_97600 : decode_any W_97600 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97608 : bv 32 := 0x00013023.
Lemma F_97608 : fetch_word AsanUbsan.M.loaded_segments (0x97a20 : word) = Some W_97608.
Proof. vm_refl. Qed.
Lemma D_97608 : decode_any W_97608 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9760c : bv 32 := 0x00043023.
Lemma F_9760c : fetch_word AsanUbsan.M.loaded_segments (0x97a24 : word) = Some W_9760c.
Proof. vm_refl. Qed.
Lemma D_9760c : decode_any W_9760c = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97610 : bv 32 := 0x001a0913.
Lemma F_97610 : fetch_word AsanUbsan.M.loaded_segments (0x97a28 : word) = Some W_97610.
Proof. vm_refl. Qed.
Lemma D_97610 : decode_any W_97610 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97614 : bv 32 := 0x00010613.
Lemma F_97614 : fetch_word AsanUbsan.M.loaded_segments (0x97a2c : word) = Some W_97614.
Proof. vm_refl. Qed.
Lemma D_97614 : decode_any W_97614 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97618 : bv 32 := 0x00048513.
Lemma F_97618 : fetch_word AsanUbsan.M.loaded_segments (0x97a30 : word) = Some W_97618.
Proof. vm_refl. Qed.
Lemma D_97618 : decode_any W_97618 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9761c : bv 32 := 0x00090593.
Lemma F_9761c : fetch_word AsanUbsan.M.loaded_segments (0x97a34 : word) = Some W_9761c.
Proof. vm_refl. Qed.
Lemma D_9761c : decode_any W_9761c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97620 : bv 32 := 0x00040693.
Lemma F_97620 : fetch_word AsanUbsan.M.loaded_segments (0x97a38 : word) = Some W_97620.
Proof. vm_refl. Qed.
Lemma D_97620 : decode_any W_97620 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97624 : bv 32 := 0x0b0000ef.
Lemma F_97624 : fetch_word AsanUbsan.M.loaded_segments (0x97a3c : word) = Some W_97624.
Proof. vm_refl. Qed.
Lemma D_97624 : decode_any W_97624 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97628 : bv 32 := 0x06050263.
Lemma F_97628 : fetch_word AsanUbsan.M.loaded_segments (0x97a40 : word) = Some W_97628.
Proof. vm_refl. Qed.
Lemma D_97628 : decode_any W_97628 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9762c : bv 32 := 0x008a961b.
Lemma F_9762c : fetch_word AsanUbsan.M.loaded_segments (0x97a44 : word) = Some W_9762c.
Proof. vm_refl. Qed.
Lemma D_9762c : decode_any W_9762c = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97630 : bv 32 := 0x0009b583.
Lemma F_97630 : fetch_word AsanUbsan.M.loaded_segments (0x97a48 : word) = Some W_97630.
Proof. vm_refl. Qed.
Lemma D_97630 : decode_any W_97630 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97634 : bv 32 := 0x01466633.
Lemma F_97634 : fetch_word AsanUbsan.M.loaded_segments (0x97a4c : word) = Some W_97634.
Proof. vm_refl. Qed.
Lemma D_97634 : decode_any W_97634 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97638 : bv 32 := 0x00c53023.
Lemma F_97638 : fetch_word AsanUbsan.M.loaded_segments (0x97a50 : word) = Some W_97638.
Proof. vm_refl. Qed.
Lemma D_97638 : decode_any W_97638 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9763c : bv 32 := 0x00850513.
Lemma F_9763c : fetch_word AsanUbsan.M.loaded_segments (0x97a54 : word) = Some W_9763c.
Proof. vm_refl. Qed.
Lemma D_9763c : decode_any W_9763c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97640 : bv 32 := 0x003a1613.
Lemma F_97640 : fetch_word AsanUbsan.M.loaded_segments (0x97a58 : word) = Some W_97640.
Proof. vm_refl. Qed.
Lemma D_97640 : decode_any W_97640 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97644 : bv 32 := 0x989f30ef.
Lemma F_97644 : fetch_word AsanUbsan.M.loaded_segments (0x97a5c : word) = Some W_97644.
Proof. vm_refl. Qed.
Lemma D_97644 : decode_any W_97644 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97648 : bv 32 := 0x00013503.
Lemma F_97648 : fetch_word AsanUbsan.M.loaded_segments (0x97a60 : word) = Some W_97648.
Proof. vm_refl. Qed.
Lemma D_97648 : decode_any W_97648 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9764c : bv 32 := 0x01055513.
Lemma F_9764c : fetch_word AsanUbsan.M.loaded_segments (0x97a64 : word) = Some W_9764c.
Proof. vm_refl. Qed.
Lemma D_9764c : decode_any W_9764c = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97650 : bv 32 := 0xff057513.
Lemma F_97650 : fetch_word AsanUbsan.M.loaded_segments (0x97a68 : word) = Some W_97650.
Proof. vm_refl. Qed.
Lemma D_97650 : decode_any W_97650 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97654 : bv 32 := 0x00a48533.
Lemma F_97654 : fetch_word AsanUbsan.M.loaded_segments (0x97a6c : word) = Some W_97654.
Proof. vm_refl. Qed.
Lemma D_97654 : decode_any W_97654 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97658 : bv 32 := 0x01850513.
Lemma F_97658 : fetch_word AsanUbsan.M.loaded_segments (0x97a70 : word) = Some W_97658.
Proof. vm_refl. Qed.
Lemma D_97658 : decode_any W_97658 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9765c : bv 32 := 0x0325252f.
Lemma F_9765c : fetch_word AsanUbsan.M.loaded_segments (0x97a74 : word) = Some W_9765c.
Proof. vm_refl. Qed.
Lemma D_9765c : decode_any W_9765c = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97660 : bv 32 := 0x001005b7.
Lemma F_97660 : fetch_word AsanUbsan.M.loaded_segments (0x97a78 : word) = Some W_97660.
Proof. vm_refl. Qed.
Lemma D_97660 : decode_any W_97660 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97664 : bv 32 := 0x02051513.
Lemma F_97664 : fetch_word AsanUbsan.M.loaded_segments (0x97a7c : word) = Some W_97664.
Proof. vm_refl. Qed.
Lemma D_97664 : decode_any W_97664 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97668 : bv 32 := 0x02055513.
Lemma F_97668 : fetch_word AsanUbsan.M.loaded_segments (0x97a80 : word) = Some W_97668.
Proof. vm_refl. Qed.
Lemma D_97668 : decode_any W_97668 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9766c : bv 32 := 0x00a90533.
Lemma F_9766c : fetch_word AsanUbsan.M.loaded_segments (0x97a84 : word) = Some W_9766c.
Proof. vm_refl. Qed.
Lemma D_9766c : decode_any W_9766c = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97670 : bv 32 := 0x00043603.
Lemma F_97670 : fetch_word AsanUbsan.M.loaded_segments (0x97a88 : word) = Some W_97670.
Proof. vm_refl. Qed.
Lemma D_97670 : decode_any W_97670 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97674 : bv 32 := 0x00b54533.
Lemma F_97674 : fetch_word AsanUbsan.M.loaded_segments (0x97a8c : word) = Some W_97674.
Proof. vm_refl. Qed.
Lemma D_97674 : decode_any W_97674 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97678 : bv 32 := 0x00012583.
Lemma F_97678 : fetch_word AsanUbsan.M.loaded_segments (0x97a90 : word) = Some W_97678.
Proof. vm_refl. Qed.
Lemma D_97678 : decode_any W_97678 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9767c : bv 32 := 0x00153513.
Lemma F_9767c : fetch_word AsanUbsan.M.loaded_segments (0x97a94 : word) = Some W_9767c.
Proof. vm_refl. Qed.
Lemma D_9767c : decode_any W_9767c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97680 : bv 32 := 0x00a60533.
Lemma F_97680 : fetch_word AsanUbsan.M.loaded_segments (0x97a98 : word) = Some W_97680.
Proof. vm_refl. Qed.
Lemma D_97680 : decode_any W_97680 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97684 : bv 32 := 0x00a43023.
Lemma F_97684 : fetch_word AsanUbsan.M.loaded_segments (0x97a9c : word) = Some W_97684.
Proof. vm_refl. Qed.
Lemma D_97684 : decode_any W_97684 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97688 : bv 32 := 0x0015851b.
Lemma F_97688 : fetch_word AsanUbsan.M.loaded_segments (0x97aa0 : word) = Some W_97688.
Proof. vm_refl. Qed.
Lemma D_97688 : decode_any W_97688 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9768c : bv 32 := 0x03813083.
Lemma F_9768c : fetch_word AsanUbsan.M.loaded_segments (0x97aa4 : word) = Some W_9768c.
Proof. vm_refl. Qed.
Lemma D_9768c : decode_any W_9768c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97690 : bv 32 := 0x03013403.
Lemma F_97690 : fetch_word AsanUbsan.M.loaded_segments (0x97aa8 : word) = Some W_97690.
Proof. vm_refl. Qed.
Lemma D_97690 : decode_any W_97690 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97694 : bv 32 := 0x02813483.
Lemma F_97694 : fetch_word AsanUbsan.M.loaded_segments (0x97aac : word) = Some W_97694.
Proof. vm_refl. Qed.
Lemma D_97694 : decode_any W_97694 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97698 : bv 32 := 0x02013903.
Lemma F_97698 : fetch_word AsanUbsan.M.loaded_segments (0x97ab0 : word) = Some W_97698.
Proof. vm_refl. Qed.
Lemma D_97698 : decode_any W_97698 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9769c : bv 32 := 0x01813983.
Lemma F_9769c : fetch_word AsanUbsan.M.loaded_segments (0x97ab4 : word) = Some W_9769c.
Proof. vm_refl. Qed.
Lemma D_9769c : decode_any W_9769c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976a0 : bv 32 := 0x01013a03.
Lemma F_976a0 : fetch_word AsanUbsan.M.loaded_segments (0x97ab8 : word) = Some W_976a0.
Proof. vm_refl. Qed.
Lemma D_976a0 : decode_any W_976a0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976a4 : bv 32 := 0x00813a83.
Lemma F_976a4 : fetch_word AsanUbsan.M.loaded_segments (0x97abc : word) = Some W_976a4.
Proof. vm_refl. Qed.
Lemma D_976a4 : decode_any W_976a4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976a8 : bv 32 := 0x04010113.
Lemma F_976a8 : fetch_word AsanUbsan.M.loaded_segments (0x97ac0 : word) = Some W_976a8.
Proof. vm_refl. Qed.
Lemma D_976a8 : decode_any W_976a8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976ac : bv 32 := 0x00008067.
Lemma F_976ac : fetch_word AsanUbsan.M.loaded_segments (0x97ac4 : word) = Some W_976ac.
Proof. vm_refl. Qed.
Lemma D_976ac : decode_any W_976ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976d4 : bv 32 := 0xff010113.
Lemma F_976d4 : fetch_word AsanUbsan.M.loaded_segments (0x97aec : word) = Some W_976d4.
Proof. vm_refl. Qed.
Lemma D_976d4 : decode_any W_976d4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976d8 : bv 32 := 0x00113423.
Lemma F_976d8 : fetch_word AsanUbsan.M.loaded_segments (0x97af0 : word) = Some W_976d8.
Proof. vm_refl. Qed.
Lemma D_976d8 : decode_any W_976d8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976dc : bv 32 := 0x00813023.
Lemma F_976dc : fetch_word AsanUbsan.M.loaded_segments (0x97af4 : word) = Some W_976dc.
Proof. vm_refl. Qed.
Lemma D_976dc : decode_any W_976dc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976e0 : bv 32 := 0x00058793.
Lemma F_976e0 : fetch_word AsanUbsan.M.loaded_segments (0x97af8 : word) = Some W_976e0.
Proof. vm_refl. Qed.
Lemma D_976e0 : decode_any W_976e0 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976e4 : bv 32 := 0x00050593.
Lemma F_976e4 : fetch_word AsanUbsan.M.loaded_segments (0x97afc : word) = Some W_976e4.
Proof. vm_refl. Qed.
Lemma D_976e4 : decode_any W_976e4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976e8 : bv 32 := 0x00f5342f.
Lemma F_976e8 : fetch_word AsanUbsan.M.loaded_segments (0x97b00 : word) = Some W_976e8.
Proof. vm_refl. Qed.
Lemma D_976e8 : decode_any W_976e8 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976ec : bv 32 := 0xfff78513.
Lemma F_976ec : fetch_word AsanUbsan.M.loaded_segments (0x97b04 : word) = Some W_976ec.
Proof. vm_refl. Qed.
Lemma D_976ec : decode_any W_976ec = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976f0 : bv 32 := 0x01445293.
Lemma F_976f0 : fetch_word AsanUbsan.M.loaded_segments (0x97b08 : word) = Some W_976f0.
Proof. vm_refl. Qed.
Lemma D_976f0 : decode_any W_976f0 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976f4 : bv 32 := 0x00850733.
Lemma F_976f4 : fetch_word AsanUbsan.M.loaded_segments (0x97b0c : word) = Some W_976f4.
Proof. vm_refl. Qed.
Lemma D_976f4 : decode_any W_976f4 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976f8 : bv 32 := 0x01475313.
Lemma F_976f8 : fetch_word AsanUbsan.M.loaded_segments (0x97b10 : word) = Some W_976f8.
Proof. vm_refl. Qed.
Lemma D_976f8 : decode_any W_976f8 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_976fc : bv 32 := 0x04629863.
Lemma F_976fc : fetch_word AsanUbsan.M.loaded_segments (0x97b14 : word) = Some W_976fc.
Proof. vm_refl. Qed.
Lemma D_976fc : decode_any W_976fc = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97700 : bv 32 := 0x02045513.
Lemma F_97700 : fetch_word AsanUbsan.M.loaded_segments (0x97b18 : word) = Some W_97700.
Proof. vm_refl. Qed.
Lemma D_97700 : decode_any W_97700 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97704 : bv 32 := 0x00050c63.
Lemma F_97704 : fetch_word AsanUbsan.M.loaded_segments (0x97b1c : word) = Some W_97704.
Proof. vm_refl. Qed.
Lemma D_97704 : decode_any W_97704 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9771c : bv 32 := 0x00863023.
Lemma F_9771c : fetch_word AsanUbsan.M.loaded_segments (0x97b34 : word) = Some W_9771c.
Proof. vm_refl. Qed.
Lemma D_9771c : decode_any W_9771c = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97720 : bv 32 := 0x00429613.
Lemma F_97720 : fetch_word AsanUbsan.M.loaded_segments (0x97b38 : word) = Some W_97720.
Proof. vm_refl. Qed.
Lemma D_97720 : decode_any W_97720 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97724 : bv 32 := 0x00c58633.
Lemma F_97724 : fetch_word AsanUbsan.M.loaded_segments (0x97b3c : word) = Some W_97724.
Proof. vm_refl. Qed.
Lemma D_97724 : decode_any W_97724 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97728 : bv 32 := 0x01063503.
Lemma F_97728 : fetch_word AsanUbsan.M.loaded_segments (0x97b40 : word) = Some W_97728.
Proof. vm_refl. Qed.
Lemma D_97728 : decode_any W_97728 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9772c : bv 32 := 0x0a050a63.
Lemma F_9772c : fetch_word AsanUbsan.M.loaded_segments (0x97b44 : word) = Some W_9772c.
Proof. vm_refl. Qed.
Lemma D_9772c : decode_any W_9772c = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97730 : bv 32 := 0x02c41413.
Lemma F_97730 : fetch_word AsanUbsan.M.loaded_segments (0x97b48 : word) = Some W_97730.
Proof. vm_refl. Qed.
Lemma D_97730 : decode_any W_97730 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97734 : bv 32 := 0x02945413.
Lemma F_97734 : fetch_word AsanUbsan.M.loaded_segments (0x97b4c : word) = Some W_97734.
Proof. vm_refl. Qed.
Lemma D_97734 : decode_any W_97734 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97738 : bv 32 := 0x00850533.
Lemma F_97738 : fetch_word AsanUbsan.M.loaded_segments (0x97b50 : word) = Some W_97738.
Proof. vm_refl. Qed.
Lemma D_97738 : decode_any W_97738 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9773c : bv 32 := 0x00813083.
Lemma F_9773c : fetch_word AsanUbsan.M.loaded_segments (0x97b54 : word) = Some W_9773c.
Proof. vm_refl. Qed.
Lemma D_9773c : decode_any W_9773c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97740 : bv 32 := 0x00013403.
Lemma F_97740 : fetch_word AsanUbsan.M.loaded_segments (0x97b58 : word) = Some W_97740.
Proof. vm_refl. Qed.
Lemma D_97740 : decode_any W_97740 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97744 : bv 32 := 0x01010113.
Lemma F_97744 : fetch_word AsanUbsan.M.loaded_segments (0x97b5c : word) = Some W_97744.
Proof. vm_refl. Qed.
Lemma D_97744 : decode_any W_97744 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97748 : bv 32 := 0x00008067.
Lemma F_97748 : fetch_word AsanUbsan.M.loaded_segments (0x97b60 : word) = Some W_97748.
Proof. vm_refl. Qed.
Lemma D_97748 : decode_any W_97748 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
