(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_38288 : bv 32 := 0x00195593.
Lemma F_38288 : fetch_word AsanUbsan.M.loaded_segments (0x38288 : word) = Some W_38288.
Proof. vm_refl. Qed.
Lemma D_38288 : decode_any W_38288 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3828c : bv 32 := 0x55555637.
Lemma F_3828c : fetch_word AsanUbsan.M.loaded_segments (0x3828c : word) = Some W_3828c.
Proof. vm_refl. Qed.
Lemma D_3828c : decode_any W_3828c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38290 : bv 32 := 0x33333737.
Lemma F_38290 : fetch_word AsanUbsan.M.loaded_segments (0x38290 : word) = Some W_38290.
Proof. vm_refl. Qed.
Lemma D_38290 : decode_any W_38290 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38294 : bv 32 := 0x0f0f17b7.
Lemma F_38294 : fetch_word AsanUbsan.M.loaded_segments (0x38294 : word) = Some W_38294.
Proof. vm_refl. Qed.
Lemma D_38294 : decode_any W_38294 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38298 : bv 32 := 0x00b965b3.
Lemma F_38298 : fetch_word AsanUbsan.M.loaded_segments (0x38298 : word) = Some W_38298.
Proof. vm_refl. Qed.
Lemma D_38298 : decode_any W_38298 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3829c : bv 32 := 0x5556061b.
Lemma F_3829c : fetch_word AsanUbsan.M.loaded_segments (0x3829c : word) = Some W_3829c.
Proof. vm_refl. Qed.
Lemma D_3829c : decode_any W_3829c = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382a0 : bv 32 := 0x3337071b.
Lemma F_382a0 : fetch_word AsanUbsan.M.loaded_segments (0x382a0 : word) = Some W_382a0.
Proof. vm_refl. Qed.
Lemma D_382a0 : decode_any W_382a0 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382a4 : bv 32 := 0xf0f7879b.
Lemma F_382a4 : fetch_word AsanUbsan.M.loaded_segments (0x382a4 : word) = Some W_382a4.
Proof. vm_refl. Qed.
Lemma D_382a4 : decode_any W_382a4 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382a8 : bv 32 := 0x0025d813.
Lemma F_382a8 : fetch_word AsanUbsan.M.loaded_segments (0x382a8 : word) = Some W_382a8.
Proof. vm_refl. Qed.
Lemma D_382a8 : decode_any W_382a8 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382ac : bv 32 := 0x0105e5b3.
Lemma F_382ac : fetch_word AsanUbsan.M.loaded_segments (0x382ac : word) = Some W_382ac.
Proof. vm_refl. Qed.
Lemma D_382ac : decode_any W_382ac = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382b0 : bv 32 := 0x02061813.
Lemma F_382b0 : fetch_word AsanUbsan.M.loaded_segments (0x382b0 : word) = Some W_382b0.
Proof. vm_refl. Qed.
Lemma D_382b0 : decode_any W_382b0 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382b4 : bv 32 := 0x01060633.
Lemma F_382b4 : fetch_word AsanUbsan.M.loaded_segments (0x382b4 : word) = Some W_382b4.
Proof. vm_refl. Qed.
Lemma D_382b4 : decode_any W_382b4 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382b8 : bv 32 := 0x02071813.
Lemma F_382b8 : fetch_word AsanUbsan.M.loaded_segments (0x382b8 : word) = Some W_382b8.
Proof. vm_refl. Qed.
Lemma D_382b8 : decode_any W_382b8 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382bc : bv 32 := 0x01070733.
Lemma F_382bc : fetch_word AsanUbsan.M.loaded_segments (0x382bc : word) = Some W_382bc.
Proof. vm_refl. Qed.
Lemma D_382bc : decode_any W_382bc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382c0 : bv 32 := 0x02079813.
Lemma F_382c0 : fetch_word AsanUbsan.M.loaded_segments (0x382c0 : word) = Some W_382c0.
Proof. vm_refl. Qed.
Lemma D_382c0 : decode_any W_382c0 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382c4 : bv 32 := 0x010787b3.
Lemma F_382c4 : fetch_word AsanUbsan.M.loaded_segments (0x382c4 : word) = Some W_382c4.
Proof. vm_refl. Qed.
Lemma D_382c4 : decode_any W_382c4 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382c8 : bv 32 := 0x0045d813.
Lemma F_382c8 : fetch_word AsanUbsan.M.loaded_segments (0x382c8 : word) = Some W_382c8.
Proof. vm_refl. Qed.
Lemma D_382c8 : decode_any W_382c8 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382cc : bv 32 := 0x0105e5b3.
Lemma F_382cc : fetch_word AsanUbsan.M.loaded_segments (0x382cc : word) = Some W_382cc.
Proof. vm_refl. Qed.
Lemma D_382cc : decode_any W_382cc = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382d0 : bv 32 := 0x0085d813.
Lemma F_382d0 : fetch_word AsanUbsan.M.loaded_segments (0x382d0 : word) = Some W_382d0.
Proof. vm_refl. Qed.
Lemma D_382d0 : decode_any W_382d0 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382d4 : bv 32 := 0x0105e5b3.
Lemma F_382d4 : fetch_word AsanUbsan.M.loaded_segments (0x382d4 : word) = Some W_382d4.
Proof. vm_refl. Qed.
Lemma D_382d4 : decode_any W_382d4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382d8 : bv 32 := 0x0105d813.
Lemma F_382d8 : fetch_word AsanUbsan.M.loaded_segments (0x382d8 : word) = Some W_382d8.
Proof. vm_refl. Qed.
Lemma D_382d8 : decode_any W_382d8 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382dc : bv 32 := 0x0105e5b3.
Lemma F_382dc : fetch_word AsanUbsan.M.loaded_segments (0x382dc : word) = Some W_382dc.
Proof. vm_refl. Qed.
Lemma D_382dc : decode_any W_382dc = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382e0 : bv 32 := 0x0205d813.
Lemma F_382e0 : fetch_word AsanUbsan.M.loaded_segments (0x382e0 : word) = Some W_382e0.
Proof. vm_refl. Qed.
Lemma D_382e0 : decode_any W_382e0 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382e4 : bv 32 := 0x0105e5b3.
Lemma F_382e4 : fetch_word AsanUbsan.M.loaded_segments (0x382e4 : word) = Some W_382e4.
Proof. vm_refl. Qed.
Lemma D_382e4 : decode_any W_382e4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382e8 : bv 32 := 0xfff5c593.
Lemma F_382e8 : fetch_word AsanUbsan.M.loaded_segments (0x382e8 : word) = Some W_382e8.
Proof. vm_refl. Qed.
Lemma D_382e8 : decode_any W_382e8 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382ec : bv 32 := 0x0015d813.
Lemma F_382ec : fetch_word AsanUbsan.M.loaded_segments (0x382ec : word) = Some W_382ec.
Proof. vm_refl. Qed.
Lemma D_382ec : decode_any W_382ec = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382f0 : bv 32 := 0x00c87633.
Lemma F_382f0 : fetch_word AsanUbsan.M.loaded_segments (0x382f0 : word) = Some W_382f0.
Proof. vm_refl. Qed.
Lemma D_382f0 : decode_any W_382f0 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382f4 : bv 32 := 0x01010837.
Lemma F_382f4 : fetch_word AsanUbsan.M.loaded_segments (0x382f4 : word) = Some W_382f4.
Proof. vm_refl. Qed.
Lemma D_382f4 : decode_any W_382f4 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382f8 : bv 32 := 0x40c585b3.
Lemma F_382f8 : fetch_word AsanUbsan.M.loaded_segments (0x382f8 : word) = Some W_382f8.
Proof. vm_refl. Qed.
Lemma D_382f8 : decode_any W_382f8 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_382fc : bv 32 := 0x0025d613.
Lemma F_382fc : fetch_word AsanUbsan.M.loaded_segments (0x382fc : word) = Some W_382fc.
Proof. vm_refl. Qed.
Lemma D_382fc : decode_any W_382fc = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38300 : bv 32 := 0x00e5f5b3.
Lemma F_38300 : fetch_word AsanUbsan.M.loaded_segments (0x38300 : word) = Some W_38300.
Proof. vm_refl. Qed.
Lemma D_38300 : decode_any W_38300 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38304 : bv 32 := 0x00e67633.
Lemma F_38304 : fetch_word AsanUbsan.M.loaded_segments (0x38304 : word) = Some W_38304.
Proof. vm_refl. Qed.
Lemma D_38304 : decode_any W_38304 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38308 : bv 32 := 0x0304b703.
Lemma F_38308 : fetch_word AsanUbsan.M.loaded_segments (0x38308 : word) = Some W_38308.
Proof. vm_refl. Qed.
Lemma D_38308 : decode_any W_38308 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3830c : bv 32 := 0x1018081b.
Lemma F_3830c : fetch_word AsanUbsan.M.loaded_segments (0x3830c : word) = Some W_3830c.
Proof. vm_refl. Qed.
Lemma D_3830c : decode_any W_3830c = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38310 : bv 32 := 0x00c585b3.
Lemma F_38310 : fetch_word AsanUbsan.M.loaded_segments (0x38310 : word) = Some W_38310.
Proof. vm_refl. Qed.
Lemma D_38310 : decode_any W_38310 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38314 : bv 32 := 0x0045d613.
Lemma F_38314 : fetch_word AsanUbsan.M.loaded_segments (0x38314 : word) = Some W_38314.
Proof. vm_refl. Qed.
Lemma D_38314 : decode_any W_38314 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38318 : bv 32 := 0x00c585b3.
Lemma F_38318 : fetch_word AsanUbsan.M.loaded_segments (0x38318 : word) = Some W_38318.
Proof. vm_refl. Qed.
Lemma D_38318 : decode_any W_38318 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3831c : bv 32 := 0x02081613.
Lemma F_3831c : fetch_word AsanUbsan.M.loaded_segments (0x3831c : word) = Some W_3831c.
Proof. vm_refl. Qed.
Lemma D_3831c : decode_any W_3831c = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38320 : bv 32 := 0x00f5f5b3.
Lemma F_38320 : fetch_word AsanUbsan.M.loaded_segments (0x38320 : word) = Some W_38320.
Proof. vm_refl. Qed.
Lemma D_38320 : decode_any W_38320 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38324 : bv 32 := 0x00c80633.
Lemma F_38324 : fetch_word AsanUbsan.M.loaded_segments (0x38324 : word) = Some W_38324.
Proof. vm_refl. Qed.
Lemma D_38324 : decode_any W_38324 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38328 : bv 32 := 0x02c585b3.
Lemma F_38328 : fetch_word AsanUbsan.M.loaded_segments (0x38328 : word) = Some W_38328.
Proof. vm_refl. Qed.
Lemma D_38328 : decode_any W_38328 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3832c : bv 32 := 0x0385d993.
Lemma F_3832c : fetch_word AsanUbsan.M.loaded_segments (0x3832c : word) = Some W_3832c.
Proof. vm_refl. Qed.
Lemma D_3832c : decode_any W_3832c = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38330 : bv 32 := 0x1ce68c63.
Lemma F_38330 : fetch_word AsanUbsan.M.loaded_segments (0x38330 : word) = Some W_38330.
Proof. vm_refl. Qed.
Lemma D_38330 : decode_any W_38330 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38334 : bv 32 := 0x0084b603.
Lemma F_38334 : fetch_word AsanUbsan.M.loaded_segments (0x38334 : word) = Some W_38334.
Proof. vm_refl. Qed.
Lemma D_38334 : decode_any W_38334 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38338 : bv 32 := 0x03f9c593.
Lemma F_38338 : fetch_word AsanUbsan.M.loaded_segments (0x38338 : word) = Some W_38338.
Proof. vm_refl. Qed.
Lemma D_38338 : decode_any W_38338 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3833c : bv 32 := 0x00dabc23.
Lemma F_3833c : fetch_word AsanUbsan.M.loaded_segments (0x3833c : word) = Some W_3833c.
Proof. vm_refl. Qed.
Lemma D_3833c : decode_any W_3833c = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38340 : bv 32 := 0x00369713.
Lemma F_38340 : fetch_word AsanUbsan.M.loaded_segments (0x38340 : word) = Some W_38340.
Proof. vm_refl. Qed.
Lemma D_38340 : decode_any W_38340 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38344 : bv 32 := 0x00e60633.
Lemma F_38344 : fetch_word AsanUbsan.M.loaded_segments (0x38344 : word) = Some W_38344.
Proof. vm_refl. Qed.
Lemma D_38344 : decode_any W_38344 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38348 : bv 32 := 0x01563023.
Lemma F_38348 : fetch_word AsanUbsan.M.loaded_segments (0x38348 : word) = Some W_38348.
Proof. vm_refl. Qed.
Lemma D_38348 : decode_any W_38348 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3834c : bv 32 := 0x0484b703.
Lemma F_3834c : fetch_word AsanUbsan.M.loaded_segments (0x3834c : word) = Some W_3834c.
Proof. vm_refl. Qed.
Lemma D_3834c : decode_any W_3834c = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38350 : bv 32 := 0x0584b783.
Lemma F_38350 : fetch_word AsanUbsan.M.loaded_segments (0x38350 : word) = Some W_38350.
Proof. vm_refl. Qed.
Lemma D_38350 : decode_any W_38350 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38354 : bv 32 := 0x00168813.
Lemma F_38354 : fetch_word AsanUbsan.M.loaded_segments (0x38354 : word) = Some W_38354.
Proof. vm_refl. Qed.
Lemma D_38354 : decode_any W_38354 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38358 : bv 32 := 0x0604b603.
Lemma F_38358 : fetch_word AsanUbsan.M.loaded_segments (0x38358 : word) = Some W_38358.
Proof. vm_refl. Qed.
Lemma D_38358 : decode_any W_38358 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3835c : bv 32 := 0x00170713.
Lemma F_3835c : fetch_word AsanUbsan.M.loaded_segments (0x3835c : word) = Some W_3835c.
Proof. vm_refl. Qed.
Lemma D_3835c : decode_any W_3835c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38360 : bv 32 := 0x012786b3.
Lemma F_38360 : fetch_word AsanUbsan.M.loaded_segments (0x38360 : word) = Some W_38360.
Proof. vm_refl. Qed.
Lemma D_38360 : decode_any W_38360 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38364 : bv 32 := 0x0304bc23.
Lemma F_38364 : fetch_word AsanUbsan.M.loaded_segments (0x38364 : word) = Some W_38364.
Proof. vm_refl. Qed.
Lemma D_38364 : decode_any W_38364 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38368 : bv 32 := 0x04048023.
Lemma F_38368 : fetch_word AsanUbsan.M.loaded_segments (0x38368 : word) = Some W_38368.
Proof. vm_refl. Qed.
Lemma D_38368 : decode_any W_38368 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3836c : bv 32 := 0x04e4b423.
Lemma F_3836c : fetch_word AsanUbsan.M.loaded_segments (0x3836c : word) = Some W_3836c.
Proof. vm_refl. Qed.
Lemma D_3836c : decode_any W_3836c = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38370 : bv 32 := 0x04d4bc23.
Lemma F_38370 : fetch_word AsanUbsan.M.loaded_segments (0x38370 : word) = Some W_38370.
Proof. vm_refl. Qed.
Lemma D_38370 : decode_any W_38370 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38374 : bv 32 := 0x00c6e463.
Lemma F_38374 : fetch_word AsanUbsan.M.loaded_segments (0x38374 : word) = Some W_38374.
Proof. vm_refl. Qed.
Lemma D_38374 : decode_any W_38374 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38378 : bv 32 := 0x00068613.
Lemma F_38378 : fetch_word AsanUbsan.M.loaded_segments (0x38378 : word) = Some W_38378.
Proof. vm_refl. Qed.
Lemma D_38378 : decode_any W_38378 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3837c : bv 32 := 0x00359593.
Lemma F_3837c : fetch_word AsanUbsan.M.loaded_segments (0x3837c : word) = Some W_3837c.
Proof. vm_refl. Qed.
Lemma D_3837c : decode_any W_3837c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38380 : bv 32 := 0x00b485b3.
Lemma F_38380 : fetch_word AsanUbsan.M.loaded_segments (0x38380 : word) = Some W_38380.
Proof. vm_refl. Qed.
Lemma D_38380 : decode_any W_38380 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38384 : bv 32 := 0x0685b683.
Lemma F_38384 : fetch_word AsanUbsan.M.loaded_segments (0x38384 : word) = Some W_38384.
Proof. vm_refl. Qed.
Lemma D_38384 : decode_any W_38384 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38388 : bv 32 := 0x00168693.
Lemma F_38388 : fetch_word AsanUbsan.M.loaded_segments (0x38388 : word) = Some W_38388.
Proof. vm_refl. Qed.
Lemma D_38388 : decode_any W_38388 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3838c : bv 32 := 0x06c4b023.
Lemma F_3838c : fetch_word AsanUbsan.M.loaded_segments (0x3838c : word) = Some W_3838c.
Proof. vm_refl. Qed.
Lemma D_3838c : decode_any W_3838c = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38390 : bv 32 := 0x06d5b423.
Lemma F_38390 : fetch_word AsanUbsan.M.loaded_segments (0x38390 : word) = Some W_38390.
Proof. vm_refl. Qed.
Lemma D_38390 : decode_any W_38390 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_38394 : bv 32 := 0x01040593.
Lemma F_38394 : fetch_word AsanUbsan.M.loaded_segments (0x38394 : word) = Some W_38394.
Proof. vm_refl. Qed.
Lemma D_38394 : decode_any W_38394 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.
