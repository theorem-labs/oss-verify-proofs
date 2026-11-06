(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition Wx_80abc : bv 32 := 0x2590006f.
Lemma Fx_80abc : fetch_word AsanUbsan.M.loaded_segments (0x80b04 : word) = Some Wx_80abc.
Proof. vm_refl. Qed.
Lemma Dx_80abc : decode_any Wx_80abc = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_81514 : bv 32 := 0x81010113.
Lemma Fx_81514 : fetch_word AsanUbsan.M.loaded_segments (0x8155c : word) = Some Wx_81514.
Proof. vm_refl. Qed.
Lemma Dx_81514 : decode_any Wx_81514 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81518 : bv 32 := 0x7e113423.
Lemma Fx_81518 : fetch_word AsanUbsan.M.loaded_segments (0x81560 : word) = Some Wx_81518.
Proof. vm_refl. Qed.
Lemma Dx_81518 : decode_any Wx_81518 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8151c : bv 32 := 0x7e813023.
Lemma Fx_8151c : fetch_word AsanUbsan.M.loaded_segments (0x81564 : word) = Some Wx_8151c.
Proof. vm_refl. Qed.
Lemma Dx_8151c : decode_any Wx_8151c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81520 : bv 32 := 0x7c913c23.
Lemma Fx_81520 : fetch_word AsanUbsan.M.loaded_segments (0x81568 : word) = Some Wx_81520.
Proof. vm_refl. Qed.
Lemma Dx_81520 : decode_any Wx_81520 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81524 : bv 32 := 0x7d213823.
Lemma Fx_81524 : fetch_word AsanUbsan.M.loaded_segments (0x8156c : word) = Some Wx_81524.
Proof. vm_refl. Qed.
Lemma Dx_81524 : decode_any Wx_81524 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81528 : bv 32 := 0x7d313423.
Lemma Fx_81528 : fetch_word AsanUbsan.M.loaded_segments (0x81570 : word) = Some Wx_81528.
Proof. vm_refl. Qed.
Lemma Dx_81528 : decode_any Wx_81528 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8152c : bv 32 := 0x7d413023.
Lemma Fx_8152c : fetch_word AsanUbsan.M.loaded_segments (0x81574 : word) = Some Wx_8152c.
Proof. vm_refl. Qed.
Lemma Dx_8152c : decode_any Wx_8152c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81530 : bv 32 := 0x7b513c23.
Lemma Fx_81530 : fetch_word AsanUbsan.M.loaded_segments (0x81578 : word) = Some Wx_81530.
Proof. vm_refl. Qed.
Lemma Dx_81530 : decode_any Wx_81530 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81534 : bv 32 := 0x7b613823.
Lemma Fx_81534 : fetch_word AsanUbsan.M.loaded_segments (0x8157c : word) = Some Wx_81534.
Proof. vm_refl. Qed.
Lemma Dx_81534 : decode_any Wx_81534 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81538 : bv 32 := 0x7f010413.
Lemma Fx_81538 : fetch_word AsanUbsan.M.loaded_segments (0x81580 : word) = Some Wx_81538.
Proof. vm_refl. Qed.
Lemma Dx_81538 : decode_any Wx_81538 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8153c : bv 32 := 0xf9010113.
Lemma Fx_8153c : fetch_word AsanUbsan.M.loaded_segments (0x81584 : word) = Some Wx_8153c.
Proof. vm_refl. Qed.
Lemma Dx_8153c : decode_any Wx_8153c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81540 : bv 32 := 0x000e4697.
Lemma Fx_81540 : fetch_word AsanUbsan.M.loaded_segments (0x81588 : word) = Some Wx_81540.
Proof. vm_refl. Qed.
Lemma Dx_81540 : decode_any Wx_81540 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81544 : bv 32 := 0xaf86b683.
Lemma Fx_81544 : fetch_word AsanUbsan.M.loaded_segments (0x8158c : word) = Some Wx_81544.
Proof. vm_refl. Qed.
Lemma Dx_81544 : decode_any Wx_81544 = Some (Load SZ8 true 13 13 2808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81548 : bv 32 := 0x0006c683.
Lemma Fx_81548 : fetch_word AsanUbsan.M.loaded_segments (0x81590 : word) = Some Wx_81548.
Proof. vm_refl. Qed.
Lemma Dx_81548 : decode_any Wx_81548 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8154c : bv 32 := 0x08068a63.
Lemma Fx_8154c : fetch_word AsanUbsan.M.loaded_segments (0x81594 : word) = Some Wx_8154c.
Proof. vm_refl. Qed.
Lemma Dx_8154c : decode_any Wx_8154c = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81550 : bv 32 := 0xfff54693.
Lemma Fx_81550 : fetch_word AsanUbsan.M.loaded_segments (0x81598 : word) = Some Wx_81550.
Proof. vm_refl. Qed.
Lemma Dx_81550 : decode_any Wx_81550 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81554 : bv 32 := 0x80040a93.
Lemma Fx_81554 : fetch_word AsanUbsan.M.loaded_segments (0x8159c : word) = Some Wx_81554.
Proof. vm_refl. Qed.
Lemma Dx_81554 : decode_any Wx_81554 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81558 : bv 32 := 0xfa8a8a93.
Lemma Fx_81558 : fetch_word AsanUbsan.M.loaded_segments (0x815a0 : word) = Some Wx_81558.
Proof. vm_refl. Qed.
Lemma Dx_81558 : decode_any Wx_81558 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8155c : bv 32 := 0x0cc6ea63.
Lemma Fx_8155c : fetch_word AsanUbsan.M.loaded_segments (0x815a4 : word) = Some Wx_8155c.
Proof. vm_refl. Qed.
Lemma Dx_8155c : decode_any Wx_8155c = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81560 : bv 32 := 0xfbf60693.
Lemma Fx_81560 : fetch_word AsanUbsan.M.loaded_segments (0x815a8 : word) = Some Wx_81560.
Proof. vm_refl. Qed.
Lemma Dx_81560 : decode_any Wx_81560 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81564 : bv 32 := 0xfbf00713.
Lemma Fx_81564 : fetch_word AsanUbsan.M.loaded_segments (0x815ac : word) = Some Wx_81564.
Proof. vm_refl. Qed.
Lemma Dx_81564 : decode_any Wx_81564 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81568 : bv 32 := 0x14d77863.
Lemma Fx_81568 : fetch_word AsanUbsan.M.loaded_segments (0x815b0 : word) = Some Wx_81568.
Proof. vm_refl. Qed.
Lemma Dx_81568 : decode_any Wx_81568 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8156c : bv 32 := 0x000e3697.
Lemma Fx_8156c : fetch_word AsanUbsan.M.loaded_segments (0x815b4 : word) = Some Wx_8156c.
Proof. vm_refl. Qed.
Lemma Dx_8156c : decode_any Wx_8156c = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81570 : bv 32 := 0xf646b683.
Lemma Fx_81570 : fetch_word AsanUbsan.M.loaded_segments (0x815b8 : word) = Some Wx_81570.
Proof. vm_refl. Qed.
Lemma Dx_81570 : decode_any Wx_81570 = Some (Load SZ8 true 13 13 3940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81574 : bv 32 := 0x00c507b3.
Lemma Fx_81574 : fetch_word AsanUbsan.M.loaded_segments (0x815bc : word) = Some Wx_81574.
Proof. vm_refl. Qed.
Lemma Dx_81574 : decode_any Wx_81574 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81578 : bv 32 := 0x0006b703.
Lemma Fx_81578 : fetch_word AsanUbsan.M.loaded_segments (0x815c0 : word) = Some Wx_81578.
Proof. vm_refl. Qed.
Lemma Dx_81578 : decode_any Wx_81578 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8157c : bv 32 := 0x00355693.
Lemma Fx_8157c : fetch_word AsanUbsan.M.loaded_segments (0x815c4 : word) = Some Wx_8157c.
Proof. vm_refl. Qed.
Lemma Dx_8157c : decode_any Wx_8157c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81580 : bv 32 := 0xfff78793.
Lemma Fx_81580 : fetch_word AsanUbsan.M.loaded_segments (0x815c8 : word) = Some Wx_81580.
Proof. vm_refl. Qed.
Lemma Dx_81580 : decode_any Wx_81580 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81584 : bv 32 := 0x0037d813.
Lemma Fx_81584 : fetch_word AsanUbsan.M.loaded_segments (0x815cc : word) = Some Wx_81584.
Proof. vm_refl. Qed.
Lemma Dx_81584 : decode_any Wx_81584 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81588 : bv 32 := 0x00d706b3.
Lemma Fx_81588 : fetch_word AsanUbsan.M.loaded_segments (0x815d0 : word) = Some Wx_81588.
Proof. vm_refl. Qed.
Lemma Dx_81588 : decode_any Wx_81588 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8158c : bv 32 := 0x01070733.
Lemma Fx_8158c : fetch_word AsanUbsan.M.loaded_segments (0x815d4 : word) = Some Wx_8158c.
Proof. vm_refl. Qed.
Lemma Dx_8158c : decode_any Wx_8158c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81590 : bv 32 := 0xff86f813.
Lemma Fx_81590 : fetch_word AsanUbsan.M.loaded_segments (0x815d8 : word) = Some Wx_81590.
Proof. vm_refl. Qed.
Lemma Dx_81590 : decode_any Wx_81590 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81594 : bv 32 := 0xff877893.
Lemma Fx_81594 : fetch_word AsanUbsan.M.loaded_segments (0x815dc : word) = Some Wx_81594.
Proof. vm_refl. Qed.
Lemma Dx_81594 : decode_any Wx_81594 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81598 : bv 32 := 0x00083803.
Lemma Fx_81598 : fetch_word AsanUbsan.M.loaded_segments (0x815e0 : word) = Some Wx_81598.
Proof. vm_refl. Qed.
Lemma Dx_81598 : decode_any Wx_81598 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8159c : bv 32 := 0x0008b883.
Lemma Fx_8159c : fetch_word AsanUbsan.M.loaded_segments (0x815e4 : word) = Some Wx_8159c.
Proof. vm_refl. Qed.
Lemma Dx_8159c : decode_any Wx_8159c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815a0 : bv 32 := 0x0108e833.
Lemma Fx_815a0 : fetch_word AsanUbsan.M.loaded_segments (0x815e8 : word) = Some Wx_815a0.
Proof. vm_refl. Qed.
Lemma Dx_815a0 : decode_any Wx_815a0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815a4 : bv 32 := 0x10081e63.
Lemma Fx_815a4 : fetch_word AsanUbsan.M.loaded_segments (0x815ec : word) = Some Wx_815a4.
Proof. vm_refl. Qed.
Lemma Dx_815a4 : decode_any Wx_815a4 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815a8 : bv 32 := 0x000e5697.
Lemma Fx_815a8 : fetch_word AsanUbsan.M.loaded_segments (0x815f0 : word) = Some Wx_815a8.
Proof. vm_refl. Qed.
Lemma Dx_815a8 : decode_any Wx_815a8 = Some (Auipc 13 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815ac : bv 32 := 0xf606b683.
Lemma Fx_815ac : fetch_word AsanUbsan.M.loaded_segments (0x815f4 : word) = Some Wx_815ac.
Proof. vm_refl. Qed.
Lemma Dx_815ac : decode_any Wx_815ac = Some (Load SZ8 true 13 13 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815b0 : bv 32 := 0x000680e7.
Lemma Fx_815b0 : fetch_word AsanUbsan.M.loaded_segments (0x815f8 : word) = Some Wx_815b0.
Proof. vm_refl. Qed.
Lemma Dx_815b0 : decode_any Wx_815b0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815b4 : bv 32 := 0x07010113.
Lemma Fx_815b4 : fetch_word AsanUbsan.M.loaded_segments (0x815fc : word) = Some Wx_815b4.
Proof. vm_refl. Qed.
Lemma Dx_815b4 : decode_any Wx_815b4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815b8 : bv 32 := 0x7e813083.
Lemma Fx_815b8 : fetch_word AsanUbsan.M.loaded_segments (0x81600 : word) = Some Wx_815b8.
Proof. vm_refl. Qed.
Lemma Dx_815b8 : decode_any Wx_815b8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815bc : bv 32 := 0x7e013403.
Lemma Fx_815bc : fetch_word AsanUbsan.M.loaded_segments (0x81604 : word) = Some Wx_815bc.
Proof. vm_refl. Qed.
Lemma Dx_815bc : decode_any Wx_815bc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815c0 : bv 32 := 0x7d813483.
Lemma Fx_815c0 : fetch_word AsanUbsan.M.loaded_segments (0x81608 : word) = Some Wx_815c0.
Proof. vm_refl. Qed.
Lemma Dx_815c0 : decode_any Wx_815c0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815c4 : bv 32 := 0x7d013903.
Lemma Fx_815c4 : fetch_word AsanUbsan.M.loaded_segments (0x8160c : word) = Some Wx_815c4.
Proof. vm_refl. Qed.
Lemma Dx_815c4 : decode_any Wx_815c4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815c8 : bv 32 := 0x7c813983.
Lemma Fx_815c8 : fetch_word AsanUbsan.M.loaded_segments (0x81610 : word) = Some Wx_815c8.
Proof. vm_refl. Qed.
Lemma Dx_815c8 : decode_any Wx_815c8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815cc : bv 32 := 0x7c013a03.
Lemma Fx_815cc : fetch_word AsanUbsan.M.loaded_segments (0x81614 : word) = Some Wx_815cc.
Proof. vm_refl. Qed.
Lemma Dx_815cc : decode_any Wx_815cc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815d0 : bv 32 := 0x7b813a83.
Lemma Fx_815d0 : fetch_word AsanUbsan.M.loaded_segments (0x81618 : word) = Some Wx_815d0.
Proof. vm_refl. Qed.
Lemma Dx_815d0 : decode_any Wx_815d0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815d4 : bv 32 := 0x7b013b03.
Lemma Fx_815d4 : fetch_word AsanUbsan.M.loaded_segments (0x8161c : word) = Some Wx_815d4.
Proof. vm_refl. Qed.
Lemma Dx_815d4 : decode_any Wx_815d4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815d8 : bv 32 := 0x7f010113.
Lemma Fx_815d8 : fetch_word AsanUbsan.M.loaded_segments (0x81620 : word) = Some Wx_815d8.
Proof. vm_refl. Qed.
Lemma Dx_815d8 : decode_any Wx_815d8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_815dc : bv 32 := 0x00008067.
Lemma Fx_815dc : fetch_word AsanUbsan.M.loaded_segments (0x81624 : word) = Some Wx_815dc.
Proof. vm_refl. Qed.
Lemma Dx_815dc : decode_any Wx_815dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816b8 : bv 32 := 0x02061e63.
Lemma Fx_816b8 : fetch_word AsanUbsan.M.loaded_segments (0x81700 : word) = Some Wx_816b8.
Proof. vm_refl. Qed.
Lemma Dx_816b8 : decode_any Wx_816b8 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816bc : bv 32 := 0xeedff06f.
Lemma Fx_816bc : fetch_word AsanUbsan.M.loaded_segments (0x81704 : word) = Some Wx_816bc.
Proof. vm_refl. Qed.
Lemma Dx_816bc : decode_any Wx_816bc = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816c0 : bv 32 := 0x00070803.
Lemma Fx_816c0 : fetch_word AsanUbsan.M.loaded_segments (0x81708 : word) = Some Wx_816c0.
Proof. vm_refl. Qed.
Lemma Dx_816c0 : decode_any Wx_816c0 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816c4 : bv 32 := 0x0077f793.
Lemma Fx_816c4 : fetch_word AsanUbsan.M.loaded_segments (0x8170c : word) = Some Wx_816c4.
Proof. vm_refl. Qed.
Lemma Dx_816c4 : decode_any Wx_816c4 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816c8 : bv 32 := 0x010038b3.
Lemma Fx_816c8 : fetch_word AsanUbsan.M.loaded_segments (0x81710 : word) = Some Wx_816c8.
Proof. vm_refl. Qed.
Lemma Dx_816c8 : decode_any Wx_816c8 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816cc : bv 32 := 0x0107a7b3.
Lemma Fx_816cc : fetch_word AsanUbsan.M.loaded_segments (0x81714 : word) = Some Wx_816cc.
Proof. vm_refl. Qed.
Lemma Dx_816cc : decode_any Wx_816cc = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816d0 : bv 32 := 0x0017c793.
Lemma Fx_816d0 : fetch_word AsanUbsan.M.loaded_segments (0x81718 : word) = Some Wx_816d0.
Proof. vm_refl. Qed.
Lemma Dx_816d0 : decode_any Wx_816d0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816d4 : bv 32 := 0x00f8f7b3.
Lemma Fx_816d4 : fetch_word AsanUbsan.M.loaded_segments (0x8171c : word) = Some Wx_816d4.
Proof. vm_refl. Qed.
Lemma Dx_816d4 : decode_any Wx_816d4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816d8 : bv 32 := 0x00e6fa63.
Lemma Fx_816d8 : fetch_word AsanUbsan.M.loaded_segments (0x81720 : word) = Some Wx_816d8.
Proof. vm_refl. Qed.
Lemma Dx_816d8 : decode_any Wx_816d8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816dc : bv 32 := 0x0006c803.
Lemma Fx_816dc : fetch_word AsanUbsan.M.loaded_segments (0x81724 : word) = Some Wx_816dc.
Proof. vm_refl. Qed.
Lemma Dx_816dc : decode_any Wx_816dc = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816e0 : bv 32 := 0x00168693.
Lemma Fx_816e0 : fetch_word AsanUbsan.M.loaded_segments (0x81728 : word) = Some Wx_816e0.
Proof. vm_refl. Qed.
Lemma Dx_816e0 : decode_any Wx_816e0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816e4 : bv 32 := 0x00f867b3.
Lemma Fx_816e4 : fetch_word AsanUbsan.M.loaded_segments (0x8172c : word) = Some Wx_816e4.
Proof. vm_refl. Qed.
Lemma Dx_816e4 : decode_any Wx_816e4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816e8 : bv 32 := 0xfee69ae3.
Lemma Fx_816e8 : fetch_word AsanUbsan.M.loaded_segments (0x81730 : word) = Some Wx_816e8.
Proof. vm_refl. Qed.
Lemma Dx_816e8 : decode_any Wx_816e8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816ec : bv 32 := 0x0ff7f693.
Lemma Fx_816ec : fetch_word AsanUbsan.M.loaded_segments (0x81734 : word) = Some Wx_816ec.
Proof. vm_refl. Qed.
Lemma Dx_816ec : decode_any Wx_816ec = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816f0 : bv 32 := 0xea068ce3.
Lemma Fx_816f0 : fetch_word AsanUbsan.M.loaded_segments (0x81738 : word) = Some Wx_816f0.
Proof. vm_refl. Qed.
Lemma Dx_816f0 : decode_any Wx_816f0 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816f4 : bv 32 := 0x00050493.
Lemma Fx_816f4 : fetch_word AsanUbsan.M.loaded_segments (0x8173c : word) = Some Wx_816f4.
Proof. vm_refl. Qed.
Lemma Dx_816f4 : decode_any Wx_816f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816f8 : bv 32 := 0x00058b13.
Lemma Fx_816f8 : fetch_word AsanUbsan.M.loaded_segments (0x81740 : word) = Some Wx_816f8.
Proof. vm_refl. Qed.
Lemma Dx_816f8 : decode_any Wx_816f8 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_816fc : bv 32 := 0x00060593.
Lemma Fx_816fc : fetch_word AsanUbsan.M.loaded_segments (0x81744 : word) = Some Wx_816fc.
Proof. vm_refl. Qed.
Lemma Dx_816fc : decode_any Wx_816fc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81700 : bv 32 := 0x00060913.
Lemma Fx_81700 : fetch_word AsanUbsan.M.loaded_segments (0x81748 : word) = Some Wx_81700.
Proof. vm_refl. Qed.
Lemma Dx_81700 : decode_any Wx_81700 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81704 : bv 32 := 0x3f1020ef.
Lemma Fx_81704 : fetch_word AsanUbsan.M.loaded_segments (0x8174c : word) = Some Wx_81704.
Proof. vm_refl. Qed.
Lemma Dx_81704 : decode_any Wx_81704 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81708 : bv 32 := 0x000b0593.
Lemma Fx_81708 : fetch_word AsanUbsan.M.loaded_segments (0x81750 : word) = Some Wx_81708.
Proof. vm_refl. Qed.
Lemma Dx_81708 : decode_any Wx_81708 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8170c : bv 32 := 0x00090613.
Lemma Fx_8170c : fetch_word AsanUbsan.M.loaded_segments (0x81754 : word) = Some Wx_8170c.
Proof. vm_refl. Qed.
Lemma Dx_8170c : decode_any Wx_8170c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81710 : bv 32 := 0x00050993.
Lemma Fx_81710 : fetch_word AsanUbsan.M.loaded_segments (0x81758 : word) = Some Wx_81710.
Proof. vm_refl. Qed.
Lemma Dx_81710 : decode_any Wx_81710 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81714 : bv 32 := 0x00048513.
Lemma Fx_81714 : fetch_word AsanUbsan.M.loaded_segments (0x8175c : word) = Some Wx_81714.
Proof. vm_refl. Qed.
Lemma Dx_81714 : decode_any Wx_81714 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_81718 : bv 32 := 0xe80988e3.
Lemma Fx_81718 : fetch_word AsanUbsan.M.loaded_segments (0x81760 : word) = Some Wx_81718.
Proof. vm_refl. Qed.
Lemma Dx_81718 : decode_any Wx_81718 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

