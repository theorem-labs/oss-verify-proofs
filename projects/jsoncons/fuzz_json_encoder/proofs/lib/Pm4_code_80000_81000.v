(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_801e8 : bv 32 := 0x5450006f.
Lemma F_801e8 : fetch_word Asan.M.loaded_segments (0x80238 : word) = Some W_801e8.
Proof. vm_refl. Qed.
Lemma D_801e8 : decode_any W_801e8 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_801ec : bv 32 := 0x2000106f.
Lemma F_801ec : fetch_word Asan.M.loaded_segments (0x8023c : word) = Some W_801ec.
Proof. vm_refl. Qed.
Lemma D_801ec : decode_any W_801ec = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_801f0 : bv 32 := 0x81010113.
Lemma F_801f0 : fetch_word Asan.M.loaded_segments (0x80240 : word) = Some W_801f0.
Proof. vm_refl. Qed.
Lemma D_801f0 : decode_any W_801f0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_801f4 : bv 32 := 0x7e113423.
Lemma F_801f4 : fetch_word Asan.M.loaded_segments (0x80244 : word) = Some W_801f4.
Proof. vm_refl. Qed.
Lemma D_801f4 : decode_any W_801f4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_801f8 : bv 32 := 0x7e813023.
Lemma F_801f8 : fetch_word Asan.M.loaded_segments (0x80248 : word) = Some W_801f8.
Proof. vm_refl. Qed.
Lemma D_801f8 : decode_any W_801f8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_801fc : bv 32 := 0x7c913c23.
Lemma F_801fc : fetch_word Asan.M.loaded_segments (0x8024c : word) = Some W_801fc.
Proof. vm_refl. Qed.
Lemma D_801fc : decode_any W_801fc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80200 : bv 32 := 0x7d213823.
Lemma F_80200 : fetch_word Asan.M.loaded_segments (0x80250 : word) = Some W_80200.
Proof. vm_refl. Qed.
Lemma D_80200 : decode_any W_80200 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80204 : bv 32 := 0x7d313423.
Lemma F_80204 : fetch_word Asan.M.loaded_segments (0x80254 : word) = Some W_80204.
Proof. vm_refl. Qed.
Lemma D_80204 : decode_any W_80204 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80208 : bv 32 := 0x7d413023.
Lemma F_80208 : fetch_word Asan.M.loaded_segments (0x80258 : word) = Some W_80208.
Proof. vm_refl. Qed.
Lemma D_80208 : decode_any W_80208 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8020c : bv 32 := 0x7b513c23.
Lemma F_8020c : fetch_word Asan.M.loaded_segments (0x8025c : word) = Some W_8020c.
Proof. vm_refl. Qed.
Lemma D_8020c : decode_any W_8020c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80210 : bv 32 := 0x7b613823.
Lemma F_80210 : fetch_word Asan.M.loaded_segments (0x80260 : word) = Some W_80210.
Proof. vm_refl. Qed.
Lemma D_80210 : decode_any W_80210 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80214 : bv 32 := 0x7b713423.
Lemma F_80214 : fetch_word Asan.M.loaded_segments (0x80264 : word) = Some W_80214.
Proof. vm_refl. Qed.
Lemma D_80214 : decode_any W_80214 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80218 : bv 32 := 0x7f010413.
Lemma F_80218 : fetch_word Asan.M.loaded_segments (0x80268 : word) = Some W_80218.
Proof. vm_refl. Qed.
Lemma D_80218 : decode_any W_80218 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8021c : bv 32 := 0xf9010113.
Lemma F_8021c : fetch_word Asan.M.loaded_segments (0x8026c : word) = Some W_8021c.
Proof. vm_refl. Qed.
Lemma D_8021c : decode_any W_8021c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80220 : bv 32 := 0x000e1697.
Lemma F_80220 : fetch_word Asan.M.loaded_segments (0x80270 : word) = Some W_80220.
Proof. vm_refl. Qed.
Lemma D_80220 : decode_any W_80220 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80224 : bv 32 := 0x5106b683.
Lemma F_80224 : fetch_word Asan.M.loaded_segments (0x80274 : word) = Some W_80224.
Proof. vm_refl. Qed.
Lemma D_80224 : decode_any W_80224 = Some (Load SZ8 true 13 13 1296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80228 : bv 32 := 0x0006c683.
Lemma F_80228 : fetch_word Asan.M.loaded_segments (0x80278 : word) = Some W_80228.
Proof. vm_refl. Qed.
Lemma D_80228 : decode_any W_80228 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8022c : bv 32 := 0x0e068863.
Lemma F_8022c : fetch_word Asan.M.loaded_segments (0x8027c : word) = Some W_8022c.
Proof. vm_refl. Qed.
Lemma D_8022c : decode_any W_8022c = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80230 : bv 32 := 0x80040a13.
Lemma F_80230 : fetch_word Asan.M.loaded_segments (0x80280 : word) = Some W_80230.
Proof. vm_refl. Qed.
Lemma D_80230 : decode_any W_80230 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80234 : bv 32 := 0xfa0a0a13.
Lemma F_80234 : fetch_word Asan.M.loaded_segments (0x80284 : word) = Some W_80234.
Proof. vm_refl. Qed.
Lemma D_80234 : decode_any W_80234 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80238 : bv 32 := 0x00c58ab3.
Lemma F_80238 : fetch_word Asan.M.loaded_segments (0x80288 : word) = Some W_80238.
Proof. vm_refl. Qed.
Lemma D_80238 : decode_any W_80238 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8023c : bv 32 := 0x00c509b3.
Lemma F_8023c : fetch_word Asan.M.loaded_segments (0x8028c : word) = Some W_8023c.
Proof. vm_refl. Qed.
Lemma D_8023c : decode_any W_8023c = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80240 : bv 32 := 0x00b50663.
Lemma F_80240 : fetch_word Asan.M.loaded_segments (0x80290 : word) = Some W_80240.
Proof. vm_refl. Qed.
Lemma D_80240 : decode_any W_80240 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80244 : bv 32 := 0x0135f463.
Lemma F_80244 : fetch_word Asan.M.loaded_segments (0x80294 : word) = Some W_80244.
Proof. vm_refl. Qed.
Lemma D_80244 : decode_any W_80244 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80248 : bv 32 := 0x1b556a63.
Lemma F_80248 : fetch_word Asan.M.loaded_segments (0x80298 : word) = Some W_80248.
Proof. vm_refl. Qed.
Lemma D_80248 : decode_any W_80248 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8024c : bv 32 := 0xfff5c693.
Lemma F_8024c : fetch_word Asan.M.loaded_segments (0x8029c : word) = Some W_8024c.
Proof. vm_refl. Qed.
Lemma D_8024c : decode_any W_8024c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80250 : bv 32 := 0x26c6e463.
Lemma F_80250 : fetch_word Asan.M.loaded_segments (0x802a0 : word) = Some W_80250.
Proof. vm_refl. Qed.
Lemma D_80250 : decode_any W_80250 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80254 : bv 32 := 0xfbf60b13.
Lemma F_80254 : fetch_word Asan.M.loaded_segments (0x802a4 : word) = Some W_80254.
Proof. vm_refl. Qed.
Lemma D_80254 : decode_any W_80254 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80258 : bv 32 := 0xfbf00693.
Lemma F_80258 : fetch_word Asan.M.loaded_segments (0x802a8 : word) = Some W_80258.
Proof. vm_refl. Qed.
Lemma D_80258 : decode_any W_80258 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8025c : bv 32 := 0x2f66f263.
Lemma F_8025c : fetch_word Asan.M.loaded_segments (0x802ac : word) = Some W_8025c.
Proof. vm_refl. Qed.
Lemma D_8025c : decode_any W_8025c = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80260 : bv 32 := 0x000e1697.
Lemma F_80260 : fetch_word Asan.M.loaded_segments (0x802b0 : word) = Some W_80260.
Proof. vm_refl. Qed.
Lemma D_80260 : decode_any W_80260 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80264 : bv 32 := 0x9686b683.
Lemma F_80264 : fetch_word Asan.M.loaded_segments (0x802b4 : word) = Some W_80264.
Proof. vm_refl. Qed.
Lemma D_80264 : decode_any W_80264 = Some (Load SZ8 true 13 13 2408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80268 : bv 32 := 0x0006b703.
Lemma F_80268 : fetch_word Asan.M.loaded_segments (0x802b8 : word) = Some W_80268.
Proof. vm_refl. Qed.
Lemma D_80268 : decode_any W_80268 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8026c : bv 32 := 0xfffa8a93.
Lemma F_8026c : fetch_word Asan.M.loaded_segments (0x802bc : word) = Some W_8026c.
Proof. vm_refl. Qed.
Lemma D_8026c : decode_any W_8026c = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80270 : bv 32 := 0x0035d693.
Lemma F_80270 : fetch_word Asan.M.loaded_segments (0x802c0 : word) = Some W_80270.
Proof. vm_refl. Qed.
Lemma D_80270 : decode_any W_80270 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80274 : bv 32 := 0x003ad793.
Lemma F_80274 : fetch_word Asan.M.loaded_segments (0x802c4 : word) = Some W_80274.
Proof. vm_refl. Qed.
Lemma D_80274 : decode_any W_80274 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80278 : bv 32 := 0x00d706b3.
Lemma F_80278 : fetch_word Asan.M.loaded_segments (0x802c8 : word) = Some W_80278.
Proof. vm_refl. Qed.
Lemma D_80278 : decode_any W_80278 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8027c : bv 32 := 0x00f70733.
Lemma F_8027c : fetch_word Asan.M.loaded_segments (0x802cc : word) = Some W_8027c.
Proof. vm_refl. Qed.
Lemma D_8027c : decode_any W_8027c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80280 : bv 32 := 0xff86f793.
Lemma F_80280 : fetch_word Asan.M.loaded_segments (0x802d0 : word) = Some W_80280.
Proof. vm_refl. Qed.
Lemma D_80280 : decode_any W_80280 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80284 : bv 32 := 0xff877813.
Lemma F_80284 : fetch_word Asan.M.loaded_segments (0x802d4 : word) = Some W_80284.
Proof. vm_refl. Qed.
Lemma D_80284 : decode_any W_80284 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80288 : bv 32 := 0x0007b783.
Lemma F_80288 : fetch_word Asan.M.loaded_segments (0x802d8 : word) = Some W_80288.
Proof. vm_refl. Qed.
Lemma D_80288 : decode_any W_80288 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8028c : bv 32 := 0x00083803.
Lemma F_8028c : fetch_word Asan.M.loaded_segments (0x802dc : word) = Some W_8028c.
Proof. vm_refl. Qed.
Lemma D_8028c : decode_any W_8028c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80290 : bv 32 := 0x00f867b3.
Lemma F_80290 : fetch_word Asan.M.loaded_segments (0x802e0 : word) = Some W_80290.
Proof. vm_refl. Qed.
Lemma D_80290 : decode_any W_80290 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80294 : bv 32 := 0x2a079a63.
Lemma F_80294 : fetch_word Asan.M.loaded_segments (0x802e4 : word) = Some W_80294.
Proof. vm_refl. Qed.
Lemma D_80294 : decode_any W_80294 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80298 : bv 32 := 0xfff54693.
Lemma F_80298 : fetch_word Asan.M.loaded_segments (0x802e8 : word) = Some W_80298.
Proof. vm_refl. Qed.
Lemma D_80298 : decode_any W_80298 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8029c : bv 32 := 0x0cc6ea63.
Lemma F_8029c : fetch_word Asan.M.loaded_segments (0x802ec : word) = Some W_8029c.
Proof. vm_refl. Qed.
Lemma D_8029c : decode_any W_8029c = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802a0 : bv 32 := 0xfbf00693.
Lemma F_802a0 : fetch_word Asan.M.loaded_segments (0x802f0 : word) = Some W_802a0.
Proof. vm_refl. Qed.
Lemma D_802a0 : decode_any W_802a0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802a4 : bv 32 := 0x1566f863.
Lemma F_802a4 : fetch_word Asan.M.loaded_segments (0x802f4 : word) = Some W_802a4.
Proof. vm_refl. Qed.
Lemma D_802a4 : decode_any W_802a4 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802a8 : bv 32 := 0x000e1697.
Lemma F_802a8 : fetch_word Asan.M.loaded_segments (0x802f8 : word) = Some W_802a8.
Proof. vm_refl. Qed.
Lemma D_802a8 : decode_any W_802a8 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802ac : bv 32 := 0x9206b683.
Lemma F_802ac : fetch_word Asan.M.loaded_segments (0x802fc : word) = Some W_802ac.
Proof. vm_refl. Qed.
Lemma D_802ac : decode_any W_802ac = Some (Load SZ8 true 13 13 2336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802b0 : bv 32 := 0x0006b703.
Lemma F_802b0 : fetch_word Asan.M.loaded_segments (0x80300 : word) = Some W_802b0.
Proof. vm_refl. Qed.
Lemma D_802b0 : decode_any W_802b0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802b4 : bv 32 := 0xfff98993.
Lemma F_802b4 : fetch_word Asan.M.loaded_segments (0x80304 : word) = Some W_802b4.
Proof. vm_refl. Qed.
Lemma D_802b4 : decode_any W_802b4 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802b8 : bv 32 := 0x00355693.
Lemma F_802b8 : fetch_word Asan.M.loaded_segments (0x80308 : word) = Some W_802b8.
Proof. vm_refl. Qed.
Lemma D_802b8 : decode_any W_802b8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802bc : bv 32 := 0x0039d793.
Lemma F_802bc : fetch_word Asan.M.loaded_segments (0x8030c : word) = Some W_802bc.
Proof. vm_refl. Qed.
Lemma D_802bc : decode_any W_802bc = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802c0 : bv 32 := 0x00d706b3.
Lemma F_802c0 : fetch_word Asan.M.loaded_segments (0x80310 : word) = Some W_802c0.
Proof. vm_refl. Qed.
Lemma D_802c0 : decode_any W_802c0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802c4 : bv 32 := 0x00f70733.
Lemma F_802c4 : fetch_word Asan.M.loaded_segments (0x80314 : word) = Some W_802c4.
Proof. vm_refl. Qed.
Lemma D_802c4 : decode_any W_802c4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802c8 : bv 32 := 0xff86f793.
Lemma F_802c8 : fetch_word Asan.M.loaded_segments (0x80318 : word) = Some W_802c8.
Proof. vm_refl. Qed.
Lemma D_802c8 : decode_any W_802c8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802cc : bv 32 := 0xff877813.
Lemma F_802cc : fetch_word Asan.M.loaded_segments (0x8031c : word) = Some W_802cc.
Proof. vm_refl. Qed.
Lemma D_802cc : decode_any W_802cc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802d0 : bv 32 := 0x0007b783.
Lemma F_802d0 : fetch_word Asan.M.loaded_segments (0x80320 : word) = Some W_802d0.
Proof. vm_refl. Qed.
Lemma D_802d0 : decode_any W_802d0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802d4 : bv 32 := 0x00083803.
Lemma F_802d4 : fetch_word Asan.M.loaded_segments (0x80324 : word) = Some W_802d4.
Proof. vm_refl. Qed.
Lemma D_802d4 : decode_any W_802d4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802d8 : bv 32 := 0x00f867b3.
Lemma F_802d8 : fetch_word Asan.M.loaded_segments (0x80328 : word) = Some W_802d8.
Proof. vm_refl. Qed.
Lemma D_802d8 : decode_any W_802d8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802dc : bv 32 := 0x30079863.
Lemma F_802dc : fetch_word Asan.M.loaded_segments (0x8032c : word) = Some W_802dc.
Proof. vm_refl. Qed.
Lemma D_802dc : decode_any W_802dc = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802e0 : bv 32 := 0x000e3697.
Lemma F_802e0 : fetch_word Asan.M.loaded_segments (0x80330 : word) = Some W_802e0.
Proof. vm_refl. Qed.
Lemma D_802e0 : decode_any W_802e0 = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802e4 : bv 32 := 0x9186b683.
Lemma F_802e4 : fetch_word Asan.M.loaded_segments (0x80334 : word) = Some W_802e4.
Proof. vm_refl. Qed.
Lemma D_802e4 : decode_any W_802e4 = Some (Load SZ8 true 13 13 2328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802e8 : bv 32 := 0x000680e7.
Lemma F_802e8 : fetch_word Asan.M.loaded_segments (0x80338 : word) = Some W_802e8.
Proof. vm_refl. Qed.
Lemma D_802e8 : decode_any W_802e8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802ec : bv 32 := 0x07010113.
Lemma F_802ec : fetch_word Asan.M.loaded_segments (0x8033c : word) = Some W_802ec.
Proof. vm_refl. Qed.
Lemma D_802ec : decode_any W_802ec = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802f0 : bv 32 := 0x7e813083.
Lemma F_802f0 : fetch_word Asan.M.loaded_segments (0x80340 : word) = Some W_802f0.
Proof. vm_refl. Qed.
Lemma D_802f0 : decode_any W_802f0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802f4 : bv 32 := 0x7e013403.
Lemma F_802f4 : fetch_word Asan.M.loaded_segments (0x80344 : word) = Some W_802f4.
Proof. vm_refl. Qed.
Lemma D_802f4 : decode_any W_802f4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802f8 : bv 32 := 0x7d813483.
Lemma F_802f8 : fetch_word Asan.M.loaded_segments (0x80348 : word) = Some W_802f8.
Proof. vm_refl. Qed.
Lemma D_802f8 : decode_any W_802f8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_802fc : bv 32 := 0x7d013903.
Lemma F_802fc : fetch_word Asan.M.loaded_segments (0x8034c : word) = Some W_802fc.
Proof. vm_refl. Qed.
Lemma D_802fc : decode_any W_802fc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80300 : bv 32 := 0x7c813983.
Lemma F_80300 : fetch_word Asan.M.loaded_segments (0x80350 : word) = Some W_80300.
Proof. vm_refl. Qed.
Lemma D_80300 : decode_any W_80300 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80304 : bv 32 := 0x7c013a03.
Lemma F_80304 : fetch_word Asan.M.loaded_segments (0x80354 : word) = Some W_80304.
Proof. vm_refl. Qed.
Lemma D_80304 : decode_any W_80304 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80308 : bv 32 := 0x7b813a83.
Lemma F_80308 : fetch_word Asan.M.loaded_segments (0x80358 : word) = Some W_80308.
Proof. vm_refl. Qed.
Lemma D_80308 : decode_any W_80308 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8030c : bv 32 := 0x7b013b03.
Lemma F_8030c : fetch_word Asan.M.loaded_segments (0x8035c : word) = Some W_8030c.
Proof. vm_refl. Qed.
Lemma D_8030c : decode_any W_8030c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80310 : bv 32 := 0x7a813b83.
Lemma F_80310 : fetch_word Asan.M.loaded_segments (0x80360 : word) = Some W_80310.
Proof. vm_refl. Qed.
Lemma D_80310 : decode_any W_80310 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80314 : bv 32 := 0x7f010113.
Lemma F_80314 : fetch_word Asan.M.loaded_segments (0x80364 : word) = Some W_80314.
Proof. vm_refl. Qed.
Lemma D_80314 : decode_any W_80314 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80318 : bv 32 := 0x00008067.
Lemma F_80318 : fetch_word Asan.M.loaded_segments (0x80368 : word) = Some W_80318.
Proof. vm_refl. Qed.
Lemma D_80318 : decode_any W_80318 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803f4 : bv 32 := 0x22061663.
Lemma F_803f4 : fetch_word Asan.M.loaded_segments (0x80444 : word) = Some W_803f4.
Proof. vm_refl. Qed.
Lemma D_803f4 : decode_any W_803f4 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803f8 : bv 32 := 0xee9ff06f.
Lemma F_803f8 : fetch_word Asan.M.loaded_segments (0x80448 : word) = Some W_803f8.
Proof. vm_refl. Qed.
Lemma D_803f8 : decode_any W_803f8 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80540 : bv 32 := 0x02061e63.
Lemma F_80540 : fetch_word Asan.M.loaded_segments (0x80590 : word) = Some W_80540.
Proof. vm_refl. Qed.
Lemma D_80540 : decode_any W_80540 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80544 : bv 32 := 0xd55ff06f.
Lemma F_80544 : fetch_word Asan.M.loaded_segments (0x80594 : word) = Some W_80544.
Proof. vm_refl. Qed.
Lemma D_80544 : decode_any W_80544 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80548 : bv 32 := 0x00070783.
Lemma F_80548 : fetch_word Asan.M.loaded_segments (0x80598 : word) = Some W_80548.
Proof. vm_refl. Qed.
Lemma D_80548 : decode_any W_80548 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8054c : bv 32 := 0x007af813.
Lemma F_8054c : fetch_word Asan.M.loaded_segments (0x8059c : word) = Some W_8054c.
Proof. vm_refl. Qed.
Lemma D_8054c : decode_any W_8054c = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80550 : bv 32 := 0x00f038b3.
Lemma F_80550 : fetch_word Asan.M.loaded_segments (0x805a0 : word) = Some W_80550.
Proof. vm_refl. Qed.
Lemma D_80550 : decode_any W_80550 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80554 : bv 32 := 0x00f827b3.
Lemma F_80554 : fetch_word Asan.M.loaded_segments (0x805a4 : word) = Some W_80554.
Proof. vm_refl. Qed.
Lemma D_80554 : decode_any W_80554 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80558 : bv 32 := 0x0017c793.
Lemma F_80558 : fetch_word Asan.M.loaded_segments (0x805a8 : word) = Some W_80558.
Proof. vm_refl. Qed.
Lemma D_80558 : decode_any W_80558 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8055c : bv 32 := 0x00f8f7b3.
Lemma F_8055c : fetch_word Asan.M.loaded_segments (0x805ac : word) = Some W_8055c.
Proof. vm_refl. Qed.
Lemma D_8055c : decode_any W_8055c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80560 : bv 32 := 0x00e6fa63.
Lemma F_80560 : fetch_word Asan.M.loaded_segments (0x805b0 : word) = Some W_80560.
Proof. vm_refl. Qed.
Lemma D_80560 : decode_any W_80560 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80564 : bv 32 := 0x0006c803.
Lemma F_80564 : fetch_word Asan.M.loaded_segments (0x805b4 : word) = Some W_80564.
Proof. vm_refl. Qed.
Lemma D_80564 : decode_any W_80564 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80568 : bv 32 := 0x00168693.
Lemma F_80568 : fetch_word Asan.M.loaded_segments (0x805b8 : word) = Some W_80568.
Proof. vm_refl. Qed.
Lemma D_80568 : decode_any W_80568 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8056c : bv 32 := 0x00f867b3.
Lemma F_8056c : fetch_word Asan.M.loaded_segments (0x805bc : word) = Some W_8056c.
Proof. vm_refl. Qed.
Lemma D_8056c : decode_any W_8056c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80570 : bv 32 := 0xfee69ae3.
Lemma F_80570 : fetch_word Asan.M.loaded_segments (0x805c0 : word) = Some W_80570.
Proof. vm_refl. Qed.
Lemma D_80570 : decode_any W_80570 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80574 : bv 32 := 0x0ff7f693.
Lemma F_80574 : fetch_word Asan.M.loaded_segments (0x805c4 : word) = Some W_80574.
Proof. vm_refl. Qed.
Lemma D_80574 : decode_any W_80574 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80578 : bv 32 := 0xd20680e3.
Lemma F_80578 : fetch_word Asan.M.loaded_segments (0x805c8 : word) = Some W_80578.
Proof. vm_refl. Qed.
Lemma D_80578 : decode_any W_80578 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8057c : bv 32 := 0x00050a93.
Lemma F_8057c : fetch_word Asan.M.loaded_segments (0x805cc : word) = Some W_8057c.
Proof. vm_refl. Qed.
Lemma D_8057c : decode_any W_8057c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80580 : bv 32 := 0x00058513.
Lemma F_80580 : fetch_word Asan.M.loaded_segments (0x805d0 : word) = Some W_80580.
Proof. vm_refl. Qed.
Lemma D_80580 : decode_any W_80580 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80584 : bv 32 := 0x00058b93.
Lemma F_80584 : fetch_word Asan.M.loaded_segments (0x805d4 : word) = Some W_80584.
Proof. vm_refl. Qed.
Lemma D_80584 : decode_any W_80584 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80588 : bv 32 := 0x00060593.
Lemma F_80588 : fetch_word Asan.M.loaded_segments (0x805d8 : word) = Some W_80588.
Proof. vm_refl. Qed.
Lemma D_80588 : decode_any W_80588 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8058c : bv 32 := 0x00060493.
Lemma F_8058c : fetch_word Asan.M.loaded_segments (0x805dc : word) = Some W_8058c.
Proof. vm_refl. Qed.
Lemma D_8058c : decode_any W_8058c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80590 : bv 32 := 0x48c030ef.
Lemma F_80590 : fetch_word Asan.M.loaded_segments (0x805e0 : word) = Some W_80590.
Proof. vm_refl. Qed.
Lemma D_80590 : decode_any W_80590 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80594 : bv 32 := 0x000b8593.
Lemma F_80594 : fetch_word Asan.M.loaded_segments (0x805e4 : word) = Some W_80594.
Proof. vm_refl. Qed.
Lemma D_80594 : decode_any W_80594 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80598 : bv 32 := 0x00048613.
Lemma F_80598 : fetch_word Asan.M.loaded_segments (0x805e8 : word) = Some W_80598.
Proof. vm_refl. Qed.
Lemma D_80598 : decode_any W_80598 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8059c : bv 32 := 0x00050913.
Lemma F_8059c : fetch_word Asan.M.loaded_segments (0x805ec : word) = Some W_8059c.
Proof. vm_refl. Qed.
Lemma D_8059c : decode_any W_8059c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805a0 : bv 32 := 0x000a8513.
Lemma F_805a0 : fetch_word Asan.M.loaded_segments (0x805f0 : word) = Some W_805a0.
Proof. vm_refl. Qed.
Lemma D_805a0 : decode_any W_805a0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805a4 : bv 32 := 0xce090ae3.
Lemma F_805a4 : fetch_word Asan.M.loaded_segments (0x805f4 : word) = Some W_805a4.
Proof. vm_refl. Qed.
Lemma D_805a4 : decode_any W_805a4 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805ec : bv 32 := 0x00070783.
Lemma F_805ec : fetch_word Asan.M.loaded_segments (0x8063c : word) = Some W_805ec.
Proof. vm_refl. Qed.
Lemma D_805ec : decode_any W_805ec = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f0 : bv 32 := 0x0079f813.
Lemma F_805f0 : fetch_word Asan.M.loaded_segments (0x80640 : word) = Some W_805f0.
Proof. vm_refl. Qed.
Lemma D_805f0 : decode_any W_805f0 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f4 : bv 32 := 0x00f038b3.
Lemma F_805f4 : fetch_word Asan.M.loaded_segments (0x80644 : word) = Some W_805f4.
Proof. vm_refl. Qed.
Lemma D_805f4 : decode_any W_805f4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f8 : bv 32 := 0x00f827b3.
Lemma F_805f8 : fetch_word Asan.M.loaded_segments (0x80648 : word) = Some W_805f8.
Proof. vm_refl. Qed.
Lemma D_805f8 : decode_any W_805f8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805fc : bv 32 := 0x0017c793.
Lemma F_805fc : fetch_word Asan.M.loaded_segments (0x8064c : word) = Some W_805fc.
Proof. vm_refl. Qed.
Lemma D_805fc : decode_any W_805fc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80600 : bv 32 := 0x00f8f7b3.
Lemma F_80600 : fetch_word Asan.M.loaded_segments (0x80650 : word) = Some W_80600.
Proof. vm_refl. Qed.
Lemma D_80600 : decode_any W_80600 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80604 : bv 32 := 0x00e6fa63.
Lemma F_80604 : fetch_word Asan.M.loaded_segments (0x80654 : word) = Some W_80604.
Proof. vm_refl. Qed.
Lemma D_80604 : decode_any W_80604 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80608 : bv 32 := 0x0006c803.
Lemma F_80608 : fetch_word Asan.M.loaded_segments (0x80658 : word) = Some W_80608.
Proof. vm_refl. Qed.
Lemma D_80608 : decode_any W_80608 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8060c : bv 32 := 0x00168693.
Lemma F_8060c : fetch_word Asan.M.loaded_segments (0x8065c : word) = Some W_8060c.
Proof. vm_refl. Qed.
Lemma D_8060c : decode_any W_8060c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80610 : bv 32 := 0x00f867b3.
Lemma F_80610 : fetch_word Asan.M.loaded_segments (0x80660 : word) = Some W_80610.
Proof. vm_refl. Qed.
Lemma D_80610 : decode_any W_80610 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80614 : bv 32 := 0xfee69ae3.
Lemma F_80614 : fetch_word Asan.M.loaded_segments (0x80664 : word) = Some W_80614.
Proof. vm_refl. Qed.
Lemma D_80614 : decode_any W_80614 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80618 : bv 32 := 0x0ff7f693.
Lemma F_80618 : fetch_word Asan.M.loaded_segments (0x80668 : word) = Some W_80618.
Proof. vm_refl. Qed.
Lemma D_80618 : decode_any W_80618 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8061c : bv 32 := 0xcc0682e3.
Lemma F_8061c : fetch_word Asan.M.loaded_segments (0x8066c : word) = Some W_8061c.
Proof. vm_refl. Qed.
Lemma D_8061c : decode_any W_8061c = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80620 : bv 32 := 0x00050493.
Lemma F_80620 : fetch_word Asan.M.loaded_segments (0x80670 : word) = Some W_80620.
Proof. vm_refl. Qed.
Lemma D_80620 : decode_any W_80620 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80624 : bv 32 := 0x00058a93.
Lemma F_80624 : fetch_word Asan.M.loaded_segments (0x80674 : word) = Some W_80624.
Proof. vm_refl. Qed.
Lemma D_80624 : decode_any W_80624 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80628 : bv 32 := 0x00060593.
Lemma F_80628 : fetch_word Asan.M.loaded_segments (0x80678 : word) = Some W_80628.
Proof. vm_refl. Qed.
Lemma D_80628 : decode_any W_80628 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8062c : bv 32 := 0x00060913.
Lemma F_8062c : fetch_word Asan.M.loaded_segments (0x8067c : word) = Some W_8062c.
Proof. vm_refl. Qed.
Lemma D_8062c : decode_any W_8062c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80630 : bv 32 := 0x3ec030ef.
Lemma F_80630 : fetch_word Asan.M.loaded_segments (0x80680 : word) = Some W_80630.
Proof. vm_refl. Qed.
Lemma D_80630 : decode_any W_80630 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80634 : bv 32 := 0x000a8593.
Lemma F_80634 : fetch_word Asan.M.loaded_segments (0x80684 : word) = Some W_80634.
Proof. vm_refl. Qed.
Lemma D_80634 : decode_any W_80634 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80638 : bv 32 := 0x00090613.
Lemma F_80638 : fetch_word Asan.M.loaded_segments (0x80688 : word) = Some W_80638.
Proof. vm_refl. Qed.
Lemma D_80638 : decode_any W_80638 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8063c : bv 32 := 0x00050993.
Lemma F_8063c : fetch_word Asan.M.loaded_segments (0x8068c : word) = Some W_8063c.
Proof. vm_refl. Qed.
Lemma D_8063c : decode_any W_8063c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80640 : bv 32 := 0x00048513.
Lemma F_80640 : fetch_word Asan.M.loaded_segments (0x80690 : word) = Some W_80640.
Proof. vm_refl. Qed.
Lemma D_80640 : decode_any W_80640 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80644 : bv 32 := 0xc8098ee3.
Lemma F_80644 : fetch_word Asan.M.loaded_segments (0x80694 : word) = Some W_80644.
Proof. vm_refl. Qed.
Lemma D_80644 : decode_any W_80644 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8068c : bv 32 := 0x81010113.
Lemma F_8068c : fetch_word Asan.M.loaded_segments (0x806dc : word) = Some W_8068c.
Proof. vm_refl. Qed.
Lemma D_8068c : decode_any W_8068c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80690 : bv 32 := 0x7e113423.
Lemma F_80690 : fetch_word Asan.M.loaded_segments (0x806e0 : word) = Some W_80690.
Proof. vm_refl. Qed.
Lemma D_80690 : decode_any W_80690 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80694 : bv 32 := 0x7e813023.
Lemma F_80694 : fetch_word Asan.M.loaded_segments (0x806e4 : word) = Some W_80694.
Proof. vm_refl. Qed.
Lemma D_80694 : decode_any W_80694 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80698 : bv 32 := 0x7c913c23.
Lemma F_80698 : fetch_word Asan.M.loaded_segments (0x806e8 : word) = Some W_80698.
Proof. vm_refl. Qed.
Lemma D_80698 : decode_any W_80698 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8069c : bv 32 := 0x7d213823.
Lemma F_8069c : fetch_word Asan.M.loaded_segments (0x806ec : word) = Some W_8069c.
Proof. vm_refl. Qed.
Lemma D_8069c : decode_any W_8069c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806a0 : bv 32 := 0x7d313423.
Lemma F_806a0 : fetch_word Asan.M.loaded_segments (0x806f0 : word) = Some W_806a0.
Proof. vm_refl. Qed.
Lemma D_806a0 : decode_any W_806a0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806a4 : bv 32 := 0x7d413023.
Lemma F_806a4 : fetch_word Asan.M.loaded_segments (0x806f4 : word) = Some W_806a4.
Proof. vm_refl. Qed.
Lemma D_806a4 : decode_any W_806a4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806a8 : bv 32 := 0x7b513c23.
Lemma F_806a8 : fetch_word Asan.M.loaded_segments (0x806f8 : word) = Some W_806a8.
Proof. vm_refl. Qed.
Lemma D_806a8 : decode_any W_806a8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806ac : bv 32 := 0x7f010413.
Lemma F_806ac : fetch_word Asan.M.loaded_segments (0x806fc : word) = Some W_806ac.
Proof. vm_refl. Qed.
Lemma D_806ac : decode_any W_806ac = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806b0 : bv 32 := 0xfa010113.
Lemma F_806b0 : fetch_word Asan.M.loaded_segments (0x80700 : word) = Some W_806b0.
Proof. vm_refl. Qed.
Lemma D_806b0 : decode_any W_806b0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806b4 : bv 32 := 0x000e1697.
Lemma F_806b4 : fetch_word Asan.M.loaded_segments (0x80704 : word) = Some W_806b4.
Proof. vm_refl. Qed.
Lemma D_806b4 : decode_any W_806b4 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806b8 : bv 32 := 0x07c6b683.
Lemma F_806b8 : fetch_word Asan.M.loaded_segments (0x80708 : word) = Some W_806b8.
Proof. vm_refl. Qed.
Lemma D_806b8 : decode_any W_806b8 = Some (Load SZ8 true 13 13 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806bc : bv 32 := 0x0006c683.
Lemma F_806bc : fetch_word Asan.M.loaded_segments (0x8070c : word) = Some W_806bc.
Proof. vm_refl. Qed.
Lemma D_806bc : decode_any W_806bc = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806c0 : bv 32 := 0x08068863.
Lemma F_806c0 : fetch_word Asan.M.loaded_segments (0x80710 : word) = Some W_806c0.
Proof. vm_refl. Qed.
Lemma D_806c0 : decode_any W_806c0 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806c4 : bv 32 := 0xfff54693.
Lemma F_806c4 : fetch_word Asan.M.loaded_segments (0x80714 : word) = Some W_806c4.
Proof. vm_refl. Qed.
Lemma D_806c4 : decode_any W_806c4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806c8 : bv 32 := 0x80040a13.
Lemma F_806c8 : fetch_word Asan.M.loaded_segments (0x80718 : word) = Some W_806c8.
Proof. vm_refl. Qed.
Lemma D_806c8 : decode_any W_806c8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806cc : bv 32 := 0xfb0a0a13.
Lemma F_806cc : fetch_word Asan.M.loaded_segments (0x8071c : word) = Some W_806cc.
Proof. vm_refl. Qed.
Lemma D_806cc : decode_any W_806cc = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806d0 : bv 32 := 0x0cc6e663.
Lemma F_806d0 : fetch_word Asan.M.loaded_segments (0x80720 : word) = Some W_806d0.
Proof. vm_refl. Qed.
Lemma D_806d0 : decode_any W_806d0 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806d4 : bv 32 := 0xfbf60693.
Lemma F_806d4 : fetch_word Asan.M.loaded_segments (0x80724 : word) = Some W_806d4.
Proof. vm_refl. Qed.
Lemma D_806d4 : decode_any W_806d4 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806d8 : bv 32 := 0xfbf00713.
Lemma F_806d8 : fetch_word Asan.M.loaded_segments (0x80728 : word) = Some W_806d8.
Proof. vm_refl. Qed.
Lemma D_806d8 : decode_any W_806d8 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806dc : bv 32 := 0x14d77463.
Lemma F_806dc : fetch_word Asan.M.loaded_segments (0x8072c : word) = Some W_806dc.
Proof. vm_refl. Qed.
Lemma D_806dc : decode_any W_806dc = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806e0 : bv 32 := 0x000e0697.
Lemma F_806e0 : fetch_word Asan.M.loaded_segments (0x80730 : word) = Some W_806e0.
Proof. vm_refl. Qed.
Lemma D_806e0 : decode_any W_806e0 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806e4 : bv 32 := 0x4e86b683.
Lemma F_806e4 : fetch_word Asan.M.loaded_segments (0x80734 : word) = Some W_806e4.
Proof. vm_refl. Qed.
Lemma D_806e4 : decode_any W_806e4 = Some (Load SZ8 true 13 13 1256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806e8 : bv 32 := 0x00c507b3.
Lemma F_806e8 : fetch_word Asan.M.loaded_segments (0x80738 : word) = Some W_806e8.
Proof. vm_refl. Qed.
Lemma D_806e8 : decode_any W_806e8 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806ec : bv 32 := 0x0006b703.
Lemma F_806ec : fetch_word Asan.M.loaded_segments (0x8073c : word) = Some W_806ec.
Proof. vm_refl. Qed.
Lemma D_806ec : decode_any W_806ec = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806f0 : bv 32 := 0x00355693.
Lemma F_806f0 : fetch_word Asan.M.loaded_segments (0x80740 : word) = Some W_806f0.
Proof. vm_refl. Qed.
Lemma D_806f0 : decode_any W_806f0 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806f4 : bv 32 := 0xfff78793.
Lemma F_806f4 : fetch_word Asan.M.loaded_segments (0x80744 : word) = Some W_806f4.
Proof. vm_refl. Qed.
Lemma D_806f4 : decode_any W_806f4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806f8 : bv 32 := 0x0037d813.
Lemma F_806f8 : fetch_word Asan.M.loaded_segments (0x80748 : word) = Some W_806f8.
Proof. vm_refl. Qed.
Lemma D_806f8 : decode_any W_806f8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_806fc : bv 32 := 0x00d706b3.
Lemma F_806fc : fetch_word Asan.M.loaded_segments (0x8074c : word) = Some W_806fc.
Proof. vm_refl. Qed.
Lemma D_806fc : decode_any W_806fc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80700 : bv 32 := 0x01070733.
Lemma F_80700 : fetch_word Asan.M.loaded_segments (0x80750 : word) = Some W_80700.
Proof. vm_refl. Qed.
Lemma D_80700 : decode_any W_80700 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80704 : bv 32 := 0xff86f813.
Lemma F_80704 : fetch_word Asan.M.loaded_segments (0x80754 : word) = Some W_80704.
Proof. vm_refl. Qed.
Lemma D_80704 : decode_any W_80704 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80708 : bv 32 := 0xff877893.
Lemma F_80708 : fetch_word Asan.M.loaded_segments (0x80758 : word) = Some W_80708.
Proof. vm_refl. Qed.
Lemma D_80708 : decode_any W_80708 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8070c : bv 32 := 0x00083803.
Lemma F_8070c : fetch_word Asan.M.loaded_segments (0x8075c : word) = Some W_8070c.
Proof. vm_refl. Qed.
Lemma D_8070c : decode_any W_8070c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80710 : bv 32 := 0x0008b883.
Lemma F_80710 : fetch_word Asan.M.loaded_segments (0x80760 : word) = Some W_80710.
Proof. vm_refl. Qed.
Lemma D_80710 : decode_any W_80710 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80714 : bv 32 := 0x0108e833.
Lemma F_80714 : fetch_word Asan.M.loaded_segments (0x80764 : word) = Some W_80714.
Proof. vm_refl. Qed.
Lemma D_80714 : decode_any W_80714 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80718 : bv 32 := 0x10081a63.
Lemma F_80718 : fetch_word Asan.M.loaded_segments (0x80768 : word) = Some W_80718.
Proof. vm_refl. Qed.
Lemma D_80718 : decode_any W_80718 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8071c : bv 32 := 0x000e2697.
Lemma F_8071c : fetch_word Asan.M.loaded_segments (0x8076c : word) = Some W_8071c.
Proof. vm_refl. Qed.
Lemma D_8071c : decode_any W_8071c = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80720 : bv 32 := 0x4e46b683.
Lemma F_80720 : fetch_word Asan.M.loaded_segments (0x80770 : word) = Some W_80720.
Proof. vm_refl. Qed.
Lemma D_80720 : decode_any W_80720 = Some (Load SZ8 true 13 13 1252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80724 : bv 32 := 0x000680e7.
Lemma F_80724 : fetch_word Asan.M.loaded_segments (0x80774 : word) = Some W_80724.
Proof. vm_refl. Qed.
Lemma D_80724 : decode_any W_80724 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80728 : bv 32 := 0x06010113.
Lemma F_80728 : fetch_word Asan.M.loaded_segments (0x80778 : word) = Some W_80728.
Proof. vm_refl. Qed.
Lemma D_80728 : decode_any W_80728 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8072c : bv 32 := 0x7e813083.
Lemma F_8072c : fetch_word Asan.M.loaded_segments (0x8077c : word) = Some W_8072c.
Proof. vm_refl. Qed.
Lemma D_8072c : decode_any W_8072c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80730 : bv 32 := 0x7e013403.
Lemma F_80730 : fetch_word Asan.M.loaded_segments (0x80780 : word) = Some W_80730.
Proof. vm_refl. Qed.
Lemma D_80730 : decode_any W_80730 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80734 : bv 32 := 0x7d813483.
Lemma F_80734 : fetch_word Asan.M.loaded_segments (0x80784 : word) = Some W_80734.
Proof. vm_refl. Qed.
Lemma D_80734 : decode_any W_80734 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80738 : bv 32 := 0x7d013903.
Lemma F_80738 : fetch_word Asan.M.loaded_segments (0x80788 : word) = Some W_80738.
Proof. vm_refl. Qed.
Lemma D_80738 : decode_any W_80738 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8073c : bv 32 := 0x7c813983.
Lemma F_8073c : fetch_word Asan.M.loaded_segments (0x8078c : word) = Some W_8073c.
Proof. vm_refl. Qed.
Lemma D_8073c : decode_any W_8073c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80740 : bv 32 := 0x7c013a03.
Lemma F_80740 : fetch_word Asan.M.loaded_segments (0x80790 : word) = Some W_80740.
Proof. vm_refl. Qed.
Lemma D_80740 : decode_any W_80740 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80744 : bv 32 := 0x7b813a83.
Lemma F_80744 : fetch_word Asan.M.loaded_segments (0x80794 : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80748 : bv 32 := 0x7f010113.
Lemma F_80748 : fetch_word Asan.M.loaded_segments (0x80798 : word) = Some W_80748.
Proof. vm_refl. Qed.
Lemma D_80748 : decode_any W_80748 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8074c : bv 32 := 0x00008067.
Lemma F_8074c : fetch_word Asan.M.loaded_segments (0x8079c : word) = Some W_8074c.
Proof. vm_refl. Qed.
Lemma D_8074c : decode_any W_8074c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80824 : bv 32 := 0x02061e63.
Lemma F_80824 : fetch_word Asan.M.loaded_segments (0x80874 : word) = Some W_80824.
Proof. vm_refl. Qed.
Lemma D_80824 : decode_any W_80824 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80828 : bv 32 := 0xef5ff06f.
Lemma F_80828 : fetch_word Asan.M.loaded_segments (0x80878 : word) = Some W_80828.
Proof. vm_refl. Qed.
Lemma D_80828 : decode_any W_80828 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8082c : bv 32 := 0x00070803.
Lemma F_8082c : fetch_word Asan.M.loaded_segments (0x8087c : word) = Some W_8082c.
Proof. vm_refl. Qed.
Lemma D_8082c : decode_any W_8082c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80830 : bv 32 := 0x0077f793.
Lemma F_80830 : fetch_word Asan.M.loaded_segments (0x80880 : word) = Some W_80830.
Proof. vm_refl. Qed.
Lemma D_80830 : decode_any W_80830 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80834 : bv 32 := 0x010038b3.
Lemma F_80834 : fetch_word Asan.M.loaded_segments (0x80884 : word) = Some W_80834.
Proof. vm_refl. Qed.
Lemma D_80834 : decode_any W_80834 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80838 : bv 32 := 0x0107a7b3.
Lemma F_80838 : fetch_word Asan.M.loaded_segments (0x80888 : word) = Some W_80838.
Proof. vm_refl. Qed.
Lemma D_80838 : decode_any W_80838 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8083c : bv 32 := 0x0017c793.
Lemma F_8083c : fetch_word Asan.M.loaded_segments (0x8088c : word) = Some W_8083c.
Proof. vm_refl. Qed.
Lemma D_8083c : decode_any W_8083c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80840 : bv 32 := 0x00f8f7b3.
Lemma F_80840 : fetch_word Asan.M.loaded_segments (0x80890 : word) = Some W_80840.
Proof. vm_refl. Qed.
Lemma D_80840 : decode_any W_80840 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80844 : bv 32 := 0x00e6fa63.
Lemma F_80844 : fetch_word Asan.M.loaded_segments (0x80894 : word) = Some W_80844.
Proof. vm_refl. Qed.
Lemma D_80844 : decode_any W_80844 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80848 : bv 32 := 0x0006c803.
Lemma F_80848 : fetch_word Asan.M.loaded_segments (0x80898 : word) = Some W_80848.
Proof. vm_refl. Qed.
Lemma D_80848 : decode_any W_80848 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8084c : bv 32 := 0x00168693.
Lemma F_8084c : fetch_word Asan.M.loaded_segments (0x8089c : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80850 : bv 32 := 0x00f867b3.
Lemma F_80850 : fetch_word Asan.M.loaded_segments (0x808a0 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80854 : bv 32 := 0xfee69ae3.
Lemma F_80854 : fetch_word Asan.M.loaded_segments (0x808a4 : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80858 : bv 32 := 0x0ff7f693.
Lemma F_80858 : fetch_word Asan.M.loaded_segments (0x808a8 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8085c : bv 32 := 0xec0680e3.
Lemma F_8085c : fetch_word Asan.M.loaded_segments (0x808ac : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80860 : bv 32 := 0x00050493.
Lemma F_80860 : fetch_word Asan.M.loaded_segments (0x808b0 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80864 : bv 32 := 0x00058a93.
Lemma F_80864 : fetch_word Asan.M.loaded_segments (0x808b4 : word) = Some W_80864.
Proof. vm_refl. Qed.
Lemma D_80864 : decode_any W_80864 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80868 : bv 32 := 0x00060593.
Lemma F_80868 : fetch_word Asan.M.loaded_segments (0x808b8 : word) = Some W_80868.
Proof. vm_refl. Qed.
Lemma D_80868 : decode_any W_80868 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8086c : bv 32 := 0x00060913.
Lemma F_8086c : fetch_word Asan.M.loaded_segments (0x808bc : word) = Some W_8086c.
Proof. vm_refl. Qed.
Lemma D_8086c : decode_any W_8086c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80870 : bv 32 := 0x1ac030ef.
Lemma F_80870 : fetch_word Asan.M.loaded_segments (0x808c0 : word) = Some W_80870.
Proof. vm_refl. Qed.
Lemma D_80870 : decode_any W_80870 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80874 : bv 32 := 0x000a8593.
Lemma F_80874 : fetch_word Asan.M.loaded_segments (0x808c4 : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80878 : bv 32 := 0x00090613.
Lemma F_80878 : fetch_word Asan.M.loaded_segments (0x808c8 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8087c : bv 32 := 0x00050993.
Lemma F_8087c : fetch_word Asan.M.loaded_segments (0x808cc : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80880 : bv 32 := 0x00048513.
Lemma F_80880 : fetch_word Asan.M.loaded_segments (0x808d0 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80884 : bv 32 := 0xe8098ce3.
Lemma F_80884 : fetch_word Asan.M.loaded_segments (0x808d4 : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808cc : bv 32 := 0x81010113.
Lemma F_808cc : fetch_word Asan.M.loaded_segments (0x8091c : word) = Some W_808cc.
Proof. vm_refl. Qed.
Lemma D_808cc : decode_any W_808cc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d0 : bv 32 := 0x7e113423.
Lemma F_808d0 : fetch_word Asan.M.loaded_segments (0x80920 : word) = Some W_808d0.
Proof. vm_refl. Qed.
Lemma D_808d0 : decode_any W_808d0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d4 : bv 32 := 0x7e813023.
Lemma F_808d4 : fetch_word Asan.M.loaded_segments (0x80924 : word) = Some W_808d4.
Proof. vm_refl. Qed.
Lemma D_808d4 : decode_any W_808d4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d8 : bv 32 := 0x7c913c23.
Lemma F_808d8 : fetch_word Asan.M.loaded_segments (0x80928 : word) = Some W_808d8.
Proof. vm_refl. Qed.
Lemma D_808d8 : decode_any W_808d8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808dc : bv 32 := 0x7d213823.
Lemma F_808dc : fetch_word Asan.M.loaded_segments (0x8092c : word) = Some W_808dc.
Proof. vm_refl. Qed.
Lemma D_808dc : decode_any W_808dc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e0 : bv 32 := 0x7d313423.
Lemma F_808e0 : fetch_word Asan.M.loaded_segments (0x80930 : word) = Some W_808e0.
Proof. vm_refl. Qed.
Lemma D_808e0 : decode_any W_808e0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e4 : bv 32 := 0x7d413023.
Lemma F_808e4 : fetch_word Asan.M.loaded_segments (0x80934 : word) = Some W_808e4.
Proof. vm_refl. Qed.
Lemma D_808e4 : decode_any W_808e4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e8 : bv 32 := 0x7b513c23.
Lemma F_808e8 : fetch_word Asan.M.loaded_segments (0x80938 : word) = Some W_808e8.
Proof. vm_refl. Qed.
Lemma D_808e8 : decode_any W_808e8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808ec : bv 32 := 0x7b613823.
Lemma F_808ec : fetch_word Asan.M.loaded_segments (0x8093c : word) = Some W_808ec.
Proof. vm_refl. Qed.
Lemma D_808ec : decode_any W_808ec = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f0 : bv 32 := 0x7f010413.
Lemma F_808f0 : fetch_word Asan.M.loaded_segments (0x80940 : word) = Some W_808f0.
Proof. vm_refl. Qed.
Lemma D_808f0 : decode_any W_808f0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f4 : bv 32 := 0xf9010113.
Lemma F_808f4 : fetch_word Asan.M.loaded_segments (0x80944 : word) = Some W_808f4.
Proof. vm_refl. Qed.
Lemma D_808f4 : decode_any W_808f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f8 : bv 32 := 0x000e1697.
Lemma F_808f8 : fetch_word Asan.M.loaded_segments (0x80948 : word) = Some W_808f8.
Proof. vm_refl. Qed.
Lemma D_808f8 : decode_any W_808f8 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808fc : bv 32 := 0xe386b683.
Lemma F_808fc : fetch_word Asan.M.loaded_segments (0x8094c : word) = Some W_808fc.
Proof. vm_refl. Qed.
Lemma D_808fc : decode_any W_808fc = Some (Load SZ8 true 13 13 3640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80900 : bv 32 := 0x0006c683.
Lemma F_80900 : fetch_word Asan.M.loaded_segments (0x80950 : word) = Some W_80900.
Proof. vm_refl. Qed.
Lemma D_80900 : decode_any W_80900 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80904 : bv 32 := 0x0a068463.
Lemma F_80904 : fetch_word Asan.M.loaded_segments (0x80954 : word) = Some W_80904.
Proof. vm_refl. Qed.
Lemma D_80904 : decode_any W_80904 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80908 : bv 32 := 0xfff5c693.
Lemma F_80908 : fetch_word Asan.M.loaded_segments (0x80958 : word) = Some W_80908.
Proof. vm_refl. Qed.
Lemma D_80908 : decode_any W_80908 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8090c : bv 32 := 0x80040a13.
Lemma F_8090c : fetch_word Asan.M.loaded_segments (0x8095c : word) = Some W_8090c.
Proof. vm_refl. Qed.
Lemma D_8090c : decode_any W_8090c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80910 : bv 32 := 0xfa8a0a13.
Lemma F_80910 : fetch_word Asan.M.loaded_segments (0x80960 : word) = Some W_80910.
Proof. vm_refl. Qed.
Lemma D_80910 : decode_any W_80910 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80914 : bv 32 := 0x0cc6e463.
Lemma F_80914 : fetch_word Asan.M.loaded_segments (0x80964 : word) = Some W_80914.
Proof. vm_refl. Qed.
Lemma D_80914 : decode_any W_80914 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80918 : bv 32 := 0xfbf60993.
Lemma F_80918 : fetch_word Asan.M.loaded_segments (0x80968 : word) = Some W_80918.
Proof. vm_refl. Qed.
Lemma D_80918 : decode_any W_80918 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8091c : bv 32 := 0xfbf00693.
Lemma F_8091c : fetch_word Asan.M.loaded_segments (0x8096c : word) = Some W_8091c.
Proof. vm_refl. Qed.
Lemma D_8091c : decode_any W_8091c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80920 : bv 32 := 0x1536f263.
Lemma F_80920 : fetch_word Asan.M.loaded_segments (0x80970 : word) = Some W_80920.
Proof. vm_refl. Qed.
Lemma D_80920 : decode_any W_80920 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80924 : bv 32 := 0x000e0697.
Lemma F_80924 : fetch_word Asan.M.loaded_segments (0x80974 : word) = Some W_80924.
Proof. vm_refl. Qed.
Lemma D_80924 : decode_any W_80924 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80928 : bv 32 := 0x2a46b683.
Lemma F_80928 : fetch_word Asan.M.loaded_segments (0x80978 : word) = Some W_80928.
Proof. vm_refl. Qed.
Lemma D_80928 : decode_any W_80928 = Some (Load SZ8 true 13 13 676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8092c : bv 32 := 0x00c587b3.
Lemma F_8092c : fetch_word Asan.M.loaded_segments (0x8097c : word) = Some W_8092c.
Proof. vm_refl. Qed.
Lemma D_8092c : decode_any W_8092c = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80930 : bv 32 := 0x0006b703.
Lemma F_80930 : fetch_word Asan.M.loaded_segments (0x80980 : word) = Some W_80930.
Proof. vm_refl. Qed.
Lemma D_80930 : decode_any W_80930 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80934 : bv 32 := 0x0035d693.
Lemma F_80934 : fetch_word Asan.M.loaded_segments (0x80984 : word) = Some W_80934.
Proof. vm_refl. Qed.
Lemma D_80934 : decode_any W_80934 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80938 : bv 32 := 0xfff78793.
Lemma F_80938 : fetch_word Asan.M.loaded_segments (0x80988 : word) = Some W_80938.
Proof. vm_refl. Qed.
Lemma D_80938 : decode_any W_80938 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8093c : bv 32 := 0x0037d813.
Lemma F_8093c : fetch_word Asan.M.loaded_segments (0x8098c : word) = Some W_8093c.
Proof. vm_refl. Qed.
Lemma D_8093c : decode_any W_8093c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80940 : bv 32 := 0x00d706b3.
Lemma F_80940 : fetch_word Asan.M.loaded_segments (0x80990 : word) = Some W_80940.
Proof. vm_refl. Qed.
Lemma D_80940 : decode_any W_80940 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80944 : bv 32 := 0x01070733.
Lemma F_80944 : fetch_word Asan.M.loaded_segments (0x80994 : word) = Some W_80944.
Proof. vm_refl. Qed.
Lemma D_80944 : decode_any W_80944 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80948 : bv 32 := 0xff86f813.
Lemma F_80948 : fetch_word Asan.M.loaded_segments (0x80998 : word) = Some W_80948.
Proof. vm_refl. Qed.
Lemma D_80948 : decode_any W_80948 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8094c : bv 32 := 0xff877893.
Lemma F_8094c : fetch_word Asan.M.loaded_segments (0x8099c : word) = Some W_8094c.
Proof. vm_refl. Qed.
Lemma D_8094c : decode_any W_8094c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80950 : bv 32 := 0x00083803.
Lemma F_80950 : fetch_word Asan.M.loaded_segments (0x809a0 : word) = Some W_80950.
Proof. vm_refl. Qed.
Lemma D_80950 : decode_any W_80950 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80954 : bv 32 := 0x0008b883.
Lemma F_80954 : fetch_word Asan.M.loaded_segments (0x809a4 : word) = Some W_80954.
Proof. vm_refl. Qed.
Lemma D_80954 : decode_any W_80954 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80958 : bv 32 := 0x0108e833.
Lemma F_80958 : fetch_word Asan.M.loaded_segments (0x809a8 : word) = Some W_80958.
Proof. vm_refl. Qed.
Lemma D_80958 : decode_any W_80958 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8095c : bv 32 := 0x18081e63.
Lemma F_8095c : fetch_word Asan.M.loaded_segments (0x809ac : word) = Some W_8095c.
Proof. vm_refl. Qed.
Lemma D_8095c : decode_any W_8095c = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80960 : bv 32 := 0xfff54693.
Lemma F_80960 : fetch_word Asan.M.loaded_segments (0x809b0 : word) = Some W_80960.
Proof. vm_refl. Qed.
Lemma D_80960 : decode_any W_80960 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80964 : bv 32 := 0x10c6e463.
Lemma F_80964 : fetch_word Asan.M.loaded_segments (0x809b4 : word) = Some W_80964.
Proof. vm_refl. Qed.
Lemma D_80964 : decode_any W_80964 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80968 : bv 32 := 0xfbf00693.
Lemma F_80968 : fetch_word Asan.M.loaded_segments (0x809b8 : word) = Some W_80968.
Proof. vm_refl. Qed.
Lemma D_80968 : decode_any W_80968 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8096c : bv 32 := 0x1936f263.
Lemma F_8096c : fetch_word Asan.M.loaded_segments (0x809bc : word) = Some W_8096c.
Proof. vm_refl. Qed.
Lemma D_8096c : decode_any W_8096c = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80970 : bv 32 := 0x000e0697.
Lemma F_80970 : fetch_word Asan.M.loaded_segments (0x809c0 : word) = Some W_80970.
Proof. vm_refl. Qed.
Lemma D_80970 : decode_any W_80970 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80974 : bv 32 := 0x2586b683.
Lemma F_80974 : fetch_word Asan.M.loaded_segments (0x809c4 : word) = Some W_80974.
Proof. vm_refl. Qed.
Lemma D_80974 : decode_any W_80974 = Some (Load SZ8 true 13 13 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80978 : bv 32 := 0x00c507b3.
Lemma F_80978 : fetch_word Asan.M.loaded_segments (0x809c8 : word) = Some W_80978.
Proof. vm_refl. Qed.
Lemma D_80978 : decode_any W_80978 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8097c : bv 32 := 0x0006b703.
Lemma F_8097c : fetch_word Asan.M.loaded_segments (0x809cc : word) = Some W_8097c.
Proof. vm_refl. Qed.
Lemma D_8097c : decode_any W_8097c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80980 : bv 32 := 0x00355693.
Lemma F_80980 : fetch_word Asan.M.loaded_segments (0x809d0 : word) = Some W_80980.
Proof. vm_refl. Qed.
Lemma D_80980 : decode_any W_80980 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80984 : bv 32 := 0xfff78793.
Lemma F_80984 : fetch_word Asan.M.loaded_segments (0x809d4 : word) = Some W_80984.
Proof. vm_refl. Qed.
Lemma D_80984 : decode_any W_80984 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80988 : bv 32 := 0x0037d813.
Lemma F_80988 : fetch_word Asan.M.loaded_segments (0x809d8 : word) = Some W_80988.
Proof. vm_refl. Qed.
Lemma D_80988 : decode_any W_80988 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8098c : bv 32 := 0x00d706b3.
Lemma F_8098c : fetch_word Asan.M.loaded_segments (0x809dc : word) = Some W_8098c.
Proof. vm_refl. Qed.
Lemma D_8098c : decode_any W_8098c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80990 : bv 32 := 0x01070733.
Lemma F_80990 : fetch_word Asan.M.loaded_segments (0x809e0 : word) = Some W_80990.
Proof. vm_refl. Qed.
Lemma D_80990 : decode_any W_80990 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80994 : bv 32 := 0xff86f813.
Lemma F_80994 : fetch_word Asan.M.loaded_segments (0x809e4 : word) = Some W_80994.
Proof. vm_refl. Qed.
Lemma D_80994 : decode_any W_80994 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80998 : bv 32 := 0xff877893.
Lemma F_80998 : fetch_word Asan.M.loaded_segments (0x809e8 : word) = Some W_80998.
Proof. vm_refl. Qed.
Lemma D_80998 : decode_any W_80998 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8099c : bv 32 := 0x00083803.
Lemma F_8099c : fetch_word Asan.M.loaded_segments (0x809ec : word) = Some W_8099c.
Proof. vm_refl. Qed.
Lemma D_8099c : decode_any W_8099c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809a0 : bv 32 := 0x0008b883.
Lemma F_809a0 : fetch_word Asan.M.loaded_segments (0x809f0 : word) = Some W_809a0.
Proof. vm_refl. Qed.
Lemma D_809a0 : decode_any W_809a0 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809a4 : bv 32 := 0x0108e833.
Lemma F_809a4 : fetch_word Asan.M.loaded_segments (0x809f4 : word) = Some W_809a4.
Proof. vm_refl. Qed.
Lemma D_809a4 : decode_any W_809a4 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809a8 : bv 32 := 0x1e081a63.
Lemma F_809a8 : fetch_word Asan.M.loaded_segments (0x809f8 : word) = Some W_809a8.
Proof. vm_refl. Qed.
Lemma D_809a8 : decode_any W_809a8 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809ac : bv 32 := 0x7b9120ef.
Lemma F_809ac : fetch_word Asan.M.loaded_segments (0x809fc : word) = Some W_809ac.
Proof. vm_refl. Qed.
Lemma D_809ac : decode_any W_809ac = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809b0 : bv 32 := 0x07010113.
Lemma F_809b0 : fetch_word Asan.M.loaded_segments (0x80a00 : word) = Some W_809b0.
Proof. vm_refl. Qed.
Lemma D_809b0 : decode_any W_809b0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809b4 : bv 32 := 0x7e813083.
Lemma F_809b4 : fetch_word Asan.M.loaded_segments (0x80a04 : word) = Some W_809b4.
Proof. vm_refl. Qed.
Lemma D_809b4 : decode_any W_809b4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809b8 : bv 32 := 0x7e013403.
Lemma F_809b8 : fetch_word Asan.M.loaded_segments (0x80a08 : word) = Some W_809b8.
Proof. vm_refl. Qed.
Lemma D_809b8 : decode_any W_809b8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809bc : bv 32 := 0x7d813483.
Lemma F_809bc : fetch_word Asan.M.loaded_segments (0x80a0c : word) = Some W_809bc.
Proof. vm_refl. Qed.
Lemma D_809bc : decode_any W_809bc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809c0 : bv 32 := 0x7d013903.
Lemma F_809c0 : fetch_word Asan.M.loaded_segments (0x80a10 : word) = Some W_809c0.
Proof. vm_refl. Qed.
Lemma D_809c0 : decode_any W_809c0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809c4 : bv 32 := 0x7c813983.
Lemma F_809c4 : fetch_word Asan.M.loaded_segments (0x80a14 : word) = Some W_809c4.
Proof. vm_refl. Qed.
Lemma D_809c4 : decode_any W_809c4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809c8 : bv 32 := 0x7c013a03.
Lemma F_809c8 : fetch_word Asan.M.loaded_segments (0x80a18 : word) = Some W_809c8.
Proof. vm_refl. Qed.
Lemma D_809c8 : decode_any W_809c8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809cc : bv 32 := 0x7b813a83.
Lemma F_809cc : fetch_word Asan.M.loaded_segments (0x80a1c : word) = Some W_809cc.
Proof. vm_refl. Qed.
Lemma D_809cc : decode_any W_809cc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809d0 : bv 32 := 0x7b013b03.
Lemma F_809d0 : fetch_word Asan.M.loaded_segments (0x80a20 : word) = Some W_809d0.
Proof. vm_refl. Qed.
Lemma D_809d0 : decode_any W_809d0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809d4 : bv 32 := 0x7f010113.
Lemma F_809d4 : fetch_word Asan.M.loaded_segments (0x80a24 : word) = Some W_809d4.
Proof. vm_refl. Qed.
Lemma D_809d4 : decode_any W_809d4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_809d8 : bv 32 := 0x00008067.
Lemma F_809d8 : fetch_word Asan.M.loaded_segments (0x80a28 : word) = Some W_809d8.
Proof. vm_refl. Qed.
Lemma D_809d8 : decode_any W_809d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80a64 : bv 32 := 0x0c061463.
Lemma F_80a64 : fetch_word Asan.M.loaded_segments (0x80ab4 : word) = Some W_80a64.
Proof. vm_refl. Qed.
Lemma D_80a64 : decode_any W_80a64 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80a68 : bv 32 := 0xef9ff06f.
Lemma F_80a68 : fetch_word Asan.M.loaded_segments (0x80ab8 : word) = Some W_80a68.
Proof. vm_refl. Qed.
Lemma D_80a68 : decode_any W_80a68 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af0 : bv 32 := 0x0e061063.
Lemma F_80af0 : fetch_word Asan.M.loaded_segments (0x80b40 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af4 : bv 32 := 0xeb9ff06f.
Lemma F_80af4 : fetch_word Asan.M.loaded_segments (0x80b44 : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80af8 : bv 32 := 0x00070803.
Lemma F_80af8 : fetch_word Asan.M.loaded_segments (0x80b48 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80afc : bv 32 := 0x0077f793.
Lemma F_80afc : fetch_word Asan.M.loaded_segments (0x80b4c : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b00 : bv 32 := 0x010038b3.
Lemma F_80b00 : fetch_word Asan.M.loaded_segments (0x80b50 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b04 : bv 32 := 0x0107a7b3.
Lemma F_80b04 : fetch_word Asan.M.loaded_segments (0x80b54 : word) = Some W_80b04.
Proof. vm_refl. Qed.
Lemma D_80b04 : decode_any W_80b04 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b08 : bv 32 := 0x0017c793.
Lemma F_80b08 : fetch_word Asan.M.loaded_segments (0x80b58 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b0c : bv 32 := 0x00f8f7b3.
Lemma F_80b0c : fetch_word Asan.M.loaded_segments (0x80b5c : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b10 : bv 32 := 0x00e6fa63.
Lemma F_80b10 : fetch_word Asan.M.loaded_segments (0x80b60 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b14 : bv 32 := 0x0006c803.
Lemma F_80b14 : fetch_word Asan.M.loaded_segments (0x80b64 : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b18 : bv 32 := 0x00168693.
Lemma F_80b18 : fetch_word Asan.M.loaded_segments (0x80b68 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b1c : bv 32 := 0x00f867b3.
Lemma F_80b1c : fetch_word Asan.M.loaded_segments (0x80b6c : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b20 : bv 32 := 0xfee69ae3.
Lemma F_80b20 : fetch_word Asan.M.loaded_segments (0x80b70 : word) = Some W_80b20.
Proof. vm_refl. Qed.
Lemma D_80b20 : decode_any W_80b20 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b24 : bv 32 := 0x0ff7f693.
Lemma F_80b24 : fetch_word Asan.M.loaded_segments (0x80b74 : word) = Some W_80b24.
Proof. vm_refl. Qed.
Lemma D_80b24 : decode_any W_80b24 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b28 : bv 32 := 0xe2068ce3.
Lemma F_80b28 : fetch_word Asan.M.loaded_segments (0x80b78 : word) = Some W_80b28.
Proof. vm_refl. Qed.
Lemma D_80b28 : decode_any W_80b28 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b2c : bv 32 := 0x00050a93.
Lemma F_80b2c : fetch_word Asan.M.loaded_segments (0x80b7c : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b30 : bv 32 := 0x00058513.
Lemma F_80b30 : fetch_word Asan.M.loaded_segments (0x80b80 : word) = Some W_80b30.
Proof. vm_refl. Qed.
Lemma D_80b30 : decode_any W_80b30 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b34 : bv 32 := 0x00058b13.
Lemma F_80b34 : fetch_word Asan.M.loaded_segments (0x80b84 : word) = Some W_80b34.
Proof. vm_refl. Qed.
Lemma D_80b34 : decode_any W_80b34 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b38 : bv 32 := 0x00060593.
Lemma F_80b38 : fetch_word Asan.M.loaded_segments (0x80b88 : word) = Some W_80b38.
Proof. vm_refl. Qed.
Lemma D_80b38 : decode_any W_80b38 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b3c : bv 32 := 0x00060493.
Lemma F_80b3c : fetch_word Asan.M.loaded_segments (0x80b8c : word) = Some W_80b3c.
Proof. vm_refl. Qed.
Lemma D_80b3c : decode_any W_80b3c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b40 : bv 32 := 0x6dd020ef.
Lemma F_80b40 : fetch_word Asan.M.loaded_segments (0x80b90 : word) = Some W_80b40.
Proof. vm_refl. Qed.
Lemma D_80b40 : decode_any W_80b40 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b44 : bv 32 := 0x000b0593.
Lemma F_80b44 : fetch_word Asan.M.loaded_segments (0x80b94 : word) = Some W_80b44.
Proof. vm_refl. Qed.
Lemma D_80b44 : decode_any W_80b44 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b48 : bv 32 := 0x00048613.
Lemma F_80b48 : fetch_word Asan.M.loaded_segments (0x80b98 : word) = Some W_80b48.
Proof. vm_refl. Qed.
Lemma D_80b48 : decode_any W_80b48 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b4c : bv 32 := 0x00050913.
Lemma F_80b4c : fetch_word Asan.M.loaded_segments (0x80b9c : word) = Some W_80b4c.
Proof. vm_refl. Qed.
Lemma D_80b4c : decode_any W_80b4c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b50 : bv 32 := 0x000a8513.
Lemma F_80b50 : fetch_word Asan.M.loaded_segments (0x80ba0 : word) = Some W_80b50.
Proof. vm_refl. Qed.
Lemma D_80b50 : decode_any W_80b50 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b54 : bv 32 := 0xe00906e3.
Lemma F_80b54 : fetch_word Asan.M.loaded_segments (0x80ba4 : word) = Some W_80b54.
Proof. vm_refl. Qed.
Lemma D_80b54 : decode_any W_80b54 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b9c : bv 32 := 0x00070803.
Lemma F_80b9c : fetch_word Asan.M.loaded_segments (0x80bec : word) = Some W_80b9c.
Proof. vm_refl. Qed.
Lemma D_80b9c : decode_any W_80b9c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba0 : bv 32 := 0x0077f793.
Lemma F_80ba0 : fetch_word Asan.M.loaded_segments (0x80bf0 : word) = Some W_80ba0.
Proof. vm_refl. Qed.
Lemma D_80ba0 : decode_any W_80ba0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba4 : bv 32 := 0x010038b3.
Lemma F_80ba4 : fetch_word Asan.M.loaded_segments (0x80bf4 : word) = Some W_80ba4.
Proof. vm_refl. Qed.
Lemma D_80ba4 : decode_any W_80ba4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ba8 : bv 32 := 0x0107a7b3.
Lemma F_80ba8 : fetch_word Asan.M.loaded_segments (0x80bf8 : word) = Some W_80ba8.
Proof. vm_refl. Qed.
Lemma D_80ba8 : decode_any W_80ba8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bac : bv 32 := 0x0017c793.
Lemma F_80bac : fetch_word Asan.M.loaded_segments (0x80bfc : word) = Some W_80bac.
Proof. vm_refl. Qed.
Lemma D_80bac : decode_any W_80bac = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb0 : bv 32 := 0x00f8f7b3.
Lemma F_80bb0 : fetch_word Asan.M.loaded_segments (0x80c00 : word) = Some W_80bb0.
Proof. vm_refl. Qed.
Lemma D_80bb0 : decode_any W_80bb0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb4 : bv 32 := 0x00e6fa63.
Lemma F_80bb4 : fetch_word Asan.M.loaded_segments (0x80c04 : word) = Some W_80bb4.
Proof. vm_refl. Qed.
Lemma D_80bb4 : decode_any W_80bb4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bb8 : bv 32 := 0x0006c803.
Lemma F_80bb8 : fetch_word Asan.M.loaded_segments (0x80c08 : word) = Some W_80bb8.
Proof. vm_refl. Qed.
Lemma D_80bb8 : decode_any W_80bb8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bbc : bv 32 := 0x00168693.
Lemma F_80bbc : fetch_word Asan.M.loaded_segments (0x80c0c : word) = Some W_80bbc.
Proof. vm_refl. Qed.
Lemma D_80bbc : decode_any W_80bbc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc0 : bv 32 := 0x00f867b3.
Lemma F_80bc0 : fetch_word Asan.M.loaded_segments (0x80c10 : word) = Some W_80bc0.
Proof. vm_refl. Qed.
Lemma D_80bc0 : decode_any W_80bc0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc4 : bv 32 := 0xfee69ae3.
Lemma F_80bc4 : fetch_word Asan.M.loaded_segments (0x80c14 : word) = Some W_80bc4.
Proof. vm_refl. Qed.
Lemma D_80bc4 : decode_any W_80bc4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bc8 : bv 32 := 0x0ff7f693.
Lemma F_80bc8 : fetch_word Asan.M.loaded_segments (0x80c18 : word) = Some W_80bc8.
Proof. vm_refl. Qed.
Lemma D_80bc8 : decode_any W_80bc8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bcc : bv 32 := 0xde0680e3.
Lemma F_80bcc : fetch_word Asan.M.loaded_segments (0x80c1c : word) = Some W_80bcc.
Proof. vm_refl. Qed.
Lemma D_80bcc : decode_any W_80bcc = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd0 : bv 32 := 0x00050493.
Lemma F_80bd0 : fetch_word Asan.M.loaded_segments (0x80c20 : word) = Some W_80bd0.
Proof. vm_refl. Qed.
Lemma D_80bd0 : decode_any W_80bd0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd4 : bv 32 := 0x00058a93.
Lemma F_80bd4 : fetch_word Asan.M.loaded_segments (0x80c24 : word) = Some W_80bd4.
Proof. vm_refl. Qed.
Lemma D_80bd4 : decode_any W_80bd4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bd8 : bv 32 := 0x00060593.
Lemma F_80bd8 : fetch_word Asan.M.loaded_segments (0x80c28 : word) = Some W_80bd8.
Proof. vm_refl. Qed.
Lemma D_80bd8 : decode_any W_80bd8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bdc : bv 32 := 0x00060913.
Lemma F_80bdc : fetch_word Asan.M.loaded_segments (0x80c2c : word) = Some W_80bdc.
Proof. vm_refl. Qed.
Lemma D_80bdc : decode_any W_80bdc = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be0 : bv 32 := 0x63d020ef.
Lemma F_80be0 : fetch_word Asan.M.loaded_segments (0x80c30 : word) = Some W_80be0.
Proof. vm_refl. Qed.
Lemma D_80be0 : decode_any W_80be0 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be4 : bv 32 := 0x000a8593.
Lemma F_80be4 : fetch_word Asan.M.loaded_segments (0x80c34 : word) = Some W_80be4.
Proof. vm_refl. Qed.
Lemma D_80be4 : decode_any W_80be4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be8 : bv 32 := 0x00090613.
Lemma F_80be8 : fetch_word Asan.M.loaded_segments (0x80c38 : word) = Some W_80be8.
Proof. vm_refl. Qed.
Lemma D_80be8 : decode_any W_80be8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bec : bv 32 := 0x00050993.
Lemma F_80bec : fetch_word Asan.M.loaded_segments (0x80c3c : word) = Some W_80bec.
Proof. vm_refl. Qed.
Lemma D_80bec : decode_any W_80bec = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf0 : bv 32 := 0x00048513.
Lemma F_80bf0 : fetch_word Asan.M.loaded_segments (0x80c40 : word) = Some W_80bf0.
Proof. vm_refl. Qed.
Lemma D_80bf0 : decode_any W_80bf0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf4 : bv 32 := 0xda098ce3.
Lemma F_80bf4 : fetch_word Asan.M.loaded_segments (0x80c44 : word) = Some W_80bf4.
Proof. vm_refl. Qed.
Lemma D_80bf4 : decode_any W_80bf4 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f2c : bv 32 := 0x81010113.
Lemma F_80f2c : fetch_word Asan.M.loaded_segments (0x80f7c : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f30 : bv 32 := 0x7e113423.
Lemma F_80f30 : fetch_word Asan.M.loaded_segments (0x80f80 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f34 : bv 32 := 0x7e813023.
Lemma F_80f34 : fetch_word Asan.M.loaded_segments (0x80f84 : word) = Some W_80f34.
Proof. vm_refl. Qed.
Lemma D_80f34 : decode_any W_80f34 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f38 : bv 32 := 0x7c913c23.
Lemma F_80f38 : fetch_word Asan.M.loaded_segments (0x80f88 : word) = Some W_80f38.
Proof. vm_refl. Qed.
Lemma D_80f38 : decode_any W_80f38 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f3c : bv 32 := 0x7d213823.
Lemma F_80f3c : fetch_word Asan.M.loaded_segments (0x80f8c : word) = Some W_80f3c.
Proof. vm_refl. Qed.
Lemma D_80f3c : decode_any W_80f3c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f40 : bv 32 := 0x7d313423.
Lemma F_80f40 : fetch_word Asan.M.loaded_segments (0x80f90 : word) = Some W_80f40.
Proof. vm_refl. Qed.
Lemma D_80f40 : decode_any W_80f40 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f44 : bv 32 := 0x7d413023.
Lemma F_80f44 : fetch_word Asan.M.loaded_segments (0x80f94 : word) = Some W_80f44.
Proof. vm_refl. Qed.
Lemma D_80f44 : decode_any W_80f44 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f48 : bv 32 := 0x7b513c23.
Lemma F_80f48 : fetch_word Asan.M.loaded_segments (0x80f98 : word) = Some W_80f48.
Proof. vm_refl. Qed.
Lemma D_80f48 : decode_any W_80f48 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f4c : bv 32 := 0x7b613823.
Lemma F_80f4c : fetch_word Asan.M.loaded_segments (0x80f9c : word) = Some W_80f4c.
Proof. vm_refl. Qed.
Lemma D_80f4c : decode_any W_80f4c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f50 : bv 32 := 0x7b713423.
Lemma F_80f50 : fetch_word Asan.M.loaded_segments (0x80fa0 : word) = Some W_80f50.
Proof. vm_refl. Qed.
Lemma D_80f50 : decode_any W_80f50 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f54 : bv 32 := 0x7f010413.
Lemma F_80f54 : fetch_word Asan.M.loaded_segments (0x80fa4 : word) = Some W_80f54.
Proof. vm_refl. Qed.
Lemma D_80f54 : decode_any W_80f54 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f58 : bv 32 := 0xf9010113.
Lemma F_80f58 : fetch_word Asan.M.loaded_segments (0x80fa8 : word) = Some W_80f58.
Proof. vm_refl. Qed.
Lemma D_80f58 : decode_any W_80f58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f5c : bv 32 := 0x000e0697.
Lemma F_80f5c : fetch_word Asan.M.loaded_segments (0x80fac : word) = Some W_80f5c.
Proof. vm_refl. Qed.
Lemma D_80f5c : decode_any W_80f5c = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f60 : bv 32 := 0x7d46b683.
Lemma F_80f60 : fetch_word Asan.M.loaded_segments (0x80fb0 : word) = Some W_80f60.
Proof. vm_refl. Qed.
Lemma D_80f60 : decode_any W_80f60 = Some (Load SZ8 true 13 13 2004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f64 : bv 32 := 0x0006c683.
Lemma F_80f64 : fetch_word Asan.M.loaded_segments (0x80fb4 : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f68 : bv 32 := 0x0a068463.
Lemma F_80f68 : fetch_word Asan.M.loaded_segments (0x80fb8 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f6c : bv 32 := 0xfff5c693.
Lemma F_80f6c : fetch_word Asan.M.loaded_segments (0x80fbc : word) = Some W_80f6c.
Proof. vm_refl. Qed.
Lemma D_80f6c : decode_any W_80f6c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f70 : bv 32 := 0x80040a93.
Lemma F_80f70 : fetch_word Asan.M.loaded_segments (0x80fc0 : word) = Some W_80f70.
Proof. vm_refl. Qed.
Lemma D_80f70 : decode_any W_80f70 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f74 : bv 32 := 0xfa0a8a93.
Lemma F_80f74 : fetch_word Asan.M.loaded_segments (0x80fc4 : word) = Some W_80f74.
Proof. vm_refl. Qed.
Lemma D_80f74 : decode_any W_80f74 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f78 : bv 32 := 0x0cc6e663.
Lemma F_80f78 : fetch_word Asan.M.loaded_segments (0x80fc8 : word) = Some W_80f78.
Proof. vm_refl. Qed.
Lemma D_80f78 : decode_any W_80f78 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f7c : bv 32 := 0xfbf60a13.
Lemma F_80f7c : fetch_word Asan.M.loaded_segments (0x80fcc : word) = Some W_80f7c.
Proof. vm_refl. Qed.
Lemma D_80f7c : decode_any W_80f7c = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f80 : bv 32 := 0xfbf00693.
Lemma F_80f80 : fetch_word Asan.M.loaded_segments (0x80fd0 : word) = Some W_80f80.
Proof. vm_refl. Qed.
Lemma D_80f80 : decode_any W_80f80 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f84 : bv 32 := 0x1546f463.
Lemma F_80f84 : fetch_word Asan.M.loaded_segments (0x80fd4 : word) = Some W_80f84.
Proof. vm_refl. Qed.
Lemma D_80f84 : decode_any W_80f84 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f88 : bv 32 := 0x000e0697.
Lemma F_80f88 : fetch_word Asan.M.loaded_segments (0x80fd8 : word) = Some W_80f88.
Proof. vm_refl. Qed.
Lemma D_80f88 : decode_any W_80f88 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f8c : bv 32 := 0xc406b683.
Lemma F_80f8c : fetch_word Asan.M.loaded_segments (0x80fdc : word) = Some W_80f8c.
Proof. vm_refl. Qed.
Lemma D_80f8c : decode_any W_80f8c = Some (Load SZ8 true 13 13 3136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f90 : bv 32 := 0x00c587b3.
Lemma F_80f90 : fetch_word Asan.M.loaded_segments (0x80fe0 : word) = Some W_80f90.
Proof. vm_refl. Qed.
Lemma D_80f90 : decode_any W_80f90 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f94 : bv 32 := 0x0006b703.
Lemma F_80f94 : fetch_word Asan.M.loaded_segments (0x80fe4 : word) = Some W_80f94.
Proof. vm_refl. Qed.
Lemma D_80f94 : decode_any W_80f94 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f98 : bv 32 := 0x0035d693.
Lemma F_80f98 : fetch_word Asan.M.loaded_segments (0x80fe8 : word) = Some W_80f98.
Proof. vm_refl. Qed.
Lemma D_80f98 : decode_any W_80f98 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f9c : bv 32 := 0xfff78793.
Lemma F_80f9c : fetch_word Asan.M.loaded_segments (0x80fec : word) = Some W_80f9c.
Proof. vm_refl. Qed.
Lemma D_80f9c : decode_any W_80f9c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa0 : bv 32 := 0x0037d813.
Lemma F_80fa0 : fetch_word Asan.M.loaded_segments (0x80ff0 : word) = Some W_80fa0.
Proof. vm_refl. Qed.
Lemma D_80fa0 : decode_any W_80fa0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa4 : bv 32 := 0x00d706b3.
Lemma F_80fa4 : fetch_word Asan.M.loaded_segments (0x80ff4 : word) = Some W_80fa4.
Proof. vm_refl. Qed.
Lemma D_80fa4 : decode_any W_80fa4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fa8 : bv 32 := 0x01070733.
Lemma F_80fa8 : fetch_word Asan.M.loaded_segments (0x80ff8 : word) = Some W_80fa8.
Proof. vm_refl. Qed.
Lemma D_80fa8 : decode_any W_80fa8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fac : bv 32 := 0xff86f813.
Lemma F_80fac : fetch_word Asan.M.loaded_segments (0x80ffc : word) = Some W_80fac.
Proof. vm_refl. Qed.
Lemma D_80fac : decode_any W_80fac = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb0 : bv 32 := 0xff877893.
Lemma F_80fb0 : fetch_word Asan.M.loaded_segments (0x81000 : word) = Some W_80fb0.
Proof. vm_refl. Qed.
Lemma D_80fb0 : decode_any W_80fb0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb4 : bv 32 := 0x00083803.
Lemma F_80fb4 : fetch_word Asan.M.loaded_segments (0x81004 : word) = Some W_80fb4.
Proof. vm_refl. Qed.
Lemma D_80fb4 : decode_any W_80fb4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fb8 : bv 32 := 0x0008b883.
Lemma F_80fb8 : fetch_word Asan.M.loaded_segments (0x81008 : word) = Some W_80fb8.
Proof. vm_refl. Qed.
Lemma D_80fb8 : decode_any W_80fb8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fbc : bv 32 := 0x0108e833.
Lemma F_80fbc : fetch_word Asan.M.loaded_segments (0x8100c : word) = Some W_80fbc.
Proof. vm_refl. Qed.
Lemma D_80fbc : decode_any W_80fbc = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc0 : bv 32 := 0x1a081063.
Lemma F_80fc0 : fetch_word Asan.M.loaded_segments (0x81010 : word) = Some W_80fc0.
Proof. vm_refl. Qed.
Lemma D_80fc0 : decode_any W_80fc0 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc4 : bv 32 := 0xfff54693.
Lemma F_80fc4 : fetch_word Asan.M.loaded_segments (0x81014 : word) = Some W_80fc4.
Proof. vm_refl. Qed.
Lemma D_80fc4 : decode_any W_80fc4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fc8 : bv 32 := 0x10c6e663.
Lemma F_80fc8 : fetch_word Asan.M.loaded_segments (0x81018 : word) = Some W_80fc8.
Proof. vm_refl. Qed.
Lemma D_80fc8 : decode_any W_80fc8 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fcc : bv 32 := 0xfbf00693.
Lemma F_80fcc : fetch_word Asan.M.loaded_segments (0x8101c : word) = Some W_80fcc.
Proof. vm_refl. Qed.
Lemma D_80fcc : decode_any W_80fcc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd0 : bv 32 := 0x1946f463.
Lemma F_80fd0 : fetch_word Asan.M.loaded_segments (0x81020 : word) = Some W_80fd0.
Proof. vm_refl. Qed.
Lemma D_80fd0 : decode_any W_80fd0 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd4 : bv 32 := 0x000e0697.
Lemma F_80fd4 : fetch_word Asan.M.loaded_segments (0x81024 : word) = Some W_80fd4.
Proof. vm_refl. Qed.
Lemma D_80fd4 : decode_any W_80fd4 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fd8 : bv 32 := 0xbf46b683.
Lemma F_80fd8 : fetch_word Asan.M.loaded_segments (0x81028 : word) = Some W_80fd8.
Proof. vm_refl. Qed.
Lemma D_80fd8 : decode_any W_80fd8 = Some (Load SZ8 true 13 13 3060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fdc : bv 32 := 0x00c507b3.
Lemma F_80fdc : fetch_word Asan.M.loaded_segments (0x8102c : word) = Some W_80fdc.
Proof. vm_refl. Qed.
Lemma D_80fdc : decode_any W_80fdc = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe0 : bv 32 := 0x0006b703.
Lemma F_80fe0 : fetch_word Asan.M.loaded_segments (0x81030 : word) = Some W_80fe0.
Proof. vm_refl. Qed.
Lemma D_80fe0 : decode_any W_80fe0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe4 : bv 32 := 0x00355693.
Lemma F_80fe4 : fetch_word Asan.M.loaded_segments (0x81034 : word) = Some W_80fe4.
Proof. vm_refl. Qed.
Lemma D_80fe4 : decode_any W_80fe4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fe8 : bv 32 := 0xfff78793.
Lemma F_80fe8 : fetch_word Asan.M.loaded_segments (0x81038 : word) = Some W_80fe8.
Proof. vm_refl. Qed.
Lemma D_80fe8 : decode_any W_80fe8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80fec : bv 32 := 0x0037d813.
Lemma F_80fec : fetch_word Asan.M.loaded_segments (0x8103c : word) = Some W_80fec.
Proof. vm_refl. Qed.
Lemma D_80fec : decode_any W_80fec = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff0 : bv 32 := 0x00d706b3.
Lemma F_80ff0 : fetch_word Asan.M.loaded_segments (0x81040 : word) = Some W_80ff0.
Proof. vm_refl. Qed.
Lemma D_80ff0 : decode_any W_80ff0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff4 : bv 32 := 0x01070733.
Lemma F_80ff4 : fetch_word Asan.M.loaded_segments (0x81044 : word) = Some W_80ff4.
Proof. vm_refl. Qed.
Lemma D_80ff4 : decode_any W_80ff4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ff8 : bv 32 := 0xff86f813.
Lemma F_80ff8 : fetch_word Asan.M.loaded_segments (0x81048 : word) = Some W_80ff8.
Proof. vm_refl. Qed.
Lemma D_80ff8 : decode_any W_80ff8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ffc : bv 32 := 0xff877893.
Lemma F_80ffc : fetch_word Asan.M.loaded_segments (0x8104c : word) = Some W_80ffc.
Proof. vm_refl. Qed.
Lemma D_80ffc : decode_any W_80ffc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

