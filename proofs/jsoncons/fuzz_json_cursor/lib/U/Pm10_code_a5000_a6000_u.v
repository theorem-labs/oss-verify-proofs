(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a5078 : bv 32 := 0x00050593.
Lemma F_a5078 : fetch_word Ubsan.M.loaded_segments (0xa6e68 : word) = Some W_a5078.
Proof. vm_refl. Qed.
Lemma D_a5078 : decode_any W_a5078 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a507c : bv 32 := 0x05e00893.
Lemma F_a507c : fetch_word Ubsan.M.loaded_segments (0xa6e6c : word) = Some W_a507c.
Proof. vm_refl. Qed.
Lemma D_a507c : decode_any W_a507c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5080 : bv 32 := 0x00000073.
Lemma F_a5080 : fetch_word Ubsan.M.loaded_segments (0xa6e70 : word) = Some W_a5080.
Proof. vm_refl. Qed.
Lemma D_a5080 : decode_any W_a5080 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a5080 : is_ecall W_a5080 = true.
Proof. reflexivity. Qed.

Definition W_a50c4 : bv 32 := 0xfd010113.
Lemma F_a50c4 : fetch_word Ubsan.M.loaded_segments (0xa6eb4 : word) = Some W_a50c4.
Proof. vm_refl. Qed.
Lemma D_a50c4 : decode_any W_a50c4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50c8 : bv 32 := 0x02113423.
Lemma F_a50c8 : fetch_word Ubsan.M.loaded_segments (0xa6eb8 : word) = Some W_a50c8.
Proof. vm_refl. Qed.
Lemma D_a50c8 : decode_any W_a50c8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50cc : bv 32 := 0x02813023.
Lemma F_a50cc : fetch_word Ubsan.M.loaded_segments (0xa6ebc : word) = Some W_a50cc.
Proof. vm_refl. Qed.
Lemma D_a50cc : decode_any W_a50cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50d0 : bv 32 := 0x00913c23.
Lemma F_a50d0 : fetch_word Ubsan.M.loaded_segments (0xa6ec0 : word) = Some W_a50d0.
Proof. vm_refl. Qed.
Lemma D_a50d0 : decode_any W_a50d0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50d4 : bv 32 := 0x01213823.
Lemma F_a50d4 : fetch_word Ubsan.M.loaded_segments (0xa6ec4 : word) = Some W_a50d4.
Proof. vm_refl. Qed.
Lemma D_a50d4 : decode_any W_a50d4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50d8 : bv 32 := 0x01313423.
Lemma F_a50d8 : fetch_word Ubsan.M.loaded_segments (0xa6ec8 : word) = Some W_a50d8.
Proof. vm_refl. Qed.
Lemma D_a50d8 : decode_any W_a50d8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50dc : bv 32 := 0x00050517.
Lemma F_a50dc : fetch_word Ubsan.M.loaded_segments (0xa6ecc : word) = Some W_a50dc.
Proof. vm_refl. Qed.
Lemma D_a50dc : decode_any W_a50dc = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50e0 : bv 32 := 0x97c50913.
Lemma F_a50e0 : fetch_word Ubsan.M.loaded_segments (0xa6ed0 : word) = Some W_a50e0.
Proof. vm_refl. Qed.
Lemma D_a50e0 : decode_any W_a50e0 = Some (OpImm ALU_ADD 18 10 2428, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50e4 : bv 32 := 0x00490413.
Lemma F_a50e4 : fetch_word Ubsan.M.loaded_segments (0xa6ed4 : word) = Some W_a50e4.
Proof. vm_refl. Qed.
Lemma D_a50e4 : decode_any W_a50e4 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50e8 : bv 32 := 0x00040513.
Lemma F_a50e8 : fetch_word Ubsan.M.loaded_segments (0xa6ed8 : word) = Some W_a50e8.
Proof. vm_refl. Qed.
Lemma D_a50e8 : decode_any W_a50e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50ec : bv 32 := 0x648110ef.
Lemma F_a50ec : fetch_word Ubsan.M.loaded_segments (0xa6edc : word) = Some W_a50ec.
Proof. vm_refl. Qed.
Lemma D_a50ec : decode_any W_a50ec = Some (Jal 1 71240, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50f0 : bv 32 := 0x01093503.
Lemma F_a50f0 : fetch_word Ubsan.M.loaded_segments (0xa6ee0 : word) = Some W_a50f0.
Proof. vm_refl. Qed.
Lemma D_a50f0 : decode_any W_a50f0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50f4 : bv 32 := 0x06050863.
Lemma F_a50f4 : fetch_word Ubsan.M.loaded_segments (0xa6ee4 : word) = Some W_a50f4.
Proof. vm_refl. Qed.
Lemma D_a50f4 : decode_any W_a50f4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50f8 : bv 32 := 0x00892583.
Lemma F_a50f8 : fetch_word Ubsan.M.loaded_segments (0xa6ee8 : word) = Some W_a50f8.
Proof. vm_refl. Qed.
Lemma D_a50f8 : decode_any W_a50f8 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50fc : bv 32 := 0x0180006f.
Lemma F_a50fc : fetch_word Ubsan.M.loaded_segments (0xa6eec : word) = Some W_a50fc.
Proof. vm_refl. Qed.
Lemma D_a50fc : decode_any W_a50fc = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5100 : bv 32 := 0x00053503.
Lemma F_a5100 : fetch_word Ubsan.M.loaded_segments (0xa6ef0 : word) = Some W_a5100.
Proof. vm_refl. Qed.
Lemma D_a5100 : decode_any W_a5100 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5104 : bv 32 := 0x02000593.
Lemma F_a5104 : fetch_word Ubsan.M.loaded_segments (0xa6ef4 : word) = Some W_a5104.
Proof. vm_refl. Qed.
Lemma D_a5104 : decode_any W_a5104 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5108 : bv 32 := 0x00b92423.
Lemma F_a5108 : fetch_word Ubsan.M.loaded_segments (0xa6ef8 : word) = Some W_a5108.
Proof. vm_refl. Qed.
Lemma D_a5108 : decode_any W_a5108 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a510c : bv 32 := 0x00a93823.
Lemma F_a510c : fetch_word Ubsan.M.loaded_segments (0xa6efc : word) = Some W_a510c.
Proof. vm_refl. Qed.
Lemma D_a510c : decode_any W_a510c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5110 : bv 32 := 0x04050a63.
Lemma F_a5110 : fetch_word Ubsan.M.loaded_segments (0xa6f00 : word) = Some W_a5110.
Proof. vm_refl. Qed.
Lemma D_a5110 : decode_any W_a5110 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5114 : bv 32 := 0xfff5861b.
Lemma F_a5114 : fetch_word Ubsan.M.loaded_segments (0xa6f04 : word) = Some W_a5114.
Proof. vm_refl. Qed.
Lemma D_a5114 : decode_any W_a5114 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5118 : bv 32 := 0x00c92423.
Lemma F_a5118 : fetch_word Ubsan.M.loaded_segments (0xa6f08 : word) = Some W_a5118.
Proof. vm_refl. Qed.
Lemma D_a5118 : decode_any W_a5118 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a511c : bv 32 := 0xfeb052e3.
Lemma F_a511c : fetch_word Ubsan.M.loaded_segments (0xa6f0c : word) = Some W_a511c.
Proof. vm_refl. Qed.
Lemma D_a511c : decode_any W_a511c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5120 : bv 32 := 0x01093503.
Lemma F_a5120 : fetch_word Ubsan.M.loaded_segments (0xa6f10 : word) = Some W_a5120.
Proof. vm_refl. Qed.
Lemma D_a5120 : decode_any W_a5120 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5124 : bv 32 := 0x00361613.
Lemma F_a5124 : fetch_word Ubsan.M.loaded_segments (0xa6f14 : word) = Some W_a5124.
Proof. vm_refl. Qed.
Lemma D_a5124 : decode_any W_a5124 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5128 : bv 32 := 0x00c50533.
Lemma F_a5128 : fetch_word Ubsan.M.loaded_segments (0xa6f18 : word) = Some W_a5128.
Proof. vm_refl. Qed.
Lemma D_a5128 : decode_any W_a5128 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a512c : bv 32 := 0x00853983.
Lemma F_a512c : fetch_word Ubsan.M.loaded_segments (0xa6f1c : word) = Some W_a512c.
Proof. vm_refl. Qed.
Lemma D_a512c : decode_any W_a512c = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5130 : bv 32 := 0x10853483.
Lemma F_a5130 : fetch_word Ubsan.M.loaded_segments (0xa6f20 : word) = Some W_a5130.
Proof. vm_refl. Qed.
Lemma D_a5130 : decode_any W_a5130 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5134 : bv 32 := 0x00040513.
Lemma F_a5134 : fetch_word Ubsan.M.loaded_segments (0xa6f24 : word) = Some W_a5134.
Proof. vm_refl. Qed.
Lemma D_a5134 : decode_any W_a5134 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5138 : bv 32 := 0x085110ef.
Lemma F_a5138 : fetch_word Ubsan.M.loaded_segments (0xa6f28 : word) = Some W_a5138.
Proof. vm_refl. Qed.
Lemma D_a5138 : decode_any W_a5138 = Some (Jal 1 71812, 4%Z).
Proof. vm_refl. Qed.

Definition W_a513c : bv 32 := 0x00048513.
Lemma F_a513c : fetch_word Ubsan.M.loaded_segments (0xa6f2c : word) = Some W_a513c.
Proof. vm_refl. Qed.
Lemma D_a513c : decode_any W_a513c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5140 : bv 32 := 0x000980e7.
Lemma F_a5140 : fetch_word Ubsan.M.loaded_segments (0xa6f30 : word) = Some W_a5140.
Proof. vm_refl. Qed.
Lemma D_a5140 : decode_any W_a5140 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5144 : bv 32 := 0x00040513.
Lemma F_a5144 : fetch_word Ubsan.M.loaded_segments (0xa6f34 : word) = Some W_a5144.
Proof. vm_refl. Qed.
Lemma D_a5144 : decode_any W_a5144 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5148 : bv 32 := 0x5ec110ef.
Lemma F_a5148 : fetch_word Ubsan.M.loaded_segments (0xa6f38 : word) = Some W_a5148.
Proof. vm_refl. Qed.
Lemma D_a5148 : decode_any W_a5148 = Some (Jal 1 71148, 4%Z).
Proof. vm_refl. Qed.

Definition W_a514c : bv 32 := 0x00892503.
Lemma F_a514c : fetch_word Ubsan.M.loaded_segments (0xa6f3c : word) = Some W_a514c.
Proof. vm_refl. Qed.
Lemma D_a514c : decode_any W_a514c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5150 : bv 32 := 0xfff5061b.
Lemma F_a5150 : fetch_word Ubsan.M.loaded_segments (0xa6f40 : word) = Some W_a5150.
Proof. vm_refl. Qed.
Lemma D_a5150 : decode_any W_a5150 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5154 : bv 32 := 0x00c92423.
Lemma F_a5154 : fetch_word Ubsan.M.loaded_segments (0xa6f44 : word) = Some W_a5154.
Proof. vm_refl. Qed.
Lemma D_a5154 : decode_any W_a5154 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5158 : bv 32 := 0xfca044e3.
Lemma F_a5158 : fetch_word Ubsan.M.loaded_segments (0xa6f48 : word) = Some W_a5158.
Proof. vm_refl. Qed.
Lemma D_a5158 : decode_any W_a5158 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a515c : bv 32 := 0x01093503.
Lemma F_a515c : fetch_word Ubsan.M.loaded_segments (0xa6f4c : word) = Some W_a515c.
Proof. vm_refl. Qed.
Lemma D_a515c : decode_any W_a515c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5160 : bv 32 := 0xfa1ff06f.
Lemma F_a5160 : fetch_word Ubsan.M.loaded_segments (0xa6f50 : word) = Some W_a5160.
Proof. vm_refl. Qed.
Lemma D_a5160 : decode_any W_a5160 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5164 : bv 32 := 0x00100513.
Lemma F_a5164 : fetch_word Ubsan.M.loaded_segments (0xa6f54 : word) = Some W_a5164.
Proof. vm_refl. Qed.
Lemma D_a5164 : decode_any W_a5164 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5168 : bv 32 := 0x00a90023.
Lemma F_a5168 : fetch_word Ubsan.M.loaded_segments (0xa6f58 : word) = Some W_a5168.
Proof. vm_refl. Qed.
Lemma D_a5168 : decode_any W_a5168 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a516c : bv 32 := 0x00040513.
Lemma F_a516c : fetch_word Ubsan.M.loaded_segments (0xa6f5c : word) = Some W_a516c.
Proof. vm_refl. Qed.
Lemma D_a516c : decode_any W_a516c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5170 : bv 32 := 0x02813083.
Lemma F_a5170 : fetch_word Ubsan.M.loaded_segments (0xa6f60 : word) = Some W_a5170.
Proof. vm_refl. Qed.
Lemma D_a5170 : decode_any W_a5170 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5174 : bv 32 := 0x02013403.
Lemma F_a5174 : fetch_word Ubsan.M.loaded_segments (0xa6f64 : word) = Some W_a5174.
Proof. vm_refl. Qed.
Lemma D_a5174 : decode_any W_a5174 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5178 : bv 32 := 0x01813483.
Lemma F_a5178 : fetch_word Ubsan.M.loaded_segments (0xa6f68 : word) = Some W_a5178.
Proof. vm_refl. Qed.
Lemma D_a5178 : decode_any W_a5178 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a517c : bv 32 := 0x01013903.
Lemma F_a517c : fetch_word Ubsan.M.loaded_segments (0xa6f6c : word) = Some W_a517c.
Proof. vm_refl. Qed.
Lemma D_a517c : decode_any W_a517c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5180 : bv 32 := 0x00813983.
Lemma F_a5180 : fetch_word Ubsan.M.loaded_segments (0xa6f70 : word) = Some W_a5180.
Proof. vm_refl. Qed.
Lemma D_a5180 : decode_any W_a5180 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5184 : bv 32 := 0x03010113.
Lemma F_a5184 : fetch_word Ubsan.M.loaded_segments (0xa6f74 : word) = Some W_a5184.
Proof. vm_refl. Qed.
Lemma D_a5184 : decode_any W_a5184 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5188 : bv 32 := 0x0351106f.
Lemma F_a5188 : fetch_word Ubsan.M.loaded_segments (0xa6f78 : word) = Some W_a5188.
Proof. vm_refl. Qed.
Lemma D_a5188 : decode_any W_a5188 = Some (Jal 0 71732, 4%Z).
Proof. vm_refl. Qed.

Definition W_a518c : bv 32 := 0x00008067.
Lemma F_a518c : fetch_word Ubsan.M.loaded_segments (0xa6f7c : word) = Some W_a518c.
Proof. vm_refl. Qed.
Lemma D_a518c : decode_any W_a518c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a531c : bv 32 := 0x00050067.
Lemma F_a531c : fetch_word Ubsan.M.loaded_segments (0xa710c : word) = Some W_a531c.
Proof. vm_refl. Qed.
Lemma D_a531c : decode_any W_a531c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5320 : bv 32 := 0x00008067.
Lemma F_a5320 : fetch_word Ubsan.M.loaded_segments (0xa7110 : word) = Some W_a5320.
Proof. vm_refl. Qed.
Lemma D_a5320 : decode_any W_a5320 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5324 : bv 32 := 0xfe010113.
Lemma F_a5324 : fetch_word Ubsan.M.loaded_segments (0xa7114 : word) = Some W_a5324.
Proof. vm_refl. Qed.
Lemma D_a5324 : decode_any W_a5324 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5328 : bv 32 := 0x00113c23.
Lemma F_a5328 : fetch_word Ubsan.M.loaded_segments (0xa7118 : word) = Some W_a5328.
Proof. vm_refl. Qed.
Lemma D_a5328 : decode_any W_a5328 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a532c : bv 32 := 0x00813823.
Lemma F_a532c : fetch_word Ubsan.M.loaded_segments (0xa711c : word) = Some W_a532c.
Proof. vm_refl. Qed.
Lemma D_a532c : decode_any W_a532c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5330 : bv 32 := 0x00913423.
Lemma F_a5330 : fetch_word Ubsan.M.loaded_segments (0xa7120 : word) = Some W_a5330.
Proof. vm_refl. Qed.
Lemma D_a5330 : decode_any W_a5330 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5334 : bv 32 := 0x0001d517.
Lemma F_a5334 : fetch_word Ubsan.M.loaded_segments (0xa7124 : word) = Some W_a5334.
Proof. vm_refl. Qed.
Lemma D_a5334 : decode_any W_a5334 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5338 : bv 32 := 0x0001d597.
Lemma F_a5338 : fetch_word Ubsan.M.loaded_segments (0xa7128 : word) = Some W_a5338.
Proof. vm_refl. Qed.
Lemma D_a5338 : decode_any W_a5338 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a533c : bv 32 := 0x92c53503.
Lemma F_a533c : fetch_word Ubsan.M.loaded_segments (0xa712c : word) = Some W_a533c.
Proof. vm_refl. Qed.
Lemma D_a533c : decode_any W_a533c = Some (Load SZ8 true 10 10 2348, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5340 : bv 32 := 0x9305b403.
Lemma F_a5340 : fetch_word Ubsan.M.loaded_segments (0xa7130 : word) = Some W_a5340.
Proof. vm_refl. Qed.
Lemma D_a5340 : decode_any W_a5340 = Some (Load SZ8 true 8 11 2352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5344 : bv 32 := 0x00a47c63.
Lemma F_a5344 : fetch_word Ubsan.M.loaded_segments (0xa7134 : word) = Some W_a5344.
Proof. vm_refl. Qed.
Lemma D_a5344 : decode_any W_a5344 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5348 : bv 32 := 0xff853583.
Lemma F_a5348 : fetch_word Ubsan.M.loaded_segments (0xa7138 : word) = Some W_a5348.
Proof. vm_refl. Qed.
Lemma D_a5348 : decode_any W_a5348 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a534c : bv 32 := 0xff850493.
Lemma F_a534c : fetch_word Ubsan.M.loaded_segments (0xa713c : word) = Some W_a534c.
Proof. vm_refl. Qed.
Lemma D_a534c : decode_any W_a534c = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5350 : bv 32 := 0x000580e7.
Lemma F_a5350 : fetch_word Ubsan.M.loaded_segments (0xa7140 : word) = Some W_a5350.
Proof. vm_refl. Qed.
Lemma D_a5350 : decode_any W_a5350 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5354 : bv 32 := 0x00048513.
Lemma F_a5354 : fetch_word Ubsan.M.loaded_segments (0xa7144 : word) = Some W_a5354.
Proof. vm_refl. Qed.
Lemma D_a5354 : decode_any W_a5354 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5358 : bv 32 := 0xfe9468e3.
Lemma F_a5358 : fetch_word Ubsan.M.loaded_segments (0xa7148 : word) = Some W_a5358.
Proof. vm_refl. Qed.
Lemma D_a5358 : decode_any W_a5358 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a535c : bv 32 := 0x01813083.
Lemma F_a535c : fetch_word Ubsan.M.loaded_segments (0xa714c : word) = Some W_a535c.
Proof. vm_refl. Qed.
Lemma D_a535c : decode_any W_a535c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5360 : bv 32 := 0x01013403.
Lemma F_a5360 : fetch_word Ubsan.M.loaded_segments (0xa7150 : word) = Some W_a5360.
Proof. vm_refl. Qed.
Lemma D_a5360 : decode_any W_a5360 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5364 : bv 32 := 0x00813483.
Lemma F_a5364 : fetch_word Ubsan.M.loaded_segments (0xa7154 : word) = Some W_a5364.
Proof. vm_refl. Qed.
Lemma D_a5364 : decode_any W_a5364 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5368 : bv 32 := 0x02010113.
Lemma F_a5368 : fetch_word Ubsan.M.loaded_segments (0xa7158 : word) = Some W_a5368.
Proof. vm_refl. Qed.
Lemma D_a5368 : decode_any W_a5368 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a536c : bv 32 := 0xfb5ff06f.
Lemma F_a536c : fetch_word Ubsan.M.loaded_segments (0xa715c : word) = Some W_a536c.
Proof. vm_refl. Qed.
Lemma D_a536c : decode_any W_a536c = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5370 : bv 32 := 0xff010113.
Lemma F_a5370 : fetch_word Ubsan.M.loaded_segments (0xa7160 : word) = Some W_a5370.
Proof. vm_refl. Qed.
Lemma D_a5370 : decode_any W_a5370 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5374 : bv 32 := 0x00113423.
Lemma F_a5374 : fetch_word Ubsan.M.loaded_segments (0xa7164 : word) = Some W_a5374.
Proof. vm_refl. Qed.
Lemma D_a5374 : decode_any W_a5374 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5378 : bv 32 := 0x00813023.
Lemma F_a5378 : fetch_word Ubsan.M.loaded_segments (0xa7168 : word) = Some W_a5378.
Proof. vm_refl. Qed.
Lemma D_a5378 : decode_any W_a5378 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a537c : bv 32 := 0x00000593.
Lemma F_a537c : fetch_word Ubsan.M.loaded_segments (0xa716c : word) = Some W_a537c.
Proof. vm_refl. Qed.
Lemma D_a537c : decode_any W_a537c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5380 : bv 32 := 0x00020613.
Lemma F_a5380 : fetch_word Ubsan.M.loaded_segments (0xa7170 : word) = Some W_a5380.
Proof. vm_refl. Qed.
Lemma D_a5380 : decode_any W_a5380 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5384 : bv 32 := 0xf5862603.
Lemma F_a5384 : fetch_word Ubsan.M.loaded_segments (0xa7174 : word) = Some W_a5384.
Proof. vm_refl. Qed.
Lemma D_a5384 : decode_any W_a5384 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5388 : bv 32 := 0x00050697.
Lemma F_a5388 : fetch_word Ubsan.M.loaded_segments (0xa7178 : word) = Some W_a5388.
Proof. vm_refl. Qed.
Lemma D_a5388 : decode_any W_a5388 = Some (Auipc 13 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a538c : bv 32 := 0x8f068693.
Lemma F_a538c : fetch_word Ubsan.M.loaded_segments (0xa717c : word) = Some W_a538c.
Proof. vm_refl. Qed.
Lemma D_a538c : decode_any W_a538c = Some (OpImm ALU_ADD 13 13 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5390 : bv 32 := 0x1606a72f.
Lemma F_a5390 : fetch_word Ubsan.M.loaded_segments (0xa7180 : word) = Some W_a5390.
Proof. vm_refl. Qed.
Lemma D_a5390 : decode_any W_a5390 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5394 : bv 32 := 0x00b71663.
Lemma F_a5394 : fetch_word Ubsan.M.loaded_segments (0xa7184 : word) = Some W_a5394.
Proof. vm_refl. Qed.
Lemma D_a5394 : decode_any W_a5394 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5398 : bv 32 := 0x1ec6a7af.
Lemma F_a5398 : fetch_word Ubsan.M.loaded_segments (0xa7188 : word) = Some W_a5398.
Proof. vm_refl. Qed.
Lemma D_a5398 : decode_any W_a5398 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a539c : bv 32 := 0xfe079ae3.
Lemma F_a539c : fetch_word Ubsan.M.loaded_segments (0xa718c : word) = Some W_a539c.
Proof. vm_refl. Qed.
Lemma D_a539c : decode_any W_a539c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53a0 : bv 32 := 0x0007059b.
Lemma F_a53a0 : fetch_word Ubsan.M.loaded_segments (0xa7190 : word) = Some W_a53a0.
Proof. vm_refl. Qed.
Lemma D_a53a0 : decode_any W_a53a0 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53a4 : bv 32 := 0x02c58263.
Lemma F_a53a4 : fetch_word Ubsan.M.loaded_segments (0xa7194 : word) = Some W_a53a4.
Proof. vm_refl. Qed.
Lemma D_a53a4 : decode_any W_a53a4 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53a8 : bv 32 := 0x02058263.
Lemma F_a53a8 : fetch_word Ubsan.M.loaded_segments (0xa7198 : word) = Some W_a53a8.
Proof. vm_refl. Qed.
Lemma D_a53a8 : decode_any W_a53a8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53cc : bv 32 := 0x00050413.
Lemma F_a53cc : fetch_word Ubsan.M.loaded_segments (0xa71bc : word) = Some W_a53cc.
Proof. vm_refl. Qed.
Lemma D_a53cc : decode_any W_a53cc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53d0 : bv 32 := 0xcf5ff0ef.
Lemma F_a53d0 : fetch_word Ubsan.M.loaded_segments (0xa71c0 : word) = Some W_a53d0.
Proof. vm_refl. Qed.
Lemma D_a53d0 : decode_any W_a53d0 = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53d4 : bv 32 := 0xf51ff0ef.
Lemma F_a53d4 : fetch_word Ubsan.M.loaded_segments (0xa71c4 : word) = Some W_a53d4.
Proof. vm_refl. Qed.
Lemma D_a53d4 : decode_any W_a53d4 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53d8 : bv 32 := 0x6dc050ef.
Lemma F_a53d8 : fetch_word Ubsan.M.loaded_segments (0xa71c8 : word) = Some W_a53d8.
Proof. vm_refl. Qed.
Lemma D_a53d8 : decode_any W_a53d8 = Some (Jal 1 22236, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53dc : bv 32 := 0x00040513.
Lemma F_a53dc : fetch_word Ubsan.M.loaded_segments (0xa71cc : word) = Some W_a53dc.
Proof. vm_refl. Qed.
Lemma D_a53dc : decode_any W_a53dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a53e0 : bv 32 := 0xc99ff0ef.
Lemma F_a53e0 : fetch_word Ubsan.M.loaded_segments (0xa71d0 : word) = Some W_a53e0.
Proof. vm_refl. Qed.
Lemma D_a53e0 : decode_any W_a53e0 = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54c8 : bv 32 := 0xff010113.
Lemma F_a54c8 : fetch_word Ubsan.M.loaded_segments (0xa72b8 : word) = Some W_a54c8.
Proof. vm_refl. Qed.
Lemma D_a54c8 : decode_any W_a54c8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54cc : bv 32 := 0x00113423.
Lemma F_a54cc : fetch_word Ubsan.M.loaded_segments (0xa72bc : word) = Some W_a54cc.
Proof. vm_refl. Qed.
Lemma D_a54cc : decode_any W_a54cc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54d0 : bv 32 := 0x00050e63.
Lemma F_a54d0 : fetch_word Ubsan.M.loaded_segments (0xa72c0 : word) = Some W_a54d0.
Proof. vm_refl. Qed.
Lemma D_a54d0 : decode_any W_a54d0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54d4 : bv 32 := 0x00050593.
Lemma F_a54d4 : fetch_word Ubsan.M.loaded_segments (0xa72c4 : word) = Some W_a54d4.
Proof. vm_refl. Qed.
Lemma D_a54d4 : decode_any W_a54d4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54d8 : bv 32 := 0x0001c517.
Lemma F_a54d8 : fetch_word Ubsan.M.loaded_segments (0xa72c8 : word) = Some W_a54d8.
Proof. vm_refl. Qed.
Lemma D_a54d8 : decode_any W_a54d8 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54dc : bv 32 := 0x78053503.
Lemma F_a54dc : fetch_word Ubsan.M.loaded_segments (0xa72cc : word) = Some W_a54dc.
Proof. vm_refl. Qed.
Lemma D_a54dc : decode_any W_a54dc = Some (Load SZ8 true 10 10 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54e0 : bv 32 := 0x00800613.
Lemma F_a54e0 : fetch_word Ubsan.M.loaded_segments (0xa72d0 : word) = Some W_a54e0.
Proof. vm_refl. Qed.
Lemma D_a54e0 : decode_any W_a54e0 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54e4 : bv 32 := 0x5c0100ef.
Lemma F_a54e4 : fetch_word Ubsan.M.loaded_segments (0xa72d4 : word) = Some W_a54e4.
Proof. vm_refl. Qed.
Lemma D_a54e4 : decode_any W_a54e4 = Some (Jal 1 67008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a54e8 : bv 32 := 0x01c0006f.
Lemma F_a54e8 : fetch_word Ubsan.M.loaded_segments (0xa72d8 : word) = Some W_a54e8.
Proof. vm_refl. Qed.
Lemma D_a54e8 : decode_any W_a54e8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5504 : bv 32 := 0x0001c517.
Lemma F_a5504 : fetch_word Ubsan.M.loaded_segments (0xa72f4 : word) = Some W_a5504.
Proof. vm_refl. Qed.
Lemma D_a5504 : decode_any W_a5504 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5508 : bv 32 := 0x75453503.
Lemma F_a5508 : fetch_word Ubsan.M.loaded_segments (0xa72f8 : word) = Some W_a5508.
Proof. vm_refl. Qed.
Lemma D_a5508 : decode_any W_a5508 = Some (Load SZ8 true 10 10 1876, 4%Z).
Proof. vm_refl. Qed.

Definition W_a550c : bv 32 := 0x000500a3.
Lemma F_a550c : fetch_word Ubsan.M.loaded_segments (0xa72fc : word) = Some W_a550c.
Proof. vm_refl. Qed.
Lemma D_a550c : decode_any W_a550c = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5510 : bv 32 := 0x00053503.
Lemma F_a5510 : fetch_word Ubsan.M.loaded_segments (0xa7300 : word) = Some W_a5510.
Proof. vm_refl. Qed.
Lemma D_a5510 : decode_any W_a5510 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5514 : bv 32 := 0x00020593.
Lemma F_a5514 : fetch_word Ubsan.M.loaded_segments (0xa7304 : word) = Some W_a5514.
Proof. vm_refl. Qed.
Lemma D_a5514 : decode_any W_a5514 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5518 : bv 32 := 0xfea5b823.
Lemma F_a5518 : fetch_word Ubsan.M.loaded_segments (0xa7308 : word) = Some W_a5518.
Proof. vm_refl. Qed.
Lemma D_a5518 : decode_any W_a5518 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a551c : bv 32 := 0x00813083.
Lemma F_a551c : fetch_word Ubsan.M.loaded_segments (0xa730c : word) = Some W_a551c.
Proof. vm_refl. Qed.
Lemma D_a551c : decode_any W_a551c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5520 : bv 32 := 0x01010113.
Lemma F_a5520 : fetch_word Ubsan.M.loaded_segments (0xa7310 : word) = Some W_a5520.
Proof. vm_refl. Qed.
Lemma D_a5520 : decode_any W_a5520 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5524 : bv 32 := 0x00008067.
Lemma F_a5524 : fetch_word Ubsan.M.loaded_segments (0xa7314 : word) = Some W_a5524.
Proof. vm_refl. Qed.
Lemma D_a5524 : decode_any W_a5524 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5530 : bv 32 := 0xfffff5b7.
Lemma F_a5530 : fetch_word Ubsan.M.loaded_segments (0xa7320 : word) = Some W_a5530.
Proof. vm_refl. Qed.
Lemma D_a5530 : decode_any W_a5530 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5534 : bv 32 := 0x0015859b.
Lemma F_a5534 : fetch_word Ubsan.M.loaded_segments (0xa7324 : word) = Some W_a5534.
Proof. vm_refl. Qed.
Lemma D_a5534 : decode_any W_a5534 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5538 : bv 32 := 0x02b56663.
Lemma F_a5538 : fetch_word Ubsan.M.loaded_segments (0xa7328 : word) = Some W_a5538.
Proof. vm_refl. Qed.
Lemma D_a5538 : decode_any W_a5538 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5564 : bv 32 := 0x00008067.
Lemma F_a5564 : fetch_word Ubsan.M.loaded_segments (0xa7354 : word) = Some W_a5564.
Proof. vm_refl. Qed.
Lemma D_a5564 : decode_any W_a5564 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

