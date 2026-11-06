(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_201fc : bv 32 := 0xffff0197.
Lemma F_201fc : fetch_word Ubsan.M.loaded_segments (0x201fc : word) = Some W_201fc.
Proof. vm_refl. Qed.
Lemma D_201fc : decode_any W_201fc = Some (Auipc 3 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_20200 : bv 32 := 0x60418193.
Lemma F_20200 : fetch_word Ubsan.M.loaded_segments (0x20200 : word) = Some W_20200.
Proof. vm_refl. Qed.
Lemma D_20200 : decode_any W_20200 = Some (OpImm ALU_ADD 3 3 1540, 4%Z).
Proof. vm_refl. Qed.

Definition W_20204 : bv 32 := 0x00010513.
Lemma F_20204 : fetch_word Ubsan.M.loaded_segments (0x20204 : word) = Some W_20204.
Proof. vm_refl. Qed.
Lemma D_20204 : decode_any W_20204 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20208 : bv 32 := 0xfffe0597.
Lemma F_20208 : fetch_word Ubsan.M.loaded_segments (0x20208 : word) = Some W_20208.
Proof. vm_refl. Qed.
Lemma D_20208 : decode_any W_20208 = Some (Auipc 11 1048544, 4%Z).
Proof. vm_refl. Qed.

Definition W_2020c : bv 32 := 0xdf858593.
Lemma F_2020c : fetch_word Ubsan.M.loaded_segments (0x2020c : word) = Some W_2020c.
Proof. vm_refl. Qed.
Lemma D_2020c : decode_any W_2020c = Some (OpImm ALU_ADD 11 11 3576, 4%Z).
Proof. vm_refl. Qed.

Definition W_20210 : bv 32 := 0xff017113.
Lemma F_20210 : fetch_word Ubsan.M.loaded_segments (0x20210 : word) = Some W_20210.
Proof. vm_refl. Qed.
Lemma D_20210 : decode_any W_20210 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_20214 : bv 32 := 0x0040006f.
Lemma F_20214 : fetch_word Ubsan.M.loaded_segments (0x20214 : word) = Some W_20214.
Proof. vm_refl. Qed.
Lemma D_20214 : decode_any W_20214 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20218 : bv 32 := 0x00052583.
Lemma F_20218 : fetch_word Ubsan.M.loaded_segments (0x20218 : word) = Some W_20218.
Proof. vm_refl. Qed.
Lemma D_20218 : decode_any W_20218 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2021c : bv 32 := 0x0003f617.
Lemma F_2021c : fetch_word Ubsan.M.loaded_segments (0x2021c : word) = Some W_2021c.
Proof. vm_refl. Qed.
Lemma D_2021c : decode_any W_2021c = Some (Auipc 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_20220 : bv 32 := 0x0003f697.
Lemma F_20220 : fetch_word Ubsan.M.loaded_segments (0x20220 : word) = Some W_20220.
Proof. vm_refl. Qed.
Lemma D_20220 : decode_any W_20220 = Some (Auipc 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_20224 : bv 32 := 0x0003f717.
Lemma F_20224 : fetch_word Ubsan.M.loaded_segments (0x20224 : word) = Some W_20224.
Proof. vm_refl. Qed.
Lemma D_20224 : decode_any W_20224 = Some (Auipc 14 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_20228 : bv 32 := 0xd8463783.
Lemma F_20228 : fetch_word Ubsan.M.loaded_segments (0x20228 : word) = Some W_20228.
Proof. vm_refl. Qed.
Lemma D_20228 : decode_any W_20228 = Some (Load SZ8 true 15 12 3460, 4%Z).
Proof. vm_refl. Qed.

Definition W_2022c : bv 32 := 0xd886b683.
Lemma F_2022c : fetch_word Ubsan.M.loaded_segments (0x2022c : word) = Some W_2022c.
Proof. vm_refl. Qed.
Lemma D_2022c : decode_any W_2022c = Some (Load SZ8 true 13 13 3464, 4%Z).
Proof. vm_refl. Qed.

Definition W_20230 : bv 32 := 0xd8c73703.
Lemma F_20230 : fetch_word Ubsan.M.loaded_segments (0x20230 : word) = Some W_20230.
Proof. vm_refl. Qed.
Lemma D_20230 : decode_any W_20230 = Some (Load SZ8 true 14 14 3468, 4%Z).
Proof. vm_refl. Qed.

Definition W_20234 : bv 32 := 0x00850613.
Lemma F_20234 : fetch_word Ubsan.M.loaded_segments (0x20234 : word) = Some W_20234.
Proof. vm_refl. Qed.
Lemma D_20234 : decode_any W_20234 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20238 : bv 32 := 0x00078513.
Lemma F_20238 : fetch_word Ubsan.M.loaded_segments (0x20238 : word) = Some W_20238.
Proof. vm_refl. Qed.
Lemma D_20238 : decode_any W_20238 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2023c : bv 32 := 0x00000793.
Lemma F_2023c : fetch_word Ubsan.M.loaded_segments (0x2023c : word) = Some W_2023c.
Proof. vm_refl. Qed.
Lemma D_2023c : decode_any W_2023c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20240 : bv 32 := 0x6f02b06f.
Lemma F_20240 : fetch_word Ubsan.M.loaded_segments (0x20240 : word) = Some W_20240.
Proof. vm_refl. Qed.
Lemma D_20240 : decode_any W_20240 = Some (Jal 0 177904, 4%Z).
Proof. vm_refl. Qed.

Definition W_20244 : bv 32 := 0xff010113.
Lemma F_20244 : fetch_word Ubsan.M.loaded_segments (0x20244 : word) = Some W_20244.
Proof. vm_refl. Qed.
Lemma D_20244 : decode_any W_20244 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_20248 : bv 32 := 0x00113423.
Lemma F_20248 : fetch_word Ubsan.M.loaded_segments (0x20248 : word) = Some W_20248.
Proof. vm_refl. Qed.
Lemma D_20248 : decode_any W_20248 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2024c : bv 32 := 0x00813023.
Lemma F_2024c : fetch_word Ubsan.M.loaded_segments (0x2024c : word) = Some W_2024c.
Proof. vm_refl. Qed.
Lemma D_2024c : decode_any W_2024c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20250 : bv 32 := 0x01010413.
Lemma F_20250 : fetch_word Ubsan.M.loaded_segments (0x20250 : word) = Some W_20250.
Proof. vm_refl. Qed.
Lemma D_20250 : decode_any W_20250 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20254 : bv 32 := 0x00040517.
Lemma F_20254 : fetch_word Ubsan.M.loaded_segments (0x20254 : word) = Some W_20254.
Proof. vm_refl. Qed.
Lemma D_20254 : decode_any W_20254 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20258 : bv 32 := 0x11c50513.
Lemma F_20258 : fetch_word Ubsan.M.loaded_segments (0x20258 : word) = Some W_20258.
Proof. vm_refl. Qed.
Lemma D_20258 : decode_any W_20258 = Some (OpImm ALU_ADD 10 10 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_2025c : bv 32 := 0x00054503.
Lemma F_2025c : fetch_word Ubsan.M.loaded_segments (0x2025c : word) = Some W_2025c.
Proof. vm_refl. Qed.
Lemma D_2025c : decode_any W_2025c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20260 : bv 32 := 0x00157513.
Lemma F_20260 : fetch_word Ubsan.M.loaded_segments (0x20260 : word) = Some W_20260.
Proof. vm_refl. Qed.
Lemma D_20260 : decode_any W_20260 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20264 : bv 32 := 0x00050663.
Lemma F_20264 : fetch_word Ubsan.M.loaded_segments (0x20264 : word) = Some W_20264.
Proof. vm_refl. Qed.
Lemma D_20264 : decode_any W_20264 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20270 : bv 32 := 0x00040517.
Lemma F_20270 : fetch_word Ubsan.M.loaded_segments (0x20270 : word) = Some W_20270.
Proof. vm_refl. Qed.
Lemma D_20270 : decode_any W_20270 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20274 : bv 32 := 0x10050593.
Lemma F_20274 : fetch_word Ubsan.M.loaded_segments (0x20274 : word) = Some W_20274.
Proof. vm_refl. Qed.
Lemma D_20274 : decode_any W_20274 = Some (OpImm ALU_ADD 11 10 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_20278 : bv 32 := 0x00100513.
Lemma F_20278 : fetch_word Ubsan.M.loaded_segments (0x20278 : word) = Some W_20278.
Proof. vm_refl. Qed.
Lemma D_20278 : decode_any W_20278 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2027c : bv 32 := 0x00a58023.
Lemma F_2027c : fetch_word Ubsan.M.loaded_segments (0x2027c : word) = Some W_2027c.
Proof. vm_refl. Qed.
Lemma D_2027c : decode_any W_2027c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20280 : bv 32 := 0x0003f517.
Lemma F_20280 : fetch_word Ubsan.M.loaded_segments (0x20280 : word) = Some W_20280.
Proof. vm_refl. Qed.
Lemma D_20280 : decode_any W_20280 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_20284 : bv 32 := 0xd3853503.
Lemma F_20284 : fetch_word Ubsan.M.loaded_segments (0x20284 : word) = Some W_20284.
Proof. vm_refl. Qed.
Lemma D_20284 : decode_any W_20284 = Some (Load SZ8 true 10 10 3384, 4%Z).
Proof. vm_refl. Qed.

Definition W_20288 : bv 32 := 0x02050063.
Lemma F_20288 : fetch_word Ubsan.M.loaded_segments (0x20288 : word) = Some W_20288.
Proof. vm_refl. Qed.
Lemma D_20288 : decode_any W_20288 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_202a8 : bv 32 := 0x00813083.
Lemma F_202a8 : fetch_word Ubsan.M.loaded_segments (0x202a8 : word) = Some W_202a8.
Proof. vm_refl. Qed.
Lemma D_202a8 : decode_any W_202a8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_202ac : bv 32 := 0x00013403.
Lemma F_202ac : fetch_word Ubsan.M.loaded_segments (0x202ac : word) = Some W_202ac.
Proof. vm_refl. Qed.
Lemma D_202ac : decode_any W_202ac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202b0 : bv 32 := 0x01010113.
Lemma F_202b0 : fetch_word Ubsan.M.loaded_segments (0x202b0 : word) = Some W_202b0.
Proof. vm_refl. Qed.
Lemma D_202b0 : decode_any W_202b0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_202b4 : bv 32 := 0x00008067.
Lemma F_202b4 : fetch_word Ubsan.M.loaded_segments (0x202b4 : word) = Some W_202b4.
Proof. vm_refl. Qed.
Lemma D_202b4 : decode_any W_202b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202b8 : bv 32 := 0xff010113.
Lemma F_202b8 : fetch_word Ubsan.M.loaded_segments (0x202b8 : word) = Some W_202b8.
Proof. vm_refl. Qed.
Lemma D_202b8 : decode_any W_202b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_202bc : bv 32 := 0x00113423.
Lemma F_202bc : fetch_word Ubsan.M.loaded_segments (0x202bc : word) = Some W_202bc.
Proof. vm_refl. Qed.
Lemma D_202bc : decode_any W_202bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c0 : bv 32 := 0x00813023.
Lemma F_202c0 : fetch_word Ubsan.M.loaded_segments (0x202c0 : word) = Some W_202c0.
Proof. vm_refl. Qed.
Lemma D_202c0 : decode_any W_202c0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c4 : bv 32 := 0x01010413.
Lemma F_202c4 : fetch_word Ubsan.M.loaded_segments (0x202c4 : word) = Some W_202c4.
Proof. vm_refl. Qed.
Lemma D_202c4 : decode_any W_202c4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c8 : bv 32 := 0x00040517.
Lemma F_202c8 : fetch_word Ubsan.M.loaded_segments (0x202c8 : word) = Some W_202c8.
Proof. vm_refl. Qed.
Lemma D_202c8 : decode_any W_202c8 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_202cc : bv 32 := 0x0f050513.
Lemma F_202cc : fetch_word Ubsan.M.loaded_segments (0x202cc : word) = Some W_202cc.
Proof. vm_refl. Qed.
Lemma D_202cc : decode_any W_202cc = Some (OpImm ALU_ADD 10 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d0 : bv 32 := 0x00054503.
Lemma F_202d0 : fetch_word Ubsan.M.loaded_segments (0x202d0 : word) = Some W_202d0.
Proof. vm_refl. Qed.
Lemma D_202d0 : decode_any W_202d0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d4 : bv 32 := 0x00157513.
Lemma F_202d4 : fetch_word Ubsan.M.loaded_segments (0x202d4 : word) = Some W_202d4.
Proof. vm_refl. Qed.
Lemma D_202d4 : decode_any W_202d4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d8 : bv 32 := 0x00050663.
Lemma F_202d8 : fetch_word Ubsan.M.loaded_segments (0x202d8 : word) = Some W_202d8.
Proof. vm_refl. Qed.
Lemma D_202d8 : decode_any W_202d8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_202e4 : bv 32 := 0x00040517.
Lemma F_202e4 : fetch_word Ubsan.M.loaded_segments (0x202e4 : word) = Some W_202e4.
Proof. vm_refl. Qed.
Lemma D_202e4 : decode_any W_202e4 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_202e8 : bv 32 := 0x0d450593.
Lemma F_202e8 : fetch_word Ubsan.M.loaded_segments (0x202e8 : word) = Some W_202e8.
Proof. vm_refl. Qed.
Lemma D_202e8 : decode_any W_202e8 = Some (OpImm ALU_ADD 11 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_202ec : bv 32 := 0x00100513.
Lemma F_202ec : fetch_word Ubsan.M.loaded_segments (0x202ec : word) = Some W_202ec.
Proof. vm_refl. Qed.
Lemma D_202ec : decode_any W_202ec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f0 : bv 32 := 0x00a58023.
Lemma F_202f0 : fetch_word Ubsan.M.loaded_segments (0x202f0 : word) = Some W_202f0.
Proof. vm_refl. Qed.
Lemma D_202f0 : decode_any W_202f0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f4 : bv 32 := 0x0003f517.
Lemma F_202f4 : fetch_word Ubsan.M.loaded_segments (0x202f4 : word) = Some W_202f4.
Proof. vm_refl. Qed.
Lemma D_202f4 : decode_any W_202f4 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f8 : bv 32 := 0xccc53503.
Lemma F_202f8 : fetch_word Ubsan.M.loaded_segments (0x202f8 : word) = Some W_202f8.
Proof. vm_refl. Qed.
Lemma D_202f8 : decode_any W_202f8 = Some (Load SZ8 true 10 10 3276, 4%Z).
Proof. vm_refl. Qed.

Definition W_202fc : bv 32 := 0x00050e63.
Lemma F_202fc : fetch_word Ubsan.M.loaded_segments (0x202fc : word) = Some W_202fc.
Proof. vm_refl. Qed.
Lemma D_202fc : decode_any W_202fc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_20318 : bv 32 := 0x0003f517.
Lemma F_20318 : fetch_word Ubsan.M.loaded_segments (0x20318 : word) = Some W_20318.
Proof. vm_refl. Qed.
Lemma D_20318 : decode_any W_20318 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_2031c : bv 32 := 0xcb053503.
Lemma F_2031c : fetch_word Ubsan.M.loaded_segments (0x2031c : word) = Some W_2031c.
Proof. vm_refl. Qed.
Lemma D_2031c : decode_any W_2031c = Some (Load SZ8 true 10 10 3248, 4%Z).
Proof. vm_refl. Qed.

Definition W_20320 : bv 32 := 0x00050c63.
Lemma F_20320 : fetch_word Ubsan.M.loaded_segments (0x20320 : word) = Some W_20320.
Proof. vm_refl. Qed.
Lemma D_20320 : decode_any W_20320 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_20338 : bv 32 := 0x00813083.
Lemma F_20338 : fetch_word Ubsan.M.loaded_segments (0x20338 : word) = Some W_20338.
Proof. vm_refl. Qed.
Lemma D_20338 : decode_any W_20338 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2033c : bv 32 := 0x00013403.
Lemma F_2033c : fetch_word Ubsan.M.loaded_segments (0x2033c : word) = Some W_2033c.
Proof. vm_refl. Qed.
Lemma D_2033c : decode_any W_2033c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20340 : bv 32 := 0x01010113.
Lemma F_20340 : fetch_word Ubsan.M.loaded_segments (0x20340 : word) = Some W_20340.
Proof. vm_refl. Qed.
Lemma D_20340 : decode_any W_20340 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20344 : bv 32 := 0x00008067.
Lemma F_20344 : fetch_word Ubsan.M.loaded_segments (0x20344 : word) = Some W_20344.
Proof. vm_refl. Qed.
Lemma D_20344 : decode_any W_20344 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2039c : bv 32 := 0x24050a63.
Lemma F_2039c : fetch_word Ubsan.M.loaded_segments (0x2039c : word) = Some W_2039c.
Proof. vm_refl. Qed.
Lemma D_2039c : decode_any W_2039c = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_203dc : bv 32 := 0x01a9d513.
Lemma F_203dc : fetch_word Ubsan.M.loaded_segments (0x203dc : word) = Some W_203dc.
Proof. vm_refl. Qed.
Lemma D_203dc : decode_any W_203dc = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_203e0 : bv 32 := 0x1a051863.
Lemma F_203e0 : fetch_word Ubsan.M.loaded_segments (0x203e0 : word) = Some W_203e0.
Proof. vm_refl. Qed.
Lemma D_203e0 : decode_any W_203e0 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_203e4 : bv 32 := 0x00199a93.
Lemma F_203e4 : fetch_word Ubsan.M.loaded_segments (0x203e4 : word) = Some W_203e4.
Proof. vm_refl. Qed.
Lemma D_203e4 : decode_any W_203e4 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_203e8 : bv 32 := 0x000a8513.
Lemma F_203e8 : fetch_word Ubsan.M.loaded_segments (0x203e8 : word) = Some W_203e8.
Proof. vm_refl. Qed.
Lemma D_203e8 : decode_any W_203e8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_203ec : bv 32 := 0x0542c0ef.
Lemma F_203ec : fetch_word Ubsan.M.loaded_segments (0x203ec : word) = Some W_203ec.
Proof. vm_refl. Qed.
Lemma D_203ec : decode_any W_203ec = Some (Jal 1 180308, 4%Z).
Proof. vm_refl. Qed.

Definition W_203f0 : bv 32 := 0x1c050063.
Lemma F_203f0 : fetch_word Ubsan.M.loaded_segments (0x203f0 : word) = Some W_203f0.
Proof. vm_refl. Qed.
Lemma D_203f0 : decode_any W_203f0 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_203f4 : bv 32 := 0x00050493.
Lemma F_203f4 : fetch_word Ubsan.M.loaded_segments (0x203f4 : word) = Some W_203f4.
Proof. vm_refl. Qed.
Lemma D_203f4 : decode_any W_203f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_203f8 : bv 32 := 0x00098a63.
Lemma F_203f8 : fetch_word Ubsan.M.loaded_segments (0x203f8 : word) = Some W_203f8.
Proof. vm_refl. Qed.
Lemma D_203f8 : decode_any W_203f8 = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_203fc : bv 32 := 0x00048513.
Lemma F_203fc : fetch_word Ubsan.M.loaded_segments (0x203fc : word) = Some W_203fc.
Proof. vm_refl. Qed.
Lemma D_203fc : decode_any W_203fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20400 : bv 32 := 0x000b8593.
Lemma F_20400 : fetch_word Ubsan.M.loaded_segments (0x20400 : word) = Some W_20400.
Proof. vm_refl. Qed.
Lemma D_20400 : decode_any W_20400 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20404 : bv 32 := 0x00098613.
Lemma F_20404 : fetch_word Ubsan.M.loaded_segments (0x20404 : word) = Some W_20404.
Proof. vm_refl. Qed.
Lemma D_20404 : decode_any W_20404 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20408 : bv 32 := 0x018390ef.
Lemma F_20408 : fetch_word Ubsan.M.loaded_segments (0x20408 : word) = Some W_20408.
Proof. vm_refl. Qed.
Lemma D_20408 : decode_any W_20408 = Some (Jal 1 233496, 4%Z).
Proof. vm_refl. Qed.

Definition W_2043c : bv 32 := 0x000a0513.
Lemma F_2043c : fetch_word Ubsan.M.loaded_segments (0x2043c : word) = Some W_2043c.
Proof. vm_refl. Qed.
Lemma D_2043c : decode_any W_2043c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20440 : bv 32 := 0x6d83a0ef.
Lemma F_20440 : fetch_word Ubsan.M.loaded_segments (0x20440 : word) = Some W_20440.
Proof. vm_refl. Qed.
Lemma D_20440 : decode_any W_20440 = Some (Jal 1 239320, 4%Z).
Proof. vm_refl. Qed.

Definition W_204bc : bv 32 := 0x000ac663.
Lemma F_204bc : fetch_word Ubsan.M.loaded_segments (0x204bc : word) = Some W_204bc.
Proof. vm_refl. Qed.
Lemma D_204bc : decode_any W_204bc = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_204c0 : bv 32 := 0x00050413.
Lemma F_204c0 : fetch_word Ubsan.M.loaded_segments (0x204c0 : word) = Some W_204c0.
Proof. vm_refl. Qed.
Lemma D_204c0 : decode_any W_204c0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_204c4 : bv 32 := 0x0780006f.
Lemma F_204c4 : fetch_word Ubsan.M.loaded_segments (0x204c4 : word) = Some W_204c4.
Proof. vm_refl. Qed.
Lemma D_204c4 : decode_any W_204c4 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_204c8 : bv 32 := 0x148000ef.
Lemma F_204c8 : fetch_word Ubsan.M.loaded_segments (0x204c8 : word) = Some W_204c8.
Proof. vm_refl. Qed.
Lemma D_204c8 : decode_any W_204c8 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_204cc : bv 32 := 0x0fb00593.
Lemma F_204cc : fetch_word Ubsan.M.loaded_segments (0x204cc : word) = Some W_204cc.
Proof. vm_refl. Qed.
Lemma D_204cc : decode_any W_204cc = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_204d0 : bv 32 := 0x00050413.
Lemma F_204d0 : fetch_word Ubsan.M.loaded_segments (0x204d0 : word) = Some W_204d0.
Proof. vm_refl. Qed.
Lemma D_204d0 : decode_any W_204d0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_204d4 : bv 32 := 0x06b56463.
Lemma F_204d4 : fetch_word Ubsan.M.loaded_segments (0x204d4 : word) = Some W_204d4.
Proof. vm_refl. Qed.
Lemma D_204d4 : decode_any W_204d4 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_20610 : bv 32 := 0x00000513.
Lemma F_20610 : fetch_word Ubsan.M.loaded_segments (0x20610 : word) = Some W_20610.
Proof. vm_refl. Qed.
Lemma D_20610 : decode_any W_20610 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20614 : bv 32 := 0x00008067.
Lemma F_20614 : fetch_word Ubsan.M.loaded_segments (0x20614 : word) = Some W_20614.
Proof. vm_refl. Qed.
Lemma D_20614 : decode_any W_20614 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20bbc : bv 32 := 0x00008067.
Lemma F_20bbc : fetch_word Ubsan.M.loaded_segments (0x20bbc : word) = Some W_20bbc.
Proof. vm_refl. Qed.
Lemma D_20bbc : decode_any W_20bbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20c88 : bv 32 := 0x00008067.
Lemma F_20c88 : fetch_word Ubsan.M.loaded_segments (0x20c88 : word) = Some W_20c88.
Proof. vm_refl. Qed.
Lemma D_20c88 : decode_any W_20c88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d2c : bv 32 := 0x00008067.
Lemma F_20d2c : fetch_word Ubsan.M.loaded_segments (0x20d2c : word) = Some W_20d2c.
Proof. vm_refl. Qed.
Lemma D_20d2c : decode_any W_20d2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20e94 : bv 32 := 0x00008067.
Lemma F_20e94 : fetch_word Ubsan.M.loaded_segments (0x20e94 : word) = Some W_20e94.
Proof. vm_refl. Qed.
Lemma D_20e94 : decode_any W_20e94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f00 : bv 32 := 0x00054683.
Lemma F_20f00 : fetch_word Ubsan.M.loaded_segments (0x20f00 : word) = Some W_20f00.
Proof. vm_refl. Qed.
Lemma D_20f00 : decode_any W_20f00 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f04 : bv 32 := 0x00b69863.
Lemma F_20f04 : fetch_word Ubsan.M.loaded_segments (0x20f04 : word) = Some W_20f04.
Proof. vm_refl. Qed.
Lemma D_20f04 : decode_any W_20f04 = Some (Branch BC_NE 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f08 : bv 32 := 0x18c50a63.
Lemma F_20f08 : fetch_word Ubsan.M.loaded_segments (0x20f08 : word) = Some W_20f08.
Proof. vm_refl. Qed.
Lemma D_20f08 : decode_any W_20f08 = Some (Branch BC_EQ 10 12 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f0c : bv 32 := 0x00150513.
Lemma F_20f0c : fetch_word Ubsan.M.loaded_segments (0x20f0c : word) = Some W_20f0c.
Proof. vm_refl. Qed.
Lemma D_20f0c : decode_any W_20f0c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f10 : bv 32 := 0xfe8568e3.
Lemma F_20f10 : fetch_word Ubsan.M.loaded_segments (0x20f10 : word) = Some W_20f10.
Proof. vm_refl. Qed.
Lemma D_20f10 : decode_any W_20f10 = Some (Branch BC_LTU 10 8 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_20f14 : bv 32 := 0x00850a63.
Lemma F_20f14 : fetch_word Ubsan.M.loaded_segments (0x20f14 : word) = Some W_20f14.
Proof. vm_refl. Qed.
Lemma D_20f14 : decode_any W_20f14 = Some (Branch BC_EQ 10 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_21080 : bv 32 := 0x00008067.
Lemma F_21080 : fetch_word Ubsan.M.loaded_segments (0x21080 : word) = Some W_21080.
Proof. vm_refl. Qed.
Lemma D_21080 : decode_any W_21080 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
