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
Definition W_153344 : bv 32 := 0x00757593.
Lemma F_153344 : fetch_word Asan.M.loaded_segments (0x153388 : word) = Some W_153344.
Proof. vm_refl. Qed.
Lemma D_153344 : decode_any W_153344 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153348 : bv 32 := 0x00050613.
Lemma F_153348 : fetch_word Asan.M.loaded_segments (0x15338c : word) = Some W_153348.
Proof. vm_refl. Qed.
Lemma D_153348 : decode_any W_153348 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15334c : bv 32 := 0x02058a63.
Lemma F_15334c : fetch_word Asan.M.loaded_segments (0x153390 : word) = Some W_15334c.
Proof. vm_refl. Qed.
Lemma D_15334c : decode_any W_15334c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153350 : bv 32 := 0x00054583.
Lemma F_153350 : fetch_word Asan.M.loaded_segments (0x153394 : word) = Some W_153350.
Proof. vm_refl. Qed.
Lemma D_153350 : decode_any W_153350 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153354 : bv 32 := 0x06058c63.
Lemma F_153354 : fetch_word Asan.M.loaded_segments (0x153398 : word) = Some W_153354.
Proof. vm_refl. Qed.
Lemma D_153354 : decode_any W_153354 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153358 : bv 32 := 0x00150613.
Lemma F_153358 : fetch_word Asan.M.loaded_segments (0x15339c : word) = Some W_153358.
Proof. vm_refl. Qed.
Lemma D_153358 : decode_any W_153358 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15335c : bv 32 := 0x00050593.
Lemma F_15335c : fetch_word Asan.M.loaded_segments (0x1533a0 : word) = Some W_15335c.
Proof. vm_refl. Qed.
Lemma D_15335c : decode_any W_15335c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153360 : bv 32 := 0x00158693.
Lemma F_153360 : fetch_word Asan.M.loaded_segments (0x1533a4 : word) = Some W_153360.
Proof. vm_refl. Qed.
Lemma D_153360 : decode_any W_153360 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153364 : bv 32 := 0x0076f693.
Lemma F_153364 : fetch_word Asan.M.loaded_segments (0x1533a8 : word) = Some W_153364.
Proof. vm_refl. Qed.
Lemma D_153364 : decode_any W_153364 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153368 : bv 32 := 0x00068c63.
Lemma F_153368 : fetch_word Asan.M.loaded_segments (0x1533ac : word) = Some W_153368.
Proof. vm_refl. Qed.
Lemma D_153368 : decode_any W_153368 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15336c : bv 32 := 0x00064683.
Lemma F_15336c : fetch_word Asan.M.loaded_segments (0x1533b0 : word) = Some W_15336c.
Proof. vm_refl. Qed.
Lemma D_15336c : decode_any W_15336c = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153370 : bv 32 := 0x00160613.
Lemma F_153370 : fetch_word Asan.M.loaded_segments (0x1533b4 : word) = Some W_153370.
Proof. vm_refl. Qed.
Lemma D_153370 : decode_any W_153370 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153374 : bv 32 := 0x00158593.
Lemma F_153374 : fetch_word Asan.M.loaded_segments (0x1533b8 : word) = Some W_153374.
Proof. vm_refl. Qed.
Lemma D_153374 : decode_any W_153374 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153378 : bv 32 := 0xfe0694e3.
Lemma F_153378 : fetch_word Asan.M.loaded_segments (0x1533bc : word) = Some W_153378.
Proof. vm_refl. Qed.
Lemma D_153378 : decode_any W_153378 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15337c : bv 32 := 0x0480006f.
Lemma F_15337c : fetch_word Asan.M.loaded_segments (0x1533c0 : word) = Some W_15337c.
Proof. vm_refl. Qed.
Lemma D_15337c : decode_any W_15337c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153380 : bv 32 := 0xffebd597.
Lemma F_153380 : fetch_word Asan.M.loaded_segments (0x1533c4 : word) = Some W_153380.
Proof. vm_refl. Qed.
Lemma D_153380 : decode_any W_153380 = Some (Auipc 11 1048253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153384 : bv 32 := 0xffebd717.
Lemma F_153384 : fetch_word Asan.M.loaded_segments (0x1533c8 : word) = Some W_153384.
Proof. vm_refl. Qed.
Lemma D_153384 : decode_any W_153384 = Some (Auipc 14 1048253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153388 : bv 32 := 0x0145b683.
Lemma F_153388 : fetch_word Asan.M.loaded_segments (0x1533cc : word) = Some W_153388.
Proof. vm_refl. Qed.
Lemma D_153388 : decode_any W_153388 = Some (Load SZ8 true 13 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15338c : bv 32 := 0xff873703.
Lemma F_15338c : fetch_word Asan.M.loaded_segments (0x1533d0 : word) = Some W_15338c.
Proof. vm_refl. Qed.
Lemma D_15338c : decode_any W_15338c = Some (Load SZ8 true 14 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153390 : bv 32 := 0xff760593.
Lemma F_153390 : fetch_word Asan.M.loaded_segments (0x1533d4 : word) = Some W_153390.
Proof. vm_refl. Qed.
Lemma D_153390 : decode_any W_153390 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153394 : bv 32 := 0xff860613.
Lemma F_153394 : fetch_word Asan.M.loaded_segments (0x1533d8 : word) = Some W_153394.
Proof. vm_refl. Qed.
Lemma D_153394 : decode_any W_153394 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153398 : bv 32 := 0x00863783.
Lemma F_153398 : fetch_word Asan.M.loaded_segments (0x1533dc : word) = Some W_153398.
Proof. vm_refl. Qed.
Lemma D_153398 : decode_any W_153398 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15339c : bv 32 := 0x00860613.
Lemma F_15339c : fetch_word Asan.M.loaded_segments (0x1533e0 : word) = Some W_15339c.
Proof. vm_refl. Qed.
Lemma D_15339c : decode_any W_15339c = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533a0 : bv 32 := 0x40f68833.
Lemma F_1533a0 : fetch_word Asan.M.loaded_segments (0x1533e4 : word) = Some W_1533a0.
Proof. vm_refl. Qed.
Lemma D_1533a0 : decode_any W_1533a0 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533a4 : bv 32 := 0x00f867b3.
Lemma F_1533a4 : fetch_word Asan.M.loaded_segments (0x1533e8 : word) = Some W_1533a4.
Proof. vm_refl. Qed.
Lemma D_1533a4 : decode_any W_1533a4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533a8 : bv 32 := 0x00e7f7b3.
Lemma F_1533a8 : fetch_word Asan.M.loaded_segments (0x1533ec : word) = Some W_1533a8.
Proof. vm_refl. Qed.
Lemma D_1533a8 : decode_any W_1533a8 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533ac : bv 32 := 0x00858593.
Lemma F_1533ac : fetch_word Asan.M.loaded_segments (0x1533f0 : word) = Some W_1533ac.
Proof. vm_refl. Qed.
Lemma D_1533ac : decode_any W_1533ac = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533b0 : bv 32 := 0xfee784e3.
Lemma F_1533b0 : fetch_word Asan.M.loaded_segments (0x1533f4 : word) = Some W_1533b0.
Proof. vm_refl. Qed.
Lemma D_1533b0 : decode_any W_1533b0 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533b4 : bv 32 := 0x00064683.
Lemma F_1533b4 : fetch_word Asan.M.loaded_segments (0x1533f8 : word) = Some W_1533b4.
Proof. vm_refl. Qed.
Lemma D_1533b4 : decode_any W_1533b4 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533b8 : bv 32 := 0x00160613.
Lemma F_1533b8 : fetch_word Asan.M.loaded_segments (0x1533fc : word) = Some W_1533b8.
Proof. vm_refl. Qed.
Lemma D_1533b8 : decode_any W_1533b8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533bc : bv 32 := 0x00158593.
Lemma F_1533bc : fetch_word Asan.M.loaded_segments (0x153400 : word) = Some W_1533bc.
Proof. vm_refl. Qed.
Lemma D_1533bc : decode_any W_1533bc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533c0 : bv 32 := 0xfe069ae3.
Lemma F_1533c0 : fetch_word Asan.M.loaded_segments (0x153404 : word) = Some W_1533c0.
Proof. vm_refl. Qed.
Lemma D_1533c0 : decode_any W_1533c0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533c4 : bv 32 := 0x40a58533.
Lemma F_1533c4 : fetch_word Asan.M.loaded_segments (0x153408 : word) = Some W_1533c4.
Proof. vm_refl. Qed.
Lemma D_1533c4 : decode_any W_1533c4 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533c8 : bv 32 := 0x00008067.
Lemma F_1533c8 : fetch_word Asan.M.loaded_segments (0x15340c : word) = Some W_1533c8.
Proof. vm_refl. Qed.
Lemma D_1533c8 : decode_any W_1533c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533cc : bv 32 := 0x40a50533.
Lemma F_1533cc : fetch_word Asan.M.loaded_segments (0x153410 : word) = Some W_1533cc.
Proof. vm_refl. Qed.
Lemma D_1533cc : decode_any W_1533cc = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533d0 : bv 32 := 0x00008067.
Lemma F_1533d0 : fetch_word Asan.M.loaded_segments (0x153414 : word) = Some W_1533d0.
Proof. vm_refl. Qed.
Lemma D_1533d0 : decode_any W_1533d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15371c : bv 32 := 0x0056b597.
Lemma F_15371c : fetch_word Asan.M.loaded_segments (0x153760 : word) = Some W_15371c.
Proof. vm_refl. Qed.
Lemma D_15371c : decode_any W_15371c = Some (Auipc 11 1387, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153720 : bv 32 := 0xb0358683.
Lemma F_153720 : fetch_word Asan.M.loaded_segments (0x153764 : word) = Some W_153720.
Proof. vm_refl. Qed.
Lemma D_153720 : decode_any W_153720 = Some (Load SZ1 true 13 11 2819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153724 : bv 32 := 0x1e068863.
Lemma F_153724 : fetch_word Asan.M.loaded_segments (0x153768 : word) = Some W_153724.
Proof. vm_refl. Qed.
Lemma D_153724 : decode_any W_153724 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153914 : bv 32 := 0x00008067.
Lemma F_153914 : fetch_word Asan.M.loaded_segments (0x153958 : word) = Some W_153914.
Proof. vm_refl. Qed.
Lemma D_153914 : decode_any W_153914 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539a4 : bv 32 := 0x00052583.
Lemma F_1539a4 : fetch_word Asan.M.loaded_segments (0x1539e8 : word) = Some W_1539a4.
Proof. vm_refl. Qed.
Lemma D_1539a4 : decode_any W_1539a4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539a8 : bv 32 := 0x0005c463.
Lemma F_1539a8 : fetch_word Asan.M.loaded_segments (0x1539ec : word) = Some W_1539a8.
Proof. vm_refl. Qed.
Lemma D_1539a8 : decode_any W_1539a8 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539ac : bv 32 := 0x00008067.
Lemma F_1539ac : fetch_word Asan.M.loaded_segments (0x1539f0 : word) = Some W_1539ac.
Proof. vm_refl. Qed.
Lemma D_1539ac : decode_any W_1539ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a18 : bv 32 := 0x00050893.
Lemma F_153a18 : fetch_word Asan.M.loaded_segments (0x153a5c : word) = Some W_153a18.
Proof. vm_refl. Qed.
Lemma D_153a18 : decode_any W_153a18 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a1c : bv 32 := 0x00058513.
Lemma F_153a1c : fetch_word Asan.M.loaded_segments (0x153a60 : word) = Some W_153a1c.
Proof. vm_refl. Qed.
Lemma D_153a1c : decode_any W_153a1c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a20 : bv 32 := 0x00060593.
Lemma F_153a20 : fetch_word Asan.M.loaded_segments (0x153a64 : word) = Some W_153a20.
Proof. vm_refl. Qed.
Lemma D_153a20 : decode_any W_153a20 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a24 : bv 32 := 0x00068613.
Lemma F_153a24 : fetch_word Asan.M.loaded_segments (0x153a68 : word) = Some W_153a24.
Proof. vm_refl. Qed.
Lemma D_153a24 : decode_any W_153a24 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a28 : bv 32 := 0x00070693.
Lemma F_153a28 : fetch_word Asan.M.loaded_segments (0x153a6c : word) = Some W_153a28.
Proof. vm_refl. Qed.
Lemma D_153a28 : decode_any W_153a28 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a2c : bv 32 := 0x00078713.
Lemma F_153a2c : fetch_word Asan.M.loaded_segments (0x153a70 : word) = Some W_153a2c.
Proof. vm_refl. Qed.
Lemma D_153a2c : decode_any W_153a2c = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a30 : bv 32 := 0x00080793.
Lemma F_153a30 : fetch_word Asan.M.loaded_segments (0x153a74 : word) = Some W_153a30.
Proof. vm_refl. Qed.
Lemma D_153a30 : decode_any W_153a30 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a38 : bv 32 := 0x00008067.
Lemma F_153a38 : fetch_word Asan.M.loaded_segments (0x153a7c : word) = Some W_153a38.
Proof. vm_refl. Qed.
Lemma D_153a38 : decode_any W_153a38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a3c : bv 32 := 0xfddff06f.
Lemma F_153a3c : fetch_word Asan.M.loaded_segments (0x153a80 : word) = Some W_153a3c.
Proof. vm_refl. Qed.
Lemma D_153a3c : decode_any W_153a3c = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a40 : bv 32 := 0x00020593.
Lemma F_153a40 : fetch_word Asan.M.loaded_segments (0x153a84 : word) = Some W_153a40.
Proof. vm_refl. Qed.
Lemma D_153a40 : decode_any W_153a40 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a44 : bv 32 := 0x00053603.
Lemma F_153a44 : fetch_word Asan.M.loaded_segments (0x153a88 : word) = Some W_153a44.
Proof. vm_refl. Qed.
Lemma D_153a44 : decode_any W_153a44 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a48 : bv 32 := 0xff85b583.
Lemma F_153a48 : fetch_word Asan.M.loaded_segments (0x153a8c : word) = Some W_153a48.
Proof. vm_refl. Qed.
Lemma D_153a48 : decode_any W_153a48 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a4c : bv 32 := 0x00853503.
Lemma F_153a4c : fetch_word Asan.M.loaded_segments (0x153a90 : word) = Some W_153a4c.
Proof. vm_refl. Qed.
Lemma D_153a4c : decode_any W_153a4c = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a50 : bv 32 := 0x00361613.
Lemma F_153a50 : fetch_word Asan.M.loaded_segments (0x153a94 : word) = Some W_153a50.
Proof. vm_refl. Qed.
Lemma D_153a50 : decode_any W_153a50 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a54 : bv 32 := 0x00c585b3.
Lemma F_153a54 : fetch_word Asan.M.loaded_segments (0x153a98 : word) = Some W_153a54.
Proof. vm_refl. Qed.
Lemma D_153a54 : decode_any W_153a54 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a58 : bv 32 := 0x0005b583.
Lemma F_153a58 : fetch_word Asan.M.loaded_segments (0x153a9c : word) = Some W_153a58.
Proof. vm_refl. Qed.
Lemma D_153a58 : decode_any W_153a58 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a5c : bv 32 := 0x00b50533.
Lemma F_153a5c : fetch_word Asan.M.loaded_segments (0x153aa0 : word) = Some W_153a5c.
Proof. vm_refl. Qed.
Lemma D_153a5c : decode_any W_153a5c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a60 : bv 32 := 0x00008067.
Lemma F_153a60 : fetch_word Asan.M.loaded_segments (0x153aa4 : word) = Some W_153a60.
Proof. vm_refl. Qed.
Lemma D_153a60 : decode_any W_153a60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

