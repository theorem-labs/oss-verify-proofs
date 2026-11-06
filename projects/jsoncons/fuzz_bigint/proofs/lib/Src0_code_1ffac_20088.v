(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1ffac : bv 32 := 0xffff1197.
Lemma F_1ffac : fetch_word Plain.M.loaded_segments (0x1ffac : word) = Some W_1ffac.
Proof. vm_refl. Qed.
Lemma D_1ffac : decode_any W_1ffac = Some (Auipc 3 1048561, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffb0 : bv 32 := 0x85418193.
Lemma F_1ffb0 : fetch_word Plain.M.loaded_segments (0x1ffb0 : word) = Some W_1ffb0.
Proof. vm_refl. Qed.
Lemma D_1ffb0 : decode_any W_1ffb0 = Some (OpImm ALU_ADD 3 3 2132, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffb4 : bv 32 := 0x00010513.
Lemma F_1ffb4 : fetch_word Plain.M.loaded_segments (0x1ffb4 : word) = Some W_1ffb4.
Proof. vm_refl. Qed.
Lemma D_1ffb4 : decode_any W_1ffb4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffb8 : bv 32 := 0xfffe0597.
Lemma F_1ffb8 : fetch_word Plain.M.loaded_segments (0x1ffb8 : word) = Some W_1ffb8.
Proof. vm_refl. Qed.
Lemma D_1ffb8 : decode_any W_1ffb8 = Some (Auipc 11 1048544, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffbc : bv 32 := 0x04858593.
Lemma F_1ffbc : fetch_word Plain.M.loaded_segments (0x1ffbc : word) = Some W_1ffbc.
Proof. vm_refl. Qed.
Lemma D_1ffbc : decode_any W_1ffbc = Some (OpImm ALU_ADD 11 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffc0 : bv 32 := 0xff017113.
Lemma F_1ffc0 : fetch_word Plain.M.loaded_segments (0x1ffc0 : word) = Some W_1ffc0.
Proof. vm_refl. Qed.
Lemma D_1ffc0 : decode_any W_1ffc0 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffc4 : bv 32 := 0x0040006f.
Lemma F_1ffc4 : fetch_word Plain.M.loaded_segments (0x1ffc4 : word) = Some W_1ffc4.
Proof. vm_refl. Qed.
Lemma D_1ffc4 : decode_any W_1ffc4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffc8 : bv 32 := 0x00052583.
Lemma F_1ffc8 : fetch_word Plain.M.loaded_segments (0x1ffc8 : word) = Some W_1ffc8.
Proof. vm_refl. Qed.
Lemma D_1ffc8 : decode_any W_1ffc8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffcc : bv 32 := 0x0003e617.
Lemma F_1ffcc : fetch_word Plain.M.loaded_segments (0x1ffcc : word) = Some W_1ffcc.
Proof. vm_refl. Qed.
Lemma D_1ffcc : decode_any W_1ffcc = Some (Auipc 12 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffd0 : bv 32 := 0x0003e697.
Lemma F_1ffd0 : fetch_word Plain.M.loaded_segments (0x1ffd0 : word) = Some W_1ffd0.
Proof. vm_refl. Qed.
Lemma D_1ffd0 : decode_any W_1ffd0 = Some (Auipc 13 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffd4 : bv 32 := 0x0003e717.
Lemma F_1ffd4 : fetch_word Plain.M.loaded_segments (0x1ffd4 : word) = Some W_1ffd4.
Proof. vm_refl. Qed.
Lemma D_1ffd4 : decode_any W_1ffd4 = Some (Auipc 14 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffd8 : bv 32 := 0x4dc63783.
Lemma F_1ffd8 : fetch_word Plain.M.loaded_segments (0x1ffd8 : word) = Some W_1ffd8.
Proof. vm_refl. Qed.
Lemma D_1ffd8 : decode_any W_1ffd8 = Some (Load SZ8 true 15 12 1244, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffdc : bv 32 := 0x4e06b683.
Lemma F_1ffdc : fetch_word Plain.M.loaded_segments (0x1ffdc : word) = Some W_1ffdc.
Proof. vm_refl. Qed.
Lemma D_1ffdc : decode_any W_1ffdc = Some (Load SZ8 true 13 13 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffe0 : bv 32 := 0x4e473703.
Lemma F_1ffe0 : fetch_word Plain.M.loaded_segments (0x1ffe0 : word) = Some W_1ffe0.
Proof. vm_refl. Qed.
Lemma D_1ffe0 : decode_any W_1ffe0 = Some (Load SZ8 true 14 14 1252, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffe4 : bv 32 := 0x00850613.
Lemma F_1ffe4 : fetch_word Plain.M.loaded_segments (0x1ffe4 : word) = Some W_1ffe4.
Proof. vm_refl. Qed.
Lemma D_1ffe4 : decode_any W_1ffe4 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffe8 : bv 32 := 0x00078513.
Lemma F_1ffe8 : fetch_word Plain.M.loaded_segments (0x1ffe8 : word) = Some W_1ffe8.
Proof. vm_refl. Qed.
Lemma D_1ffe8 : decode_any W_1ffe8 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ffec : bv 32 := 0x00000793.
Lemma F_1ffec : fetch_word Plain.M.loaded_segments (0x1ffec : word) = Some W_1ffec.
Proof. vm_refl. Qed.
Lemma D_1ffec : decode_any W_1ffec = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fff0 : bv 32 := 0x6452a06f.
Lemma F_1fff0 : fetch_word Plain.M.loaded_segments (0x1fff0 : word) = Some W_1fff0.
Proof. vm_refl. Qed.
Lemma D_1fff0 : decode_any W_1fff0 = Some (Jal 0 175684, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fff4 : bv 32 := 0xff010113.
Lemma F_1fff4 : fetch_word Plain.M.loaded_segments (0x1fff4 : word) = Some W_1fff4.
Proof. vm_refl. Qed.
Lemma D_1fff4 : decode_any W_1fff4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fff8 : bv 32 := 0x00113423.
Lemma F_1fff8 : fetch_word Plain.M.loaded_segments (0x1fff8 : word) = Some W_1fff8.
Proof. vm_refl. Qed.
Lemma D_1fff8 : decode_any W_1fff8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fffc : bv 32 := 0x00813023.
Lemma F_1fffc : fetch_word Plain.M.loaded_segments (0x1fffc : word) = Some W_1fffc.
Proof. vm_refl. Qed.
Lemma D_1fffc : decode_any W_1fffc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20000 : bv 32 := 0x01010413.
Lemma F_20000 : fetch_word Plain.M.loaded_segments (0x20000 : word) = Some W_20000.
Proof. vm_refl. Qed.
Lemma D_20000 : decode_any W_20000 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20004 : bv 32 := 0x00040517.
Lemma F_20004 : fetch_word Plain.M.loaded_segments (0x20004 : word) = Some W_20004.
Proof. vm_refl. Qed.
Lemma D_20004 : decode_any W_20004 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20008 : bv 32 := 0x86c50513.
Lemma F_20008 : fetch_word Plain.M.loaded_segments (0x20008 : word) = Some W_20008.
Proof. vm_refl. Qed.
Lemma D_20008 : decode_any W_20008 = Some (OpImm ALU_ADD 10 10 2156, 4%Z).
Proof. vm_refl. Qed.

Definition W_2000c : bv 32 := 0x00054503.
Lemma F_2000c : fetch_word Plain.M.loaded_segments (0x2000c : word) = Some W_2000c.
Proof. vm_refl. Qed.
Lemma D_2000c : decode_any W_2000c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20010 : bv 32 := 0x00157513.
Lemma F_20010 : fetch_word Plain.M.loaded_segments (0x20010 : word) = Some W_20010.
Proof. vm_refl. Qed.
Lemma D_20010 : decode_any W_20010 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20014 : bv 32 := 0x00050663.
Lemma F_20014 : fetch_word Plain.M.loaded_segments (0x20014 : word) = Some W_20014.
Proof. vm_refl. Qed.
Lemma D_20014 : decode_any W_20014 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20020 : bv 32 := 0x00040517.
Lemma F_20020 : fetch_word Plain.M.loaded_segments (0x20020 : word) = Some W_20020.
Proof. vm_refl. Qed.
Lemma D_20020 : decode_any W_20020 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20024 : bv 32 := 0x85050593.
Lemma F_20024 : fetch_word Plain.M.loaded_segments (0x20024 : word) = Some W_20024.
Proof. vm_refl. Qed.
Lemma D_20024 : decode_any W_20024 = Some (OpImm ALU_ADD 11 10 2128, 4%Z).
Proof. vm_refl. Qed.

Definition W_20028 : bv 32 := 0x00100513.
Lemma F_20028 : fetch_word Plain.M.loaded_segments (0x20028 : word) = Some W_20028.
Proof. vm_refl. Qed.
Lemma D_20028 : decode_any W_20028 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2002c : bv 32 := 0x00a58023.
Lemma F_2002c : fetch_word Plain.M.loaded_segments (0x2002c : word) = Some W_2002c.
Proof. vm_refl. Qed.
Lemma D_2002c : decode_any W_2002c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20030 : bv 32 := 0x0003e517.
Lemma F_20030 : fetch_word Plain.M.loaded_segments (0x20030 : word) = Some W_20030.
Proof. vm_refl. Qed.
Lemma D_20030 : decode_any W_20030 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_20034 : bv 32 := 0x49053503.
Lemma F_20034 : fetch_word Plain.M.loaded_segments (0x20034 : word) = Some W_20034.
Proof. vm_refl. Qed.
Lemma D_20034 : decode_any W_20034 = Some (Load SZ8 true 10 10 1168, 4%Z).
Proof. vm_refl. Qed.

Definition W_20038 : bv 32 := 0x02050063.
Lemma F_20038 : fetch_word Plain.M.loaded_segments (0x20038 : word) = Some W_20038.
Proof. vm_refl. Qed.
Lemma D_20038 : decode_any W_20038 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_20058 : bv 32 := 0x00813083.
Lemma F_20058 : fetch_word Plain.M.loaded_segments (0x20058 : word) = Some W_20058.
Proof. vm_refl. Qed.
Lemma D_20058 : decode_any W_20058 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2005c : bv 32 := 0x00013403.
Lemma F_2005c : fetch_word Plain.M.loaded_segments (0x2005c : word) = Some W_2005c.
Proof. vm_refl. Qed.
Lemma D_2005c : decode_any W_2005c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20060 : bv 32 := 0x01010113.
Lemma F_20060 : fetch_word Plain.M.loaded_segments (0x20060 : word) = Some W_20060.
Proof. vm_refl. Qed.
Lemma D_20060 : decode_any W_20060 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20064 : bv 32 := 0x00008067.
Lemma F_20064 : fetch_word Plain.M.loaded_segments (0x20064 : word) = Some W_20064.
Proof. vm_refl. Qed.
Lemma D_20064 : decode_any W_20064 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20068 : bv 32 := 0xff010113.
Lemma F_20068 : fetch_word Plain.M.loaded_segments (0x20068 : word) = Some W_20068.
Proof. vm_refl. Qed.
Lemma D_20068 : decode_any W_20068 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2006c : bv 32 := 0x00113423.
Lemma F_2006c : fetch_word Plain.M.loaded_segments (0x2006c : word) = Some W_2006c.
Proof. vm_refl. Qed.
Lemma D_2006c : decode_any W_2006c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20070 : bv 32 := 0x00813023.
Lemma F_20070 : fetch_word Plain.M.loaded_segments (0x20070 : word) = Some W_20070.
Proof. vm_refl. Qed.
Lemma D_20070 : decode_any W_20070 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20074 : bv 32 := 0x01010413.
Lemma F_20074 : fetch_word Plain.M.loaded_segments (0x20074 : word) = Some W_20074.
Proof. vm_refl. Qed.
Lemma D_20074 : decode_any W_20074 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20078 : bv 32 := 0x00040517.
Lemma F_20078 : fetch_word Plain.M.loaded_segments (0x20078 : word) = Some W_20078.
Proof. vm_refl. Qed.
Lemma D_20078 : decode_any W_20078 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_2007c : bv 32 := 0x84050513.
Lemma F_2007c : fetch_word Plain.M.loaded_segments (0x2007c : word) = Some W_2007c.
Proof. vm_refl. Qed.
Lemma D_2007c : decode_any W_2007c = Some (OpImm ALU_ADD 10 10 2112, 4%Z).
Proof. vm_refl. Qed.

Definition W_20080 : bv 32 := 0x00054503.
Lemma F_20080 : fetch_word Plain.M.loaded_segments (0x20080 : word) = Some W_20080.
Proof. vm_refl. Qed.
Lemma D_20080 : decode_any W_20080 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20084 : bv 32 := 0x00157513.
Lemma F_20084 : fetch_word Plain.M.loaded_segments (0x20084 : word) = Some W_20084.
Proof. vm_refl. Qed.
Lemma D_20084 : decode_any W_20084 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.
