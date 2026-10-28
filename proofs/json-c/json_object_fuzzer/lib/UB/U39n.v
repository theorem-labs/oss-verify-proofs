(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_52fa0 : bv 32 := 0xff010113.
Lemma F_52fa0 : fetch_word Ubsan.M.loaded_segments (0x54d7c : word) = Some W_52fa0.
Proof. vm_refl. Qed.
Lemma D_52fa0 : decode_any W_52fa0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fa4 : bv 32 := 0x00113423.
Lemma F_52fa4 : fetch_word Ubsan.M.loaded_segments (0x54d80 : word) = Some W_52fa4.
Proof. vm_refl. Qed.
Lemma D_52fa4 : decode_any W_52fa4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fa8 : bv 32 := 0x00813023.
Lemma F_52fa8 : fetch_word Ubsan.M.loaded_segments (0x54d84 : word) = Some W_52fa8.
Proof. vm_refl. Qed.
Lemma D_52fa8 : decode_any W_52fa8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fac : bv 32 := 0x388000ef.
Lemma F_52fac : fetch_word Ubsan.M.loaded_segments (0x54d88 : word) = Some W_52fac.
Proof. vm_refl. Qed.
Lemma D_52fac : decode_any W_52fac = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fb0 : bv 32 := 0x00053403.
Lemma F_52fb0 : fetch_word Ubsan.M.loaded_segments (0x54d8c : word) = Some W_52fb0.
Proof. vm_refl. Qed.
Lemma D_52fb0 : decode_any W_52fb0 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fb4 : bv 32 := 0x12041663.
Lemma F_52fb4 : fetch_word Ubsan.M.loaded_segments (0x54d90 : word) = Some W_52fb4.
Proof. vm_refl. Qed.
Lemma D_52fb4 : decode_any W_52fb4 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fb8 : bv 32 := 0x00043517.
Lemma F_52fb8 : fetch_word Ubsan.M.loaded_segments (0x54d94 : word) = Some W_52fb8.
Proof. vm_refl. Qed.
Lemma D_52fb8 : decode_any W_52fb8 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fbc : bv 32 := 0x59453403.
Lemma F_52fbc : fetch_word Ubsan.M.loaded_segments (0x54d98 : word) = Some W_52fbc.
Proof. vm_refl. Qed.
Lemma D_52fbc : decode_any W_52fbc = Some (Load SZ8 true 8 10 1428, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fc0 : bv 32 := 0x04040a63.
Lemma F_52fc0 : fetch_word Ubsan.M.loaded_segments (0x54d9c : word) = Some W_52fc0.
Proof. vm_refl. Qed.
Lemma D_52fc0 : decode_any W_52fc0 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_53014 : bv 32 := 0x00012517.
Lemma F_53014 : fetch_word Ubsan.M.loaded_segments (0x54df0 : word) = Some W_53014.
Proof. vm_refl. Qed.
Lemma D_53014 : decode_any W_53014 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_53018 : bv 32 := 0x12053403.
Lemma F_53018 : fetch_word Ubsan.M.loaded_segments (0x54df4 : word) = Some W_53018.
Proof. vm_refl. Qed.
Lemma D_53018 : decode_any W_53018 = Some (Load SZ8 true 8 10 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_5301c : bv 32 := 0x04040a63.
Lemma F_5301c : fetch_word Ubsan.M.loaded_segments (0x54df8 : word) = Some W_5301c.
Proof. vm_refl. Qed.
Lemma D_5301c : decode_any W_5301c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_53020 : bv 32 := 0x08c42503.
Lemma F_53020 : fetch_word Ubsan.M.loaded_segments (0x54dfc : word) = Some W_53020.
Proof. vm_refl. Qed.
Lemma D_53020 : decode_any W_53020 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_53024 : bv 32 := 0x00054663.
Lemma F_53024 : fetch_word Ubsan.M.loaded_segments (0x54e00 : word) = Some W_53024.
Proof. vm_refl. Qed.
Lemma D_53024 : decode_any W_53024 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53030 : bv 32 := 0x02843503.
Lemma F_53030 : fetch_word Ubsan.M.loaded_segments (0x54e0c : word) = Some W_53030.
Proof. vm_refl. Qed.
Lemma D_53030 : decode_any W_53030 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_53034 : bv 32 := 0x03843583.
Lemma F_53034 : fetch_word Ubsan.M.loaded_segments (0x54e10 : word) = Some W_53034.
Proof. vm_refl. Qed.
Lemma D_53034 : decode_any W_53034 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53038 : bv 32 := 0x00b50c63.
Lemma F_53038 : fetch_word Ubsan.M.loaded_segments (0x54e14 : word) = Some W_53038.
Proof. vm_refl. Qed.
Lemma D_53038 : decode_any W_53038 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5303c : bv 32 := 0x04843683.
Lemma F_5303c : fetch_word Ubsan.M.loaded_segments (0x54e18 : word) = Some W_5303c.
Proof. vm_refl. Qed.
Lemma D_5303c : decode_any W_5303c = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_53040 : bv 32 := 0x00040513.
Lemma F_53040 : fetch_word Ubsan.M.loaded_segments (0x54e1c : word) = Some W_53040.
Proof. vm_refl. Qed.
Lemma D_53040 : decode_any W_53040 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53044 : bv 32 := 0x00000593.
Lemma F_53044 : fetch_word Ubsan.M.loaded_segments (0x54e20 : word) = Some W_53044.
Proof. vm_refl. Qed.
Lemma D_53044 : decode_any W_53044 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53048 : bv 32 := 0x00000613.
Lemma F_53048 : fetch_word Ubsan.M.loaded_segments (0x54e24 : word) = Some W_53048.
Proof. vm_refl. Qed.
Lemma D_53048 : decode_any W_53048 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5304c : bv 32 := 0x000680e7.
Lemma F_5304c : fetch_word Ubsan.M.loaded_segments (0x54e28 : word) = Some W_5304c.
Proof. vm_refl. Qed.
Lemma D_5304c : decode_any W_5304c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53050 : bv 32 := 0x00843503.
Lemma F_53050 : fetch_word Ubsan.M.loaded_segments (0x54e2c : word) = Some W_53050.
Proof. vm_refl. Qed.
Lemma D_53050 : decode_any W_53050 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53054 : bv 32 := 0x01043583.
Lemma F_53054 : fetch_word Ubsan.M.loaded_segments (0x54e30 : word) = Some W_53054.
Proof. vm_refl. Qed.
Lemma D_53054 : decode_any W_53054 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53058 : bv 32 := 0x00b50c63.
Lemma F_53058 : fetch_word Ubsan.M.loaded_segments (0x54e34 : word) = Some W_53058.
Proof. vm_refl. Qed.
Lemma D_53058 : decode_any W_53058 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53070 : bv 32 := 0x00012517.
Lemma F_53070 : fetch_word Ubsan.M.loaded_segments (0x54e4c : word) = Some W_53070.
Proof. vm_refl. Qed.
Lemma D_53070 : decode_any W_53070 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_53074 : bv 32 := 0xfd453403.
Lemma F_53074 : fetch_word Ubsan.M.loaded_segments (0x54e50 : word) = Some W_53074.
Proof. vm_refl. Qed.
Lemma D_53074 : decode_any W_53074 = Some (Load SZ8 true 8 10 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_53078 : bv 32 := 0x0a040e63.
Lemma F_53078 : fetch_word Ubsan.M.loaded_segments (0x54e54 : word) = Some W_53078.
Proof. vm_refl. Qed.
Lemma D_53078 : decode_any W_53078 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_5307c : bv 32 := 0x08c42503.
Lemma F_5307c : fetch_word Ubsan.M.loaded_segments (0x54e58 : word) = Some W_5307c.
Proof. vm_refl. Qed.
Lemma D_5307c : decode_any W_5307c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_53080 : bv 32 := 0x00054663.
Lemma F_53080 : fetch_word Ubsan.M.loaded_segments (0x54e5c : word) = Some W_53080.
Proof. vm_refl. Qed.
Lemma D_53080 : decode_any W_53080 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5308c : bv 32 := 0x02843503.
Lemma F_5308c : fetch_word Ubsan.M.loaded_segments (0x54e68 : word) = Some W_5308c.
Proof. vm_refl. Qed.
Lemma D_5308c : decode_any W_5308c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_53090 : bv 32 := 0x03843583.
Lemma F_53090 : fetch_word Ubsan.M.loaded_segments (0x54e6c : word) = Some W_53090.
Proof. vm_refl. Qed.
Lemma D_53090 : decode_any W_53090 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53094 : bv 32 := 0x00b50c63.
Lemma F_53094 : fetch_word Ubsan.M.loaded_segments (0x54e70 : word) = Some W_53094.
Proof. vm_refl. Qed.
Lemma D_53094 : decode_any W_53094 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_530ac : bv 32 := 0x00843503.
Lemma F_530ac : fetch_word Ubsan.M.loaded_segments (0x54e88 : word) = Some W_530ac.
Proof. vm_refl. Qed.
Lemma D_530ac : decode_any W_530ac = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_530b0 : bv 32 := 0x01043583.
Lemma F_530b0 : fetch_word Ubsan.M.loaded_segments (0x54e8c : word) = Some W_530b0.
Proof. vm_refl. Qed.
Lemma D_530b0 : decode_any W_530b0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_530b4 : bv 32 := 0x08b50063.
Lemma F_530b4 : fetch_word Ubsan.M.loaded_segments (0x54e90 : word) = Some W_530b4.
Proof. vm_refl. Qed.
Lemma D_530b4 : decode_any W_530b4 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_53134 : bv 32 := 0x00813083.
Lemma F_53134 : fetch_word Ubsan.M.loaded_segments (0x54f10 : word) = Some W_53134.
Proof. vm_refl. Qed.
Lemma D_53134 : decode_any W_53134 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53138 : bv 32 := 0x00013403.
Lemma F_53138 : fetch_word Ubsan.M.loaded_segments (0x54f14 : word) = Some W_53138.
Proof. vm_refl. Qed.
Lemma D_53138 : decode_any W_53138 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5313c : bv 32 := 0x01010113.
Lemma F_5313c : fetch_word Ubsan.M.loaded_segments (0x54f18 : word) = Some W_5313c.
Proof. vm_refl. Qed.
Lemma D_5313c : decode_any W_5313c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53140 : bv 32 := 0x00008067.
Lemma F_53140 : fetch_word Ubsan.M.loaded_segments (0x54f1c : word) = Some W_53140.
Proof. vm_refl. Qed.
Lemma D_53140 : decode_any W_53140 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53334 : bv 32 := 0xff010113.
Lemma F_53334 : fetch_word Ubsan.M.loaded_segments (0x55110 : word) = Some W_53334.
Proof. vm_refl. Qed.
Lemma D_53334 : decode_any W_53334 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_53338 : bv 32 := 0x00113423.
Lemma F_53338 : fetch_word Ubsan.M.loaded_segments (0x55114 : word) = Some W_53338.
Proof. vm_refl. Qed.
Lemma D_53338 : decode_any W_53338 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5333c : bv 32 := 0x00813023.
Lemma F_5333c : fetch_word Ubsan.M.loaded_segments (0x55118 : word) = Some W_5333c.
Proof. vm_refl. Qed.
Lemma D_5333c : decode_any W_5333c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53340 : bv 32 := 0x00043517.
Lemma F_53340 : fetch_word Ubsan.M.loaded_segments (0x5511c : word) = Some W_53340.
Proof. vm_refl. Qed.
Lemma D_53340 : decode_any W_53340 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_53344 : bv 32 := 0x21450413.
Lemma F_53344 : fetch_word Ubsan.M.loaded_segments (0x55120 : word) = Some W_53344.
Proof. vm_refl. Qed.
Lemma D_53344 : decode_any W_53344 = Some (OpImm ALU_ADD 8 10 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_53348 : bv 32 := 0x00040513.
Lemma F_53348 : fetch_word Ubsan.M.loaded_segments (0x55124 : word) = Some W_53348.
Proof. vm_refl. Qed.
Lemma D_53348 : decode_any W_53348 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5334c : bv 32 := 0x4280b0ef.
Lemma F_5334c : fetch_word Ubsan.M.loaded_segments (0x55128 : word) = Some W_5334c.
Proof. vm_refl. Qed.
Lemma D_5334c : decode_any W_5334c = Some (Jal 1 46120, 4%Z).
Proof. vm_refl. Qed.

Definition W_53350 : bv 32 := 0x00840513.
Lemma F_53350 : fetch_word Ubsan.M.loaded_segments (0x5512c : word) = Some W_53350.
Proof. vm_refl. Qed.
Lemma D_53350 : decode_any W_53350 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53354 : bv 32 := 0x00813083.
Lemma F_53354 : fetch_word Ubsan.M.loaded_segments (0x55130 : word) = Some W_53354.
Proof. vm_refl. Qed.
Lemma D_53354 : decode_any W_53354 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53358 : bv 32 := 0x00013403.
Lemma F_53358 : fetch_word Ubsan.M.loaded_segments (0x55134 : word) = Some W_53358.
Proof. vm_refl. Qed.
Lemma D_53358 : decode_any W_53358 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5335c : bv 32 := 0x01010113.
Lemma F_5335c : fetch_word Ubsan.M.loaded_segments (0x55138 : word) = Some W_5335c.
Proof. vm_refl. Qed.
Lemma D_5335c : decode_any W_5335c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53360 : bv 32 := 0x00008067.
Lemma F_53360 : fetch_word Ubsan.M.loaded_segments (0x5513c : word) = Some W_53360.
Proof. vm_refl. Qed.
Lemma D_53360 : decode_any W_53360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53400 : bv 32 := 0xf9010113.
Lemma F_53400 : fetch_word Ubsan.M.loaded_segments (0x551dc : word) = Some W_53400.
Proof. vm_refl. Qed.
Lemma D_53400 : decode_any W_53400 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_53404 : bv 32 := 0x06113423.
Lemma F_53404 : fetch_word Ubsan.M.loaded_segments (0x551e0 : word) = Some W_53404.
Proof. vm_refl. Qed.
Lemma D_53404 : decode_any W_53404 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_53408 : bv 32 := 0x06813023.
Lemma F_53408 : fetch_word Ubsan.M.loaded_segments (0x551e4 : word) = Some W_53408.
Proof. vm_refl. Qed.
Lemma D_53408 : decode_any W_53408 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5340c : bv 32 := 0x04913c23.
Lemma F_5340c : fetch_word Ubsan.M.loaded_segments (0x551e8 : word) = Some W_5340c.
Proof. vm_refl. Qed.
Lemma D_5340c : decode_any W_5340c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_53410 : bv 32 := 0x05213823.
Lemma F_53410 : fetch_word Ubsan.M.loaded_segments (0x551ec : word) = Some W_53410.
Proof. vm_refl. Qed.
Lemma D_53410 : decode_any W_53410 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_53414 : bv 32 := 0x05313423.
Lemma F_53414 : fetch_word Ubsan.M.loaded_segments (0x551f0 : word) = Some W_53414.
Proof. vm_refl. Qed.
Lemma D_53414 : decode_any W_53414 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_53418 : bv 32 := 0x05413023.
Lemma F_53418 : fetch_word Ubsan.M.loaded_segments (0x551f4 : word) = Some W_53418.
Proof. vm_refl. Qed.
Lemma D_53418 : decode_any W_53418 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5341c : bv 32 := 0x03513c23.
Lemma F_5341c : fetch_word Ubsan.M.loaded_segments (0x551f8 : word) = Some W_5341c.
Proof. vm_refl. Qed.
Lemma D_5341c : decode_any W_5341c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53420 : bv 32 := 0x03613823.
Lemma F_53420 : fetch_word Ubsan.M.loaded_segments (0x551fc : word) = Some W_53420.
Proof. vm_refl. Qed.
Lemma D_53420 : decode_any W_53420 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_53424 : bv 32 := 0x00060413.
Lemma F_53424 : fetch_word Ubsan.M.loaded_segments (0x55200 : word) = Some W_53424.
Proof. vm_refl. Qed.
Lemma D_53424 : decode_any W_53424 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53428 : bv 32 := 0x00050493.
Lemma F_53428 : fetch_word Ubsan.M.loaded_segments (0x55204 : word) = Some W_53428.
Proof. vm_refl. Qed.
Lemma D_53428 : decode_any W_53428 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5342c : bv 32 := 0x00010517.
Lemma F_5342c : fetch_word Ubsan.M.loaded_segments (0x55208 : word) = Some W_5342c.
Proof. vm_refl. Qed.
Lemma D_5342c : decode_any W_5342c = Some (Auipc 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53430 : bv 32 := 0x7c853a83.
Lemma F_53430 : fetch_word Ubsan.M.loaded_segments (0x5520c : word) = Some W_53430.
Proof. vm_refl. Qed.
Lemma D_53430 : decode_any W_53430 = Some (Load SZ8 true 21 10 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_53434 : bv 32 := 0x000ab503.
Lemma F_53434 : fetch_word Ubsan.M.loaded_segments (0x55210 : word) = Some W_53434.
Proof. vm_refl. Qed.
Lemma D_53434 : decode_any W_53434 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53438 : bv 32 := 0x02a13423.
Lemma F_53438 : fetch_word Ubsan.M.loaded_segments (0x55214 : word) = Some W_53438.
Proof. vm_refl. Qed.
Lemma D_53438 : decode_any W_53438 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5343c : bv 32 := 0x0284b503.
Lemma F_5343c : fetch_word Ubsan.M.loaded_segments (0x55218 : word) = Some W_5343c.
Proof. vm_refl. Qed.
Lemma D_5343c : decode_any W_5343c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_53440 : bv 32 := 0x0384b603.
Lemma F_53440 : fetch_word Ubsan.M.loaded_segments (0x5521c : word) = Some W_53440.
Proof. vm_refl. Qed.
Lemma D_53440 : decode_any W_53440 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53444 : bv 32 := 0x40c50b33.
Lemma F_53444 : fetch_word Ubsan.M.loaded_segments (0x55220 : word) = Some W_53444.
Proof. vm_refl. Qed.
Lemma D_53444 : decode_any W_53444 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53448 : bv 32 := 0x00c546b3.
Lemma F_53448 : fetch_word Ubsan.M.loaded_segments (0x55224 : word) = Some W_53448.
Proof. vm_refl. Qed.
Lemma D_53448 : decode_any W_53448 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5344c : bv 32 := 0x00c13423.
Lemma F_5344c : fetch_word Ubsan.M.loaded_segments (0x55228 : word) = Some W_5344c.
Proof. vm_refl. Qed.
Lemma D_5344c : decode_any W_5344c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53450 : bv 32 := 0x01613823.
Lemma F_53450 : fetch_word Ubsan.M.loaded_segments (0x5522c : word) = Some W_53450.
Proof. vm_refl. Qed.
Lemma D_53450 : decode_any W_53450 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53454 : bv 32 := 0x00b13c23.
Lemma F_53454 : fetch_word Ubsan.M.loaded_segments (0x55230 : word) = Some W_53454.
Proof. vm_refl. Qed.
Lemma D_53454 : decode_any W_53454 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53458 : bv 32 := 0x02813023.
Lemma F_53458 : fetch_word Ubsan.M.loaded_segments (0x55234 : word) = Some W_53458.
Proof. vm_refl. Qed.
Lemma D_53458 : decode_any W_53458 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5345c : bv 32 := 0x008b0b33.
Lemma F_5345c : fetch_word Ubsan.M.loaded_segments (0x55238 : word) = Some W_5345c.
Proof. vm_refl. Qed.
Lemma D_5345c : decode_any W_5345c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53460 : bv 32 := 0x00d03933.
Lemma F_53460 : fetch_word Ubsan.M.loaded_segments (0x5523c : word) = Some W_53460.
Proof. vm_refl. Qed.
Lemma D_53460 : decode_any W_53460 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_53464 : bv 32 := 0x00c50663.
Lemma F_53464 : fetch_word Ubsan.M.loaded_segments (0x55240 : word) = Some W_53464.
Proof. vm_refl. Qed.
Lemma D_53464 : decode_any W_53464 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53468 : bv 32 := 0x00810993.
Lemma F_53468 : fetch_word Ubsan.M.loaded_segments (0x55244 : word) = Some W_53468.
Proof. vm_refl. Qed.
Lemma D_53468 : decode_any W_53468 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5346c : bv 32 := 0x0080006f.
Lemma F_5346c : fetch_word Ubsan.M.loaded_segments (0x55248 : word) = Some W_5346c.
Proof. vm_refl. Qed.
Lemma D_5346c : decode_any W_5346c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53470 : bv 32 := 0x01810993.
Lemma F_53470 : fetch_word Ubsan.M.loaded_segments (0x5524c : word) = Some W_53470.
Proof. vm_refl. Qed.
Lemma D_53470 : decode_any W_53470 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53474 : bv 32 := 0x0784a503.
Lemma F_53474 : fetch_word Ubsan.M.loaded_segments (0x55250 : word) = Some W_53474.
Proof. vm_refl. Qed.
Lemma D_53474 : decode_any W_53474 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_53478 : bv 32 := 0x00190913.
Lemma F_53478 : fetch_word Ubsan.M.loaded_segments (0x55254 : word) = Some W_53478.
Proof. vm_refl. Qed.
Lemma D_53478 : decode_any W_53478 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5347c : bv 32 := 0x04200893.
Lemma F_5347c : fetch_word Ubsan.M.loaded_segments (0x55258 : word) = Some W_5347c.
Proof. vm_refl. Qed.
Lemma D_5347c : decode_any W_5347c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_53480 : bv 32 := 0x00098593.
Lemma F_53480 : fetch_word Ubsan.M.loaded_segments (0x5525c : word) = Some W_53480.
Proof. vm_refl. Qed.
Lemma D_53480 : decode_any W_53480 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53484 : bv 32 := 0x00090613.
Lemma F_53484 : fetch_word Ubsan.M.loaded_segments (0x55260 : word) = Some W_53484.
Proof. vm_refl. Qed.
Lemma D_53484 : decode_any W_53484 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53488 : bv 32 := 0x00000073.
Lemma F_53488 : fetch_word Ubsan.M.loaded_segments (0x55264 : word) = Some W_53488.
Proof. vm_refl. Qed.

Lemma E_53488 : is_ecall W_53488 = true.
Proof. reflexivity. Qed.

Definition W_5348c : bv 32 := 0xdc5fb0ef.
Lemma F_5348c : fetch_word Ubsan.M.loaded_segments (0x55268 : word) = Some W_5348c.
Proof. vm_refl. Qed.
Lemma D_5348c : decode_any W_5348c = Some (Jal 1 2080196, 4%Z).
Proof. vm_refl. Qed.

Definition W_53490 : bv 32 := 0x09651863.
Lemma F_53490 : fetch_word Ubsan.M.loaded_segments (0x5526c : word) = Some W_53490.
Proof. vm_refl. Qed.
Lemma D_53490 : decode_any W_53490 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_53494 : bv 32 := 0x0584b503.
Lemma F_53494 : fetch_word Ubsan.M.loaded_segments (0x55270 : word) = Some W_53494.
Proof. vm_refl. Qed.
Lemma D_53494 : decode_any W_53494 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_53498 : bv 32 := 0x0604b583.
Lemma F_53498 : fetch_word Ubsan.M.loaded_segments (0x55274 : word) = Some W_53498.
Proof. vm_refl. Qed.
Lemma D_53498 : decode_any W_53498 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5349c : bv 32 := 0x00b505b3.
Lemma F_5349c : fetch_word Ubsan.M.loaded_segments (0x55278 : word) = Some W_5349c.
Proof. vm_refl. Qed.
Lemma D_5349c : decode_any W_5349c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a0 : bv 32 := 0x02b4b023.
Lemma F_534a0 : fetch_word Ubsan.M.loaded_segments (0x5527c : word) = Some W_534a0.
Proof. vm_refl. Qed.
Lemma D_534a0 : decode_any W_534a0 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a4 : bv 32 := 0x02a4b423.
Lemma F_534a4 : fetch_word Ubsan.M.loaded_segments (0x55280 : word) = Some W_534a4.
Proof. vm_refl. Qed.
Lemma D_534a4 : decode_any W_534a4 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a8 : bv 32 := 0x02a4bc23.
Lemma F_534a8 : fetch_word Ubsan.M.loaded_segments (0x55284 : word) = Some W_534a8.
Proof. vm_refl. Qed.
Lemma D_534a8 : decode_any W_534a8 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_534ac : bv 32 := 0x00040513.
Lemma F_534ac : fetch_word Ubsan.M.loaded_segments (0x55288 : word) = Some W_534ac.
Proof. vm_refl. Qed.
Lemma D_534ac : decode_any W_534ac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b0 : bv 32 := 0x000ab583.
Lemma F_534b0 : fetch_word Ubsan.M.loaded_segments (0x5528c : word) = Some W_534b0.
Proof. vm_refl. Qed.
Lemma D_534b0 : decode_any W_534b0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b4 : bv 32 := 0x02813603.
Lemma F_534b4 : fetch_word Ubsan.M.loaded_segments (0x55290 : word) = Some W_534b4.
Proof. vm_refl. Qed.
Lemma D_534b4 : decode_any W_534b4 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b8 : bv 32 := 0x0cc59a63.
Lemma F_534b8 : fetch_word Ubsan.M.loaded_segments (0x55294 : word) = Some W_534b8.
Proof. vm_refl. Qed.
Lemma D_534b8 : decode_any W_534b8 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_534bc : bv 32 := 0x06813083.
Lemma F_534bc : fetch_word Ubsan.M.loaded_segments (0x55298 : word) = Some W_534bc.
Proof. vm_refl. Qed.
Lemma D_534bc : decode_any W_534bc = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c0 : bv 32 := 0x06013403.
Lemma F_534c0 : fetch_word Ubsan.M.loaded_segments (0x5529c : word) = Some W_534c0.
Proof. vm_refl. Qed.
Lemma D_534c0 : decode_any W_534c0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c4 : bv 32 := 0x05813483.
Lemma F_534c4 : fetch_word Ubsan.M.loaded_segments (0x552a0 : word) = Some W_534c4.
Proof. vm_refl. Qed.
Lemma D_534c4 : decode_any W_534c4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c8 : bv 32 := 0x05013903.
Lemma F_534c8 : fetch_word Ubsan.M.loaded_segments (0x552a4 : word) = Some W_534c8.
Proof. vm_refl. Qed.
Lemma D_534c8 : decode_any W_534c8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_534cc : bv 32 := 0x04813983.
Lemma F_534cc : fetch_word Ubsan.M.loaded_segments (0x552a8 : word) = Some W_534cc.
Proof. vm_refl. Qed.
Lemma D_534cc : decode_any W_534cc = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d0 : bv 32 := 0x04013a03.
Lemma F_534d0 : fetch_word Ubsan.M.loaded_segments (0x552ac : word) = Some W_534d0.
Proof. vm_refl. Qed.
Lemma D_534d0 : decode_any W_534d0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d4 : bv 32 := 0x03813a83.
Lemma F_534d4 : fetch_word Ubsan.M.loaded_segments (0x552b0 : word) = Some W_534d4.
Proof. vm_refl. Qed.
Lemma D_534d4 : decode_any W_534d4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d8 : bv 32 := 0x03013b03.
Lemma F_534d8 : fetch_word Ubsan.M.loaded_segments (0x552b4 : word) = Some W_534d8.
Proof. vm_refl. Qed.
Lemma D_534d8 : decode_any W_534d8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_534dc : bv 32 := 0x07010113.
Lemma F_534dc : fetch_word Ubsan.M.loaded_segments (0x552b8 : word) = Some W_534dc.
Proof. vm_refl. Qed.
Lemma D_534dc : decode_any W_534dc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e0 : bv 32 := 0x00008067.
Lemma F_534e0 : fetch_word Ubsan.M.loaded_segments (0x552bc : word) = Some W_534e0.
Proof. vm_refl. Qed.
Lemma D_534e0 : decode_any W_534e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e4 : bv 32 := 0x00800713.
Lemma F_534e4 : fetch_word Ubsan.M.loaded_segments (0x552c0 : word) = Some W_534e4.
Proof. vm_refl. Qed.
Lemma D_534e4 : decode_any W_534e4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e8 : bv 32 := 0x000a0593.
Lemma F_534e8 : fetch_word Ubsan.M.loaded_segments (0x552c4 : word) = Some W_534e8.
Proof. vm_refl. Qed.
Lemma D_534e8 : decode_any W_534e8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534ec : bv 32 := 0x00e98733.
Lemma F_534ec : fetch_word Ubsan.M.loaded_segments (0x552c8 : word) = Some W_534ec.
Proof. vm_refl. Qed.
Lemma D_534ec : decode_any W_534ec = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_534f0 : bv 32 := 0x00073783.
Lemma F_534f0 : fetch_word Ubsan.M.loaded_segments (0x552cc : word) = Some W_534f0.
Proof. vm_refl. Qed.
Lemma D_534f0 : decode_any W_534f0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534f4 : bv 32 := 0x40ab0b33.
Lemma F_534f4 : fetch_word Ubsan.M.loaded_segments (0x552d0 : word) = Some W_534f4.
Proof. vm_refl. Qed.
Lemma D_534f4 : decode_any W_534f4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_534f8 : bv 32 := 0x0784a503.
Lemma F_534f8 : fetch_word Ubsan.M.loaded_segments (0x552d4 : word) = Some W_534f8.
Proof. vm_refl. Qed.
Lemma D_534f8 : decode_any W_534f8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_534fc : bv 32 := 0x40c9093b.
Lemma F_534fc : fetch_word Ubsan.M.loaded_segments (0x552d8 : word) = Some W_534fc.
Proof. vm_refl. Qed.
Lemma D_534fc : decode_any W_534fc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53500 : bv 32 := 0x40d787b3.
Lemma F_53500 : fetch_word Ubsan.M.loaded_segments (0x552dc : word) = Some W_53500.
Proof. vm_refl. Qed.
Lemma D_53500 : decode_any W_53500 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_53504 : bv 32 := 0x00f73023.
Lemma F_53504 : fetch_word Ubsan.M.loaded_segments (0x552e0 : word) = Some W_53504.
Proof. vm_refl. Qed.
Lemma D_53504 : decode_any W_53504 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53508 : bv 32 := 0x04200893.
Lemma F_53508 : fetch_word Ubsan.M.loaded_segments (0x552e4 : word) = Some W_53508.
Proof. vm_refl. Qed.
Lemma D_53508 : decode_any W_53508 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_5350c : bv 32 := 0x00090613.
Lemma F_5350c : fetch_word Ubsan.M.loaded_segments (0x552e8 : word) = Some W_5350c.
Proof. vm_refl. Qed.
Lemma D_5350c : decode_any W_5350c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53510 : bv 32 := 0x00000073.
Lemma F_53510 : fetch_word Ubsan.M.loaded_segments (0x552ec : word) = Some W_53510.
Proof. vm_refl. Qed.

Lemma E_53510 : is_ecall W_53510 = true.
Proof. reflexivity. Qed.

Definition W_53514 : bv 32 := 0xd3dfb0ef.
Lemma F_53514 : fetch_word Ubsan.M.loaded_segments (0x552f0 : word) = Some W_53514.
Proof. vm_refl. Qed.
Lemma D_53514 : decode_any W_53514 = Some (Jal 1 2080060, 4%Z).
Proof. vm_refl. Qed.

Definition W_53518 : bv 32 := 0x000a0993.
Lemma F_53518 : fetch_word Ubsan.M.loaded_segments (0x552f4 : word) = Some W_53518.
Proof. vm_refl. Qed.
Lemma D_53518 : decode_any W_53518 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5351c : bv 32 := 0xf7650ce3.
Lemma F_5351c : fetch_word Ubsan.M.loaded_segments (0x552f8 : word) = Some W_5351c.
Proof. vm_refl. Qed.
Lemma D_5351c : decode_any W_5351c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_53520 : bv 32 := 0x02054c63.
Lemma F_53520 : fetch_word Ubsan.M.loaded_segments (0x552fc : word) = Some W_53520.
Proof. vm_refl. Qed.
Lemma D_53520 : decode_any W_53520 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53524 : bv 32 := 0x0089b583.
Lemma F_53524 : fetch_word Ubsan.M.loaded_segments (0x55300 : word) = Some W_53524.
Proof. vm_refl. Qed.
Lemma D_53524 : decode_any W_53524 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53528 : bv 32 := 0x00a5b633.
Lemma F_53528 : fetch_word Ubsan.M.loaded_segments (0x55304 : word) = Some W_53528.
Proof. vm_refl. Qed.
Lemma D_53528 : decode_any W_53528 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5352c : bv 32 := 0x00461a13.
Lemma F_5352c : fetch_word Ubsan.M.loaded_segments (0x55308 : word) = Some W_5352c.
Proof. vm_refl. Qed.
Lemma D_5352c : decode_any W_5352c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_53530 : bv 32 := 0x01498a33.
Lemma F_53530 : fetch_word Ubsan.M.loaded_segments (0x5530c : word) = Some W_53530.
Proof. vm_refl. Qed.
Lemma D_53530 : decode_any W_53530 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_53534 : bv 32 := 0x000a3703.
Lemma F_53534 : fetch_word Ubsan.M.loaded_segments (0x55310 : word) = Some W_53534.
Proof. vm_refl. Qed.
Lemma D_53534 : decode_any W_53534 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.
