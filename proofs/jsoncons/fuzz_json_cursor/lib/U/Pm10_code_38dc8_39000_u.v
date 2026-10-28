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

Definition W_38dc8 : bv 32 := 0xfffd7197.
Lemma F_38dc8 : fetch_word Ubsan.M.loaded_segments (0x39100 : word) = Some W_38dc8.
Proof. vm_refl. Qed.
Lemma D_38dc8 : decode_any W_38dc8 = Some (Auipc 3 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dcc : bv 32 := 0x70018193.
Lemma F_38dcc : fetch_word Ubsan.M.loaded_segments (0x39104 : word) = Some W_38dcc.
Proof. vm_refl. Qed.
Lemma D_38dcc : decode_any W_38dcc = Some (OpImm ALU_ADD 3 3 1792, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dd0 : bv 32 := 0x00010513.
Lemma F_38dd0 : fetch_word Ubsan.M.loaded_segments (0x39108 : word) = Some W_38dd0.
Proof. vm_refl. Qed.
Lemma D_38dd0 : decode_any W_38dd0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dd4 : bv 32 := 0xfffc7597.
Lemma F_38dd4 : fetch_word Ubsan.M.loaded_segments (0x3910c : word) = Some W_38dd4.
Proof. vm_refl. Qed.
Lemma D_38dd4 : decode_any W_38dd4 = Some (Auipc 11 1048519, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dd8 : bv 32 := 0xef458593.
Lemma F_38dd8 : fetch_word Ubsan.M.loaded_segments (0x39110 : word) = Some W_38dd8.
Proof. vm_refl. Qed.
Lemma D_38dd8 : decode_any W_38dd8 = Some (OpImm ALU_ADD 11 11 3828, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ddc : bv 32 := 0xff017113.
Lemma F_38ddc : fetch_word Ubsan.M.loaded_segments (0x39114 : word) = Some W_38ddc.
Proof. vm_refl. Qed.
Lemma D_38ddc : decode_any W_38ddc = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38de0 : bv 32 := 0x0040006f.
Lemma F_38de0 : fetch_word Ubsan.M.loaded_segments (0x39118 : word) = Some W_38de0.
Proof. vm_refl. Qed.
Lemma D_38de0 : decode_any W_38de0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38de4 : bv 32 := 0x00052583.
Lemma F_38de4 : fetch_word Ubsan.M.loaded_segments (0x3911c : word) = Some W_38de4.
Proof. vm_refl. Qed.
Lemma D_38de4 : decode_any W_38de4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38de8 : bv 32 := 0x0008a617.
Lemma F_38de8 : fetch_word Ubsan.M.loaded_segments (0x39120 : word) = Some W_38de8.
Proof. vm_refl. Qed.
Lemma D_38de8 : decode_any W_38de8 = Some (Auipc 12 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dec : bv 32 := 0x0008a697.
Lemma F_38dec : fetch_word Ubsan.M.loaded_segments (0x39124 : word) = Some W_38dec.
Proof. vm_refl. Qed.
Lemma D_38dec : decode_any W_38dec = Some (Auipc 13 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38df0 : bv 32 := 0x0008a717.
Lemma F_38df0 : fetch_word Ubsan.M.loaded_segments (0x39128 : word) = Some W_38df0.
Proof. vm_refl. Qed.
Lemma D_38df0 : decode_any W_38df0 = Some (Auipc 14 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38df4 : bv 32 := 0x78863783.
Lemma F_38df4 : fetch_word Ubsan.M.loaded_segments (0x3912c : word) = Some W_38df4.
Proof. vm_refl. Qed.
Lemma D_38df4 : decode_any W_38df4 = Some (Load SZ8 true 15 12 1928, 4%Z).
Proof. vm_refl. Qed.

Definition W_38df8 : bv 32 := 0x78c6b683.
Lemma F_38df8 : fetch_word Ubsan.M.loaded_segments (0x39130 : word) = Some W_38df8.
Proof. vm_refl. Qed.
Lemma D_38df8 : decode_any W_38df8 = Some (Load SZ8 true 13 13 1932, 4%Z).
Proof. vm_refl. Qed.

Definition W_38dfc : bv 32 := 0x79073703.
Lemma F_38dfc : fetch_word Ubsan.M.loaded_segments (0x39134 : word) = Some W_38dfc.
Proof. vm_refl. Qed.
Lemma D_38dfc : decode_any W_38dfc = Some (Load SZ8 true 14 14 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e00 : bv 32 := 0x00850613.
Lemma F_38e00 : fetch_word Ubsan.M.loaded_segments (0x39138 : word) = Some W_38e00.
Proof. vm_refl. Qed.
Lemma D_38e00 : decode_any W_38e00 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e04 : bv 32 := 0x00078513.
Lemma F_38e04 : fetch_word Ubsan.M.loaded_segments (0x3913c : word) = Some W_38e04.
Proof. vm_refl. Qed.
Lemma D_38e04 : decode_any W_38e04 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e08 : bv 32 := 0x00000793.
Lemma F_38e08 : fetch_word Ubsan.M.loaded_segments (0x39140 : word) = Some W_38e08.
Proof. vm_refl. Qed.
Lemma D_38e08 : decode_any W_38e08 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e0c : bv 32 := 0x12d6d06f.
Lemma F_38e0c : fetch_word Ubsan.M.loaded_segments (0x39144 : word) = Some W_38e0c.
Proof. vm_refl. Qed.
Lemma D_38e0c : decode_any W_38e0c = Some (Jal 0 448812, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e10 : bv 32 := 0xff010113.
Lemma F_38e10 : fetch_word Ubsan.M.loaded_segments (0x39148 : word) = Some W_38e10.
Proof. vm_refl. Qed.
Lemma D_38e10 : decode_any W_38e10 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e14 : bv 32 := 0x00113423.
Lemma F_38e14 : fetch_word Ubsan.M.loaded_segments (0x3914c : word) = Some W_38e14.
Proof. vm_refl. Qed.
Lemma D_38e14 : decode_any W_38e14 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e18 : bv 32 := 0x00813023.
Lemma F_38e18 : fetch_word Ubsan.M.loaded_segments (0x39150 : word) = Some W_38e18.
Proof. vm_refl. Qed.
Lemma D_38e18 : decode_any W_38e18 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e1c : bv 32 := 0x01010413.
Lemma F_38e1c : fetch_word Ubsan.M.loaded_segments (0x39154 : word) = Some W_38e1c.
Proof. vm_refl. Qed.
Lemma D_38e1c : decode_any W_38e1c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e20 : bv 32 := 0x0008c517.
Lemma F_38e20 : fetch_word Ubsan.M.loaded_segments (0x39158 : word) = Some W_38e20.
Proof. vm_refl. Qed.
Lemma D_38e20 : decode_any W_38e20 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e24 : bv 32 := 0xc1850513.
Lemma F_38e24 : fetch_word Ubsan.M.loaded_segments (0x3915c : word) = Some W_38e24.
Proof. vm_refl. Qed.
Lemma D_38e24 : decode_any W_38e24 = Some (OpImm ALU_ADD 10 10 3096, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e28 : bv 32 := 0x00054503.
Lemma F_38e28 : fetch_word Ubsan.M.loaded_segments (0x39160 : word) = Some W_38e28.
Proof. vm_refl. Qed.
Lemma D_38e28 : decode_any W_38e28 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e2c : bv 32 := 0x00157513.
Lemma F_38e2c : fetch_word Ubsan.M.loaded_segments (0x39164 : word) = Some W_38e2c.
Proof. vm_refl. Qed.
Lemma D_38e2c : decode_any W_38e2c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e30 : bv 32 := 0x00050663.
Lemma F_38e30 : fetch_word Ubsan.M.loaded_segments (0x39168 : word) = Some W_38e30.
Proof. vm_refl. Qed.
Lemma D_38e30 : decode_any W_38e30 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e3c : bv 32 := 0x0008c517.
Lemma F_38e3c : fetch_word Ubsan.M.loaded_segments (0x39174 : word) = Some W_38e3c.
Proof. vm_refl. Qed.
Lemma D_38e3c : decode_any W_38e3c = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e40 : bv 32 := 0xbfc50593.
Lemma F_38e40 : fetch_word Ubsan.M.loaded_segments (0x39178 : word) = Some W_38e40.
Proof. vm_refl. Qed.
Lemma D_38e40 : decode_any W_38e40 = Some (OpImm ALU_ADD 11 10 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e44 : bv 32 := 0x00100513.
Lemma F_38e44 : fetch_word Ubsan.M.loaded_segments (0x3917c : word) = Some W_38e44.
Proof. vm_refl. Qed.
Lemma D_38e44 : decode_any W_38e44 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e48 : bv 32 := 0x00a58023.
Lemma F_38e48 : fetch_word Ubsan.M.loaded_segments (0x39180 : word) = Some W_38e48.
Proof. vm_refl. Qed.
Lemma D_38e48 : decode_any W_38e48 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e4c : bv 32 := 0x0008a517.
Lemma F_38e4c : fetch_word Ubsan.M.loaded_segments (0x39184 : word) = Some W_38e4c.
Proof. vm_refl. Qed.
Lemma D_38e4c : decode_any W_38e4c = Some (Auipc 10 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e50 : bv 32 := 0x73c53503.
Lemma F_38e50 : fetch_word Ubsan.M.loaded_segments (0x39188 : word) = Some W_38e50.
Proof. vm_refl. Qed.
Lemma D_38e50 : decode_any W_38e50 = Some (Load SZ8 true 10 10 1852, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e54 : bv 32 := 0x02050063.
Lemma F_38e54 : fetch_word Ubsan.M.loaded_segments (0x3918c : word) = Some W_38e54.
Proof. vm_refl. Qed.
Lemma D_38e54 : decode_any W_38e54 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e74 : bv 32 := 0x00813083.
Lemma F_38e74 : fetch_word Ubsan.M.loaded_segments (0x391ac : word) = Some W_38e74.
Proof. vm_refl. Qed.
Lemma D_38e74 : decode_any W_38e74 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e78 : bv 32 := 0x00013403.
Lemma F_38e78 : fetch_word Ubsan.M.loaded_segments (0x391b0 : word) = Some W_38e78.
Proof. vm_refl. Qed.
Lemma D_38e78 : decode_any W_38e78 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e7c : bv 32 := 0x01010113.
Lemma F_38e7c : fetch_word Ubsan.M.loaded_segments (0x391b4 : word) = Some W_38e7c.
Proof. vm_refl. Qed.
Lemma D_38e7c : decode_any W_38e7c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e80 : bv 32 := 0x00008067.
Lemma F_38e80 : fetch_word Ubsan.M.loaded_segments (0x391b8 : word) = Some W_38e80.
Proof. vm_refl. Qed.
Lemma D_38e80 : decode_any W_38e80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e84 : bv 32 := 0xff010113.
Lemma F_38e84 : fetch_word Ubsan.M.loaded_segments (0x391bc : word) = Some W_38e84.
Proof. vm_refl. Qed.
Lemma D_38e84 : decode_any W_38e84 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e88 : bv 32 := 0x00113423.
Lemma F_38e88 : fetch_word Ubsan.M.loaded_segments (0x391c0 : word) = Some W_38e88.
Proof. vm_refl. Qed.
Lemma D_38e88 : decode_any W_38e88 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e8c : bv 32 := 0x00813023.
Lemma F_38e8c : fetch_word Ubsan.M.loaded_segments (0x391c4 : word) = Some W_38e8c.
Proof. vm_refl. Qed.
Lemma D_38e8c : decode_any W_38e8c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e90 : bv 32 := 0x01010413.
Lemma F_38e90 : fetch_word Ubsan.M.loaded_segments (0x391c8 : word) = Some W_38e90.
Proof. vm_refl. Qed.
Lemma D_38e90 : decode_any W_38e90 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e94 : bv 32 := 0x0008c517.
Lemma F_38e94 : fetch_word Ubsan.M.loaded_segments (0x391cc : word) = Some W_38e94.
Proof. vm_refl. Qed.
Lemma D_38e94 : decode_any W_38e94 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e98 : bv 32 := 0xbec50513.
Lemma F_38e98 : fetch_word Ubsan.M.loaded_segments (0x391d0 : word) = Some W_38e98.
Proof. vm_refl. Qed.
Lemma D_38e98 : decode_any W_38e98 = Some (OpImm ALU_ADD 10 10 3052, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e9c : bv 32 := 0x00054503.
Lemma F_38e9c : fetch_word Ubsan.M.loaded_segments (0x391d4 : word) = Some W_38e9c.
Proof. vm_refl. Qed.
Lemma D_38e9c : decode_any W_38e9c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ea0 : bv 32 := 0x00157513.
Lemma F_38ea0 : fetch_word Ubsan.M.loaded_segments (0x391d8 : word) = Some W_38ea0.
Proof. vm_refl. Qed.
Lemma D_38ea0 : decode_any W_38ea0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ea4 : bv 32 := 0x00050663.
Lemma F_38ea4 : fetch_word Ubsan.M.loaded_segments (0x391dc : word) = Some W_38ea4.
Proof. vm_refl. Qed.
Lemma D_38ea4 : decode_any W_38ea4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb0 : bv 32 := 0x0008c517.
Lemma F_38eb0 : fetch_word Ubsan.M.loaded_segments (0x391e8 : word) = Some W_38eb0.
Proof. vm_refl. Qed.
Lemma D_38eb0 : decode_any W_38eb0 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb4 : bv 32 := 0xbd050593.
Lemma F_38eb4 : fetch_word Ubsan.M.loaded_segments (0x391ec : word) = Some W_38eb4.
Proof. vm_refl. Qed.
Lemma D_38eb4 : decode_any W_38eb4 = Some (OpImm ALU_ADD 11 10 3024, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb8 : bv 32 := 0x00100513.
Lemma F_38eb8 : fetch_word Ubsan.M.loaded_segments (0x391f0 : word) = Some W_38eb8.
Proof. vm_refl. Qed.
Lemma D_38eb8 : decode_any W_38eb8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ebc : bv 32 := 0x00a58023.
Lemma F_38ebc : fetch_word Ubsan.M.loaded_segments (0x391f4 : word) = Some W_38ebc.
Proof. vm_refl. Qed.
Lemma D_38ebc : decode_any W_38ebc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec0 : bv 32 := 0x0008a517.
Lemma F_38ec0 : fetch_word Ubsan.M.loaded_segments (0x391f8 : word) = Some W_38ec0.
Proof. vm_refl. Qed.
Lemma D_38ec0 : decode_any W_38ec0 = Some (Auipc 10 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec4 : bv 32 := 0x6d053503.
Lemma F_38ec4 : fetch_word Ubsan.M.loaded_segments (0x391fc : word) = Some W_38ec4.
Proof. vm_refl. Qed.
Lemma D_38ec4 : decode_any W_38ec4 = Some (Load SZ8 true 10 10 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec8 : bv 32 := 0x00050e63.
Lemma F_38ec8 : fetch_word Ubsan.M.loaded_segments (0x39200 : word) = Some W_38ec8.
Proof. vm_refl. Qed.
Lemma D_38ec8 : decode_any W_38ec8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ecc : bv 32 := 0x0040006f.
Lemma F_38ecc : fetch_word Ubsan.M.loaded_segments (0x39204 : word) = Some W_38ecc.
Proof. vm_refl. Qed.
Lemma D_38ecc : decode_any W_38ecc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed0 : bv 32 := 0x0008c517.
Lemma F_38ed0 : fetch_word Ubsan.M.loaded_segments (0x39208 : word) = Some W_38ed0.
Proof. vm_refl. Qed.
Lemma D_38ed0 : decode_any W_38ed0 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed4 : bv 32 := 0x87050513.
Lemma F_38ed4 : fetch_word Ubsan.M.loaded_segments (0x3920c : word) = Some W_38ed4.
Proof. vm_refl. Qed.
Lemma D_38ed4 : decode_any W_38ed4 = Some (OpImm ALU_ADD 10 10 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed8 : bv 32 := 0x00053503.
Lemma F_38ed8 : fetch_word Ubsan.M.loaded_segments (0x39210 : word) = Some W_38ed8.
Proof. vm_refl. Qed.
Lemma D_38ed8 : decode_any W_38ed8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38edc : bv 32 := 0x5696d0ef.
Lemma F_38edc : fetch_word Ubsan.M.loaded_segments (0x39214 : word) = Some W_38edc.
Proof. vm_refl. Qed.
Lemma D_38edc : decode_any W_38edc = Some (Jal 1 449896, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee0 : bv 32 := 0x0040006f.
Lemma F_38ee0 : fetch_word Ubsan.M.loaded_segments (0x39218 : word) = Some W_38ee0.
Proof. vm_refl. Qed.
Lemma D_38ee0 : decode_any W_38ee0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee4 : bv 32 := 0x0008a517.
Lemma F_38ee4 : fetch_word Ubsan.M.loaded_segments (0x3921c : word) = Some W_38ee4.
Proof. vm_refl. Qed.
Lemma D_38ee4 : decode_any W_38ee4 = Some (Auipc 10 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee8 : bv 32 := 0x6b453503.
Lemma F_38ee8 : fetch_word Ubsan.M.loaded_segments (0x39220 : word) = Some W_38ee8.
Proof. vm_refl. Qed.
Lemma D_38ee8 : decode_any W_38ee8 = Some (Load SZ8 true 10 10 1716, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eec : bv 32 := 0x00050c63.
Lemma F_38eec : fetch_word Ubsan.M.loaded_segments (0x39224 : word) = Some W_38eec.
Proof. vm_refl. Qed.
Lemma D_38eec : decode_any W_38eec = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f04 : bv 32 := 0x00813083.
Lemma F_38f04 : fetch_word Ubsan.M.loaded_segments (0x3923c : word) = Some W_38f04.
Proof. vm_refl. Qed.
Lemma D_38f04 : decode_any W_38f04 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f08 : bv 32 := 0x00013403.
Lemma F_38f08 : fetch_word Ubsan.M.loaded_segments (0x39240 : word) = Some W_38f08.
Proof. vm_refl. Qed.
Lemma D_38f08 : decode_any W_38f08 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f0c : bv 32 := 0x01010113.
Lemma F_38f0c : fetch_word Ubsan.M.loaded_segments (0x39244 : word) = Some W_38f0c.
Proof. vm_refl. Qed.
Lemma D_38f0c : decode_any W_38f0c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f10 : bv 32 := 0x00008067.
Lemma F_38f10 : fetch_word Ubsan.M.loaded_segments (0x39248 : word) = Some W_38f10.
Proof. vm_refl. Qed.
Lemma D_38f10 : decode_any W_38f10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

