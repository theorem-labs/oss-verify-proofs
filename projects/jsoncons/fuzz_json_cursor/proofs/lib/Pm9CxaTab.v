(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_66f38 : bv 32 := 0xfa010113.
Lemma Fx_66f38 : fetch_word AsanUbsan.M.loaded_segments (0x66f80 : word) = Some Wx_66f38.
Proof. vm_refl. Qed.
Lemma Dx_66f38 : decode_any Wx_66f38 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f3c : bv 32 := 0x04113c23.
Lemma Fx_66f3c : fetch_word AsanUbsan.M.loaded_segments (0x66f84 : word) = Some Wx_66f3c.
Proof. vm_refl. Qed.
Lemma Dx_66f3c : decode_any Wx_66f3c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f40 : bv 32 := 0x04813823.
Lemma Fx_66f40 : fetch_word AsanUbsan.M.loaded_segments (0x66f88 : word) = Some Wx_66f40.
Proof. vm_refl. Qed.
Lemma Dx_66f40 : decode_any Wx_66f40 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f44 : bv 32 := 0x04913423.
Lemma Fx_66f44 : fetch_word AsanUbsan.M.loaded_segments (0x66f8c : word) = Some Wx_66f44.
Proof. vm_refl. Qed.
Lemma Dx_66f44 : decode_any Wx_66f44 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f48 : bv 32 := 0x05213023.
Lemma Fx_66f48 : fetch_word AsanUbsan.M.loaded_segments (0x66f90 : word) = Some Wx_66f48.
Proof. vm_refl. Qed.
Lemma Dx_66f48 : decode_any Wx_66f48 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f4c : bv 32 := 0x03313c23.
Lemma Fx_66f4c : fetch_word AsanUbsan.M.loaded_segments (0x66f94 : word) = Some Wx_66f4c.
Proof. vm_refl. Qed.
Lemma Dx_66f4c : decode_any Wx_66f4c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f50 : bv 32 := 0x03413823.
Lemma Fx_66f50 : fetch_word AsanUbsan.M.loaded_segments (0x66f98 : word) = Some Wx_66f50.
Proof. vm_refl. Qed.
Lemma Dx_66f50 : decode_any Wx_66f50 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f54 : bv 32 := 0x03513423.
Lemma Fx_66f54 : fetch_word AsanUbsan.M.loaded_segments (0x66f9c : word) = Some Wx_66f54.
Proof. vm_refl. Qed.
Lemma Dx_66f54 : decode_any Wx_66f54 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f58 : bv 32 := 0x03613023.
Lemma Fx_66f58 : fetch_word AsanUbsan.M.loaded_segments (0x66fa0 : word) = Some Wx_66f58.
Proof. vm_refl. Qed.
Lemma Dx_66f58 : decode_any Wx_66f58 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f5c : bv 32 := 0x01713c23.
Lemma Fx_66f5c : fetch_word AsanUbsan.M.loaded_segments (0x66fa4 : word) = Some Wx_66f5c.
Proof. vm_refl. Qed.
Lemma Dx_66f5c : decode_any Wx_66f5c = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f60 : bv 32 := 0x01813823.
Lemma Fx_66f60 : fetch_word AsanUbsan.M.loaded_segments (0x66fa8 : word) = Some Wx_66f60.
Proof. vm_refl. Qed.
Lemma Dx_66f60 : decode_any Wx_66f60 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f64 : bv 32 := 0x01913423.
Lemma Fx_66f64 : fetch_word AsanUbsan.M.loaded_segments (0x66fac : word) = Some Wx_66f64.
Proof. vm_refl. Qed.
Lemma Dx_66f64 : decode_any Wx_66f64 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f68 : bv 32 := 0x000ed517.
Lemma Fx_66f68 : fetch_word AsanUbsan.M.loaded_segments (0x66fb0 : word) = Some Wx_66f68.
Proof. vm_refl. Qed.
Lemma Dx_66f68 : decode_any Wx_66f68 = Some (Auipc 10 237, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f6c : bv 32 := 0x54853a03.
Lemma Fx_66f6c : fetch_word AsanUbsan.M.loaded_segments (0x66fb4 : word) = Some Wx_66f6c.
Proof. vm_refl. Qed.
Lemma Dx_66f6c : decode_any Wx_66f6c = Some (Load SZ8 true 20 10 1352, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f70 : bv 32 := 0x01ca4503.
Lemma Fx_66f70 : fetch_word AsanUbsan.M.loaded_segments (0x66fb8 : word) = Some Wx_66f70.
Proof. vm_refl. Qed.
Lemma Dx_66f70 : decode_any Wx_66f70 = Some (Load SZ1 false 10 20 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66f74 : bv 32 := 0x1e050e63.
Lemma Fx_66f74 : fetch_word AsanUbsan.M.loaded_segments (0x66fbc : word) = Some Wx_66f74.
Proof. vm_refl. Qed.
Lemma Dx_66f74 : decode_any Wx_66f74 = Some (Branch BC_EQ 10 0 508, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67170 : bv 32 := 0x05813083.
Lemma Fx_67170 : fetch_word AsanUbsan.M.loaded_segments (0x671b8 : word) = Some Wx_67170.
Proof. vm_refl. Qed.
Lemma Dx_67170 : decode_any Wx_67170 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67174 : bv 32 := 0x05013403.
Lemma Fx_67174 : fetch_word AsanUbsan.M.loaded_segments (0x671bc : word) = Some Wx_67174.
Proof. vm_refl. Qed.
Lemma Dx_67174 : decode_any Wx_67174 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67178 : bv 32 := 0x04813483.
Lemma Fx_67178 : fetch_word AsanUbsan.M.loaded_segments (0x671c0 : word) = Some Wx_67178.
Proof. vm_refl. Qed.
Lemma Dx_67178 : decode_any Wx_67178 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6717c : bv 32 := 0x04013903.
Lemma Fx_6717c : fetch_word AsanUbsan.M.loaded_segments (0x671c4 : word) = Some Wx_6717c.
Proof. vm_refl. Qed.
Lemma Dx_6717c : decode_any Wx_6717c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67180 : bv 32 := 0x03813983.
Lemma Fx_67180 : fetch_word AsanUbsan.M.loaded_segments (0x671c8 : word) = Some Wx_67180.
Proof. vm_refl. Qed.
Lemma Dx_67180 : decode_any Wx_67180 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67184 : bv 32 := 0x03013a03.
Lemma Fx_67184 : fetch_word AsanUbsan.M.loaded_segments (0x671cc : word) = Some Wx_67184.
Proof. vm_refl. Qed.
Lemma Dx_67184 : decode_any Wx_67184 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67188 : bv 32 := 0x02813a83.
Lemma Fx_67188 : fetch_word AsanUbsan.M.loaded_segments (0x671d0 : word) = Some Wx_67188.
Proof. vm_refl. Qed.
Lemma Dx_67188 : decode_any Wx_67188 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6718c : bv 32 := 0x02013b03.
Lemma Fx_6718c : fetch_word AsanUbsan.M.loaded_segments (0x671d4 : word) = Some Wx_6718c.
Proof. vm_refl. Qed.
Lemma Dx_6718c : decode_any Wx_6718c = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67190 : bv 32 := 0x01813b83.
Lemma Fx_67190 : fetch_word AsanUbsan.M.loaded_segments (0x671d8 : word) = Some Wx_67190.
Proof. vm_refl. Qed.
Lemma Dx_67190 : decode_any Wx_67190 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67194 : bv 32 := 0x01013c03.
Lemma Fx_67194 : fetch_word AsanUbsan.M.loaded_segments (0x671dc : word) = Some Wx_67194.
Proof. vm_refl. Qed.
Lemma Dx_67194 : decode_any Wx_67194 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_67198 : bv 32 := 0x00813c83.
Lemma Fx_67198 : fetch_word AsanUbsan.M.loaded_segments (0x671e0 : word) = Some Wx_67198.
Proof. vm_refl. Qed.
Lemma Dx_67198 : decode_any Wx_67198 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6719c : bv 32 := 0x06010113.
Lemma Fx_6719c : fetch_word AsanUbsan.M.loaded_segments (0x671e4 : word) = Some Wx_6719c.
Proof. vm_refl. Qed.
Lemma Dx_6719c : decode_any Wx_6719c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_671a0 : bv 32 := 0x00008067.
Lemma Fx_671a0 : fetch_word AsanUbsan.M.loaded_segments (0x671e8 : word) = Some Wx_671a0.
Proof. vm_refl. Qed.
Lemma Dx_671a0 : decode_any Wx_671a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a9a4 : bv 32 := 0x5cc0a06f.
Lemma Fx_6a9a4 : fetch_word AsanUbsan.M.loaded_segments (0x6a9ec : word) = Some Wx_6a9a4.
Proof. vm_refl. Qed.
Lemma Dx_6a9a4 : decode_any Wx_6a9a4 = Some (Jal 0 42444, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f70 : bv 32 := 0xfd010113.
Lemma Fx_74f70 : fetch_word AsanUbsan.M.loaded_segments (0x74fb8 : word) = Some Wx_74f70.
Proof. vm_refl. Qed.
Lemma Dx_74f70 : decode_any Wx_74f70 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f74 : bv 32 := 0x02113423.
Lemma Fx_74f74 : fetch_word AsanUbsan.M.loaded_segments (0x74fbc : word) = Some Wx_74f74.
Proof. vm_refl. Qed.
Lemma Dx_74f74 : decode_any Wx_74f74 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f78 : bv 32 := 0x02813023.
Lemma Fx_74f78 : fetch_word AsanUbsan.M.loaded_segments (0x74fc0 : word) = Some Wx_74f78.
Proof. vm_refl. Qed.
Lemma Dx_74f78 : decode_any Wx_74f78 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f7c : bv 32 := 0x00913c23.
Lemma Fx_74f7c : fetch_word AsanUbsan.M.loaded_segments (0x74fc4 : word) = Some Wx_74f7c.
Proof. vm_refl. Qed.
Lemma Dx_74f7c : decode_any Wx_74f7c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f80 : bv 32 := 0x01213823.
Lemma Fx_74f80 : fetch_word AsanUbsan.M.loaded_segments (0x74fc8 : word) = Some Wx_74f80.
Proof. vm_refl. Qed.
Lemma Dx_74f80 : decode_any Wx_74f80 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f84 : bv 32 := 0x01313423.
Lemma Fx_74f84 : fetch_word AsanUbsan.M.loaded_segments (0x74fcc : word) = Some Wx_74f84.
Proof. vm_refl. Qed.
Lemma Dx_74f84 : decode_any Wx_74f84 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f88 : bv 32 := 0x00060413.
Lemma Fx_74f88 : fetch_word AsanUbsan.M.loaded_segments (0x74fd0 : word) = Some Wx_74f88.
Proof. vm_refl. Qed.
Lemma Dx_74f88 : decode_any Wx_74f88 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f8c : bv 32 := 0x00058493.
Lemma Fx_74f8c : fetch_word AsanUbsan.M.loaded_segments (0x74fd4 : word) = Some Wx_74f8c.
Proof. vm_refl. Qed.
Lemma Dx_74f8c : decode_any Wx_74f8c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f90 : bv 32 := 0x00050913.
Lemma Fx_74f90 : fetch_word AsanUbsan.M.loaded_segments (0x74fd8 : word) = Some Wx_74f90.
Proof. vm_refl. Qed.
Lemma Dx_74f90 : decode_any Wx_74f90 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f94 : bv 32 := 0x364130ef.
Lemma Fx_74f94 : fetch_word AsanUbsan.M.loaded_segments (0x74fdc : word) = Some Wx_74f94.
Proof. vm_refl. Qed.
Lemma Dx_74f94 : decode_any Wx_74f94 = Some (Jal 1 78692, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f98 : bv 32 := 0x29d390ef.
Lemma Fx_74f98 : fetch_word AsanUbsan.M.loaded_segments (0x74fe0 : word) = Some Wx_74f98.
Proof. vm_refl. Qed.
Lemma Dx_74f98 : decode_any Wx_74f98 = Some (Jal 1 236188, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74f9c : bv 32 := 0x000e1997.
Lemma Fx_74f9c : fetch_word AsanUbsan.M.loaded_segments (0x74fe4 : word) = Some Wx_74f9c.
Proof. vm_refl. Qed.
Lemma Dx_74f9c : decode_any Wx_74f9c = Some (Auipc 19 225, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fa0 : bv 32 := 0x4e49b683.
Lemma Fx_74fa0 : fetch_word AsanUbsan.M.loaded_segments (0x74fe8 : word) = Some Wx_74fa0.
Proof. vm_refl. Qed.
Lemma Dx_74fa0 : decode_any Wx_74fa0 = Some (Load SZ8 true 13 19 1252, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fa4 : bv 32 := 0x00090513.
Lemma Fx_74fa4 : fetch_word AsanUbsan.M.loaded_segments (0x74fec : word) = Some Wx_74fa4.
Proof. vm_refl. Qed.
Lemma Dx_74fa4 : decode_any Wx_74fa4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fa8 : bv 32 := 0x00048593.
Lemma Fx_74fa8 : fetch_word AsanUbsan.M.loaded_segments (0x74ff0 : word) = Some Wx_74fa8.
Proof. vm_refl. Qed.
Lemma Dx_74fa8 : decode_any Wx_74fa8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fac : bv 32 := 0x00040613.
Lemma Fx_74fac : fetch_word AsanUbsan.M.loaded_segments (0x74ff4 : word) = Some Wx_74fac.
Proof. vm_refl. Qed.
Lemma Dx_74fac : decode_any Wx_74fac = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fb0 : bv 32 := 0x000680e7.
Lemma Fx_74fb0 : fetch_word AsanUbsan.M.loaded_segments (0x74ff8 : word) = Some Wx_74fb0.
Proof. vm_refl. Qed.
Lemma Dx_74fb0 : decode_any Wx_74fb0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fb4 : bv 32 := 0x4e49b683.
Lemma Fx_74fb4 : fetch_word AsanUbsan.M.loaded_segments (0x74ffc : word) = Some Wx_74fb4.
Proof. vm_refl. Qed.
Lemma Dx_74fb4 : decode_any Wx_74fb4 = Some (Load SZ8 true 13 19 1252, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fb8 : bv 32 := 0x00050413.
Lemma Fx_74fb8 : fetch_word AsanUbsan.M.loaded_segments (0x75000 : word) = Some Wx_74fb8.
Proof. vm_refl. Qed.
Lemma Dx_74fb8 : decode_any Wx_74fb8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fbc : bv 32 := 0x00000517.
Lemma Fx_74fbc : fetch_word AsanUbsan.M.loaded_segments (0x75004 : word) = Some Wx_74fbc.
Proof. vm_refl. Qed.
Lemma Dx_74fbc : decode_any Wx_74fbc = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fc0 : bv 32 := 0x03850513.
Lemma Fx_74fc0 : fetch_word AsanUbsan.M.loaded_segments (0x75008 : word) = Some Wx_74fc0.
Proof. vm_refl. Qed.
Lemma Dx_74fc0 : decode_any Wx_74fc0 = Some (OpImm ALU_ADD 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fc4 : bv 32 := 0x00000593.
Lemma Fx_74fc4 : fetch_word AsanUbsan.M.loaded_segments (0x7500c : word) = Some Wx_74fc4.
Proof. vm_refl. Qed.
Lemma Dx_74fc4 : decode_any Wx_74fc4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fc8 : bv 32 := 0x00000613.
Lemma Fx_74fc8 : fetch_word AsanUbsan.M.loaded_segments (0x75010 : word) = Some Wx_74fc8.
Proof. vm_refl. Qed.
Lemma Dx_74fc8 : decode_any Wx_74fc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fcc : bv 32 := 0x000680e7.
Lemma Fx_74fcc : fetch_word AsanUbsan.M.loaded_segments (0x75014 : word) = Some Wx_74fcc.
Proof. vm_refl. Qed.
Lemma Dx_74fcc : decode_any Wx_74fcc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fd0 : bv 32 := 0x281390ef.
Lemma Fx_74fd0 : fetch_word AsanUbsan.M.loaded_segments (0x75018 : word) = Some Wx_74fd0.
Proof. vm_refl. Qed.
Lemma Dx_74fd0 : decode_any Wx_74fd0 = Some (Jal 1 236160, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fd4 : bv 32 := 0x00040513.
Lemma Fx_74fd4 : fetch_word AsanUbsan.M.loaded_segments (0x7501c : word) = Some Wx_74fd4.
Proof. vm_refl. Qed.
Lemma Dx_74fd4 : decode_any Wx_74fd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fd8 : bv 32 := 0x02813083.
Lemma Fx_74fd8 : fetch_word AsanUbsan.M.loaded_segments (0x75020 : word) = Some Wx_74fd8.
Proof. vm_refl. Qed.
Lemma Dx_74fd8 : decode_any Wx_74fd8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fdc : bv 32 := 0x02013403.
Lemma Fx_74fdc : fetch_word AsanUbsan.M.loaded_segments (0x75024 : word) = Some Wx_74fdc.
Proof. vm_refl. Qed.
Lemma Dx_74fdc : decode_any Wx_74fdc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fe0 : bv 32 := 0x01813483.
Lemma Fx_74fe0 : fetch_word AsanUbsan.M.loaded_segments (0x75028 : word) = Some Wx_74fe0.
Proof. vm_refl. Qed.
Lemma Dx_74fe0 : decode_any Wx_74fe0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fe4 : bv 32 := 0x01013903.
Lemma Fx_74fe4 : fetch_word AsanUbsan.M.loaded_segments (0x7502c : word) = Some Wx_74fe4.
Proof. vm_refl. Qed.
Lemma Dx_74fe4 : decode_any Wx_74fe4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fe8 : bv 32 := 0x00813983.
Lemma Fx_74fe8 : fetch_word AsanUbsan.M.loaded_segments (0x75030 : word) = Some Wx_74fe8.
Proof. vm_refl. Qed.
Lemma Dx_74fe8 : decode_any Wx_74fe8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74fec : bv 32 := 0x03010113.
Lemma Fx_74fec : fetch_word AsanUbsan.M.loaded_segments (0x75034 : word) = Some Wx_74fec.
Proof. vm_refl. Qed.
Lemma Dx_74fec : decode_any Wx_74fec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74ff0 : bv 32 := 0x00008067.
Lemma Fx_74ff0 : fetch_word AsanUbsan.M.loaded_segments (0x75038 : word) = Some Wx_74ff0.
Proof. vm_refl. Qed.
Lemma Dx_74ff0 : decode_any Wx_74ff0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74ff4 : bv 32 := 0xf45f106f.
Lemma Fx_74ff4 : fetch_word AsanUbsan.M.loaded_segments (0x7503c : word) = Some Wx_74ff4.
Proof. vm_refl. Qed.
Lemma Dx_74ff4 : decode_any Wx_74ff4 = Some (Jal 0 2039620, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_882f8 : bv 32 := 0xff010113.
Lemma Fx_882f8 : fetch_word AsanUbsan.M.loaded_segments (0x88340 : word) = Some Wx_882f8.
Proof. vm_refl. Qed.
Lemma Dx_882f8 : decode_any Wx_882f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_882fc : bv 32 := 0x00113423.
Lemma Fx_882fc : fetch_word AsanUbsan.M.loaded_segments (0x88344 : word) = Some Wx_882fc.
Proof. vm_refl. Qed.
Lemma Dx_882fc : decode_any Wx_882fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88300 : bv 32 := 0x00813023.
Lemma Fx_88300 : fetch_word AsanUbsan.M.loaded_segments (0x88348 : word) = Some Wx_88300.
Proof. vm_refl. Qed.
Lemma Dx_88300 : decode_any Wx_88300 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88304 : bv 32 := 0x000d6517.
Lemma Fx_88304 : fetch_word AsanUbsan.M.loaded_segments (0x8834c : word) = Some Wx_88304.
Proof. vm_refl. Qed.
Lemma Dx_88304 : decode_any Wx_88304 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88308 : bv 32 := 0x68c50413.
Lemma Fx_88308 : fetch_word AsanUbsan.M.loaded_segments (0x88350 : word) = Some Wx_88308.
Proof. vm_refl. Qed.
Lemma Dx_88308 : decode_any Wx_88308 = Some (OpImm ALU_ADD 8 10 1676, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8830c : bv 32 := 0x00040503.
Lemma Fx_8830c : fetch_word AsanUbsan.M.loaded_segments (0x88354 : word) = Some Wx_8830c.
Proof. vm_refl. Qed.
Lemma Dx_8830c : decode_any Wx_8830c = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88310 : bv 32 := 0x00100593.
Lemma Fx_88310 : fetch_word AsanUbsan.M.loaded_segments (0x88358 : word) = Some Wx_88310.
Proof. vm_refl. Qed.
Lemma Dx_88310 : decode_any Wx_88310 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88314 : bv 32 := 0x0230000f.
Lemma Fx_88314 : fetch_word AsanUbsan.M.loaded_segments (0x8835c : word) = Some Wx_88314.
Proof. vm_refl. Qed.
Lemma Dx_88314 : decode_any Wx_88314 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88318 : bv 32 := 0x00b51a63.
Lemma Fx_88318 : fetch_word AsanUbsan.M.loaded_segments (0x88360 : word) = Some Wx_88318.
Proof. vm_refl. Qed.
Lemma Dx_88318 : decode_any Wx_88318 = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8831c : bv 32 := 0x00813083.
Lemma Fx_8831c : fetch_word AsanUbsan.M.loaded_segments (0x88364 : word) = Some Wx_8831c.
Proof. vm_refl. Qed.
Lemma Dx_8831c : decode_any Wx_8831c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88320 : bv 32 := 0x00013403.
Lemma Fx_88320 : fetch_word AsanUbsan.M.loaded_segments (0x88368 : word) = Some Wx_88320.
Proof. vm_refl. Qed.
Lemma Dx_88320 : decode_any Wx_88320 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88324 : bv 32 := 0x01010113.
Lemma Fx_88324 : fetch_word AsanUbsan.M.loaded_segments (0x8836c : word) = Some Wx_88324.
Proof. vm_refl. Qed.
Lemma Dx_88324 : decode_any Wx_88324 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_88328 : bv 32 := 0x00008067.
Lemma Fx_88328 : fetch_word AsanUbsan.M.loaded_segments (0x88370 : word) = Some Wx_88328.
Proof. vm_refl. Qed.
Lemma Dx_88328 : decode_any Wx_88328 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea34 : bv 32 := 0x000a6517.
Lemma Fx_aea34 : fetch_word AsanUbsan.M.loaded_segments (0xaea7c : word) = Some Wx_aea34.
Proof. vm_refl. Qed.
Lemma Dx_aea34 : decode_any Wx_aea34 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea38 : bv 32 := 0x6e453503.
Lemma Fx_aea38 : fetch_word AsanUbsan.M.loaded_segments (0xaea80 : word) = Some Wx_aea38.
Proof. vm_refl. Qed.
Lemma Dx_aea38 : decode_any Wx_aea38 = Some (Load SZ8 true 10 10 1764, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea3c : bv 32 := 0x00450533.
Lemma Fx_aea3c : fetch_word AsanUbsan.M.loaded_segments (0xaea84 : word) = Some Wx_aea3c.
Proof. vm_refl. Qed.
Lemma Dx_aea3c : decode_any Wx_aea3c = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea40 : bv 32 := 0x00052583.
Lemma Fx_aea40 : fetch_word AsanUbsan.M.loaded_segments (0xaea88 : word) = Some Wx_aea40.
Proof. vm_refl. Qed.
Lemma Dx_aea40 : decode_any Wx_aea40 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea44 : bv 32 := 0x00158593.
Lemma Fx_aea44 : fetch_word AsanUbsan.M.loaded_segments (0xaea8c : word) = Some Wx_aea44.
Proof. vm_refl. Qed.
Lemma Dx_aea44 : decode_any Wx_aea44 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea48 : bv 32 := 0x00b52023.
Lemma Fx_aea48 : fetch_word AsanUbsan.M.loaded_segments (0xaea90 : word) = Some Wx_aea48.
Proof. vm_refl. Qed.
Lemma Dx_aea48 : decode_any Wx_aea48 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea4c : bv 32 := 0x00008067.
Lemma Fx_aea4c : fetch_word AsanUbsan.M.loaded_segments (0xaea94 : word) = Some Wx_aea4c.
Proof. vm_refl. Qed.
Lemma Dx_aea4c : decode_any Wx_aea4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea50 : bv 32 := 0xff010113.
Lemma Fx_aea50 : fetch_word AsanUbsan.M.loaded_segments (0xaea98 : word) = Some Wx_aea50.
Proof. vm_refl. Qed.
Lemma Dx_aea50 : decode_any Wx_aea50 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea54 : bv 32 := 0x00113423.
Lemma Fx_aea54 : fetch_word AsanUbsan.M.loaded_segments (0xaea9c : word) = Some Wx_aea54.
Proof. vm_refl. Qed.
Lemma Dx_aea54 : decode_any Wx_aea54 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea58 : bv 32 := 0x00813023.
Lemma Fx_aea58 : fetch_word AsanUbsan.M.loaded_segments (0xaeaa0 : word) = Some Wx_aea58.
Proof. vm_refl. Qed.
Lemma Dx_aea58 : decode_any Wx_aea58 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea5c : bv 32 := 0x000a6517.
Lemma Fx_aea5c : fetch_word AsanUbsan.M.loaded_segments (0xaeaa4 : word) = Some Wx_aea5c.
Proof. vm_refl. Qed.
Lemma Dx_aea5c : decode_any Wx_aea5c = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea60 : bv 32 := 0x6bc53403.
Lemma Fx_aea60 : fetch_word AsanUbsan.M.loaded_segments (0xaeaa8 : word) = Some Wx_aea60.
Proof. vm_refl. Qed.
Lemma Dx_aea60 : decode_any Wx_aea60 = Some (Load SZ8 true 8 10 1724, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea64 : bv 32 := 0x00440433.
Lemma Fx_aea64 : fetch_word AsanUbsan.M.loaded_segments (0xaeaac : word) = Some Wx_aea64.
Proof. vm_refl. Qed.
Lemma Dx_aea64 : decode_any Wx_aea64 = Some (Op ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea68 : bv 32 := 0x00042503.
Lemma Fx_aea68 : fetch_word AsanUbsan.M.loaded_segments (0xaeab0 : word) = Some Wx_aea68.
Proof. vm_refl. Qed.
Lemma Dx_aea68 : decode_any Wx_aea68 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea6c : bv 32 := 0x00050e63.
Lemma Fx_aea6c : fetch_word AsanUbsan.M.loaded_segments (0xaeab4 : word) = Some Wx_aea6c.
Proof. vm_refl. Qed.
Lemma Dx_aea6c : decode_any Wx_aea6c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea70 : bv 32 := 0xfff50513.
Lemma Fx_aea70 : fetch_word AsanUbsan.M.loaded_segments (0xaeab8 : word) = Some Wx_aea70.
Proof. vm_refl. Qed.
Lemma Dx_aea70 : decode_any Wx_aea70 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea74 : bv 32 := 0x00a42023.
Lemma Fx_aea74 : fetch_word AsanUbsan.M.loaded_segments (0xaeabc : word) = Some Wx_aea74.
Proof. vm_refl. Qed.
Lemma Dx_aea74 : decode_any Wx_aea74 = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea78 : bv 32 := 0x00813083.
Lemma Fx_aea78 : fetch_word AsanUbsan.M.loaded_segments (0xaeac0 : word) = Some Wx_aea78.
Proof. vm_refl. Qed.
Lemma Dx_aea78 : decode_any Wx_aea78 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea7c : bv 32 := 0x00013403.
Lemma Fx_aea7c : fetch_word AsanUbsan.M.loaded_segments (0xaeac4 : word) = Some Wx_aea7c.
Proof. vm_refl. Qed.
Lemma Dx_aea7c : decode_any Wx_aea7c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea80 : bv 32 := 0x01010113.
Lemma Fx_aea80 : fetch_word AsanUbsan.M.loaded_segments (0xaeac8 : word) = Some Wx_aea80.
Proof. vm_refl. Qed.
Lemma Dx_aea80 : decode_any Wx_aea80 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_aea84 : bv 32 := 0x00008067.
Lemma Fx_aea84 : fetch_word AsanUbsan.M.loaded_segments (0xaeacc : word) = Some Wx_aea84.
Proof. vm_refl. Qed.
Lemma Dx_aea84 : decode_any Wx_aea84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

