(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HWord HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_BiW32S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_ContV4 LbB_ContVot.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition bw1f_E (R : bvmap 5 word) (it src spz v b len cap : Z) : env := Eseed R [Z_to_bv 64 it; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 v; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 cap].
Definition bw1f_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition bw1f_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 35); KWord (SA (EVar 35) 0) 8 (EVar 36); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWr (SA (EVar 34) (-64)) (ELit 64); KRange (EVar 34) (2 ^ 45 + 64) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KAlign (EVar 32) 8; KRange (EVar 35) 7241728 (2 ^ 47); KAlign (EVar 35) 8; KRange (EVar 36) 16 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 34) (-64)) (ELit 64); KDisj (SA (EVar 32) 0) (ELit 8) (SA (EVar 34) (-64)) (ELit 64)].
Definition bw1f_F_dirs : list bool := [false; false].
Definition bw1f_F_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [770924; 1018252] (SCR bw1f_F_dirs [] []) 1033820 bw1f_sr bw1f_kn 40.
Definition bw1f_F_x := sym_exec bsegs 200 true [770924; 1018252] (SCR bw1f_F_dirs [] []) (SS 1033820 bw1f_sr [] bw1f_F_knF 40) [].
Definition bw1f_F_ss : sym_state := Eval vm_compute in fst (fst bw1f_F_x).
Definition bw1f_F_scs : list sidecond := Eval vm_compute in snd (fst bw1f_F_x).
Lemma bw1f_F_eq : bw1f_F_x = (bw1f_F_ss, bw1f_F_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw1f_F_pc : s_pc bw1f_F_ss = 770924.
Proof. reflexivity. Qed.
Lemma bw1f_F_sc : forall (R : bvmap 5 word) (m : word -> option byte) (it src spz v b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= it) -> (it + 8 <= 2 ^ 47) -> (it mod 8 = 0) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v mod 8 = 0) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (cap <= 2 ^ 24) -> (16 <= b) -> (len < cap) ->
  scs_denot bsegs m (bw1f_E R it src spz v b len cap) bw1f_F_scs.
Proof.
  intros R m it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold bw1f_E, bw1f_F_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma bw1f_F_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (it src spz v b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= it) -> (it + 8 <= 2 ^ 47) -> (it mod 8 = 0) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v mod 8 = 0) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (cap <= 2 ^ 24) -> (16 <= b) -> (len < cap) ->
  regs_ok (bw1f_E R it src spz v b len cap) bw1f_sr R -> know_ok bsegs (bw1f_E R it src spz v b len cap) m bw1f_F_knF ->
  exists R', regs_ok (bw1f_E R it src spz v b len cap) (s_regs bw1f_F_ss) R' /\ log_flat (bw1f_E R it src spz v b len cap) (s_log bw1f_F_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1033820) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 770924) (mem_denot (bw1f_E R it src spz v b len cap) m (s_log bw1f_F_ss)) rom).
Proof.
  intros fx R m rom it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw1f_F_eq HR HK
              (bw1f_F_sc R m it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw1s_E (R : bvmap 5 word) (it src spz v b len cap : Z) : env := Eseed R [Z_to_bv 64 it; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 v; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 cap].
Definition bw1s_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition bw1s_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 35); KWord (SA (EVar 35) 0) 8 (EVar 36); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWr (SA (EVar 34) (-64)) (ELit 64); KRange (EVar 34) (2 ^ 45 + 64) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KAlign (EVar 32) 8; KRange (EVar 35) 7241728 (2 ^ 47); KAlign (EVar 35) 8; KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 34) (-64)) (ELit 64); KDisj (SA (EVar 32) 0) (ELit 8) (SA (EVar 34) (-64)) (ELit 64)].
Definition bw1s_S_dirs : list bool := [true].
Definition bw1s_S_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [770924; 1018252] (SCR bw1s_S_dirs [] []) 1033820 bw1s_sr bw1s_kn 40.
Definition bw1s_S_x := sym_exec bsegs 200 true [770924; 1018252] (SCR bw1s_S_dirs [] []) (SS 1033820 bw1s_sr [] bw1s_S_knF 40) [].
Definition bw1s_S_ss : sym_state := Eval vm_compute in fst (fst bw1s_S_x).
Definition bw1s_S_scs : list sidecond := Eval vm_compute in snd (fst bw1s_S_x).
Lemma bw1s_S_eq : bw1s_S_x = (bw1s_S_ss, bw1s_S_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw1s_S_pc : s_pc bw1s_S_ss = 1018252.
Proof. reflexivity. Qed.
Lemma bw1s_S_sc : forall (R : bvmap 5 word) (m : word -> option byte) (it src spz v b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= it) -> (it + 8 <= 2 ^ 47) -> (it mod 8 = 0) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v mod 8 = 0) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (cap <= 2 ^ 24) -> (0 <= b) -> (len = cap) ->
  scs_denot bsegs m (bw1s_E R it src spz v b len cap) bw1s_S_scs.
Proof.
  intros R m it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold bw1s_E, bw1s_S_scs. split_scs.
  - sc_closeB.
Qed.
Lemma bw1s_S_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (it src spz v b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= it) -> (it + 8 <= 2 ^ 47) -> (it mod 8 = 0) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v mod 8 = 0) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (cap <= 2 ^ 24) -> (0 <= b) -> (len = cap) ->
  regs_ok (bw1s_E R it src spz v b len cap) bw1s_sr R -> know_ok bsegs (bw1s_E R it src spz v b len cap) m bw1s_S_knF ->
  exists R', regs_ok (bw1s_E R it src spz v b len cap) (s_regs bw1s_S_ss) R' /\ log_flat (bw1s_E R it src spz v b len cap) (s_log bw1s_S_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1033820) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1018252) (mem_denot (bw1s_E R it src spz v b len cap) m (s_log bw1s_S_ss)) rom).
Proof.
  intros fx R m rom it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw1s_S_eq HR HK
              (bw1s_S_sc R m it src spz v b len cap H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw2a_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21; Z_to_bv 64 w22; Z_to_bv 64 it].
Definition bw2a_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EVar 48); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (18%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (19%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EVar 36)].
Definition bw2a_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 0) 8 (EVar 47); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 32 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (ELit 0)].
Definition bw2a_A_dirs : list bool := [].
Definition bw2a_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1034160] (SCR bw2a_A_dirs [] []) 1034024 bw2a_sr bw2a_kn 50.
Definition bw2a_A_x := sym_exec bsegs 200 true [1034160] (SCR bw2a_A_dirs [] []) (SS 1034024 bw2a_sr [] bw2a_A_knF 50) [].
Definition bw2a_A_ss : sym_state := Eval vm_compute in fst (fst bw2a_A_x).
Definition bw2a_A_scs : list sidecond := Eval vm_compute in snd (fst bw2a_A_x).
Lemma bw2a_A_eq : bw2a_A_x = (bw2a_A_ss, bw2a_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw2a_A_pc : s_pc bw2a_A_ss = 1034160.
Proof. reflexivity. Qed.
Lemma bw2a_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) ->
  scs_denot bsegs m (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2a_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23. unfold bw2a_E, bw2a_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma bw2a_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) ->
  regs_ok (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2a_sr R -> know_ok bsegs (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m bw2a_A_knF ->
  exists R', regs_ok (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_regs bw2a_A_ss) R' /\ log_flat (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_log bw2a_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1034024) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1034160) (mem_denot (bw2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m (s_log bw2a_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw2a_A_eq HR HK
              (bw2a_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw2b_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21; Z_to_bv 64 w22; Z_to_bv 64 it].
Definition bw2b_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EVar 48); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (18%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (19%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EVar 36)].
Definition bw2b_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 0) 8 (EVar 47); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 32 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (EVar 38); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (ELit 0); KRange (EVar 38) 1 7].
Definition bw2b_A_dirs : list bool := [true].
Definition bw2b_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1034160] (SCR bw2b_A_dirs [] []) 1034024 bw2b_sr bw2b_kn 50.
Definition bw2b_A_x := sym_exec bsegs 200 true [1034160] (SCR bw2b_A_dirs [] []) (SS 1034024 bw2b_sr [] bw2b_A_knF 50) [].
Definition bw2b_A_ss : sym_state := Eval vm_compute in fst (fst bw2b_A_x).
Definition bw2b_A_scs : list sidecond := Eval vm_compute in snd (fst bw2b_A_x).
Lemma bw2b_A_eq : bw2b_A_x = (bw2b_A_ss, bw2b_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw2b_A_pc : s_pc bw2b_A_ss = 1034160.
Proof. reflexivity. Qed.
Lemma bw2b_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) ->
  scs_denot bsegs m (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2b_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24. unfold bw2b_E, bw2b_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma bw2b_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) ->
  regs_ok (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2b_sr R -> know_ok bsegs (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m bw2b_A_knF ->
  exists R', regs_ok (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_regs bw2b_A_ss) R' /\ log_flat (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_log bw2b_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1034024) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1034160) (mem_denot (bw2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m (s_log bw2b_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw2b_A_eq HR HK
              (bw2b_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw2c_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21; Z_to_bv 64 w22; Z_to_bv 64 it].
Definition bw2c_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EVar 48); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (18%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (19%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EVar 36)].
Definition bw2c_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 0) 8 (EVar 47); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 32 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (EVar 39); KRange (EVar 39) 1 7].
Definition bw2c_A_dirs : list bool := [true].
Definition bw2c_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1034160] (SCR bw2c_A_dirs [] []) 1034024 bw2c_sr bw2c_kn 50.
Definition bw2c_A_x := sym_exec bsegs 200 true [1034160] (SCR bw2c_A_dirs [] []) (SS 1034024 bw2c_sr [] bw2c_A_knF 50) [].
Definition bw2c_A_ss : sym_state := Eval vm_compute in fst (fst bw2c_A_x).
Definition bw2c_A_scs : list sidecond := Eval vm_compute in snd (fst bw2c_A_x).
Lemma bw2c_A_eq : bw2c_A_x = (bw2c_A_ss, bw2c_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw2c_A_pc : s_pc bw2c_A_ss = 1034160.
Proof. reflexivity. Qed.
Lemma bw2c_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  scs_denot bsegs m (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2c_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24. unfold bw2c_E, bw2c_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma bw2c_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  regs_ok (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2c_sr R -> know_ok bsegs (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m bw2c_A_knF ->
  exists R', regs_ok (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_regs bw2c_A_ss) R' /\ log_flat (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_log bw2c_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1034024) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1034160) (mem_denot (bw2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m (s_log bw2c_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw2c_A_eq HR HK
              (bw2c_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw2d_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21; Z_to_bv 64 w22; Z_to_bv 64 it].
Definition bw2d_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EVar 48); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (18%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (19%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EVar 36)].
Definition bw2d_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 0) 8 (EVar 47); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 32 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (EVar 38); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (EVar 39); KRange (EVar 38) 1 7; KRange (EVar 39) 1 7].
Definition bw2d_A_dirs : list bool := [true; true].
Definition bw2d_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1034160] (SCR bw2d_A_dirs [] []) 1034024 bw2d_sr bw2d_kn 50.
Definition bw2d_A_x := sym_exec bsegs 200 true [1034160] (SCR bw2d_A_dirs [] []) (SS 1034024 bw2d_sr [] bw2d_A_knF 50) [].
Definition bw2d_A_ss : sym_state := Eval vm_compute in fst (fst bw2d_A_x).
Definition bw2d_A_scs : list sidecond := Eval vm_compute in snd (fst bw2d_A_x).
Lemma bw2d_A_eq : bw2d_A_x = (bw2d_A_ss, bw2d_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw2d_A_pc : s_pc bw2d_A_ss = 1034160.
Proof. reflexivity. Qed.
Lemma bw2d_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  scs_denot bsegs m (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2d_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25. unfold bw2d_E, bw2d_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma bw2d_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 32) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  regs_ok (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) bw2d_sr R -> know_ok bsegs (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m bw2d_A_knF ->
  exists R', regs_ok (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_regs bw2d_A_ss) R' /\ log_flat (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) (s_log bw2d_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1034024) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1034160) (mem_denot (bw2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it) m (s_log bw2d_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw2d_A_eq HR HK
              (bw2d_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bw3_E (R : bvmap 5 word) (v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 e; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21; Z_to_bv 64 w22; Z_to_bv 64 it].
Definition bw3_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EVar 48); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (10%bv, EVar 34); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880)].
Definition bw3_kn : list kentry := [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 0) 8 (EVar 47); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KDisj (SA (EVar 32) 8) (ELit 8) (SA (EVar 33) 0) (ELit 64); KRange (EVar 34) 5 (2 ^ 64 - 1); KAlign (EVar 34) 4].
Definition bw3_A_dirs : list bool := [].
Definition bw3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1034160] (SCR bw3_A_dirs [] []) 1034084 bw3_sr bw3_kn 50.
Definition bw3_A_x := sym_exec bsegs 200 true [1034160] (SCR bw3_A_dirs [] []) (SS 1034084 bw3_sr [] bw3_A_knF 50) [].
Definition bw3_A_ss : sym_state := Eval vm_compute in fst (fst bw3_A_x).
Definition bw3_A_scs : list sidecond := Eval vm_compute in snd (fst bw3_A_x).
Lemma bw3_A_eq : bw3_A_x = (bw3_A_ss, bw3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bw3_A_pc : s_pc bw3_A_ss = 1034160.
Proof. reflexivity. Qed.
Lemma bw3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (4 < e < 2 ^ 64) -> (e mod 4 = 0) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) ->
  scs_denot bsegs m (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) bw3_A_scs.
Proof.
  intros R m v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold bw3_E, bw3_A_scs. split_scs.
Qed.
Lemma bw3_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (4 < e < 2 ^ 64) -> (e mod 4 = 0) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (0 <= w22 < 2 ^ 64) -> (0 <= it < 2 ^ 64) ->
  regs_ok (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) bw3_sr R -> know_ok bsegs (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) m bw3_A_knF ->
  exists R', regs_ok (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) (s_regs bw3_A_ss) R' /\ log_flat (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) (s_log bw3_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1034084) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1034160) (mem_denot (bw3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it) m (s_log bw3_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bw3_A_eq HR HK
              (bw3_A_sc R m v sp1 e w1 w8 w9 w18 w19 w20 w21 w22 it H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.


Definition BW_FRET : Z := 0xfc728.
Definition BW_SRET : Z := 0xfc764.
Definition BW_RET  : Z := 0xfc7b0.

Definition BSAVED : list reg := [22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition BK1 : list reg := [3; 4; 23; 24; 25; 26; 27]%bv.

Ltac bw_frame E Hlf :=
  first
  [ lazymatch goal with |- munch _ ?m0 (mem_denot _ _ _) =>
      let MU := fresh "MU" in
      pose proof (munch_mem_denot_sb [(-64, 0)] (EVar 34) E m0 _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
      eapply v4_munch_eqW; [exact MU | cbn [map fst snd]; evs; rewrite u64_of_Z by lia; repeat f_equal; lia] end
  | lazymatch goal with |- rw_cells _ (mem_denot _ _ ?lg) _ _ =>
      change lg with (v4_c8log (EVar 34) (-64) [EVar 22; EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1]);
      eapply rw_cells_mem_eq_list;
      [ apply v4_rw_cells_c8log;
        [ exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia
        | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; eapply wr_at_of_stk_win; [eassumption | lia | lia] ]
      | reflexivity ] end ].

Ltac bw_fin2 E Hlf :=
  first
  [ lazymatch goal with |- munch _ _ (mem_denot _ _ _) =>
      apply munch_mem_denot; [exact Hlf|];
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_mul, ?w_add by lia;
                                  rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]);
      apply Forall_nil end
  | lazymatch goal with |- rw_cells _ (mem_denot _ ?m0 [?e1; ?e2]) (?v + 8) _ =>
      change [e1; e2] with ([] ++ e1 :: [e2]);
      eapply rw_cells_mem_denot_w;
      [ exact Hlf | apply Forall_nil | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite u64_of_Z by lia; lia
      | eassumption | reflexivity | exact I | evs; unfold wz; rewrite ?w_mul, ?w_add by lia; reflexivity ] end
  | lazymatch goal with |- rw_cells _ (mem_denot _ ?m0 [?e1; ?e2]) _ _ =>
      change [e1; e2] with ([e1] ++ e2 :: []);
      eapply rw_cells_mem_denot_w;
      [ exact Hlf
      | apply Forall_cons; [|apply Forall_nil]; cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; unfold wz;
        rewrite ?w_mul, ?w_add by lia; rewrite !u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_mul, ?w_add by lia; rewrite u64_of_Z by lia; lia
      | eassumption | reflexivity | exact I | evs; rewrite ?le4_ext by lia; reflexivity ] end ].

Lemma bw_wrange : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. exact (bv_unsigned_in_range _ w). Qed.

Ltac bw_kfr :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA ?bs ?off) 8 ?e) =>
      match goal with HC : rw_cells _ M ?A ?cs |- _ =>
        let k := eval vm_compute in (Z.to_nat off) in
        eapply (kword_of_rw_cells asegs E M A cs k _ (SA bs off) e 8 HC);
        [ cbn; reflexivity | reflexivity | lia | rw_addrB | lia | lia
        | cbn [cbytes]; evs; rewrite Z_to_bv_bv_unsigned; reflexivity ]
      end
  end.

Ltac bw_knowF := change bsegs with asegs; kn_eval; unfold know_ok; repeat (apply Forall_cons; [first [kentryB | bw_kfr] |]); apply Forall_nil.

Ltac bw_wreg := evs; apply Z_to_bv_bv_unsigned.

Definition bw_P1F : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (it src spz v b len cap lo : Z),
    getr R 10 = wz it -> getr R 11 = wz src -> getr R 2 = wz spz ->
    ACONST m -> fldA m it 8 v -> gz m it 8 ->
    fldA m v 8 b -> fldA m (v + 8) 8 (b + 4 * len) -> fldA m (v + 16) 8 (b + 4 * cap) -> gz m v 24 ->
    stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    7241728 <= it -> it + 8 <= 2 ^ 47 -> it mod 8 = 0 -> (it + 8 <= spz - 64 \/ spz <= it) ->
    7241728 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 -> (v + 24 <= spz - 64 \/ spz <= v) ->
    16 <= b -> b + 4 * cap < 2 ^ 47 -> 0 <= len -> len < cap -> cap <= 2 ^ 24 ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz BIW32_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 64) (map (fun r => C8 (getr R r)) BSAVED)
      /\ getr R' 1 = wz BW_FRET /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz it /\ getr R' 9 = wz (v + 8)
      /\ getr R' 10 = wz b /\ getr R' 11 = wz (b + 4 * cap) /\ getr R' 12 = wz (b + 4 * len) /\ getr R' 13 = wz (b + 4 * len + 4)
      /\ getr R' 18 = wz (b + 4 * len + 4) /\ getr R' 19 = wz (b + 4 * len) /\ getr R' 20 = wz (sh (v + 8))
      /\ getr R' 21 = wz ASHADOW_BASE /\ getr R' 22 = wz src
      /\ (forall r, In r BK1 -> getr R' r = getr R r).

Definition bw_P1S : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (it src spz v b len cap lo : Z),
    getr R 10 = wz it -> getr R 11 = wz src -> getr R 2 = wz spz ->
    ACONST m -> fldA m it 8 v -> gz m it 8 ->
    fldA m v 8 b -> fldA m (v + 8) 8 (b + 4 * len) -> fldA m (v + 16) 8 (b + 4 * cap) -> gz m v 24 ->
    stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    7241728 <= it -> it + 8 <= 2 ^ 47 -> it mod 8 = 0 -> (it + 8 <= spz - 64 \/ spz <= it) ->
    7241728 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 -> (v + 24 <= spz - 64 \/ spz <= v) ->
    0 <= b -> b + 4 * cap < 2 ^ 47 -> len = cap -> 0 <= cap <= 2 ^ 24 ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz BIW32_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz (v4_entry V32_SLOW_RREF)) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 64) (map (fun r => C8 (getr R r)) BSAVED)
      /\ getr R' 1 = wz BW_SRET /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz it /\ getr R' 9 = wz (v + 8)
      /\ getr R' 10 = wz v /\ getr R' 11 = wz src /\ getr R' 20 = wz (sh (v + 8)) /\ getr R' 21 = wz ASHADOW_BASE
      /\ (forall r, In r BK1 -> getr R' r = getr R r).

Lemma bw_P1F_ok : bw_P1F.
Proof.
  intros R F fc m it src spz v b len cap lo H10 H11 H2 HAC Hit Hgi Hb He Hc HGZ HST Hlo Hs1 Hs2 Hi1 Hi2 Hi8 Hid
    Hv1 Hv2 Hv8 Hvd Hb16 Hbc Hl0 Hlc Hc24.
  set (fx := PropExec.mkFP F fc).
  stash_disjB.
  assert (HR : regs_ok (bw1f_E R it src spz v b len cap) bw1f_sr R) by (unfold bw1f_E, bw1f_sr; rw_seedB).
  assert (HK : know_ok bsegs (bw1f_E R it src spz v b len cap) m bw1f_F_knF) by (unfold bw1f_E; knowB).
  destruct (bw1f_F_run fx R m (seg_rom asegs) it src spz v b len cap ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold bw1f_F_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := bw1f_E R it src spz v b len cap) in *. unfold bw1f_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [bw_frame Ev Hlf|].
  split; [apply rw_wmono|].
  split; [bw_frame Ev Hlf|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  keptB HR HR' BK1.
Qed.

Lemma bw_P1S_ok : bw_P1S.
Proof.
  intros R F fc m it src spz v b len cap lo H10 H11 H2 HAC Hit Hgi Hb He Hc HGZ HST Hlo Hs1 Hs2 Hi1 Hi2 Hi8 Hid
    Hv1 Hv2 Hv8 Hvd Hb0 Hbc Hlc Hc24.
  set (fx := PropExec.mkFP F fc).
  stash_disjB.
  assert (HR : regs_ok (bw1s_E R it src spz v b len cap) bw1s_sr R) by (unfold bw1s_E, bw1s_sr; rw_seedB).
  assert (HK : know_ok bsegs (bw1s_E R it src spz v b len cap) m bw1s_S_knF) by (unfold bw1s_E; knowB).
  destruct (bw1s_S_run fx R m (seg_rom asegs) it src spz v b len cap ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold bw1s_S_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := bw1s_E R it src spz v b len cap) in *. unfold bw1s_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [bw_frame Ev Hlf|].
  split; [apply rw_wmono|].
  split; [bw_frame Ev Hlf|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' BK1.
Qed.

Definition BK2 : list reg := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition bw_P2 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (it v sp1 b len src x k j : Z) (x22 x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 2 = wz sp1 -> getr R 8 = wz it -> getr R 9 = wz (v + 8) -> getr R 18 = wz (b + 4 * len + 4) -> getr R 19 = wz (b + 4 * len)
    -> getr R 20 = wz (sh (v + 8)) -> getr R 21 = wz ASHADOW_BASE -> getr R 22 = wz src ->
    rw_cells asegs m sp1 (map (fun w => C8 w) [x22; x21; x20; x19; x18; x9; x8; x1]) ->
    fldA m src 4 x -> LbB_Kit.shk m src k -> (k = 0 \/ src mod 8 + 4 <= k < 8) ->
    LbB_Kit.shk m (b + 4 * len) j -> (j = 0 \/ (b + 4 * len) mod 8 + 4 <= j < 8) ->
    LbB_Kit.shk m (v + 8) 0 -> wr_at asegs m (b + 4 * len) 4 -> wr_at asegs m (v + 8) 8 ->
    2 ^ 45 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> 7241728 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= sp1 \/ sp1 + 64 <= v) ->
    16 <= b -> b mod 4 = 0 -> b + 4 * len + 4 <= sp1 -> 0 <= len <= 2 ^ 24 -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) ->
    b + 4 * len + 4 <= 2147446784 \/ 17594333495296 <= b ->
    0 <= src -> src + 4 <= 2 ^ 47 -> src mod 4 = 0 -> 0 <= x < 2 ^ 32 -> 0 <= it < 2 ^ 64 ->
    exists R' M2,
      CatSim.msteps asegs (MS R F (wz BW_FRET) fc None m (seg_rom asegs)) (MS R' F (wz BW_RET) fc None M2 (seg_rom asegs))
      /\ munch [(v + 8, v + 16); (b + 4 * len, b + 4 * len + 4)] m M2 /\ wmono asegs m M2
      /\ rw_cells asegs M2 (v + 8) [C8 (wz (b + 4 * len + 4))] /\ rw_cells asegs M2 (b + 4 * len) [C4 (wz x)]
      /\ getr R' 1 = x1 /\ getr R' 2 = wz (sp1 + 64) /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 10 = wz it
      /\ getr R' 18 = x18 /\ getr R' 19 = x19 /\ getr R' 20 = x20 /\ getr R' 21 = x21 /\ getr R' 22 = x22
      /\ (forall r, In r BK2 -> getr R' r = getr R r).

Ltac bw_p2_close HR HR' Ev Hlf Hms :=
  unstashB; rw_exB Hms;
  split; [exact Hms|];
  split; [bw_fin2 Ev Hlf|];
  split; [apply rw_wmono|];
  split; [bw_fin2 Ev Hlf|];
  split; [bw_fin2 Ev Hlf|];
  split; [rrwB HR' (1%bv : reg); bw_wreg|];
  split; [rrwB HR' (2%bv : reg); regB|];
  split; [rrwB HR' (8%bv : reg); bw_wreg|];
  split; [rrwB HR' (9%bv : reg); bw_wreg|];
  split; [rrwB HR' (10%bv : reg); regB|];
  split; [rrwB HR' (18%bv : reg); bw_wreg|];
  split; [rrwB HR' (19%bv : reg); bw_wreg|];
  split; [rrwB HR' (20%bv : reg); bw_wreg|];
  split; [rrwB HR' (21%bv : reg); bw_wreg|];
  split; [rrwB HR' (22%bv : reg); bw_wreg|];
  keptB HR HR' BK2.

Lemma bw_P2_ok : bw_P2.
Proof.
  intros R F fc m it v sp1 b len src x k j x22 x21 x20 x19 x18 x9 x8 x1 H2 H8 H9 H18 H19 H20 H21 H22 HFR HX HSK Hk HSJ Hj HS8 HWE HW8
    Hs1 Hs2 Hv1 Hv2 Hvd Hb16 Hb4 Hbs Hlen Hbv Hband Hsr0 Hsr1 Hsr4 Hx Hit.
  set (fx := PropExec.mkFP F fc).
  pose proof (bw_wrange x1) as B1. pose proof (bw_wrange x8) as B8. pose proof (bw_wrange x9) as B9.
  pose proof (bw_wrange x18) as B18. pose proof (bw_wrange x19) as B19. pose proof (bw_wrange x20) as B20.
  pose proof (bw_wrange x21) as B21. pose proof (bw_wrange x22) as B22.
  stash_disjB.
  destruct Hk as [Hk | Hk]; destruct Hj as [Hj | Hj].
  - subst k j.
    assert (HR : regs_ok (bw2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) bw2a_sr R)
      by (unfold bw2a_E, bw2a_sr; rw_seedB).
    assert (HK : know_ok bsegs (bw2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) m bw2a_A_knF)
      by (unfold bw2a_E; bw_knowF).
    destruct (bw2a_A_run fx R m (seg_rom asegs) v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
      as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold bw2a_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := bw2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) in *. unfold bw2a_E in Ev.
    bw_p2_close HR HR' Ev Hlf Hms.
  - subst k.
    assert (HR : regs_ok (bw2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) bw2c_sr R)
      by (unfold bw2c_E, bw2c_sr; rw_seedB).
    assert (HK : know_ok bsegs (bw2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) m bw2c_A_knF)
      by (unfold bw2c_E; bw_knowF).
    destruct (bw2c_A_run fx R m (seg_rom asegs) v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
      as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold bw2c_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := bw2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) in *. unfold bw2c_E in Ev.
    bw_p2_close HR HR' Ev Hlf Hms.
  - subst j.
    assert (HR : regs_ok (bw2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) bw2b_sr R)
      by (unfold bw2b_E, bw2b_sr; rw_seedB).
    assert (HK : know_ok bsegs (bw2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) m bw2b_A_knF)
      by (unfold bw2b_E; bw_knowF).
    destruct (bw2b_A_run fx R m (seg_rom asegs) v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
      as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold bw2b_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := bw2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) in *. unfold bw2b_E in Ev.
    bw_p2_close HR HR' Ev Hlf Hms.
  - idtac.
    assert (HR : regs_ok (bw2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) bw2d_sr R)
      by (unfold bw2d_E, bw2d_sr; rw_seedB).
    assert (HK : know_ok bsegs (bw2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) m bw2d_A_knF)
      by (unfold bw2d_E; bw_knowF).
    destruct (bw2d_A_run fx R m (seg_rom asegs) v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
      as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold bw2d_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := bw2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) in *. unfold bw2d_E in Ev.
    bw_p2_close HR HR' Ev Hlf Hms.
Qed.

Definition BK3 : list reg := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition bw_P3 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (it v sp1 e : Z) (x22 x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 2 = wz sp1 -> getr R 8 = wz it -> getr R 9 = wz (v + 8) -> getr R 10 = wz e -> getr R 20 = wz (sh (v + 8))
    -> getr R 21 = wz ASHADOW_BASE ->
    rw_cells asegs m sp1 (map (fun w => C8 w) [x22; x21; x20; x19; x18; x9; x8; x1]) ->
    LbB_Kit.shk m (v + 8) 0 -> wr_at asegs m (v + 8) 8 ->
    2 ^ 45 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> 7241728 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= sp1 \/ sp1 + 64 <= v) ->
    4 < e < 2 ^ 64 -> e mod 4 = 0 -> 0 <= it < 2 ^ 64 ->
    exists R' M3,
      CatSim.msteps asegs (MS R F (wz BW_SRET) fc None m (seg_rom asegs)) (MS R' F (wz BW_RET) fc None M3 (seg_rom asegs))
      /\ munch [(v + 8, v + 16)] m M3 /\ wmono asegs m M3 /\ rw_cells asegs M3 (v + 8) [C8 (wz e)]
      /\ getr R' 1 = x1 /\ getr R' 2 = wz (sp1 + 64) /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 10 = wz it
      /\ getr R' 18 = x18 /\ getr R' 19 = x19 /\ getr R' 20 = x20 /\ getr R' 21 = x21 /\ getr R' 22 = x22
      /\ (forall r, In r BK3 -> getr R' r = getr R r).

Lemma bw_P3_ok : bw_P3.
Proof.
  intros R F fc m it v sp1 e x22 x21 x20 x19 x18 x9 x8 x1 H2 H8 H9 H10 H20 H21 HFR HS8 HW8 Hs1 Hs2 Hv1 Hv2 Hvd He He4 Hit.
  set (fx := PropExec.mkFP F fc).
  pose proof (bw_wrange x1) as B1. pose proof (bw_wrange x8) as B8. pose proof (bw_wrange x9) as B9.
  pose proof (bw_wrange x18) as B18. pose proof (bw_wrange x19) as B19. pose proof (bw_wrange x20) as B20.
  pose proof (bw_wrange x21) as B21. pose proof (bw_wrange x22) as B22.
  stash_disjB.
  assert (HR : regs_ok (bw3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) bw3_sr R) by (unfold bw3_E, bw3_sr; rw_seedB).
  assert (HK : know_ok bsegs (bw3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) m bw3_A_knF) by (unfold bw3_E; bw_knowF).
  destruct (bw3_A_run fx R m (seg_rom asegs) v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
    as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold bw3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := bw3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) (bv_unsigned x22) it) in *. unfold bw3_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0%nat]|].
  split; [apply rw_wmono|].
  split.
  { lazymatch goal with |- rw_cells _ (mem_denot _ ?m0 [?e1]) _ _ => change [e1] with ([] ++ e1 :: []) end.
    eapply rw_cells_mem_denot_w;
      [ exact Hlf | apply Forall_nil | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite u64_of_Z by lia; lia
      | eassumption | reflexivity | exact I | evs; reflexivity ]. }
  split; [rrwB HR' (1%bv : reg); bw_wreg|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); bw_wreg|].
  split; [rrwB HR' (9%bv : reg); bw_wreg|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); bw_wreg|].
  split; [rrwB HR' (19%bv : reg); bw_wreg|].
  split; [rrwB HR' (20%bv : reg); bw_wreg|].
  split; [rrwB HR' (21%bv : reg); bw_wreg|].
  split; [rrwB HR' (22%bv : reg); bw_wreg|].
  keptB HR HR' BK3.
Qed.


Lemma bw_fld_munch : forall W (m0 m' : mem) a k z, fldA m0 a k z -> munch W m0 m' -> disjoint_from W a (Z.of_nat k) ->
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m' a k z.
Proof.
  intros W m0 m' a k z HF MU D Ha Hk. unfold fldA in *.
  eapply fld_agree; [exact Ha | exact Hk | exact HF |].
  intros y Hy. hnf in Hy. apply MU. rewrite u64_of_Z by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma bw_mdef_munch : forall W (m0 m' : mem) a n, mdef m0 a n -> munch W m0 m' -> disjoint_from W a n ->
  0 <= a -> a + n <= 2 ^ 64 -> mdef m' a n.
Proof.
  intros W m0 m' a n HD MU D Ha Hn i Hi. rewrite MU; [apply HD; exact Hi|].
  rewrite u64_of_Z by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma bw_mdef_sub : forall (m0 : mem) a n d k, mdef m0 a n -> 0 <= d -> d + k <= n -> mdef m0 (a + d) k.
Proof. intros m0 a n d k HD Hd Hk i Hi. replace (a + d + i) with (a + (d + i)) by lia. apply HD. lia. Qed.

Lemma bw_mdef3 : forall (m0 : mem) a, mdef m0 a 8 -> mdef m0 (a + 8) 8 -> mdef m0 (a + 16) 8 -> mdef m0 a 24.
Proof.
  intros m0 a D0 D1 D2 i Hi.
  destruct (Z_lt_le_dec i 8) as [L0|L0]; [apply D0; lia|].
  destruct (Z_lt_le_dec i 16) as [L1|L1].
  - replace (a + i) with (a + 8 + (i - 8)) by lia. apply D1. lia.
  - replace (a + i) with (a + 16 + (i - 16)) by lia. apply D2. lia.
Qed.

Lemma bw_rw_cells_xpres {HCEIL : HeapCeil} : forall (H : asr) LB SP X (m0 m' : mem) A cs,
  xpres H LB SP X m0 m' -> rw_cells asegs m0 A cs -> xclient_range H LB SP X A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m' A cs.
Proof.
  intros H LB SP X m0 m' A cs XP [[WF BA] WR] XC.
  split; [split; [exact WF|] |].
  - eapply xpres_bytes_at; [exact XP | exact BA |]. rewrite cells_bytes_length by exact WF. exact XC.
  - eapply xpres_wr_at; [exact XP | exact WR | exact XC].
Qed.

Lemma bw_sh_lo : forall a, 0 <= a <= 2 ^ 47 -> sh a + 8 <= 2 ^ 45.
Proof. intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

Section BiW32P.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HV4R : v4slow_stmt H V32_SLOW_RREF.

Section BW.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (it v b cap src x : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SP16 : spz mod 16 = 0.
  Hypothesis SPH : spz <= 2 ^ 47.
  Hypothesis ITC : fldA m it 8 v.
  Hypothesis IT8 : it mod 8 = 0.
  Hypothesis ITAD : addressable m it 8.
  Hypothesis ITAP : aapp it 8.
  Hypothesis VEC : vec32A LB m v b xs cap.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis VBAND : (7241728 <= v /\ v + 24 <= 2147446784) \/ (17594333495296 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LB m.
  Hypothesis OLD : v4_oldblk LB b cap pid.
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs)).
  Hypothesis CAPB : 4 * cap <= 2 ^ 26.
  Hypothesis GROW : Zlen xs = cap -> 4 * v4_newcap cap <= 2 ^ 26.
  Hypothesis SRC : src4_keep_x H LB spz (if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))]) m src x.
  Hypothesis XR : 0 <= x < 2 ^ 32.
  Hypothesis SRCR : src mod 4 = 0 /\ 0 <= src /\ src + 4 <= 2 ^ 47.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis SLOWOK : Zlen xs = cap -> as_alloc_ok H s LB (4 * v4_newcap cap)
                      /\ as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra V32_SLOW_RREF].
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - BIW32_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.

  Let Q := biw32_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF it v b cap x xs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma bw_spz_sp : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma bw_num : 140735332483072 <= aceil /\ aceil <= lo /\ lo + 8384 <= spz /\ spz <= 2 ^ 47
                 /\ 7241728 <= it /\ it + 8 <= aceil.
  Proof.
    pose proof aceil_facts as ((A1 & A2) & _ & _). destruct LOR as [L1 L2].
    unfold BIW32_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in L2.
    pose proof (aapp_bounds _ _ ITAP ltac:(lia)) as (I1 & I2 & _). unfold AIMG_TOP in I1. lia.
  Qed.

  Lemma bw_vfacts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 4 * Zlen xs) /\ fldA m (v + 16) 8 (b + 4 * cap)
    /\ (forall i, 0 <= i < Zlen xs -> 0 <= Znth i xs < 2 ^ 32 /\ fldA m (b + 4 * i) 4 (Znth i xs))
    /\ 0 <= Zlen xs <= cap /\ ((b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap)))
    /\ (b <> 0 -> v + 24 <= b \/ b + 4 * cap <= v) /\ mdef m v 24.
  Proof.
    pose proof VEC as V. unfold vec32A, vec32 in V.
    destruct V as (Hv0 & Hv24 & HD & Hlen & Hb & F0 & F1 & F2 & FE).
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact FE|]. split; [exact Hlen|].
    split.
    - destruct OLD as [[E1 E2] | [C0 IN]]; [left; split; assumption | right].
      split; [exact C0|]. split; [exact IN|].
      pose proof (ah_blocks H HH _ _ _ (pid, b, 4 * cap) RH0 IN) as AB.
      unfold blk_addr, blk_size in AB. cbn [fst snd] in AB. exact AB.
    - split; [|exact HD]. intros Hb0. destruct Hb as [[E1 E2] | (_ & _ & _ & _ & _ & D)]; [lia | exact D].
  Qed.

  Lemma bw_cells64 : Z.of_nat (cells_size FRAME) = 64.
  Proof. reflexivity. Qed.

  Lemma bw_after_frame : forall m1, munch [(spz - 64, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (spz - 64) FRAME ->
    as_RHEAP H s LB m1 /\ as_RFS H LF m1 /\ ACONST m1 /\ as_rauxv_ok H m1 B /\ stk asegs m1 lo spz /\ stack0 m1 lo shi
    /\ xpres H LB spz [] m m1 /\ lb_own LB m1 /\ vec32A LB m1 v b xs cap /\ addressable m1 v 24 /\ wr_at asegs m1 v 24
    /\ (0 < cap -> SHAD m1 b (cc_gen (4 * cap) (4 * Zlen xs))).
  Proof.
    intros m1 MU WM FR.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    pose proof bw_vfacts as (_ & _ & _ & _ & Hlen & Hb & _ & _).
    destruct (stack_window_ok H LB LF (spz - 64) spz ltac:(lia) ltac:(lia)) as (W1 & W2 & W3).
    destruct (client_frame H HH s LB LF B [(spz - 64, spz)] m m1 RH0 RF0 AC0 RA0 MU WM
                ltac:(apply Forall_cons; [exact W1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact W2 | apply Forall_nil]) ltac:(apply Forall_cons; [exact W3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    split; [exact RH1|]. split; [exact RF1|]. split; [exact AC1|]. split; [exact RA1|].
    split.
    { destruct (stk_split asegs m lo (spz - 64) spz ST0 ltac:(lia)) as [SA _].
      apply (stk_merge asegs m1 lo (spz - 64) spz); [| | lia].
      - eapply stk_transport_disjoint; [exact SA | exact MU | exact WM | cbn; lia].
      - pose proof (stk_of_rw_cells asegs m1 (spz - 64) FRAME FR) as SB. rewrite bw_cells64 in SB.
        replace (spz - 64 + 64) with spz in SB by lia. exact SB. }
    split.
    { eapply stack0_transport; [exact S00 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    split.
    { eapply (xpres_of_munch H s LB spz [] _ m m m1); [exact HH | exact RH0 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
    split; [exact (lb_own_wmono LB m m1 OWN WM)|].
    split.
    { eapply vec32A_munch; [exact VEC | exact MU | |].
      - destruct OBJ as (_ & _ & _ & _ & _ & D). cbn [disjoint_from]. split; [lia | exact I].
      - destruct Hb as [[E1 E2] | (C0 & IN & AB)]; cbn [disjoint_from]; (split; [|exact I]).
        + lia.
        + destruct AB as (B0 & B16 & Bn & BI & BC & BF & BAPP). lia. }
    split.
    { eapply addressable_transport; [exact ADV0 | exact MU | exact WM |].
      pose proof (bw_sh_lo v ltac:(destruct VBAND; lia)). cbn [disjoint_from]. rewrite v4_nsh24. split; [lia | exact I]. }
    split; [exact (wr_at_wmono m m1 v 24 VWR WM)|].
    intros C0.
    eapply SHAD_transport; [exact (OLDSH C0) | exact MU | exact WM |].
    destruct Hb as [[E1 E2] | (_ & IN & AB)]; [lia|].
    destruct AB as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    rewrite cc_gen_length by lia.
    pose proof (bw_sh_lo (b + 4 * cap) ltac:(lia)) as K.
    assert (sh b + nsh (4 * cap) <= sh (b + 4 * cap) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
    cbn [disjoint_from]. split; [lia | exact I].
  Qed.

  Lemma bw_end : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem)
                        (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (LB' : list block) (b' cap' : Z) (e3 : word),
    as_VIS H sk3 msF3 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 it) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 BW_RET) fc None m3 (seg_rom asegs) ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    mem_inv asegs m3 -> stk asegs m3 lo spz -> rw_cells asegs m3 (errno_addr tp) [C4 e3] -> as_rauxv_ok H m3 B ->
    vec32A LB' m3 v b' (xs ++ [x]) cap' -> as_RHEAP H sk3 LB' m3 ->
    SHAD m3 b' (cc_gen (4 * cap') (4 * (Zlen xs + 1))) -> addressable m3 v 24 -> wr_at asegs m3 v 24 -> lb_own LB' m3 ->
    ((Zlen xs < cap /\ b' = b /\ cap' = cap /\ LB' = LB
      /\ xpres H LB spz [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m m3 /\ as_AL H sk3 >= as_AL H s)
     \/ (Zlen xs = cap /\ cap' = v4_newcap cap
         /\ (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
         /\ xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m3
         /\ as_AL H sk3 >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)))) ->
    as_RFS H LF m3 -> ACONST m3 -> stack0 m3 lo shi ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LB' b' cap' e3 VIS KR MP MI ST ERR RA VC RH SH AD WR OW
      DJ RF AC S0.
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 it) a1 a2 a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m3 (seg_rom asegs));
      [exact KR | exact VIS | |].
    { step. apply evt_done. reflexivity. }
    intros msF' mo' KR' MP' HP. cbv beta in HP.
    unfold Q, biw32_post.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m3, e3, sk3, LB', b', cap'.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    split; [exact HP|]. split; [exact KR'|]. split; [eapply (ah_mpres_trans H HH); [exact MP | exact MP']|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|].
    split; [exact VC|]. split; [exact RH|]. split; [exact SH|]. split; [exact AD|]. split; [exact WR|].
    split; [exact OW|]. split; [exact DJ|]. split; [exact RF|]. split; [exact AC|]. exact S0.
  Qed.



  Lemma bw_b16 : forall a, a mod 16 = 0 -> 0 < a -> 16 <= a.
  Proof. intros a Ha Hp. Z.div_mod_to_equations. lia. Qed.

  Lemma bw_m4of16 : forall a, a mod 16 = 0 -> a mod 4 = 0.
  Proof. intros a Ha. Z.div_mod_to_equations. lia. Qed.

  Lemma bw_mod4 : forall a k, a mod 16 = 0 -> (a + 4 * k) mod 4 = 0.
  Proof. intros a k Ha. Z.div_mod_to_equations. lia. Qed.

  Lemma bw_errno_val : bv_unsigned tp + -164 = 0x6c57b4.
  Proof. rewrite TPV. vm_compute. reflexivity. Qed.

  Lemma bw_tls_val : ATLS_PRIV_HI = 0x6c5888.
  Proof. vm_compute. reflexivity. Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma bw_obj64 : obj_win H LB LF (spz - 64) lo v 24.
  Proof.
    pose proof OBJ as O. unfold obj_win in O |- *. destruct O as (C1 & C2 & C3 & C4 & C5 & C6).
    unfold aclient_range in C1, C2 |- *.
    split; [destruct C1 as [C1|C1]; [left; lia | right; exact C1]|].
    split; [destruct C2 as [C2|C2]; [left; lia | right; exact C2]|].
    split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. lia.
  Qed.

  Lemma bw_wv : forall l h, v <= l -> h <= v + 24 ->
    aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)
    /\ disjoint_from [(l, h)] (errno_addr tp) 4.
  Proof.
    intros l h L1 L2. pose proof OBJ as O. destruct O as (_ & _ & C3 & C4 & C5 & _).
    split; [eapply aclient_write_ok_sub; [exact C3 | lia | lia]|].
    split; [eapply afs_write_ok_sub; [exact C4 | lia | lia]|].
    split; [eapply aconst_ok_sub; [exact C5 | lia | lia]|].
    split.
    - unfold stack0_ok, sh. cbn [fst snd]. pose proof aceil_facts as ((A1 & A2) & _ & _).
      assert (0 <= aceil / 8) by (apply Z.div_pos; lia).
      rewrite ASHADOW_BASE_val. unfold AHI_LO. destruct VBAND; lia.
    - rewrite bw_errno_val. cbn [disjoint_from]. split; [destruct VBAND; lia | exact I].
  Qed.

  Lemma bw_wb : forall l h, 0 < cap -> b <= l -> h <= b + 4 * cap ->
    aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)
    /\ disjoint_from [(l, h)] (errno_addr tp) 4.
  Proof.
    intros l h C0 L1 L2.
    pose proof bw_vfacts as (_ & _ & _ & _ & _ & Hb & _ & _).
    destruct Hb as [[E1 E2] | (_ & IN & AB)]; [lia|].
    pose proof AB as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    split.
    { unfold aclient_write_ok. right; right; left. exists (pid, b, 4 * cap).
      unfold blk_addr, blk_size. cbn [fst snd]. split; [exact IN | lia]. }
    split.
    { unfold afs_write_ok. left. cbn [fst snd]. rewrite bw_tls_val. split; lia. }
    split; [eapply aconst_ok_app; [exact BAPP | lia | lia]|].
    split; [eapply stack0_ok_aapp; [exact BAPP | lia | lia]|].
    rewrite bw_errno_val. cbn [disjoint_from]. split; [lia | exact I].
  Qed.

  Lemma bw_wsh : forall l h, 0 < cap -> sh b <= l -> h <= sh b + nsh (4 * cap) ->
    aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)
    /\ disjoint_from [(l, h)] (errno_addr tp) 4.
  Proof.
    intros l h C0 L1 L2.
    pose proof bw_vfacts as (_ & _ & _ & _ & _ & Hb & _ & _).
    destruct Hb as [[E1 E2] | (_ & IN & AB)]; [lia|].
    pose proof AB as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    pose proof aceil_facts as ((A1 & A2) & A3 & _).
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SH1.
    assert (SH0 : ASHADOW_BASE <= sh b) by (unfold sh; assert (0 <= b / 8) by (apply Z.div_pos; lia); lia).
    rewrite ASHADOW_BASE_val in SH0.
    assert (SHA : sh b + nsh (4 * cap) <= sh aceil) by (clear - B16 B0 Bn BC A3; unfold sh, nsh; Z.div_mod_to_equations; lia).
    split.
    { unfold aclient_write_ok. right; right; right; left. exists (pid, b, 4 * cap).
      unfold blk_addr, blk_size. cbn [fst snd]. split; [exact IN | lia]. }
    split.
    { unfold afs_write_ok. left. cbn [fst snd]. rewrite bw_tls_val.
      pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
      split; [| right; lia].
      destruct FS4 as [[F1 F2]|[F1 F2]]; unfold AHI_LO, ALOWSH_LO in *; lia. }
    split.
    { eapply aconst_ok_high; [| right; left; lia].
      apply Z.le_trans with (sh b); [| exact L1]. unfold sh. apply Zplus_le_compat_l. apply Z.div_le_mono; [lia|].
      first [exact BI | unfold AIMG_TOP in *; lia]. }
    split; [unfold stack0_ok; cbn [fst snd]; right; lia|].
    rewrite bw_errno_val. cbn [disjoint_from]. split; [lia | exact I].
  Qed.

  Lemma bw_wstk : forall l h, aceil <= l -> h <= spz ->
    aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)
    /\ disjoint_from [(l, h)] (errno_addr tp) 4.
  Proof.
    intros l h L1 L2.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    destruct (stack_window_ok H LB LF l h L1 FS2) as (W1 & W2 & W3).
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [unfold stack0_ok; left; cbn [fst]; unfold AHI_LO; lia|].
    rewrite bw_errno_val. cbn [disjoint_from]. split; [lia | exact I].
  Qed.

  Lemma bw_awo_new : forall LB', (b = 0 -> forall bb, In bb LB -> In bb LB') ->
    (b <> 0 -> forall bb, In bb LB -> blk_id bb <> pid -> In bb LB') ->
    aclient_write_ok H LB' (v + 8, v + 16).
  Proof.
    intros LB' K0 K1.
    pose proof bw_vfacts as (_ & _ & _ & _ & Hlen & Hb & Hvb & _).
    pose proof OBJ as O. destruct O as (_ & _ & AW & _ & _ & _).
    unfold aclient_write_ok in AW |- *. cbn [fst snd] in AW |- *.
    destruct AW as [A|[A|[(bb & IN & A1 & A2)|[(bb & IN & A1 & A2)|A]]]].
    - left. lia.
    - right; left. unfold aimg_client_w in A |- *. lia.
    - right; right; left. exists bb. split; [|lia].
      destruct (Z.eq_dec b 0) as [E|E]; [exact (K0 E bb IN)|].
      apply (K1 E bb IN). intros Hid.
      destruct Hb as [[E1 E2]|(C0 & INb & AB)]; [lia|].
      destruct bb as [[p A0] n]. unfold blk_id in Hid. cbn [fst] in Hid. subst p.
      pose proof (nodup_id_same LB pid b (4 * cap) A0 n (ah_nodup H HH _ _ _ RH0) INb IN) as EQ.
      assert (EA : A0 = b) by congruence. assert (EN : n = 4 * cap) by congruence. subst A0 n.
      unfold blk_addr, blk_size in A1, A2. cbn [fst snd] in A1, A2.
      destruct (Hvb E); lia.
    - exfalso. pose proof (ah_blocks H HH _ _ _ bb RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
      pose proof aceil_facts as ((AC1 & AC2) & _ & _).
      pose proof (v4_app_sh v 24 (blk_addr bb) (blk_size bb) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(destruct VBAND; [left|right]; lia)) as D.
      lia.
    - right; right; right; right.
      destruct A as [A|[A|A]]; [left | right; left | right; right]; lia.
  Qed.

  Lemma bw_end2 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word)
                         (LB' : list block) (b' cap' : Z) (e3 : word),
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 BW_RET) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = ra -> getr R3 2 = sp -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 8 = s0 -> getr R3 9 = s1 ->
    getr R3 10 = Z_to_bv 64 it ->
    getr R3 18 = s2 -> getr R3 19 = s3 -> getr R3 20 = s4 -> getr R3 21 = s5 -> getr R3 22 = s6 -> getr R3 23 = s7 ->
    getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    mem_inv asegs m3 -> stk asegs m3 lo spz -> rw_cells asegs m3 (errno_addr tp) [C4 e3] -> as_rauxv_ok H m3 B ->
    vec32A LB' m3 v b' (xs ++ [x]) cap' -> as_RHEAP H sk3 LB' m3 ->
    SHAD m3 b' (cc_gen (4 * cap') (4 * (Zlen xs + 1))) -> addressable m3 v 24 -> wr_at asegs m3 v 24 -> lb_own LB' m3 ->
    ((Zlen xs < cap /\ b' = b /\ cap' = cap /\ LB' = LB
      /\ xpres H LB spz [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m m3 /\ as_AL H sk3 >= as_AL H s)
     \/ (Zlen xs = cap /\ cap' = v4_newcap cap
         /\ (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
         /\ xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m3
         /\ as_AL H sk3 >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)))) ->
    as_RFS H LF m3 -> ACONST m3 -> stack0 m3 lo shi ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 LB' b' cap' e3 VIS HF G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
    rewrite (rfull_eq R3 HF), G1, G2, G3, G4, G8, G9, G10, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27 in VIS.
    exact (bw_end msF3 mo3 sk3 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB' b' cap' e3 VIS).
  Qed.

  Lemma bw_f2 : forall (msF2 : machine_state) (mo2 : Model) (m2 : mem) (R2 : bvmap 5 word) (e2 : word),
    Zlen xs < cap ->
    as_VIS H s msF2 = MS R2 F (Z_to_bv 64 BW_FRET) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = wz (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = wz it -> getr R2 9 = wz (v + 8) ->
    getr R2 18 = wz (b + 4 * Zlen xs + 4) -> getr R2 19 = wz (b + 4 * Zlen xs) -> getr R2 20 = wz (sh (v + 8)) ->
    getr R2 21 = wz ASHADOW_BASE -> getr R2 22 = wz src ->
    getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H s (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    rw_cells asegs m2 (spz - 64) FRAME -> mem_inv asegs m2 -> stk asegs m2 lo spz ->
    rw_cells asegs m2 (errno_addr tp) [C4 e2] -> as_rauxv_ok H m2 B ->
    as_RHEAP H s LB m2 -> as_RFS H LF m2 -> ACONST m2 -> stack0 m2 lo shi -> lb_own LB m2 ->
    xpres H LB spz [(sh b, sh b + nsh (4 * cap))] m m2 -> vec32A LB m2 v b xs cap ->
    addressable m2 v 24 -> wr_at asegs m2 v 24 -> SHAD m2 b (cc_gen (4 * cap) (4 * Zlen xs + 4)) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 m2 R2 e2 LT VIS2 HF2 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR2 MP2
      FR2 MI2 ST2 ERR2 RA2 RH2 RF2 AC2 S02 OW2 XP2 VC2 AD2 WR2 SH2.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof bw_vfacts as (_ & _ & _ & _ & Hlen & Hb & Hvb & _).
    assert (C0 : 0 < cap) by lia.
    destruct Hb as [[E1 E2] | (_ & IN & AB)]; [lia|].
    pose proof AB as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    pose proof (bw_b16 b B16 B0) as B16'. pose proof (bw_m4of16 b B16) as B4.
    pose proof (Hvb ltac:(lia)) as VB.
    pose proof VC2 as V. unfold vec32A, vec32 in V. destruct V as (Hv0 & Hv24 & HD & _ & _ & F0 & F1 & F2 & FE).
    pose proof OBJ as O. destruct O as (_ & _ & _ & _ & _ & OD).
    pose proof SRCR as (SR4 & SR0 & SR47).
    assert (SRC' : src4_keep_x H LB spz [(sh b, sh b + nsh (4 * cap))] m src x).
    { assert (Eb : (b =? 0) = false) by (apply Z.eqb_neq; lia). pose proof SRC as S. rewrite Eb in S. exact S. }
    destruct (SRC' m2 AC2 MI2 XP2) as (FX & ACX).
    destruct (v4_src_shk m2 src ACX SR4 SR0) as (k & SK & Hk).
    destruct (vt_slot_shk m2 b cap (Zlen xs) SH2 B16 ltac:(lia) ltac:(lia) LT) as (j & SJ & Hj).
    assert (S8 : LbB_Kit.shk m2 (v + 8) 0).
    { exact (sh0_of_addressable m2 v 24 (v + 8) AD2 ltac:(change (8 * (24 / 8)) with 24; lia)). }
    assert (WB : wr_at asegs m2 (b + 4 * Zlen xs) 4).
    { pose proof (lb_own_In LB m2 (pid, b, 4 * cap) OW2 IN) as W. unfold blk_addr, blk_size in W. cbn [fst snd] in W.
      eapply vt_wr_sub; [exact W | lia | lia | lia]. }
    assert (W8 : wr_at asegs m2 (v + 8) 8) by (eapply vt_wr_sub; [exact WR2 | lia | lia | lia]).
    destruct (bw_P2_ok R2 F fc m2 it v (spz - 64) b (Zlen xs) src x k j s6 s5 s4 s3 s2 s1 s0 ra
                G2 G8 G9 G18 G19 G20 G21 G22 FR2 FX SK Hk SJ Hj S8 WB W8
                ltac:(lia) ltac:(lia) ltac:(destruct VBAND; lia) ltac:(lia) ltac:(lia)
                B16' B4 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(destruct (vt_band_of_aapp _ _ BAPP); lia)
                SR0 SR47 SR4 XR ltac:(lia))
      as (R3 & M3 & Hms & MU & WM & C8v & C4b & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & KK).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
    assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
    pose proof (bw_wv (v + 8) (v + 16) ltac:(lia) ltac:(lia)) as (WV1 & WV2 & WV3 & WV4 & WV5).
    pose proof (bw_wb (b + 4 * Zlen xs) (b + 4 * Zlen xs + 4) C0 ltac:(lia) ltac:(lia)) as (WB1 & WB2 & WB3 & WB4 & WB5).
    destruct (client_frame H HH s LB LF B _ m2 M3 RH2 RF2 AC2 RA2 MU WM
                ltac:(apply Forall_cons; [exact WV1|]; apply Forall_cons; [exact WB1 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact WV2|]; apply Forall_cons; [exact WB2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact WV3|]; apply Forall_cons; [exact WB3 | apply Forall_nil]))
      as (RH3 & RF3 & AC3 & RA3).
    assert (ERR3 : rw_cells asegs M3 (errno_addr tp) [C4 e2]).
    { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |].
      change (Z.of_nat (cells_size [C4 e2])) with 4.
      destruct WV5 as [WV5 _]. destruct WB5 as [WB5 _]. cbn [disjoint_from]. split; [exact WV5 | split; [exact WB5 | exact I]]. }
    assert (ST3 : stk asegs M3 lo spz) by (apply (stk_high_transport m2 M3 lo spz ST2 WM); unfold AIMG_TOP; lia).
    assert (S03 : stack0 M3 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU | exact WM |].
      apply Forall_cons; [exact WV4|]. apply Forall_cons; [exact WB4 | apply Forall_nil]. }
    assert (OW3 : lb_own LB M3) by exact (lb_own_wmono _ _ _ OW2 WM).
    assert (WR3 : wr_at asegs M3 v 24) by exact (wr_at_wmono _ _ _ _ WR2 WM).
    assert (BB : (0 <= b + 4 * Zlen xs /\ b + 4 * Zlen xs + 4 <= 0x7fff7000) \/ 0x10007fff8000 <= b + 4 * Zlen xs)
      by (destruct (vt_band_of_aapp _ _ BAPP); [left|right]; lia).
    assert (BV : (0 <= v + 8 /\ v + 8 + 8 <= 0x7fff7000) \/ 0x10007fff8000 <= v + 8)
      by (destruct VBAND; [left|right]; lia).
    assert (AD3 : addressable M3 v 24).
    { eapply addressable_transport; [exact AD2 | exact MU | exact WM |].
      pose proof (v4_app_sh (v + 8) 8 v 24 ltac:(lia) ltac:(lia) ltac:(lia) BV) as D1.
      pose proof (v4_app_sh (b + 4 * Zlen xs) 4 v 24 ltac:(lia) ltac:(lia) ltac:(lia) BB) as D2.
      cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
    assert (SH3 : SHAD M3 b (cc_gen (4 * cap) (4 * (Zlen xs + 1)))).
    { replace (4 * (Zlen xs + 1)) with (4 * Zlen xs + 4) by lia.
      eapply SHAD_transport; [exact SH2 | exact MU | exact WM |].
      rewrite cc_gen_length by lia.
      pose proof (v4_app_sh (v + 8) 8 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) BV) as D1.
      pose proof (v4_app_sh (b + 4 * Zlen xs) 4 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) BB) as D2.
      cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
    assert (XP3 : xpres H LB spz [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m M3).
    { apply (xpres_trans H LB spz _ m m2 M3).
      - eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hbb; exact Hbb |].
        intros a Ha. cbn [rin_ivs fst snd] in Ha |- *. destruct Ha as [Ha|Ha]; [right; right; left; exact Ha | destruct Ha].
      - eapply (xpres_of_munch H s LB spz _ _ m m2 M3); [exact HH | exact RH0 | exact MU | exact WM |].
        apply Forall_cons; [right; intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; left; lia|].
        apply Forall_cons; [right; intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; right; left; lia | apply Forall_nil]. }
    assert (VC3 : vec32A LB M3 v b (xs ++ [x]) cap).
    { pose proof (bw_mdef_sub m2 v 24 0 8 HD ltac:(lia) ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
      pose proof (bw_mdef_sub m2 v 24 16 8 HD ltac:(lia) ltac:(lia)) as D16.
      eapply (vec32A_push LB m2 M3 v b xs cap x VC2 LT).
      - apply bw_mdef3.
        + eapply bw_mdef_munch; [exact D0 | exact MU | cbn [disjoint_from]; split; [lia | split; [lia | exact I]] | lia | lia].
        + exact (mdef_of_rw_cells_hi _ _ _ C8v ltac:(unfold AIMG_TOP; destruct VBAND; lia)).
        + eapply bw_mdef_munch; [exact D16 | exact MU | cbn [disjoint_from]; split; [lia | split; [lia | exact I]] | lia | lia].
      - eapply bw_fld_munch; [exact F0 | exact MU | change (Z.of_nat 8) with 8; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]
                             | lia | change (Z.of_nat 8) with 8; lia].
      - replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia. exact (fld_of_rw_cells8 _ _ _ C8v ltac:(lia)).
      - eapply bw_fld_munch; [exact F2 | exact MU | change (Z.of_nat 8) with 8; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]
                             | lia | change (Z.of_nat 8) with 8; lia].
      - intros i Hi. destruct (FE i Hi) as [_ Fi].
        eapply bw_fld_munch; [exact Fi | exact MU | change (Z.of_nat 4) with 4; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]
                             | lia | change (Z.of_nat 4) with 4; lia].
      - exact (fld_of_rw_cells4 _ _ _ C4b ltac:(lia)).
      - exact XR. }
    eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
    intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
    eapply (bw_end2 msF3 mo3 s M3 R3 LB b cap e2 VIS3 HF3).
    - exact K1.
    - rewrite K2, bw_spz_sp. unfold wz. f_equal. lia.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
    - exact K22.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - exact MI3.
    - exact ST3.
    - exact ERR3.
    - exact RA3.
    - exact VC3.
    - exact RH3.
    - exact SH3.
    - exact AD3.
    - exact WR3.
    - exact OW3.
    - left. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact XP3 | lia].
    - exact RF3.
    - exact AC3.
    - exact S03.
  Qed.

  Lemma bw_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word)
                       (LB' : list block) (b' : Z) (e2 : word),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 BW_SRET) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = wz (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = wz it -> getr R2 9 = wz (v + 8) ->
    getr R2 10 = wz (b' + 4 * (cap + 1)) -> getr R2 20 = wz (sh (v + 8)) -> getr R2 21 = wz ASHADOW_BASE ->
    getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    Zlen xs = cap -> rw_cells asegs m2 (spz - 64) FRAME ->
    mem_inv asegs m2 -> stk asegs m2 lo spz -> rw_cells asegs m2 (errno_addr tp) [C4 e2] -> as_rauxv_ok H m2 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m2 ->
    (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * v4_newcap cap) /\ ablock_range H b' (4 * v4_newcap cap)) ->
    as_RHEAP H sk2 LB' m2 -> vec32A LB' m2 v b' (xs ++ [x]) (v4_newcap cap) ->
    SHAD m2 b' (cc_gen (4 * v4_newcap cap) (4 * (cap + 1))) -> addressable m2 v 24 -> wr_at asegs m2 v 24 -> lb_own LB' m2 ->
    as_RFS H LF m2 -> ACONST m2 -> stack0 m2 lo shi ->
    as_AL H sk2 >= as_AL H s - (as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap)) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 LB' b' e2 VIS2 HF2 G2 G3 G4 G8 G9 G10 G20 G21 G23 G24 G25 G26 G27 KR2 MP2 EQ FR2
      MI2 ST2 ERR2 RA2 XP2 NLB RH2 VC2 SH2 AD2 WR2 OW2 RF2 AC2 S02 AL2.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof bw_vfacts as (_ & _ & _ & _ & Hlen & Hb & Hvb & _).
    pose proof (v4_newcap_ge cap) as NC.
    destruct NLB as (pid' & ELB & ABR).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP).
    pose proof OBJ as O. destruct O as (_ & _ & _ & _ & _ & OD).
    assert (S8 : LbB_Kit.shk m2 (v + 8) 0).
    { exact (sh0_of_addressable m2 v 24 (v + 8) AD2 ltac:(change (8 * (24 / 8)) with 24; lia)). }
    assert (W8 : wr_at asegs m2 (v + 8) 8) by (eapply vt_wr_sub; [exact WR2 | lia | lia | lia]).
    destruct (bw_P3_ok R2 F fc m2 it v (spz - 64) (b' + 4 * (cap + 1)) s6 s5 s4 s3 s2 s1 s0 ra
                G2 G8 G9 G10 G20 G21 FR2 S8 W8 ltac:(lia) ltac:(lia) ltac:(destruct VBAND; lia) ltac:(lia) ltac:(lia)
                ltac:(pose proof (bw_b16 b' A16 A0); lia) (bw_mod4 b' (cap + 1) A16) ltac:(lia))
      as (R3 & M3 & Hms & MU & WM & C8v & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & KK).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
    assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
    pose proof (bw_wv (v + 8) (v + 16) ltac:(lia) ltac:(lia)) as (_ & WV2 & WV3 & WV4 & WV5).
    assert (WV1 : aclient_write_ok H LB' (v + 8, v + 16)).
    { apply bw_awo_new.
      - intros E0 bb Hbb. rewrite ELB. unfold v4_newLB. rewrite (proj2 (Z.eqb_eq b 0) E0). right. exact Hbb.
      - intros E0 bb Hbb Hid. rewrite ELB. unfold v4_newLB. rewrite (proj2 (Z.eqb_neq b 0) E0). right.
        exact (lb_remove_keep H HH pid LB bb (ah_nodup H HH _ _ _ RH0) Hbb Hid). }
    destruct (client_frame H HH sk2 LB' LF B _ m2 M3 RH2 RF2 AC2 RA2 MU WM
                ltac:(apply Forall_cons; [exact WV1 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact WV2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact WV3 | apply Forall_nil]))
      as (RH3 & RF3 & AC3 & RA3).
    assert (ERR3 : rw_cells asegs M3 (errno_addr tp) [C4 e2]).
    { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |].
      change (Z.of_nat (cells_size [C4 e2])) with 4. exact WV5. }
    assert (ST3 : stk asegs M3 lo spz) by (apply (stk_high_transport m2 M3 lo spz ST2 WM); unfold AIMG_TOP; lia).
    assert (S03 : stack0 M3 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU | exact WM |]. apply Forall_cons; [exact WV4 | apply Forall_nil]. }
    assert (OW3 : lb_own LB' M3) by exact (lb_own_wmono _ _ _ OW2 WM).
    assert (WR3 : wr_at asegs M3 v 24) by exact (wr_at_wmono _ _ _ _ WR2 WM).
    assert (BV : (0 <= v + 8 /\ v + 8 + 8 <= 0x7fff7000) \/ 0x10007fff8000 <= v + 8)
      by (destruct VBAND; [left|right]; lia).
    assert (AD3 : addressable M3 v 24).
    { eapply addressable_transport; [exact AD2 | exact MU | exact WM |].
      pose proof (v4_app_sh (v + 8) 8 v 24 ltac:(lia) ltac:(lia) ltac:(lia) BV) as D1.
      cbn [disjoint_from]. split; [lia | exact I]. }
    assert (SH3 : SHAD M3 b' (cc_gen (4 * v4_newcap cap) (4 * (Zlen xs + 1)))).
    { rewrite EQ. eapply SHAD_transport; [exact SH2 | exact MU | exact WM |].
      rewrite cc_gen_length by lia.
      pose proof (v4_app_sh (v + 8) 8 b' (4 * v4_newcap cap) ltac:(lia) ltac:(lia) ltac:(lia) BV) as D1.
      cbn [disjoint_from]. split; [lia | exact I]. }
    assert (VC3 : vec32A LB' M3 v b' (xs ++ [x]) (v4_newcap cap)).
    { eapply vec32A_set_end; [exact VC2 | unfold AIMG_TOP; destruct VBAND; lia | exact MU |].
      rewrite Zlen_app1, EQ. exact C8v. }
    assert (XP3 : xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m M3).
    { apply (xpres_trans H LB spz _ m m2 M3); [exact XP2|].
      eapply (xpres_of_munch H s LB spz _ _ m m2 M3); [exact HH | exact RH0 | exact MU | exact WM |].
      apply Forall_cons; [right; intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; left; lia | apply Forall_nil]. }
    eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
    intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
    eapply (bw_end2 msF3 mo3 sk2 M3 R3 LB' b' (v4_newcap cap) e2 VIS3 HF3).
    - exact K1.
    - rewrite K2, bw_spz_sp. unfold wz. f_equal. lia.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
    - exact K22.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - exact MI3.
    - exact ST3.
    - exact ERR3.
    - exact RA3.
    - exact VC3.
    - exact RH3.
    - exact SH3.
    - exact AD3.
    - exact WR3.
    - exact OW3.
    - right. split; [exact EQ|]. split; [reflexivity|]. split; [exists pid'; split; [exact ELB | exact ABR]|].
      split; [exact XP3 | exact AL2].
    - exact RF3.
    - exact AC3.
    - exact S03.
  Qed.

  Lemma bw_sl : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    Zlen xs = cap ->
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (v4_entry V32_SLOW_RREF)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = wz BW_SRET -> getr R1 2 = wz (spz - 64) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = wz it -> getr R1 9 = wz (v + 8) -> getr R1 10 = wz v -> getr R1 11 = wz src ->
    getr R1 20 = wz (sh (v + 8)) -> getr R1 21 = wz ASHADOW_BASE ->
    getr R1 23 = s7 -> getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    munch [(spz - 64, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (spz - 64) FRAME ->
    mem_inv asegs m1 -> rw_cells asegs m1 (errno_addr tp) [C4 e1] ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 EQ VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G11 G20 G21 G23 G24 G25 G26 G27 KR1 MP1 MU1 WM1 FR1 MI1 ERR1.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof bw_vfacts as (_ & _ & _ & _ & Hlen & Hb & Hvb & _).
    destruct (bw_after_frame m1 MU1 WM1 FR1) as (RH1 & RF1 & AC1 & RA1 & ST1 & S01 & XP1 & OW1 & VC1 & AD1 & WR1 & SH1).
    pose proof SRCR as (SR4 & SR0 & SR47).
    pose proof LOR as (LO1 & LO2). unfold BIW32_STACK in LO2.
    pose proof OBJ as O. destruct O as (_ & _ & _ & _ & _ & OD).
    assert (SP64 : bv_unsigned (getr R1 2) = spz - 64) by (rewrite G2; unfold wz; rewrite u64_of_Z by lia; reflexivity).
    assert (XPX : forall X, xpres H LB spz X m m1)
      by (intros X; eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hbb; exact Hbb | intros a Ha; destruct Ha]).
    assert (SK : src4_keep H LB (spz - 64) m1 src x).
    { intros m' ACm MIm APm.
      apply SRC; [exact ACm | exact MIm |].
      apply (xpres_trans H LB spz _ m m1 m'); [exact (XPX _)|].
      eapply (xpres_weaken H); [eapply (xpres_of_apres H); exact APm | lia | intros bb Hbb; exact Hbb | intros a Ha; exact Ha]. }
    assert (SHC : 0 < cap -> SHAD m1 b (cc_gen (4 * cap) (4 * cap))) by (intros C0; pose proof (SH1 C0) as K; rewrite EQ in K; exact K).
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply HV4R with (v := v) (b := b) (cap := cap) (src := src) (x := x) (xs := xs) (pid := pid) (LB := LB) (LF := LF)
                       (lo := lo) (B := B) (shi := shi) (errv := e1).
      - exact VIS1.
      - exact G10.
      - exact G11.
      - exact VC1.
      - exact EQ.
      - exact V8.
      - exact AD1.
      - rewrite SP64. exact bw_obj64.
      - exact VBAND.
      - exact WR1.
      - exact OW1.
      - exact OLD.
      - exact SHC.
      - exact (GROW EQ).
      - rewrite SP64. exact SK.
      - cbn [v4_xmax V32_SLOW_RREF]. lia.
      - exact SR4.
      - exact SR0.
      - exact SR47.
      - exact RH1.
      - exact KR1.
      - exact (proj1 (SLOWOK EQ)).
      - exact (proj2 (SLOWOK EQ)).
      - exact TRO.
      - exact RA1.
      - rewrite SP64. lia.
      - rewrite SP64. apply v4_mod16_sub64. exact SP16.
      - rewrite SP64. lia.
      - rewrite SP64. exact (proj1 (stk_split asegs m1 lo (spz - 64) spz ST1 ltac:(lia))).
      - exact LO1.
      - rewrite SP64. lia.
      - rewrite G4. exact ERR1.
      - exact MI1.
      - rewrite G4. exact TPV.
      - rewrite G1. unfold wz. rewrite u64_of_Z by (unfold BW_SRET; lia). unfold BW_SRET. reflexivity.
      - exact AC1.
      - exact RF1.
      - exact S01.
      - rewrite SP64. lia. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & sk2
                      & pid' & b' & P).
    cbv zeta in P.
    destruct P as (VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & XP2 & ABR & RH2 & VC2 & SH2 & AD2 & WR2 & OW2 & RF2 & AC2
                   & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite SP64 in ST2, XP2. rewrite G4 in ERR2.
    rewrite G1 in VIS2. unfold wz in VIS2.
    rewrite (ret_pc_even BW_SRET ltac:(unfold BW_SRET; lia) ltac:(unfold BW_SRET; reflexivity)) in VIS2.
    assert (FR2 : rw_cells asegs m2 (spz - 64) FRAME).
    { eapply (xpres_rw_cells H); [exact XP2 | exact FR1 |]. rewrite bw_cells64. unfold xclient_range. split.
      - unfold aclient_range. left. lia.
      - apply Forall_cons; [cbn [fst snd]; lia|]. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
        destruct Hb as [[E1 E2]|(C0 & IN & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [lia|].
        pose proof (bw_sh_lo (b + 4 * cap) ltac:(lia)) as SHL.
        assert (sh b + nsh (4 * cap) <= sh (b + 4 * cap) + 1) by (clear - B16 B0 Bn; unfold sh, nsh; Z.div_mod_to_equations; lia).
        apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (ST2' : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 64) spz); [exact ST2 | | lia].
      pose proof (stk_of_rw_cells asegs m2 (spz - 64) FRAME FR2) as SB. rewrite bw_cells64 in SB.
      replace (spz - 64 + 64) with spz in SB by lia. exact SB. }
    assert (XP2' : xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m2).
    { apply (xpres_trans H LB spz _ m m1 m2); [exact (XPX _)|].
      eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hbb; exact Hbb | intros a Ha; exact Ha]. }
    eapply (bw_s3 msF2 mo2 sk2 m2 _ (v4_newLB H LB b pid pid' b' (4 * v4_newcap cap)) b' errv2 VIS2
              (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - reflexivity.
    - exact G20.
    - exact G21.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - exact EQ.
    - exact FR2.
    - exact MI2.
    - exact ST2'.
    - exact ERR2.
    - exact RAX2.
    - exact XP2'.
    - exists pid'. split; [reflexivity | exact ABR].
    - exact RH2.
    - exact VC2.
    - exact SH2.
    - exact AD2.
    - exact WR2.
    - exact OW2.
    - exact RF2.
    - exact AC2.
    - exact S02.
    - exact AL2.
  Qed.

  Lemma bw_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 it) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 BIW32_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof bw_num as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof bw_vfacts as (F0 & F1 & F2 & FE & Hlen & Hb & Hvb & HD).
    pose proof LOR as (LO1 & LO2).
    pose proof OBJ as O. destruct O as (_ & _ & _ & _ & _ & OD).
    assert (GZ : gz m v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]).
    assert (GZI : gz m it 8) by (intros i Hi; eapply sh0_of_addressable; [exact ITAD | change (8 * (8 / 8)) with 8; lia]).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct Hb as [[E1 E2]|(C0 & IN & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [rewrite E1, E2; lia | lia]. }
    assert (ISD : it + 8 <= spz - 64 \/ spz <= it) by lia.
    assert (VSD : v + 24 <= spz - 64 \/ spz <= v) by lia.
    assert (ERRF : forall m1, munch [(spz - 64, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (errno_addr tp) [C4 errv]).
    { intros m1 MU WM. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |].
      change (Z.of_nat (cells_size [C4 errv])) with 4. rewrite bw_errno_val. cbn [disjoint_from]. split; [lia | exact I]. }
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 it) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (Z_lt_le_dec (Zlen xs) cap) as [LT | GE].
    - destruct Hb as [[E1 E2]|(C0 & IN & AB)]; [lia|].
      pose proof AB as (B0 & B16 & Bn & BI & BC & BF & BAPP).
      destruct (bw_P1F_ok R0 F fc m it src spz v b (Zlen xs) cap lo
                  ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; exact bw_spz_sp)
                  AC0 ITC GZI F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH ltac:(lia) ltac:(lia) IT8 ISD
                  ltac:(destruct VBAND; lia) ltac:(destruct VBAND; lia) V8 VSD (bw_b16 b B16 B0) ltac:(lia) ltac:(lia) LT ltac:(lia))
        as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K18 & K19 & K20 & K21 & K22 & KK).
      assert (FRM : rw_cells asegs M1 (spz - 64) FRAME) by (rewrite HR0 in FR1; exact FR1).
      pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
      destruct (bw_after_frame M1 MU1 WM1 FRM) as (RH1 & RF1 & AC1 & RA1 & ST1 & S01 & XP1 & OW1 & VC1 & AD1 & WR1 & SH1).
      pose proof (ERRF M1 MU1 WM1) as ERR1.
      assert (Q3 : getr R1 3 = gp) by (rewrite (KK 3%bv ltac:(inb)), HR0; reflexivity).
      assert (Q4 : getr R1 4 = tp) by (rewrite (KK 4%bv ltac:(inb)), HR0; reflexivity).
      assert (Q23 : getr R1 23 = s7) by (rewrite (KK 23%bv ltac:(inb)), HR0; reflexivity).
      assert (Q24 : getr R1 24 = s8) by (rewrite (KK 24%bv ltac:(inb)), HR0; reflexivity).
      assert (Q25 : getr R1 25 = s9) by (rewrite (KK 25%bv ltac:(inb)), HR0; reflexivity).
      assert (Q26 : getr R1 26 = s10) by (rewrite (KK 26%bv ltac:(inb)), HR0; reflexivity).
      assert (Q27 : getr R1 27 = s11) by (rewrite (KK 27%bv ltac:(inb)), HR0; reflexivity).
      eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (ahh_evt_then H HH); [exact KR1 | exact VIS1 | |].
      { eapply HANN with (beg := b) (len := 4 * cap) (oldmid := 4 * Zlen xs) (newmid := 4 * Zlen xs + 4) (lo := lo).
        - exact K10.
        - exact K11.
        - exact K12.
        - rewrite K13. unfold wz. f_equal. lia.
        - exact (v4_mod16_8 b B16).
        - lia.
        - lia.
        - lia.
        - exact BAPP.
        - unfold AAPP_HI; lia.
        - exact (SH1 C0).
        - rewrite K2. unfold wz. rewrite u64_of_Z by lia. exact (proj1 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(lia))).
        - exact LO1.
        - rewrite K2. unfold wz. rewrite u64_of_Z by lia. unfold AINTRIN_STACK. lia.
        - exact MI1.
        - exact AC1.
        - unfold in_app_mem. destruct (vt_band_of_aapp _ _ BAPP) as [K|K]; [left | right];
            rewrite ?ASHADOW_BASE_val; unfold AHI_LO, AAPP_HI; lia. }
      intros msF2 mo2 KR2 MP2 POST.
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                        & VIS2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
      rewrite K2 in MU2, ST2. unfold wz in MU2, ST2. rewrite u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.
      rewrite K1 in VIS2. unfold wz in VIS2.
      rewrite (ret_pc_even BW_FRET ltac:(unfold BW_FRET; lia) ltac:(unfold BW_FRET; reflexivity)) in VIS2.
      pose proof (bw_wsh (sh b) (sh b + nsh (4 * cap)) C0 ltac:(lia) ltac:(lia)) as (WS1 & WS2 & WS3 & WS4 & WS5).
      pose proof (bw_wstk (spz - 64 - 4096) (spz - 64) ltac:(lia) ltac:(lia)) as (WT1 & WT2 & WT3 & WT4 & WT5).
      destruct (client_frame H HH s LB LF B _ M1 m2 RH1 RF1 AC1 RA1 MU2 WM2
                  ltac:(apply Forall_cons; [exact WS1|]; apply Forall_cons; [exact WT1 | apply Forall_nil])
                  ltac:(apply Forall_cons; [exact WS2|]; apply Forall_cons; [exact WT2 | apply Forall_nil])
                  ltac:(apply Forall_cons; [exact WS3|]; apply Forall_cons; [exact WT3 | apply Forall_nil]))
        as (RH2 & RF2 & AC2' & RA2).
      pose proof (bw_sh_lo (b + 4 * cap) ltac:(lia)) as SHL.
      assert (SHN : sh b + nsh (4 * cap) <= sh (b + 4 * cap) + 1) by (clear - B16 B0 Bn; unfold sh, nsh; Z.div_mod_to_equations; lia).
      assert (FR2 : rw_cells asegs m2 (spz - 64) FRAME).
      { eapply rw_cells_transport; [exact FRM | exact MU2 | exact WM2 |]. rewrite bw_cells64.
        cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
      assert (ST2' : stk asegs m2 lo spz).
      { apply (stk_merge asegs m2 lo (spz - 64) spz); [exact ST2 | | lia].
        pose proof (stk_of_rw_cells asegs m2 (spz - 64) FRAME FR2) as SB. rewrite bw_cells64 in SB.
        replace (spz - 64 + 64) with spz in SB by lia. exact SB. }
      assert (ERR2 : rw_cells asegs m2 (errno_addr tp) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR1 | exact MU2 | exact WM2 |].
        change (Z.of_nat (cells_size [C4 errv])) with 4.
        destruct WS5 as [WS5 _]. destruct WT5 as [WT5 _]. cbn [disjoint_from]. split; [exact WS5 | split; [exact WT5 | exact I]]. }
      assert (S02 : stack0 m2 lo shi).
      { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
        apply Forall_cons; [exact WS4|]. apply Forall_cons; [exact WT4 | apply Forall_nil]. }
      assert (XP2 : xpres H LB spz [(sh b, sh b + nsh (4 * cap))] m m2).
      { apply (xpres_trans H LB spz _ m M1 m2).
        - eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hbb; exact Hbb | intros a Ha; destruct Ha].
        - eapply (xpres_of_munch H s LB spz _ _ m M1 m2); [exact HH | exact RH0 | exact MU2 | exact WM2 |].
          apply Forall_cons; [right; intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; left; lia|].
          apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
      assert (VC2 : vec32A LB m2 v b xs cap).
      { eapply vec32A_munch; [exact VC1 | exact MU2 | |].
        - pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
          cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
        - pose proof (v4_app_sh b (4 * Zlen xs) b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(destruct (vt_band_of_aapp _ _ BAPP); [left|right]; lia)) as D.
          cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
      assert (AD2 : addressable m2 v 24).
      { eapply addressable_transport; [exact AD1 | exact MU2 | exact WM2 |].
        pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) (Hvb ltac:(lia))) as D.
        pose proof (bw_sh_lo v ltac:(destruct VBAND; lia)) as D2. rewrite v4_nsh24 in D |- *.
        cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
      assert (WR2 : wr_at asegs m2 v 24) by exact (wr_at_wmono _ _ _ _ WR1 WM2).
      assert (OW2 : lb_own LB m2) by exact (lb_own_wmono _ _ _ OW1 WM2).
      eapply (bw_f2 msF2 mo2 m2 _ errv LT VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + exact K2.
      + exact Q3.
      + exact Q4.
      + exact K8.
      + exact K9.
      + exact K18.
      + exact K19.
      + exact K20.
      + exact K21.
      + exact K22.
      + exact Q23.
      + exact Q24.
      + exact Q25.
      + exact Q26.
      + exact Q27.
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
      + exact FR2.
      + exact MI2.
      + exact ST2'.
      + exact ERR2.
      + exact RA2.
      + exact RH2.
      + exact RF2.
      + exact AC2.
      + exact S02.
      + exact OW2.
      + exact XP2.
      + exact VC2.
      + exact AD2.
      + exact WR2.
      + exact SH2.
    - assert (EQ : Zlen xs = cap) by lia.
      destruct (bw_P1S_ok R0 F fc m it src spz v b (Zlen xs) cap lo
                  ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; exact bw_spz_sp)
                  AC0 ITC GZI F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH ltac:(lia) ltac:(lia) IT8 ISD
                  ltac:(destruct VBAND; lia) ltac:(destruct VBAND; lia) V8 VSD (proj1 OB0) (proj2 OB0) EQ ltac:(lia))
        as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K8 & K9 & K10 & K11 & K20 & K21 & KK).
      assert (FRM : rw_cells asegs M1 (spz - 64) FRAME) by (rewrite HR0 in FR1; exact FR1).
      pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
      pose proof (ERRF M1 MU1 WM1) as ERR1.
      eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
      eapply (bw_sl msF1 mo1 M1 R1 errv EQ VIS1 HF1).
      + exact K1.
      + exact K2.
      + rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
      + rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
      + exact K8.
      + exact K9.
      + exact K10.
      + exact K11.
      + exact K20.
      + exact K21.
      + rewrite (KK 23%bv ltac:(inb)), HR0. reflexivity.
      + rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
      + rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
      + rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
      + rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
      + exact KR1.
      + exact MP1.
      + exact MU1.
      + exact WM1.
      + exact FRM.
      + exact MI1.
      + exact ERR1.
  Qed.

End BW.

  Theorem biw32_ok : biw32_stmt H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo
      s LB LF it v b cap src x xs pid lo B shi errv
      VIS EA0 EA1 ITC IT8 ITAD ITAP VEC V8 ADV0 OBJ VBAND VWR OWN OLD OLDSH CAPB GROW SRC XR SR4 SR0 SR47 RH0 KR SLOWOK TRO
      RA0 SPB SP16 SPH ST0 ACL LOH ERR MI0 TPV RAE AC0 RF0 S00 SHI.
    subst a0 a1.
    eapply (bw_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF it v b cap src x xs pid lo B shi
              (bv_unsigned sp));
      first [ exact VIS | exact KR | exact ERR | reflexivity | eassumption
            | (split; [assumption | split; assumption]) | (split; assumption) ].
  Qed.

End BiW32P.
