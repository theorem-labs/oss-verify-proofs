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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition VOT_FRET : Z := 0xf9304.
Definition VOT_SRET : Z := 0xf9344.
Definition VOT_RET  : Z := 0xf9388.

Definition VSAVED : list reg := [21; 20; 19; 18; 9; 8; 1]%bv.
Definition VK1 : list reg := [3; 4; 22; 23; 24; 25; 26; 27]%bv.

Definition vtr1f_E (R : bvmap 5 word) (v src spz b len cap : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 cap].
Definition vtr1f_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition vtr1f_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 35); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 4) (EVar 36))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 4) (EVar 37))); KWr (SA (EVar 34) (-64)) (ELit 64); KRange (EVar 34) (2 ^ 45 + 64) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 35) 16 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-64)) (ELit 64)].
Definition vtr1f_F_dirs : list bool := [false; false].
Definition vtr1f_F_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [770924; 1029076] (SCR vtr1f_F_dirs [] []) 1020512 vtr1f_sr vtr1f_kn 40.
Definition vtr1f_F_x := sym_exec bsegs 200 true [770924; 1029076] (SCR vtr1f_F_dirs [] []) (SS 1020512 vtr1f_sr [] vtr1f_F_knF 40) [].
Definition vtr1f_F_ss : sym_state := Eval vm_compute in fst (fst vtr1f_F_x).
Definition vtr1f_F_scs : list sidecond := Eval vm_compute in snd (fst vtr1f_F_x).
Lemma vtr1f_F_eq : vtr1f_F_x = (vtr1f_F_ss, vtr1f_F_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr1f_F_pc : s_pc vtr1f_F_ss = 770924.
Proof. reflexivity. Qed.
Lemma vtr1f_F_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (len < cap) -> (cap <= 2 ^ 24) ->
  scs_denot bsegs m (vtr1f_E R v src spz b len cap) vtr1f_F_scs.
Proof.
  intros R m v src spz b len cap H0 H1 H2 H3 H4 H5 H6 H7. unfold vtr1f_E, vtr1f_F_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma vtr1f_F_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= len) -> (len < cap) -> (cap <= 2 ^ 24) ->
  regs_ok (vtr1f_E R v src spz b len cap) vtr1f_sr R -> know_ok bsegs (vtr1f_E R v src spz b len cap) m vtr1f_F_knF ->
  exists R', regs_ok (vtr1f_E R v src spz b len cap) (s_regs vtr1f_F_ss) R' /\ log_flat (vtr1f_E R v src spz b len cap) (s_log vtr1f_F_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020512) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 770924) (mem_denot (vtr1f_E R v src spz b len cap) m (s_log vtr1f_F_ss)) rom).
Proof.
  intros fx R m rom v src spz b len cap H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr1f_F_eq HR HK
              (vtr1f_F_sc R m v src spz b len cap H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr1s_E (R : bvmap 5 word) (v src spz b len cap : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 cap].
Definition vtr1s_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition vtr1s_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 35); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 4) (EVar 36))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 4) (EVar 37))); KWr (SA (EVar 34) (-64)) (ELit 64); KRange (EVar 34) (2 ^ 45 + 64) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 35) 0 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-64)) (ELit 64)].
Definition vtr1s_S_dirs : list bool := [true].
Definition vtr1s_S_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [770924; 1029076] (SCR vtr1s_S_dirs [] []) 1020512 vtr1s_sr vtr1s_kn 40.
Definition vtr1s_S_x := sym_exec bsegs 200 true [770924; 1029076] (SCR vtr1s_S_dirs [] []) (SS 1020512 vtr1s_sr [] vtr1s_S_knF 40) [].
Definition vtr1s_S_ss : sym_state := Eval vm_compute in fst (fst vtr1s_S_x).
Definition vtr1s_S_scs : list sidecond := Eval vm_compute in snd (fst vtr1s_S_x).
Lemma vtr1s_S_eq : vtr1s_S_x = (vtr1s_S_ss, vtr1s_S_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr1s_S_pc : s_pc vtr1s_S_ss = 1029076.
Proof. reflexivity. Qed.
Lemma vtr1s_S_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (len = cap) -> (0 <= cap <= 2 ^ 24) ->
  scs_denot bsegs m (vtr1s_E R v src spz b len cap) vtr1s_S_scs.
Proof.
  intros R m v src spz b len cap H0 H1 H2 H3 H4 H5 H6. unfold vtr1s_E, vtr1s_S_scs. split_scs.
  - sc_closeB.
Qed.
Lemma vtr1s_S_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b len cap : Z),
  (2 ^ 45 + 64 <= spz <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (len = cap) -> (0 <= cap <= 2 ^ 24) ->
  regs_ok (vtr1s_E R v src spz b len cap) vtr1s_sr R -> know_ok bsegs (vtr1s_E R v src spz b len cap) m vtr1s_S_knF ->
  exists R', regs_ok (vtr1s_E R v src spz b len cap) (s_regs vtr1s_S_ss) R' /\ log_flat (vtr1s_E R v src spz b len cap) (s_log vtr1s_S_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020512) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1029076) (mem_denot (vtr1s_E R v src spz b len cap) m (s_log vtr1s_S_ss)) rom).
Proof.
  intros fx R m rom v src spz b len cap H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr1s_S_eq HR HK
              (vtr1s_S_sc R m v src spz b len cap H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr2a_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21].
Definition vtr2a_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (9%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (18%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 36)].
Definition vtr2a_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 31 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (ELit 0)].
Definition vtr2a_A_dirs : list bool := [].
Definition vtr2a_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1020808] (SCR vtr2a_A_dirs [] []) 1020676 vtr2a_sr vtr2a_kn 50.
Definition vtr2a_A_x := sym_exec bsegs 200 true [1020808] (SCR vtr2a_A_dirs [] []) (SS 1020676 vtr2a_sr [] vtr2a_A_knF 50) [].
Definition vtr2a_A_ss : sym_state := Eval vm_compute in fst (fst vtr2a_A_x).
Definition vtr2a_A_scs : list sidecond := Eval vm_compute in snd (fst vtr2a_A_x).
Lemma vtr2a_A_eq : vtr2a_A_x = (vtr2a_A_ss, vtr2a_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr2a_A_pc : s_pc vtr2a_A_ss = 1020808.
Proof. reflexivity. Qed.
Lemma vtr2a_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) ->
  scs_denot bsegs m (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2a_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21. unfold vtr2a_E, vtr2a_A_scs. split_scs.
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
Lemma vtr2a_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) ->
  regs_ok (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2a_sr R -> know_ok bsegs (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m vtr2a_A_knF ->
  exists R', regs_ok (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_regs vtr2a_A_ss) R' /\ log_flat (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_log vtr2a_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020676) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1020808) (mem_denot (vtr2a_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m (s_log vtr2a_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr2a_A_eq HR HK
              (vtr2a_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr2b_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21].
Definition vtr2b_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (9%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (18%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 36)].
Definition vtr2b_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 31 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (EVar 38); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (ELit 0); KRange (EVar 38) 1 7].
Definition vtr2b_A_dirs : list bool := [true].
Definition vtr2b_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1020808] (SCR vtr2b_A_dirs [] []) 1020676 vtr2b_sr vtr2b_kn 50.
Definition vtr2b_A_x := sym_exec bsegs 200 true [1020808] (SCR vtr2b_A_dirs [] []) (SS 1020676 vtr2b_sr [] vtr2b_A_knF 50) [].
Definition vtr2b_A_ss : sym_state := Eval vm_compute in fst (fst vtr2b_A_x).
Definition vtr2b_A_scs : list sidecond := Eval vm_compute in snd (fst vtr2b_A_x).
Lemma vtr2b_A_eq : vtr2b_A_x = (vtr2b_A_ss, vtr2b_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr2b_A_pc : s_pc vtr2b_A_ss = 1020808.
Proof. reflexivity. Qed.
Lemma vtr2b_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) ->
  scs_denot bsegs m (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2b_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22. unfold vtr2b_E, vtr2b_A_scs. split_scs.
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
Lemma vtr2b_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) ->
  regs_ok (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2b_sr R -> know_ok bsegs (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m vtr2b_A_knF ->
  exists R', regs_ok (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_regs vtr2b_A_ss) R' /\ log_flat (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_log vtr2b_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020676) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1020808) (mem_denot (vtr2b_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m (s_log vtr2b_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr2b_A_eq HR HK
              (vtr2b_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr2c_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21].
Definition vtr2c_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (9%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (18%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 36)].
Definition vtr2c_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 31 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (EVar 39); KRange (EVar 39) 1 7].
Definition vtr2c_A_dirs : list bool := [true].
Definition vtr2c_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1020808] (SCR vtr2c_A_dirs [] []) 1020676 vtr2c_sr vtr2c_kn 50.
Definition vtr2c_A_x := sym_exec bsegs 200 true [1020808] (SCR vtr2c_A_dirs [] []) (SS 1020676 vtr2c_sr [] vtr2c_A_knF 50) [].
Definition vtr2c_A_ss : sym_state := Eval vm_compute in fst (fst vtr2c_A_x).
Definition vtr2c_A_scs : list sidecond := Eval vm_compute in snd (fst vtr2c_A_x).
Lemma vtr2c_A_eq : vtr2c_A_x = (vtr2c_A_ss, vtr2c_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr2c_A_pc : s_pc vtr2c_A_ss = 1020808.
Proof. reflexivity. Qed.
Lemma vtr2c_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  scs_denot bsegs m (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2c_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22. unfold vtr2c_E, vtr2c_A_scs. split_scs.
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
Lemma vtr2c_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  regs_ok (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2c_sr R -> know_ok bsegs (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m vtr2c_A_knF ->
  exists R', regs_ok (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_regs vtr2c_A_ss) R' /\ log_flat (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_log vtr2c_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020676) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1020808) (mem_denot (vtr2c_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m (s_log vtr2c_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr2c_A_eq HR HK
              (vtr2c_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr2d_E (R : bvmap 5 word) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 src; Z_to_bv 64 x; Z_to_bv 64 k; Z_to_bv 64 j; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21].
Definition vtr2d_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (9%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 4)); (18%bv, EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 36)].
Definition vtr2d_kn : list kentry := [KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 36) 0 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 0 (2 ^ 31 - 1); KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (EVar 38); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) (ELit 3)) 2147450880) 1 (EVar 39); KRange (EVar 38) 1 7; KRange (EVar 39) 1 7].
Definition vtr2d_A_dirs : list bool := [true; true].
Definition vtr2d_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1020808] (SCR vtr2d_A_dirs [] []) 1020676 vtr2d_sr vtr2d_kn 50.
Definition vtr2d_A_x := sym_exec bsegs 200 true [1020808] (SCR vtr2d_A_dirs [] []) (SS 1020676 vtr2d_sr [] vtr2d_A_knF 50) [].
Definition vtr2d_A_ss : sym_state := Eval vm_compute in fst (fst vtr2d_A_x).
Definition vtr2d_A_scs : list sidecond := Eval vm_compute in snd (fst vtr2d_A_x).
Lemma vtr2d_A_eq : vtr2d_A_x = (vtr2d_A_ss, vtr2d_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr2d_A_pc : s_pc vtr2d_A_ss = 1020808.
Proof. reflexivity. Qed.
Lemma vtr2d_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  scs_denot bsegs m (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2d_A_scs.
Proof.
  intros R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23. unfold vtr2d_E, vtr2d_A_scs. split_scs.
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
Lemma vtr2d_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (16 <= b) -> (b mod 4 = 0) -> (b + 4 * len + 4 <= sp1) -> (0 <= len <= 2 ^ 24) -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) -> (b + 4 * len + 4 <= 2147450880 \/ 17594333495296 <= b) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src mod 4 = 0) -> (0 <= x < 2 ^ 31) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) -> (src mod 8 + 4 <= k < 8) -> ((b + 4 * len) mod 8 + 4 <= j < 8) ->
  regs_ok (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) vtr2d_sr R -> know_ok bsegs (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m vtr2d_A_knF ->
  exists R', regs_ok (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_regs vtr2d_A_ss) R' /\ log_flat (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) (s_log vtr2d_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020676) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1020808) (mem_denot (vtr2d_E R v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21) m (s_log vtr2d_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr2d_A_eq HR HK
              (vtr2d_A_sc R m v sp1 b len src x k j w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vtr3_E (R : bvmap 5 word) (v sp1 e w1 w8 w9 w18 w19 w20 w21 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sp1; Z_to_bv 64 e; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 w1; Z_to_bv 64 w8; Z_to_bv 64 w9; Z_to_bv 64 w18; Z_to_bv 64 w19; Z_to_bv 64 w20; Z_to_bv 64 w21].
Definition vtr3_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (10%bv, EVar 34); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880)].
Definition vtr3_kn : list kentry := [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0); KWr (SA (EVar 32) 8) (ELit 8); KWord (SA (EVar 33) 8) 8 (EVar 46); KWord (SA (EVar 33) 16) 8 (EVar 45); KWord (SA (EVar 33) 24) 8 (EVar 44); KWord (SA (EVar 33) 32) 8 (EVar 43); KWord (SA (EVar 33) 40) 8 (EVar 42); KWord (SA (EVar 33) 48) 8 (EVar 41); KWord (SA (EVar 33) 56) 8 (EVar 40); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 7241728 (2 ^ 47); KDisj (SA (EVar 32) 8) (ELit 8) (SA (EVar 33) 0) (ELit 64); KRange (EVar 34) 5 (2 ^ 64 - 1); KAlign (EVar 34) 4].
Definition vtr3_A_dirs : list bool := [].
Definition vtr3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 200 [1020808] (SCR vtr3_A_dirs [] []) 1020740 vtr3_sr vtr3_kn 50.
Definition vtr3_A_x := sym_exec bsegs 200 true [1020808] (SCR vtr3_A_dirs [] []) (SS 1020740 vtr3_sr [] vtr3_A_knF 50) [].
Definition vtr3_A_ss : sym_state := Eval vm_compute in fst (fst vtr3_A_x).
Definition vtr3_A_scs : list sidecond := Eval vm_compute in snd (fst vtr3_A_x).
Lemma vtr3_A_eq : vtr3_A_x = (vtr3_A_ss, vtr3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vtr3_A_pc : s_pc vtr3_A_ss = 1020808.
Proof. reflexivity. Qed.
Lemma vtr3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sp1 e w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (4 < e < 2 ^ 64) -> (e mod 4 = 0) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) ->
  scs_denot bsegs m (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) vtr3_A_scs.
Proof.
  intros R m v sp1 e w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold vtr3_E, vtr3_A_scs. split_scs.
Qed.
Lemma vtr3_A_run : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sp1 e w1 w8 w9 w18 w19 w20 w21 : Z),
  (2 ^ 45 <= sp1) -> (sp1 + 64 <= 2 ^ 47) -> (7241728 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp1 \/ sp1 + 64 <= v) -> (4 < e < 2 ^ 64) -> (e mod 4 = 0) -> (0 <= w1 < 2 ^ 64) -> (0 <= w8 < 2 ^ 64) -> (0 <= w9 < 2 ^ 64) -> (0 <= w18 < 2 ^ 64) -> (0 <= w19 < 2 ^ 64) -> (0 <= w20 < 2 ^ 64) -> (0 <= w21 < 2 ^ 64) ->
  regs_ok (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) vtr3_sr R -> know_ok bsegs (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) m vtr3_A_knF ->
  exists R', regs_ok (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) (s_regs vtr3_A_ss) R' /\ log_flat (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) (s_log vtr3_A_ss)
    /\ CatSim.msteps bsegs (PropExec.mkst R (Z_to_bv 64 1020740) m rom)
                    (PropExec.mkst R' (Z_to_bv 64 1020808) (mem_denot (vtr3_E R v sp1 e w1 w8 w9 w18 w19 w20 w21) m (s_log vtr3_A_ss)) rom).
Proof.
  intros fx R m rom v sp1 e w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vtr3_A_eq HR HK
              (vtr3_A_sc R m v sp1 e w1 w8 w9 w18 w19 w20 w21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.

Ltac vt_frame E Hlf :=
  first
  [ lazymatch goal with |- munch _ ?m0 (mem_denot _ _ _) =>
      let MU := fresh "MU" in
      pose proof (munch_mem_denot_sb [(-56, 0)] (EVar 34) E m0 _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
      eapply v4_munch_eqW; [exact MU | cbn [map fst snd]; evs; rewrite u64_of_Z by lia; repeat f_equal; lia] end
  | lazymatch goal with |- rw_cells _ (mem_denot _ _ ?lg) _ _ =>
      change lg with (v4_c8log (EVar 34) (-56) [EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1]);
      eapply rw_cells_mem_eq_list;
      [ apply v4_rw_cells_c8log;
        [ exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia
        | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; eapply wr_at_of_stk_win; [eassumption | lia | lia] ]
      | reflexivity ] end ].

Ltac vt_fin2 E Hlf :=
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

Lemma vt_wrange : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. exact (bv_unsigned_in_range _ w). Qed.

Ltac vt_kfr :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA ?bs ?off) 8 ?e) =>
      match goal with HC : rw_cells _ M ?A ?cs |- _ =>
        let k := eval vm_compute in (Z.to_nat (off - 8)) in
        eapply (kword_of_rw_cells asegs E M A cs k _ (SA bs off) e 8 HC);
        [ cbn; reflexivity | reflexivity | lia | rw_addrB | lia | lia
        | cbn [cbytes]; evs; rewrite Z_to_bv_bv_unsigned; reflexivity ]
      end
  end.

Ltac vt_knowF := change bsegs with asegs; kn_eval; unfold know_ok; repeat (apply Forall_cons; [first [kentryB | vt_kfr] |]); apply Forall_nil.

Ltac vt_wreg := evs; apply Z_to_bv_bv_unsigned.

Definition vt_P1F : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v src spz b len cap lo : Z),
    getr R 10 = wz v -> getr R 11 = wz src -> getr R 2 = wz spz ->
    ACONST m -> fldA m v 8 b -> fldA m (v + 8) 8 (b + 4 * len) -> fldA m (v + 16) 8 (b + 4 * cap) -> gz m v 24 ->
    stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= spz - 64 \/ spz <= v) ->
    16 <= b -> b + 4 * cap < 2 ^ 47 -> 0 <= len -> len < cap -> cap <= 2 ^ 24 ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz 0xf9260) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 56, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 56) (map (fun r => C8 (getr R r)) VSAVED)
      /\ getr R' 1 = wz VOT_FRET /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz (v + 8) /\ getr R' 9 = wz (b + 4 * len + 4)
      /\ getr R' 10 = wz b /\ getr R' 11 = wz (b + 4 * cap) /\ getr R' 12 = wz (b + 4 * len) /\ getr R' 13 = wz (b + 4 * len + 4)
      /\ getr R' 18 = wz (b + 4 * len) /\ getr R' 19 = wz (sh (v + 8)) /\ getr R' 20 = wz ASHADOW_BASE /\ getr R' 21 = wz src
      /\ (forall r, In r VK1 -> getr R' r = getr R r).

Definition vt_P1S : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v src spz b len cap lo : Z),
    getr R 10 = wz v -> getr R 11 = wz src -> getr R 2 = wz spz ->
    ACONST m -> fldA m v 8 b -> fldA m (v + 8) 8 (b + 4 * len) -> fldA m (v + 16) 8 (b + 4 * cap) -> gz m v 24 ->
    stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= spz - 64 \/ spz <= v) ->
    0 <= b -> b + 4 * cap < 2 ^ 47 -> len = cap -> 0 <= cap <= 2 ^ 24 ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz 0xf9260) fc None m (seg_rom asegs)) (MS R' F (wz 0xfb3d4) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 56, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 56) (map (fun r => C8 (getr R r)) VSAVED)
      /\ getr R' 1 = wz VOT_SRET /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz (v + 8) /\ getr R' 10 = wz v /\ getr R' 11 = wz src
      /\ getr R' 19 = wz (sh (v + 8)) /\ getr R' 20 = wz ASHADOW_BASE
      /\ (forall r, In r VK1 -> getr R' r = getr R r).

Lemma vt_P1F_ok : vt_P1F.
Proof.
  intros R F fc m v src spz b len cap lo H10 H11 H2 HAC Hb He Hc HGZ HST Hlo Hs1 Hs2 Hv1 Hv2 Hvd Hb16 Hbc Hl0 Hlc Hc24.
  set (fx := PropExec.mkFP F fc).
  stash_disjB.
  assert (HR : regs_ok (vtr1f_E R v src spz b len cap) vtr1f_sr R) by (unfold vtr1f_E, vtr1f_sr; rw_seedB).
  assert (HK : know_ok bsegs (vtr1f_E R v src spz b len cap) m vtr1f_F_knF) by (unfold vtr1f_E; knowB).
  destruct (vtr1f_F_run fx R m (seg_rom asegs) v src spz b len cap ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold vtr1f_F_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := vtr1f_E R v src spz b len cap) in *. unfold vtr1f_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [vt_frame Ev Hlf|].
  split; [apply rw_wmono|].
  split; [vt_frame Ev Hlf|].
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
  keptB HR HR' VK1.
Qed.

Lemma vt_P1S_ok : vt_P1S.
Proof.
  intros R F fc m v src spz b len cap lo H10 H11 H2 HAC Hb He Hc HGZ HST Hlo Hs1 Hs2 Hv1 Hv2 Hvd Hb0 Hbc Hlc Hc24.
  set (fx := PropExec.mkFP F fc).
  stash_disjB.
  assert (HR : regs_ok (vtr1s_E R v src spz b len cap) vtr1s_sr R) by (unfold vtr1s_E, vtr1s_sr; rw_seedB).
  assert (HK : know_ok bsegs (vtr1s_E R v src spz b len cap) m vtr1s_S_knF) by (unfold vtr1s_E; knowB).
  destruct (vtr1s_S_run fx R m (seg_rom asegs) v src spz b len cap ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold vtr1s_S_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := vtr1s_E R v src spz b len cap) in *. unfold vtr1s_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [vt_frame Ev Hlf|].
  split; [apply rw_wmono|].
  split; [vt_frame Ev Hlf|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' VK1.
Qed.

Definition VK2 : list reg := [3; 4; 22; 23; 24; 25; 26; 27]%bv.
Definition vt_P2 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sp1 b len src x k j : Z) (x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 2 = wz sp1 -> getr R 8 = wz (v + 8) -> getr R 9 = wz (b + 4 * len + 4) -> getr R 18 = wz (b + 4 * len)
    -> getr R 19 = wz (sh (v + 8)) -> getr R 20 = wz ASHADOW_BASE -> getr R 21 = wz src ->
    rw_cells asegs m (sp1 + 8) (map (fun w => C8 w) [x21; x20; x19; x18; x9; x8; x1]) ->
    fldA m src 4 x -> LbB_Kit.shk m src k -> (k = 0 \/ src mod 8 + 4 <= k < 8) ->
    LbB_Kit.shk m (b + 4 * len) j -> (j = 0 \/ (b + 4 * len) mod 8 + 4 <= j < 8) ->
    LbB_Kit.shk m (v + 8) 0 -> wr_at asegs m (b + 4 * len) 4 -> wr_at asegs m (v + 8) 8 ->
    2 ^ 45 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> 0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= sp1 \/ sp1 + 64 <= v) ->
    16 <= b -> b mod 4 = 0 -> b + 4 * len + 4 <= sp1 -> 0 <= len <= 2 ^ 24 -> (v + 24 <= b + 4 * len \/ b + 4 * len + 4 <= v) ->
    b + 4 * len + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= b ->
    0 <= src -> src + 4 <= 2 ^ 47 -> src mod 4 = 0 -> 0 <= x < 2 ^ 31 ->
    exists R' M2,
      CatSim.msteps asegs (MS R F (wz VOT_FRET) fc None m (seg_rom asegs)) (MS R' F (wz VOT_RET) fc None M2 (seg_rom asegs))
      /\ munch [(v + 8, v + 16); (b + 4 * len, b + 4 * len + 4)] m M2 /\ wmono asegs m M2
      /\ rw_cells asegs M2 (v + 8) [C8 (wz (b + 4 * len + 4))] /\ rw_cells asegs M2 (b + 4 * len) [C4 (wz x)]
      /\ getr R' 1 = x1 /\ getr R' 2 = wz (sp1 + 64) /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 18 = x18
      /\ getr R' 19 = x19 /\ getr R' 20 = x20 /\ getr R' 21 = x21
      /\ (forall r, In r VK2 -> getr R' r = getr R r).

Ltac vt_p2_close HR HR' Ev Hlf Hms :=
  unstashB; rw_exB Hms;
  split; [exact Hms|];
  split; [vt_fin2 Ev Hlf|];
  split; [apply rw_wmono|];
  split; [vt_fin2 Ev Hlf|];
  split; [vt_fin2 Ev Hlf|];
  split; [rrwB HR' (1%bv : reg); vt_wreg|];
  split; [rrwB HR' (2%bv : reg); regB|];
  split; [rrwB HR' (8%bv : reg); vt_wreg|];
  split; [rrwB HR' (9%bv : reg); vt_wreg|];
  split; [rrwB HR' (18%bv : reg); vt_wreg|];
  split; [rrwB HR' (19%bv : reg); vt_wreg|];
  split; [rrwB HR' (20%bv : reg); vt_wreg|];
  split; [rrwB HR' (21%bv : reg); vt_wreg|];
  keptB HR HR' VK2.

Lemma vt_P2_ok : vt_P2.
Proof.
  intros R F fc m v sp1 b len src x k j x21 x20 x19 x18 x9 x8 x1 H2 H8 H9 H18 H19 H20 H21 HFR HX HSK Hk HSJ Hj HS8 HWE HW8
    Hs1 Hs2 Hv1 Hv2 Hvd Hb16 Hb4 Hbs Hlen Hbv Hband Hsr0 Hsr1 Hsr4 Hx.
  set (fx := PropExec.mkFP F fc).
  pose proof (vt_wrange x1) as B1. pose proof (vt_wrange x8) as B8. pose proof (vt_wrange x9) as B9.
  pose proof (vt_wrange x18) as B18. pose proof (vt_wrange x19) as B19. pose proof (vt_wrange x20) as B20.
  pose proof (vt_wrange x21) as B21.
  stash_disjB.
  destruct Hk as [Hk | Hk]; destruct Hj as [Hj | Hj].
  - subst k j.
    assert (HR : regs_ok (vtr2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) vtr2a_sr R)
      by (unfold vtr2a_E, vtr2a_sr; rw_seedB).
    assert (HK : know_ok bsegs (vtr2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) m vtr2a_A_knF)
      by (unfold vtr2a_E; vt_knowF).
    destruct (vtr2a_A_run fx R m (seg_rom asegs) v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK) as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold vtr2a_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := vtr2a_E R v sp1 b len src x 0 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) in *. unfold vtr2a_E in Ev.
    vt_p2_close HR HR' Ev Hlf Hms.
  - subst k.
    assert (HR : regs_ok (vtr2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) vtr2c_sr R)
      by (unfold vtr2c_E, vtr2c_sr; rw_seedB).
    assert (HK : know_ok bsegs (vtr2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) m vtr2c_A_knF)
      by (unfold vtr2c_E; vt_knowF).
    destruct (vtr2c_A_run fx R m (seg_rom asegs) v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK) as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold vtr2c_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := vtr2c_E R v sp1 b len src x 0 j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) in *. unfold vtr2c_E in Ev.
    vt_p2_close HR HR' Ev Hlf Hms.
  - subst j.
    assert (HR : regs_ok (vtr2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) vtr2b_sr R)
      by (unfold vtr2b_E, vtr2b_sr; rw_seedB).
    assert (HK : know_ok bsegs (vtr2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) m vtr2b_A_knF)
      by (unfold vtr2b_E; vt_knowF).
    destruct (vtr2b_A_run fx R m (seg_rom asegs) v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK) as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold vtr2b_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := vtr2b_E R v sp1 b len src x k 0 (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) in *. unfold vtr2b_E in Ev.
    vt_p2_close HR HR' Ev Hlf Hms.
  - idtac.
    assert (HR : regs_ok (vtr2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) vtr2d_sr R)
      by (unfold vtr2d_E, vtr2d_sr; rw_seedB).
    assert (HK : know_ok bsegs (vtr2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) m vtr2d_A_knF)
      by (unfold vtr2d_E; vt_knowF).
    destruct (vtr2d_A_run fx R m (seg_rom asegs) v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)
                ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK) as (R' & HR' & Hlf & Hms).
    change bsegs with asegs in Hms. unfold vtr2d_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
    set (Ev := vtr2d_E R v sp1 b len src x k j (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) in *. unfold vtr2d_E in Ev.
    vt_p2_close HR HR' Ev Hlf Hms.
Qed.

Definition VK3 : list reg := [3; 4; 22; 23; 24; 25; 26; 27]%bv.
Definition vt_P3 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sp1 e : Z) (x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 2 = wz sp1 -> getr R 8 = wz (v + 8) -> getr R 10 = wz e -> getr R 19 = wz (sh (v + 8)) -> getr R 20 = wz ASHADOW_BASE ->
    rw_cells asegs m (sp1 + 8) (map (fun w => C8 w) [x21; x20; x19; x18; x9; x8; x1]) ->
    LbB_Kit.shk m (v + 8) 0 -> wr_at asegs m (v + 8) 8 ->
    2 ^ 45 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> 0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> (v + 24 <= sp1 \/ sp1 + 64 <= v) ->
    4 < e < 2 ^ 64 -> e mod 4 = 0 ->
    exists R' M3,
      CatSim.msteps asegs (MS R F (wz VOT_SRET) fc None m (seg_rom asegs)) (MS R' F (wz VOT_RET) fc None M3 (seg_rom asegs))
      /\ munch [(v + 8, v + 16)] m M3 /\ wmono asegs m M3 /\ rw_cells asegs M3 (v + 8) [C8 (wz e)]
      /\ getr R' 1 = x1 /\ getr R' 2 = wz (sp1 + 64) /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 18 = x18
      /\ getr R' 19 = x19 /\ getr R' 20 = x20 /\ getr R' 21 = x21
      /\ (forall r, In r VK3 -> getr R' r = getr R r).

Lemma vt_P3_ok : vt_P3.
Proof.
  intros R F fc m v sp1 e x21 x20 x19 x18 x9 x8 x1 H2 H8 H10 H19 H20 HFR HS8 HW8 Hs1 Hs2 Hv1 Hv2 Hvd He He4.
  set (fx := PropExec.mkFP F fc).
  pose proof (vt_wrange x1) as B1. pose proof (vt_wrange x8) as B8. pose proof (vt_wrange x9) as B9.
  pose proof (vt_wrange x18) as B18. pose proof (vt_wrange x19) as B19. pose proof (vt_wrange x20) as B20.
  pose proof (vt_wrange x21) as B21.
  stash_disjB.
  assert (HR : regs_ok (vtr3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) vtr3_sr R) by (unfold vtr3_E, vtr3_sr; rw_seedB).
  assert (HK : know_ok bsegs (vtr3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) m vtr3_A_knF) by (unfold vtr3_E; vt_knowF).
  destruct (vtr3_A_run fx R m (seg_rom asegs) v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) ltac:(first [assumption | lia]) HR HK)
    as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold vtr3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := vtr3_E R v sp1 e (bv_unsigned x1) (bv_unsigned x8) (bv_unsigned x9) (bv_unsigned x18) (bv_unsigned x19) (bv_unsigned x20) (bv_unsigned x21)) in *. unfold vtr3_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0%nat]|].
  split; [apply rw_wmono|].
  split.
  { lazymatch goal with |- rw_cells _ (mem_denot _ ?m0 [?e1]) _ _ => change [e1] with ([] ++ e1 :: []) end.
    eapply rw_cells_mem_denot_w;
      [ exact Hlf | apply Forall_nil | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite u64_of_Z by lia; lia
      | eassumption | reflexivity | exact I | evs; reflexivity ]. }
  split; [rrwB HR' (1%bv : reg); vt_wreg|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); vt_wreg|].
  split; [rrwB HR' (9%bv : reg); vt_wreg|].
  split; [rrwB HR' (18%bv : reg); vt_wreg|].
  split; [rrwB HR' (19%bv : reg); vt_wreg|].
  split; [rrwB HR' (20%bv : reg); vt_wreg|].
  split; [rrwB HR' (21%bv : reg); vt_wreg|].
  keptB HR HR' VK3.
Qed.
