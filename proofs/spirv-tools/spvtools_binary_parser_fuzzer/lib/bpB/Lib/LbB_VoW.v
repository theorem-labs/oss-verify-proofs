From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HWord HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition vp1_E (R : bvmap 5 word) (v src spz b cap : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap].
Definition vp1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition vp1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KImg 65536 593920; KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWr (SA (EVar 34) (-96)) (ELit 96); KRange (EVar 34) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-96)) (ELit 96)].
Definition vp1_T_dirs : list bool := [false; true; true; false; false].
Definition vp1_T_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912] (SCR vp1_T_dirs [] []) 1033216 vp1_sr vp1_kn 40.
Definition vp1_T_x := sym_exec bsegs 400 true [1561912] (SCR vp1_T_dirs [] []) (SS 1033216 vp1_sr [] vp1_T_knF 40) [].
Definition vp1_T_ss : sym_state := Eval vm_compute in fst (fst vp1_T_x).
Definition vp1_T_scs : list sidecond := Eval vm_compute in snd (fst vp1_T_x).
Lemma vp1_T_eq : vp1_T_x = (vp1_T_ss, vp1_T_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp1_T_pc : s_pc vp1_T_ss = 1561912.
Proof. reflexivity. Qed.
Lemma vp1_T_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 <= cap) ->
  scs_denot bsegs m (vp1_E R v src spz b cap) vp1_T_scs.
Proof.
  intros R m v src spz b cap H0 H1 H2 H3 H4 H5 H6. unfold vp1_E, vp1_T_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma vp1_T_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 <= cap) ->
  regs_ok (vp1_E R v src spz b cap) vp1_sr R -> know_ok bsegs (vp1_E R v src spz b cap) m vp1_T_knF ->
  exists R', regs_ok (vp1_E R v src spz b cap) (s_regs vp1_T_ss) R' /\ log_flat (vp1_E R v src spz b cap) (s_log vp1_T_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033216) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (vp1_E R v src spz b cap) m (s_log vp1_T_ss)) rom).
Proof.
  intros fx R m rom v src spz b cap H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp1_T_eq HR HK
              (vp1_T_sc R m v src spz b cap H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp1_F_dirs : list bool := [false; false; true; false; false].
Definition vp1_F_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912] (SCR vp1_F_dirs [] []) 1033216 vp1_sr vp1_kn 40.
Definition vp1_F_x := sym_exec bsegs 400 true [1561912] (SCR vp1_F_dirs [] []) (SS 1033216 vp1_sr [] vp1_F_knF 40) [].
Definition vp1_F_ss : sym_state := Eval vm_compute in fst (fst vp1_F_x).
Definition vp1_F_scs : list sidecond := Eval vm_compute in snd (fst vp1_F_x).
Lemma vp1_F_eq : vp1_F_x = (vp1_F_ss, vp1_F_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp1_F_pc : s_pc vp1_F_ss = 1561912.
Proof. reflexivity. Qed.
Lemma vp1_F_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (cap <= 1) ->
  scs_denot bsegs m (vp1_E R v src spz b cap) vp1_F_scs.
Proof.
  intros R m v src spz b cap H0 H1 H2 H3 H4 H5 H6. unfold vp1_E, vp1_F_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma vp1_F_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (cap <= 1) ->
  regs_ok (vp1_E R v src spz b cap) vp1_sr R -> know_ok bsegs (vp1_E R v src spz b cap) m vp1_F_knF ->
  exists R', regs_ok (vp1_E R v src spz b cap) (s_regs vp1_F_ss) R' /\ log_flat (vp1_E R v src spz b cap) (s_log vp1_F_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033216) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (vp1_E R v src spz b cap) m (s_log vp1_F_ss)) rom).
Proof.
  intros fx R m rom v src spz b cap H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp1_F_eq HR HK
              (vp1_F_sc R m v src spz b cap H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp3_E (R : bvmap 5 word) (bn sp v src cap b nc : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 nc].
Definition vp3_sr : list expr := srs sr_id [(10%bv, EVar 32); (21%bv, EVar 37); (2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (19%bv, EVar 41); (20%bv, EMd M_MUL (ELit 20) (EVar 38))].
Definition vp3_kn : list kentry := [KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 33) 32) 8 (EVar 35); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 39) 0 (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 33) 0) (ELit 96)].
Definition vp3_A_dirs : list bool := [true; false; false].
Definition vp3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR vp3_A_dirs [] []) 1033464 vp3_sr vp3_kn 42.
Definition vp3_A_x := sym_exec bsegs 400 true [755076] (SCR vp3_A_dirs [] []) (SS 1033464 vp3_sr [] vp3_A_knF 42) [].
Definition vp3_A_ss : sym_state := Eval vm_compute in fst (fst vp3_A_x).
Definition vp3_A_scs : list sidecond := Eval vm_compute in snd (fst vp3_A_x).
Lemma vp3_A_eq : vp3_A_x = (vp3_A_ss, vp3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp3_A_pc : s_pc vp3_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma vp3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  scs_denot bsegs m (vp3_E R bn sp v src cap b nc) vp3_A_scs.
Proof.
  intros R m bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold vp3_E, vp3_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma vp3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  regs_ok (vp3_E R bn sp v src cap b nc) vp3_sr R -> know_ok bsegs (vp3_E R bn sp v src cap b nc) m vp3_A_knF ->
  exists R', regs_ok (vp3_E R bn sp v src cap b nc) (s_regs vp3_A_ss) R' /\ log_flat (vp3_E R bn sp v src cap b nc) (s_log vp3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033464) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (vp3_E R bn sp v src cap b nc) m (s_log vp3_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp3_A_eq HR HK
              (vp3_A_sc R m bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp4_E (R : bvmap 5 word) (bn sp v src cap b nc : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 nc].
Definition vp4_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (19%bv, EVar 41); (20%bv, EMd M_MUL (ELit 20) (EVar 38))].
Definition vp4_kn : list kentry := [KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 33) 0) 8 (EVar 32); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 41))); KWord (SA (EVar 33) 32) 8 (EVar 35); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 39) 0 (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 33) 0) (ELit 96)].
Definition vp4_A_dirs : list bool := [].
Definition vp4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968952] (SCR vp4_A_dirs [] []) 1033608 vp4_sr vp4_kn 42.
Definition vp4_A_x := sym_exec bsegs 400 true [968952] (SCR vp4_A_dirs [] []) (SS 1033608 vp4_sr [] vp4_A_knF 42) [].
Definition vp4_A_ss : sym_state := Eval vm_compute in fst (fst vp4_A_x).
Definition vp4_A_scs : list sidecond := Eval vm_compute in snd (fst vp4_A_x).
Lemma vp4_A_eq : vp4_A_x = (vp4_A_ss, vp4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp4_A_pc : s_pc vp4_A_ss = 968952.
Proof. reflexivity. Qed.
Lemma vp4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  scs_denot bsegs m (vp4_E R bn sp v src cap b nc) vp4_A_scs.
Proof.
  intros R m bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. unfold vp4_E, vp4_A_scs. split_scs.
Qed.
Lemma vp4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  regs_ok (vp4_E R bn sp v src cap b nc) vp4_sr R -> know_ok bsegs (vp4_E R bn sp v src cap b nc) m vp4_A_knF ->
  exists R', regs_ok (vp4_E R bn sp v src cap b nc) (s_regs vp4_A_ss) R' /\ log_flat (vp4_E R bn sp v src cap b nc) (s_log vp4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033608) m rom)
                    (mkst R' (Z_to_bv 64 968952) (mem_denot (vp4_E R bn sp v src cap b nc) m (s_log vp4_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp4_A_eq HR HK
              (vp4_A_sc R m bn sp v src cap b nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp5_E (R : bvmap 5 word) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pv1; Z_to_bv 64 pv8; Z_to_bv 64 pv9; Z_to_bv 64 pv18; Z_to_bv 64 pv19; Z_to_bv 64 pv20; Z_to_bv 64 pv21].
Definition vp5_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (19%bv, EVar 41); (20%bv, EMd M_MUL (ELit 20) (EVar 38))].
Definition vp5_kn : list kentry := [KWord (SA (EVar 35) 0) 8 (EVar 32); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 38))) (ELit 20)); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 41))); KWord (SA (EVar 33) 0) 8 (EVar 39); KWord (SA (EVar 33) 8) 8 (EVar 39); KWord (SA (EVar 33) 16) 8 (EVar 39); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 33) 32) 8 (EVar 35); KWord (SA (EVar 33) 88) 8 (EVar 50); KWord (SA (EVar 33) 80) 8 (EVar 51); KWord (SA (EVar 33) 72) 8 (EVar 52); KWord (SA (EVar 33) 64) 8 (EVar 53); KWord (SA (EVar 33) 56) 8 (EVar 54); KWord (SA (EVar 33) 48) 8 (EVar 55); KWord (SA (EVar 33) 40) 8 (EVar 56); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 39) 0 (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 33) 0) (ELit 96)].
Definition vp5_D_dirs : list bool := [false].
Definition vp5_D_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 1033764] (SCR vp5_D_dirs [] []) 1033644 vp5_sr vp5_kn 60.
Definition vp5_D_x := sym_exec bsegs 400 true [1169580; 1033764] (SCR vp5_D_dirs [] []) (SS 1033644 vp5_sr [] vp5_D_knF 60) [].
Definition vp5_D_ss : sym_state := Eval vm_compute in fst (fst vp5_D_x).
Definition vp5_D_scs : list sidecond := Eval vm_compute in snd (fst vp5_D_x).
Lemma vp5_D_eq : vp5_D_x = (vp5_D_ss, vp5_D_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp5_D_pc : s_pc vp5_D_ss = 1169580.
Proof. reflexivity. Qed.
Lemma vp5_D_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) -> (b <> 0) ->
  scs_denot bsegs m (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp5_D_scs.
Proof.
  intros R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold vp5_E, vp5_D_scs. split_scs.
  - sc_closeB.
Qed.
Lemma vp5_D_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) -> (b <> 0) ->
  regs_ok (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp5_sr R -> know_ok bsegs (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m vp5_D_knF ->
  exists R', regs_ok (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_regs vp5_D_ss) R' /\ log_flat (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_log vp5_D_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033644) m rom)
                    (mkst R' (Z_to_bv 64 1169580) (mem_denot (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m (s_log vp5_D_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp5_D_eq HR HK
              (vp5_D_sc R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp5_N_dirs : list bool := [true].
Definition vp5_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 1033764] (SCR vp5_N_dirs [] []) 1033644 vp5_sr vp5_kn 60.
Definition vp5_N_x := sym_exec bsegs 400 true [1169580; 1033764] (SCR vp5_N_dirs [] []) (SS 1033644 vp5_sr [] vp5_N_knF 60) [].
Definition vp5_N_ss : sym_state := Eval vm_compute in fst (fst vp5_N_x).
Definition vp5_N_scs : list sidecond := Eval vm_compute in snd (fst vp5_N_x).
Lemma vp5_N_eq : vp5_N_x = (vp5_N_ss, vp5_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp5_N_pc : s_pc vp5_N_ss = 1033764.
Proof. reflexivity. Qed.
Lemma vp5_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) -> (b = 0) ->
  scs_denot bsegs m (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp5_N_scs.
Proof.
  intros R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold vp5_E, vp5_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma vp5_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= src) -> (src + 20 <= 2 ^ 47) -> (src + 20 <= sp \/ sp + 96 <= src) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) -> (b = 0) ->
  regs_ok (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp5_sr R -> know_ok bsegs (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m vp5_N_knF ->
  exists R', regs_ok (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_regs vp5_N_ss) R' /\ log_flat (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_log vp5_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033644) m rom)
                    (mkst R' (Z_to_bv 64 1033764) (mem_denot (vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m (s_log vp5_N_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp5_N_eq HR HK
              (vp5_N_sc R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition vp9_E (R : bvmap 5 word) (bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cap; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pv1; Z_to_bv 64 pv8; Z_to_bv 64 pv9; Z_to_bv 64 pv18; Z_to_bv 64 pv19; Z_to_bv 64 pv20; Z_to_bv 64 pv21].
Definition vp9_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 20) (EVar 38))) (ELit 20))].
Definition vp9_kn : list kentry := [KWord (SA (EVar 33) 88) 8 (EVar 50); KWord (SA (EVar 33) 80) 8 (EVar 51); KWord (SA (EVar 33) 72) 8 (EVar 52); KWord (SA (EVar 33) 64) 8 (EVar 53); KWord (SA (EVar 33) 56) 8 (EVar 54); KWord (SA (EVar 33) 48) 8 (EVar 55); KWord (SA (EVar 33) 40) 8 (EVar 56); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24)].
Definition vp9_A_dirs : list bool := [].
Definition vp9_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1033764] (SCR vp9_A_dirs [] []) 1033728 vp9_sr vp9_kn 60.
Definition vp9_A_x := sym_exec bsegs 400 true [1033764] (SCR vp9_A_dirs [] []) (SS 1033728 vp9_sr [] vp9_A_knF 60) [].
Definition vp9_A_ss : sym_state := Eval vm_compute in fst (fst vp9_A_x).
Definition vp9_A_scs : list sidecond := Eval vm_compute in snd (fst vp9_A_x).
Lemma vp9_A_eq : vp9_A_x = (vp9_A_ss, vp9_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vp9_A_pc : s_pc vp9_A_ss = 1033764.
Proof. reflexivity. Qed.
Lemma vp9_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * cap + 20 < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) ->
  scs_denot bsegs m (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp9_A_scs.
Proof.
  intros R m bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4. unfold vp9_E, vp9_A_scs. split_scs.
Qed.
Lemma vp9_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
  (1048576 <= bn) -> (bn + 20 * cap + 20 < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) ->
  regs_ok (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) vp9_sr R -> know_ok bsegs (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) m vp9_A_knF ->
  exists R', regs_ok (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_regs vp9_A_ss) R' /\ log_flat (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) (s_log vp9_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1033728) m rom)
                    (mkst R' (Z_to_bv 64 1033764) (mem_denot (vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) m (s_log vp9_A_ss)) rom).
Proof.
  intros fx R m rom bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R vp9_A_eq HR HK
              (vp9_A_sc R m bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 H0 H1 H2 H3 H4)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
