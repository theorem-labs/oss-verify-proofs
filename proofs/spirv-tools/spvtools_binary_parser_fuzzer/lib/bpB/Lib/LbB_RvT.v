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

Definition t1_E (R : bvmap 5 word) (v k spz b cap n : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 spz; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n].
Definition t1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition t1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWr (SA (EVar 34) (-80)) (ELit 80); KRange (EVar 34) (2 ^ 45 + 80) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 45); KRange (EVar 38) 0 (2 ^ 45); KRange (EVar 33) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-80)) (ELit 80)].
Definition t1_R_dirs : list bool := [true].
Definition t1_R_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912; 968884] (SCR t1_R_dirs [] []) 968584 t1_sr t1_kn 40.
Definition t1_R_x := sym_exec bsegs 400 true [1561912; 968884] (SCR t1_R_dirs [] []) (SS 968584 t1_sr [] t1_R_knF 40) [].
Definition t1_R_ss : sym_state := Eval vm_compute in fst (fst t1_R_x).
Definition t1_R_scs : list sidecond := Eval vm_compute in snd (fst t1_R_x).
Lemma t1_R_eq : t1_R_x = (t1_R_ss, t1_R_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t1_R_pc : s_pc t1_R_ss = 968884.
Proof. reflexivity. Qed.
Lemma t1_R_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap <= 2 ^ 45) -> (0 <= n <= cap) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 80 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k <= 2 ^ 24) -> (k <= cap) ->
  scs_denot bsegs m (t1_E R v k spz b cap n) t1_R_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8. unfold t1_E, t1_R_scs. split_scs.
  - sc_closeB.
Qed.
Lemma t1_R_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap <= 2 ^ 45) -> (0 <= n <= cap) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 80 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k <= 2 ^ 24) -> (k <= cap) ->
  regs_ok (t1_E R v k spz b cap n) t1_sr R -> know_ok bsegs (t1_E R v k spz b cap n) m t1_R_knF ->
  exists R', regs_ok (t1_E R v k spz b cap n) (s_regs t1_R_ss) R' /\ log_flat (t1_E R v k spz b cap n) (s_log t1_R_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968584) m rom)
                    (mkst R' (Z_to_bv 64 968884) (mem_denot (t1_E R v k spz b cap n) m (s_log t1_R_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t1_R_eq HR HK
              (t1_R_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t1_N_dirs : list bool := [false].
Definition t1_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912; 968884] (SCR t1_N_dirs [] []) 968584 t1_sr t1_kn 40.
Definition t1_N_x := sym_exec bsegs 400 true [1561912; 968884] (SCR t1_N_dirs [] []) (SS 968584 t1_sr [] t1_N_knF 40) [].
Definition t1_N_ss : sym_state := Eval vm_compute in fst (fst t1_N_x).
Definition t1_N_scs : list sidecond := Eval vm_compute in snd (fst t1_N_x).
Lemma t1_N_eq : t1_N_x = (t1_N_ss, t1_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t1_N_pc : s_pc t1_N_ss = 1561912.
Proof. reflexivity. Qed.
Lemma t1_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap <= 2 ^ 45) -> (0 <= n <= cap) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 80 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k <= 2 ^ 24) -> (cap < k) ->
  scs_denot bsegs m (t1_E R v k spz b cap n) t1_N_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8. unfold t1_E, t1_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma t1_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap <= 2 ^ 45) -> (0 <= n <= cap) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 80 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k <= 2 ^ 24) -> (cap < k) ->
  regs_ok (t1_E R v k spz b cap n) t1_sr R -> know_ok bsegs (t1_E R v k spz b cap n) m t1_N_knF ->
  exists R', regs_ok (t1_E R v k spz b cap n) (s_regs t1_N_ss) R' /\ log_flat (t1_E R v k spz b cap n) (s_log t1_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968584) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (t1_E R v k spz b cap n) m (s_log t1_N_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t1_N_eq HR HK
              (t1_N_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t3a_E (R : bvmap 5 word) (bn sp v k b cap n : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n].
Definition t3a_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 36); (9%bv, EVar 35); (18%bv, EMd M_MUL (ELit 4) (EVar 36)); (19%bv, EMd M_MUL (ELit 4) (EVar 39))].
Definition t3a_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 37); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 4) (EVar 39))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 4) (EVar 38))); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EVar 33) (-96)) (ELit 96); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 36) 1 (2 ^ 24); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 176); KRange (EVar 38) 1 (2 ^ 24); KRange (EVar 39) 0 (2 ^ 24); KRange (EVar 37) 16 (2 ^ 47)].
Definition t3a_A_dirs : list bool := [false; false].
Definition t3a_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR t3a_A_dirs [] []) 968736 t3a_sr t3a_kn 42.
Definition t3a_A_x := sym_exec bsegs 400 true [770924] (SCR t3a_A_dirs [] []) (SS 968736 t3a_sr [] t3a_A_knF 42) [].
Definition t3a_A_ss : sym_state := Eval vm_compute in fst (fst t3a_A_x).
Definition t3a_A_scs : list sidecond := Eval vm_compute in snd (fst t3a_A_x).
Lemma t3a_A_eq : t3a_A_x = (t3a_A_ss, t3a_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t3a_A_pc : s_pc t3a_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma t3a_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v k b cap n : Z),
  (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (2 ^ 45 + 96 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp - 96 \/ sp + 80 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 80 <= 2147446784 \/ 17594333495296 <= sp - 96) -> (7241728 <= bn) -> (bn + 4 * k <= 2147446784 \/ 17594333495296 <= bn) -> (bn + 4 * k <= sp - 96) -> (0 <= n <= cap) -> (cap < k <= 2 ^ 24) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1 <= cap) ->
  scs_denot bsegs m (t3a_E R bn sp v k b cap n) t3a_A_scs.
Proof.
  intros R m bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17. unfold t3a_E, t3a_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma t3a_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v k b cap n : Z),
  (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (2 ^ 45 + 96 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp - 96 \/ sp + 80 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 80 <= 2147446784 \/ 17594333495296 <= sp - 96) -> (7241728 <= bn) -> (bn + 4 * k <= 2147446784 \/ 17594333495296 <= bn) -> (bn + 4 * k <= sp - 96) -> (0 <= n <= cap) -> (cap < k <= 2 ^ 24) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1 <= cap) ->
  regs_ok (t3a_E R bn sp v k b cap n) t3a_sr R -> know_ok bsegs (t3a_E R bn sp v k b cap n) m t3a_A_knF ->
  exists R', regs_ok (t3a_E R bn sp v k b cap n) (s_regs t3a_A_ss) R' /\ log_flat (t3a_E R bn sp v k b cap n) (s_log t3a_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968736) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (t3a_E R bn sp v k b cap n) m (s_log t3a_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t3a_A_eq HR HK
              (t3a_A_sc R m bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t3b_E (R : bvmap 5 word) (bn sp v k b cap n : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n].
Definition t3b_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 36); (9%bv, EVar 35); (18%bv, EMd M_MUL (ELit 4) (EVar 36)); (19%bv, EMd M_MUL (ELit 4) (EVar 39))].
Definition t3b_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 37); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 4) (EVar 39))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 4) (EVar 38))); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EVar 33) (-96)) (ELit 96); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 36) 1 (2 ^ 24); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 176); KRange (EVar 37) 0 1; KRange (EVar 38) 0 1; KRange (EVar 39) 0 1].
Definition t3b_A_dirs : list bool := [false; false; false; false; true; false; false].
Definition t3b_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR t3b_A_dirs [] []) 968736 t3b_sr t3b_kn 42.
Definition t3b_A_x := sym_exec bsegs 400 true [755076] (SCR t3b_A_dirs [] []) (SS 968736 t3b_sr [] t3b_A_knF 42) [].
Definition t3b_A_ss : sym_state := Eval vm_compute in fst (fst t3b_A_x).
Definition t3b_A_scs : list sidecond := Eval vm_compute in snd (fst t3b_A_x).
Lemma t3b_A_eq : t3b_A_x = (t3b_A_ss, t3b_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t3b_A_pc : s_pc t3b_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma t3b_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v k b cap n : Z),
  (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (2 ^ 45 + 96 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp - 96 \/ sp + 80 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 80 <= 2147446784 \/ 17594333495296 <= sp - 96) -> (7241728 <= bn) -> (bn + 4 * k <= 2147446784 \/ 17594333495296 <= bn) -> (bn + 4 * k <= sp - 96) -> (0 <= n <= cap) -> (cap < k <= 2 ^ 24) -> (b = 0) -> (cap = 0) -> (n = 0) -> (b mod 4 = 0) ->
  scs_denot bsegs m (t3b_E R bn sp v k b cap n) t3b_A_scs.
Proof.
  intros R m bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold t3b_E, t3b_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma t3b_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v k b cap n : Z),
  (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (2 ^ 45 + 96 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (v + 24 <= sp - 96 \/ sp + 80 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 80 <= 2147446784 \/ 17594333495296 <= sp - 96) -> (7241728 <= bn) -> (bn + 4 * k <= 2147446784 \/ 17594333495296 <= bn) -> (bn + 4 * k <= sp - 96) -> (0 <= n <= cap) -> (cap < k <= 2 ^ 24) -> (b = 0) -> (cap = 0) -> (n = 0) -> (b mod 4 = 0) ->
  regs_ok (t3b_E R bn sp v k b cap n) t3b_sr R -> know_ok bsegs (t3b_E R bn sp v k b cap n) m t3b_A_knF ->
  exists R', regs_ok (t3b_E R bn sp v k b cap n) (s_regs t3b_A_ss) R' /\ log_flat (t3b_E R bn sp v k b cap n) (s_log t3b_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968736) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (t3b_E R bn sp v k b cap n) m (s_log t3b_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t3b_A_eq HR HK
              (t3b_A_sc R m bn sp v k b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t5_E (R : bvmap 5 word) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 k; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition t5_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition t5_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-96)) 8 (EVar 50); KWord (SA (EVar 33) (-88)) 8 (EVar 51); KWord (SA (EVar 33) (-80)) 8 (EVar 52); KWord (SA (EVar 33) (-72)) 8 (EVar 53); KWord (SA (EVar 33) (-64)) 8 (EVar 54); KWord (SA (EVar 33) (-56)) 8 (EVar 55); KWord (SA (EVar 33) (-48)) 8 (EVar 56); KWord (SA (EVar 33) (-40)) 8 (EVar 57); KWord (SA (EVar 33) (-32)) 8 (EVar 58); KWord (SA (EVar 33) (-24)) 8 (EVar 59); KWord (SA (EVar 33) (-16)) 8 (EVar 60); KWord (SA (EVar 33) (-8)) 8 (EVar 61)].
Definition t5_A_dirs : list bool := [false].
Definition t5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR t5_A_dirs [] []) 970008 t5_sr t5_kn 40.
Definition t5_A_x := sym_exec bsegs 400 true [755076] (SCR t5_A_dirs [] []) (SS 970008 t5_sr [] t5_A_knF 40) [].
Definition t5_A_ss : sym_state := Eval vm_compute in fst (fst t5_A_x).
Definition t5_A_scs : list sidecond := Eval vm_compute in snd (fst t5_A_x).
Lemma t5_A_eq : t5_A_x = (t5_A_ss, t5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t5_A_pc : s_pc t5_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma t5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) t5_A_scs.
Proof.
  intros R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold t5_E, t5_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma t5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) t5_sr R -> know_ok bsegs (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m t5_A_knF ->
  exists R', regs_ok (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs t5_A_ss) R' /\ log_flat (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log t5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 970008) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (t5_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log t5_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t5_A_eq HR HK
              (t5_A_sc R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t7_E (R : bvmap 5 word) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 k; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition t7_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (21%bv, EVar 38); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition t7_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 40))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-96)) 8 (EVar 50); KWord (SA (EVar 33) (-88)) 8 (EVar 51); KWord (SA (EVar 33) (-80)) 8 (EVar 52); KWord (SA (EVar 33) (-72)) 8 (EVar 53); KWord (SA (EVar 33) (-64)) 8 (EVar 54); KWord (SA (EVar 33) (-56)) 8 (EVar 55); KWord (SA (EVar 33) (-48)) 8 (EVar 56); KWord (SA (EVar 33) (-40)) 8 (EVar 57); KWord (SA (EVar 33) (-32)) 8 (EVar 58); KWord (SA (EVar 33) (-24)) 8 (EVar 59); KWord (SA (EVar 33) (-16)) 8 (EVar 60); KWord (SA (EVar 33) (-8)) 8 (EVar 61)].
Definition t7_A_dirs : list bool := [false; false].
Definition t7_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR t7_A_dirs [] []) 970144 t7_sr t7_kn 40.
Definition t7_A_x := sym_exec bsegs 400 true [770924] (SCR t7_A_dirs [] []) (SS 970144 t7_sr [] t7_A_knF 40) [].
Definition t7_A_ss : sym_state := Eval vm_compute in fst (fst t7_A_x).
Definition t7_A_scs : list sidecond := Eval vm_compute in snd (fst t7_A_x).
Lemma t7_A_eq : t7_A_x = (t7_A_ss, t7_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t7_A_pc : s_pc t7_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma t7_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) t7_A_scs.
Proof.
  intros R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold t7_E, t7_A_scs. split_scs.
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
Lemma t7_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) t7_sr R -> know_ok bsegs (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m t7_A_knF ->
  exists R', regs_ok (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs t7_A_ss) R' /\ log_flat (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log t7_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 970144) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (t7_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log t7_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t7_A_eq HR HK
              (t7_A_sc R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t9_E (R : bvmap 5 word) (bn sp v cap b k : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 k].
Definition t9_sr : list expr := srs sr_id [(2%bv, EVar 33)].
Definition t9_kn : list kentry := [KWord (SA (EVar 33) 0) 8 (EVar 39); KWord (SA (EVar 33) 8) 8 (EVar 39); KWord (SA (EVar 33) 16) 8 (EVar 39); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 33) 32) 8 (EVar 35); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 0 (2 ^ 47)].
Definition t9_D_dirs : list bool := [false].
Definition t9_D_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968860] (SCR t9_D_dirs [] []) 968792 t9_sr t9_kn 60.
Definition t9_D_x := sym_exec bsegs 400 true [1169580; 968860] (SCR t9_D_dirs [] []) (SS 968792 t9_sr [] t9_D_knF 60) [].
Definition t9_D_ss : sym_state := Eval vm_compute in fst (fst t9_D_x).
Definition t9_D_scs : list sidecond := Eval vm_compute in snd (fst t9_D_x).
Lemma t9_D_eq : t9_D_x = (t9_D_ss, t9_D_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t9_D_pc : s_pc t9_D_ss = 1169580.
Proof. reflexivity. Qed.
Lemma t9_D_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v cap b k : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b <> 0) ->
  scs_denot bsegs m (t9_E R bn sp v cap b k) t9_D_scs.
Proof.
  intros R m bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7. unfold t9_E, t9_D_scs. split_scs.
  - sc_closeB.
Qed.
Lemma t9_D_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v cap b k : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b <> 0) ->
  regs_ok (t9_E R bn sp v cap b k) t9_sr R -> know_ok bsegs (t9_E R bn sp v cap b k) m t9_D_knF ->
  exists R', regs_ok (t9_E R bn sp v cap b k) (s_regs t9_D_ss) R' /\ log_flat (t9_E R bn sp v cap b k) (s_log t9_D_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968792) m rom)
                    (mkst R' (Z_to_bv 64 1169580) (mem_denot (t9_E R bn sp v cap b k) m (s_log t9_D_ss)) rom).
Proof.
  intros fx R m rom bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t9_D_eq HR HK
              (t9_D_sc R m bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t9_Z_dirs : list bool := [true].
Definition t9_Z_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968860] (SCR t9_Z_dirs [] []) 968792 t9_sr t9_kn 60.
Definition t9_Z_x := sym_exec bsegs 400 true [1169580; 968860] (SCR t9_Z_dirs [] []) (SS 968792 t9_sr [] t9_Z_knF 60) [].
Definition t9_Z_ss : sym_state := Eval vm_compute in fst (fst t9_Z_x).
Definition t9_Z_scs : list sidecond := Eval vm_compute in snd (fst t9_Z_x).
Lemma t9_Z_eq : t9_Z_x = (t9_Z_ss, t9_Z_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t9_Z_pc : s_pc t9_Z_ss = 968860.
Proof. reflexivity. Qed.
Lemma t9_Z_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v cap b k : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b = 0) ->
  scs_denot bsegs m (t9_E R bn sp v cap b k) t9_Z_scs.
Proof.
  intros R m bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7. unfold t9_E, t9_Z_scs. split_scs.
  - sc_closeB.
Qed.
Lemma t9_Z_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v cap b k : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b = 0) ->
  regs_ok (t9_E R bn sp v cap b k) t9_sr R -> know_ok bsegs (t9_E R bn sp v cap b k) m t9_Z_knF ->
  exists R', regs_ok (t9_E R bn sp v cap b k) (s_regs t9_Z_ss) R' /\ log_flat (t9_E R bn sp v cap b k) (s_log t9_Z_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968792) m rom)
                    (mkst R' (Z_to_bv 64 968860) (mem_denot (t9_E R bn sp v cap b k) m (s_log t9_Z_ss)) rom).
Proof.
  intros fx R m rom bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t9_Z_eq HR HK
              (t9_Z_sc R m bn sp v cap b k H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition t11_E (R : bvmap 5 word) (sp sv1 sv8 sv9 sv18 sv19 : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sv1; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19].
Definition t11_sr : list expr := srs sr_id [(2%bv, EVar 33)].
Definition t11_kn : list kentry := [KWord (SA (EVar 33) 72) 8 (EVar 50); KWord (SA (EVar 33) 64) 8 (EVar 51); KWord (SA (EVar 33) 56) 8 (EVar 52); KWord (SA (EVar 33) 48) 8 (EVar 53); KWord (SA (EVar 33) 40) 8 (EVar 54); KRange (EVar 33) (2 ^ 45) (2 ^ 47)].
Definition t11_A_dirs : list bool := [].
Definition t11_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968884] (SCR t11_A_dirs [] []) 968860 t11_sr t11_kn 60.
Definition t11_A_x := sym_exec bsegs 400 true [968884] (SCR t11_A_dirs [] []) (SS 968860 t11_sr [] t11_A_knF 60) [].
Definition t11_A_ss : sym_state := Eval vm_compute in fst (fst t11_A_x).
Definition t11_A_scs : list sidecond := Eval vm_compute in snd (fst t11_A_x).
Lemma t11_A_eq : t11_A_x = (t11_A_ss, t11_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma t11_A_pc : s_pc t11_A_ss = 968884.
Proof. reflexivity. Qed.
Lemma t11_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sp sv1 sv8 sv9 sv18 sv19 : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) ->
  scs_denot bsegs m (t11_E R sp sv1 sv8 sv9 sv18 sv19) t11_A_scs.
Proof.
  intros R m sp sv1 sv8 sv9 sv18 sv19 H0 H1. unfold t11_E, t11_A_scs. split_scs.
Qed.
Lemma t11_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sp sv1 sv8 sv9 sv18 sv19 : Z),
  (2 ^ 45 <= sp) -> (sp + 80 <= 2 ^ 47) ->
  regs_ok (t11_E R sp sv1 sv8 sv9 sv18 sv19) t11_sr R -> know_ok bsegs (t11_E R sp sv1 sv8 sv9 sv18 sv19) m t11_A_knF ->
  exists R', regs_ok (t11_E R sp sv1 sv8 sv9 sv18 sv19) (s_regs t11_A_ss) R' /\ log_flat (t11_E R sp sv1 sv8 sv9 sv18 sv19) (s_log t11_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968860) m rom)
                    (mkst R' (Z_to_bv 64 968884) (mem_denot (t11_E R sp sv1 sv8 sv9 sv18 sv19) m (s_log t11_A_ss)) rom).
Proof.
  intros fx R m rom sp sv1 sv8 sv9 sv18 sv19 H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R t11_A_eq HR HK
              (t11_A_sc R m sp sv1 sv8 sv9 sv18 sv19 H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
