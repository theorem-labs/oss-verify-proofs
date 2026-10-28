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

Definition b1_E (R : bvmap 5 word) (v src spz b cap : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 src; Z_to_bv 64 spz; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap].
Definition b1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition b1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWr (SA (EVar 34) (-112)) (ELit 112); KRange (EVar 34) (2 ^ 45 + 112) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-112)) (ELit 112)].
Definition b1_T_dirs : list bool := [true].
Definition b1_T_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912] (SCR b1_T_dirs [] []) 1017628 b1_sr b1_kn 40.
Definition b1_T_x := sym_exec bsegs 400 true [1561912] (SCR b1_T_dirs [] []) (SS 1017628 b1_sr [] b1_T_knF 40) [].
Definition b1_T_ss : sym_state := Eval vm_compute in fst (fst b1_T_x).
Definition b1_T_scs : list sidecond := Eval vm_compute in snd (fst b1_T_x).
Lemma b1_T_eq : b1_T_x = (b1_T_ss, b1_T_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b1_T_pc : s_pc b1_T_ss = 1561912.
Proof. reflexivity. Qed.
Lemma b1_T_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 112 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (cap <= 1) ->
  scs_denot bsegs m (b1_E R v src spz b cap) b1_T_scs.
Proof.
  intros R m v src spz b cap H0 H1 H2 H3 H4 H5 H6. unfold b1_E, b1_T_scs. split_scs.
  - sc_closeB.
Qed.
Lemma b1_T_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 112 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (cap <= 1) ->
  regs_ok (b1_E R v src spz b cap) b1_sr R -> know_ok bsegs (b1_E R v src spz b cap) m b1_T_knF ->
  exists R', regs_ok (b1_E R v src spz b cap) (s_regs b1_T_ss) R' /\ log_flat (b1_E R v src spz b cap) (s_log b1_T_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017628) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (b1_E R v src spz b cap) m (s_log b1_T_ss)) rom).
Proof.
  intros fx R m rom v src spz b cap H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b1_T_eq HR HK
              (b1_T_sc R m v src spz b cap H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b1_F_dirs : list bool := [false; false].
Definition b1_F_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912] (SCR b1_F_dirs [] []) 1017628 b1_sr b1_kn 40.
Definition b1_F_x := sym_exec bsegs 400 true [1561912] (SCR b1_F_dirs [] []) (SS 1017628 b1_sr [] b1_F_knF 40) [].
Definition b1_F_ss : sym_state := Eval vm_compute in fst (fst b1_F_x).
Definition b1_F_scs : list sidecond := Eval vm_compute in snd (fst b1_F_x).
Lemma b1_F_eq : b1_F_x = (b1_F_ss, b1_F_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b1_F_pc : s_pc b1_F_ss = 1561912.
Proof. reflexivity. Qed.
Lemma b1_F_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 112 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 <= cap) ->
  scs_denot bsegs m (b1_E R v src spz b cap) b1_F_scs.
Proof.
  intros R m v src spz b cap H0 H1 H2 H3 H4 H5 H6. unfold b1_E, b1_F_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma b1_F_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v src spz b cap : Z),
  (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (2 ^ 45 + 112 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 <= cap) ->
  regs_ok (b1_E R v src spz b cap) b1_sr R -> know_ok bsegs (b1_E R v src spz b cap) m b1_F_knF ->
  exists R', regs_ok (b1_E R v src spz b cap) (s_regs b1_F_ss) R' /\ log_flat (b1_E R v src spz b cap) (s_log b1_F_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017628) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (b1_E R v src spz b cap) m (s_log b1_F_ss)) rom).
Proof.
  intros fx R m rom v src spz b cap H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b1_F_eq HR HK
              (b1_F_sc R m v src spz b cap H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b3a_E (R : bvmap 5 word) (bn sp v src cap b x nc : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 x; Z_to_bv 64 nc].
Definition b3a_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (23%bv, EVar 35); (9%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EMd M_MUL (ELit 4) (EVar 38)); (22%bv, EVar 41); (18%bv, EMd M_MUL (ELit 4) (EVar 41))].
Definition b3a_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 37) 0) 4 (EVar 40); KWord (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EVar 33) 32) 8 (EVar 35); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) 0) (ELit 4); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 38) 1 (2 ^ 24); KRange (EVar 41) 2 (2 ^ 25); KRange (EVar 39) 16 (2 ^ 47); KRange (EVar 33) (2 ^ 45 + 112) (2 ^ 47); KWr (SA (EVar 33) (-112)) (ELit 112); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-112)) (ELit 224)].
Definition b3a_A_dirs : list bool := [true; false; false; false; false].
Definition b3a_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR b3a_A_dirs [] []) 1017828 b3a_sr b3a_kn 42.
Definition b3a_A_x := sym_exec bsegs 400 true [770924] (SCR b3a_A_dirs [] []) (SS 1017828 b3a_sr [] b3a_A_knF 42) [].
Definition b3a_A_ss : sym_state := Eval vm_compute in fst (fst b3a_A_x).
Definition b3a_A_scs : list sidecond := Eval vm_compute in snd (fst b3a_A_x).
Lemma b3a_A_eq : b3a_A_x = (b3a_A_ss, b3a_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b3a_A_pc : s_pc b3a_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma b3a_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b x nc : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (bn + 4 * nc <= sp - 112) ->
  scs_denot bsegs m (b3a_E R bn sp v src cap b x nc) b3a_A_scs.
Proof.
  intros R m bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21. unfold b3a_E, b3a_A_scs. split_scs.
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
Lemma b3a_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b x nc : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (bn + 4 * nc <= sp - 112) ->
  regs_ok (b3a_E R bn sp v src cap b x nc) b3a_sr R -> know_ok bsegs (b3a_E R bn sp v src cap b x nc) m b3a_A_knF ->
  exists R', regs_ok (b3a_E R bn sp v src cap b x nc) (s_regs b3a_A_ss) R' /\ log_flat (b3a_E R bn sp v src cap b x nc) (s_log b3a_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017828) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (b3a_E R bn sp v src cap b x nc) m (s_log b3a_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b3a_A_eq HR HK
              (b3a_A_sc R m bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b3ak_E (R : bvmap 5 word) (bn sp v src cap b x nc k : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 x; Z_to_bv 64 nc; Z_to_bv 64 k].
Definition b3ak_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (23%bv, EVar 35); (9%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EMd M_MUL (ELit 4) (EVar 38)); (22%bv, EVar 41); (18%bv, EMd M_MUL (ELit 4) (EVar 41))].
Definition b3ak_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 37) 0) 4 (EVar 40); KWord (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) 1 (EVar 42); KWord (SA (EVar 33) 32) 8 (EVar 35); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) 0) (ELit 4); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 38) 1 (2 ^ 24); KRange (EVar 41) 2 (2 ^ 25); KRange (EVar 39) 16 (2 ^ 47); KRange (EVar 33) (2 ^ 45 + 112) (2 ^ 47); KWr (SA (EVar 33) (-112)) (ELit 112); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-112)) (ELit 224); KRange (EVar 42) 4 7; KAlign (EVar 37) 8].
Definition b3ak_A_dirs : list bool := [true; false; false; false; false].
Definition b3ak_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR b3ak_A_dirs [] []) 1017828 b3ak_sr b3ak_kn 43.
Definition b3ak_A_x := sym_exec bsegs 400 true [770924] (SCR b3ak_A_dirs [] []) (SS 1017828 b3ak_sr [] b3ak_A_knF 43) [].
Definition b3ak_A_ss : sym_state := Eval vm_compute in fst (fst b3ak_A_x).
Definition b3ak_A_scs : list sidecond := Eval vm_compute in snd (fst b3ak_A_x).
Lemma b3ak_A_eq : b3ak_A_x = (b3ak_A_ss, b3ak_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b3ak_A_pc : s_pc b3ak_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma b3ak_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b x nc k : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (bn + 4 * nc <= sp - 112) -> (4 <= k <= 7) -> (src mod 8 = 0) ->
  scs_denot bsegs m (b3ak_E R bn sp v src cap b x nc k) b3ak_A_scs.
Proof.
  intros R m bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23. unfold b3ak_E, b3ak_A_scs. split_scs.
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
Lemma b3ak_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b x nc k : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (16 <= b) -> (b + 4 * cap < 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (bn + 4 * nc <= sp - 112) -> (4 <= k <= 7) -> (src mod 8 = 0) ->
  regs_ok (b3ak_E R bn sp v src cap b x nc k) b3ak_sr R -> know_ok bsegs (b3ak_E R bn sp v src cap b x nc k) m b3ak_A_knF ->
  exists R', regs_ok (b3ak_E R bn sp v src cap b x nc k) (s_regs b3ak_A_ss) R' /\ log_flat (b3ak_E R bn sp v src cap b x nc k) (s_log b3ak_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017828) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (b3ak_E R bn sp v src cap b x nc k) m (s_log b3ak_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b3ak_A_eq HR HK
              (b3ak_A_sc R m bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b3b_E (R : bvmap 5 word) (bn sp v src cap b x nc : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 x; Z_to_bv 64 nc].
Definition b3b_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (23%bv, EVar 35); (9%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EMd M_MUL (ELit 4) (EVar 38)); (22%bv, EVar 41); (18%bv, EMd M_MUL (ELit 4) (EVar 41))].
Definition b3b_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 37) 0) 4 (EVar 40); KWord (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) 1 (ELit 0); KWord (SA (EVar 33) 32) 8 (EVar 35); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) 0) (ELit 4); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 33) (2 ^ 45 + 112) (2 ^ 47); KWr (SA (EVar 33) (-112)) (ELit 112); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-112)) (ELit 224); KRange (EVar 39) 0 1; KRange (EVar 38) 0 1; KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) (ELit 3)) 2147450880) 1 (ELit 4)].
Definition b3b_A_dirs : list bool := [true; false; true; false; false; false; false; false; false; true; false; false].
Definition b3b_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR b3b_A_dirs [] []) 1017828 b3b_sr b3b_kn 42.
Definition b3b_A_x := sym_exec bsegs 400 true [755076] (SCR b3b_A_dirs [] []) (SS 1017828 b3b_sr [] b3b_A_knF 42) [].
Definition b3b_A_ss : sym_state := Eval vm_compute in fst (fst b3b_A_x).
Definition b3b_A_scs : list sidecond := Eval vm_compute in snd (fst b3b_A_x).
Lemma b3b_A_eq : b3b_A_x = (b3b_A_ss, b3b_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b3b_A_pc : s_pc b3b_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma b3b_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b x nc : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (b = 0) -> (cap = 0) -> (b mod 4 = 0) -> (bn + 4 * nc <= sp - 112) ->
  scs_denot bsegs m (b3b_E R bn sp v src cap b x nc) b3b_A_scs.
Proof.
  intros R m bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21. unfold b3b_E, b3b_A_scs. split_scs.
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
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma b3b_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b x nc : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (b = 0) -> (cap = 0) -> (b mod 4 = 0) -> (bn + 4 * nc <= sp - 112) ->
  regs_ok (b3b_E R bn sp v src cap b x nc) b3b_sr R -> know_ok bsegs (b3b_E R bn sp v src cap b x nc) m b3b_A_knF ->
  exists R', regs_ok (b3b_E R bn sp v src cap b x nc) (s_regs b3b_A_ss) R' /\ log_flat (b3b_E R bn sp v src cap b x nc) (s_log b3b_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017828) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (b3b_E R bn sp v src cap b x nc) m (s_log b3b_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b3b_A_eq HR HK
              (b3b_A_sc R m bn sp v src cap b x nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b3bk_E (R : bvmap 5 word) (bn sp v src cap b x nc k : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 x; Z_to_bv 64 nc; Z_to_bv 64 k].
Definition b3bk_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (23%bv, EVar 35); (9%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EMd M_MUL (ELit 4) (EVar 38)); (22%bv, EVar 41); (18%bv, EMd M_MUL (ELit 4) (EVar 41))].
Definition b3bk_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 37) 0) 4 (EVar 40); KWord (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) 1 (EVar 42); KWord (SA (EVar 33) 32) 8 (EVar 35); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) 0) (ELit 4); KAlign (EVar 32) 16; KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 33) (2 ^ 45 + 112) (2 ^ 47); KWr (SA (EVar 33) (-112)) (ELit 112); KDisj (SA (EVar 35) 0) (ELit 24) (SA (EVar 33) (-112)) (ELit 224); KRange (EVar 39) 0 1; KRange (EVar 38) 0 1; KRange (EVar 42) 4 7; KAlign (EVar 37) 8; KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) (ELit 3)) 2147450880) 1 (ELit 4)].
Definition b3bk_A_dirs : list bool := [true; false; true; false; false; false; false; false; false; true; false; false].
Definition b3bk_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR b3bk_A_dirs [] []) 1017828 b3bk_sr b3bk_kn 43.
Definition b3bk_A_x := sym_exec bsegs 400 true [755076] (SCR b3bk_A_dirs [] []) (SS 1017828 b3bk_sr [] b3bk_A_knF 43) [].
Definition b3bk_A_ss : sym_state := Eval vm_compute in fst (fst b3bk_A_x).
Definition b3bk_A_scs : list sidecond := Eval vm_compute in snd (fst b3bk_A_x).
Lemma b3bk_A_eq : b3bk_A_x = (b3bk_A_ss, b3bk_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b3bk_A_pc : s_pc b3bk_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma b3bk_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b x nc k : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (b = 0) -> (cap = 0) -> (b mod 4 = 0) -> (bn + 4 * nc <= sp - 112) -> (4 <= k <= 7) -> (src mod 8 = 0) ->
  scs_denot bsegs m (b3bk_E R bn sp v src cap b x nc k) b3bk_A_scs.
Proof.
  intros R m bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23. unfold b3bk_E, b3bk_A_scs. split_scs.
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
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma b3bk_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b x nc k : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 + 112 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= src) -> (src + 4 <= 2 ^ 47) -> (src + 4 <= sp \/ sp + 112 <= src) -> (0 <= x < 2 ^ 32) -> (1 <= nc <= 2 ^ 25) -> (v + 24 <= sp - 112 \/ sp + 112 <= v) -> (bn mod 16 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (7241728 <= bn) -> (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn) -> (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v) -> (b = 0) -> (cap = 0) -> (b mod 4 = 0) -> (bn + 4 * nc <= sp - 112) -> (4 <= k <= 7) -> (src mod 8 = 0) ->
  regs_ok (b3bk_E R bn sp v src cap b x nc k) b3bk_sr R -> know_ok bsegs (b3bk_E R bn sp v src cap b x nc k) m b3bk_A_knF ->
  exists R', regs_ok (b3bk_E R bn sp v src cap b x nc k) (s_regs b3bk_A_ss) R' /\ log_flat (b3bk_E R bn sp v src cap b x nc k) (s_log b3bk_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1017828) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (b3bk_E R bn sp v src cap b x nc k) m (s_log b3bk_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b3bk_A_eq HR HK
              (b3bk_A_sc R m bn sp v src cap b x nc k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b5_E (R : bvmap 5 word) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9].
Definition b5_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (8%bv, EVar 33); (9%bv, EVar 32); (21%bv, ELit 2147450880)].
Definition b5_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 37))) (ELit 4)); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 25); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-96)) 8 (EVar 33); KWord (SA (EVar 33) (-88)) 8 (ELit 956276); KWord (SA (EVar 33) (-80)) 8 (EVar 50); KWord (SA (EVar 33) (-72)) 8 (EVar 51); KWord (SA (EVar 33) (-64)) 8 (EVar 52); KWord (SA (EVar 33) (-56)) 8 (EVar 53); KWord (SA (EVar 33) (-48)) 8 (EVar 54); KWord (SA (EVar 33) (-40)) 8 (EVar 55); KWord (SA (EVar 33) (-32)) 8 (EVar 56); KWord (SA (EVar 33) (-24)) 8 (EVar 57); KWord (SA (EVar 33) (-16)) 8 (EVar 58); KWord (SA (EVar 33) (-8)) 8 (EVar 59)].
Definition b5_A_dirs : list bool := [false].
Definition b5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR b5_A_dirs [] []) 954568 b5_sr b5_kn 60.
Definition b5_A_x := sym_exec bsegs 400 true [755076] (SCR b5_A_dirs [] []) (SS 954568 b5_sr [] b5_A_knF 60) [].
Definition b5_A_ss : sym_state := Eval vm_compute in fst (fst b5_A_x).
Definition b5_A_scs : list sidecond := Eval vm_compute in snd (fst b5_A_x).
Lemma b5_A_eq : b5_A_x = (b5_A_ss, b5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b5_A_pc : s_pc b5_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma b5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) b5_A_scs.
Proof.
  intros R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold b5_E, b5_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma b5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) b5_sr R -> know_ok bsegs (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m b5_A_knF ->
  exists R', regs_ok (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_regs b5_A_ss) R' /\ log_flat (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_log b5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 954568) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m (s_log b5_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b5_A_eq HR HK
              (b5_A_sc R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b7_E (R : bvmap 5 word) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9].
Definition b7_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (8%bv, EVar 33); (9%bv, EVar 32); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (20%bv, EVar 38); (21%bv, ELit 2147450880); (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition b7_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 37))) (ELit 4)); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 4) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 80) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 25); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-80)) (ELit 80); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-80)) (ELit 120); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-80)) 8 (EVar 50); KWord (SA (EVar 33) (-72)) 8 (EVar 51); KWord (SA (EVar 33) (-64)) 8 (EVar 52); KWord (SA (EVar 33) (-56)) 8 (EVar 53); KWord (SA (EVar 33) (-48)) 8 (EVar 54); KWord (SA (EVar 33) (-40)) 8 (EVar 55); KWord (SA (EVar 33) (-32)) 8 (EVar 56); KWord (SA (EVar 33) (-24)) 8 (EVar 57); KWord (SA (EVar 33) (-16)) 8 (EVar 58); KWord (SA (EVar 33) (-8)) 8 (EVar 59)].
Definition b7_A_dirs : list bool := [false; false; false].
Definition b7_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR b7_A_dirs [] []) 956436 b7_sr b7_kn 60.
Definition b7_A_x := sym_exec bsegs 400 true [770924] (SCR b7_A_dirs [] []) (SS 956436 b7_sr [] b7_A_knF 60) [].
Definition b7_A_ss : sym_state := Eval vm_compute in fst (fst b7_A_x).
Definition b7_A_scs : list sidecond := Eval vm_compute in snd (fst b7_A_x).
Lemma b7_A_eq : b7_A_x = (b7_A_ss, b7_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b7_A_pc : s_pc b7_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma b7_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 80 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 80 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80) -> (7241728 <= v) ->
  scs_denot bsegs m (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) b7_A_scs.
Proof.
  intros R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold b7_E, b7_A_scs. split_scs.
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
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma b7_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 80 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 80 \/ sb + 40 <= v) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80) -> (7241728 <= v) ->
  regs_ok (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) b7_sr R -> know_ok bsegs (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m b7_A_knF ->
  exists R', regs_ok (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_regs b7_A_ss) R' /\ log_flat (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_log b7_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 956436) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m (s_log b7_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b7_A_eq HR HK
              (b7_A_sc R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b9_E (R : bvmap 5 word) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 src; Z_to_bv 64 cap; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sv1; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19; Z_to_bv 64 sv20; Z_to_bv 64 sv21; Z_to_bv 64 sv22; Z_to_bv 64 sv23].
Definition b9_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-16))); (8%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (9%bv, EVar 37); (18%bv, EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 41))); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EMd M_MUL (ELit 4) (EVar 38)); (22%bv, EVar 41); (23%bv, EVar 35)].
Definition b9_kn : list kentry := [KWord (SA (EVar 35) 0) 8 (EVar 32); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) (ELit 4)); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 41))); KWord (SA (EVar 33) 0) 8 (EVar 39); KWord (SA (EVar 33) 8) 8 (EVar 39); KWord (SA (EVar 33) 16) 8 (EVar 39); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 33) 32) 8 (EVar 35); KWord (SA (EVar 33) 104) 8 (EVar 50); KWord (SA (EVar 33) 96) 8 (EVar 51); KWord (SA (EVar 33) 88) 8 (EVar 52); KWord (SA (EVar 33) 80) 8 (EVar 53); KWord (SA (EVar 33) 72) 8 (EVar 54); KWord (SA (EVar 33) 64) 8 (EVar 55); KWord (SA (EVar 33) 56) 8 (EVar 56); KWord (SA (EVar 33) 48) 8 (EVar 57); KWord (SA (EVar 33) 40) 8 (EVar 58); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 41) 1 (2 ^ 25); KRange (EVar 39) 0 (2 ^ 47); KWr (SA (EVar 33) 0) (ELit 112); KWord (SA (EVar 33) (-8)) 8 (ELit 1018032); KWord (SA (EVar 33) (-16)) 8 (EAlu ALU_ADD (EVar 35) (ELit 8))].
Definition b9_D_dirs : list bool := [false].
Definition b9_D_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 1018112] (SCR b9_D_dirs [] []) 958128 b9_sr b9_kn 60.
Definition b9_D_x := sym_exec bsegs 400 true [1169580; 1018112] (SCR b9_D_dirs [] []) (SS 958128 b9_sr [] b9_D_knF 60) [].
Definition b9_D_ss : sym_state := Eval vm_compute in fst (fst b9_D_x).
Definition b9_D_scs : list sidecond := Eval vm_compute in snd (fst b9_D_x).
Lemma b9_D_eq : b9_D_x = (b9_D_ss, b9_D_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b9_D_pc : s_pc b9_D_ss = 1169580.
Proof. reflexivity. Qed.
Lemma b9_D_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b <> 0) ->
  scs_denot bsegs m (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b9_D_scs.
Proof.
  intros R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. unfold b9_E, b9_D_scs. split_scs.
  - sc_closeB.
Qed.
Lemma b9_D_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b <> 0) ->
  regs_ok (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b9_sr R -> know_ok bsegs (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m b9_D_knF ->
  exists R', regs_ok (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_regs b9_D_ss) R' /\ log_flat (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_log b9_D_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 958128) m rom)
                    (mkst R' (Z_to_bv 64 1169580) (mem_denot (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m (s_log b9_D_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b9_D_eq HR HK
              (b9_D_sc R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b9_N_dirs : list bool := [true].
Definition b9_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 1018112] (SCR b9_N_dirs [] []) 958128 b9_sr b9_kn 60.
Definition b9_N_x := sym_exec bsegs 400 true [1169580; 1018112] (SCR b9_N_dirs [] []) (SS 958128 b9_sr [] b9_N_knF 60) [].
Definition b9_N_ss : sym_state := Eval vm_compute in fst (fst b9_N_x).
Definition b9_N_scs : list sidecond := Eval vm_compute in snd (fst b9_N_x).
Lemma b9_N_eq : b9_N_x = (b9_N_ss, b9_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b9_N_pc : s_pc b9_N_ss = 1018112.
Proof. reflexivity. Qed.
Lemma b9_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b = 0) ->
  scs_denot bsegs m (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b9_N_scs.
Proof.
  intros R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. unfold b9_E, b9_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma b9_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * nc < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (cap < nc <= 2 ^ 25) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (b = 0) ->
  regs_ok (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b9_sr R -> know_ok bsegs (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m b9_N_knF ->
  exists R', regs_ok (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_regs b9_N_ss) R' /\ log_flat (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_log b9_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 958128) m rom)
                    (mkst R' (Z_to_bv 64 1018112) (mem_denot (b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m (s_log b9_N_ss)) rom).
Proof.
  intros fx R m rom bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b9_N_eq HR HK
              (b9_N_sc R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition b11_E (R : bvmap 5 word) (bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cap; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sv1; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19; Z_to_bv 64 sv20; Z_to_bv 64 sv21; Z_to_bv 64 sv22; Z_to_bv 64 sv23].
Definition b11_sr : list expr := srs sr_id [(2%bv, EVar 33); (8%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 4) (EVar 38))) (ELit 4))].
Definition b11_kn : list kentry := [KWord (SA (EVar 33) 104) 8 (EVar 50); KWord (SA (EVar 33) 96) 8 (EVar 51); KWord (SA (EVar 33) 88) 8 (EVar 52); KWord (SA (EVar 33) 80) 8 (EVar 53); KWord (SA (EVar 33) 72) 8 (EVar 54); KWord (SA (EVar 33) 64) 8 (EVar 55); KWord (SA (EVar 33) 56) 8 (EVar 56); KWord (SA (EVar 33) 48) 8 (EVar 57); KWord (SA (EVar 33) 40) 8 (EVar 58); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24)].
Definition b11_A_dirs : list bool := [].
Definition b11_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1018156] (SCR b11_A_dirs [] []) 1018112 b11_sr b11_kn 60.
Definition b11_A_x := sym_exec bsegs 400 true [1018156] (SCR b11_A_dirs [] []) (SS 1018112 b11_sr [] b11_A_knF 60) [].
Definition b11_A_ss : sym_state := Eval vm_compute in fst (fst b11_A_x).
Definition b11_A_scs : list sidecond := Eval vm_compute in snd (fst b11_A_x).
Lemma b11_A_eq : b11_A_x = (b11_A_ss, b11_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma b11_A_pc : s_pc b11_A_ss = 1018156.
Proof. reflexivity. Qed.
Lemma b11_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * cap + 4 < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) ->
  scs_denot bsegs m (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b11_A_scs.
Proof.
  intros R m bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4. unfold b11_E, b11_A_scs. split_scs.
Qed.
Lemma b11_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
  (1048576 <= bn) -> (bn + 4 * cap + 4 < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 112 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) ->
  regs_ok (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) b11_sr R -> know_ok bsegs (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m b11_A_knF ->
  exists R', regs_ok (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_regs b11_A_ss) R' /\ log_flat (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) (s_log b11_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1018112) m rom)
                    (mkst R' (Z_to_bv 64 1018156) (mem_denot (b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m (s_log b11_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R b11_A_eq HR HK
              (b11_A_sc R m bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 H0 H1 H2 H3 H4)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
