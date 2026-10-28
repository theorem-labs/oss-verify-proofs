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

Definition q1_E (R : bvmap 5 word) (v sb b cap bn nc : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 nc].
Definition q1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 33)].
Definition q1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))) (ELit 20)); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 25); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32)].
Definition q1_A_dirs : list bool := [false; false; false; false; false].
Definition q1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR q1_A_dirs [] []) 968952 q1_sr q1_kn 40.
Definition q1_A_x := sym_exec bsegs 400 true [770924; 755076] (SCR q1_A_dirs [] []) (SS 968952 q1_sr [] q1_A_knF 40) [].
Definition q1_A_ss : sym_state := Eval vm_compute in fst (fst q1_A_x).
Definition q1_A_scs : list sidecond := Eval vm_compute in snd (fst q1_A_x).
Lemma q1_A_eq : q1_A_x = (q1_A_ss, q1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma q1_A_pc : s_pc q1_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma q1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) -> (b <> 0) ->
  scs_denot bsegs m (q1_E R v sb b cap bn nc) q1_A_scs.
Proof.
  intros R m v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold q1_E, q1_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma q1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) -> (b <> 0) ->
  regs_ok (q1_E R v sb b cap bn nc) q1_sr R -> know_ok bsegs (q1_E R v sb b cap bn nc) m q1_A_knF ->
  exists R', regs_ok (q1_E R v sb b cap bn nc) (s_regs q1_A_ss) R' /\ log_flat (q1_E R v sb b cap bn nc) (s_log q1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968952) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (q1_E R v sb b cap bn nc) m (s_log q1_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R q1_A_eq HR HK
              (q1_A_sc R m v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition q1_Z_dirs : list bool := [false; false; false; false; true; false].
Definition q1_Z_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR q1_Z_dirs [] []) 968952 q1_sr q1_kn 40.
Definition q1_Z_x := sym_exec bsegs 400 true [770924; 755076] (SCR q1_Z_dirs [] []) (SS 968952 q1_sr [] q1_Z_knF 40) [].
Definition q1_Z_ss : sym_state := Eval vm_compute in fst (fst q1_Z_x).
Definition q1_Z_scs : list sidecond := Eval vm_compute in snd (fst q1_Z_x).
Lemma q1_Z_eq : q1_Z_x = (q1_Z_ss, q1_Z_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma q1_Z_pc : s_pc q1_Z_ss = 755076.
Proof. reflexivity. Qed.
Lemma q1_Z_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) -> (b = 0) -> (cap = 0) ->
  scs_denot bsegs m (q1_E R v sb b cap bn nc) q1_Z_scs.
Proof.
  intros R m v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. unfold q1_E, q1_Z_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma q1_Z_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) -> (b = 0) -> (cap = 0) ->
  regs_ok (q1_E R v sb b cap bn nc) q1_sr R -> know_ok bsegs (q1_E R v sb b cap bn nc) m q1_Z_knF ->
  exists R', regs_ok (q1_E R v sb b cap bn nc) (s_regs q1_Z_ss) R' /\ log_flat (q1_E R v sb b cap bn nc) (s_log q1_Z_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968952) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (q1_E R v sb b cap bn nc) m (s_log q1_Z_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R q1_Z_eq HR HK
              (q1_Z_sc R m v sb b cap bn nc H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition q2_E (R : bvmap 5 word) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition q2_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition q2_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))) (ELit 20)); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 25); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-96)) 8 (EVar 50); KWord (SA (EVar 33) (-88)) 8 (EVar 51); KWord (SA (EVar 33) (-80)) 8 (EVar 52); KWord (SA (EVar 33) (-72)) 8 (EVar 53); KWord (SA (EVar 33) (-64)) 8 (EVar 54); KWord (SA (EVar 33) (-56)) 8 (EVar 55); KWord (SA (EVar 33) (-48)) 8 (EVar 56); KWord (SA (EVar 33) (-40)) 8 (EVar 57); KWord (SA (EVar 33) (-32)) 8 (EVar 58); KWord (SA (EVar 33) (-24)) 8 (EVar 59); KWord (SA (EVar 33) (-16)) 8 (EVar 60); KWord (SA (EVar 33) (-8)) 8 (EVar 61)].
Definition q2_A_dirs : list bool := [false].
Definition q2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR q2_A_dirs [] []) 969148 q2_sr q2_kn 40.
Definition q2_A_x := sym_exec bsegs 400 true [755076] (SCR q2_A_dirs [] []) (SS 969148 q2_sr [] q2_A_knF 40) [].
Definition q2_A_ss : sym_state := Eval vm_compute in fst (fst q2_A_x).
Definition q2_A_scs : list sidecond := Eval vm_compute in snd (fst q2_A_x).
Lemma q2_A_eq : q2_A_x = (q2_A_ss, q2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma q2_A_pc : s_pc q2_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma q2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) q2_A_scs.
Proof.
  intros R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold q2_E, q2_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma q2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) q2_sr R -> know_ok bsegs (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m q2_A_knF ->
  exists R', regs_ok (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs q2_A_ss) R' /\ log_flat (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log q2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 969148) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log q2_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R q2_A_eq HR HK
              (q2_A_sc R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition q3_E (R : bvmap 5 word) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 nc; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition q3_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (21%bv, EVar 38); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition q3_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 37))) (ELit 20)); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 25); KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-96)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-96)) (ELit 136); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-96)) 8 (EVar 50); KWord (SA (EVar 33) (-88)) 8 (EVar 51); KWord (SA (EVar 33) (-80)) 8 (EVar 52); KWord (SA (EVar 33) (-72)) 8 (EVar 53); KWord (SA (EVar 33) (-64)) 8 (EVar 54); KWord (SA (EVar 33) (-56)) 8 (EVar 55); KWord (SA (EVar 33) (-48)) 8 (EVar 56); KWord (SA (EVar 33) (-40)) 8 (EVar 57); KWord (SA (EVar 33) (-32)) 8 (EVar 58); KWord (SA (EVar 33) (-24)) 8 (EVar 59); KWord (SA (EVar 33) (-16)) 8 (EVar 60); KWord (SA (EVar 33) (-8)) 8 (EVar 61)].
Definition q3_A_dirs : list bool := [false; false].
Definition q3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 969584] (SCR q3_A_dirs [] []) 969252 q3_sr q3_kn 40.
Definition q3_A_x := sym_exec bsegs 400 true [770924; 969584] (SCR q3_A_dirs [] []) (SS 969252 q3_sr [] q3_A_knF 40) [].
Definition q3_A_ss : sym_state := Eval vm_compute in fst (fst q3_A_x).
Definition q3_A_scs : list sidecond := Eval vm_compute in snd (fst q3_A_x).
Lemma q3_A_eq : q3_A_x = (q3_A_ss, q3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma q3_A_pc : s_pc q3_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma q3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) q3_A_scs.
Proof.
  intros R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold q3_E, q3_A_scs. split_scs.
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
Lemma q3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * nc < 2 ^ 47) -> (cap < nc <= 2 ^ 25) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) q3_sr R -> know_ok bsegs (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m q3_A_knF ->
  exists R', regs_ok (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs q3_A_ss) R' /\ log_flat (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log q3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 969252) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log q3_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R q3_A_eq HR HK
              (q3_A_sc R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
