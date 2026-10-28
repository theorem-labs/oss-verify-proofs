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

Definition r1_E (R : bvmap 5 word) (v k spz b cap n : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 spz; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n].
Definition r1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition r1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KImg 65536 593920; KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWr (SA (EVar 34) (-96)) (ELit 96); KRange (EVar 34) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 43); KRange (EVar 38) 0 (2 ^ 43); KRange (EVar 33) 0 3355443; KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-96)) (ELit 96)].
Definition r1_R_dirs : list bool := [true].
Definition r1_R_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912; 968204] (SCR r1_R_dirs [] []) 967852 r1_sr r1_kn 60.
Definition r1_R_x := sym_exec bsegs 400 true [1561912; 968204] (SCR r1_R_dirs [] []) (SS 967852 r1_sr [] r1_R_knF 60) [].
Definition r1_R_ss : sym_state := Eval vm_compute in fst (fst r1_R_x).
Definition r1_R_scs : list sidecond := Eval vm_compute in snd (fst r1_R_x).
Lemma r1_R_eq : r1_R_x = (r1_R_ss, r1_R_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r1_R_pc : s_pc r1_R_ss = 968204.
Proof. reflexivity. Qed.
Lemma r1_R_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap) -> (0 <= n <= cap) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k) -> (20 * k <= 2 ^ 26) -> (k <= cap) ->
  scs_denot bsegs m (r1_E R v k spz b cap n) r1_R_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold r1_E, r1_R_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r1_R_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap) -> (0 <= n <= cap) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k) -> (20 * k <= 2 ^ 26) -> (k <= cap) ->
  regs_ok (r1_E R v k spz b cap n) r1_sr R -> know_ok bsegs (r1_E R v k spz b cap n) m r1_R_knF ->
  exists R', regs_ok (r1_E R v k spz b cap n) (s_regs r1_R_ss) R' /\ log_flat (r1_E R v k spz b cap n) (s_log r1_R_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 967852) m rom)
                    (mkst R' (Z_to_bv 64 968204) (mem_denot (r1_E R v k spz b cap n) m (s_log r1_R_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r1_R_eq HR HK
              (r1_R_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r1_N_dirs : list bool := [false].
Definition r1_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1561912; 968204] (SCR r1_N_dirs [] []) 967852 r1_sr r1_kn 60.
Definition r1_N_x := sym_exec bsegs 400 true [1561912; 968204] (SCR r1_N_dirs [] []) (SS 967852 r1_sr [] r1_N_knF 60) [].
Definition r1_N_ss : sym_state := Eval vm_compute in fst (fst r1_N_x).
Definition r1_N_scs : list sidecond := Eval vm_compute in snd (fst r1_N_x).
Lemma r1_N_eq : r1_N_x = (r1_N_ss, r1_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r1_N_pc : s_pc r1_N_ss = 1561912.
Proof. reflexivity. Qed.
Lemma r1_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap) -> (0 <= n <= cap) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k) -> (20 * k <= 2 ^ 26) -> (cap < k) ->
  scs_denot bsegs m (r1_E R v k spz b cap n) r1_N_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold r1_E, r1_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r1_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (0 <= cap) -> (0 <= n <= cap) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (2 ^ 45 + 96 <= spz <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= k) -> (20 * k <= 2 ^ 26) -> (cap < k) ->
  regs_ok (r1_E R v k spz b cap n) r1_sr R -> know_ok bsegs (r1_E R v k spz b cap n) m r1_N_knF ->
  exists R', regs_ok (r1_E R v k spz b cap n) (s_regs r1_N_ss) R' /\ log_flat (r1_E R v k spz b cap n) (s_log r1_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 967852) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (r1_E R v k spz b cap n) m (s_log r1_N_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r1_N_eq HR HK
              (r1_N_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r2_E (R : bvmap 5 word) (bn sp v k cap b n : Z) : env := Eseed R [Z_to_bv 64 bn; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 cap; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 n].
Definition r2_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 36); (9%bv, EVar 35); (18%bv, EMd M_MUL (ELit 20) (EVar 36)); (19%bv, ELit 20); (20%bv, EMd M_MUL (ELit 20) (EVar 40))].
Definition r2_kn : list kentry := [KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 37))); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KRange (EVar 36) 1 3355443; KRange (EVar 39) 0 (2 ^ 47); KAlign (EVar 32) 16; KWr (SA (EVar 33) 0) (ELit 96)].
Definition r2_A_dirs : list bool := [false].
Definition r2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968952] (SCR r2_A_dirs [] []) 968036 r2_sr r2_kn 60.
Definition r2_A_x := sym_exec bsegs 400 true [968952] (SCR r2_A_dirs [] []) (SS 968036 r2_sr [] r2_A_knF 60) [].
Definition r2_A_ss : sym_state := Eval vm_compute in fst (fst r2_A_x).
Definition r2_A_scs : list sidecond := Eval vm_compute in snd (fst r2_A_x).
Lemma r2_A_eq : r2_A_x = (r2_A_ss, r2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r2_A_pc : s_pc r2_A_ss = 968952.
Proof. reflexivity. Qed.
Lemma r2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (bn sp v k cap b n : Z),
  (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= n <= cap) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  scs_denot bsegs m (r2_E R bn sp v k cap b n) r2_A_scs.
Proof.
  intros R m bn sp v k cap b n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. unfold r2_E, r2_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (bn sp v k cap b n : Z),
  (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= n <= cap) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (bn mod 16 = 0) ->
  regs_ok (r2_E R bn sp v k cap b n) r2_sr R -> know_ok bsegs (r2_E R bn sp v k cap b n) m r2_A_knF ->
  exists R', regs_ok (r2_E R bn sp v k cap b n) (s_regs r2_A_ss) R' /\ log_flat (r2_E R bn sp v k cap b n) (s_log r2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968036) m rom)
                    (mkst R' (Z_to_bv 64 968952) (mem_denot (r2_E R bn sp v k cap b n) m (s_log r2_A_ss)) rom).
Proof.
  intros fx R m rom bn sp v k cap b n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r2_A_eq HR HK
              (r2_A_sc R m bn sp v k cap b n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h1_E (R : bvmap 5 word) (v sb b cap bn k n : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 k; Z_to_bv 64 n].
Definition h1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-8)))].
Definition h1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 104) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 3355443; KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-104)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-104)) (ELit 144); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32)].
Definition h1_A_dirs : list bool := [false; false; false; false; false].
Definition h1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR h1_A_dirs [] []) 968952 h1_sr h1_kn 70.
Definition h1_A_x := sym_exec bsegs 400 true [770924; 755076] (SCR h1_A_dirs [] []) (SS 968952 h1_sr [] h1_A_knF 70) [].
Definition h1_A_ss : sym_state := Eval vm_compute in fst (fst h1_A_x).
Definition h1_A_scs : list sidecond := Eval vm_compute in snd (fst h1_A_x).
Lemma h1_A_eq : h1_A_x = (h1_A_ss, h1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1_A_pc : s_pc h1_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma h1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) -> (b <> 0) ->
  scs_denot bsegs m (h1_E R v sb b cap bn k n) h1_A_scs.
Proof.
  intros R m v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17. unfold h1_E, h1_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) -> (b <> 0) ->
  regs_ok (h1_E R v sb b cap bn k n) h1_sr R -> know_ok bsegs (h1_E R v sb b cap bn k n) m h1_A_knF ->
  exists R', regs_ok (h1_E R v sb b cap bn k n) (s_regs h1_A_ss) R' /\ log_flat (h1_E R v sb b cap bn k n) (s_log h1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968952) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (h1_E R v sb b cap bn k n) m (s_log h1_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1_A_eq HR HK
              (h1_A_sc R m v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h1_Z_dirs : list bool := [false; false; false; false; true; false].
Definition h1_Z_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR h1_Z_dirs [] []) 968952 h1_sr h1_kn 70.
Definition h1_Z_x := sym_exec bsegs 400 true [770924; 755076] (SCR h1_Z_dirs [] []) (SS 968952 h1_sr [] h1_Z_knF 70) [].
Definition h1_Z_ss : sym_state := Eval vm_compute in fst (fst h1_Z_x).
Definition h1_Z_scs : list sidecond := Eval vm_compute in snd (fst h1_Z_x).
Lemma h1_Z_eq : h1_Z_x = (h1_Z_ss, h1_Z_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1_Z_pc : s_pc h1_Z_ss = 755076.
Proof. reflexivity. Qed.
Lemma h1_Z_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) -> (b = 0) -> (cap = 0) ->
  scs_denot bsegs m (h1_E R v sb b cap bn k n) h1_Z_scs.
Proof.
  intros R m v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h1_E, h1_Z_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h1_Z_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) -> (b = 0) -> (cap = 0) ->
  regs_ok (h1_E R v sb b cap bn k n) h1_sr R -> know_ok bsegs (h1_E R v sb b cap bn k n) m h1_Z_knF ->
  exists R', regs_ok (h1_E R v sb b cap bn k n) (s_regs h1_Z_ss) R' /\ log_flat (h1_E R v sb b cap bn k n) (s_log h1_Z_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968952) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (h1_E R v sb b cap bn k n) m (s_log h1_Z_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1_Z_eq HR HK
              (h1_Z_sc R m v sb b cap bn k n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h2_E (R : bvmap 5 word) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 k; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition h2_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-104))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition h2_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 104) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 3355443; KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-104)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-104)) (ELit 144); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-104)) 8 (EVar 50); KWord (SA (EVar 33) (-96)) 8 (EVar 51); KWord (SA (EVar 33) (-88)) 8 (EVar 52); KWord (SA (EVar 33) (-80)) 8 (EVar 53); KWord (SA (EVar 33) (-72)) 8 (EVar 54); KWord (SA (EVar 33) (-64)) 8 (EVar 55); KWord (SA (EVar 33) (-56)) 8 (EVar 56); KWord (SA (EVar 33) (-48)) 8 (EVar 57); KWord (SA (EVar 33) (-40)) 8 (EVar 58); KWord (SA (EVar 33) (-32)) 8 (EVar 59); KWord (SA (EVar 33) (-24)) 8 (EVar 60); KWord (SA (EVar 33) (-16)) 8 (EVar 61)].
Definition h2_A_dirs : list bool := [false].
Definition h2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR h2_A_dirs [] []) 969148 h2_sr h2_kn 70.
Definition h2_A_x := sym_exec bsegs 400 true [755076] (SCR h2_A_dirs [] []) (SS 969148 h2_sr [] h2_A_knF 70) [].
Definition h2_A_ss : sym_state := Eval vm_compute in fst (fst h2_A_x).
Definition h2_A_scs : list sidecond := Eval vm_compute in snd (fst h2_A_x).
Lemma h2_A_eq : h2_A_x = (h2_A_ss, h2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h2_A_pc : s_pc h2_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma h2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) ->
  scs_denot bsegs m (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) h2_A_scs.
Proof.
  intros R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. unfold h2_E, h2_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma h2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) ->
  regs_ok (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) h2_sr R -> know_ok bsegs (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m h2_A_knF ->
  exists R', regs_ok (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs h2_A_ss) R' /\ log_flat (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log h2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 969148) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (h2_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log h2_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h2_A_eq HR HK
              (h2_A_sc R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3_E (R : bvmap 5 word) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 bn; Z_to_bv 64 k; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9; Z_to_bv 64 hs10; Z_to_bv 64 hs11].
Definition h3_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-104))); (8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (22%bv, ELit 2147450880); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (20%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (21%bv, EVar 38); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880))].
Definition h3_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 0) 8 (EVar 38); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 40))); KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit 20) (EVar 39))); KRange (EVar 33) (2 ^ 45 + 104) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 24); KRange (EVar 38) 1048576 (2 ^ 47); KRange (EVar 39) 1 3355443; KAlign (EVar 38) 16; KAlign (EVar 36) 4; KWr (SA (EVar 33) (-104)) (ELit 96); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-104)) (ELit 144); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) 0) (ELit 32); KWord (SA (EVar 33) (-104)) 8 (EVar 50); KWord (SA (EVar 33) (-96)) 8 (EVar 51); KWord (SA (EVar 33) (-88)) 8 (EVar 52); KWord (SA (EVar 33) (-80)) 8 (EVar 53); KWord (SA (EVar 33) (-72)) 8 (EVar 54); KWord (SA (EVar 33) (-64)) 8 (EVar 55); KWord (SA (EVar 33) (-56)) 8 (EVar 56); KWord (SA (EVar 33) (-48)) 8 (EVar 57); KWord (SA (EVar 33) (-40)) 8 (EVar 58); KWord (SA (EVar 33) (-32)) 8 (EVar 59); KWord (SA (EVar 33) (-24)) 8 (EVar 60); KWord (SA (EVar 33) (-16)) 8 (EVar 61)].
Definition h3_A_dirs : list bool := [false; false].
Definition h3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 969584] (SCR h3_A_dirs [] []) 969252 h3_sr h3_kn 70.
Definition h3_A_x := sym_exec bsegs 400 true [770924; 969584] (SCR h3_A_dirs [] []) (SS 969252 h3_sr [] h3_A_knF 70) [].
Definition h3_A_ss : sym_state := Eval vm_compute in fst (fst h3_A_x).
Definition h3_A_scs : list sidecond := Eval vm_compute in snd (fst h3_A_x).
Lemma h3_A_eq : h3_A_x = (h3_A_ss, h3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3_A_pc : s_pc h3_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma h3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) ->
  scs_denot bsegs m (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) h3_A_scs.
Proof.
  intros R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. unfold h3_E, h3_A_scs. split_scs.
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
Lemma h3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (2 ^ 45 + 104 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 104 \/ sb + 40 <= v) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (1048576 <= bn) -> (bn + 20 * k < 2 ^ 47) -> (cap < k) -> (20 * k <= 2 ^ 26) -> (0 <= n <= cap) -> (bn mod 16 = 0) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 104) ->
  regs_ok (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) h3_sr R -> know_ok bsegs (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m h3_A_knF ->
  exists R', regs_ok (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_regs h3_A_ss) R' /\ log_flat (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) (s_log h3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 969252) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (h3_E R v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m (s_log h3_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3_A_eq HR HK
              (h3_A_sc R m v sb b cap bn k n hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r3_E (R : bvmap 5 word) (sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 cap; Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pv1; Z_to_bv 64 pv8; Z_to_bv 64 pv9; Z_to_bv 64 pv18; Z_to_bv 64 pv19; Z_to_bv 64 pv20].
Definition r3_sr : list expr := srs sr_id [(2%bv, EVar 33)].
Definition r3_kn : list kentry := [KWord (SA (EVar 33) 8) 8 (EVar 39); KWord (SA (EVar 33) 16) 8 (EVar 39); KWord (SA (EVar 33) 24) 8 (EVar 39); KWord (SA (EVar 33) 32) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 20) (EVar 37))); KWord (SA (EVar 33) 40) 8 (EVar 35); KWord (SA (EVar 33) 88) 8 (EVar 50); KWord (SA (EVar 33) 80) 8 (EVar 51); KWord (SA (EVar 33) 72) 8 (EVar 52); KWord (SA (EVar 33) 64) 8 (EVar 53); KWord (SA (EVar 33) 56) 8 (EVar 54); KWord (SA (EVar 33) 48) 8 (EVar 55); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 35) 1048576 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 39) 0 (2 ^ 47); KWr (SA (EVar 33) 0) (ELit 96)].
Definition r3_D_dirs : list bool := [false].
Definition r3_D_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968204] (SCR r3_D_dirs [] []) 968104 r3_sr r3_kn 70.
Definition r3_D_x := sym_exec bsegs 400 true [1169580; 968204] (SCR r3_D_dirs [] []) (SS 968104 r3_sr [] r3_D_knF 70) [].
Definition r3_D_ss : sym_state := Eval vm_compute in fst (fst r3_D_x).
Definition r3_D_scs : list sidecond := Eval vm_compute in snd (fst r3_D_x).
Lemma r3_D_eq : r3_D_x = (r3_D_ss, r3_D_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r3_D_pc : s_pc r3_D_ss = 1169580.
Proof. reflexivity. Qed.
Lemma r3_D_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (b <> 0) ->
  scs_denot bsegs m (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) r3_D_scs.
Proof.
  intros R m sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7. unfold r3_E, r3_D_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r3_D_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (b <> 0) ->
  regs_ok (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) r3_sr R -> know_ok bsegs (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) m r3_D_knF ->
  exists R', regs_ok (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) (s_regs r3_D_ss) R' /\ log_flat (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) (s_log r3_D_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968104) m rom)
                    (mkst R' (Z_to_bv 64 1169580) (mem_denot (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) m (s_log r3_D_ss)) rom).
Proof.
  intros fx R m rom sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r3_D_eq HR HK
              (r3_D_sc R m sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r3_N_dirs : list bool := [true].
Definition r3_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968204] (SCR r3_N_dirs [] []) 968104 r3_sr r3_kn 70.
Definition r3_N_x := sym_exec bsegs 400 true [1169580; 968204] (SCR r3_N_dirs [] []) (SS 968104 r3_sr [] r3_N_knF 70) [].
Definition r3_N_ss : sym_state := Eval vm_compute in fst (fst r3_N_x).
Definition r3_N_scs : list sidecond := Eval vm_compute in snd (fst r3_N_x).
Lemma r3_N_eq : r3_N_x = (r3_N_ss, r3_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r3_N_pc : s_pc r3_N_ss = 968204.
Proof. reflexivity. Qed.
Lemma r3_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (b = 0) ->
  scs_denot bsegs m (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) r3_N_scs.
Proof.
  intros R m sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7. unfold r3_E, r3_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r3_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) -> (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (0 <= b) -> (b + 20 * cap < 2 ^ 47) -> (b = 0) ->
  regs_ok (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) r3_sr R -> know_ok bsegs (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) m r3_N_knF ->
  exists R', regs_ok (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) (s_regs r3_N_ss) R' /\ log_flat (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) (s_log r3_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968104) m rom)
                    (mkst R' (Z_to_bv 64 968204) (mem_denot (r3_E R sp v cap b pv1 pv8 pv9 pv18 pv19 pv20) m (s_log r3_N_ss)) rom).
Proof.
  intros fx R m rom sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r3_N_eq HR HK
              (r3_N_sc R m sp v cap b pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r9_E (R : bvmap 5 word) (sp pv1 pv8 pv9 pv18 pv19 pv20 : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pv1; Z_to_bv 64 pv8; Z_to_bv 64 pv9; Z_to_bv 64 pv18; Z_to_bv 64 pv19; Z_to_bv 64 pv20].
Definition r9_sr : list expr := srs sr_id [(2%bv, EVar 33)].
Definition r9_kn : list kentry := [KWord (SA (EVar 33) 88) 8 (EVar 50); KWord (SA (EVar 33) 80) 8 (EVar 51); KWord (SA (EVar 33) 72) 8 (EVar 52); KWord (SA (EVar 33) 64) 8 (EVar 53); KWord (SA (EVar 33) 56) 8 (EVar 54); KWord (SA (EVar 33) 48) 8 (EVar 55); KRange (EVar 33) (2 ^ 45) (2 ^ 47)].
Definition r9_A_dirs : list bool := [].
Definition r9_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968204] (SCR r9_A_dirs [] []) 968176 r9_sr r9_kn 70.
Definition r9_A_x := sym_exec bsegs 400 true [968204] (SCR r9_A_dirs [] []) (SS 968176 r9_sr [] r9_A_knF 70) [].
Definition r9_A_ss : sym_state := Eval vm_compute in fst (fst r9_A_x).
Definition r9_A_scs : list sidecond := Eval vm_compute in snd (fst r9_A_x).
Lemma r9_A_eq : r9_A_x = (r9_A_ss, r9_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r9_A_pc : s_pc r9_A_ss = 968204.
Proof. reflexivity. Qed.
Lemma r9_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sp pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) ->
  scs_denot bsegs m (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) r9_A_scs.
Proof.
  intros R m sp pv1 pv8 pv9 pv18 pv19 pv20 H0 H1. unfold r9_E, r9_A_scs. split_scs.
Qed.
Lemma r9_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sp pv1 pv8 pv9 pv18 pv19 pv20 : Z),
  (2 ^ 45 <= sp) -> (sp + 96 <= 2 ^ 47) ->
  regs_ok (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) r9_sr R -> know_ok bsegs (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) m r9_A_knF ->
  exists R', regs_ok (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) (s_regs r9_A_ss) R' /\ log_flat (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) (s_log r9_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968176) m rom)
                    (mkst R' (Z_to_bv 64 968204) (mem_denot (r9_E R sp pv1 pv8 pv9 pv18 pv19 pv20) m (s_log r9_A_ss)) rom).
Proof.
  intros fx R m rom sp pv1 pv8 pv9 pv18 pv19 pv20 H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r9_A_eq HR HK
              (r9_A_sc R m sp pv1 pv8 pv9 pv18 pv19 pv20 H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
