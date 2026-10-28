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
Definition r1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWr (SA (EVar 34) (-80)) (ELit 80); KRange (EVar 34) (2 ^ 45 + 192) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 45); KRange (EVar 38) 0 (2 ^ 45); KRange (EVar 33) 0 (2 ^ 24); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-80)) (ELit 80)].
Definition r1_R_dirs : list bool := [true].
Definition r1_R_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968544; 1561912] (SCR r1_R_dirs [] []) 968244 r1_sr r1_kn 70.
Definition r1_R_x := sym_exec bsegs 400 true [968544; 1561912] (SCR r1_R_dirs [] []) (SS 968244 r1_sr [] r1_R_knF 70) [].
Definition r1_R_ss : sym_state := Eval vm_compute in fst (fst r1_R_x).
Definition r1_R_scs : list sidecond := Eval vm_compute in snd (fst r1_R_x).
Lemma r1_R_eq : r1_R_x = (r1_R_ss, r1_R_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r1_R_pc : s_pc r1_R_ss = 968544.
Proof. reflexivity. Qed.
Lemma r1_R_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 45) -> (0 <= k <= 2 ^ 24) -> (2 ^ 45 + 192 <= spz <= 2 ^ 47) -> (v + 24 <= spz - 80 \/ spz <= v) -> (k <= cap) ->
  scs_denot bsegs m (r1_E R v k spz b cap n) r1_R_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold r1_E, r1_R_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r1_R_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 45) -> (0 <= k <= 2 ^ 24) -> (2 ^ 45 + 192 <= spz <= 2 ^ 47) -> (v + 24 <= spz - 80 \/ spz <= v) -> (k <= cap) ->
  regs_ok (r1_E R v k spz b cap n) r1_sr R -> know_ok bsegs (r1_E R v k spz b cap n) m r1_R_knF ->
  exists R', regs_ok (r1_E R v k spz b cap n) (s_regs r1_R_ss) R' /\ log_flat (r1_E R v k spz b cap n) (s_log r1_R_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968244) m rom)
                    (mkst R' (Z_to_bv 64 968544) (mem_denot (r1_E R v k spz b cap n) m (s_log r1_R_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r1_R_eq HR HK
              (r1_R_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r1_N_dirs : list bool := [false].
Definition r1_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968544; 1561912] (SCR r1_N_dirs [] []) 968244 r1_sr r1_kn 70.
Definition r1_N_x := sym_exec bsegs 400 true [968544; 1561912] (SCR r1_N_dirs [] []) (SS 968244 r1_sr [] r1_N_knF 70) [].
Definition r1_N_ss : sym_state := Eval vm_compute in fst (fst r1_N_x).
Definition r1_N_scs : list sidecond := Eval vm_compute in snd (fst r1_N_x).
Lemma r1_N_eq : r1_N_x = (r1_N_ss, r1_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r1_N_pc : s_pc r1_N_ss = 1561912.
Proof. reflexivity. Qed.
Lemma r1_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k spz b cap n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 45) -> (0 <= k <= 2 ^ 24) -> (2 ^ 45 + 192 <= spz <= 2 ^ 47) -> (v + 24 <= spz - 80 \/ spz <= v) -> (cap < k) ->
  scs_denot bsegs m (r1_E R v k spz b cap n) r1_N_scs.
Proof.
  intros R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold r1_E, r1_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma r1_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k spz b cap n : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 45) -> (0 <= k <= 2 ^ 24) -> (2 ^ 45 + 192 <= spz <= 2 ^ 47) -> (v + 24 <= spz - 80 \/ spz <= v) -> (cap < k) ->
  regs_ok (r1_E R v k spz b cap n) r1_sr R -> know_ok bsegs (r1_E R v k spz b cap n) m r1_N_knF ->
  exists R', regs_ok (r1_E R v k spz b cap n) (s_regs r1_N_ss) R' /\ log_flat (r1_E R v k spz b cap n) (s_log r1_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968244) m rom)
                    (mkst R' (Z_to_bv 64 1561912) (mem_denot (r1_E R v k spz b cap n) m (s_log r1_N_ss)) rom).
Proof.
  intros fx R m rom v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r1_N_eq HR HK
              (r1_N_sc R m v k spz b cap n H0 H1 H2 H3 H4 H5 H6 H7 H8 H9)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r2_E (R : bvmap 5 word) (v k sb n A : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 A].
Definition r2_sr : list expr := srs sr_id [(10%bv, EVar 39); (2%bv, EVar 35); (8%bv, EVar 33); (9%bv, EVar 32); (18%bv, EMd M_MUL (ELit 4) (EVar 33)); (19%bv, EMd M_MUL (ELit 4) (EVar 38))].
Definition r2_kn : list kentry := [KWr (SA (EVar 35) 0) (ELit 32); KRange (EVar 35) (2 ^ 45 + 112) (2 ^ 47); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 1048576 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 24); KAlign (EVar 39) 16].
Definition r2_A_dirs : list bool := [].
Definition r2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [956208] (SCR r2_A_dirs [] []) 968396 r2_sr r2_kn 70.
Definition r2_A_x := sym_exec bsegs 400 true [956208] (SCR r2_A_dirs [] []) (SS 968396 r2_sr [] r2_A_knF 70) [].
Definition r2_A_ss : sym_state := Eval vm_compute in fst (fst r2_A_x).
Definition r2_A_scs : list sidecond := Eval vm_compute in snd (fst r2_A_x).
Lemma r2_A_eq : r2_A_x = (r2_A_ss, r2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r2_A_pc : s_pc r2_A_ss = 956208.
Proof. reflexivity. Qed.
Lemma r2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v k sb n A : Z),
  (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (0 <= n <= k) -> (1 <= k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 80 <= 2 ^ 47) ->
  scs_denot bsegs m (r2_E R v k sb n A) r2_A_scs.
Proof.
  intros R m v k sb n A H0 H1 H2 H3 H4 H5 H6. unfold r2_E, r2_A_scs. split_scs.
Qed.
Lemma r2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v k sb n A : Z),
  (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (0 <= n <= k) -> (1 <= k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 80 <= 2 ^ 47) ->
  regs_ok (r2_E R v k sb n A) r2_sr R -> know_ok bsegs (r2_E R v k sb n A) m r2_A_knF ->
  exists R', regs_ok (r2_E R v k sb n A) (s_regs r2_A_ss) R' /\ log_flat (r2_E R v k sb n A) (s_log r2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968396) m rom)
                    (mkst R' (Z_to_bv 64 956208) (mem_denot (r2_E R v k sb n A) m (s_log r2_A_ss)) rom).
Proof.
  intros fx R m rom v k sb n A H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r2_A_eq HR HK
              (r2_A_sc R m v k sb n A H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h1_E (R : bvmap 5 word) (v sb b cap n A k : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n; Z_to_bv 64 A].
Definition h1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 35); (2%bv, EVar 35)].
Definition h1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 33))); KRange (EVar 35) (2 ^ 45 + 112) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 1048576 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 24); KAlign (EVar 39) 16; KAlign (EVar 36) 4; KWr (SA (EVar 35) (-112)) (ELit 112); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 35) (-112)) (ELit 152)].
Definition h1_A_dirs : list bool := [false; false; false; false; false; false; false].
Definition h1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR h1_A_dirs [] []) 956208 h1_sr h1_kn 70.
Definition h1_A_x := sym_exec bsegs 400 true [770924; 755076] (SCR h1_A_dirs [] []) (SS 956208 h1_sr [] h1_A_knF 70) [].
Definition h1_A_ss : sym_state := Eval vm_compute in fst (fst h1_A_x).
Definition h1_A_scs : list sidecond := Eval vm_compute in snd (fst h1_A_x).
Lemma h1_A_eq : h1_A_x = (h1_A_ss, h1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1_A_pc : s_pc h1_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma h1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap n A k : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 112 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 112) -> (b <> 0) ->
  scs_denot bsegs m (h1_E R v sb b cap n A k) h1_A_scs.
Proof.
  intros R m v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. unfold h1_E, h1_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap n A k : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 112 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 112) -> (b <> 0) ->
  regs_ok (h1_E R v sb b cap n A k) h1_sr R -> know_ok bsegs (h1_E R v sb b cap n A k) m h1_A_knF ->
  exists R', regs_ok (h1_E R v sb b cap n A k) (s_regs h1_A_ss) R' /\ log_flat (h1_E R v sb b cap n A k) (s_log h1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 956208) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (h1_E R v sb b cap n A k) m (s_log h1_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1_A_eq HR HK
              (h1_A_sc R m v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h1_Z_dirs : list bool := [false; false; false; false; false; false; true; false].
Definition h1_Z_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924; 755076] (SCR h1_Z_dirs [] []) 956208 h1_sr h1_kn 70.
Definition h1_Z_x := sym_exec bsegs 400 true [770924; 755076] (SCR h1_Z_dirs [] []) (SS 956208 h1_sr [] h1_Z_knF 70) [].
Definition h1_Z_ss : sym_state := Eval vm_compute in fst (fst h1_Z_x).
Definition h1_Z_scs : list sidecond := Eval vm_compute in snd (fst h1_Z_x).
Lemma h1_Z_eq : h1_Z_x = (h1_Z_ss, h1_Z_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1_Z_pc : s_pc h1_Z_ss = 755076.
Proof. reflexivity. Qed.
Lemma h1_Z_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap n A k : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 112 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 112) -> (b = 0) -> (cap = 0) -> (n = 0) ->
  scs_denot bsegs m (h1_E R v sb b cap n A k) h1_Z_scs.
Proof.
  intros R m v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h1_E, h1_Z_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h1_Z_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap n A k : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 112 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 112 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 112) -> (b = 0) -> (cap = 0) -> (n = 0) ->
  regs_ok (h1_E R v sb b cap n A k) h1_sr R -> know_ok bsegs (h1_E R v sb b cap n A k) m h1_Z_knF ->
  exists R', regs_ok (h1_E R v sb b cap n A k) (s_regs h1_Z_ss) R' /\ log_flat (h1_E R v sb b cap n A k) (s_log h1_Z_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 956208) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (h1_E R v sb b cap n A k) m (s_log h1_Z_ss)) rom).
Proof.
  intros fx R m rom v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1_Z_eq HR HK
              (h1_Z_sc R m v sb b cap n A k H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h2_E (R : bvmap 5 word) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n; Z_to_bv 64 A; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9].
Definition h2_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 35) (ELit (-96))); (8%bv, EVar 35); (9%bv, EVar 32); (21%bv, ELit 2147450880)].
Definition h2_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 33))); KWord (SA (EVar 35) (-96)) 8 (EVar 35); KWord (SA (EVar 35) (-88)) 8 (ELit 956276); KRange (EVar 35) (2 ^ 45 + 96) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 1048576 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 24); KAlign (EVar 39) 16; KAlign (EVar 36) 4; KWord (SA (EVar 35) (-80)) 8 (EVar 50); KWord (SA (EVar 35) (-72)) 8 (EVar 51); KWord (SA (EVar 35) (-64)) 8 (EVar 52); KWord (SA (EVar 35) (-56)) 8 (EVar 53); KWord (SA (EVar 35) (-48)) 8 (EVar 54); KWord (SA (EVar 35) (-40)) 8 (EVar 55); KWord (SA (EVar 35) (-32)) 8 (EVar 56); KWord (SA (EVar 35) (-24)) 8 (EVar 57); KWord (SA (EVar 35) (-16)) 8 (EVar 58); KWord (SA (EVar 35) (-8)) 8 (EVar 59)].
Definition h2_A_dirs : list bool := [false].
Definition h2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [755076] (SCR h2_A_dirs [] []) 954568 h2_sr h2_kn 70.
Definition h2_A_x := sym_exec bsegs 400 true [755076] (SCR h2_A_dirs [] []) (SS 954568 h2_sr [] h2_A_knF 70) [].
Definition h2_A_ss : sym_state := Eval vm_compute in fst (fst h2_A_x).
Definition h2_A_scs : list sidecond := Eval vm_compute in snd (fst h2_A_x).
Lemma h2_A_eq : h2_A_x = (h2_A_ss, h2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h2_A_pc : s_pc h2_A_ss = 755076.
Proof. reflexivity. Qed.
Lemma h2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  scs_denot bsegs m (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) h2_A_scs.
Proof.
  intros R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h2_E, h2_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma h2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 96 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 96 \/ sb + 40 <= v) -> (b mod 4 = 0) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96) ->
  regs_ok (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) h2_sr R -> know_ok bsegs (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m h2_A_knF ->
  exists R', regs_ok (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_regs h2_A_ss) R' /\ log_flat (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_log h2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 954568) m rom)
                    (mkst R' (Z_to_bv 64 755076) (mem_denot (h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m (s_log h2_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h2_A_eq HR HK
              (h2_A_sc R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3_E (R : bvmap 5 word) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 n; Z_to_bv 64 A; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs0; Z_to_bv 64 hs1; Z_to_bv 64 hs2; Z_to_bv 64 hs3; Z_to_bv 64 hs4; Z_to_bv 64 hs5; Z_to_bv 64 hs6; Z_to_bv 64 hs7; Z_to_bv 64 hs8; Z_to_bv 64 hs9].
Definition h3_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 35) (ELit (-80))); (8%bv, EVar 35); (9%bv, EVar 32); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EAlu ALU_ADD (EVar 35) (ELit 8)); (20%bv, EVar 39); (21%bv, ELit 2147450880); (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition h3_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 32) 16) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 0) 8 (EVar 39); KWord (SA (EVar 35) 8) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 16) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 38))); KWord (SA (EVar 35) 24) 8 (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 33))); KRange (EVar 35) (2 ^ 45 + 80) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 1048576 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 24); KAlign (EVar 39) 16; KWr (SA (EVar 35) (-80)) (ELit 80); KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 35) (-80)) (ELit 120); KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 35) 0) (ELit 32); KWord (SA (EVar 35) (-80)) 8 (EVar 50); KWord (SA (EVar 35) (-72)) 8 (EVar 51); KWord (SA (EVar 35) (-64)) 8 (EVar 52); KWord (SA (EVar 35) (-56)) 8 (EVar 53); KWord (SA (EVar 35) (-48)) 8 (EVar 54); KWord (SA (EVar 35) (-40)) 8 (EVar 55); KWord (SA (EVar 35) (-32)) 8 (EVar 56); KWord (SA (EVar 35) (-24)) 8 (EVar 57); KWord (SA (EVar 35) (-16)) 8 (EVar 58); KWord (SA (EVar 35) (-8)) 8 (EVar 59)].
Definition h3_A_dirs : list bool := [false; false; false].
Definition h3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [770924] (SCR h3_A_dirs [] []) 956436 h3_sr h3_kn 70.
Definition h3_A_x := sym_exec bsegs 400 true [770924] (SCR h3_A_dirs [] []) (SS 956436 h3_sr [] h3_A_knF 70) [].
Definition h3_A_ss : sym_state := Eval vm_compute in fst (fst h3_A_x).
Definition h3_A_scs : list sidecond := Eval vm_compute in snd (fst h3_A_x).
Lemma h3_A_eq : h3_A_x = (h3_A_ss, h3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3_A_pc : s_pc h3_A_ss = 770924.
Proof. reflexivity. Qed.
Lemma h3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 80 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 80 \/ sb + 40 <= v) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80) -> (7241728 <= v) ->
  scs_denot bsegs m (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) h3_A_scs.
Proof.
  intros R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h3_E, h3_A_scs. split_scs.
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
Lemma h3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= n <= cap) -> (cap <= 2 ^ 24) -> (1048576 <= A) -> (A + 4 * k < 2 ^ 47) -> (cap < k <= 2 ^ 24) -> (A mod 16 = 0) -> (2 ^ 45 + 80 <= sb) -> (sb + 40 <= 2 ^ 47) -> (v + 24 <= sb - 80 \/ sb + 40 <= v) -> (v + 24 <= 2147446784 \/ 17594333495296 <= v) -> (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80) -> (7241728 <= v) ->
  regs_ok (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) h3_sr R -> know_ok bsegs (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m h3_A_knF ->
  exists R', regs_ok (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_regs h3_A_ss) R' /\ log_flat (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) (s_log h3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 956436) m rom)
                    (mkst R' (Z_to_bv 64 770924) (mem_denot (h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m (s_log h3_A_ss)) rom).
Proof.
  intros fx R m rom v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3_A_eq HR HK
              (h3_A_sc R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h4_E (R : bvmap 5 word) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z) : env := Eseed R [Z_to_bv 64 v; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 b; Z_to_bv 64 cap; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hs8; Z_to_bv 64 0; Z_to_bv 64 sv1; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19].
Definition h4_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 35) (ELit (-16)))].
Definition h4_kn : list kentry := [KWord (SA (EVar 35) (-8)) 8 (ELit 968452); KWord (SA (EVar 35) (-16)) 8 (EVar 58); KWord (SA (EVar 35) 0) 8 (EVar 36); KWord (SA (EVar 35) 8) 8 (EVar 36); KWord (SA (EVar 35) 16) 8 (EVar 36); KWord (SA (EVar 35) 24) 8 (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 37))); KWord (SA (EVar 35) 32) 8 (EVar 32); KWord (SA (EVar 35) 72) 8 (EVar 60); KWord (SA (EVar 35) 64) 8 (EVar 61); KWord (SA (EVar 35) 56) 8 (EVar 62); KWord (SA (EVar 35) 48) 8 (EVar 63); KWord (SA (EVar 35) 40) 8 (EVar 64); KRange (EVar 35) (2 ^ 45 + 16) (2 ^ 47); KRange (EVar 32) 1048576 (2 ^ 47); KRange (EVar 36) 0 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 24)].
Definition h4_D_dirs : list bool := [false].
Definition h4_D_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968544] (SCR h4_D_dirs [] []) 958128 h4_sr h4_kn 70.
Definition h4_D_x := sym_exec bsegs 400 true [1169580; 968544] (SCR h4_D_dirs [] []) (SS 958128 h4_sr [] h4_D_knF 70) [].
Definition h4_D_ss : sym_state := Eval vm_compute in fst (fst h4_D_x).
Definition h4_D_scs : list sidecond := Eval vm_compute in snd (fst h4_D_x).
Lemma h4_D_eq : h4_D_x = (h4_D_ss, h4_D_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h4_D_pc : s_pc h4_D_ss = 1169580.
Proof. reflexivity. Qed.
Lemma h4_D_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (2 ^ 45 + 16 <= sb) -> (sb + 80 <= 2 ^ 47) -> (b <> 0) ->
  scs_denot bsegs m (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) h4_D_scs.
Proof.
  intros R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7. unfold h4_E, h4_D_scs. split_scs.
  - sc_closeB.
Qed.
Lemma h4_D_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (2 ^ 45 + 16 <= sb) -> (sb + 80 <= 2 ^ 47) -> (b <> 0) ->
  regs_ok (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) h4_sr R -> know_ok bsegs (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m h4_D_knF ->
  exists R', regs_ok (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) (s_regs h4_D_ss) R' /\ log_flat (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) (s_log h4_D_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 958128) m rom)
                    (mkst R' (Z_to_bv 64 1169580) (mem_denot (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m (s_log h4_D_ss)) rom).
Proof.
  intros fx R m rom v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h4_D_eq HR HK
              (h4_D_sc R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h4_N_dirs : list bool := [true].
Definition h4_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1169580; 968544] (SCR h4_N_dirs [] []) 958128 h4_sr h4_kn 70.
Definition h4_N_x := sym_exec bsegs 400 true [1169580; 968544] (SCR h4_N_dirs [] []) (SS 958128 h4_sr [] h4_N_knF 70) [].
Definition h4_N_ss : sym_state := Eval vm_compute in fst (fst h4_N_x).
Definition h4_N_scs : list sidecond := Eval vm_compute in snd (fst h4_N_x).
Lemma h4_N_eq : h4_N_x = (h4_N_ss, h4_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h4_N_pc : s_pc h4_N_ss = 968544.
Proof. reflexivity. Qed.
Lemma h4_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (2 ^ 45 + 16 <= sb) -> (sb + 80 <= 2 ^ 47) -> (b = 0) ->
  scs_denot bsegs m (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) h4_N_scs.
Proof.
  intros R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7. unfold h4_E, h4_N_scs. split_scs.
  - sc_closeB.
Qed.
Lemma h4_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
  (1048576 <= v) -> (v + 24 <= 2 ^ 47) -> (0 <= b) -> (b + 4 * cap < 2 ^ 47) -> (0 <= cap <= 2 ^ 24) -> (2 ^ 45 + 16 <= sb) -> (sb + 80 <= 2 ^ 47) -> (b = 0) ->
  regs_ok (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) h4_sr R -> know_ok bsegs (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m h4_N_knF ->
  exists R', regs_ok (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) (s_regs h4_N_ss) R' /\ log_flat (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) (s_log h4_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 958128) m rom)
                    (mkst R' (Z_to_bv 64 968544) (mem_denot (h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m (s_log h4_N_ss)) rom).
Proof.
  intros fx R m rom v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h4_N_eq HR HK
              (h4_N_sc R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 H0 H1 H2 H3 H4 H5 H6 H7)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition r4_E (R : bvmap 5 word) (sb sv1 sv8 sv9 sv18 sv19 : Z) : env := Eseed R [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sb; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sv1; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19].
Definition r4_sr : list expr := srs sr_id [(2%bv, EVar 35)].
Definition r4_kn : list kentry := [KWord (SA (EVar 35) 72) 8 (EVar 60); KWord (SA (EVar 35) 64) 8 (EVar 61); KWord (SA (EVar 35) 56) 8 (EVar 62); KWord (SA (EVar 35) 48) 8 (EVar 63); KWord (SA (EVar 35) 40) 8 (EVar 64); KRange (EVar 35) (2 ^ 45) (2 ^ 47)].
Definition r4_A_dirs : list bool := [].
Definition r4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [968544] (SCR r4_A_dirs [] []) 968520 r4_sr r4_kn 70.
Definition r4_A_x := sym_exec bsegs 400 true [968544] (SCR r4_A_dirs [] []) (SS 968520 r4_sr [] r4_A_knF 70) [].
Definition r4_A_ss : sym_state := Eval vm_compute in fst (fst r4_A_x).
Definition r4_A_scs : list sidecond := Eval vm_compute in snd (fst r4_A_x).
Lemma r4_A_eq : r4_A_x = (r4_A_ss, r4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma r4_A_pc : s_pc r4_A_ss = 968544.
Proof. reflexivity. Qed.
Lemma r4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sb sv1 sv8 sv9 sv18 sv19 : Z),
  (2 ^ 45 <= sb) -> (sb + 80 <= 2 ^ 47) ->
  scs_denot bsegs m (r4_E R sb sv1 sv8 sv9 sv18 sv19) r4_A_scs.
Proof.
  intros R m sb sv1 sv8 sv9 sv18 sv19 H0 H1. unfold r4_E, r4_A_scs. split_scs.
Qed.
Lemma r4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sb sv1 sv8 sv9 sv18 sv19 : Z),
  (2 ^ 45 <= sb) -> (sb + 80 <= 2 ^ 47) ->
  regs_ok (r4_E R sb sv1 sv8 sv9 sv18 sv19) r4_sr R -> know_ok bsegs (r4_E R sb sv1 sv8 sv9 sv18 sv19) m r4_A_knF ->
  exists R', regs_ok (r4_E R sb sv1 sv8 sv9 sv18 sv19) (s_regs r4_A_ss) R' /\ log_flat (r4_E R sb sv1 sv8 sv9 sv18 sv19) (s_log r4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 968520) m rom)
                    (mkst R' (Z_to_bv 64 968544) (mem_denot (r4_E R sb sv1 sv8 sv9 sv18 sv19) m (s_log r4_A_ss)) rom).
Proof.
  intros fx R m rom sb sv1 sv8 sv9 sv18 sv19 H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R r4_A_eq HR HK
              (r4_A_sc R m sb sv1 sv8 sv9 sv18 sv19 H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
