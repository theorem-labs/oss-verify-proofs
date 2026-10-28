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

Definition a0c_E (R : bvmap 5 word) (S1 pp cp : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 pp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cp].
Definition a0c_sr : list expr := srs sr_id [(9%bv, EVar 32); (10%bv, EVar 33)].
Definition a0c_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 33) 0) 8 (EVar 38); KRange (EVar 38) 1 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].
Definition a0c_C_dirs : list bool := [].
Definition a0c_C_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1005944; 1006320] (SCR a0c_C_dirs [] []) 1006292 a0c_sr a0c_kn 60.
Definition a0c_C_x := sym_exec bsegs 40 true [1005944; 1006320] (SCR a0c_C_dirs [] []) (SS 1006292 a0c_sr [] a0c_C_knF 60) [].
Definition a0c_C_ss : sym_state := Eval vm_compute in fst (fst a0c_C_x).
Definition a0c_C_scs : list sidecond := Eval vm_compute in snd (fst a0c_C_x).
Lemma a0c_C_eq : a0c_C_x = (a0c_C_ss, a0c_C_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma a0c_C_pc : s_pc a0c_C_ss = 1005944.
Proof. reflexivity. Qed.
Lemma a0c_C_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pp cp : Z),
  scs_denot bsegs m (a0c_E R S1 pp cp) a0c_C_scs ->
  regs_ok (a0c_E R S1 pp cp) a0c_sr R -> know_ok bsegs (a0c_E R S1 pp cp) m a0c_C_knF ->
  exists R', regs_ok (a0c_E R S1 pp cp) (s_regs a0c_C_ss) R' /\ log_flat (a0c_E R S1 pp cp) (s_log a0c_C_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006292) m rom)
                    (mkst R' (Z_to_bv 64 1005944) (mem_denot (a0c_E R S1 pp cp) m (s_log a0c_C_ss)) rom).
Proof.
  intros fx R m rom S1 pp cp HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R a0c_C_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition a0x_E (R : bvmap 5 word) (S1 pp : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 pp].
Definition a0x_sr : list expr := srs sr_id [(9%bv, EVar 32); (10%bv, EVar 33)].
Definition a0x_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 33) 0) 8 (ELit 0); KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].
Definition a0x_X_dirs : list bool := [].
Definition a0x_X_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1005944; 1006320] (SCR a0x_X_dirs [] []) 1006292 a0x_sr a0x_kn 60.
Definition a0x_X_x := sym_exec bsegs 40 true [1005944; 1006320] (SCR a0x_X_dirs [] []) (SS 1006292 a0x_sr [] a0x_X_knF 60) [].
Definition a0x_X_ss : sym_state := Eval vm_compute in fst (fst a0x_X_x).
Definition a0x_X_scs : list sidecond := Eval vm_compute in snd (fst a0x_X_x).
Lemma a0x_X_eq : a0x_X_x = (a0x_X_ss, a0x_X_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma a0x_X_pc : s_pc a0x_X_ss = 1006320.
Proof. reflexivity. Qed.
Lemma a0x_X_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pp : Z),
  scs_denot bsegs m (a0x_E R S1 pp) a0x_X_scs ->
  regs_ok (a0x_E R S1 pp) a0x_sr R -> know_ok bsegs (a0x_E R S1 pp) m a0x_X_knF ->
  exists R', regs_ok (a0x_E R S1 pp) (s_regs a0x_X_ss) R' /\ log_flat (a0x_E R S1 pp) (s_log a0x_X_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006292) m rom)
                    (mkst R' (Z_to_bv 64 1006320) (mem_denot (a0x_E R S1 pp) m (s_log a0x_X_ss)) rom).
Proof.
  intros fx R m rom S1 pp HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R a0x_X_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition a1_E (R : bvmap 5 word) (S1 pc n cp hv : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pc; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 cp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 hv].
Definition a1_sr : list expr := srs sr_id [(9%bv, EVar 32); (11%bv, EVar 38); (5%bv, ELit 1); (15%bv, EVar 35); (27%bv, EVar 36)].
Definition a1_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KWord (SA (EVar 38) 8) 8 (EVar 43); KRange (EVar 43) 0 (2 ^ 32 - 1); KRange (EVar 35) 2 64; KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].
Definition a1_L_dirs : list bool := [true].
Definition a1_L_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1006004] (SCR a1_L_dirs [] []) 1005944 a1_sr a1_kn 60.
Definition a1_L_x := sym_exec bsegs 40 true [1006004] (SCR a1_L_dirs [] []) (SS 1005944 a1_sr [] a1_L_knF 60) [].
Definition a1_L_ss : sym_state := Eval vm_compute in fst (fst a1_L_x).
Definition a1_L_scs : list sidecond := Eval vm_compute in snd (fst a1_L_x).
Lemma a1_L_eq : a1_L_x = (a1_L_ss, a1_L_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma a1_L_pc : s_pc a1_L_ss = 1006004.
Proof. reflexivity. Qed.
Lemma a1_L_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pc n cp hv : Z),
  scs_denot bsegs m (a1_E R S1 pc n cp hv) a1_L_scs ->
  regs_ok (a1_E R S1 pc n cp hv) a1_sr R -> know_ok bsegs (a1_E R S1 pc n cp hv) m a1_L_knF ->
  exists R', regs_ok (a1_E R S1 pc n cp hv) (s_regs a1_L_ss) R' /\ log_flat (a1_E R S1 pc n cp hv) (s_log a1_L_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005944) m rom)
                    (mkst R' (Z_to_bv 64 1006004) (mem_denot (a1_E R S1 pc n cp hv) m (s_log a1_L_ss)) rom).
Proof.
  intros fx R m rom S1 pc n cp hv HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R a1_L_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition a1_G_dirs : list bool := [false].
Definition a1_G_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1006004] (SCR a1_G_dirs [] []) 1005944 a1_sr a1_kn 60.
Definition a1_G_x := sym_exec bsegs 40 true [1006004] (SCR a1_G_dirs [] []) (SS 1005944 a1_sr [] a1_G_knF 60) [].
Definition a1_G_ss : sym_state := Eval vm_compute in fst (fst a1_G_x).
Definition a1_G_scs : list sidecond := Eval vm_compute in snd (fst a1_G_x).
Lemma a1_G_eq : a1_G_x = (a1_G_ss, a1_G_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma a1_G_pc : s_pc a1_G_ss = 1006004.
Proof. reflexivity. Qed.
Lemma a1_G_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pc n cp hv : Z),
  scs_denot bsegs m (a1_E R S1 pc n cp hv) a1_G_scs ->
  regs_ok (a1_E R S1 pc n cp hv) a1_sr R -> know_ok bsegs (a1_E R S1 pc n cp hv) m a1_G_knF ->
  exists R', regs_ok (a1_E R S1 pc n cp hv) (s_regs a1_G_ss) R' /\ log_flat (a1_E R S1 pc n cp hv) (s_log a1_G_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005944) m rom)
                    (mkst R' (Z_to_bv 64 1006004) (mem_denot (a1_E R S1 pc n cp hv) m (s_log a1_G_ss)) rom).
Proof.
  intros fx R m rom S1 pc n cp hv HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R a1_G_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bs_E (R : bvmap 5 word) (S1 pp p n ph cp ch bv cnx bnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 pp; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 ph; Z_to_bv 64 cp; Z_to_bv 64 ch; Z_to_bv 64 bv; Z_to_bv 64 cnx; Z_to_bv 64 bnx].
Definition bs_sr : list expr := srs sr_id [(9%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 38); (13%bv, EVar 39); (14%bv, EVar 34); (17%bv, EVar 37); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60)); (5%bv, ELit 1); (29%bv, ELit B_SHBASE)].
Definition bs_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KRange (EVar 39) 0 (2 ^ 25); KRange (EVar 37) 0 (2 ^ 25); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KAlign (EVar 33) 8; KRange (EVar 33) 1 (2 ^ 47 - 8)].
Definition bs_S_dirs : list bool := [false].
Definition bs_S_knF : list kentry := Eval vm_compute in kn_fixB 30 80 [1006292] (SCR bs_S_dirs [] []) 1006004 bs_sr bs_kn 60.
Definition bs_S_x := sym_exec bsegs 80 true [1006292] (SCR bs_S_dirs [] []) (SS 1006004 bs_sr [] bs_S_knF 60) [].
Definition bs_S_ss : sym_state := Eval vm_compute in fst (fst bs_S_x).
Definition bs_S_scs : list sidecond := Eval vm_compute in snd (fst bs_S_x).
Lemma bs_S_eq : bs_S_x = (bs_S_ss, bs_S_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bs_S_pc : s_pc bs_S_ss = 1006292.
Proof. reflexivity. Qed.
Lemma bs_S_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pp p n ph cp ch bv cnx bnx : Z),
  scs_denot bsegs m (bs_E R S1 pp p n ph cp ch bv cnx bnx) bs_S_scs ->
  regs_ok (bs_E R S1 pp p n ph cp ch bv cnx bnx) bs_sr R -> know_ok bsegs (bs_E R S1 pp p n ph cp ch bv cnx bnx) m bs_S_knF ->
  exists R', regs_ok (bs_E R S1 pp p n ph cp ch bv cnx bnx) (s_regs bs_S_ss) R' /\ log_flat (bs_E R S1 pp p n ph cp ch bv cnx bnx) (s_log bs_S_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006004) m rom)
                    (mkst R' (Z_to_bv 64 1006292) (mem_denot (bs_E R S1 pp p n ph cp ch bv cnx bnx) m (s_log bs_S_ss)) rom).
Proof.
  intros fx R m rom S1 pp p n ph cp ch bv cnx bnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bs_S_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition be_E (R : bvmap 5 word) (S1 pp p n ph cp ch bv cnx bnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 pp; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 ph; Z_to_bv 64 cp; Z_to_bv 64 ch; Z_to_bv 64 bv; Z_to_bv 64 cnx; Z_to_bv 64 bnx].
Definition be_sr : list expr := srs sr_id [(9%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 38); (13%bv, EVar 39); (14%bv, EVar 34); (17%bv, EVar 37); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60)); (5%bv, ELit 1); (29%bv, ELit B_SHBASE)].
Definition be_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KRange (EVar 39) 0 (2 ^ 25); KRange (EVar 37) 0 (2 ^ 25); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KAlign (EVar 33) 8; KRange (EVar 33) 1 (2 ^ 47 - 8)].
Definition be_E_dirs : list bool := [true; true; true].
Definition be_E_knF : list kentry := Eval vm_compute in kn_fixB 30 80 [1006292] (SCR be_E_dirs [EVar 40] []) 1006004 be_sr be_kn 60.
Definition be_E_x := sym_exec bsegs 80 true [1006292] (SCR be_E_dirs [EVar 40] []) (SS 1006004 be_sr [] be_E_knF 60) [].
Definition be_E_ss : sym_state := Eval vm_compute in fst (fst be_E_x).
Definition be_E_scs : list sidecond := Eval vm_compute in snd (fst be_E_x).
Lemma be_E_eq : be_E_x = (be_E_ss, be_E_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma be_E_pc : s_pc be_E_ss = 1006292.
Proof. reflexivity. Qed.
Lemma be_E_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pp p n ph cp ch bv cnx bnx : Z),
  scs_denot bsegs m (be_E R S1 pp p n ph cp ch bv cnx bnx) be_E_scs ->
  regs_ok (be_E R S1 pp p n ph cp ch bv cnx bnx) be_sr R -> know_ok bsegs (be_E R S1 pp p n ph cp ch bv cnx bnx) m be_E_knF ->
  exists R', regs_ok (be_E R S1 pp p n ph cp ch bv cnx bnx) (s_regs be_E_ss) R' /\ log_flat (be_E R S1 pp p n ph cp ch bv cnx bnx) (s_log be_E_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006004) m rom)
                    (mkst R' (Z_to_bv 64 1006292) (mem_denot (be_E R S1 pp p n ph cp ch bv cnx bnx) m (s_log be_E_ss)) rom).
Proof.
  intros fx R m rom S1 pp p n ph cp ch bv cnx bnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R be_E_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bn_E (R : bvmap 5 word) (S1 pp p n ph cp ch bv cnx bnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 pp; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 ph; Z_to_bv 64 cp; Z_to_bv 64 ch; Z_to_bv 64 bv; Z_to_bv 64 cnx; Z_to_bv 64 bnx].
Definition bn_sr : list expr := srs sr_id [(9%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 38); (13%bv, EVar 39); (14%bv, EVar 34); (17%bv, EVar 37); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60)); (5%bv, ELit 1); (29%bv, ELit B_SHBASE)].
Definition bn_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KRange (EVar 39) 0 (2 ^ 25); KRange (EVar 37) 0 (2 ^ 25); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KAlign (EVar 33) 8; KRange (EVar 33) 1 (2 ^ 47 - 8); KWord (SA (EVar 38) 0) 8 (EVar 41)].
Definition bn_N_dirs : list bool := [true; true; false; true; true; true; true].
Definition bn_N_knF : list kentry := Eval vm_compute in kn_fixB 30 80 [1006292] (SCR bn_N_dirs [EVar 40; EVar 40; EVar 42; EVar 40] []) 1006004 bn_sr bn_kn 60.
Definition bn_N_x := sym_exec bsegs 80 true [1006292] (SCR bn_N_dirs [EVar 40; EVar 40; EVar 42; EVar 40] []) (SS 1006004 bn_sr [] bn_N_knF 60) [].
Definition bn_N_ss : sym_state := Eval vm_compute in fst (fst bn_N_x).
Definition bn_N_scs : list sidecond := Eval vm_compute in snd (fst bn_N_x).
Lemma bn_N_eq : bn_N_x = (bn_N_ss, bn_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bn_N_pc : s_pc bn_N_ss = 1006292.
Proof. reflexivity. Qed.
Lemma bn_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 pp p n ph cp ch bv cnx bnx : Z),
  scs_denot bsegs m (bn_E R S1 pp p n ph cp ch bv cnx bnx) bn_N_scs ->
  regs_ok (bn_E R S1 pp p n ph cp ch bv cnx bnx) bn_sr R -> know_ok bsegs (bn_E R S1 pp p n ph cp ch bv cnx bnx) m bn_N_knF ->
  exists R', regs_ok (bn_E R S1 pp p n ph cp ch bv cnx bnx) (s_regs bn_N_ss) R' /\ log_flat (bn_E R S1 pp p n ph cp ch bv cnx bnx) (s_log bn_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006004) m rom)
                    (mkst R' (Z_to_bv 64 1006292) (mem_denot (bn_E R S1 pp p n ph cp ch bv cnx bnx) m (s_log bn_N_ss)) rom).
Proof.
  intros fx R m rom S1 pp p n ph cp ch bv cnx bnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bn_N_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition pe_E (R : bvmap 5 word) (S1 p n cp hv P np cnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 cp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cnx; Z_to_bv 64 0; Z_to_bv 64 hv; Z_to_bv 64 P; Z_to_bv 64 np].
Definition pe_sr : list expr := srs sr_id [(9%bv, EVar 32); (13%bv, EVar 45); (14%bv, EVar 34); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60))].
Definition pe_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 32) 648) 8 (EVar 44); KRange (EVar 44) 1 (2 ^ 47 - 200); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 2 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 45) (2 ^ 63) (2 ^ 64 - 1); KWord (SA (EVar 44) 152) 8 (ELit 0)].
Definition pe_E_dirs : list bool := [].
Definition pe_E_knF : list kentry := Eval vm_compute in kn_fixB 30 120 [1005944; 1006320] (SCR pe_E_dirs [] []) 1005220 pe_sr pe_kn 60.
Definition pe_E_x := sym_exec bsegs 120 true [1005944; 1006320] (SCR pe_E_dirs [] []) (SS 1005220 pe_sr [] pe_E_knF 60) [].
Definition pe_E_ss : sym_state := Eval vm_compute in fst (fst pe_E_x).
Definition pe_E_scs : list sidecond := Eval vm_compute in snd (fst pe_E_x).
Lemma pe_E_eq : pe_E_x = (pe_E_ss, pe_E_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma pe_E_pc : s_pc pe_E_ss = 1006320.
Proof. reflexivity. Qed.
Lemma pe_E_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 p n cp hv P np cnx : Z),
  scs_denot bsegs m (pe_E R S1 p n cp hv P np cnx) pe_E_scs ->
  regs_ok (pe_E R S1 p n cp hv P np cnx) pe_sr R -> know_ok bsegs (pe_E R S1 p n cp hv P np cnx) m pe_E_knF ->
  exists R', regs_ok (pe_E R S1 p n cp hv P np cnx) (s_regs pe_E_ss) R' /\ log_flat (pe_E R S1 p n cp hv P np cnx) (s_log pe_E_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005220) m rom)
                    (mkst R' (Z_to_bv 64 1006320) (mem_denot (pe_E R S1 p n cp hv P np cnx) m (s_log pe_E_ss)) rom).
Proof.
  intros fx R m rom S1 p n cp hv P np cnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R pe_E_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ps_E (R : bvmap 5 word) (S1 p n cp hv P np cnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 cp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cnx; Z_to_bv 64 0; Z_to_bv 64 hv; Z_to_bv 64 P; Z_to_bv 64 np].
Definition ps_sr : list expr := srs sr_id [(9%bv, EVar 32); (13%bv, EVar 45); (14%bv, EVar 34); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60))].
Definition ps_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 32) 648) 8 (EVar 44); KRange (EVar 44) 1 (2 ^ 47 - 200); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 45) (2 ^ 63) (2 ^ 64 - 1); KWord (SA (EVar 44) 152) 8 (EVar 38); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KWord (SA (EVar 38) 8) 8 (EVar 43); KRange (EVar 43) 0 (2 ^ 32 - 1); KWord (SA (EVar 38) 0) 8 (ELit 0)].
Definition ps_L_dirs : list bool := [true; true].
Definition ps_L_knF : list kentry := Eval vm_compute in kn_fixB 30 160 [1005944; 1006320] (SCR ps_L_dirs [] []) 1005220 ps_sr ps_kn 60.
Definition ps_L_x := sym_exec bsegs 160 true [1005944; 1006320] (SCR ps_L_dirs [] []) (SS 1005220 ps_sr [] ps_L_knF 60) [].
Definition ps_L_ss : sym_state := Eval vm_compute in fst (fst ps_L_x).
Definition ps_L_scs : list sidecond := Eval vm_compute in snd (fst ps_L_x).
Lemma ps_L_eq : ps_L_x = (ps_L_ss, ps_L_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ps_L_pc : s_pc ps_L_ss = 1006320.
Proof. reflexivity. Qed.
Lemma ps_L_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 p n cp hv P np cnx : Z),
  scs_denot bsegs m (ps_E R S1 p n cp hv P np cnx) ps_L_scs ->
  regs_ok (ps_E R S1 p n cp hv P np cnx) ps_sr R -> know_ok bsegs (ps_E R S1 p n cp hv P np cnx) m ps_L_knF ->
  exists R', regs_ok (ps_E R S1 p n cp hv P np cnx) (s_regs ps_L_ss) R' /\ log_flat (ps_E R S1 p n cp hv P np cnx) (s_log ps_L_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005220) m rom)
                    (mkst R' (Z_to_bv 64 1006320) (mem_denot (ps_E R S1 p n cp hv P np cnx) m (s_log ps_L_ss)) rom).
Proof.
  intros fx R m rom S1 p n cp hv P np cnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ps_L_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ps_G_dirs : list bool := [true; false; true].
Definition ps_G_knF : list kentry := Eval vm_compute in kn_fixB 30 160 [1005944; 1006320] (SCR ps_G_dirs [] []) 1005220 ps_sr ps_kn 60.
Definition ps_G_x := sym_exec bsegs 160 true [1005944; 1006320] (SCR ps_G_dirs [] []) (SS 1005220 ps_sr [] ps_G_knF 60) [].
Definition ps_G_ss : sym_state := Eval vm_compute in fst (fst ps_G_x).
Definition ps_G_scs : list sidecond := Eval vm_compute in snd (fst ps_G_x).
Lemma ps_G_eq : ps_G_x = (ps_G_ss, ps_G_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ps_G_pc : s_pc ps_G_ss = 1006320.
Proof. reflexivity. Qed.
Lemma ps_G_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 p n cp hv P np cnx : Z),
  scs_denot bsegs m (ps_E R S1 p n cp hv P np cnx) ps_G_scs ->
  regs_ok (ps_E R S1 p n cp hv P np cnx) ps_sr R -> know_ok bsegs (ps_E R S1 p n cp hv P np cnx) m ps_G_knF ->
  exists R', regs_ok (ps_E R S1 p n cp hv P np cnx) (s_regs ps_G_ss) R' /\ log_flat (ps_E R S1 p n cp hv P np cnx) (s_log ps_G_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005220) m rom)
                    (mkst R' (Z_to_bv 64 1006320) (mem_denot (ps_E R S1 p n cp hv P np cnx) m (s_log ps_G_ss)) rom).
Proof.
  intros fx R m rom S1 p n cp hv P np cnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ps_G_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition pm_E (R : bvmap 5 word) (S1 p n cp hv P np cnx : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 cp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cnx; Z_to_bv 64 0; Z_to_bv 64 hv; Z_to_bv 64 P; Z_to_bv 64 np].
Definition pm_sr : list expr := srs sr_id [(9%bv, EVar 32); (13%bv, EVar 45); (14%bv, EVar 34); (27%bv, EVar 36); (31%bv, ELit (2 ^ 60))].
Definition pm_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 32) 648) 8 (EVar 44); KRange (EVar 44) 1 (2 ^ 47 - 200); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 36) 5 (2 ^ 25); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 45) (2 ^ 63) (2 ^ 64 - 1); KWord (SA (EVar 44) 152) 8 (EVar 38); KAlign (EVar 38) 16; KRange (EVar 38) 1 (2 ^ 47 - 32); KWord (SA (EVar 38) 8) 8 (EVar 43); KRange (EVar 43) 0 (2 ^ 32 - 1); KWord (SA (EVar 38) 0) 8 (EVar 41); KRange (EVar 41) 1 (2 ^ 47)].
Definition pm_L_dirs : list bool := [true; true].
Definition pm_L_knF : list kentry := Eval vm_compute in kn_fixB 30 160 [1005944; 1006320] (SCR pm_L_dirs [] []) 1005220 pm_sr pm_kn 60.
Definition pm_L_x := sym_exec bsegs 160 true [1005944; 1006320] (SCR pm_L_dirs [] []) (SS 1005220 pm_sr [] pm_L_knF 60) [].
Definition pm_L_ss : sym_state := Eval vm_compute in fst (fst pm_L_x).
Definition pm_L_scs : list sidecond := Eval vm_compute in snd (fst pm_L_x).
Lemma pm_L_eq : pm_L_x = (pm_L_ss, pm_L_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma pm_L_pc : s_pc pm_L_ss = 1005944.
Proof. reflexivity. Qed.
Lemma pm_L_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 p n cp hv P np cnx : Z),
  scs_denot bsegs m (pm_E R S1 p n cp hv P np cnx) pm_L_scs ->
  regs_ok (pm_E R S1 p n cp hv P np cnx) pm_sr R -> know_ok bsegs (pm_E R S1 p n cp hv P np cnx) m pm_L_knF ->
  exists R', regs_ok (pm_E R S1 p n cp hv P np cnx) (s_regs pm_L_ss) R' /\ log_flat (pm_E R S1 p n cp hv P np cnx) (s_log pm_L_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005220) m rom)
                    (mkst R' (Z_to_bv 64 1005944) (mem_denot (pm_E R S1 p n cp hv P np cnx) m (s_log pm_L_ss)) rom).
Proof.
  intros fx R m rom S1 p n cp hv P np cnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R pm_L_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition pm_G_dirs : list bool := [true; false; true].
Definition pm_G_knF : list kentry := Eval vm_compute in kn_fixB 30 160 [1005944; 1006320] (SCR pm_G_dirs [] []) 1005220 pm_sr pm_kn 60.
Definition pm_G_x := sym_exec bsegs 160 true [1005944; 1006320] (SCR pm_G_dirs [] []) (SS 1005220 pm_sr [] pm_G_knF 60) [].
Definition pm_G_ss : sym_state := Eval vm_compute in fst (fst pm_G_x).
Definition pm_G_scs : list sidecond := Eval vm_compute in snd (fst pm_G_x).
Lemma pm_G_eq : pm_G_x = (pm_G_ss, pm_G_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma pm_G_pc : s_pc pm_G_ss = 1005944.
Proof. reflexivity. Qed.
Lemma pm_G_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 p n cp hv P np cnx : Z),
  scs_denot bsegs m (pm_E R S1 p n cp hv P np cnx) pm_G_scs ->
  regs_ok (pm_E R S1 p n cp hv P np cnx) pm_sr R -> know_ok bsegs (pm_E R S1 p n cp hv P np cnx) m pm_G_knF ->
  exists R', regs_ok (pm_E R S1 p n cp hv P np cnx) (s_regs pm_G_ss) R' /\ log_flat (pm_E R S1 p n cp hv P np cnx) (s_log pm_G_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1005220) m rom)
                    (mkst R' (Z_to_bv 64 1005944) (mem_denot (pm_E R S1 p n cp hv P np cnx) m (s_log pm_G_ss)) rom).
Proof.
  intros fx R m rom S1 p n cp hv P np cnx HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R pm_G_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition x_E (R : bvmap 5 word) (S1 n ob ky : Z) : env := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 ob; Z_to_bv 64 ky].
Definition x_sr : list expr := srs sr_id [(9%bv, EVar 32); (18%bv, EVar 47)].
Definition x_kn : list kentry := [KWord (SA (EVar 32) 616) 8 (ELit B_SHBASE); KWord (SA (EVar 32) 664) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 46) (ELit 8)) (ELit 3)) (ELit B_SHBASE)); KWord (SA (EVar 32) 632) 8 (EAlu ALU_ADD (EVar 46) (ELit 8)); KWord (SA (EVar 46) 8) 8 (EVar 36); KRange (EVar 46) 1 (2 ^ 47 - 40); KAlign (EVar 46) 8; KRange (EVar 36) 2 (2 ^ 25); KRange (EVar 47) 0 (2 ^ 32 - 1); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].
Definition x_P_dirs : list bool := [false].
Definition x_P_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1006384] (SCR x_P_dirs [] []) 1006320 x_sr x_kn 60.
Definition x_P_x := sym_exec bsegs 40 true [1006384] (SCR x_P_dirs [] []) (SS 1006320 x_sr [] x_P_knF 60) [].
Definition x_P_ss : sym_state := Eval vm_compute in fst (fst x_P_x).
Definition x_P_scs : list sidecond := Eval vm_compute in snd (fst x_P_x).
Lemma x_P_eq : x_P_x = (x_P_ss, x_P_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma x_P_pc : s_pc x_P_ss = 1006384.
Proof. reflexivity. Qed.
Lemma x_P_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 n ob ky : Z),
  scs_denot bsegs m (x_E R S1 n ob ky) x_P_scs ->
  regs_ok (x_E R S1 n ob ky) x_sr R -> know_ok bsegs (x_E R S1 n ob ky) m x_P_knF ->
  exists R', regs_ok (x_E R S1 n ob ky) (s_regs x_P_ss) R' /\ log_flat (x_E R S1 n ob ky) (s_log x_P_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006320) m rom)
                    (mkst R' (Z_to_bv 64 1006384) (mem_denot (x_E R S1 n ob ky) m (s_log x_P_ss)) rom).
Proof.
  intros fx R m rom S1 n ob ky HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R x_P_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition x_L_dirs : list bool := [true; false].
Definition x_L_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1006384] (SCR x_L_dirs [] []) 1006320 x_sr x_kn 60.
Definition x_L_x := sym_exec bsegs 40 true [1006384] (SCR x_L_dirs [] []) (SS 1006320 x_sr [] x_L_knF 60) [].
Definition x_L_ss : sym_state := Eval vm_compute in fst (fst x_L_x).
Definition x_L_scs : list sidecond := Eval vm_compute in snd (fst x_L_x).
Lemma x_L_eq : x_L_x = (x_L_ss, x_L_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma x_L_pc : s_pc x_L_ss = 1006384.
Proof. reflexivity. Qed.
Lemma x_L_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 n ob ky : Z),
  scs_denot bsegs m (x_E R S1 n ob ky) x_L_scs ->
  regs_ok (x_E R S1 n ob ky) x_sr R -> know_ok bsegs (x_E R S1 n ob ky) m x_L_knF ->
  exists R', regs_ok (x_E R S1 n ob ky) (s_regs x_L_ss) R' /\ log_flat (x_E R S1 n ob ky) (s_log x_L_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006320) m rom)
                    (mkst R' (Z_to_bv 64 1006384) (mem_denot (x_E R S1 n ob ky) m (s_log x_L_ss)) rom).
Proof.
  intros fx R m rom S1 n ob ky HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R x_L_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition x_M_dirs : list bool := [true; true].
Definition x_M_knF : list kentry := Eval vm_compute in kn_fixB 30 40 [1006384] (SCR x_M_dirs [] []) 1006320 x_sr x_kn 60.
Definition x_M_x := sym_exec bsegs 40 true [1006384] (SCR x_M_dirs [] []) (SS 1006320 x_sr [] x_M_knF 60) [].
Definition x_M_ss : sym_state := Eval vm_compute in fst (fst x_M_x).
Definition x_M_scs : list sidecond := Eval vm_compute in snd (fst x_M_x).
Lemma x_M_eq : x_M_x = (x_M_ss, x_M_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma x_M_pc : s_pc x_M_ss = 1006384.
Proof. reflexivity. Qed.
Lemma x_M_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (S1 n ob ky : Z),
  scs_denot bsegs m (x_E R S1 n ob ky) x_M_scs ->
  regs_ok (x_E R S1 n ob ky) x_sr R -> know_ok bsegs (x_E R S1 n ob ky) m x_M_knF ->
  exists R', regs_ok (x_E R S1 n ob ky) (s_regs x_M_ss) R' /\ log_flat (x_E R S1 n ob ky) (s_log x_M_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1006320) m rom)
                    (mkst R' (Z_to_bv 64 1006384) (mem_denot (x_E R S1 n ob ky) m (s_log x_M_ss)) rom).
Proof.
  intros fx R m rom S1 n ob ky HS HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R x_M_eq HR HK HS) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
