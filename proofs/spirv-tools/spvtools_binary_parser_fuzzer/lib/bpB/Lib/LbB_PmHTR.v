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

Definition hta_E (R : bvmap 5 word) (p sh fb b e h : Z) : env := Eseed R [Z_to_bv 64 p; Z_to_bv 64 sh; Z_to_bv 64 fb; Z_to_bv 64 b; Z_to_bv 64 e; Z_to_bv 64 h].
Definition hta_sr : list expr := srs sr_id [(9%bv, EVar 34); (18%bv, EVar 32); (19%bv, EVar 33); (25%bv, EVar 35)].
Definition hta_kn : list kentry := [KWord (SA (EVar 32) 88) 4 (EVar 36); KWord (SA (EVar 34) 48) 8 (EVar 37); KDisj (SA (EVar 33) 278) (ELit 4) (SA (EVar 32) 88) (ELit 4); KDisj (SA (EVar 33) 278) (ELit 4) (SA (EVar 34) 48) (ELit 8); KWr (SA (EVar 33) 278) (ELit 4)].
Definition hta_A_dirs : list bool := [false].
Definition hta_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959156] (SCR hta_A_dirs [] []) 966084 hta_sr hta_kn 40.
Definition hta_A_x := sym_exec bsegs 400 true [959156] (SCR hta_A_dirs [] []) (SS 966084 hta_sr [] hta_A_knF 40) [].
Definition hta_A_ss : sym_state := Eval vm_compute in fst (fst hta_A_x).
Definition hta_A_scs : list sidecond := Eval vm_compute in snd (fst hta_A_x).
Lemma hta_A_eq : hta_A_x = (hta_A_ss, hta_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma hta_A_pc : s_pc hta_A_ss = 959156.
Proof. reflexivity. Qed.
Lemma hta_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (p sh fb b e h : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) -> (0 <= sh) -> (sh + 288 <= 2 ^ 47) -> (0 <= fb) -> (fb + 64 <= 2 ^ 47) -> (0 <= b < 2 ^ 64) -> (0 <= e <= 1) -> (0 <= h < 2 ^ 64) ->
  scs_denot bsegs m (hta_E R p sh fb b e h) hta_A_scs.
Proof.
  intros R m p sh fb b e h H0 H1 H2 H3 H4 H5 H6 H7 H8. unfold hta_E, hta_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma hta_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (p sh fb b e h : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) -> (0 <= sh) -> (sh + 288 <= 2 ^ 47) -> (0 <= fb) -> (fb + 64 <= 2 ^ 47) -> (0 <= b < 2 ^ 64) -> (0 <= e <= 1) -> (0 <= h < 2 ^ 64) ->
  regs_ok (hta_E R p sh fb b e h) hta_sr R -> know_ok bsegs (hta_E R p sh fb b e h) m hta_A_knF ->
  exists R', regs_ok (hta_E R p sh fb b e h) (s_regs hta_A_ss) R' /\ log_flat (hta_E R p sh fb b e h) (s_log hta_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966084) m rom)
                    (mkst R' (Z_to_bv 64 959156) (mem_denot (hta_E R p sh fb b e h) m (s_log hta_A_ss)) rom).
Proof.
  intros fx R m rom p sh fb b e h H0 H1 H2 H3 H4 H5 H6 H7 H8 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R hta_A_eq HR HK
              (hta_A_sc R m p sh fb b e h H0 H1 H2 H3 H4 H5 H6 H7 H8)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition htz_E (R : bvmap 5 word) (p : Z) : env := Eseed R [Z_to_bv 64 p].
Definition htz_sr : list expr := srs sr_id [(10%bv, ELit 0); (18%bv, EVar 32)].
Definition htz_kn : list kentry := [KWord (SA (EVar 32) 24) 8 (ELit 0)].
Definition htz_Z_dirs : list bool := [].
Definition htz_Z_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966836; 966124] (SCR htz_Z_dirs [] []) 966120 htz_sr htz_kn 40.
Definition htz_Z_x := sym_exec bsegs 400 true [966836; 966124] (SCR htz_Z_dirs [] []) (SS 966120 htz_sr [] htz_Z_knF 40) [].
Definition htz_Z_ss : sym_state := Eval vm_compute in fst (fst htz_Z_x).
Definition htz_Z_scs : list sidecond := Eval vm_compute in snd (fst htz_Z_x).
Lemma htz_Z_eq : htz_Z_x = (htz_Z_ss, htz_Z_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma htz_Z_pc : s_pc htz_Z_ss = 966836.
Proof. reflexivity. Qed.
Lemma htz_Z_sc : forall (R : bvmap 5 word) (m : word -> option byte) (p : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) ->
  scs_denot bsegs m (htz_E R p) htz_Z_scs.
Proof.
  intros R m p H0 H1. unfold htz_E, htz_Z_scs. split_scs.
  - sc_closeB.
Qed.
Lemma htz_Z_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (p : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) ->
  regs_ok (htz_E R p) htz_sr R -> know_ok bsegs (htz_E R p) m htz_Z_knF ->
  exists R', regs_ok (htz_E R p) (s_regs htz_Z_ss) R' /\ log_flat (htz_E R p) (s_log htz_Z_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966120) m rom)
                    (mkst R' (Z_to_bv 64 966836) (mem_denot (htz_E R p) m (s_log htz_Z_ss)) rom).
Proof.
  intros fx R m rom p H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R htz_Z_eq HR HK
              (htz_Z_sc R m p H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition htn_E (R : bvmap 5 word) (p : Z) : env := Eseed R [Z_to_bv 64 p].
Definition htn_sr : list expr := srs sr_id [(10%bv, ELit (-4)); (18%bv, EVar 32)].
Definition htn_kn : list kentry := [].
Definition htn_N_dirs : list bool := [].
Definition htn_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966836; 966124] (SCR htn_N_dirs [] []) 966120 htn_sr htn_kn 40.
Definition htn_N_x := sym_exec bsegs 400 true [966836; 966124] (SCR htn_N_dirs [] []) (SS 966120 htn_sr [] htn_N_knF 40) [].
Definition htn_N_ss : sym_state := Eval vm_compute in fst (fst htn_N_x).
Definition htn_N_scs : list sidecond := Eval vm_compute in snd (fst htn_N_x).
Lemma htn_N_eq : htn_N_x = (htn_N_ss, htn_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma htn_N_pc : s_pc htn_N_ss = 966124.
Proof. reflexivity. Qed.
Lemma htn_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (p : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) ->
  scs_denot bsegs m (htn_E R p) htn_N_scs.
Proof.
  intros R m p H0 H1. unfold htn_E, htn_N_scs. split_scs.
Qed.
Lemma htn_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (p : Z),
  (0 <= p) -> (p + 96 <= 2 ^ 47) ->
  regs_ok (htn_E R p) htn_sr R -> know_ok bsegs (htn_E R p) m htn_N_knF ->
  exists R', regs_ok (htn_E R p) (s_regs htn_N_ss) R' /\ log_flat (htn_E R p) (s_log htn_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966120) m rom)
                    (mkst R' (Z_to_bv 64 966124) (mem_denot (htn_E R p) m (s_log htn_N_ss)) rom).
Proof.
  intros fx R m rom p H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R htn_N_eq HR HK
              (htn_N_sc R m p H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
