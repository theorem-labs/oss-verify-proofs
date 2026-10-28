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

Definition bx0_E (R : bvmap 5 word) (sf : Z) : env := Eseed R [Z_to_bv 64 sf].
Definition bx0_sr : list expr := srs sr_id [(19%bv, EVar 32)].
Definition bx0_kn : list kentry := [KWr (SA (EVar 32) 0) (ELit 476)].
Definition bx0_A_dirs : list bool := [].
Definition bx0_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [963836] (SCR bx0_A_dirs [] []) 963712 bx0_sr bx0_kn 40.
Definition bx0_A_x := sym_exec bsegs 400 true [963836] (SCR bx0_A_dirs [] []) (SS 963712 bx0_sr [] bx0_A_knF 40) [].
Definition bx0_A_ss : sym_state := Eval vm_compute in fst (fst bx0_A_x).
Definition bx0_A_scs : list sidecond := Eval vm_compute in snd (fst bx0_A_x).
Lemma bx0_A_eq : bx0_A_x = (bx0_A_ss, bx0_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bx0_A_pc : s_pc bx0_A_ss = 963836.
Proof. reflexivity. Qed.
Lemma bx0_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  scs_denot bsegs m (bx0_E R sf) bx0_A_scs.
Proof.
  intros R m sf H0 H1. unfold bx0_E, bx0_A_scs. split_scs.
  all: sc_closeB.
Qed.
Lemma bx0_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  regs_ok (bx0_E R sf) bx0_sr R -> know_ok bsegs (bx0_E R sf) m bx0_A_knF ->
  exists R', regs_ok (bx0_E R sf) (s_regs bx0_A_ss) R' /\ log_flat (bx0_E R sf) (s_log bx0_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 963712) m rom)
                    (mkst R' (Z_to_bv 64 963836) (mem_denot (bx0_E R sf) m (s_log bx0_A_ss)) rom).
Proof.
  intros fx R m rom sf H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bx0_A_eq HR HK
              (bx0_A_sc R m sf H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bx1_E (R : bvmap 5 word) (sf : Z) : env := Eseed R [Z_to_bv 64 sf].
Definition bx1_sr : list expr := srs sr_id [(19%bv, EVar 32)].
Definition bx1_kn : list kentry := [KWr (SA (EVar 32) 0) (ELit 476)].
Definition bx1_A_dirs : list bool := [].
Definition bx1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966900] (SCR bx1_A_dirs [] []) 966880 bx1_sr bx1_kn 40.
Definition bx1_A_x := sym_exec bsegs 400 true [966900] (SCR bx1_A_dirs [] []) (SS 966880 bx1_sr [] bx1_A_knF 40) [].
Definition bx1_A_ss : sym_state := Eval vm_compute in fst (fst bx1_A_x).
Definition bx1_A_scs : list sidecond := Eval vm_compute in snd (fst bx1_A_x).
Lemma bx1_A_eq : bx1_A_x = (bx1_A_ss, bx1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bx1_A_pc : s_pc bx1_A_ss = 966900.
Proof. reflexivity. Qed.
Lemma bx1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  scs_denot bsegs m (bx1_E R sf) bx1_A_scs.
Proof.
  intros R m sf H0 H1. unfold bx1_E, bx1_A_scs. split_scs.
  all: sc_closeB.
Qed.
Lemma bx1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  regs_ok (bx1_E R sf) bx1_sr R -> know_ok bsegs (bx1_E R sf) m bx1_A_knF ->
  exists R', regs_ok (bx1_E R sf) (s_regs bx1_A_ss) R' /\ log_flat (bx1_E R sf) (s_log bx1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966880) m rom)
                    (mkst R' (Z_to_bv 64 966900) (mem_denot (bx1_E R sf) m (s_log bx1_A_ss)) rom).
Proof.
  intros fx R m rom sf H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bx1_A_eq HR HK
              (bx1_A_sc R m sf H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition bx2_E (R : bvmap 5 word) (sf : Z) : env := Eseed R [Z_to_bv 64 sf].
Definition bx2_sr : list expr := srs sr_id [(19%bv, EVar 32)].
Definition bx2_kn : list kentry := [KWr (SA (EVar 32) 0) (ELit 476)].
Definition bx2_A_dirs : list bool := [].
Definition bx2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966912] (SCR bx2_A_dirs [] []) 966900 bx2_sr bx2_kn 40.
Definition bx2_A_x := sym_exec bsegs 400 true [966912] (SCR bx2_A_dirs [] []) (SS 966900 bx2_sr [] bx2_A_knF 40) [].
Definition bx2_A_ss : sym_state := Eval vm_compute in fst (fst bx2_A_x).
Definition bx2_A_scs : list sidecond := Eval vm_compute in snd (fst bx2_A_x).
Lemma bx2_A_eq : bx2_A_x = (bx2_A_ss, bx2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma bx2_A_pc : s_pc bx2_A_ss = 966912.
Proof. reflexivity. Qed.
Lemma bx2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  scs_denot bsegs m (bx2_E R sf) bx2_A_scs.
Proof.
  intros R m sf H0 H1. unfold bx2_E, bx2_A_scs. split_scs.
  all: sc_closeB.
Qed.
Lemma bx2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (sf : Z),
  (0 <= sf) -> (sf + 512 <= 2 ^ 47) ->
  regs_ok (bx2_E R sf) bx2_sr R -> know_ok bsegs (bx2_E R sf) m bx2_A_knF ->
  exists R', regs_ok (bx2_E R sf) (s_regs bx2_A_ss) R' /\ log_flat (bx2_E R sf) (s_log bx2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966900) m rom)
                    (mkst R' (Z_to_bv 64 966912) (mem_denot (bx2_E R sf) m (s_log bx2_A_ss)) rom).
Proof.
  intros fx R m rom sf H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R bx2_A_eq HR HK
              (bx2_A_sc R m sf H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
