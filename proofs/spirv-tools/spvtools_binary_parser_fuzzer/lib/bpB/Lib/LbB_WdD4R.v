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

Definition d1_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition d1_sr : list expr := srs sr_id [(20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition d1_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition d1_A_dirs : list bool := [].
Definition d1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [756256] (SCR d1_A_dirs [] []) 966124 d1_sr d1_kn 40.
Definition d1_A_x := sym_exec bsegs 400 true [756256] (SCR d1_A_dirs [] []) (SS 966124 d1_sr [] d1_A_knF 40) [].
Definition d1_A_ss : sym_state := Eval vm_compute in fst (fst d1_A_x).
Definition d1_A_scs : list sidecond := Eval vm_compute in snd (fst d1_A_x).
Lemma d1_A_eq : d1_A_x = (d1_A_ss, d1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma d1_A_pc : s_pc d1_A_ss = 756256.
Proof. reflexivity. Qed.
Lemma d1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (d1_E R ff) d1_A_scs.
Proof.
  intros R m ff H0 H1. unfold d1_E, d1_A_scs. split_scs.
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
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma d1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (d1_E R ff) d1_sr R -> know_ok bsegs (d1_E R ff) m d1_A_knF ->
  exists R', regs_ok (d1_E R ff) (s_regs d1_A_ss) R' /\ log_flat (d1_E R ff) (s_log d1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966124) m rom)
                    (mkst R' (Z_to_bv 64 756256) (mem_denot (d1_E R ff) m (s_log d1_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R d1_A_eq HR HK
              (d1_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition d2_E (R : bvmap 5 word) (ff S1 cons pos : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 cons; Z_to_bv 64 pos].
Definition d2_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 608)); (9%bv, EVar 33); (20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition d2_kn : list kentry := [KWord (SA (EVar 32) 3536) 8 (EVar 36); KWord (SA (EVar 32) 3464) 8 (EVar 35); KWord (SA (EVar 33) 48) 8 (EAlu ALU_ADD (EVar 32) (ELit 2224)); KAlign (EVar 35) 16; KRange (EVar 35) 1 (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 4096); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KDisj (SA (EVar 32) 0) (ELit 4096) (SA (EVar 33) 0) (ELit 192); KDisj (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512) (SA (EVar 32) 0) (ELit 4096)].
Definition d2_A_dirs : list bool := [].
Definition d2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1010964] (SCR d2_A_dirs [] []) 966368 d2_sr d2_kn 40.
Definition d2_A_x := sym_exec bsegs 400 true [1010964] (SCR d2_A_dirs [] []) (SS 966368 d2_sr [] d2_A_knF 40) [].
Definition d2_A_ss : sym_state := Eval vm_compute in fst (fst d2_A_x).
Definition d2_A_scs : list sidecond := Eval vm_compute in snd (fst d2_A_x).
Lemma d2_A_eq : d2_A_x = (d2_A_ss, d2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma d2_A_pc : s_pc d2_A_ss = 1010964.
Proof. reflexivity. Qed.
Lemma d2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff S1 cons pos : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) -> (2 ^ 45 <= S1) -> (S1 + 192 <= 2 ^ 47) ->
  scs_denot bsegs m (d2_E R ff S1 cons pos) d2_A_scs.
Proof.
  intros R m ff S1 cons pos H0 H1 H2 H3. unfold d2_E, d2_A_scs. split_scs.
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
Lemma d2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff S1 cons pos : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) -> (2 ^ 45 <= S1) -> (S1 + 192 <= 2 ^ 47) ->
  regs_ok (d2_E R ff S1 cons pos) d2_sr R -> know_ok bsegs (d2_E R ff S1 cons pos) m d2_A_knF ->
  exists R', regs_ok (d2_E R ff S1 cons pos) (s_regs d2_A_ss) R' /\ log_flat (d2_E R ff S1 cons pos) (s_log d2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966368) m rom)
                    (mkst R' (Z_to_bv 64 1010964) (mem_denot (d2_E R ff S1 cons pos) m (s_log d2_A_ss)) rom).
Proof.
  intros fx R m rom ff S1 cons pos H0 H1 H2 H3 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R d2_A_eq HR HK
              (d2_A_sc R m ff S1 cons pos H0 H1 H2 H3)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition d3_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition d3_sr : list expr := srs sr_id [(26%bv, EAlu ALU_ADD (EVar 32) (ELit 736)); (25%bv, EAlu ALU_ADD (EVar 32) (ELit 672)); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 2288))].
Definition d3_kn : list kentry := [KWord (SA (EVar 32) 736) 1 (ELit 0); KWord (SA (EVar 32) 672) 1 (ELit 0); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition d3_A_dirs : list bool := [].
Definition d3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1008288] (SCR d3_A_dirs [] []) 966452 d3_sr d3_kn 40.
Definition d3_A_x := sym_exec bsegs 400 true [1008288] (SCR d3_A_dirs [] []) (SS 966452 d3_sr [] d3_A_knF 40) [].
Definition d3_A_ss : sym_state := Eval vm_compute in fst (fst d3_A_x).
Definition d3_A_scs : list sidecond := Eval vm_compute in snd (fst d3_A_x).
Lemma d3_A_eq : d3_A_x = (d3_A_ss, d3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma d3_A_pc : s_pc d3_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma d3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (d3_E R ff) d3_A_scs.
Proof.
  intros R m ff H0 H1. unfold d3_E, d3_A_scs. split_scs.
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
Lemma d3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (d3_E R ff) d3_sr R -> know_ok bsegs (d3_E R ff) m d3_A_knF ->
  exists R', regs_ok (d3_E R ff) (s_regs d3_A_ss) R' /\ log_flat (d3_E R ff) (s_log d3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966452) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (d3_E R ff) m (s_log d3_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R d3_A_eq HR HK
              (d3_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition d4_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition d4_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 2288))].
Definition d4_kn : list kentry := [KWord (SA (EVar 32) 2648) 4 (ELit 4294967295)].
Definition d4_A_dirs : list bool := [].
Definition d4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034672] (SCR d4_A_dirs [] []) 966568 d4_sr d4_kn 40.
Definition d4_A_x := sym_exec bsegs 400 true [1034672] (SCR d4_A_dirs [] []) (SS 966568 d4_sr [] d4_A_knF 40) [].
Definition d4_A_ss : sym_state := Eval vm_compute in fst (fst d4_A_x).
Definition d4_A_scs : list sidecond := Eval vm_compute in snd (fst d4_A_x).
Lemma d4_A_eq : d4_A_x = (d4_A_ss, d4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma d4_A_pc : s_pc d4_A_ss = 1034672.
Proof. reflexivity. Qed.
Lemma d4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (d4_E R ff) d4_A_scs.
Proof.
  intros R m ff H0 H1. unfold d4_E, d4_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma d4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (d4_E R ff) d4_sr R -> know_ok bsegs (d4_E R ff) m d4_A_knF ->
  exists R', regs_ok (d4_E R ff) (s_regs d4_A_ss) R' /\ log_flat (d4_E R ff) (s_log d4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966568) m rom)
                    (mkst R' (Z_to_bv 64 1034672) (mem_denot (d4_E R ff) m (s_log d4_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R d4_A_eq HR HK
              (d4_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition d5_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition d5_sr : list expr := srs sr_id [(21%bv, ELit 18446744073709551608); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition d5_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition d5_A_dirs : list bool := [].
Definition d5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966880] (SCR d5_A_dirs [] []) 966580 d5_sr d5_kn 40.
Definition d5_A_x := sym_exec bsegs 400 true [966880] (SCR d5_A_dirs [] []) (SS 966580 d5_sr [] d5_A_knF 40) [].
Definition d5_A_ss : sym_state := Eval vm_compute in fst (fst d5_A_x).
Definition d5_A_scs : list sidecond := Eval vm_compute in snd (fst d5_A_x).
Lemma d5_A_eq : d5_A_x = (d5_A_ss, d5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma d5_A_pc : s_pc d5_A_ss = 966880.
Proof. reflexivity. Qed.
Lemma d5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (d5_E R ff) d5_A_scs.
Proof.
  intros R m ff H0 H1. unfold d5_E, d5_A_scs. split_scs.
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
Lemma d5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (d5_E R ff) d5_sr R -> know_ok bsegs (d5_E R ff) m d5_A_knF ->
  exists R', regs_ok (d5_E R ff) (s_regs d5_A_ss) R' /\ log_flat (d5_E R ff) (s_log d5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 966580) m rom)
                    (mkst R' (Z_to_bv 64 966880) (mem_denot (d5_E R ff) m (s_log d5_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R d5_A_eq HR HK
              (d5_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
