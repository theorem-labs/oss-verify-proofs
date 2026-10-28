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

Definition mm0_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition mm0_sr : list expr := srs sr_id [(22%bv, EAlu ALU_ADD (EVar 32) (ELit 3504)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456))].
Definition mm0_kn : list kentry := [KWord (SA (EVar 32) 3504) 8 (ELit 0)].
Definition mm0_A_dirs : list bool := [].
Definition mm0_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [964564] (SCR mm0_A_dirs [] []) 963836 mm0_sr mm0_kn 40.
Definition mm0_A_x := sym_exec bsegs 400 true [964564] (SCR mm0_A_dirs [] []) (SS 963836 mm0_sr [] mm0_A_knF 40) [].
Definition mm0_A_ss : sym_state := Eval vm_compute in fst (fst mm0_A_x).
Definition mm0_A_scs : list sidecond := Eval vm_compute in snd (fst mm0_A_x).
Lemma mm0_A_eq : mm0_A_x = (mm0_A_ss, mm0_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm0_A_pc : s_pc mm0_A_ss = 964564.
Proof. reflexivity. Qed.
Lemma mm0_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (mm0_E R ff) mm0_A_scs.
Proof.
  intros R m ff H0 H1. unfold mm0_E, mm0_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma mm0_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (mm0_E R ff) mm0_sr R -> know_ok bsegs (mm0_E R ff) m mm0_A_knF ->
  exists R', regs_ok (mm0_E R ff) (s_regs mm0_A_ss) R' /\ log_flat (mm0_E R ff) (s_log mm0_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 963836) m rom)
                    (mkst R' (Z_to_bv 64 964564) (mem_denot (mm0_E R ff) m (s_log mm0_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm0_A_eq HR HK
              (mm0_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mm1_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition mm1_sr : list expr := srs sr_id [(20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition mm1_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition mm1_A_dirs : list bool := [].
Definition mm1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [756256] (SCR mm1_A_dirs [] []) 964564 mm1_sr mm1_kn 40.
Definition mm1_A_x := sym_exec bsegs 400 true [756256] (SCR mm1_A_dirs [] []) (SS 964564 mm1_sr [] mm1_A_knF 40) [].
Definition mm1_A_ss : sym_state := Eval vm_compute in fst (fst mm1_A_x).
Definition mm1_A_scs : list sidecond := Eval vm_compute in snd (fst mm1_A_x).
Lemma mm1_A_eq : mm1_A_x = (mm1_A_ss, mm1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm1_A_pc : s_pc mm1_A_ss = 756256.
Proof. reflexivity. Qed.
Lemma mm1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (mm1_E R ff) mm1_A_scs.
Proof.
  intros R m ff H0 H1. unfold mm1_E, mm1_A_scs. split_scs.
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
Lemma mm1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (mm1_E R ff) mm1_sr R -> know_ok bsegs (mm1_E R ff) m mm1_A_knF ->
  exists R', regs_ok (mm1_E R ff) (s_regs mm1_A_ss) R' /\ log_flat (mm1_E R ff) (s_log mm1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964564) m rom)
                    (mkst R' (Z_to_bv 64 756256) (mem_denot (mm1_E R ff) m (s_log mm1_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm1_A_eq HR HK
              (mm1_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mm2_E (R : bvmap 5 word) (ff S1 cons pos mb : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 cons; Z_to_bv 64 pos; Z_to_bv 64 mb].
Definition mm2_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 32)); (9%bv, EVar 33); (20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition mm2_kn : list kentry := [KWord (SA (EVar 32) 3536) 8 (EVar 36); KWord (SA (EVar 32) 3464) 8 (EVar 35); KWord (SA (EVar 33) 40) 8 (EVar 37); KAlign (EVar 35) 16; KRange (EVar 35) 1 (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 4096); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KDisj (SA (EVar 32) 0) (ELit 4096) (SA (EVar 33) 0) (ELit 192); KDisj (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512) (SA (EVar 32) 0) (ELit 4096)].
Definition mm2_A_dirs : list bool := [].
Definition mm2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1010964] (SCR mm2_A_dirs [] []) 964808 mm2_sr mm2_kn 40.
Definition mm2_A_x := sym_exec bsegs 400 true [1010964] (SCR mm2_A_dirs [] []) (SS 964808 mm2_sr [] mm2_A_knF 40) [].
Definition mm2_A_ss : sym_state := Eval vm_compute in fst (fst mm2_A_x).
Definition mm2_A_scs : list sidecond := Eval vm_compute in snd (fst mm2_A_x).
Lemma mm2_A_eq : mm2_A_x = (mm2_A_ss, mm2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm2_A_pc : s_pc mm2_A_ss = 1010964.
Proof. reflexivity. Qed.
Lemma mm2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff S1 cons pos mb : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) -> (2 ^ 45 <= S1) -> (S1 + 192 <= 2 ^ 47) ->
  scs_denot bsegs m (mm2_E R ff S1 cons pos mb) mm2_A_scs.
Proof.
  intros R m ff S1 cons pos mb H0 H1 H2 H3. unfold mm2_E, mm2_A_scs. split_scs.
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
Lemma mm2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff S1 cons pos mb : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) -> (2 ^ 45 <= S1) -> (S1 + 192 <= 2 ^ 47) ->
  regs_ok (mm2_E R ff S1 cons pos mb) mm2_sr R -> know_ok bsegs (mm2_E R ff S1 cons pos mb) m mm2_A_knF ->
  exists R', regs_ok (mm2_E R ff S1 cons pos mb) (s_regs mm2_A_ss) R' /\ log_flat (mm2_E R ff S1 cons pos mb) (s_log mm2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964808) m rom)
                    (mkst R' (Z_to_bv 64 1010964) (mem_denot (mm2_E R ff S1 cons pos mb) m (s_log mm2_A_ss)) rom).
Proof.
  intros fx R m rom ff S1 cons pos mb H0 H1 H2 H3 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm2_A_eq HR HK
              (mm2_A_sc R m ff S1 cons pos mb H0 H1 H2 H3)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mm3_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition mm3_sr : list expr := srs sr_id [(26%bv, EAlu ALU_ADD (EVar 32) (ELit 160)); (25%bv, EAlu ALU_ADD (EVar 32) (ELit 96)); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 800))].
Definition mm3_kn : list kentry := [KWord (SA (EVar 32) 160) 1 (ELit 0); KWord (SA (EVar 32) 96) 1 (ELit 0); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition mm3_A_dirs : list bool := [].
Definition mm3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1008288] (SCR mm3_A_dirs [] []) 964892 mm3_sr mm3_kn 40.
Definition mm3_A_x := sym_exec bsegs 400 true [1008288] (SCR mm3_A_dirs [] []) (SS 964892 mm3_sr [] mm3_A_knF 40) [].
Definition mm3_A_ss : sym_state := Eval vm_compute in fst (fst mm3_A_x).
Definition mm3_A_scs : list sidecond := Eval vm_compute in snd (fst mm3_A_x).
Lemma mm3_A_eq : mm3_A_x = (mm3_A_ss, mm3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm3_A_pc : s_pc mm3_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma mm3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (mm3_E R ff) mm3_A_scs.
Proof.
  intros R m ff H0 H1. unfold mm3_E, mm3_A_scs. split_scs.
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
Lemma mm3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (mm3_E R ff) mm3_sr R -> know_ok bsegs (mm3_E R ff) m mm3_A_knF ->
  exists R', regs_ok (mm3_E R ff) (s_regs mm3_A_ss) R' /\ log_flat (mm3_E R ff) (s_log mm3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964892) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (mm3_E R ff) m (s_log mm3_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm3_A_eq HR HK
              (mm3_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mm4_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition mm4_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 800))].
Definition mm4_kn : list kentry := [KWord (SA (EVar 32) 1160) 4 (ELit 4294967292)].
Definition mm4_A_dirs : list bool := [].
Definition mm4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034672] (SCR mm4_A_dirs [] []) 965008 mm4_sr mm4_kn 40.
Definition mm4_A_x := sym_exec bsegs 400 true [1034672] (SCR mm4_A_dirs [] []) (SS 965008 mm4_sr [] mm4_A_knF 40) [].
Definition mm4_A_ss : sym_state := Eval vm_compute in fst (fst mm4_A_x).
Definition mm4_A_scs : list sidecond := Eval vm_compute in snd (fst mm4_A_x).
Lemma mm4_A_eq : mm4_A_x = (mm4_A_ss, mm4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm4_A_pc : s_pc mm4_A_ss = 1034672.
Proof. reflexivity. Qed.
Lemma mm4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (mm4_E R ff) mm4_A_scs.
Proof.
  intros R m ff H0 H1. unfold mm4_E, mm4_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma mm4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (mm4_E R ff) mm4_sr R -> know_ok bsegs (mm4_E R ff) m mm4_A_knF ->
  exists R', regs_ok (mm4_E R ff) (s_regs mm4_A_ss) R' /\ log_flat (mm4_E R ff) (s_log mm4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965008) m rom)
                    (mkst R' (Z_to_bv 64 1034672) (mem_denot (mm4_E R ff) m (s_log mm4_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm4_A_eq HR HK
              (mm4_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition mm5_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition mm5_sr : list expr := srs sr_id [(21%bv, ELit 18446744073709551608); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition mm5_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512)].
Definition mm5_A_dirs : list bool := [].
Definition mm5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966912] (SCR mm5_A_dirs [] []) 965020 mm5_sr mm5_kn 40.
Definition mm5_A_x := sym_exec bsegs 400 true [966912] (SCR mm5_A_dirs [] []) (SS 965020 mm5_sr [] mm5_A_knF 40) [].
Definition mm5_A_ss : sym_state := Eval vm_compute in fst (fst mm5_A_x).
Definition mm5_A_scs : list sidecond := Eval vm_compute in snd (fst mm5_A_x).
Lemma mm5_A_eq : mm5_A_x = (mm5_A_ss, mm5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma mm5_A_pc : s_pc mm5_A_ss = 966912.
Proof. reflexivity. Qed.
Lemma mm5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  scs_denot bsegs m (mm5_E R ff) mm5_A_scs.
Proof.
  intros R m ff H0 H1. unfold mm5_E, mm5_A_scs. split_scs.
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
Lemma mm5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (1048576 <= ff) -> (ff + 4096 <= 2 ^ 47) ->
  regs_ok (mm5_E R ff) mm5_sr R -> know_ok bsegs (mm5_E R ff) m mm5_A_knF ->
  exists R', regs_ok (mm5_E R ff) (s_regs mm5_A_ss) R' /\ log_flat (mm5_E R ff) (s_log mm5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 965020) m rom)
                    (mkst R' (Z_to_bv 64 966912) (mem_denot (mm5_E R ff) m (s_log mm5_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R mm5_A_eq HR HK
              (mm5_A_sc R m ff H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
