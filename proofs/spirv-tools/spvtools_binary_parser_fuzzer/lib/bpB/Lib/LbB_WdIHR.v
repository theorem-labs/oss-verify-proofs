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

Definition ih0_E (R : bvmap 5 word) (ff sp mb words n : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 mb; Z_to_bv 64 0; Z_to_bv 64 words; Z_to_bv 64 n].
Definition ih0_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 3504)); (9%bv, EVar 33)].
Definition ih0_kn : list kentry := [KWord (SA (EVar 32) 3504) 8 (EVar 39); KWord (SA (EVar 32) 3512) 8 (EVar 40); KWord (SA (EVar 33) 40) 8 (EVar 37); KRange (EVar 32) 7241728 (2 ^ 47 - 4096); KRange (EVar 33) 140735332483136 (2 ^ 47); KRange (EVar 40) 0 4].
Definition ih0_A_dirs : list bool := [false].
Definition ih0_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [963860] (SCR ih0_A_dirs [] []) 963836 ih0_sr ih0_kn 50.
Definition ih0_A_x := sym_exec bsegs 400 true [963860] (SCR ih0_A_dirs [] []) (SS 963836 ih0_sr [] ih0_A_knF 50) [].
Definition ih0_A_ss : sym_state := Eval vm_compute in fst (fst ih0_A_x).
Definition ih0_A_scs : list sidecond := Eval vm_compute in snd (fst ih0_A_x).
Lemma ih0_A_eq : ih0_A_x = (ih0_A_ss, ih0_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih0_A_pc : s_pc ih0_A_ss = 963860.
Proof. reflexivity. Qed.
Lemma ih0_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff sp mb words n : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (140735332483136 <= sp <= 2 ^ 47) -> (0 <= mb <= 2 ^ 64 - 1) -> (0 <= words <= 2 ^ 64 - 1) -> (0 <= n <= 4) -> (words <> 0) ->
  scs_denot bsegs m (ih0_E R ff sp mb words n) ih0_A_scs.
Proof.
  intros R m ff sp mb words n H0 H1 H2 H3 H4 H5. unfold ih0_E, ih0_A_scs. split_scs.
  - sc_closeB.
Qed.
Lemma ih0_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff sp mb words n : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (140735332483136 <= sp <= 2 ^ 47) -> (0 <= mb <= 2 ^ 64 - 1) -> (0 <= words <= 2 ^ 64 - 1) -> (0 <= n <= 4) -> (words <> 0) ->
  regs_ok (ih0_E R ff sp mb words n) ih0_sr R -> know_ok bsegs (ih0_E R ff sp mb words n) m ih0_A_knF ->
  exists R', regs_ok (ih0_E R ff sp mb words n) (s_regs ih0_A_ss) R' /\ log_flat (ih0_E R ff sp mb words n) (s_log ih0_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 963836) m rom)
                    (mkst R' (Z_to_bv 64 963860) (mem_denot (ih0_E R ff sp mb words n) m (s_log ih0_A_ss)) rom).
Proof.
  intros fx R m rom ff sp mb words n H0 H1 H2 H3 H4 H5 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih0_A_eq HR HK
              (ih0_A_sc R m ff sp mb words n H0 H1 H2 H3 H4 H5)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih1_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition ih1_sr : list expr := srs sr_id [(20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition ih1_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KRange (EVar 32) 7241728 (2 ^ 47 - 4096)].
Definition ih1_A_dirs : list bool := [].
Definition ih1_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [756256] (SCR ih1_A_dirs [] []) 963860 ih1_sr ih1_kn 50.
Definition ih1_A_x := sym_exec bsegs 400 true [756256] (SCR ih1_A_dirs [] []) (SS 963860 ih1_sr [] ih1_A_knF 50) [].
Definition ih1_A_ss : sym_state := Eval vm_compute in fst (fst ih1_A_x).
Definition ih1_A_scs : list sidecond := Eval vm_compute in snd (fst ih1_A_x).
Lemma ih1_A_eq : ih1_A_x = (ih1_A_ss, ih1_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih1_A_pc : s_pc ih1_A_ss = 756256.
Proof. reflexivity. Qed.
Lemma ih1_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  scs_denot bsegs m (ih1_E R ff) ih1_A_scs.
Proof.
  intros R m ff H0. unfold ih1_E, ih1_A_scs. split_scs.
Qed.
Lemma ih1_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  regs_ok (ih1_E R ff) ih1_sr R -> know_ok bsegs (ih1_E R ff) m ih1_A_knF ->
  exists R', regs_ok (ih1_E R ff) (s_regs ih1_A_ss) R' /\ log_flat (ih1_E R ff) (s_log ih1_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 963860) m rom)
                    (mkst R' (Z_to_bv 64 756256) (mem_denot (ih1_E R ff) m (s_log ih1_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih1_A_eq HR HK
              (ih1_A_sc R m ff H0)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih2_E (R : bvmap 5 word) (ff cons pos : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 cons; Z_to_bv 64 pos].
Definition ih2_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 224)); (20%bv, EVar 32); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition ih2_kn : list kentry := [KWord (SA (EVar 32) 3536) 8 (EVar 36); KWord (SA (EVar 32) 3464) 8 (EVar 35); KWr (SA (EVar 32) 0) (ELit 4096); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KRange (EVar 32) 7241728 (2 ^ 47 - 4096); KRange (EVar 35) 1 (2 ^ 47); KAlign (EVar 35) 16].
Definition ih2_A_dirs : list bool := [].
Definition ih2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1010964] (SCR ih2_A_dirs [] []) 964104 ih2_sr ih2_kn 50.
Definition ih2_A_x := sym_exec bsegs 400 true [1010964] (SCR ih2_A_dirs [] []) (SS 964104 ih2_sr [] ih2_A_knF 50) [].
Definition ih2_A_ss : sym_state := Eval vm_compute in fst (fst ih2_A_x).
Definition ih2_A_scs : list sidecond := Eval vm_compute in snd (fst ih2_A_x).
Lemma ih2_A_eq : ih2_A_x = (ih2_A_ss, ih2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih2_A_pc : s_pc ih2_A_ss = 1010964.
Proof. reflexivity. Qed.
Lemma ih2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff cons pos : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (1 <= cons <= 2 ^ 47) -> (cons mod 16 = 0) -> (0 <= pos <= 2 ^ 64 - 1) -> (ff + 4096 <= 2147446784 \/ 17594333495296 <= ff) ->
  scs_denot bsegs m (ih2_E R ff cons pos) ih2_A_scs.
Proof.
  intros R m ff cons pos H0 H1 H2 H3 H4. unfold ih2_E, ih2_A_scs. split_scs.
Qed.
Lemma ih2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff cons pos : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (1 <= cons <= 2 ^ 47) -> (cons mod 16 = 0) -> (0 <= pos <= 2 ^ 64 - 1) -> (ff + 4096 <= 2147446784 \/ 17594333495296 <= ff) ->
  regs_ok (ih2_E R ff cons pos) ih2_sr R -> know_ok bsegs (ih2_E R ff cons pos) m ih2_A_knF ->
  exists R', regs_ok (ih2_E R ff cons pos) (s_regs ih2_A_ss) R' /\ log_flat (ih2_E R ff cons pos) (s_log ih2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964104) m rom)
                    (mkst R' (Z_to_bv 64 1010964) (mem_denot (ih2_E R ff cons pos) m (s_log ih2_A_ss)) rom).
Proof.
  intros fx R m rom ff cons pos H0 H1 H2 H3 H4 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih2_A_eq HR HK
              (ih2_A_sc R m ff cons pos H0 H1 H2 H3 H4)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih3_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition ih3_sr : list expr := srs sr_id [(27%bv, EAlu ALU_ADD (EVar 32) (ELit 352)); (26%bv, EAlu ALU_ADD (EVar 32) (ELit 288)); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (25%bv, EAlu ALU_ADD (EVar 32) (ELit 1264))].
Definition ih3_kn : list kentry := [KWord (SA (EVar 32) 352) 1 (ELit 0); KWord (SA (EVar 32) 288) 1 (ELit 0); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KRange (EVar 32) 7241728 (2 ^ 47 - 4096)].
Definition ih3_A_dirs : list bool := [].
Definition ih3_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1008288] (SCR ih3_A_dirs [] []) 964184 ih3_sr ih3_kn 50.
Definition ih3_A_x := sym_exec bsegs 400 true [1008288] (SCR ih3_A_dirs [] []) (SS 964184 ih3_sr [] ih3_A_knF 50) [].
Definition ih3_A_ss : sym_state := Eval vm_compute in fst (fst ih3_A_x).
Definition ih3_A_scs : list sidecond := Eval vm_compute in snd (fst ih3_A_x).
Lemma ih3_A_eq : ih3_A_x = (ih3_A_ss, ih3_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih3_A_pc : s_pc ih3_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma ih3_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  scs_denot bsegs m (ih3_E R ff) ih3_A_scs.
Proof.
  intros R m ff H0. unfold ih3_E, ih3_A_scs. split_scs.
Qed.
Lemma ih3_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  regs_ok (ih3_E R ff) ih3_sr R -> know_ok bsegs (ih3_E R ff) m ih3_A_knF ->
  exists R', regs_ok (ih3_E R ff) (s_regs ih3_A_ss) R' /\ log_flat (ih3_E R ff) (s_log ih3_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964184) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (ih3_E R ff) m (s_log ih3_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih3_A_eq HR HK
              (ih3_A_sc R m ff H0)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih4_E (R : bvmap 5 word) (ff nw : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 nw].
Definition ih4_sr : list expr := srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (25%bv, EAlu ALU_ADD (EVar 32) (ELit 1264))].
Definition ih4_kn : list kentry := [KWord (SA (EVar 32) 3512) 8 (EVar 38); KRange (EVar 32) 7241728 (2 ^ 47 - 4096)].
Definition ih4_A_dirs : list bool := [].
Definition ih4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1201164] (SCR ih4_A_dirs [] []) 964300 ih4_sr ih4_kn 50.
Definition ih4_A_x := sym_exec bsegs 400 true [1201164] (SCR ih4_A_dirs [] []) (SS 964300 ih4_sr [] ih4_A_knF 50) [].
Definition ih4_A_ss : sym_state := Eval vm_compute in fst (fst ih4_A_x).
Definition ih4_A_scs : list sidecond := Eval vm_compute in snd (fst ih4_A_x).
Lemma ih4_A_eq : ih4_A_x = (ih4_A_ss, ih4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih4_A_pc : s_pc ih4_A_ss = 1201164.
Proof. reflexivity. Qed.
Lemma ih4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff nw : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (0 <= nw <= 2 ^ 64 - 1) ->
  scs_denot bsegs m (ih4_E R ff nw) ih4_A_scs.
Proof.
  intros R m ff nw H0 H1. unfold ih4_E, ih4_A_scs. split_scs.
Qed.
Lemma ih4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff nw : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (0 <= nw <= 2 ^ 64 - 1) ->
  regs_ok (ih4_E R ff nw) ih4_sr R -> know_ok bsegs (ih4_E R ff nw) m ih4_A_knF ->
  exists R', regs_ok (ih4_E R ff nw) (s_regs ih4_A_ss) R' /\ log_flat (ih4_E R ff nw) (s_log ih4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964300) m rom)
                    (mkst R' (Z_to_bv 64 1201164) (mem_denot (ih4_E R ff nw) m (s_log ih4_A_ss)) rom).
Proof.
  intros fx R m rom ff nw H0 H1 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih4_A_eq HR HK
              (ih4_A_sc R m ff nw H0 H1)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih5_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition ih5_sr : list expr := srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 1264))].
Definition ih5_kn : list kentry := [].
Definition ih5_A_dirs : list bool := [].
Definition ih5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1008288] (SCR ih5_A_dirs [] []) 964312 ih5_sr ih5_kn 50.
Definition ih5_A_x := sym_exec bsegs 400 true [1008288] (SCR ih5_A_dirs [] []) (SS 964312 ih5_sr [] ih5_A_knF 50) [].
Definition ih5_A_ss : sym_state := Eval vm_compute in fst (fst ih5_A_x).
Definition ih5_A_scs : list sidecond := Eval vm_compute in snd (fst ih5_A_x).
Lemma ih5_A_eq : ih5_A_x = (ih5_A_ss, ih5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih5_A_pc : s_pc ih5_A_ss = 1008288.
Proof. reflexivity. Qed.
Lemma ih5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  scs_denot bsegs m (ih5_E R ff) ih5_A_scs.
Proof.
  intros R m ff H0. unfold ih5_E, ih5_A_scs. split_scs.
Qed.
Lemma ih5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  regs_ok (ih5_E R ff) ih5_sr R -> know_ok bsegs (ih5_E R ff) m ih5_A_knF ->
  exists R', regs_ok (ih5_E R ff) (s_regs ih5_A_ss) R' /\ log_flat (ih5_E R ff) (s_log ih5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964312) m rom)
                    (mkst R' (Z_to_bv 64 1008288) (mem_denot (ih5_E R ff) m (s_log ih5_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih5_A_eq HR HK
              (ih5_A_sc R m ff H0)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih6_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition ih6_sr : list expr := srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 1264))].
Definition ih6_kn : list kentry := [].
Definition ih6_A_dirs : list bool := [].
Definition ih6_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1200700] (SCR ih6_A_dirs [] []) 964332 ih6_sr ih6_kn 50.
Definition ih6_A_x := sym_exec bsegs 400 true [1200700] (SCR ih6_A_dirs [] []) (SS 964332 ih6_sr [] ih6_A_knF 50) [].
Definition ih6_A_ss : sym_state := Eval vm_compute in fst (fst ih6_A_x).
Definition ih6_A_scs : list sidecond := Eval vm_compute in snd (fst ih6_A_x).
Lemma ih6_A_eq : ih6_A_x = (ih6_A_ss, ih6_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih6_A_pc : s_pc ih6_A_ss = 1200700.
Proof. reflexivity. Qed.
Lemma ih6_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  scs_denot bsegs m (ih6_E R ff) ih6_A_scs.
Proof.
  intros R m ff H0. unfold ih6_E, ih6_A_scs. split_scs.
Qed.
Lemma ih6_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  regs_ok (ih6_E R ff) ih6_sr R -> know_ok bsegs (ih6_E R ff) m ih6_A_knF ->
  exists R', regs_ok (ih6_E R ff) (s_regs ih6_A_ss) R' /\ log_flat (ih6_E R ff) (s_log ih6_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964332) m rom)
                    (mkst R' (Z_to_bv 64 1200700) (mem_denot (ih6_E R ff) m (s_log ih6_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih6_A_eq HR HK
              (ih6_A_sc R m ff H0)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih7_E (R : bvmap 5 word) (ff : Z) : env := Eseed R [Z_to_bv 64 ff].
Definition ih7_sr : list expr := srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 1264))].
Definition ih7_kn : list kentry := [KWord (SA (EVar 32) 1624) 4 (ELit 4294967292); KRange (EVar 32) 7241728 (2 ^ 47 - 4096)].
Definition ih7_A_dirs : list bool := [].
Definition ih7_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034672] (SCR ih7_A_dirs [] []) 964344 ih7_sr ih7_kn 50.
Definition ih7_A_x := sym_exec bsegs 400 true [1034672] (SCR ih7_A_dirs [] []) (SS 964344 ih7_sr [] ih7_A_knF 50) [].
Definition ih7_A_ss : sym_state := Eval vm_compute in fst (fst ih7_A_x).
Definition ih7_A_scs : list sidecond := Eval vm_compute in snd (fst ih7_A_x).
Lemma ih7_A_eq : ih7_A_x = (ih7_A_ss, ih7_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih7_A_pc : s_pc ih7_A_ss = 1034672.
Proof. reflexivity. Qed.
Lemma ih7_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  scs_denot bsegs m (ih7_E R ff) ih7_A_scs.
Proof.
  intros R m ff H0. unfold ih7_E, ih7_A_scs. split_scs.
Qed.
Lemma ih7_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) ->
  regs_ok (ih7_E R ff) ih7_sr R -> know_ok bsegs (ih7_E R ff) m ih7_A_knF ->
  exists R', regs_ok (ih7_E R ff) (s_regs ih7_A_ss) R' /\ log_flat (ih7_E R ff) (s_log ih7_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964344) m rom)
                    (mkst R' (Z_to_bv 64 1034672) (mem_denot (ih7_E R ff) m (s_log ih7_A_ss)) rom).
Proof.
  intros fx R m rom ff H0 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih7_A_eq HR HK
              (ih7_A_sc R m ff H0)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ih8_E (R : bvmap 5 word) (ff sp mb : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 mb].
Definition ih8_sr : list expr := srs sr_id [(21%bv, ELit (-8)); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (9%bv, EVar 33)].
Definition ih8_kn : list kentry := [KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 512); KWord (SA (EVar 33) 40) 8 (EVar 37); KRange (EVar 32) 7241728 (2 ^ 47 - 4096); KRange (EVar 33) 140735332483136 (2 ^ 47)].
Definition ih8_A_dirs : list bool := [].
Definition ih8_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [966912] (SCR ih8_A_dirs [] []) 964356 ih8_sr ih8_kn 50.
Definition ih8_A_x := sym_exec bsegs 400 true [966912] (SCR ih8_A_dirs [] []) (SS 964356 ih8_sr [] ih8_A_knF 50) [].
Definition ih8_A_ss : sym_state := Eval vm_compute in fst (fst ih8_A_x).
Definition ih8_A_scs : list sidecond := Eval vm_compute in snd (fst ih8_A_x).
Lemma ih8_A_eq : ih8_A_x = (ih8_A_ss, ih8_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ih8_A_pc : s_pc ih8_A_ss = 966912.
Proof. reflexivity. Qed.
Lemma ih8_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff sp mb : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (140735332483136 <= sp <= 2 ^ 47) -> (0 <= mb <= 2 ^ 64 - 1) ->
  scs_denot bsegs m (ih8_E R ff sp mb) ih8_A_scs.
Proof.
  intros R m ff sp mb H0 H1 H2. unfold ih8_E, ih8_A_scs. split_scs.
Qed.
Lemma ih8_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff sp mb : Z),
  (7241728 <= ff <= 2 ^ 47 - 4096) -> (140735332483136 <= sp <= 2 ^ 47) -> (0 <= mb <= 2 ^ 64 - 1) ->
  regs_ok (ih8_E R ff sp mb) ih8_sr R -> know_ok bsegs (ih8_E R ff sp mb) m ih8_A_knF ->
  exists R', regs_ok (ih8_E R ff sp mb) (s_regs ih8_A_ss) R' /\ log_flat (ih8_E R ff sp mb) (s_log ih8_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 964356) m rom)
                    (mkst R' (Z_to_bv 64 966912) (mem_denot (ih8_E R ff sp mb) m (s_log ih8_A_ss)) rom).
Proof.
  intros fx R m rom ff sp mb H0 H1 H2 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ih8_A_eq HR HK
              (ih8_A_sc R m ff sp mb H0 H1 H2)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
