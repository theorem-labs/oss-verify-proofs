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

Definition h1_E (R : bvmap 5 word) (b code nn e h sp w0 : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 nn; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w0].
Definition h1_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 35); (12%bv, EVar 36); (2%bv, EVar 37)].
Definition h1_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KWord (SA (EVar 33) 0) 4 (EVar 38); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 34) 5 (2 ^ 64 - 1); KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 37) (-64)) (ELit 64); KRange (EVar 38) 0 (2 ^ 32 - 1)].
Definition h1_N_dirs : list bool := [].
Definition h1_N_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h1_N_dirs [] []) 959156 h1_sr h1_kn 50.
Definition h1_N_x := sym_exec bsegs 400 true [1034240] (SCR h1_N_dirs [] []) (SS 959156 h1_sr [] h1_N_knF 50) [].
Definition h1_N_ss : sym_state := Eval vm_compute in fst (fst h1_N_x).
Definition h1_N_scs : list sidecond := Eval vm_compute in snd (fst h1_N_x).
Lemma h1_N_eq : h1_N_x = (h1_N_ss, h1_N_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1_N_pc : s_pc h1_N_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h1_N_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code nn e h sp w0 : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (5 <= nn <= 2 ^ 64 - 1) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0 <= w0 <= 2 ^ 32 - 1) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) ->
  scs_denot bsegs m (h1_E R b code nn e h sp w0) h1_N_scs.
Proof.
  intros R m b code nn e h sp w0 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h1_E, h1_N_scs. split_scs.
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
Lemma h1_N_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code nn e h sp w0 : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (5 <= nn <= 2 ^ 64 - 1) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (0 <= w0 <= 2 ^ 32 - 1) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) ->
  regs_ok (h1_E R b code nn e h sp w0) h1_sr R -> know_ok bsegs (h1_E R b code nn e h sp w0) m h1_N_knF ->
  exists R', regs_ok (h1_E R b code nn e h sp w0) (s_regs h1_N_ss) R' /\ log_flat (h1_E R b code nn e h sp w0) (s_log h1_N_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959156) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h1_E R b code nn e h sp w0) m (s_log h1_N_ss)) rom).
Proof.
  intros fx R m rom b code nn e h sp w0 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1_N_eq HR HK
              (h1_N_sc R m b code nn e h sp w0 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h1s_E (R : bvmap 5 word) (b code nn e h sp : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 nn; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp].
Definition h1s_sr : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 35); (12%bv, EVar 36); (2%bv, EVar 37)].
Definition h1s_kn : list kentry := [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 37) (-64)) (ELit 64); KRange (EVar 34) 0 4].
Definition h1s_S_dirs : list bool := [].
Definition h1s_S_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959836] (SCR h1s_S_dirs [] []) 959156 h1s_sr h1s_kn 50.
Definition h1s_S_x := sym_exec bsegs 400 true [959836] (SCR h1s_S_dirs [] []) (SS 959156 h1s_sr [] h1s_S_knF 50) [].
Definition h1s_S_ss : sym_state := Eval vm_compute in fst (fst h1s_S_x).
Definition h1s_S_scs : list sidecond := Eval vm_compute in snd (fst h1s_S_x).
Lemma h1s_S_eq : h1s_S_x = (h1s_S_ss, h1s_S_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h1s_S_pc : s_pc h1s_S_ss = 959836.
Proof. reflexivity. Qed.
Lemma h1s_S_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code nn e h sp : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= nn <= 4) ->
  scs_denot bsegs m (h1s_E R b code nn e h sp) h1s_S_scs.
Proof.
  intros R m b code nn e h sp H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold h1s_E, h1s_S_scs. split_scs.
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
Lemma h1s_S_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code nn e h sp : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= nn <= 4) ->
  regs_ok (h1s_E R b code nn e h sp) h1s_sr R -> know_ok bsegs (h1s_E R b code nn e h sp) m h1s_S_knF ->
  exists R', regs_ok (h1s_E R b code nn e h sp) (s_regs h1s_S_ss) R' /\ log_flat (h1s_E R b code nn e h sp) (s_log h1s_S_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959156) m rom)
                    (mkst R' (Z_to_bv 64 959836) (mem_denot (h1s_E R b code nn e h sp) m (s_log h1s_S_ss)) rom).
Proof.
  intros fx R m rom b code nn e h sp H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h1s_S_eq HR HK
              (h1s_S_sc R m b code nn e h sp H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h2_E (R : bvmap 5 word) (b code e h sp r1 w : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1].
Definition h2_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h2_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 4) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1)].
Definition h2_A_dirs : list bool := [].
Definition h2_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h2_A_dirs [] []) 959328 h2_sr h2_kn 50.
Definition h2_A_x := sym_exec bsegs 400 true [1034240] (SCR h2_A_dirs [] []) (SS 959328 h2_sr [] h2_A_knF 50) [].
Definition h2_A_ss : sym_state := Eval vm_compute in fst (fst h2_A_x).
Definition h2_A_scs : list sidecond := Eval vm_compute in snd (fst h2_A_x).
Lemma h2_A_eq : h2_A_x = (h2_A_ss, h2_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h2_A_pc : s_pc h2_A_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h2_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  scs_denot bsegs m (h2_E R b code e h sp r1 w) h2_A_scs.
Proof.
  intros R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h2_E, h2_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h2_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  regs_ok (h2_E R b code e h sp r1 w) h2_sr R -> know_ok bsegs (h2_E R b code e h sp r1 w) m h2_A_knF ->
  exists R', regs_ok (h2_E R b code e h sp r1 w) (s_regs h2_A_ss) R' /\ log_flat (h2_E R b code e h sp r1 w) (s_log h2_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959328) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h2_E R b code e h sp r1 w) m (s_log h2_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h2_A_eq HR HK
              (h2_A_sc R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3x_E (R : bvmap 5 word) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1; Z_to_bv 64 fs5; Z_to_bv 64 fs4; Z_to_bv 64 fs3; Z_to_bv 64 fs2; Z_to_bv 64 fs1; Z_to_bv 64 fs0; Z_to_bv 64 fra].
Definition h3x_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h3x_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 8) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1); KWord (SA (EVar 37) (-56)) 8 (EVar 40); KWord (SA (EVar 37) (-48)) 8 (EVar 41); KWord (SA (EVar 37) (-40)) 8 (EVar 42); KWord (SA (EVar 37) (-32)) 8 (EVar 43); KWord (SA (EVar 37) (-24)) 8 (EVar 44); KWord (SA (EVar 37) (-16)) 8 (EVar 45); KWord (SA (EVar 37) (-8)) 8 (EVar 46)].
Definition h3x_A_dirs : list bool := [true].
Definition h3x_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959836] (SCR h3x_A_dirs [] []) 959416 h3x_sr h3x_kn 50.
Definition h3x_A_x := sym_exec bsegs 400 true [959836] (SCR h3x_A_dirs [] []) (SS 959416 h3x_sr [] h3x_A_knF 50) [].
Definition h3x_A_ss : sym_state := Eval vm_compute in fst (fst h3x_A_x).
Definition h3x_A_scs : list sidecond := Eval vm_compute in snd (fst h3x_A_x).
Lemma h3x_A_eq : h3x_A_x = (h3x_A_ss, h3x_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3x_A_pc : s_pc h3x_A_ss = 959836.
Proof. reflexivity. Qed.
Lemma h3x_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (0 <= r1 <= 2 ^ 64 - 1) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 <> 0) ->
  scs_denot bsegs m (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3x_A_scs.
Proof.
  intros R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h3x_E, h3x_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h3x_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (0 <= r1 <= 2 ^ 64 - 1) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 <> 0) ->
  regs_ok (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3x_sr R -> know_ok bsegs (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m h3x_A_knF ->
  exists R', regs_ok (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_regs h3x_A_ss) R' /\ log_flat (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_log h3x_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959416) m rom)
                    (mkst R' (Z_to_bv 64 959836) (mem_denot (h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m (s_log h3x_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3x_A_eq HR HK
              (h3x_A_sc R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3v_E (R : bvmap 5 word) (b code e h sp r1 w : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1].
Definition h3v_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h3v_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 8) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1); KRange (EVar 39) 65536 67072].
Definition h3v_A_dirs : list bool := [false].
Definition h3v_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h3v_A_dirs [] []) 959416 h3v_sr h3v_kn 50.
Definition h3v_A_x := sym_exec bsegs 400 true [1034240] (SCR h3v_A_dirs [] []) (SS 959416 h3v_sr [] h3v_A_knF 50) [].
Definition h3v_A_ss : sym_state := Eval vm_compute in fst (fst h3v_A_x).
Definition h3v_A_scs : list sidecond := Eval vm_compute in snd (fst h3v_A_x).
Lemma h3v_A_eq : h3v_A_x = (h3v_A_ss, h3v_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3v_A_pc : s_pc h3v_A_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h3v_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (65536 <= r1 <= 67072) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  scs_denot bsegs m (h3v_E R b code e h sp r1 w) h3v_A_scs.
Proof.
  intros R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h3v_E, h3v_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h3v_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (65536 <= r1 <= 67072) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  regs_ok (h3v_E R b code e h sp r1 w) h3v_sr R -> know_ok bsegs (h3v_E R b code e h sp r1 w) m h3v_A_knF ->
  exists R', regs_ok (h3v_E R b code e h sp r1 w) (s_regs h3v_A_ss) R' /\ log_flat (h3v_E R b code e h sp r1 w) (s_log h3v_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959416) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h3v_E R b code e h sp r1 w) m (s_log h3v_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3v_A_eq HR HK
              (h3v_A_sc R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3a_E (R : bvmap 5 word) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1; Z_to_bv 64 fs5; Z_to_bv 64 fs4; Z_to_bv 64 fs3; Z_to_bv 64 fs2; Z_to_bv 64 fs1; Z_to_bv 64 fs0; Z_to_bv 64 fra].
Definition h3a_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h3a_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 8) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1); KWord (SA (EVar 37) (-56)) 8 (EVar 40); KWord (SA (EVar 37) (-48)) 8 (EVar 41); KWord (SA (EVar 37) (-40)) 8 (EVar 42); KWord (SA (EVar 37) (-32)) 8 (EVar 43); KWord (SA (EVar 37) (-24)) 8 (EVar 44); KWord (SA (EVar 37) (-16)) 8 (EVar 45); KWord (SA (EVar 37) (-8)) 8 (EVar 46); KRange (EVar 39) 0 65535].
Definition h3a_A_dirs : list bool := [false].
Definition h3a_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959836] (SCR h3a_A_dirs [] []) 959416 h3a_sr h3a_kn 50.
Definition h3a_A_x := sym_exec bsegs 400 true [959836] (SCR h3a_A_dirs [] []) (SS 959416 h3a_sr [] h3a_A_knF 50) [].
Definition h3a_A_ss : sym_state := Eval vm_compute in fst (fst h3a_A_x).
Definition h3a_A_scs : list sidecond := Eval vm_compute in snd (fst h3a_A_x).
Lemma h3a_A_eq : h3a_A_x = (h3a_A_ss, h3a_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3a_A_pc : s_pc h3a_A_ss = 959836.
Proof. reflexivity. Qed.
Lemma h3a_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (0 <= r1 <= 65535) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  scs_denot bsegs m (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3a_A_scs.
Proof.
  intros R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h3a_E, h3a_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h3a_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (0 <= r1 <= 65535) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  regs_ok (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3a_sr R -> know_ok bsegs (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m h3a_A_knF ->
  exists R', regs_ok (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_regs h3a_A_ss) R' /\ log_flat (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_log h3a_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959416) m rom)
                    (mkst R' (Z_to_bv 64 959836) (mem_denot (h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m (s_log h3a_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3a_A_eq HR HK
              (h3a_A_sc R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h3b_E (R : bvmap 5 word) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1; Z_to_bv 64 fs5; Z_to_bv 64 fs4; Z_to_bv 64 fs3; Z_to_bv 64 fs2; Z_to_bv 64 fs1; Z_to_bv 64 fs0; Z_to_bv 64 fra].
Definition h3b_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h3b_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 8) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1); KWord (SA (EVar 37) (-56)) 8 (EVar 40); KWord (SA (EVar 37) (-48)) 8 (EVar 41); KWord (SA (EVar 37) (-40)) 8 (EVar 42); KWord (SA (EVar 37) (-32)) 8 (EVar 43); KWord (SA (EVar 37) (-24)) 8 (EVar 44); KWord (SA (EVar 37) (-16)) 8 (EVar 45); KWord (SA (EVar 37) (-8)) 8 (EVar 46); KRange (EVar 39) 67073 (2 ^ 24 - 1)].
Definition h3b_A_dirs : list bool := [false].
Definition h3b_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959836] (SCR h3b_A_dirs [] []) 959416 h3b_sr h3b_kn 50.
Definition h3b_A_x := sym_exec bsegs 400 true [959836] (SCR h3b_A_dirs [] []) (SS 959416 h3b_sr [] h3b_A_knF 50) [].
Definition h3b_A_ss : sym_state := Eval vm_compute in fst (fst h3b_A_x).
Definition h3b_A_scs : list sidecond := Eval vm_compute in snd (fst h3b_A_x).
Lemma h3b_A_eq : h3b_A_x = (h3b_A_ss, h3b_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h3b_A_pc : s_pc h3b_A_ss = 959836.
Proof. reflexivity. Qed.
Lemma h3b_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (67073 <= r1 <= 2 ^ 24 - 1) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  scs_denot bsegs m (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3b_A_scs.
Proof.
  intros R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. unfold h3b_E, h3b_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h3b_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (67073 <= r1 <= 2 ^ 24 - 1) -> (0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) -> (Z.land r1 18446744073692774655 = 0) ->
  regs_ok (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) h3b_sr R -> know_ok bsegs (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m h3b_A_knF ->
  exists R', regs_ok (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_regs h3b_A_ss) R' /\ log_flat (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_log h3b_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959416) m rom)
                    (mkst R' (Z_to_bv 64 959836) (mem_denot (h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m (s_log h3b_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h3b_A_eq HR HK
              (h3b_A_sc R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h4_E (R : bvmap 5 word) (b code e h sp r1 w : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1].
Definition h4_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h4_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 12) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1)].
Definition h4_A_dirs : list bool := [].
Definition h4_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h4_A_dirs [] []) 959536 h4_sr h4_kn 50.
Definition h4_A_x := sym_exec bsegs 400 true [1034240] (SCR h4_A_dirs [] []) (SS 959536 h4_sr [] h4_A_knF 50) [].
Definition h4_A_ss : sym_state := Eval vm_compute in fst (fst h4_A_x).
Definition h4_A_scs : list sidecond := Eval vm_compute in snd (fst h4_A_x).
Lemma h4_A_eq : h4_A_x = (h4_A_ss, h4_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h4_A_pc : s_pc h4_A_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h4_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  scs_denot bsegs m (h4_E R b code e h sp r1 w) h4_A_scs.
Proof.
  intros R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h4_E, h4_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h4_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  regs_ok (h4_E R b code e h sp r1 w) h4_sr R -> know_ok bsegs (h4_E R b code e h sp r1 w) m h4_A_knF ->
  exists R', regs_ok (h4_E R b code e h sp r1 w) (s_regs h4_A_ss) R' /\ log_flat (h4_E R b code e h sp r1 w) (s_log h4_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959536) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h4_E R b code e h sp r1 w) m (s_log h4_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h4_A_eq HR HK
              (h4_A_sc R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h5_E (R : bvmap 5 word) (b code e h sp r1 w : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1].
Definition h5_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h5_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 16) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 16)) (ELit 3)) 2147450880) 1 (ELit 4)].
Definition h5_A_dirs : list bool := [].
Definition h5_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h5_A_dirs [] []) 959624 h5_sr h5_kn 50.
Definition h5_A_x := sym_exec bsegs 400 true [1034240] (SCR h5_A_dirs [] []) (SS 959624 h5_sr [] h5_A_knF 50) [].
Definition h5_A_ss : sym_state := Eval vm_compute in fst (fst h5_A_x).
Definition h5_A_scs : list sidecond := Eval vm_compute in snd (fst h5_A_x).
Lemma h5_A_eq : h5_A_x = (h5_A_ss, h5_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h5_A_pc : s_pc h5_A_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h5_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  scs_denot bsegs m (h5_E R b code e h sp r1 w) h5_A_scs.
Proof.
  intros R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h5_E, h5_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h5_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  regs_ok (h5_E R b code e h sp r1 w) h5_sr R -> know_ok bsegs (h5_E R b code e h sp r1 w) m h5_A_knF ->
  exists R', regs_ok (h5_E R b code e h sp r1 w) (s_regs h5_A_ss) R' /\ log_flat (h5_E R b code e h sp r1 w) (s_log h5_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959624) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h5_E R b code e h sp r1 w) m (s_log h5_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h5_A_eq HR HK
              (h5_A_sc R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h5z_E (R : bvmap 5 word) (b code e h sp r1 w : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 w; Z_to_bv 64 r1].
Definition h5z_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h5z_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 33) 16) 4 (EVar 38); KRange (EVar 38) 0 (2 ^ 32 - 1)].
Definition h5z_A_dirs : list bool := [].
Definition h5z_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1034240] (SCR h5z_A_dirs [] []) 959624 h5z_sr h5z_kn 50.
Definition h5z_A_x := sym_exec bsegs 400 true [1034240] (SCR h5z_A_dirs [] []) (SS 959624 h5z_sr [] h5z_A_knF 50) [].
Definition h5z_A_ss : sym_state := Eval vm_compute in fst (fst h5z_A_x).
Definition h5z_A_scs : list sidecond := Eval vm_compute in snd (fst h5z_A_x).
Lemma h5z_A_eq : h5z_A_x = (h5z_A_ss, h5z_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h5z_A_pc : s_pc h5z_A_ss = 1034240.
Proof. reflexivity. Qed.
Lemma h5z_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  scs_denot bsegs m (h5z_E R b code e h sp r1 w) h5z_A_scs.
Proof.
  intros R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15. unfold h5z_E, h5z_A_scs. split_scs.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
  - sc_closeB.
Qed.
Lemma h5z_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 w : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (0 <= w <= 2 ^ 32 - 1) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  regs_ok (h5z_E R b code e h sp r1 w) h5z_sr R -> know_ok bsegs (h5z_E R b code e h sp r1 w) m h5z_A_knF ->
  exists R', regs_ok (h5z_E R b code e h sp r1 w) (s_regs h5z_A_ss) R' /\ log_flat (h5z_E R b code e h sp r1 w) (s_log h5z_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959624) m rom)
                    (mkst R' (Z_to_bv 64 1034240) (mem_denot (h5z_E R b code e h sp r1 w) m (s_log h5z_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h5z_A_eq HR HK
              (h5z_A_sc R m b code e h sp r1 w H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition h6_E (R : bvmap 5 word) (b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : env := Eseed R [Z_to_bv 64 b; Z_to_bv 64 code; Z_to_bv 64 0; Z_to_bv 64 e; Z_to_bv 64 h; Z_to_bv 64 sp; Z_to_bv 64 0; Z_to_bv 64 r1; Z_to_bv 64 fs5; Z_to_bv 64 fs4; Z_to_bv 64 fs3; Z_to_bv 64 fs2; Z_to_bv 64 fs1; Z_to_bv 64 fs0; Z_to_bv 64 fra].
Definition h6_sr : list expr := srs sr_id [(2%bv, EAlu ALU_ADD (EVar 37) (ELit (-64))); (8%bv, EVar 32); (9%bv, EVar 36); (18%bv, EVar 35); (19%bv, ELit (-4)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (10%bv, EVar 39)].
Definition h6_kn : list kentry := [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 32) 7241728 (2 ^ 47 - 16); KAlign (EVar 32) 8; KRange (EVar 33) 7241728 (2 ^ 47 - 20); KAlign (EVar 33) 8; KRange (EVar 35) 0 1; KRange (EVar 36) 7241728 (2 ^ 47 - 32); KAlign (EVar 36) 8; KRange (EVar 37) 140735332483136 (2 ^ 47); KAlign (EVar 37) 16; KWr (SA (EVar 36) 0) (ELit 32); KWord (SA (EVar 37) (-56)) 8 (EVar 40); KWord (SA (EVar 37) (-48)) 8 (EVar 41); KWord (SA (EVar 37) (-40)) 8 (EVar 42); KWord (SA (EVar 37) (-32)) 8 (EVar 43); KWord (SA (EVar 37) (-24)) 8 (EVar 44); KWord (SA (EVar 37) (-16)) 8 (EVar 45); KWord (SA (EVar 37) (-8)) 8 (EVar 46)].
Definition h6_A_dirs : list bool := [].
Definition h6_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [959836] (SCR h6_A_dirs [] []) 959712 h6_sr h6_kn 50.
Definition h6_A_x := sym_exec bsegs 400 true [959836] (SCR h6_A_dirs [] []) (SS 959712 h6_sr [] h6_A_knF 50) [].
Definition h6_A_ss : sym_state := Eval vm_compute in fst (fst h6_A_x).
Definition h6_A_scs : list sidecond := Eval vm_compute in snd (fst h6_A_x).
Lemma h6_A_eq : h6_A_x = (h6_A_ss, h6_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma h6_A_pc : s_pc h6_A_ss = 959836.
Proof. reflexivity. Qed.
Lemma h6_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  scs_denot bsegs m (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) h6_A_scs.
Proof.
  intros R m b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold h6_E, h6_A_scs. split_scs.
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
Lemma h6_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
  (7241728 <= b <= 2 ^ 47 - 16) -> (b mod 8 = 0) -> (7241728 <= code <= 2 ^ 47 - 20) -> (code mod 8 = 0) -> (0 <= e <= 1) -> (7241728 <= h <= 2 ^ 47 - 32) -> (h mod 8 = 0) -> (140735332483136 <= sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (b + 16 <= sp - 64 \/ sp <= b) -> (code + 20 <= sp - 64 \/ sp <= code) -> (h + 32 <= sp - 64 \/ sp <= h) -> (h + 32 <= b \/ b + 16 <= h) -> (h + 32 <= code \/ code + 20 <= h) -> (h + 32 <= 2147446784 \/ 17594333495296 <= h) ->
  regs_ok (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) h6_sr R -> know_ok bsegs (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) m h6_A_knF ->
  exists R', regs_ok (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_regs h6_A_ss) R' /\ log_flat (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) (s_log h6_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 959712) m rom)
                    (mkst R' (Z_to_bv 64 959836) (mem_denot (h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) m (s_log h6_A_ss)) rom).
Proof.
  intros fx R m rom b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R h6_A_eq HR HK
              (h6_A_sc R m b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
