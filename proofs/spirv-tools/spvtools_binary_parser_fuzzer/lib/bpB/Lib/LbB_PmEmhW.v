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

Definition xa_E (R : bvmap 5 word) (obj sp keyp : Z) : env := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 sp; Z_to_bv 64 keyp].
Definition xa_sr : list expr := srs sr_id [(2%bv, EVar 33); (10%bv, EVar 32); (11%bv, EVar 34)].
Definition xa_kn : list kentry := [KWord (SA (ELit 0) 1593592) 8 (ELit 1642560); KWord (SA (ELit 0) 1642560) 4 (ELit 1); KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWr (SA (EVar 33) (-64)) (ELit 64); KRange (EVar 33) (2 ^ 46) (2 ^ 47); KAlign (EVar 33) 16].
Definition xa_A_dirs : list bool := [].
Definition xa_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [646232] (SCR xa_A_dirs [] []) 1023632 xa_sr xa_kn 60.
Definition xa_A_x := sym_exec bsegs 400 true [646232] (SCR xa_A_dirs [] []) (SS 1023632 xa_sr [] xa_A_knF 60) [].
Definition xa_A_ss : sym_state := Eval vm_compute in fst (fst xa_A_x).
Definition xa_A_scs : list sidecond := Eval vm_compute in snd (fst xa_A_x).
Lemma xa_A_eq : xa_A_x = (xa_A_ss, xa_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma xa_A_pc : s_pc xa_A_ss = 646232.
Proof. reflexivity. Qed.
Lemma xa_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (obj sp keyp : Z),
  (2 ^ 46 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) ->
  scs_denot bsegs m (xa_E R obj sp keyp) xa_A_scs.
Proof.
  intros R m obj sp keyp H0 H1 H2. unfold xa_E, xa_A_scs. split_scs.
Qed.
Lemma xa_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (obj sp keyp : Z),
  (2 ^ 46 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) ->
  regs_ok (xa_E R obj sp keyp) xa_sr R -> know_ok bsegs (xa_E R obj sp keyp) m xa_A_knF ->
  exists R', regs_ok (xa_E R obj sp keyp) (s_regs xa_A_ss) R' /\ log_flat (xa_E R obj sp keyp) (s_log xa_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1023632) m rom)
                    (mkst R' (Z_to_bv 64 646232) (mem_denot (xa_E R obj sp keyp) m (s_log xa_A_ss)) rom).
Proof.
  intros fx R m rom obj sp keyp H0 H1 H2 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R xa_A_eq HR HK
              (xa_A_sc R m obj sp keyp H0 H1 H2)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition xb_E (R : bvmap 5 word) (ff sq keyp obj sp : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 sq; Z_to_bv 64 keyp; Z_to_bv 64 obj; Z_to_bv 64 sp].
Definition xb_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (9%bv, EVar 33); (18%bv, EVar 34); (20%bv, EVar 35); (8%bv, EVar 36); (19%bv, ELit 2147450880); (1%bv, ELit 1023720)].
Definition xb_kn : list kentry := [KImg 1564672 1597440; KWr (SA (EVar 33) 8) (ELit 8); KWr (SA (EVar 32) 0) (ELit 128); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 16); KRange (EVar 32) 7241728 (2 ^ 47); KAlign (EVar 32) 64; KRange (EVar 33) (2 ^ 46) (2 ^ 47); KAlign (EVar 33) 32].
Definition xb_A_dirs : list bool := [].
Definition xb_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1029704] (SCR xb_A_dirs [] []) 1023720 xb_sr xb_kn 60.
Definition xb_A_x := sym_exec bsegs 400 true [1029704] (SCR xb_A_dirs [] []) (SS 1023720 xb_sr [] xb_A_knF 60) [].
Definition xb_A_ss : sym_state := Eval vm_compute in fst (fst xb_A_x).
Definition xb_A_scs : list sidecond := Eval vm_compute in snd (fst xb_A_x).
Lemma xb_A_eq : xb_A_x = (xb_A_ss, xb_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma xb_A_pc : s_pc xb_A_ss = 1029704.
Proof. reflexivity. Qed.
Lemma xb_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff sq keyp obj sp : Z),
  (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (2 ^ 46 <= sq) -> (sq + 16 <= 2 ^ 47) -> (sq mod 32 = 0) ->
  scs_denot bsegs m (xb_E R ff sq keyp obj sp) xb_A_scs.
Proof.
  intros R m ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6. unfold xb_E, xb_A_scs. split_scs.
Qed.
Lemma xb_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff sq keyp obj sp : Z),
  (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (2 ^ 46 <= sq) -> (sq + 16 <= 2 ^ 47) -> (sq mod 32 = 0) ->
  regs_ok (xb_E R ff sq keyp obj sp) xb_sr R -> know_ok bsegs (xb_E R ff sq keyp obj sp) m xb_A_knF ->
  exists R', regs_ok (xb_E R ff sq keyp obj sp) (s_regs xb_A_ss) R' /\ log_flat (xb_E R ff sq keyp obj sp) (s_log xb_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1023720) m rom)
                    (mkst R' (Z_to_bv 64 1029704) (mem_denot (xb_E R ff sq keyp obj sp) m (s_log xb_A_ss)) rom).
Proof.
  intros fx R m rom ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R xb_A_eq HR HK
              (xb_A_sc R m ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition xc_E (R : bvmap 5 word) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z) : env := Eseed R [Z_to_bv 64 p; Z_to_bv 64 sq; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 0; Z_to_bv 64 ra0; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19; Z_to_bv 64 sv20].
Definition xc_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (9%bv, EVar 33); (8%bv, EVar 36); (18%bv, EVar 37); (20%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 37) (ELit 3)) (ELit 2147450880)); (1%bv, ELit 1023928)].
Definition xc_kn : list kentry := [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 8; KWr (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) (ELit 16); KWr (SA (EVar 37) 0) (ELit 8); KWord (SA (EVar 37) 120) 8 (EVar 38); KWr (SA (EVar 38) 0) (ELit 1); KWord (SA (EVar 36) (-8)) 8 (EVar 40); KWord (SA (EVar 36) (-16)) 8 (EVar 41); KWord (SA (EVar 36) (-24)) 8 (EVar 42); KWord (SA (EVar 36) (-32)) 8 (EVar 43); KWord (SA (EVar 36) (-40)) 8 (EVar 44); KWord (SA (EVar 36) (-48)) 8 (EVar 45); KRange (EVar 37) 7241728 (2 ^ 47); KAlign (EVar 37) 64; KRange (EVar 36) (2 ^ 46) (2 ^ 47); KAlign (EVar 36) 16].
Definition xc_A_dirs : list bool := [].
Definition xc_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1024132] (SCR xc_A_dirs [] []) 1023928 xc_sr xc_kn 60.
Definition xc_A_x := sym_exec bsegs 400 true [1024132] (SCR xc_A_dirs [] []) (SS 1023928 xc_sr [] xc_A_knF 60) [].
Definition xc_A_ss : sym_state := Eval vm_compute in fst (fst xc_A_x).
Definition xc_A_scs : list sidecond := Eval vm_compute in snd (fst xc_A_x).
Lemma xc_A_eq : xc_A_x = (xc_A_ss, xc_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma xc_A_pc : s_pc xc_A_ss = 1024132.
Proof. reflexivity. Qed.
Lemma xc_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z),
  (1 <= p) -> (p + 24 <= 2 ^ 47) -> (p mod 8 = 0) -> (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (7241728 <= fp) -> (fp + 1 <= ff) -> ((fp + 1 <= 2147446784 \/ 17594333495296 <= fp)) -> (2 ^ 46 + 64 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (2 ^ 46 <= sq) -> (sq + 16 <= sp) ->
  scs_denot bsegs m (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) xc_A_scs.
Proof.
  intros R m p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold xc_E, xc_A_scs. split_scs.
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
Lemma xc_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z),
  (1 <= p) -> (p + 24 <= 2 ^ 47) -> (p mod 8 = 0) -> (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (7241728 <= fp) -> (fp + 1 <= ff) -> ((fp + 1 <= 2147446784 \/ 17594333495296 <= fp)) -> (2 ^ 46 + 64 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (2 ^ 46 <= sq) -> (sq + 16 <= sp) ->
  regs_ok (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) xc_sr R -> know_ok bsegs (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) m xc_A_knF ->
  exists R', regs_ok (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) (s_regs xc_A_ss) R' /\ log_flat (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) (s_log xc_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1023928) m rom)
                    (mkst R' (Z_to_bv 64 1024132) (mem_denot (xc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) m (s_log xc_A_ss)) rom).
Proof.
  intros fx R m rom p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R xc_A_eq HR HK
              (xc_A_sc R m p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ua_E (R : bvmap 5 word) (obj sp keyp : Z) : env := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 sp; Z_to_bv 64 keyp].
Definition ua_sr : list expr := srs sr_id [(2%bv, EVar 33); (10%bv, EVar 32); (11%bv, EVar 34)].
Definition ua_kn : list kentry := [KWord (SA (ELit 0) 1593592) 8 (ELit 1642560); KWord (SA (ELit 0) 1642560) 4 (ELit 1); KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWr (SA (EVar 33) (-64)) (ELit 64); KRange (EVar 33) (2 ^ 46) (2 ^ 47); KAlign (EVar 33) 16].
Definition ua_A_dirs : list bool := [].
Definition ua_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [646232] (SCR ua_A_dirs [] []) 1020004 ua_sr ua_kn 60.
Definition ua_A_x := sym_exec bsegs 400 true [646232] (SCR ua_A_dirs [] []) (SS 1020004 ua_sr [] ua_A_knF 60) [].
Definition ua_A_ss : sym_state := Eval vm_compute in fst (fst ua_A_x).
Definition ua_A_scs : list sidecond := Eval vm_compute in snd (fst ua_A_x).
Lemma ua_A_eq : ua_A_x = (ua_A_ss, ua_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ua_A_pc : s_pc ua_A_ss = 646232.
Proof. reflexivity. Qed.
Lemma ua_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (obj sp keyp : Z),
  (2 ^ 46 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) ->
  scs_denot bsegs m (ua_E R obj sp keyp) ua_A_scs.
Proof.
  intros R m obj sp keyp H0 H1 H2. unfold ua_E, ua_A_scs. split_scs.
Qed.
Lemma ua_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (obj sp keyp : Z),
  (2 ^ 46 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) ->
  regs_ok (ua_E R obj sp keyp) ua_sr R -> know_ok bsegs (ua_E R obj sp keyp) m ua_A_knF ->
  exists R', regs_ok (ua_E R obj sp keyp) (s_regs ua_A_ss) R' /\ log_flat (ua_E R obj sp keyp) (s_log ua_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1020004) m rom)
                    (mkst R' (Z_to_bv 64 646232) (mem_denot (ua_E R obj sp keyp) m (s_log ua_A_ss)) rom).
Proof.
  intros fx R m rom obj sp keyp H0 H1 H2 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ua_A_eq HR HK
              (ua_A_sc R m obj sp keyp H0 H1 H2)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition ub_E (R : bvmap 5 word) (ff sq keyp obj sp : Z) : env := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 sq; Z_to_bv 64 keyp; Z_to_bv 64 obj; Z_to_bv 64 sp].
Definition ub_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (9%bv, EVar 33); (18%bv, EVar 34); (20%bv, EVar 35); (8%bv, EVar 36); (19%bv, ELit 2147450880); (1%bv, ELit 1020092)].
Definition ub_kn : list kentry := [KImg 1564672 1597440; KWr (SA (EVar 33) 8) (ELit 8); KWr (SA (EVar 32) 0) (ELit 128); KWr (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 16); KRange (EVar 32) 7241728 (2 ^ 47); KAlign (EVar 32) 64; KRange (EVar 33) (2 ^ 46) (2 ^ 47); KAlign (EVar 33) 32].
Definition ub_A_dirs : list bool := [].
Definition ub_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1024852] (SCR ub_A_dirs [] []) 1020092 ub_sr ub_kn 60.
Definition ub_A_x := sym_exec bsegs 400 true [1024852] (SCR ub_A_dirs [] []) (SS 1020092 ub_sr [] ub_A_knF 60) [].
Definition ub_A_ss : sym_state := Eval vm_compute in fst (fst ub_A_x).
Definition ub_A_scs : list sidecond := Eval vm_compute in snd (fst ub_A_x).
Lemma ub_A_eq : ub_A_x = (ub_A_ss, ub_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma ub_A_pc : s_pc ub_A_ss = 1024852.
Proof. reflexivity. Qed.
Lemma ub_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (ff sq keyp obj sp : Z),
  (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (2 ^ 46 <= sq) -> (sq + 16 <= 2 ^ 47) -> (sq mod 32 = 0) ->
  scs_denot bsegs m (ub_E R ff sq keyp obj sp) ub_A_scs.
Proof.
  intros R m ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6. unfold ub_E, ub_A_scs. split_scs.
Qed.
Lemma ub_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (ff sq keyp obj sp : Z),
  (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (2 ^ 46 <= sq) -> (sq + 16 <= 2 ^ 47) -> (sq mod 32 = 0) ->
  regs_ok (ub_E R ff sq keyp obj sp) ub_sr R -> know_ok bsegs (ub_E R ff sq keyp obj sp) m ub_A_knF ->
  exists R', regs_ok (ub_E R ff sq keyp obj sp) (s_regs ub_A_ss) R' /\ log_flat (ub_E R ff sq keyp obj sp) (s_log ub_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1020092) m rom)
                    (mkst R' (Z_to_bv 64 1024852) (mem_denot (ub_E R ff sq keyp obj sp) m (s_log ub_A_ss)) rom).
Proof.
  intros fx R m rom ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R ub_A_eq HR HK
              (ub_A_sc R m ff sq keyp obj sp H0 H1 H2 H3 H4 H5 H6)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
Definition uc_E (R : bvmap 5 word) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z) : env := Eseed R [Z_to_bv 64 p; Z_to_bv 64 sq; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 0; Z_to_bv 64 ra0; Z_to_bv 64 sv8; Z_to_bv 64 sv9; Z_to_bv 64 sv18; Z_to_bv 64 sv19; Z_to_bv 64 sv20].
Definition uc_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (9%bv, EVar 33); (8%bv, EVar 36); (18%bv, EVar 37); (20%bv, EVar 37); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 37) (ELit 3)) (ELit 2147450880)); (1%bv, ELit 1020300)].
Definition uc_kn : list kentry := [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 8; KWr (SA (EAlu ALU_SRL (EVar 37) (ELit 3)) 2147450880) (ELit 16); KWr (SA (EVar 37) 0) (ELit 8); KWord (SA (EVar 37) 120) 8 (EVar 38); KWr (SA (EVar 38) 0) (ELit 1); KWord (SA (EVar 36) (-8)) 8 (EVar 40); KWord (SA (EVar 36) (-16)) 8 (EVar 41); KWord (SA (EVar 36) (-24)) 8 (EVar 42); KWord (SA (EVar 36) (-32)) 8 (EVar 43); KWord (SA (EVar 36) (-40)) 8 (EVar 44); KWord (SA (EVar 36) (-48)) 8 (EVar 45); KRange (EVar 37) 7241728 (2 ^ 47); KAlign (EVar 37) 64; KRange (EVar 36) (2 ^ 46) (2 ^ 47); KAlign (EVar 36) 16].
Definition uc_A_dirs : list bool := [].
Definition uc_A_knF : list kentry := Eval vm_compute in kn_fixB 30 400 [1020504] (SCR uc_A_dirs [] []) 1020300 uc_sr uc_kn 60.
Definition uc_A_x := sym_exec bsegs 400 true [1020504] (SCR uc_A_dirs [] []) (SS 1020300 uc_sr [] uc_A_knF 60) [].
Definition uc_A_ss : sym_state := Eval vm_compute in fst (fst uc_A_x).
Definition uc_A_scs : list sidecond := Eval vm_compute in snd (fst uc_A_x).
Lemma uc_A_eq : uc_A_x = (uc_A_ss, uc_A_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma uc_A_pc : s_pc uc_A_ss = 1020504.
Proof. reflexivity. Qed.
Lemma uc_A_sc : forall (R : bvmap 5 word) (m : word -> option byte) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z),
  (1 <= p) -> (p + 24 <= 2 ^ 47) -> (p mod 8 = 0) -> (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (7241728 <= fp) -> (fp + 1 <= ff) -> ((fp + 1 <= 2147446784 \/ 17594333495296 <= fp)) -> (2 ^ 46 + 64 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (2 ^ 46 <= sq) -> (sq + 16 <= sp) ->
  scs_denot bsegs m (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) uc_A_scs.
Proof.
  intros R m p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. unfold uc_E, uc_A_scs. split_scs.
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
Lemma uc_A_run : forall (fx : FPState) (R : bvmap 5 word) (m rom : word -> option byte) (p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z),
  (1 <= p) -> (p + 24 <= 2 ^ 47) -> (p mod 8 = 0) -> (7241728 <= ff) -> (ff + 128 <= sq) -> (ff mod 64 = 0) -> ((ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> (7241728 <= fp) -> (fp + 1 <= ff) -> ((fp + 1 <= 2147446784 \/ 17594333495296 <= fp)) -> (2 ^ 46 + 64 <= sp) -> (sp <= 2 ^ 47) -> (sp mod 16 = 0) -> (2 ^ 46 <= sq) -> (sq + 16 <= sp) ->
  regs_ok (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) uc_sr R -> know_ok bsegs (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) m uc_A_knF ->
  exists R', regs_ok (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) (s_regs uc_A_ss) R' /\ log_flat (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) (s_log uc_A_ss)
    /\ msteps bsegs (mkst R (Z_to_bv 64 1020300) m rom)
                    (mkst R' (Z_to_bv 64 1020504) (mem_denot (uc_E R p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20) m (s_log uc_A_ss)) rom).
Proof.
  intros fx R m rom p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR HK.
  destruct (@run_sound fx bsegs _ _ _ _ _ _ _ _ _ _ _ m rom R uc_A_eq HR HK
              (uc_A_sc R m p sq sp ff fp ra0 sv8 sv9 sv18 sv19 sv20 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)) as (R' & HR' & HL & HM).
  exists R'. split; [exact HR'|]. split; [exact HL|]. exact HM.
Qed.
