(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux
  Hoare RefPrintfBufBase RefPrintfFirst LibTail LibDiagKn MainDefs MainWalk_defs MainArith.
Import ListNotations.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mv := MV { v_sp0 : word; v_tid : word; v_pp : word; v_A : word; v_len : word; v_cap : word; v_A2 : word;
                  v_n : word; v_b8 : word; v_b9 : word; v_b10 : word; v_b11 : word; v_b0 : word; v_b1 : word }.
Definition mvals (v : mv) (regs : bvmap 5 word) : list word :=
  [v_sp0 v; v_tid v; v_pp v; v_A v; v_len v; v_cap v; v_A2 v; v_n v; v_b8 v; v_b9 v; v_b10 v; v_b11 v; v_b0 v; v_b1 v]
  ++ junk_vals regs.
Definition MENV (v : mv) (regs : bvmap 5 word) : env := Env (vals_ev (mvals v regs)) (blobs_ev []).

Lemma mvals_length : forall v regs, length (mvals v regs) = 46%nat.
Proof. intros. unfold mvals. rewrite length_app, junk_vals_length. reflexivity. Qed.

Lemma ev_junk : forall v regs i, (i < 32)%nat -> ev (MENV v regs) (14 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros v regs i Hi. unfold MENV, mvals. cbn [ev]. unfold vals_ev.
  change (14 + i)%nat with (length [v_sp0 v; v_tid v; v_pp v; v_A v; v_len v; v_cap v; v_A2 v; v_n v; v_b8 v; v_b9 v; v_b10 v; v_b11 v; v_b0 v; v_b1 v] + i)%nat.
  rewrite app_nth2_plus. unfold junk_vals.
  rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
Qed.

Lemma ev0 : forall v regs, ev (MENV v regs) 0 = v_sp0 v. Proof. reflexivity. Qed.
Lemma ev2 : forall v regs, ev (MENV v regs) 2 = v_pp v. Proof. reflexivity. Qed.
Lemma ev3 : forall v regs, ev (MENV v regs) 3 = v_A v. Proof. reflexivity. Qed.
Lemma ev4 : forall v regs, ev (MENV v regs) 4 = v_len v. Proof. reflexivity. Qed.
Lemma ev5 : forall v regs, ev (MENV v regs) 5 = v_cap v. Proof. reflexivity. Qed.
Lemma ev6 : forall v regs, ev (MENV v regs) 6 = v_A2 v. Proof. reflexivity. Qed.
Lemma ev7 : forall v regs, ev (MENV v regs) 7 = v_n v. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac mreg_case :=
  lazymatch goal with
  | |- getr ?R ?r = edenot ?E ?e =>
      first [ apply getr_zero
            | lazymatch e with
              | EVar ?n => change (edenot E (EVar n)) with (ev E n);
                           first [ rewrite (ev_junk _ _ (n - 14)) by lia; reflexivity
                                 | cbn [ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
                                   first [reflexivity | assumption | symmetry; assumption] ]
              | ELit _ => cbn [edenot]; first [assumption | symmetry; assumption]
              | spx ?k => unfold spx; mreg_case
              | EAlu ALU_ADD (EVar 0) (ELit ?k) =>
                  cbn [edenot]; rewrite alu_add;
                  cbn [ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
                  lazymatch goal with H : getr R r = _ |- _ => rewrite H end;
                  unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l;
                  f_equal; lia
              end ]
  end.

Ltac prove_regs_ok :=
  lazymatch goal with |- regs_ok _ ?sr _ => unfold sr end;
  apply regs_ok_by_idx; intros i Hi;
  destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
  cbn [nth allregs32]; mreg_case.

(* [comment removed for export] *)
Lemma knL_ok : forall v regs mem,
  valid_sp (v_sp0 v) ->
  stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned (v_sp0 v) - 128)) MSTK ->
  ro_none mem ->
  know_ok RSEGS (MENV v regs) mem knL.
Proof.
  intros v regs mem (Hlo & Hhi & Hal) Hstk Hro. unfold sp_window_lo, sp_window_hi in *.
  unfold knL. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
  - apply kalign_intro; [lia|]. cbn [edenot]. try rewrite ev0. exact Hal.
  - apply krange_intro. cbn [edenot]. try rewrite ev0. lia.
  - cbn [kentry_ok]. split; [apply flat_intro; cbn; try rewrite ev0; unfold MSTK; lia|].
    intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. try rewrite ev0.
    pose proof (Hstk (Z_to_bv 64 (bv_unsigned (v_sp0 v) + (-128 - MSTK) + d)) m) as Hs.
    rewrite !u_small in Hs by (unfold MSTK in *; lia). apply Hs; unfold MSTK in *; lia.
  - cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
    intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
    apply RefPrintfBufBase.data_store_ok; lia.
  - apply kimg_intro; [lia|lia|exact Hro].
Qed.

(* [comment removed for export] *)
Lemma knL_ra_ok : forall v regs mem (ra : Z),
  valid_sp (v_sp0 v) ->
  stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned (v_sp0 v) - 128)) MSTK ->
  ro_none mem -> (0 <= ra < 2 ^ 64)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (v_sp0 v) - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ra)) ->
  know_ok RSEGS (MENV v regs) mem (KWord (SA (EVar 0) (-136)) 8 (ELit ra) :: knL).
Proof.
  intros v regs mem ra Hv Hstk Hro Hra Hrd. pose proof Hv as (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi in *.
  apply Forall_cons; [| apply knL_ok; assumption].
  eapply (kword_intro RSEGS _ mem (EVar 0) (v_sp0 v) (-136) 8 (ELit ra) (Z_to_bv 64 ra));
    [apply ev0 | reflexivity | lia | lia | lia | lia |].
  replace (bv_unsigned (v_sp0 v) + -136)%Z with (bv_unsigned (v_sp0 v) - 136)%Z by lia. exact Hrd.
Qed.

(* [comment removed for export] *)
Definition regL : list sregion := [(SA (EVar 0) (-128 - MSTK), MSTK)]%Z.
Definition regLe : list sregion := [(SA (EVar 0) (-128 - MSTK), MSTK); (SA (ELit 0) 0x2ef3d4, 4)]%Z.
Definition regL_w (sp0 : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128 - MSTK), MSTK)].
Definition regLe_w (sp0 : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128 - MSTK), MSTK); (Z_to_bv 64 0x2ef3d4, 4%Z)].

Lemma regL_denot : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v))%Z ->
  map (rdenot (MENV v regs)) regL = regL_w (v_sp0 v).
Proof.
  intros v regs Hlo. unfold regL, regL_w, rdenot, estart, MSTK. cbn [map fst snd a_base a_off edenot].
  try rewrite ev0. repeat f_equal; lia.
Qed.
Lemma regLe_denot : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v))%Z ->
  map (rdenot (MENV v regs)) regLe = regLe_w (v_sp0 v).
Proof.
  intros v regs Hlo. unfold regLe, regLe_w, rdenot, estart, MSTK. cbn [map fst snd a_base a_off edenot].
  try rewrite ev0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal; lia.
Qed.
Lemma regL_flat : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v) <= 0x800000000000)%Z ->
  regions_flat (MENV v regs) regL.
Proof.
  intros v regs H r Hr. unfold regL, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
  unfold flat, estart; cbn [fst snd a_base a_off edenot]. try rewrite ev0. lia.
Qed.
Lemma regLe_flat : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v) <= 0x800000000000)%Z ->
  regions_flat (MENV v regs) regLe.
Proof.
  intros v regs H r Hr. unfold regLe, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]];
  unfold flat, estart; cbn [fst snd a_base a_off edenot]; try rewrite ev0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
Qed.

Ltac scs_nil :=
  lazymatch goal with
  | |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l'
  | |- Forall _ ?l => let l' := eval vm_compute in l in change l with l'
  end; apply Forall_nil.

(* [comment removed for export] *)
Ltac run_seg scr pc sr kn nx r c E M R :=
  eapply (rz_run_lf RSEGS FUELM STOPSM scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
            (fst (fst c)) (snd (fst c)) (snd c) E M (seg_rom RSEGS) R);
  [ vm_cast_no_check (@eq_refl _ r) | vm_cast_no_check (@eq_refl _ c) | | | | scs_nil | | | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cE := Eval vm_compute in carryM rE knL.
Definition cN := Eval vm_compute in carryM rN knL.
Definition cN' := Eval vm_compute in carryM rN' knL.
Definition cR := Eval vm_compute in carryM rR knL.
Definition cR' := Eval vm_compute in carryM rR' knL.
Definition cL5a := Eval vm_compute in carryM rL5a knL5.
Definition cL5b := Eval vm_compute in carryM rL5b knL5.
Definition cL5c := Eval vm_compute in carryM rL5c knL5.
Definition cMa := Eval vm_compute in carryM rMa knL.
Definition cMb := Eval vm_compute in carryM rMb knL.
Definition cGb := Eval vm_compute in carryM rGb knL.
Definition cGr := Eval vm_compute in carryM rGr knL.
Definition cL2 := Eval vm_compute in carryM rL2 knL.
Definition cL3 := Eval vm_compute in carryM rL3 knL.
Definition cHs := Eval vm_compute in carryM rHs knH.
Definition cHo := Eval vm_compute in carryM rHo knH.
Definition cHk := Eval vm_compute in carryM rHk knH.
Definition cI := Eval vm_compute in carryM rI knL.
Lemma covE : log_covered regL (s_log (fst (fst rE))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covN : log_covered regL (s_log (fst (fst rN))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covN' : log_covered regL (s_log (fst (fst rN'))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covR : log_covered regL (s_log (fst (fst rR))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covR' : log_covered regL (s_log (fst (fst rR'))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covL5a : log_covered regL (s_log (fst (fst rL5a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covL5b : log_covered regL (s_log (fst (fst rL5b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covL5c : log_covered regLe (s_log (fst (fst rL5c))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covMa : log_covered regL (s_log (fst (fst rMa))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covMb : log_covered regL (s_log (fst (fst rMb))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covGb : log_covered regL (s_log (fst (fst rGb))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covGr : log_covered regL (s_log (fst (fst rGr))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covL2 : log_covered regL (s_log (fst (fst rL2))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covL3 : log_covered regL (s_log (fst (fst rL3))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covHs : log_covered regL (s_log (fst (fst rHs))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covHo : log_covered regL (s_log (fst (fst rHo))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covHk : log_covered regL (s_log (fst (fst rHk))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covI : log_covered regL (s_log (fst (fst rI))) = true. Proof. vm_compute. reflexivity. Qed.

Section Blocks.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  Definition base_regs (regs : bvmap 5 word) (pp : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr regs 4 = Z_to_bv 64 0x2ef478 /\ getr regs 8 = Z_to_bv 64 2
    /\ getr regs 18 = pp /\ getr regs 20 = Z_to_bv 64 3.
  (* [comment removed for export] *)
  Definition lbase_regs (regs : bvmap 5 word) (pp : word) : Prop :=
    base_regs regs pp /\ getr regs 22 = Z_to_bv 64 0x2dc8f9.

  (* [comment removed for export] *)
  Ltac unset_v := repeat match goal with w := MV _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => subst w end.
  Ltac fin_reg HR' r :=
    unset_v; regv HR' r; cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
    first [ reflexivity | assumption
          | rewrite ev_junk by lia; first [assumption | symmetry; assumption | reflexivity]
          | ed_lin idtac; unorm; first [reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia] ].
  (* [comment removed for export] *)
  Ltac sc_open :=
    lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end;
    unset_v; repeat apply Forall_cons; try apply Forall_nil;
    cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1]; ed_lin idtac; unorm.
  Ltac fin_base HR' := repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg)].
  Ltac fin_lbase HR' := split; [fin_base HR' | fin_reg HR' (22:reg)].

  (* [comment removed for export] *)
  Ltac mk_frame v regs mem cov EQM LF FR :=
    pose proof (log_covered_frame (MENV v regs) mem regL _ cov (regL_flat v regs ltac:(cbn; lia)) LF) as FR;
    rewrite <- EQM, (regL_denot v regs) in FR by (cbn; lia).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition n_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    lbase_regs regs pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap /\ getr regs 23 = Z_to_bv 64 A.

  Lemma seg_E : forall regs mem (pp : word) (A : Z) K,
    base_regs regs pp -> getr regs 10 = Z_to_bv 64 A -> (0 < A < 2 ^ 64)%Z -> getr regs 21 = Z_to_bv 64 0x10000 ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        n_regs regs' pp A 0 0x10000 ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdd950) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd914) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A K (R2 & R4 & R8 & R18 & R20) R10 HA R21 Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srE0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrE 0xdd914%Z srE0 knL 46%nat rE cE (MENV v regs) mem regs;
      [ exact HR | exact HKn | | exact Hh | exact Hlazy | ].
    { sc_open. unfold bv_eqb. unorm. destruct (Z.eqb_spec A 0); [lia|reflexivity]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rE))) with 0xdd950%Z. change (s_regs (fst (fst rE))) with srE in HR'.
    mk_frame v regs mem covE EQM LF FR.
    apply HK; [| exact FR |].
    - split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
    - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition loop_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    lbase_regs regs pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap /\ getr regs 9 = Z_to_bv 64 A.

  (* [comment removed for export] *)
  Definition read_call_regs (regs : bvmap 5 word) (pp : word) (A len cap cnt : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0x27dfb4 /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) /\ getr regs 4 = Z_to_bv 64 0x2ef478
    /\ getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = Z_to_bv 64 3
    /\ getr regs 11 = Z_to_bv 64 0x2dc8f9 /\ getr regs 12 = Z_to_bv 64 cnt /\ getr regs 17 = Z_to_bv 64 63
    /\ getr regs 18 = pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 20 = Z_to_bv 64 3 /\ getr regs 21 = Z_to_bv 64 cap
    /\ getr regs 22 = Z_to_bv 64 0x2dc8f9.

  (* [comment removed for export] *)
  Ltac read_post HR' := repeat split; try (fin_reg HR' (1:reg)); try (fin_reg HR' (2:reg));
        try (fin_reg HR' (4:reg)); try (fin_reg HR' (8:reg)); try (fin_reg HR' (9:reg)); try (fin_reg HR' (10:reg));
        try (fin_reg HR' (11:reg)); try (fin_reg HR' (12:reg)); try (fin_reg HR' (17:reg)); try (fin_reg HR' (18:reg));
        try (fin_reg HR' (19:reg)); try (fin_reg HR' (20:reg)); try (fin_reg HR' (21:reg)); try (fin_reg HR' (22:reg)); fail "post regs".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_N : forall regs mem (pp : word) (A len cap : Z) K,
    n_regs regs pp A len cap -> (0 <= len < cap)%Z -> (cap < 2 ^ 47)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        read_call_regs regs' pp A len cap (Z.min (cap - len) 65536) ->
        frame_mod mem mem' (regL_w sp0) ->
        rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc)) ->
        stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x27aa74) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd950) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R19 & R21 & R23) Hlen Hcap Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srN0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    assert (POST : forall (r : sym_state * list sidecond * scripts) (c : list kentry * list sidecond * list bool) (cov : log_covered regL (s_log (fst (fst r))) = true) R' M',
      regs_ok (MENV v regs) (s_regs (fst (fst r))) R' -> know_ok RSEGS (MENV v regs) M' (fst (fst c)) ->
      M' = mem_denot (MENV v regs) mem (s_log (fst (fst r))) -> log_flat (MENV v regs) (s_log (fst (fst r))) ->
      ((cap - len < 65536)%Z /\ s_regs (fst (fst r)) = srN \/ (65536 <= cap - len)%Z /\ s_regs (fst (fst r)) = srN') ->
      kread RSEGS (fst (fst c)) (EVar 0) (-136) 8 = Some (ELit 0xdd9bc) ->
      read_call_regs R' pp A len cap (Z.min (cap - len) 65536) /\ frame_mod mem M' (regL_w sp0)
      /\ rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc))
      /\ stk_ok RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { intros r c cov R' M' HR' HK' EQM LF Hsr Hkr.
      mk_frame v regs mem cov EQM LF FR.
      split; [|split; [exact FR|split]].
      - destruct Hsr as [[Hs Esr]|[Hb Esr]]; rewrite Esr in HR';
          [rewrite Z.min_l by lia | rewrite Z.min_r by lia].
        all: read_post HR'.
      - pose proof (kread_rdn RSEGS (MENV v regs) M' (fst (fst c)) (EVar 0) (-136) 8 (ELit 0xdd9bc) HK' Hkr ltac:(lia) ltac:(lia)
                      ltac:(apply flat_intro; cbn; lia)) as Hrd.
        unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_sp0] in Hrd.
        replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in Hrd by lia. exact Hrd.
      - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption. }
    destruct (Z_lt_le_dec (cap - len) 65536) as [Hs|Hb].
    - run_seg scrN 0xdd950%Z srN0 knL 46%nat rN cN (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rN))) with 0x27aa74%Z.
      destruct (POST rN cN covN R' M' HR' HK' EQM LF ltac:(left; split; [exact Hs|reflexivity]) ltac:(vm_compute; reflexivity)) as (P1 & P2 & P3 & P4).
      exact (HK R' M' P1 P2 P3 P4).
    - run_seg scrN' 0xdd950%Z srN0 knL 46%nat rN' cN' (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rN'))) with 0x27aa74%Z.
      destruct (POST rN' cN' covN' R' M' HR' HK' EQM LF ltac:(right; split; [exact Hb|reflexivity]) ltac:(vm_compute; reflexivity)) as (P1 & P2 & P3 & P4).
      exact (HK R' M' P1 P2 P3 P4).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_R : forall regs mem (pp : word) (A len cap : Z) K,
    loop_regs regs pp A len cap -> (0 <= len < cap)%Z -> (cap < 2 ^ 47)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        read_call_regs regs' pp A len cap (Z.min (cap - len) 65536) ->
        frame_mod mem mem' (regL_w sp0) ->
        rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc)) ->
        stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x27aa74) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd99c) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap K (((R2 & R4 & R8 & R18 & R20) & R22) & R19 & R21 & R9) Hlen Hcap Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srR0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    assert (POST : forall (r : sym_state * list sidecond * scripts) (c : list kentry * list sidecond * list bool) (cov : log_covered regL (s_log (fst (fst r))) = true) R' M',
      regs_ok (MENV v regs) (s_regs (fst (fst r))) R' -> know_ok RSEGS (MENV v regs) M' (fst (fst c)) ->
      M' = mem_denot (MENV v regs) mem (s_log (fst (fst r))) -> log_flat (MENV v regs) (s_log (fst (fst r))) ->
      ((cap - len < 65536)%Z /\ s_regs (fst (fst r)) = srR \/ (65536 <= cap - len)%Z /\ s_regs (fst (fst r)) = srR') ->
      kread RSEGS (fst (fst c)) (EVar 0) (-136) 8 = Some (ELit 0xdd9bc) ->
      read_call_regs R' pp A len cap (Z.min (cap - len) 65536) /\ frame_mod mem M' (regL_w sp0)
      /\ rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc))
      /\ stk_ok RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { intros r c cov R' M' HR' HK' EQM LF Hsr Hkr.
      mk_frame v regs mem cov EQM LF FR.
      split; [|split; [exact FR|split]].
      - destruct Hsr as [[Hs Esr]|[Hb Esr]]; rewrite Esr in HR';
          [rewrite Z.min_l by lia | rewrite Z.min_r by lia].
        all: read_post HR'.
      - pose proof (kread_rdn RSEGS (MENV v regs) M' (fst (fst c)) (EVar 0) (-136) 8 (ELit 0xdd9bc) HK' Hkr ltac:(lia) ltac:(lia)
                      ltac:(apply flat_intro; cbn; lia)) as Hrd.
        unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_sp0] in Hrd.
        replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in Hrd by lia. exact Hrd.
      - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption. }
    destruct (Z_lt_le_dec (cap - len) 65536) as [Hs|Hb].
    - run_seg scrR 0xdd99c%Z srR0 knL 46%nat rR cR (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rR))) with 0x27aa74%Z.
      destruct (POST rR cR covR R' M' HR' HK' EQM LF ltac:(left; split; [exact Hs|reflexivity]) ltac:(vm_compute; reflexivity)) as (P1 & P2 & P3 & P4).
      exact (HK R' M' P1 P2 P3 P4).
    - run_seg scrR' 0xdd99c%Z srR0 knL 46%nat rR' cR' (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rR'))) with 0x27aa74%Z.
      destruct (POST rR' cR' covR' R' M' HR' HK' EQM LF ltac:(right; split; [exact Hb|reflexivity]) ltac:(vm_compute; reflexivity)) as (P1 & P2 & P3 & P4).
      exact (HK R' M' P1 P2 P3 P4).
  Qed.

  (* [comment removed for export] *)
  Definition read_ret_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) (res : word) : Prop :=
    getr regs 1 = Z_to_bv 64 0x27dfb4 /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) /\ getr regs 4 = Z_to_bv 64 0x2ef478
    /\ getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = res
    /\ getr regs 18 = pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 20 = Z_to_bv 64 3 /\ getr regs 21 = Z_to_bv 64 cap
    /\ getr regs 22 = Z_to_bv 64 0x2dc8f9.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_L5a : forall regs mem (pp : word) (A len cap n : Z) K,
    read_ret_regs regs pp A len cap (Z_to_bv 64 n) -> (0 < n < 2 ^ 62)%Z -> (0 <= len < 2 ^ 62)%Z -> (0 < A)%Z -> (A + len < 2 ^ 62)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc)) ->
    (forall regs' mem',
        lbase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xdd944 -> getr regs' 9 = Z_to_bv 64 A ->
        getr regs' 10 = Z_to_bv 64 (A + len) -> getr regs' 11 = Z_to_bv 64 0x2dc8f9 -> getr regs' 12 = Z_to_bv 64 n ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap -> getr regs' 23 = Z_to_bv 64 n ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2798bc) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap n K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21 & R22) Hn Hlen HA HAl Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL5) by (apply knL_ra_ok; subst v; try assumption; lia).
    run_seg scrL5a 0x27aa78%Z srL50 knL5 46%nat rL5a cL5a (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open.
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec n 0); [lia|reflexivity].
      - rewrite lts_ZZ by lia. cbn [negb]. destruct (Z.ltb_spec n 0); [lia|reflexivity].
      - rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rL5a))) with 0x2798bc%Z. change (s_regs (fst (fst rL5a))) with srL5a in HR'.
    mk_frame v regs mem covL5a EQM LF FR.
    apply HK; [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg)
              | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_L5b : forall regs mem (pp : word) (A len cap : Z) K,
    read_ret_regs regs pp A len cap (Z_to_bv 64 0) ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc)) ->
    (forall regs' mem',
        getr regs' 1 = Z_to_bv 64 0x27df18 -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) -> getr regs' 4 = Z_to_bv 64 0x2ef478 ->
        getr regs' 8 = Z_to_bv 64 2 -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 3 -> getr regs' 17 = Z_to_bv 64 57 ->
        getr regs' 18 = pp -> getr regs' 19 = Z_to_bv 64 len -> getr regs' 20 = Z_to_bv 64 3 -> getr regs' 21 = Z_to_bv 64 cap ->
        getr regs' 22 = Z_to_bv 64 0x2dc8f9 ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9d4)) ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x27aa74) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21 & R22) Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50z regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL5) by (apply knL_ra_ok; subst v; try assumption; lia).
    run_seg noscr 0x27aa78%Z srL50z knL5 46%nat rL5b cL5b (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rL5b))) with 0x27aa74%Z. change (s_regs (fst (fst rL5b))) with srL5b in HR'.
    mk_frame v regs mem covL5b EQM LF FR.
    apply HK; [fin_reg HR' (1:reg) | fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg)
              | fin_reg HR' (17:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) | fin_reg HR' (21:reg) | fin_reg HR' (22:reg)
              | exact FR | |].
    - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
    - pose proof (kread_rdn RSEGS (MENV v regs) M' (fst (fst cL5b)) (EVar 0) (-136) 8 (ELit 0xdd9d4) HK' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                    ltac:(apply flat_intro; cbn; lia)) as Hrd.
      unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_sp0] in Hrd.
      replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in Hrd by lia. exact Hrd.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_L5c : forall regs mem (pp : word) (A len cap : Z) K,
    read_ret_regs regs pp A len cap (Z_to_bv 64 (2 ^ 64 - 21)) ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9bc)) ->
    (forall regs' mem',
        base_regs regs' pp ->
        frame_mod mem mem' (regLe_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddb10) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21 & R22) Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL50e regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL5) by (apply knL_ra_ok; subst v; try assumption; lia).
    run_seg noscr 0x27aa78%Z srL50e knL5 46%nat rL5c cL5c (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rL5c))) with 0xddb10%Z. change (s_regs (fst (fst rL5c))) with srL5c in HR'.
    pose proof (log_covered_frame (MENV v regs) mem regLe _ covL5c (regLe_flat v regs ltac:(cbn; lia)) LF) as FR.
    rewrite <- EQM, (regLe_denot v regs) in FR by (cbn; lia).
    apply HK; [fin_base HR' | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition m_regs (regs : bvmap 5 word) (pp : word) (A len cap n : Z) : Prop :=
    lbase_regs regs pp /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 cap
    /\ getr regs 23 = Z_to_bv 64 n.

  (* [comment removed for export] *)
  Lemma seg_Ma : forall regs mem (pp : word) (A len cap n : Z) K,
    m_regs regs pp A len cap n -> (0 <= len)%Z -> (0 <= n)%Z -> (len + n < 2 ^ 63)%Z -> (0 <= cap < 2 ^ 63)%Z -> (len + n <> cap)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        n_regs regs' pp A (len + n) cap -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdd950) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd944) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap n K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hl Hn Hln Hcap Hne Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srM0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrMa 0xdd944%Z srM0 knL 46%nat rMa cMa (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open. unfold bv_eqb. unorm. destruct (Z.eqb_spec (len + n) cap); [lia|reflexivity]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rMa))) with 0xdd950%Z. change (s_regs (fst (fst rMa))) with srMa in HR'.
    mk_frame v regs mem covMa EQM LF FR.
    apply HK; [| fin_reg HR' (9:reg) | exact FR |].
    - split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
    - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition g_regs (regs : bvmap 5 word) (pp : word) (A len : Z) : Prop :=
    lbase_regs regs pp /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 21 = Z_to_bv 64 len
    /\ getr regs 23 = Z_to_bv 64 A.

  (* [comment removed for export] *)
  Lemma seg_Mb : forall regs mem (pp : word) (A len cap n : Z) K,
    m_regs regs pp A len cap n -> (0 <= len)%Z -> (0 <= n)%Z -> (0 <= cap < 2 ^ 63)%Z -> (len + n = cap)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        g_regs regs' pp A cap ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdd958) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd944) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap n K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hl Hn Hcap Heq Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srM0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrMb 0xdd944%Z srM0 knL 46%nat rMb cMb (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open. unfold bv_eqb. unorm. rewrite <- Heq, Z.eqb_refl. reflexivity. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rMb))) with 0xdd958%Z. change (s_regs (fst (fst rMb))) with srMb in HR'.
    mk_frame v regs mem covMb EQM LF FR.
    subst cap.
    apply HK; [| exact FR |].
    - split; [fin_lbase HR'|]. repeat split; [fin_reg HR' (9:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg)].
    - intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_Gb : forall regs mem (pp : word) (A len : Z) K,
    g_regs regs pp A len -> (0 <= len < 67108864)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        lbase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xdd970 -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 (2 * len) ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 (2 * len) -> getr regs' 23 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x26f4e8) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd958) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hlen Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srG0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrGb 0xdd958%Z srG0 knL 46%nat rGb cGb (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open.
      (* [comment removed for export] *) rewrite alu_srl. unfold v_srl, bv_eqb. unorm. change (26 mod 64)%Z with 26%Z.
      rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rGb))) with 0x26f4e8%Z. change (s_regs (fst (fst rGb))) with srGb in HR'.
    mk_frame v regs mem covGb EQM LF FR.
    apply HK; [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg)
              | fin_reg HR' (23:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_Gr : forall regs mem (pp : word) (A len : Z) K,
    g_regs regs pp A len -> (67108864 <= len < 2 ^ 62)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        base_regs regs' pp -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddb2c) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd958) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len K (((R2 & R4 & R8 & R18 & R20) & R22) & R9 & R19 & R21 & R23) Hlen Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srG0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrGr 0xdd958%Z srG0 knL 46%nat rGr cGr (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open.
      rewrite alu_srl. unfold v_srl, bv_eqb. unorm. change (26 mod 64)%Z with 26%Z.
      assert (Hq : (0 <= Z.shiftr len 26 < 2 ^ 64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split;
        [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      unorm. rewrite Z.shiftr_div_pow2 in * by lia. cbn [negb].
      destruct (Z.eqb_spec (len / 2 ^ 26) 0) as [E|E]; [|reflexivity].
      exfalso. assert (2 ^ 26 <= len)%Z by lia. pose proof (Z.div_le_mono (2^26) len (2^26) ltac:(lia) ltac:(lia)) as Hd.
      rewrite Z.div_same in Hd by lia. lia. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rGr))) with 0xddb2c%Z. change (s_regs (fst (fst rGr))) with srGr in HR'.
    mk_frame v regs mem covGr EQM LF FR.
    apply HK; [fin_base HR' | fin_reg HR' (9:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_L2 : forall regs mem (pp : word) (A len cap A2 : Z) K,
    lbase_regs regs pp -> getr regs 10 = Z_to_bv 64 A2 -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
    getr regs 9 = Z_to_bv 64 A -> getr regs 23 = Z_to_bv 64 A -> (0 < A2 < 2 ^ 64)%Z -> (0 < len < 2 ^ 64)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        lbase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xdd990 -> getr regs' 9 = Z_to_bv 64 A2 ->
        getr regs' 10 = Z_to_bv 64 A2 -> getr regs' 11 = Z_to_bv 64 A -> getr regs' 12 = Z_to_bv 64 len ->
        getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap -> getr regs' 23 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2798bc) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd970) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap A2 K ((R2 & R4 & R8 & R18 & R20) & R22) R10 R19 R21 R9 R23 HA2 Hlen Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 A2) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL20 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg scrL2 0xdd970%Z srL20 knL 46%nat rL2 cL2 (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open.
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec len 0); [lia|reflexivity].
      - unfold bv_eqb. unorm. destruct (Z.eqb_spec A2 0); [lia|reflexivity]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rL2))) with 0x2798bc%Z. change (s_regs (fst (fst rL2))) with srL2 in HR'.
    mk_frame v regs mem covL2 EQM LF FR.
    apply HK; [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg)
              | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (23:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_L3 : forall regs mem (pp : word) (A len cap A2 : Z) K,
    lbase_regs regs pp -> getr regs 9 = Z_to_bv 64 A2 -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
    getr regs 23 = Z_to_bv 64 A ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        lbase_regs regs' pp -> getr regs' 1 = Z_to_bv 64 0xdd99c -> getr regs' 9 = Z_to_bv 64 A2 ->
        getr regs' 10 = Z_to_bv 64 A -> getr regs' 19 = Z_to_bv 64 len -> getr regs' 21 = Z_to_bv 64 cap ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x26f3a8) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd990) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap A2 K ((R2 & R4 & R8 & R18 & R20) & R22) R9 R19 R21 R23 Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 A2) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srL30 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg noscr 0xdd990%Z srL30 knL 46%nat rL3 cL3 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rL3))) with 0x26f3a8%Z. change (s_regs (fst (fst rL3))) with srL3 in HR'.
    mk_frame v regs mem covL3 EQM LF FR.
    apply HK; [fin_lbase HR' | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_I : forall regs mem (pp : word) (A : Z) (status : word) K,
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x2ef478 -> getr regs 8 = status ->
    getr regs 9 = Z_to_bv 64 A ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    (forall regs' mem',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs' 4 = Z_to_bv 64 0x2ef478 -> getr regs' 8 = status ->
        getr regs' 1 = Z_to_bv 64 0xddae0 -> getr regs' 9 = Z_to_bv 64 A -> getr regs' 10 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x26f3a8) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddad4) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A status K R2 R4 R8 R9 Hstk Hro HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srI0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knL) by (apply knL_ok; subst v; assumption).
    run_seg noscr 0xddad4%Z srI0 knL 46%nat rI cI (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rI))) with 0x26f3a8%Z. change (s_regs (fst (fst rI))) with srI in HR'.
    mk_frame v regs mem covI EQM LF FR.
    apply HK; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (1:reg) | fin_reg HR' (9:reg) | fin_reg HR' (10:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition close_ret_regs (regs : bvmap 5 word) (pp : word) (A len cap : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0x27df18 /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) /\ getr regs 4 = Z_to_bv 64 0x2ef478
    /\ getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 A /\ getr regs 10 = Z_to_bv 64 0
    /\ getr regs 18 = pp /\ getr regs 19 = Z_to_bv 64 len /\ getr regs 20 = Z_to_bv 64 3 /\ getr regs 21 = Z_to_bv 64 cap.

  (* [comment removed for export] *)
  Definition buf_bytes (mem : word -> option byte) (A : Z) (data : list byte) : Prop :=
    forall i, (i < length data)%nat -> rdn RSEGS mem (Z_to_bv 64 (A + Z.of_nat i)) 1 = Some [nth i data (Z_to_bv 8 0)].

  Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
  Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma seg_Hs : forall regs mem (pp : word) (A len cap : Z) K,
    close_ret_regs regs pp A len cap -> (0 <= len <= 5)%Z ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9d4)) ->
    (forall regs' mem',
        base_regs regs' pp -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdda94) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A len cap K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hlen Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply knL_ra_ok; subst v; try assumption; lia).
    run_seg scrHs 0x27aa78%Z srH0 knH 46%nat rHs cHs (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open. rewrite ltu_ZZ by lia. cbn [negb]. destruct (Z.ltb_spec 5 len); [lia|reflexivity]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rHs))) with 0xdda94%Z. change (s_regs (fst (fst rHs))) with srHs in HR'.
    mk_frame v regs mem covHs EQM LF FR.
    apply HK; [fin_base HR' | fin_reg HR' (9:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma hdr_reads : forall v regs mem (A : Z) data M',
    v_A v = Z_to_bv 64 A -> v_b0 v = Z_to_bv 64 (hdr_b data 0) -> v_b1 v = Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)) ->
    (2 <= length data)%nat -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    buf_bytes mem A data -> (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length data))%Z -> M' a = mem a) ->
    sc_denot RSEGS M' (MENV v regs) (SCReadBase (SA (EVar 3) 0) 1 false (EVar 12))
    /\ sc_denot RSEGS M' (MENV v regs) (SCFlat (SA (EVar 3) 0) (ELit 1))
    /\ sc_denot RSEGS M' (MENV v regs) (SCReadBase (SA (EVar 3) 1) 1 true (EVar 13))
    /\ sc_denot RSEGS M' (MENV v regs) (SCFlat (SA (EVar 3) 1) (ELit 1)).
  Proof.
    intros v regs mem A data M' HA Hb0 Hb1 Hl HA0 HAh HB HM.
    assert (RD : forall i, (i < length data)%nat -> rdn RSEGS M' (Z_to_bv 64 (A + Z.of_nat i)) 1 = Some [nth i data (Z_to_bv 8 0)]).
    { intros i Hi. rewrite (rdn_ext RSEGS 1 M' mem); [apply HB; exact Hi | unorm; lia |].
      intros x Hx. apply HM. revert Hx. unorm. intros Hx. lia. }
    cbn [sc_denot]. unfold adenot, v_addi, flat, estart, elenZ. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app].
    rewrite HA, Hb0, Hb1. unorm. repeat split; try lia.
    - exists [nth 0 data (Z_to_bv 8 0)]. split; [rewrite <- (RD 0%nat) by lia; f_equal; f_equal; lia|].
      rewrite bytes_le_to_Z_1. reflexivity.
    - exists [nth 1 data (Z_to_bv 8 0)]. split; [rewrite <- (RD 1%nat) by lia; f_equal; f_equal; lia|].
      rewrite bytes_le_to_Z_1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfg_expr_val : forall v regs data,
    v_b0 v = Z_to_bv 64 (hdr_b data 0) -> v_b1 v = Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)) ->
    edenot (MENV v regs) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))
    = Z_to_bv 64 (hdr_cfg data).
  Proof.
    intros v regs data Hb0 Hb1. cbn [edenot ev MENV mvals vals_ev nth app]. rewrite Hb0, Hb1.
    rewrite alu_or, alu_srl, m_mul. change 144115188075855872%Z with (2 ^ 57)%Z.
    rewrite cfg_word by apply hdr_b_range. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma seg_Ho : forall regs mem (pp : word) (A cap : Z) (data : list byte) K,
    close_ret_regs regs pp A (Z.of_nat (length data)) cap -> (6 <= length data)%nat ->
    (Z.of_nat (length data) < 6 + hdr_cfg data)%Z -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    (A + Z.of_nat (length data) <= bv_unsigned sp0 - 128 - MSTK \/ bv_unsigned sp0 <= A)%Z ->
    buf_bytes mem A data ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9d4)) ->
    (forall regs' mem',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs' 4 = Z_to_bv 64 0x2ef478 -> getr regs' 8 = Z_to_bv 64 2 ->
        getr regs' 20 = Z_to_bv 64 3 -> getr regs' 9 = Z_to_bv 64 A ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddab0) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A cap data K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hl6 Hov HA0 HAh Hdisj HB Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_cfg_range data) as Hcr.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 cap) (getr regs 22) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (hdr_b data 0)) (Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)))).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply knL_ra_ok; subst v; try assumption; lia).
    (* [comment removed for export] *)
    eapply (rz_run_lf RSEGS FUELM STOPSM scrHo 0x27aa78%Z srH0 knH 46%nat (fst (fst rHo)) (snd (fst rHo)) (snd rHo)
              (fst (fst cHo)) (snd (fst cHo)) (snd cHo) (MENV v regs) mem (seg_rom RSEGS) regs);
      [ vm_cast_no_check (@eq_refl _ rHo) | vm_cast_no_check (@eq_refl _ cHo) | exact HR | exact HKn | | scs_nil | exact Hh | exact Hlazy | ].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      destruct (hdr_reads v regs mem A data mem eq_refl eq_refl eq_refl ltac:(lia) HA0 HAh HB ltac:(intros; reflexivity)) as (S1 & S2 & S3 & S4).
      repeat apply Forall_cons; try apply Forall_nil; try assumption.
      - cbn [sc_denot branch_taken]. rewrite ed_add, (cfg_expr_val v regs data eq_refl eq_refl), ed_lit, vadd_ZZ.
        cbn [edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. apply Z.ltb_lt. lia.
      - unset_v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. cbn [negb].
        destruct (Z.ltb_spec 5 (Z.of_nat (length data))); [reflexivity|lia]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rHo))) with 0xddab0%Z. change (s_regs (fst (fst rHo))) with srHo in HR'.
    mk_frame v regs mem covHo EQM LF FR.
    apply HK; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (20:reg) | fin_reg HR' (9:reg) | exact FR |].
    intros a m Ha Hm. eapply frame_mod_store_ok; [exact FR|]. apply Hstk; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition tr_call_regs (regs : bvmap 5 word) (A len cfg sb1 : Z) : Prop :=
    getr regs 1 = Z_to_bv 64 0xdda4c /\ getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr regs 4 = Z_to_bv 64 0x2ef478
    /\ getr regs 8 = Z_to_bv 64 (A + 2) /\ getr regs 9 = Z_to_bv 64 A
    /\ getr regs 10 = Z_to_bv 64 (A + 2) /\ getr regs 11 = Z_to_bv 64 cfg
    /\ getr regs 12 = Z_to_bv 64 (A + 2 + cfg + 4) /\ getr regs 13 = Z_to_bv 64 (len - 6 - cfg)
    /\ getr regs 18 = Z_to_bv 64 cfg /\ getr regs 19 = Z_to_bv 64 (A + 2 + cfg + 4) /\ getr regs 20 = Z_to_bv 64 (len - 6 - cfg)
    /\ getr regs 21 = Z_to_bv 64 sb1.

  (* [comment removed for export] *)
  Lemma seg_Hk : forall regs mem (pp : word) (A cap : Z) (data : list byte) K,
    close_ret_regs regs pp A (Z.of_nat (length data)) cap ->
    (6 + hdr_cfg data <= Z.of_nat (length data))%Z -> (0 < A)%Z -> (A + Z.of_nat (length data) < 2 ^ 47)%Z ->
    buf_bytes mem A data ->
    stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK -> ro_none mem ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd9d4)) ->
    (forall regs' mem',
        tr_call_regs regs' A (Z.of_nat (length data)) (hdr_cfg data) (bv_swrap 8 (hdr_b data 1)) ->
        frame_mod mem mem' (regL_w sp0) -> stk_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddbc0) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x27aa78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem pp A cap data K (R1 & R2 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21) Hok HA0 HAh HB Hstk Hro Hra HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_cfg_range data) as Hcr.
    set (cfg := hdr_cfg data) in *.
    set (v := MV sp0 (Z_to_bv 64 0) pp (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 cap) (getr regs 22) (Z_to_bv 64 0)
                 (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 2))) (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 3)))
                 (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 4))) (Z_to_bv 64 (hdr_b data (Z.to_nat cfg + 5)))
                 (Z_to_bv 64 (hdr_b data 0)) (Z_to_bv 64 (bv_swrap 8 (hdr_b data 1)))).
    assert (HR : regs_ok (MENV v regs) srH0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knH) by (apply knL_ra_ok; subst v; try assumption; lia).
    assert (CFG : edenot (MENV v regs) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))
                  = Z_to_bv 64 cfg) by (subst cfg; apply cfg_expr_val; reflexivity).
    (* [comment removed for export] *)
    assert (BM : forall (k : Z) (j : nat), (2 <= k <= 5)%Z -> j = (Z.to_nat cfg + Z.to_nat k)%nat ->
      sc_denot RSEGS mem (MENV v regs)
        (SCReadBase (SA (EAlu ALU_ADD (EVar 3) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))) k)
                    1 false (ELit (hdr_b data j)))
      /\ sc_denot RSEGS mem (MENV v regs)
        (SCFlat (SA (EAlu ALU_ADD (EVar 3) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 13)) (ELit 49)) (EVar 12))) k) (ELit 1))).
    { intros k j Hk Hj. cbn [sc_denot]. unfold adenot, v_addi, flat, estart, elenZ. cbn [a_base a_off].
      rewrite ed_add, CFG. cbn [edenot ev MENV mvals vals_ev nth app v_A]. rewrite vadd_ZZ. unorm.
      split; [| lia]. exists [nth j data (Z_to_bv 8 0)]. split.
      - rewrite <- (HB j) by lia. f_equal. f_equal. lia.
      - rewrite bytes_le_to_Z_1. cbn [extz]. reflexivity. }
    eapply (rz_run_lf RSEGS FUELM STOPSM scrHk 0x27aa78%Z srH0 knH 46%nat (fst (fst rHk)) (snd (fst rHk)) (snd rHk)
              (fst (fst cHk)) (snd (fst cHk)) (snd cHk) (MENV v regs) mem (seg_rom RSEGS) regs);
      [ vm_cast_no_check (@eq_refl _ rHk) | vm_cast_no_check (@eq_refl _ cHk) | exact HR | exact HKn | | scs_nil | exact Hh | exact Hlazy | ].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      destruct (hdr_reads v regs mem A data mem eq_refl eq_refl eq_refl ltac:(lia) HA0 HAh HB ltac:(intros; reflexivity)) as (S1 & S2 & S3 & S4).
      destruct (BM 5%Z (Z.to_nat cfg + 5)%nat ltac:(lia) ltac:(lia)) as [B5 F5].
      destruct (BM 4%Z (Z.to_nat cfg + 4)%nat ltac:(lia) ltac:(lia)) as [B4 F4].
      destruct (BM 2%Z (Z.to_nat cfg + 2)%nat ltac:(lia) ltac:(lia)) as [B2 F2].
      destruct (BM 3%Z (Z.to_nat cfg + 3)%nat ltac:(lia) ltac:(lia)) as [B3 F3].
      repeat apply Forall_cons; try apply Forall_nil; try assumption.
      - cbn [sc_denot branch_taken]. rewrite ed_add, CFG, ed_lit, vadd_ZZ.
        cbn [edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. apply Z.ltb_ge. lia.
      - unset_v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_len]. rewrite ltu_ZZ by lia. cbn [negb].
        destruct (Z.ltb_spec 5 (Z.of_nat (length data))); [reflexivity|lia]. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rHk))) with 0xddbc0%Z. change (s_regs (fst (fst rHk))) with srHk in HR'.
    mk_frame v regs mem covHk EQM LF FR.
    apply HK; [| exact FR | intros a m Ha Hm; eapply frame_mod_store_ok; [exact FR|]; apply Hstk; assumption].
    unfold tr_call_regs. unset_v.
    repeat split;
      lazymatch goal with |- getr R' ?r = _ =>
        regv HR' r; rewrite ?ed_add, ?ed_mul, ?CFG, ?ed_lit, ?ed_var;
        cbn [ev MENV mvals vals_ev nth app v_sp0 v_A v_len v_b1]; ed_lin idtac; unorm;
        first [ reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia ]
      end.
  Qed.
End Blocks.
