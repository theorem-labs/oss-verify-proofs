(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux
  Spec RefNodes LibTail LibDiagKn RefPrintfFirst RefPrintfBufBase
  MainDefs MainArith MainWalk_defs MainSegs TRWalk_defs.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition cT0b := Eval vm_compute in carryM rT0b knT.
Definition cTA := Eval vm_compute in carryM rTA knT.
Definition cT1a := Eval vm_compute in carryM rT1a knT.
Definition cT1b := Eval vm_compute in carryM rT1b knT.
Definition cT1c := Eval vm_compute in carryM rT1c knT.
Definition cT1d := Eval vm_compute in carryM rT1d knT.
Definition cT2 := Eval vm_compute in carryM rT2 knT.
Definition cT3 := Eval vm_compute in carryM rT3 knT.
Definition cT4 := Eval vm_compute in carryM rT4 knT.
Definition cT5 := Eval vm_compute in carryM rT5 knT.
Definition cT6 := Eval vm_compute in carryM rT6 knT.
Definition cT7a := Eval vm_compute in carryM rT7a knT.
Definition cT7b := Eval vm_compute in carryM rT7b knT.
Definition cT7z := Eval vm_compute in carryM rT7z knT.
Definition cT8 := Eval vm_compute in carryM rT8 knT8.

(* [comment removed for export] *)
Definition regT : list sregion := [(SA (EVar 0) (-80), 80)]%Z.
Definition regTb : list sregion := [(SA (EVar 0) (-80), 80); (SA (ELit 0) 0x90c70, 1)]%Z.
Definition regTc : list sregion := [(SA (ELit 0) 0x90c74, 1)]%Z.
Definition regT_w (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 80), 80%Z)].
Definition regTb_w (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 80), 80%Z); (Z_to_bv 64 0x90c70, 1%Z)].
Definition regTc_w (sp : word) : list (word * Z) := [(Z_to_bv 64 0x90c74, 1%Z)].

Lemma covT0b : log_covered regTb (s_log (fst (fst rT0b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covTA : log_covered regT (s_log (fst (fst rTA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT1a : log_covered regT (s_log (fst (fst rT1a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT1b : log_covered regT (s_log (fst (fst rT1b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT1c : log_covered regT (s_log (fst (fst rT1c))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT1d : log_covered regT (s_log (fst (fst rT1d))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT2 : log_covered regT (s_log (fst (fst rT2))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT3 : log_covered regT (s_log (fst (fst rT3))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT4 : log_covered regT (s_log (fst (fst rT4))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT5 : log_covered regTc (s_log (fst (fst rT5))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT6 : log_covered regTc (s_log (fst (fst rT6))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT7a : log_covered regT (s_log (fst (fst rT7a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT7b : log_covered regT (s_log (fst (fst rT7b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT7z : log_covered regT (s_log (fst (fst rT7z))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT8 : log_covered regT (s_log (fst (fst rT8))) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac run_segT stops scr pc sr kn nx r c E M R :=
  eapply (rz_run_lf RSEGS FUELM stops scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
            (fst (fst c)) (snd (fst c)) (snd c) E M (seg_rom RSEGS) R);
  [ vm_cast_no_check (@eq_refl _ r) | vm_cast_no_check (@eq_refl _ c) | | | | scs_nil | | | ].

Section BlocksT.
  Variable sp : word.          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hsp16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HspLo : (0x7fff7f811000 <= bv_unsigned sp)%Z.
  Hypothesis HspHi : (bv_unsigned sp <= 0x7fffffffff80)%Z.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].

  (* [comment removed for export] *)
  Definition TV (CP cfg N D ib c r PL OW S3 : word) : mv :=
    MV sp CP cfg N D ib c r PL (Z_to_bv 64 0) OW S3 (Z_to_bv 64 0) (Z_to_bv 64 0).

  Ltac evs := cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV].
  Ltac unset_v := repeat match goal with w := TV _ _ _ _ _ _ _ _ _ _ |- _ => subst w | w := MV _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => subst w end.
  Ltac fin_reg HR' r :=
    unset_v; regv HR' r; cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV];
    first [ reflexivity | assumption
          | rewrite ev_junk by lia; first [assumption | symmetry; assumption | reflexivity]
          | ed_lin idtac; unorm; first [reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia] ].
  (* [comment removed for export] *)
  Ltac sc_eqb :=
    rewrite ?eqb_ZZ by lia;
    first [ apply Z.eqb_eq; lia
          | apply Z.eqb_neq; lia
          | rewrite Bool.negb_true_iff; apply Z.eqb_neq; lia
          | reflexivity ].
  Ltac sc_open :=
    lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end;
    unset_v; repeat apply Forall_cons; try apply Forall_nil;
    cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV]; ed_lin idtac; unorm.
  Ltac evs_in H := cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV] in H.

  Lemma knT_ok : forall v regs mem,
    v_sp0 v = sp ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    know_ok RSEGS (MENV v regs) mem knT.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs mem Ev Hstk Hro Hrel. cbn in Ev. subst v0.
    unfold knT. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. evs. exact Hsp16.
    - apply krange_intro. evs. lia.
    - cbn [kentry_ok]. split; [apply flat_intro; evs; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. evs.
      pose proof (Hstk (Z_to_bv 64 (bv_unsigned sp + -80 + d)) m) as Hs.
      rewrite !u_small in Hs by lia. apply Hs; lia.
    - cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply RefPrintfBufBase.data_store_ok; lia.
    - apply kimg_intro; [lia|lia|exact Hro].
    - apply kimg_intro; [lia|lia|exact Hrel].
  Qed.

  Lemma regT_denot : forall v regs, v_sp0 v = sp -> map (rdenot (MENV v regs)) regT = regT_w sp.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev. cbn in Ev. subst v0. unfold regT, regT_w, rdenot, estart. cbn [map fst snd a_base a_off]. evs.
    repeat f_equal; lia.
  Qed.
  Lemma regTb_denot : forall v regs, v_sp0 v = sp -> map (rdenot (MENV v regs)) regTb = regTb_w sp.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev. cbn in Ev. subst v0. unfold regTb, regTb_w, rdenot, estart. cbn [map fst snd a_base a_off]. evs.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal; lia.
  Qed.
  Lemma regTc_denot : forall v regs, v_sp0 v = sp -> map (rdenot (MENV v regs)) regTc = regTc_w sp.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev. cbn in Ev. subst v0. unfold regTc, regTc_w, rdenot, estart. cbn [map fst snd a_base a_off]. evs.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal.
  Qed.
  Lemma regT_flat : forall v regs, v_sp0 v = sp -> regions_flat (MENV v regs) regT.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev r Hr. cbn in Ev. subst v0. unfold regT in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
    unfold flat, estart; cbn [fst snd a_base a_off]. evs. lia.
  Qed.
  Lemma regTb_flat : forall v regs, v_sp0 v = sp -> regions_flat (MENV v regs) regTb.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev r Hr. cbn in Ev. subst v0. unfold regTb in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]];
    unfold flat, estart; cbn [fst snd a_base a_off]; evs; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.
  Lemma regTc_flat : forall v regs, v_sp0 v = sp -> regions_flat (MENV v regs) regTc.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev r Hr. cbn in Ev. subst v0. unfold regTc in Hr. cbn [In] in Hr. destruct Hr as [<-|[]];
    unfold flat, estart; cbn [fst snd a_base a_off]; evs; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac mk_frameT v regs mem regs_ cov den flt EQM LF FR Ev :=
    pose proof (log_covered_frame (MENV v regs) mem regs_ _ cov (flt v regs Ev) LF) as FR;
    rewrite <- EQM, (den v regs Ev) in FR.

  (* [comment removed for export] *)
  Lemma stk_after : forall mem mem' rs, frame_mod mem mem' rs -> stk_ok RSEGS mem sp 80 -> stk_ok RSEGS mem' sp 80.
  Proof. intros mem mem' rs FM Hstk a m Ha Hm. eapply frame_mod_store_ok; [exact FM|]. apply Hstk; assumption. Qed.

  (* [comment removed for export] *)
  Definition tframe (mem : word -> option byte) (s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2addc))
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (word_to_le_bytes 8 s0)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8 = Some (word_to_le_bytes 8 s1)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8 = Some (word_to_le_bytes 8 s2)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 40)) 8 = Some (word_to_le_bytes 8 s3)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 48)) 8 = Some (word_to_le_bytes 8 s4)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 56)) 8 = Some (word_to_le_bytes 8 s5)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 64)) 8 = Some (word_to_le_bytes 8 s6)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 72)) 8 = Some (word_to_le_bytes 8 s7).

  (* [comment removed for export] *)
  Definition regs118 (regs : bvmap 5 word) (N PL cfg CP : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 80) /\ getr regs 4 = Z_to_bv 64 0x92650 /\ getr regs 8 = N
    /\ getr regs 9 = PL /\ getr regs 18 = cfg /\ getr regs 19 = CP /\ getr regs 20 = Z_to_bv 64 0x90c70.
  (* [comment removed for export] *)
  Definition loop_base (regs : bvmap 5 word) (N D OW : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 80) /\ getr regs 4 = Z_to_bv 64 0x92650 /\ getr regs 8 = N
    /\ getr regs 9 = D /\ getr regs 18 = OW /\ getr regs 20 = Z_to_bv 64 0x90c70
    /\ getr regs 22 = Z_to_bv 64 0 /\ getr regs 23 = Z_to_bv 64 18446744073709551614.

  (* [comment removed for export] *)
  Definition keep4 (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, In r [24; 25; 26; 27]%list -> getr regs' r = getr regs r.
  Ltac fin_keep4 HR' :=
    intros rr Hrr; cbn [In] in Hrr;
    destruct Hrr as [<-|[<-|[<-|[<-|[]]]]];
    [fin_reg HR' (24:reg) | fin_reg HR' (25:reg) | fin_reg HR' (26:reg) | fin_reg HR' (27:reg)].

  Ltac fin_tframe HK' v :=
    unfold tframe; subst v;
    repeat split;
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 (bv_unsigned sp - ?k)) 8 = _ =>
        let off := eval vm_compute in (- k)%Z in
        let Hrd := fresh "Hrd" in
        krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot ev MENV mvals vals_ev nth app TV v_sp0]; lia|];
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev MENV mvals vals_ev nth app TV v_sp0] in Hrd;
        rewrite ?ev_junk in Hrd by lia;
        replace (bv_unsigned sp - k)%Z with (bv_unsigned sp + off)%Z by lia; exact Hrd
      end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T0b : forall regs mem (CP cfg PL N : word) K,
    getr regs 1 = Z_to_bv 64 0x2addc -> getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x92650 ->
    getr regs 10 = CP -> getr regs 11 = cfg -> getr regs 12 = PL -> getr regs 13 = N ->
    rdn RSEGS mem (Z_to_bv 64 0x90c70) 1 = Some [Z_to_bv 8 0] ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs' mem',
        regs118 regs' N PL cfg CP -> getr regs' 1 = Z_to_bv 64 0x2afcc -> getr regs' 10 = Z_to_bv 64 0x2b090 ->
        keep4 regs regs' -> frame_mod mem mem' (regTb_w sp) -> stk_ok RSEGS mem' sp 80 ->
        tframe mem' (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) ->
        rdn RSEGS mem' (Z_to_bv 64 0x90c70) 1 = Some [Z_to_bv 8 1] ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x67760) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2af38) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem CP cfg PL N K R1 R2 R4 R10 R11 R12 R13 Hib Hstk Hro Hrel HK.
    set (v := TV CP cfg N (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT00 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (RD : sc_denot RSEGS mem (MENV v regs) (SCReadBase (SA (ELit 0) 0x90c70) 1 false (EVar 5))).
    { cbn [sc_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_cap TV].
      rewrite (u_small 0) by lia. cbn [Z.add]. exists [Z_to_bv 8 0]. split; [exact Hib|].
      rewrite bytes_le_to_Z_1. cbn [extz]. subst v. cbn [v_cap]. reflexivity. }
    run_segT STOPST scrT0b 0x2af38%Z srT00 knT 46%nat rT0b cT0b (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [| apply Forall_cons; [exact RD | apply Forall_nil]].
      subst v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app TV v_cap]. unfold bv_eqb.
      rewrite u_small by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. reflexivity. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT0b))) with 0x67760%Z. change (s_regs (fst (fst rT0b))) with srT0b in HR'.
    mk_frameT v regs mem regTb covT0b regTb_denot regTb_flat EQM LF FR (@eq_refl word sp).
    apply HK.
    + unfold regs118. subst v. repeat split;
        first [ fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) ].
    + fin_reg HR' (1:reg).
    + fin_reg HR' (10:reg).
    + fin_keep4 HR'.
    + exact FR.
    + eapply stk_after; [exact FR | exact Hstk].
    + fin_tframe HK' v.
    + krd HK' 0x90c70%Z 1%nat Hrd. exact Hrd.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_TA : forall regs mem (N PL cfg CP : word) K,
    regs118 regs N PL cfg CP -> getr regs 10 = Z_to_bv 64 0 ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        regs118 regs' N PL cfg CP -> keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2af80) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2afcc) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N PL cfg CP K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R10 Hstk Hro Hrel HK.
    set (v := TV CP cfg N (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srTA0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr 0x2afcc%Z srTA0 knT 46%nat rTA cTA (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rTA))) with 0x2af80%Z. change (s_regs (fst (fst rTA))) with srTA in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_keep4 HR'].
    unfold regs118. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
  Qed.

  Lemma vand3 : forall (c : byte), v_and (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 3) = Z_to_bv 64 (Z.land (bv_unsigned c) 3).
  Proof.
    intros c. pose proof (bv_unsigned_in_range 8 c) as H. unfold bv_modulus in H. cbn in H.
    unfold v_and. rewrite !u_small by lia. reflexivity.
  Qed.

  Lemma land3_range : forall z, (0 <= z)%Z -> (0 <= Z.land z 3 <= 3)%Z.
  Proof.
    intros z Hz. replace (Z.land z 3) with (z mod 4)%Z by (symmetry; apply (Z.land_ones z 2); lia).
    pose proof (Z.mod_pos_bound z 4 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma byte_read_val : forall (b : byte), Z_to_bv 64 (bytes_le_to_Z [b]) = Z_to_bv 64 (bv_unsigned b).
  Proof. intros b. rewrite bytes_le_to_Z_1. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition calls_of (cfgz : Z) (c : byte) : Z := if (cfgz =? 0)%Z then 1 else Z.land (bv_unsigned c) 3 + 1.

  Lemma calls_of_range : forall cfgz c, (1 <= calls_of cfgz c <= 4)%Z.
  Proof. intros. unfold calls_of. destruct (cfgz =? 0)%Z; [lia|]. pose proof (land3_range (bv_unsigned c) ltac:(pose proof (bv_unsigned_in_range 8 c); lia)). lia. Qed.

  Lemma seg_T1pos : forall regs mem (Nz cfgz : Z) (PL CP : word) (c : byte) K,
    regs118 regs (Z_to_bv 64 Nz) PL (Z_to_bv 64 cfgz) CP -> (0 < Nz < 2 ^ 62)%Z -> (0 <= cfgz < 2 ^ 62)%Z ->
    (cfgz <> 0%Z -> rdn RSEGS mem CP 1 = Some [c]) -> (bv_unsigned CP + 1 < 2 ^ 64)%Z ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        regs118 regs' (Z_to_bv 64 Nz) PL (Z_to_bv 64 cfgz) CP -> getr regs' 21 = Z_to_bv 64 (calls_of cfgz c) ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2af94) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2af80) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem Nz cfgz PL CP c K (R2 & R4 & R8 & R9 & R18 & R19 & R20) HN Hcfg Hc HCP Hstk Hro Hrel HK.
    pose proof (bv_unsigned_in_range 8 c) as Hc8. cbn in Hc8. pose proof (u64_range CP) as HCPr.
    set (v := TV CP (Z_to_bv 64 cfgz) (Z_to_bv 64 Nz) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 0) PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT10 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    destruct (Z.eq_dec cfgz 0) as [C0|C0].
    - run_segT STOPST scrT1c 0x2af80%Z srT10 knT 46%nat rT1c cT1c (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open; sc_eqb. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT1c))) with 0x2af94%Z. change (s_regs (fst (fst rT1c))) with srT1c in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply HK; [| | fin_keep4 HR'].
      + unfold regs118. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_eq _ _) C0). fin_reg HR' (21:reg).
    - run_segT STOPST scrT1a 0x2af80%Z srT10 knT 46%nat rT1a cT1a (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open.
        - sc_eqb.
        - unfold adenot, v_addi. cbn [a_base a_off]. evs. exists [c]. split; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (Hc C0) | rewrite bytes_le_to_Z_1; reflexivity].
        - apply flat_intro; unfold elenZ; evs; unorm; rewrite ?u_small by lia; lia.
        - sc_eqb. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT1a))) with 0x2af94%Z. change (s_regs (fst (fst rT1a))) with srT1a in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply HK; [| | fin_keep4 HR'].
      + unfold regs118. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) C0). unset_v. regv HR' (21:reg). cbn [edenot]. evs.
        rewrite alu_add, alu_and, vand3, vadd_ZZ. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T1zero : forall regs mem (cfgz : Z) (PL CP : word) (c : byte) K,
    regs118 regs (Z_to_bv 64 0) PL (Z_to_bv 64 cfgz) CP -> (0 <= cfgz < 2 ^ 62)%Z ->
    (cfgz <> 0%Z -> rdn RSEGS mem CP 1 = Some [c]) -> (bv_unsigned CP + 1 < 2 ^ 64)%Z ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        loop_base regs' (Z_to_bv 64 0) (Z_to_bv 64 0x90c80) (Z_to_bv 64 0) -> getr regs' 21 = Z_to_bv 64 (calls_of cfgz c) ->
        getr regs' 19 = CP -> keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2aff0) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2af80) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem cfgz PL CP c K (R2 & R4 & R8 & R9 & R18 & R19 & R20) Hcfg Hc HCP Hstk Hro Hrel HK.
    pose proof (bv_unsigned_in_range 8 c) as Hc8. cbn in Hc8. pose proof (u64_range CP) as HCPr.
    set (v := TV CP (Z_to_bv 64 cfgz) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 0) PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT10 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    destruct (Z.eq_dec cfgz 0) as [C0|C0].
    - run_segT STOPST scrT1d 0x2af80%Z srT10 knT 46%nat rT1d cT1d (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open; sc_eqb. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT1d))) with 0x2aff0%Z. change (s_regs (fst (fst rT1d))) with srT1d in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply HK; [| | fin_reg HR' (19:reg) | fin_keep4 HR'].
      + unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_eq _ _) C0). fin_reg HR' (21:reg).
    - run_segT STOPST scrT1b 0x2af80%Z srT10 knT 46%nat rT1b cT1b (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
      { sc_open.
        - sc_eqb.
        - unfold adenot, v_addi. cbn [a_base a_off]. evs. exists [c]. split; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (Hc C0) | rewrite bytes_le_to_Z_1; reflexivity].
        - apply flat_intro; unfold elenZ; evs; unorm; rewrite ?u_small by lia; lia.
        - sc_eqb. }
      intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT1b))) with 0x2aff0%Z. change (s_regs (fst (fst rT1b))) with srT1b in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply HK; [| | fin_reg HR' (19:reg) | fin_keep4 HR'].
      + unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) C0). unset_v. regv HR' (21:reg). cbn [edenot]. evs.
        rewrite alu_add, alu_and, vand3, vadd_ZZ. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T2 : forall regs mem (N PL cfg CP r : word) K,
    regs118 regs N PL cfg CP -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        regs118 regs' N PL cfg CP -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 0x2af9c -> getr regs' 10 = N ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x68018) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2af94) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N PL cfg CP r K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 Hstk Hro Hrel HK.
    set (v := TV CP cfg N (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) r PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT20 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr 0x2af94%Z srT20 knT 46%nat rT2 cT2 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT2))) with 0x68018%Z. change (s_regs (fst (fst rT2))) with srT2 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_keep4 HR'].
    unfold regs118. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T3 : forall regs mem (N PL cfg CP r D : word) K,
    regs118 regs N PL cfg CP -> getr regs 21 = r -> getr regs 10 = D -> (bv_unsigned D <> 0)%Z ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        regs118 regs' N PL D CP -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 0x2afb0 ->
        getr regs' 10 = D -> getr regs' 11 = PL -> getr regs' 12 = N ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75224) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2af9c) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N PL cfg CP r D K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 R10 HD Hstk Hro Hrel HK.
    set (v := TV CP cfg N D (Z_to_bv 64 0) (Z_to_bv 64 0) r PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT30 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST scrT3 0x2af9c%Z srT30 knT 46%nat rT3 cT3 (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { sc_open. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact HD. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT3))) with 0x75224%Z. change (s_regs (fst (fst rT3))) with srT3 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg) | fin_keep4 HR'].
    unfold regs118. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T4 : forall regs mem (N PL CP r D : word) K,
    regs118 regs N PL D CP -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        loop_base regs' N D D -> getr regs' 21 = r -> getr regs' 19 = CP ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2aff0) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2afb0) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N PL CP r D K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 Hstk Hro Hrel HK.
    set (v := TV CP (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) r PL (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT40 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr 0x2afb0%Z srT40 knT 46%nat rT4 cT4 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT4))) with 0x2aff0%Z. change (s_regs (fst (fst rT4))) with srT4 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_reg HR' (21:reg) | fin_reg HR' (19:reg) | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T5 : forall regs mem (N D OW S3 r : word) K,
    loop_base regs N D OW -> getr regs 19 = S3 -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs' mem',
        loop_base regs' N D OW -> getr regs' 19 = S3 -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 0x2b004 ->
        getr regs' 10 = D -> getr regs' 11 = N ->
        keep4 regs regs' -> frame_mod mem mem' (regTc_w sp) -> stk_ok RSEGS mem' sp 80 ->
        rdn RSEGS mem' (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 1] ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b3e0) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2aff0) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D OW S3 r K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hstk Hro Hrel HK.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) r (Z_to_bv 64 0) OW S3).
    assert (HR : regs_ok (MENV v regs) srT50 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr 0x2aff0%Z srT50 knT 46%nat rT5 cT5 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT5))) with 0x2b3e0%Z. change (s_regs (fst (fst rT5))) with srT5 in HR'.
    mk_frameT v regs mem regTc covT5 regTc_denot regTc_flat EQM LF FR (@eq_refl word sp).
    apply HK; [| fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_keep4 HR'
              | exact FR | eapply stk_after; [exact FR | exact Hstk] | ].
    - unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
    - krd HK' 0x90c74%Z 1%nat Hrd. exact Hrd.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T6 : forall regs mem (N D OW r : word) K,
    loop_base regs N D OW -> getr regs 21 = r -> getr regs 10 = Z_to_bv 64 0 ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs' mem',
        loop_base regs' N D OW -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 0x2b014 ->
        getr regs' 11 = Z_to_bv 64 0 ->
        keep4 regs regs' -> frame_mod mem mem' (regTc_w sp) -> stk_ok RSEGS mem' sp 80 ->
        rdn RSEGS mem' (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b0c0) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b004) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D OW r K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R21 R10 Hstk Hro Hrel HK.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) r (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT60 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr 0x2b004%Z srT60 knT 46%nat rT6 cT6 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT6))) with 0x2b0c0%Z. change (s_regs (fst (fst rT6))) with srT6 in HR'.
    mk_frameT v regs mem regTc covT6 regTc_denot regTc_flat EQM LF FR (@eq_refl word sp).
    apply HK; [| fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (11:reg) | fin_keep4 HR'
              | exact FR | eapply stk_after; [exact FR | exact Hstk] | ].
    - unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
    - krd HK' 0x90c74%Z 1%nat Hrd. exact Hrd.
  Qed.

  (* [comment removed for export] *)
  Lemma decw_val : forall (E : env) (rz : Z), (1 <= rz <= 4)%Z -> ev E 7 = Z_to_bv 64 rz ->
    edenot E (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (rz - 1).
  Proof.
    intros E rz Hr H7. cbn [edenot]. rewrite H7.
    assert (C : (rz = 1 \/ rz = 2 \/ rz = 3 \/ rz = 4)%Z) by lia.
    destruct C as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_T7more : forall regs mem (N D OW : word) (rz : Z) K,
    loop_base regs N D OW -> getr regs 19 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 rz -> (2 <= rz <= 4)%Z ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        loop_base regs' N D OW -> getr regs' 19 = Z_to_bv 64 18446744073709551615 -> getr regs' 21 = Z_to_bv 64 (rz - 1) ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2aff0) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b014) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D OW rz K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hr Hstk Hro Hrel HK.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 rz) (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT70 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (DW : edenot (MENV v regs) (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (rz - 1)) by (apply decw_val; [lia | reflexivity]).
    run_segT STOPST scrT7a 0x2b014%Z srT70 knT 46%nat rT7a cT7a (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. cbn [sc_denot branch_taken]. rewrite DW, ed_lit. unfold bv_eqb.
      rewrite !u_small by lia. rewrite Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT7a))) with 0x2aff0%Z. change (s_regs (fst (fst rT7a))) with srT7a in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_reg HR' (19:reg) | regv HR' (21:reg); exact DW | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma seg_T7free : forall regs mem (N D OW : word) K,
    loop_base regs N D OW -> getr regs 19 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 1 ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        loop_base regs' N D OW -> getr regs' 1 = Z_to_bv 64 0x2b030 -> getr regs' 10 = OW ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x67ed8) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b014) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D OW K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hstk Hro Hrel HK.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT70 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (DW : edenot (MENV v regs) (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (1 - 1)) by (apply decw_val; [lia | reflexivity]).
    run_segT STOPST scrT7b 0x2b014%Z srT70 knT 46%nat rT7b cT7b (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. cbn [sc_denot branch_taken]. rewrite DW, ed_lit. reflexivity. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT7b))) with 0x67ed8%Z. change (s_regs (fst (fst rT7b))) with srT7b in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  (* [comment removed for export] *)
  Lemma seg_T7null : forall regs mem (N D : word) K,
    loop_base regs N D (Z_to_bv 64 0) -> getr regs 19 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 1 ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem ->
    (forall regs',
        loop_base regs' N D (Z_to_bv 64 0) ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b030) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b014) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hstk Hro Hrel HK.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT7z0 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (DW : edenot (MENV v regs) (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (1 - 1)) by (apply decw_val; [lia | reflexivity]).
    run_segT STOPSZ scrT7b 0x2b014%Z srT7z0 knT 46%nat rT7z cT7z (MENV v regs) mem regs; [exact HR | exact HKn | | exact Hh | exact Hlazy |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. cbn [sc_denot branch_taken]. rewrite DW, ed_lit. reflexivity. }
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT7z))) with 0x2b030%Z. change (s_regs (fst (fst rT7z))) with srT7z in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [| fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma knT8_ok : forall v regs mem (s0 s1 s2 s3 s4 s5 s6 s7 : word),
    v_sp0 v = sp -> v_tid v = s0 -> v_pp v = s1 -> v_A v = s2 -> v_cap v = s3 -> v_A2 v = s4 -> v_b8 v = s5 -> v_b10 v = s6 -> v_b11 v = s7 ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem -> tframe mem s0 s1 s2 s3 s4 s5 s6 s7 ->
    know_ok RSEGS (MENV v regs) mem knT8.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs mem s0 s1 s2 s3 s4 s5 s6 s7 E0 E1 E2 E3 E5 E6 E8 E10 E11 Hstk Hro Hrel (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    cbn in E0, E1, E2, E3, E5, E6, E8, E10, E11. subst.
    unfold knT8. unfold know_ok. apply Forall_app. split; [| apply (knT_ok (MV sp s0 s1 s2 v4 s3 s4 v7 s5 v9 s6 s7 v12 v13) regs mem eq_refl Hstk Hro Hrel)].
    repeat (apply Forall_cons); [ .. | apply Forall_nil].
    all: lazymatch goal with |- kentry_ok _ _ _ (KWord (SA (EVar 0) ?k) 8 ?e) =>
           eapply (kword_intro RSEGS _ mem (EVar 0) sp k 8 e); [reflexivity | evs; reflexivity | lia | lia | lia | lia |];
           replace (bv_unsigned sp + k)%Z with (bv_unsigned sp - (- k))%Z by lia; cbn [Z.opp Pos.succ]; assumption
         end.
  Qed.

  Lemma seg_T8 : forall regs mem (N D OW s0 s1 s2 s3 s4 s5 s6 s7 : word) K,
    loop_base regs N D OW ->
    stk_ok RSEGS mem sp 80 -> ro_none mem -> relro_none mem -> tframe mem s0 s1 s2 s3 s4 s5 s6 s7 ->
    (forall regs',
        getr regs' 2 = sp -> getr regs' 4 = Z_to_bv 64 0x92650 -> getr regs' 10 = Z_to_bv 64 0 ->
        getr regs' 8 = s0 -> getr regs' 9 = s1 -> getr regs' 18 = s2 -> getr regs' 19 = s3 -> getr regs' 20 = s4 -> getr regs' 21 = s5 ->
        getr regs' 22 = s6 -> getr regs' 23 = s7 -> getr regs' 3 = getr regs 3 ->
        keep4 regs regs' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2addc) mem (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b030) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem N D OW s0 s1 s2 s3 s4 s5 s6 s7 K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) Hstk Hro Hrel TF HK.
    set (v := MV sp s0 s1 s2 D s3 s4 (Z_to_bv 64 0) s5 (Z_to_bv 64 0) s6 s7 (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT80 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT8) by (eapply knT8_ok; subst v; try eassumption; reflexivity).
    run_segT STOPST noscr 0x2b030%Z srT80 knT8 46%nat rT8 cT8 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact Hh | exact Hlazy |].
    intros R' M' HR' HK' EQM LF. change (s_pc (fst (fst rT8))) with 0x2addc%Z. change (s_regs (fst (fst rT8))) with srT8 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply HK; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (10:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg)
              | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) | fin_reg HR' (21:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)
              | fin_reg HR' (3:reg) | fin_keep4 HR'].
  Qed.
End BlocksT.
