(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib MemSplit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StreamSim SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibKnowFrame LibKnowXfer RefReadLib RefReadBase RefReadStage RefReadChunkW RefReadChunk RefReadG0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet SymDriveLetRef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveX.run_block_with ::= run_block_with_let_img.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require RefReadF5_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_sr ::= constr:(RefReadF5_lits.LITS_SR).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_lg ::= constr:(RefReadF5_lits.LITS_LG).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_kn ::= constr:(RefReadF5_lits.LITS_KN).
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 40%nat -> map (vals_ev vals) (seq 0 40) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.

(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cn : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm sec cn B e content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13adc) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm sec cn B e content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13a74) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    norm_know_let HK.
  Ltac norm_regs HR :=
    norm_regs_let HR.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill5 : forall R M V B e M0 K,
    half 5 sp0 p1 mb gm sec cn B e content M0 R M V ->
    (2097152 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 5 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13aac) M (seg_rom RSEGS)) (modelG 1048576 V)) K.
  Proof using Hfile.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm sec cn B e extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = cn) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; cn; B; e; sec] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold HTOP in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBw.
    cbn [kentry_ok] in KBw. unfold estart, SWIN in KBw. cbn [a_base a_off BA LA MBA edenot ev] in KBw. cbn [ev] in KBw. rewrite P5, P0 in KBw.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & QK) Q23 PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((2097152 - 1048576)%Z) with (1048576%Z) in FR. change ((2097152 - 1048576)%Z) with (1048576%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (EVar 5) 1048688 1048576) (ELit 0) RSTAGE 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - apply flat_intro; cbn [edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; unfold RSTAGE; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 1048576 (dropz 1048576 content))) = 1048576%Z)
        by (pose proof (pref_length 1048576 (dropz 1048576 content) ltac:(lia)); pose proof (dropz_length 1048576 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 1048688) (ELit 1048576) 9%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 1048688 1048576 9%nat (pref 1048576 (dropz 1048576 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 9%nat) with (gblobs content 9%nat). rewrite (gblobs_cb 5) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 1048576 (dropz 1048576 content))) with (Z.to_nat 1048576) by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 72%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 112)) (ridx 23) (bx 112)) (ridx 19) (ELit 2097152)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm sec cn B e (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 5) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 5) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin5 : forall R M V B e M0 K,
    half 5 sp0 p1 mb gm sec cn B e content M0 R M V ->
    (1048576 <= L < 2097152)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 5 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13aac) M (seg_rom RSEGS)) (modelG 1048576 V)) K.
  Proof using Hfile.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm sec cn B e extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = cn) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; cn; B; e; sec] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold HTOP in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBw.
    cbn [kentry_ok] in KBw. unfold estart, SWIN in KBw. cbn [a_base a_off BA LA MBA edenot ev] in KBw. cbn [ev] in KBw. rewrite P5, P0 in KBw.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & QK) Q23 PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 (bv_unsigned B + 112 + 1048576), 1048576%Z); (Z_to_bv 64 RSTAGE, 65536%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside]. split; [exact O1|]. split; [|split; [exact O3 | exact I]].
        unfold in_rng in *. rewrite !u_small in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (EVar 5) 1048688 1048576) (ELit 0) RSTAGE 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - apply flat_intro; cbn [edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; unfold RSTAGE; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 5)%Z with (bv_unsigned B + 112)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 112) 1048576); try lia; [|exact PM].
        replace (Z.to_nat 1048576) with (length (pref 1048576 content)) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 40)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm sec cn B e extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 5) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
