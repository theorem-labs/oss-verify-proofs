(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymObj SymMaterialize.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue RingBuf Ring RingCfg ListCommit ECfgCuts.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base r2_ex_vals r2_ex_defs r2_ex_g r2_ex.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import R2C R2X R2E R2G.

Lemma lex_val_set_rl : forall rho l L comps,
  forallb (fun c : vdir * sv => negb (sv_has_rl l (snd c))) comps = true ->
  lex_val (rho_set_rl rho l L) comps = lex_val rho comps.
Proof.
  intros rho l L comps H. induction comps as [|[d e] t IH]; cbn [lex_val]; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite IH by exact H2.
  unfold comp_val, base_val. cbn [fst snd]. rewrite eval_set_rl by (destruct (sv_has_rl l e); [discriminate|reflexivity]). reflexivity.
Qed.

(* The ear clip: the ring cells NXT prev := next and PRV next := prev are committed into the ghost lists,
   the ring loses cur, and the run re-enters at K_c2 one step lower in the measure. *)
Lemma ex_Xc2 : forall cuts, In N_Kc2 cuts -> ex_ok cuts N_Xc2.
Proof.
  intros cuts Hin K rho0 rho HG. change (rn_state N_Xc2) with X_c2.
  apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segsU _ _ _ _ _ Hsm) as HF.
  assert (F192 : bv_unsigned (rw rho 192%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 192) vN) HF). vm_compute. tauto. }
  assert (F191 : bv_unsigned (rw rho 191%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 191) vN) HF). vm_compute. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 196%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 196)) HF ltac:(vm_compute; tauto)) as X.
    apply holds_bltu in X. rewrite U_lit in X. cbn [eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20) by (pose proof (base_n rho kc_facts HF); lia).

  destruct (smatch_nth_obj segsU rho X_c2 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segsU rho X_c2 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segsU rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segsU rho1 (commit_at X_c2 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segsU rho1 (commit_at X_c2 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segsU rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segsU rho2 K_c2 (tr, mkCfg ms md)) in Hsm2.

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval V]; lia). cbn [eval V] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval V rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval V rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN r2_N]; lia). cbn [eval rw rho_set_rl vN r2_N] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 192%positive)) as U192.
  pose proof (urange (rw rho 191%positive)) as U191. pose proof (urange (rw rho 188%positive)) as U188. pose proof (urange (rw rho 196%positive)) as U196.
  set (n := bv_unsigned (rw rho 13%positive)) in *.
  set (prev := bv_unsigned (rw rho 191%positive)) in *. set (next := bv_unsigned (rw rho 192%positive)) in *.

  destruct HG as (Hbase & Halln & _ & Hring). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn, AN, AP. fold n in Bn, AN, AP.
  destruct Hring as (HRok & Hroots & Heqs).
  unfold nval, Rn, Uv in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs eval V] in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs] in Heqs. fold n in HRok, Hroots.
  set (R := Z.to_nat (bv_unsigned (rw rho 196%positive))) in *.
  set (cur := bv_unsigned (rw rho 188%positive)) in *.
  apply Forall_cons_iff in Heqs as [E192 Heqs]. apply Forall_cons_iff in Heqs as [E191 _]. cbn [fst snd] in E192, E191. unfold V in E192, E191.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 192%positive) with (eval rho (SVar 192)). rewrite E192. unfold NXT. rewrite U_LD4 by (cbn [eval V]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 191%positive) with (eval rho (SVar 191)). rewrite E191. unfold PRV. rewrite U_LD4 by (cbn [eval V]; lia). reflexivity. }
  destruct (ring_clip n R cur (NXf LN rho) (PVf LP rho) HRok ltac:(subst R; lia)) as (HR' & LIVE' & NEpc & NEnc & NEpn & Lprev & Lnext).
  rewrite <- Enext, <- Eprev in *.

  assert (NXE : forall x, 0 <= x < n -> NXf LN rho2 x = fupd (NXf LN rho) prev next x).
  { intros x Hx. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. unfold fupd. replace (Z.to_nat (4 * prev)) with (4 * Z.to_nat prev)%nat by lia.
    destruct (Z.eqb_spec x prev) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold next. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  assert (PVE : forall x, 0 <= x < n -> PVf LP rho2 x = fupd (PVf LP rho) next prev x).
  { intros x Hx. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. unfold fupd. replace (Z.to_nat (4 * next)) with (4 * Z.to_nat next)%nat by lia.
    destruct (Z.eqb_spec x next) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold prev. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  pose proof (ring_ok_ext n (R - 1) next _ _ (NXf LN rho2) (PVf LP rho2) NXE PVE HR') as HR2.

  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  assert (En2 : nval VN rho2 = n) by reflexivity.
  assert (ER2 : Rn rho2 (mkRG R196m1 (V 192) [V 192; V 191] []) = (R - 1)%nat).
  { unfold Rn, Uv, R196m1. cbn [rg_R]. rewrite U_add, U_lit. cbn [eval V]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace ((bv_unsigned (rw rho 196%positive) + (2 ^ 64 - 1)) mod 2 ^ 64) with (bv_unsigned (rw rho 196%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 196%positive) + (2 ^ 64 - 1)) with ((bv_unsigned (rw rho 196%positive) - 1) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cut segsU NF VN LN LP K rho0 cuts N_Kc2 rho2).
  - exact Hin.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * rewrite En2. exact Bn.
    + intros _. rewrite En2. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXE by exact Hi. unfold fupd.
        destruct (i =? prev); [lia|]. apply AN. exact Hi.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVE by exact Hi. unfold fupd.
        destruct (i =? next); [lia|]. apply AP. exact Hi.
    + exact I.
    + split; [|split].
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval V]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [eval V]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  - split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). vm_compute. reflexivity.
  - eapply (rmeas_lt_sub NF VN LN LP); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | | reflexivity].
    cbn [rn_lex N_Kc2 N_Xc2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.

(* The forced clip: the same commit of the two ring cells, for the clipped vertex v192 = NXT cur; the run
   re-enters at K_g2. *)
Lemma ex_Xg2 : forall cuts, In N_Kg2 cuts -> ex_ok cuts N_Xg2.
Proof.
  intros cuts Hin K rho0 rho HG. change (rn_state N_Xg2) with X_g2.
  apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segsU _ _ _ _ _ Hsm) as HF.
  assert (F198 : bv_unsigned (rw rho 198%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 198) vN) HF). vm_compute. tauto. }
  assert (F194 : bv_unsigned (rw rho 194%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 194) vN) HF). vm_compute. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 196%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 196)) HF ltac:(vm_compute; tauto)) as X.
    apply holds_bltu in X. rewrite U_lit in X. cbn [eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20) by (pose proof (base_n rho kgb_facts HF); lia).

  destruct (smatch_nth_obj segsU rho X_g2 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segsU rho X_g2 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segsU rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segsU rho1 (commit_at X_g2 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segsU rho1 (commit_at X_g2 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segsU rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segsU rho2 K_g2 (tr, mkCfg ms md)) in Hsm2.

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval V]; lia). cbn [eval V] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval V rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval V rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN r2_N]; lia). cbn [eval rw rho_set_rl vN r2_N] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 198%positive)) as U198.
  pose proof (urange (rw rho 194%positive)) as U194. pose proof (urange (rw rho 192%positive)) as U192. pose proof (urange (rw rho 196%positive)) as U196.
  set (n := bv_unsigned (rw rho 13%positive)) in *.
  set (prev := bv_unsigned (rw rho 194%positive)) in *. set (next := bv_unsigned (rw rho 198%positive)) in *.

  destruct HG as (Hbase & Halln & _ & Hring). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn, AN, AP. fold n in Bn, AN, AP.
  destruct Hring as (HRok & Hroots & Heqs).
  unfold nval, Rn, Uv in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs eval V] in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs] in Heqs. fold n in HRok, Hroots.
  set (R := Z.to_nat (bv_unsigned (rw rho 196%positive))) in *.
  set (cur := bv_unsigned (rw rho 192%positive)) in *.
  apply Forall_cons_iff in Heqs as [E194 Heqs]. apply Forall_cons_iff in Heqs as [E198 _]. cbn [fst snd] in E198, E194. unfold V in E198, E194.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 198%positive) with (eval rho (SVar 198)). rewrite E198. unfold NXT. rewrite U_LD4 by (cbn [eval V]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 194%positive) with (eval rho (SVar 194)). rewrite E194. unfold PRV. rewrite U_LD4 by (cbn [eval V]; lia). reflexivity. }
  destruct (ring_clip n R cur (NXf LN rho) (PVf LP rho) HRok ltac:(subst R; lia)) as (HR' & LIVE' & NEpc & NEnc & NEpn & Lprev & Lnext).
  rewrite <- Enext, <- Eprev in *.

  assert (NXE : forall x, 0 <= x < n -> NXf LN rho2 x = fupd (NXf LN rho) prev next x).
  { intros x Hx. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. unfold fupd. replace (Z.to_nat (4 * prev)) with (4 * Z.to_nat prev)%nat by lia.
    destruct (Z.eqb_spec x prev) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold next. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  assert (PVE : forall x, 0 <= x < n -> PVf LP rho2 x = fupd (PVf LP rho) next prev x).
  { intros x Hx. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. unfold fupd. replace (Z.to_nat (4 * next)) with (4 * Z.to_nat next)%nat by lia.
    destruct (Z.eqb_spec x next) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold prev. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  pose proof (ring_ok_ext n (R - 1) next _ _ (NXf LN rho2) (PVf LP rho2) NXE PVE HR') as HR2.

  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  assert (En2 : nval VN rho2 = n) by reflexivity.
  assert (ER2 : Rn rho2 (mkRG R196m1 (V 198) [V 198; V 194] []) = (R - 1)%nat).
  { unfold Rn, Uv, R196m1. cbn [rg_R]. rewrite U_add, U_lit. cbn [eval V]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace ((bv_unsigned (rw rho 196%positive) + (2 ^ 64 - 1)) mod 2 ^ 64) with (bv_unsigned (rw rho 196%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 196%positive) + (2 ^ 64 - 1)) with ((bv_unsigned (rw rho 196%positive) - 1) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cut segsU NF VN LN LP K rho0 cuts N_Kg2 rho2).
  - exact Hin.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * rewrite En2. exact Bn.
    + intros _. rewrite En2. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXE by exact Hi. unfold fupd.
        destruct (i =? prev); [lia|]. apply AN. exact Hi.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVE by exact Hi. unfold fupd.
        destruct (i =? next); [lia|]. apply AP. exact Hi.
    + exact I.
    + split; [|split].
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval V]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [eval V]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  - split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). vm_compute. reflexivity.
  - eapply (rmeas_lt_sub NF VN LN LP); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | | reflexivity].
    cbn [rn_lex N_Kg2 N_Xg2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.
