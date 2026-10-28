From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymObj SymMaterialize.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue RingBuf Ring RingCfg ListCommit.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base r2_ex_vals r2_ex_defs r2_ex.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import R2C R2X R2E.

Definition s_xr : wsub :=
  Eval vm_compute in
    (123%positive, SAlu ALU_ADD (SVar 123) (SLit 1)) :: infer_sub NF (commit_at (commit_at X_r 3 LN) 4 LP) K_r.
Lemma ent_xr : entails (commit_at (commit_at X_r 3 LN) 4 LP) K_r s_xr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s_xr_id : wsub_id_below s_xr NF = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s_xr_123 : wsub_get s_xr 123 = SAlu ALU_ADD (SVar 123) (SLit 1).
Proof. vm_compute. reflexivity. Qed.

Lemma ex_Xr : forall cuts, In N_Kr cuts -> ex_ok cuts N_Xr.
Proof.
  intros cuts Hin K rho0 rho HG. change (rn_state N_Xr) with X_r.
  apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (ListCommit.smatch_facts segsU _ _ _ _ _ Hsm) as HF.
  pose proof (base_n rho (TEST_r :: inv_r) HF) as FN.
  assert (F123 : bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive))
    by exact (Forall_pick _ _ 1 (SPUlt (V 123) R2X.vN) HF eq_refl).
  assert (Fne : bv_unsigned (rw rho 123%positive) + 1 <> bv_unsigned (rw rho 13%positive)).
  { apply (proj1 (test_r rho F123 ltac:(lia))). exact (Forall_pick _ _ 0 TEST_r HF eq_refl). }
  assert (HVN : bv_unsigned (eval rho SEL) = bv_unsigned (rw rho 123%positive) + 1).
  { rewrite (sel_val rho F123 ltac:(lia)).
    destruct (Z.eqb_spec (bv_unsigned (rw rho 123%positive) + 1) (bv_unsigned (rw rho 13%positive))); lia. }
  pose proof (rem_prv_val rho FN F123) as HVP.
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123.

  destruct (smatch_nth_obj segsU rho X_r 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segsU rho X_r 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segsU rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.
  destruct (smatch_nth_obj segsU rho1 (commit_at X_r 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segsU rho1 (commit_at X_r 3 LN) 4 _ LP tr ms md eq_refl eq_refl
                ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segsU rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.

  unfold cellN, cellP in BN, BP, BN1, BN2, BP1, BP2. cbn [c_off c_val] in BN, BP, BN1, BN2, BP1, BP2.
  change I4 with (IX4 (SVar 123)) in BN, BP, BN1, BN2, BP1, BP2.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (subst rho1; cbn [eval rw rho_set_rl]; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REMP) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [eval] in BN, BP.
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl R2X.vN r2_N]; lia).
  cbn [eval rw rho_set_rl R2X.vN r2_N] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn).
  cbn [rn_init N_Xr] in Hinit. unfold initok, Uv, V in Hinit. cbn [eval] in Hinit.
  unfold nval, VN in Bn, Hinit. fold n I in Bn, Hinit.

  pose proof (SP_entails segsU K _ K_r s_xr rho2 (tr, mkCfg ms md) ent_xr (conj Hsm2 HK)) as HSP.
  set (rho3 := rho_sub rho2 s_xr) in *.
  assert (Erw : forall i, (i < NF)%positive -> rw rho3 i = rw rho i).
  { intros i Hi. subst rho3. cbn [rw rho_sub]. rewrite (wsub_get_id s_xr NF i s_xr_id Hi). reflexivity. }
  assert (E123 : bv_unsigned (rw rho3 123%positive) = I + 1).
  { subst rho3 rho2. cbn [rw rho_sub]. rewrite s_xr_123.
    rewrite U_add, U_lit. cbn [eval rw rho_set_rl]. fold I. unfold M64v.
    change (1 mod 18446744073709551616) with 1. apply Z.mod_small. lia. }
  eapply (reenter_cut segsU NF VN LN LP K rho0 cuts N_Kr rho3).
  - exact Hin.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw by exact Hi. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite (Erw VN) by reflexivity. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold initok, Uv, nval, V. cbn [eval]. rewrite E123. rewrite (Erw VN) by reflexivity.
      change (bv_unsigned (rw rho VN)) with n.
      subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl_at, rho_set_rl_other, rho_set_rl_at by (intros E; discriminate).
      intros j Hj. rewrite BN, BP. rewrite !lget_put4 by lia.
      destruct (Z.eqb_spec j I) as [->|Hne].
      * rewrite HVN, HVP. split.
        -- rewrite (Z.mod_small (I + 1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. reflexivity.
        -- pose proof (Z.mod_pos_bound (I + n - 1) n ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
      * apply Hinit. lia.
    + exact Logic.I.
  - exact HSP.
  - apply (rmeas_nonneg NF VN LN LP). vm_compute. reflexivity.
  - eapply (rmeas_lt_lex NF VN LN LP); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity |].
    cbn [rn_lex N_Kr N_Xr]. rewrite !lex3_val1. unfold comp_val, base_val. cbn [fst snd eval V].
    rewrite E123. fold I. rewrite !lit_unsigned. pose proof (B64_pos 2). pose proof (B64_pos 1). unfold B64 in *. nia.
Qed.

Lemma ex_Xrf : forall cuts, In N_Kf0 cuts -> ex_ok cuts N_Xrf.
Proof.
  intros cuts Hin K rho0 rho HG. change (rn_state N_Xrf) with X_rf.
  apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (ListCommit.smatch_facts segsU _ _ _ _ _ Hsm) as HF.
  pose proof (base_n rho (SPNot TEST_r :: inv_r) HF) as FN.
  assert (F123 : bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive))
    by exact (Forall_pick _ _ 1 (SPUlt (V 123) R2X.vN) HF eq_refl).
  assert (Feq : bv_unsigned (rw rho 123%positive) + 1 = bv_unsigned (rw rho 13%positive)).
  { pose proof (Forall_pick _ _ 0 (SPNot TEST_r) HF eq_refl) as X. cbn [holds] in X.
    destruct (Z.eq_dec (bv_unsigned (rw rho 123%positive) + 1) (bv_unsigned (rw rho 13%positive))) as [E|NE]; [exact E|].
    exfalso. apply X. apply (proj2 (test_r rho F123 ltac:(lia))). exact NE. }
  assert (HVN : bv_unsigned (eval rho SEL) = 0).
  { rewrite (sel_val rho F123 ltac:(lia)). rewrite Feq, Z.eqb_refl. reflexivity. }
  pose proof (rem_prv_val rho FN F123) as HVP.
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123.

  destruct (smatch_nth_obj segsU rho X_rf 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segsU rho X_rf 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segsU rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.
  destruct (smatch_nth_obj segsU rho1 (commit_at X_rf 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segsU rho1 (commit_at X_rf 3 LN) 4 _ LP tr ms md eq_refl eq_refl
                ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segsU rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segsU rho2 K_f0 (tr, mkCfg ms md)) in Hsm2.

  unfold cellN, cellP in BN, BP, BN1, BN2, BP1, BP2. cbn [c_off c_val] in BN, BP, BN1, BN2, BP1, BP2.
  change I4 with (IX4 (SVar 123)) in BN, BP, BN1, BN2, BP1, BP2.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (subst rho1; cbn [eval rw rho_set_rl]; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REMP) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [eval] in BN, BP.
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl R2X.vN r2_N]; lia).
  cbn [eval rw rho_set_rl R2X.vN r2_N] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  assert (EI : I = n - 1) by lia.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn).
  cbn [rn_init N_Xrf] in Hinit. unfold initok, Uv, V in Hinit. cbn [eval] in Hinit.
  unfold nval, VN in Bn, Hinit. fold n I in Bn, Hinit.

  assert (NXv : forall i, 0 <= i < n -> NXf LN rho2 i = (i + 1) mod n).
  { intros i Hi. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. rewrite lget_put4 by lia.
    destruct (Z.eqb_spec i I) as [->|Hne].
    - rewrite HVN. rewrite EI. replace (n - 1 + 1) with n by lia. rewrite Z.mod_same by lia. reflexivity.
    - apply (proj1 (Hinit i ltac:(lia))). }
  assert (PVv : forall i, 0 <= i < n -> PVf LP rho2 i = (i + n - 1) mod n).
  { intros i Hi. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. rewrite lget_put4 by lia.
    destruct (Z.eqb_spec i I) as [->|Hne].
    - rewrite HVP. pose proof (Z.mod_pos_bound (I + n - 1) n ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
    - apply (proj2 (Hinit i ltac:(lia))). }
  pose proof (ring_init n (NXf LN rho2) (PVf LP rho2) ltac:(lia) NXv PVv) as HR2.
  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  eapply (reenter_cut segsU NF VN LN LP K rho0 cuts N_Kf0 rho2).
  - exact Hin.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw. exact Bn.
    + intros _. unfold nval. rewrite Erw. change (bv_unsigned (rw rho VN)) with n. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXv by exact Hi.
        pose proof (Z.mod_pos_bound (i + 1) n ltac:(lia)). lia.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVv by exact Hi.
        pose proof (Z.mod_pos_bound (i + n - 1) n ltac:(lia)). lia.
    + exact Logic.I.
    + cbn [rn_ring N_Kf0 RGfull]. split; [|split; [constructor|constructor]].
      unfold nval, Rn, Uv. cbn [rg_R rg_cur eval R2X.vN r2_N]. rewrite !Erw. change (bv_unsigned (rw rho VN)) with n.
      change (bv_unsigned (rw rho 13%positive)) with n.
      rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0. exact HR2.
  - split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). vm_compute. reflexivity.
  - apply (rmeas_lt_ph NF VN LN LP); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

Definition Xr0a : sstate := Eval vm_compute in match materialize_at X_r0 3 LN with Some T => T | None => X_r0 end.
Lemma mat_r0_3 : materialize_at X_r0 3 LN = Some Xr0a.
Proof. vm_compute. reflexivity. Qed.
Definition Xr0b : sstate := Eval vm_compute in match materialize_at Xr0a 4 LP with Some T => T | None => Xr0a end.
Lemma mat_r0_4 : materialize_at Xr0a 4 LP = Some Xr0b.
Proof. vm_compute. reflexivity. Qed.
Lemma ent_r0 : entails Xr0b K_r [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ex_Xr0 : forall cuts, In N_Kr cuts -> ex_ok cuts N_Xr0.
Proof.
  intros cuts Hin K rho0 rho HG. change (rn_state N_Xr0) with X_r0.
  apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (ListCommit.smatch_facts segsU _ _ _ _ _ Hsm) as HF.
  assert (F0 : bv_unsigned (rw rho 123%positive) = 0).
  { pose proof (Forall_pick _ _ 0 (SPEq (V 123) (SLit 0)) HF eq_refl) as X. cbn [holds eval V] in X.
    rewrite X. rewrite lit_unsigned. reflexivity. }
  pose proof (smatch_materialize segsU rho X_r0 3 LN _ tr ms md _ _ _ _ mat_r0_3 eq_refl Hsm) as Hsm1.
  set (rho1 := rho_set_rl rho LN _) in Hsm1.
  pose proof (smatch_materialize segsU rho1 _ 4 LP _ tr ms md _ _ _ _ mat_r0_4 eq_refl Hsm1) as Hsm2.
  set (rho2 := rho_set_rl rho1 LP _) in Hsm2.
  pose proof (SP_entails segsU K _ K_r [] rho2 (tr, mkCfg ms md) ent_r0 (conj Hsm2 HK)) as HSP.
  set (rho3 := rho_sub rho2 []) in *.
  assert (Erw : forall i, rw rho3 i = rw rho i) by (intros i; reflexivity).
  destruct HG as (Hbase & _ & _ & _). destruct Hbase as (B1 & B2 & B3 & Bn).
  eapply (reenter_cut segsU NF VN LN LP K rho0 cuts N_Kr rho3).
  - exact Hin.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2 rho1. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption.
        apply B3; assumption.
      * unfold nval. rewrite Erw. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold initok, Uv, V. cbn [eval]. rewrite Erw, F0. intros j Hj. lia.
    + exact Logic.I.
  - exact HSP.
  - apply (rmeas_nonneg NF VN LN LP). vm_compute. reflexivity.
  - apply (rmeas_lt_ph NF VN LN LP); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
