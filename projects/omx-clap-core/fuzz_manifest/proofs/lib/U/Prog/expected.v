From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem LibcNeeds_c plain_c expected_c expected_m expected_s expected_ml.
Import ListNotations.
Open Scope Z_scope.

Theorem expected_holds : strlen_contract -> strchr_contract -> strncmp_contract -> bcmp_contract -> plain_contract ->
  expected_contract.
Proof.
  intros STRLEN_C STRCHR_C STRNCMP_C BCMP_C PLAIN_C. unfold expected_contract, EXPECTED, EXPECTED_K, PREFIX_LC_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    tb ts ub us CT CU T0 U0 TL UL PF MEM ST LO DT DU DP.
  change (240 + 32) with 272 in *.
  unfold off_stack in DT, DU, DP. unfold prefix_lc in PF. cbn [map app] in PF.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (RSP : bv_unsigned sp < 2^64) by lia.
  pose proof (proj1 ST) as LO0.
  destruct CT as [BT [NT LT]]. destruct CU as [BU [NU LU]].
  pose proof (bytes_at_bound _ _ _ _ BT) as TBd. pose proof (bytes_at_bound _ _ _ _ BU) as UBd.
  rewrite length_app in TBd, UBd. cbn [length] in TBd, UBd.
  assert (TB : bv_unsigned a0 + Z.of_nat (length tb + 1 + length ts) <= 2^64) by lia.
  assert (UB : bv_unsigned a1 + Z.of_nat (length ub + 1 + length us) <= 2^64) by lia.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -240)) = bv_unsigned sp + -240)
    by (apply unsigned_lit; lia).
  carve_frame 240%nat ST.
  do 18 zstep.
  eapply evt_cut; [eapply STRLEN_C|].
  { split; [exact BU|split; [exact NU|exact LU]]. }
  { exact MEM. }
  { rewrite SPU. exact ST. }
  lazymatch goal with |- forall _, kret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ _ -> _ =>
    intros ms' PO; unfold kret in PO; rewrite SPU in PO; revert ms' PO; post_call rsegs mm end.
  subst.
  zstep. if_cases HC; zify_cond HC; try rewrite !Z.mod_small in HC by lia.
  - eapply (epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a0 a1 tb ts ub us TB UB LO DT DU _
      [CB 136 _]); [unfold expected_s.MI; repeat match goal with |- _ /\ _ => split end; eassumption | exact FR | reflexivity|].
    unfold names. rewrite len_uu. replace (length ub =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    cbv beta iota. lia.
  - do 5 zstep.
    eapply evt_cut; [eapply STRCHR_C|].
    { split; [exact BT|split; [exact NT|exact LT]]. }
    { rewrite unsigned_lit by lia. lia. }
    { eassumption. }
    { rewrite SPU. eassumption. }
    { unfold STRCHR_K. rewrite SPU. lia. }
    { unfold off_stack, STRCHR_K. rewrite SPU. lia. }
    lazymatch goal with |- forall _, kret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ _ -> _ =>
      intros ms' PO; unfold kret in PO; rewrite SPU in PO; unfold STRCHR_K in PO; revert ms' PO;
      post_call rsegs mm end.
    change (bv_unsigned (Z_to_bv 64 60)) with 60 in POST.
    destruct (find_idx (fun x => x =? 60) (zbytes tb)) as [k|] eqn:Ef; subst.
    + pose proof (find_idx_some _ _ _ Ef) as (Hk & H60 & Hbef). rewrite len_tt in Hk. apply Z.eqb_eq in H60.
      zstep. if_cases HC2; zify_cond HC2; [lia|]. do 4 zstep.
      eapply (wl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a0 a1 tb ts ub us NT NU LT LU T0 U0 UL TB
        UB LO LO0 RSP DT DU DP STRCHR_C STRNCMP_C k);
        [unfold expected_s.MI; repeat match goal with |- _ /\ _ => split end; eassumption | exact FR | exact Hk | exact H60 | |
         lia | ].
      * intros j' Hj'. apply whole_at_not_lt. pose proof (Hbef j' Hj') as X. apply Z.eqb_neq in X. exact X.
      * intros Hw m' j' j'' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y23 y24 y25 y26 y27 y28 y29
          y30 y31 HM' FR'.
        eapply msetup; try (first [eassumption | lia]).
    + zstep. if_cases HC2; zify_cond HC2; [|lia].
      eapply msetup; try (first [eassumption | lia]).
      2: unfold expected_s.MI; repeat match goal with |- _ /\ _ => split end; eassumption.
      apply whole_false_of. intros k Hk. rewrite len_tt in Hk. apply whole_at_not_lt.
      destruct (Nat.lt_ge_cases k (length tb)) as [Hl|Hl].
      * pose proof (find_idx_none _ _ Ef k ltac:(rewrite len_tt; lia)) as X. apply Z.eqb_neq in X. exact X.
      * rewrite byte_at_ge by (rewrite len_tt; lia). lia.
Qed.
