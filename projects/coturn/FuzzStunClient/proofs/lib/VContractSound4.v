(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Notation B0 := (Z_to_bv 8 0).

(* [comment removed for export] *)
Lemma not_outside_2 x r1 r2 :
  ~ outside x [r1; r2] -> ~ outside x [r1] \/ ~ outside x [r2].
Proof.
  destruct r1 as [b1 n1], r2 as [b2 n2]. cbn [outside]. unfold in_rng. intros NO.
  destruct (Z_le_gt_dec (bv_unsigned b1) (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned b1 + n1));
    try (left; intros [X _]; apply X; lia);
    (destruct (Z_le_gt_dec (bv_unsigned b2) (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned b2 + n2));
       [right; intros [X _]; apply X; lia| | |]; exfalso; apply NO; repeat split; lia).
Qed.

Section CS4.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  Lemma disjoint_ranges_sound A nu a b n :
    lgamma A nu -> disjoint_ranges A a b n = true ->
    eval nu a + eval nu n <= eval nu b \/ eval nu b + eval nu n <= eval nu a.
  Proof.
    intros HL Hd. unfold disjoint_ranges in Hd. apply Bool.orb_prop in Hd as [Hd|Hd]; apply (qle_sound A nu) in Hd; auto;
      rewrite eval_lsub, eval_ladd in Hd; lia.
  Qed.

  Lemma readable_range_stack A base n so slo shi :
    readable_range P A base n = RR_stack so slo shi -> stack_range P A base n false = RR_stack so slo shi.
  Proof.
    unfold readable_range. destruct (is_sp_rel base); [auto|].
    destruct (is_data_rel base).
    - destruct (dead_lin _ _); [discriminate|]. destruct (lo_of _ _); [|discriminate].
      destruct (Z.ltb _ _); [discriminate|]. destruct (hi_of _ _); [|discriminate]. destruct (Z.ltb _ _); discriminate.
    - destruct (negb _); [discriminate|]. destruct (lo_of _ _); [|discriminate]. destruct (hi_of _ _); [|discriminate].
      destruct (in_ranges _ _ _); discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma sp_word A nu regs mem spoff :
    gammaP A nu regs mem -> get_reg A 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P <= spoff <= 0 ->
    getr regs 2%bv = wordZ (e_sp0 E + spoff) /\ 0 <= e_sp0 E + spoff /\ e_sp0 E < 2 ^ 64.
  Proof.
    intros HGm Hsp Hoff. pose proof HGm as (HE&HM&HF&_). pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    split; [|lia].
    apply (reg_word SEGS P E mem0 A nu regs mem 2%bv (lsymc SP0 spoff) _ HGm); [vm_compute; lia|exact Hsp|rewrite eval_lsymc, (nu_SP0 E nu HF); reflexivity|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_strncpy rc_lo rc_hi : Z.
  (* [comment removed for export] *)
  Hypothesis RC_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= rc_lo /\ rc_hi <= phi.
  Hypothesis STRNCPY : forall mem (d s sp : word) (n : Z) (src : list byte) regs (ret : word),
    rdn SEGS mem s (length src) = Some src ->
    (n <= Z.of_nat (length src) \/
     exists K, 0 <= K < Z.of_nat (length src) /\ bv_unsigned (nth (Z.to_nat K) src B0) = 0 /\ K + 8 <= Z.of_nat (length src)) ->
    store_ok SEGS mem d (Z.to_nat n) = true -> 0 <= n ->
    bv_unsigned s + Z.of_nat (length src) < 2 ^ 64 -> bv_unsigned d + n < 2 ^ 64 ->
    (bv_unsigned d + n <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned d) ->
    (forall i, rc_lo <= i < rc_hi -> mem (Z_to_bv 64 i) = None) ->
    (rc_hi <= bv_unsigned d \/ bv_unsigned d + n <= rc_lo) ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
    rc_hi <= bv_unsigned sp - 32 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned sp - 32) ->
    (bv_unsigned sp <= bv_unsigned d \/ bv_unsigned d + n <= bv_unsigned sp - 32) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = d -> getr regs 11%bv = s -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (wordZ a_strncpy) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv /\ getr regs' 10%bv = getr regs 10%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32); (d, n)].

  Lemma rc_clear4 mem : MCP mem -> forall i, rc_lo <= i < rc_hi -> mem (Z_to_bv 64 i) = None.
  Proof.
    intros (MF&MD&MP&MFM) i Hi. destruct RC_PRISTINE as [plo [phi (Hin&Q1&Q2)]].
    exact (MP plo phi i Hin ltac:(lia)).
  Qed.

  Lemma rc_below : rc_lo <= rc_hi -> rc_hi <= vp_splo P - vp_frame P.
  Proof.
    intros H. pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB). destruct RC_PRISTINE as [plo [phi (Hin&Q1&Q2)]].
    destruct (PP _ _ Hin). lia.
  Qed.

  #[using="PO RC_PRISTINE STRNCPY"] Theorem strncpy_post : rc_lo <= rc_hi -> contract_post SEGS P E mem0 rom CI C_strncpy a_strncpy.
  Proof.
    intros Hrc A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    pose proof (rc_below Hrc) as RCB.
    (* [comment removed for export] *)
    destruct HKw as [HKw|HKw]; [cbn in HKw; lia|]. cbn [contract_K] in HKw.
    destruct (in_ranges_sound _ _ _ HKw) as [klo [khi (HKin&HK1&HK2)]]. destruct (PR _ HKin) as [HK3 HK4]. cbn [fst snd] in HK3, HK4.
    destruct (sp_word A nu regs mem spoff HGm Hsp ltac:(lia)) as (R2&U1&U2).
    set (usp := e_sp0 E + spoff) in *.
    cbn [contract_apply] in Happ. unfold c_strncpy, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (get_reg A A1r) as [se|] eqn:Ese; [|discriminate].
    destruct (stack_range P A de ne true) as [off dlo dhi| | | |msg] eqn:Esr; try discriminate.
    destruct (Z.ltb_spec dlo spoff); [discriminate|].
    destruct (stack_dst SEGS P E mem0 PO A nu regs mem de ne off dlo dhi HGm ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1]); lia)) Esr) as (Ed&H1&H2&H3&H4&Hd0&Hdn&Hok&Hws).
    set (n := eval nu ne) in *. set (ov := eval nu off) in *. set (d := e_sp0 E + ov) in *.
    assert (R10 : getr regs 10%bv = wordZ d) by (apply (reg_word SEGS P E mem0 A nu regs mem 10%bv de d HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E1; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0]); lia)|exact Ede|exact Ed|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E1; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0]); lia)]).
    assert (R12 : getr regs 12%bv = Z_to_bv 64 n) by (apply (reg_word SEGS P E mem0 A nu regs mem 12%bv ne n HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E1; @E4; @E5; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @H2; @H4; @Hd0; @Hdn]); lia)|exact Ene|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E1; @E4; @E5; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @H2; @H4; @Hd0; @Hdn]); lia)]).
    assert (STK : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (wordZ usp) - 32)) 32 = true).
    { rewrite u_wordZ by lia. change (Z_to_bv 64 (usp - 32)) with (wordZ (usp - 32)). change 32%nat with (Z.to_nat 32).
      apply store_ok_bytes; [(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @E2; @P1]); lia)|(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @E2; @P1]); lia)|]. intros j Hj. apply (MC_frame_ok SEGS P E mem0 mem _ HM). unfold usp. lia. }
    (* [comment removed for export] *)
    assert (SRC : exists sa src,
              getr regs 11%bv = wordZ sa /\ 0 <= sa /\ sa + Z.of_nat (length src) < 2 ^ 64 /\
              rdn SEGS mem (wordZ sa) (length src) = Some src /\
              (n <= Z.of_nat (length src) \/
               exists K, 0 <= K < Z.of_nat (length src) /\ bv_unsigned (nth (Z.to_nat K) src B0) = 0 /\ K + 8 <= Z.of_nat (length src)) /\
              (d + n <= sa \/ sa + Z.of_nat (length src) <= d) /\
              (usp <= sa \/ sa + Z.of_nat (length src) <= usp - 32) /\
              let A1' := set_slots A (cm_kill (vs_slots A) dlo dhi) in
              CROk (kill_nul A1' dlo (dhi - 1) None) (Some de) = CROk A1 v).
    { destruct (rodata_cstr_len P (Some se)) as [k|] eqn:Ecs.
      - (* [comment removed for export] *)
        destruct (rodata_cstr_sound SEGS P E mem0 PO mem _ _ HE HM Ecs) as [se' (Ese'&Cse&Hk&Hs0&Hsk&NZ&ZK)]. injection Ese' as <-.
        set (ln := Z.min (k + 8) nhi) in Happ.
        destruct (in_ranges (vp_segs P) (lc se) ln) eqn:Esg; [|discriminate].
        destruct (in_ranges_sound _ _ _ Esg) as [slo [shi (Hsin&Q1&Q2)]]. destruct (PS _ _ Hsin) as (S0&S1&SB).
        destruct (rdn_bytes_vals SEGS mem (lc se) (Z.to_nat ln) (fun j b => j = k -> bv_unsigned b = 0) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hs0; @E1; @E2; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Hk; @Hsk; @Q2; @S1]); lia)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hs0; @E1; @E2; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Hk; @Hsk; @Q2; @S1]); lia))) as [src (Hsrc&Lsrc&Qsrc)].
        { intros j Hj. destruct (Z.eq_dec j k) as [->|Hne].
          - destruct ZK as [bb [Rb Ub]]. exists bb. auto.
          - destruct (rdn1_any SEGS mem (wordZ (lc se + j)) (SB (lc se + j) ltac:((ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK2; @HK3; @HK4; @Hk; @Hsk; @Hs0; @Q1; @Q2; @S1; @Hj; @Hne]); lia)))) as [bb Rb]. exists bb. split; [exact Rb|intros; (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK2; @HK3; @HK4; @Hsk; @Hs0; @Q2; @S1; @Hj; @Hne; @H0]); lia)]. }
        exists (lc se), src. rewrite Lsrc.
        split; [apply (reg_word SEGS P E mem0 A nu regs mem 11%bv se _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Hk; @Hsk; @Hs0; @Q2; @S1]); lia)|exact Ese|apply eval_is_const; exact Cse|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Hk; @Hsk; @Hs0; @Q2; @S1]); lia)]|].
        split; [(ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hs0; @Lsrc]); lia)|]. split; [(ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Hk; @Hsk; @Q2; @S1; @Lsrc]); lia)|]. split; [exact Hsrc|]. split.
        { destruct (Z_le_gt_dec nhi (k + 8)) as [Hc|Hc]; [left; (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK2; @HK3; @HK4; @Hn1; @Hk; @Hsk; @Hs0; @Lsrc; @Hc]); lia)|]. right. exists k.
          split; [(ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lsrc; @Hc]); lia)|]. split; [exact (Qsrc (Z.to_nat k) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lsrc; @Hc; @E1; @E2; @HK1; @HK2; @HK3; @HK4; @Hs0; @Q2; @S1]); lia)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lsrc; @Hc; @E1; @E2; @HK1; @HK2; @HK3; @HK4; @Hs0; @Q2; @S1]); lia)))|(ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lsrc; @Hc; @E1; @E2; @HK1; @HK2; @HK3; @HK4; @Hs0; @Q2; @S1]); lia)]. }
        split; [right; unfold d; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK3; @H; @H1; @Hk; @Hsk; @Q2; @S1; @Lsrc]); lia)|]. split; [right; unfold usp; (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK2; @HK3; @HK4; @Hk; @Hsk; @Hs0; @Q2; @S1; @Lsrc]); lia)|]. exact Happ.
      - (* [comment removed for export] *)
        pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem se ne _ HGm ltac:(lia) eq_refl) as RS.
        destruct (readable_range P A se ne) as [so slo shi|soff|ilo ihi| |msg] eqn:Err; try discriminate; try (destruct RS; fail).
        + destruct (disjoint_ranges A de se ne) eqn:Edj; [|discriminate]. cbn [negb] in Happ.
          destruct (Z.ltb_spec slo spoff); [discriminate|].
          apply readable_range_stack in Err.
          destruct (stack_range_sound P E A nu se ne false so slo shi HL HF Err) as (_&Es&T1&T2&T3&T4&_).
          destruct RS as (Sa0&Sa1&SaB).
          destruct (rdn_bytes_vals SEGS mem (eval nu se) (Z.to_nat n) (fun _ _ => True) Sa0 ltac:(lia)) as [src (Hsrc&Lsrc&_)].
          { intros j Hj. destruct (SaB j ltac:(lia)) as [b Hb]. eauto. }
          exists (eval nu se), src. rewrite Lsrc.
          split; [apply (reg_word SEGS P E mem0 A nu regs mem 11%bv se _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @Sa0; @Sa1; @Es; @T2; @T4]); lia)|exact Ese|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @Sa0; @Sa1; @Es; @T2; @T4]); lia)]|].
          split; [lia|]. split; [(ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @Hn0; @Hn1; @Es; @T2; @T4; @Lsrc]); lia)|]. split; [exact Hsrc|]. split; [left; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Lsrc]); lia)|].
          split; [pose proof (disjoint_ranges_sound A nu de se ne HL Edj) as DJ; unfold d, ov, n in *; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Ed; @Lsrc; @DJ]); lia)|].
          split; [left; unfold usp; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @H0; @Es; @T1; @Lsrc]); lia)|]. exact Happ.
        (* [comment removed for export] *)
        + (* [comment removed for export] *)
          destruct RS as (Sa0&Sa1&SaB).
          unfold readable_range in Err. destruct (is_sp_rel se); [pose proof (stack_range_shape P A se ne false) as SH; rewrite Err in SH; destruct SH|].
          destruct (is_data_rel se).
          { exfalso. destruct (dead_lin _ _); [discriminate|]. destruct (lo_of _ _); [|discriminate].
            destruct (Z.ltb _ _); [discriminate|]. destruct (hi_of _ _); [|discriminate]. destruct (Z.ltb _ _); discriminate. }
          destruct (negb _); [discriminate|].
          pose proof (bnd_sound A nu se HL) as B1. pose proof (bnd_sound A nu (ladd se ne) HL) as B2. unfold lo_of, hi_of in Err.
          destruct (bnd A se) as [[l1|] h1]; [|discriminate]. destruct (bnd A (ladd se ne)) as [l2 [h2|]]; [|discriminate]. cbn [fst snd] in Err.
          destruct (in_ranges (vp_segs P) l1 (h2 - l1)) eqn:Er; [|discriminate]. injection Err as <- <-.
          destruct B1 as [B1 _]. destruct B2 as [_ B2]. cbn [fst snd lo_le hi_ge] in B1, B2. rewrite eval_ladd in B2.
          destruct (in_ranges_sound _ _ _ Er) as [sglo [sghi (Hin&G1&G2)]]. destruct (PS _ _ Hin) as (S0&S1&SB).
          destruct (rdn_bytes_vals SEGS mem (eval nu se) (Z.to_nat n) (fun _ _ => True) Sa0 ltac:((ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @B2; @G2; @S1]); lia))) as [src (Hsrc&Lsrc&_)].
          { intros j Hj. destruct (SaB j ltac:(lia)) as [b Hb]. eauto. }
          exists (eval nu se), src. rewrite Lsrc.
          split; [apply (reg_word SEGS P E mem0 A nu regs mem 11%bv se _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Sa0; @B2; @G2; @S1]); lia)|exact Ese|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lsrc; @E1; @E2; @E4; @E5; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @Sa0; @B2; @G2; @S1]); lia)]|].
          split; [(ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Sa0; @Lsrc]); lia)|]. split; [(ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P0; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Hdn; @B2; @G2; @S1; @Lsrc]); lia)|]. split; [exact Hsrc|]. split; [left; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Lsrc]); lia)|].
          split; [right; unfold d, n in *; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK3; @Hn0; @Hn1; @H; @H1; @B2; @G2; @S1; @Lsrc]); lia)|].
          split; [right; unfold usp, n in *; (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @B2; @G2; @S1; @Lsrc]); lia)|]. exact Happ. }
    clear Happ. destruct SRC as [sa [src (R11&Sa0&Sa1&Hsrc&Hroom&Hdisj&Hsps&Happ)]]. cbn zeta in Happ.
    destruct (kill_nul_eq (set_slots A (cm_kill (vs_slots A) dlo dhi)) dlo (dhi - 1) None) as [nl [EK Hnl]]. rewrite EK in Happ.
    injection Happ as <- <-.
    set (A1 := set_nul (set_slots A (cm_kill (vs_slots A) dlo dhi)) nl).
    (* [comment removed for export] *)
    destruct (STRNCPY mem (wordZ d) (wordZ sa) (wordZ usp) n src regs ra Hsrc Hroom Hok ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia))
                ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia)) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia)) ltac:(rewrite !u_wordZ; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia)) (rc_clear4 mem HM)
                ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia); left; unfold d; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia)) STK ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia); unfold usp; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia))
                ltac:(rewrite !u_wordZ by (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia); exact Hsps) ltac:(rewrite !u_wordZ by (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia); left; unfold usp, d; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Sa1; @E2; @P1; @H2; @H4; @Hdn; @U2; @Hd0; @Hdisj; @RCB; @U1; @Hsps]); lia))
                Hret Hra R2 R10 R11 R12)
      as [regs' [mem' (RUN&HKr&Hra'&Ha0'&FM)]].
    rewrite u_wordZ in FM by (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @HK2; @HK4; @U1; @U2; @Hn0; @Hn1; @H; @H1]); lia). change (Z_to_bv 64 (usp - 32)) with (wordZ (usp - 32)) in FM.
    set (R := [(wordZ (usp - 32), 32); (wordZ d, n)]) in FM.
    assert (ROUT : forall a w, (a + w <= usp - 32 \/ usp <= a) -> (a + w <= d \/ d + n <= a) -> 0 <= a -> a + w <= 2 ^ 64 -> range_outside R a w).
    { intros a w X Y Z0 Z1 x Hx. subst R. cbn [outside]. unfold in_rng. rewrite !u_wordZ by (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @P1; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Hdisj; @Hsps; @Z0; @Hx; @H2; @H4; @Hdn; @X; @Y; @Z1; @Hd0]); lia). repeat split; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Hdisj; @Hsps; @X; @Z0; @Hx; @H2; @H4; @Y]); lia). }
    assert (L1 : lgamma A1 nu).
    { destruct HL as (LS&LC&LM&LV&(Q0&Q1&Q2&Q3&Q4&Q5)). split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
      split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (Q3 _ _ _ Hin)|]. split; [exact Q4|exact Q5]. }
    exists regs', mem', nu.
    destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_strncpy A1 spoff (Some de)) nu nu regs regs' mem mem' R
                HGm (ext_refl _ _) ltac:(destruct (contract_frame_shape C_strncpy A1 spoff (Some de)) as (_&_&_&_&F5&_); rewrite F5; cbn; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @F5]); lia))
                ltac:(apply lgamma_contract_frame; [exact L1|cbn; exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv de HGm ltac:(vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @F5]); lia)) Ede))]))
      as [HG' FM'].
    - eapply (gamma_regs_contract_frame SEGS P E mem0 C_strncpy A A1 spoff (Some de) nu nu regs regs'); try eassumption.
      + right. split; [exact HR|destruct HB as (_&_&RB&_); exact RB].
      + apply ext_refl.
      + reflexivity.
      + rewrite Ha0', R10, u_wordZ, Ed by (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @HK2; @HK4; @U2; @Hn0; @Hn1; @H2; @H4; @Hd0; @Hdn]); lia). symmetry. apply zwrap_id. (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @HK2; @HK4; @U2; @Hn0; @Hn1; @H2; @H4; @Hd0; @Hdn]); lia).
    - intros off' w' v' Hin. destruct (contract_frame_shape C_strncpy A1 spoff (Some de)) as (F1&_). rewrite F1 in Hin. cbn -[Z.sub] in Hin.
      pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D1. apply cm_kill_sub in Hin.
      pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D2. apply cm_kill_sub in Hin.
      left. split; [exact Hin|]. destruct (HSl _ _ _ Hin) as [(Ra&Rb&Rc) _].
      apply ROUT; unfold usp, d; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @D1; @E1; @E12; @HK1; @HK3; @H; @H1; @H2; @H4; @Sa0; @D2; @HK2; @HK4; @Hn0; @Hn1; @Hdisj; @Hsps; @Ra; @Rb; @E2; @P1; @Rc]); lia).
    - intros ga gw gv Hin. destruct (contract_frame_shape C_strncpy A1 spoff (Some de)) as (_&F2&_). rewrite F2 in Hin. cbn in Hin.
      split; [exact Hin|]. destruct (HG _ _ _ Hin) as [(Ra&Rb&Rc) _]. apply ROUT; unfold usp, d; (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @Sa0; @Rc; @Ra; @P0; @P1; @Hdn; @Sa1]); lia).
    - intros mlo mhi Hin. destruct (contract_frame_shape C_strncpy A1 spoff (Some de)) as (_&_&F3&_). apply F3 in Hin as [Hin W1]. cbn -[Z.sub] in Hin, W1.
      destruct (Hnl _ Hin) as [Hold [X|W2]]; [cbn in X; discriminate|]. cbn in Hold, W2.
      destruct (HN _ _ Hold) as [z [b (Q1&Q2&Q3&Q4)]]. right. exists z, b.
      split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
      rewrite <- Q3. apply (rdn_unchanged SEGS mem0 rom mem mem' R (e_sp0 E + z) 1 (proj1 FM)); [(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @H2; @Sa0; @Hdisj; @Hsps; @W1; @Q1; @Q2; @E2; @P1; @Hdn; @Sa1]); lia)|(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @H2; @Sa0; @Hdisj; @Hsps; @W1; @Q1; @Q2; @E2; @P1; @Hdn; @Sa1]); lia)|].
      apply ROUT; unfold usp, d; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Hn0; @Hn1; @H; @H1; @H2; @Sa0; @Hdisj; @Hsps; @W1; @W2; @Q1; @Q2; @E2; @P1; @Hdn; @Sa1]); lia).
    - exact FM.
    - intros x Hx. destruct (not_outside_2 x _ _ Hx) as [Hx1|Hx2].
      + apply (stack_R_ok SEGS P E mem0 PO (spoff - 32) klo khi 32); auto; try (ltac2:(LK.k []); lia).
        * exists (klo, khi). cbn [fst snd]. auto with zarith.
        * replace (e_sp0 E + (spoff - 32)) with (usp - 32) by (unfold usp; lia). exact Hx1.
      + apply (stack_R_ok SEGS P E mem0 PO ov dlo dhi n); auto; lia.
    - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite Hra'; exact Hra|].
      split; [apply ext_refl|]. split; [|exact FM'].
      destruct (contract_frame_shape C_strncpy A1 spoff (Some de)) as (_&_&_&_&F5&_); rewrite F5; cbn; lia.
  Qed.

  Theorem strncpy_dead : contract_dead SEGS P E mem0 CI C_strncpy.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&_).
    cbn [contract_apply] in Happ. unfold c_strncpy, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    { destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
      destruct (get_reg A A0r) as [de|] eqn:Ede; [|discriminate].
      destruct (get_reg A A1r) as [se|] eqn:Ese; [|discriminate].
      destruct (stack_range P A de ne true) as [off dlo dhi| | | |msg] eqn:Esr; try discriminate.
      2:{ exact (stack_range_dead P A nu de ne true HL Esr). }
      destruct (Z.ltb dlo spoff); [discriminate|].
      destruct (rodata_cstr_len P (Some se)) as [k|].
      - destruct (in_ranges _ _ _); discriminate.
      - pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem se ne _ HGm ltac:(lia) eq_refl) as RS.
        destruct (readable_range P A se ne); try discriminate; try exact RS.
        destruct (negb (disjoint_ranges _ _ _ _)); [discriminate|]. destruct (Z.ltb _ _); discriminate. }
    exact (nonneg_len_dead A nu _ _ HL En).
  Qed.
End CS4.
