(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_defs2
  Sj_stage2_numr1 Sj_stage2_numr2 Sj_stage2_numr3 Sj_stage2_numr4 Sj_stage2_numr5 Sj_stage2_numr6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumR.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Let s0 : st := mkst 0 0 1 0 [].

  Theorem seg_numr : forall (Q : machine_state -> Prop), Z.of_nat (length (e_tws E)) = 1%Z ->
    rdelAc_k E Q CP -> rdelB_k E Q CP -> (forall v r, num_word v -> rdelB_k (gapp E [v; r] []) Q CP) -> (forall v r, num_word v -> rdelC_k (gapp E [v; r] []) Q CP) ->
    numr_slowcall_k E Q CP s0 -> numr_fbcall_k E Q CP s0 ->
    numr_entry_k E Q CP.
  Proof using OK SHZ HCP SHZC.
    intros Q GLT KDA KDB KDB3 KDC KSL KFB.
    assert (GL3 : forall v r, Z.of_nat (length (e_tws (gapp E [v; r] []))) = 3%Z) by (intros; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia).
    pose proof (seg_numr_delA E OK SHZ CP Q KDA) as KX.
    pose proof (n_bound E OK) as HN. pose proof (ok_tcap _ OK) as [HTC _].
    assert (HLEN0 : (0 <= e_len E)%Z) by (unfold blen; lia).
    assert (HK : (0 <= k s0 <= e_n E)%Z) by (cbn; lia).
    assert (HW0 : (0 <= W s0)%Z) by (cbn; lia).
    assert (HW : (W s0 + 2 <= e_tcap E)%Z) by (cbn; lia).
    assert (KJ : forall v r, num_word v -> numr_join_k (gapp E [v; r] []) Q CP s0)
      by (intros v r Hv; exact (seg_numr_join (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 (KDC v r Hv))).
    assert (KFIN0 : forall v r, num_word v -> numr_fin_k (gapp E [v; r] []) Q CP s0 0 3)
      by (intros v r Hv; exact (seg_numr_fin (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 0%Z 3%Z (or_introl eq_refl) (fun _ => eq_refl) (fun _ => GL3 v r) (KDB3 v r Hv))).
    assert (TAIL : forall neg, (0 <= neg <= 1)%Z -> (0 + neg < LEN)%Z -> forall p, (0 <= p <= LEN)%Z -> numr_scan_k E Q CP s0 neg p).
    { intros neg HNEG HS p HP.
      pose proof (seg_numr_write E OK SHZ CP HCP SHZC Q s0 neg GLT KFIN0) as KW.
      pose proof (seg_numr_range E OK SHZ CP HCP SHZC Q s0 neg HW0 HW GLT KX KJ
                    (fun e He => seg_numr_cmp E OK SHZ CP HCP SHZC Q s0 neg e He KW (seg_numr_cmpslow E OK SHZ CP HCP SHZC Q s0 neg e He KW KFB))) as KR.
      assert (KFLT : forall p', (0 <= p' <= LEN)%Z -> numr_flt_k E Q CP s0 neg p')
        by (intros p' HP'; exact (seg_numr_flt E OK SHZ CP HCP SHZC Q s0 neg p' HK HNEG HS HP' KR KSL)).
      apply (seg_numr_scan E OK SHZ CP HCP SHZC Q s0 neg p HK HNEG HP).
      - intros q0 HQ0. apply (seg_numr_expd E OK SHZ CP HCP SHZC Q s0 neg q0 HK HNEG ltac:(lia) KX). intros p' HP'. apply KFLT. lia.
      - apply KFLT. exact HP.
      - apply (seg_numr_int E OK SHZ CP HCP SHZC Q s0 neg p HK HP HW0 HW GLT KX KJ). }
    apply (seg_numr_entry E OK SHZ CP HCP SHZC Q s0 KX).
    intros neg p HNEG HS HP.
    apply (seg_numr_dot E OK SHZ CP HCP SHZC Q s0 neg p HK HNEG HP).
    - intros HDOT.
      assert (HPL : (p < LEN)%Z) by (nz_lt_by ltac:(rewrite HDOT; lia)).
      apply (seg_numr_frac E OK SHZ CP HCP SHZC Q s0 neg p HK HNEG ltac:(lia)).
      intros r HR. apply (seg_numr_ftail E OK SHZ CP HCP SHZC Q s0 neg p r HK HNEG ltac:(lia) HR).
      intros r' HR'. apply (seg_numr_ftail2 E OK SHZ CP HCP SHZC Q s0 neg p r' HK HNEG ltac:(lia) ltac:(lia) KX).
      intros p' HP'. apply (TAIL neg HNEG HS p'). lia.
    - apply (TAIL neg HNEG HS p). lia.
  Qed.

  Theorem seg_numr_after_slow : forall (Q : machine_state -> Prop) r v,
    (r = 9 \/ r = 0)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> (forall v' r', num_word v' -> rdelB_k (gapp E [v'; r'] []) Q CP) -> numr_slowret_k E Q CP s0 r v.
  Proof using OK SHZ HCP SHZC.
    intros Q r v HR GLT KDB3.
    apply (seg_numr_slowret E OK SHZ CP HCP SHZC Q s0 r v GLT). intros v' r' Hv.
    apply (seg_numr_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 r 3%Z ltac:(destruct HR; [right | left]; assumption) (fun _ => eq_refl)
             ltac:(intros _; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia) (KDB3 v' r' Hv)).
  Qed.
  Theorem seg_numr_after_fb : forall (Q : machine_state -> Prop) r v,
    (r = 0 \/ r = 1)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdelB_k E Q CP -> (forall v' r', num_word v' -> rdelB_k (gapp E [v'; r'] []) Q CP) -> numr_fbret_k E Q CP s0 r v.
  Proof using OK SHZ HCP SHZC.
    intros Q r v HR GLT KDB KDB3.
    apply (seg_numr_fbret E OK SHZ CP HCP SHZC Q s0 r v HR).
    - apply (seg_numr_fin E OK SHZ CP HCP SHZC Q s0 9%Z 1%Z (or_intror eq_refl) ltac:(intros HH; discriminate HH) ltac:(intros HH; discriminate HH) KDB).
    - apply (seg_numr_write E OK SHZ CP HCP SHZC Q s0 0%Z GLT). intros v' r' Hv.
      apply (seg_numr_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 0%Z 3%Z (or_introl eq_refl) (fun _ => eq_refl)
             ltac:(intros _; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia) (KDB3 v' r' Hv)).
  Qed.
End NumR.
