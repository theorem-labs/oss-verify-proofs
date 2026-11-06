(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain Lept_objkit LeptL_kit Ed_fp Gq_numa Numa_kit Ed_tracekit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section NUMAC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem numaCreate_ok : numaCreate_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n ras
    FDO MST -> A0 NR UC TR ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct A0 as [NR2 ->].
  unfold entry_st, e_numaCreate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  walk_to AF MST [(usp - 32, usp)] [e_calloc; 0x918cc; 0x918d0].   (* [comment removed for export] *)
  destruct (Z.eq_dec n 0) as [N0|N1].
  { (* [comment removed for export] *)
    subst n. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v end. cbv iota.
    awalk [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    match goal with MUx : munch _ m ?mx |- _ => rename MUx into MU1; rename mx into m1 end.
    assert (UC1 : uctx m1 (Z_to_bv 64 usp) s0 ras).
    { unfold uctx in UC |- *. rewrite unsigned_lit by lia. unfold usp in UC |- *.
      apply (chain_ok_keep ras m m1 _ _ UC). intros a Ha. apply MU1. cbn [outside]. unfold USTACK_TOP in Ha. lia. }
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 32); rt_side idtac.
      - unfold CALLOC_MAX; lia.
      - eapply (numaCreate_unwind1 m1 (Z_to_bv 64 usp) s0 ras); [exact UC1 | exact TR | rewrite !unsigned_lit by lia; lia]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    change (1 * 32) with 32 in *. change (Z.to_nat 32) with 32%nat in *.
    lazymatch goal with H : rt_live RT ?S = (?p, 32) :: _ |- _ => rename H into LVA; rename S into Σ1; set (na := p) in * end.
    assert (INA : In (na, 32) (rt_live RT Σ1)) by (rewrite LVA; left; reflexivity).
    lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
      pose proof (af_live_range RT AF Σ1 mm na 32 A ltac:(rewrite LVA; left; reflexivity)) as (_ & PAHI & PASEG);
      pose proof (gp_live_hi RT GP Σ1 mm na 32 A ltac:(rewrite LVA; left; reflexivity)) as PASH;
      assert (NCA : forall a, PF a -> a < na \/ na + 32 <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mm na 32 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVA);
            [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *.
    walk_to AF MST [(usp - 32, usp); (na, na + 32)] [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists na, 32; split; [rewrite LVA; left; reflexivity| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia).
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 50) (size := 4); rt_side idtac.
      - unfold CALLOC_MAX; lia.
      - rewrite LVA; cbn [length]; lia.
      - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_numaCreate_2| left; ul]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    change (50 * 4) with 200 in *. change (Z.to_nat 200) with 200%nat in *.
    lazymatch goal with H : rt_live RT ?S = (?p, 200) :: _ |- _ => rename H into LVB2; rename S into Σ2; set (arr := p) in * end.
    assert (INB : In (arr, 200) (rt_live RT Σ2)) by (rewrite LVB2; left; reflexivity).
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *.
    lazymatch goal with A : ART RT Σ2 ?mm |- cps _ (ASTA RT Σ2 _ _) _ =>
      assert (QAB : na + 32 <= arr \/ arr + 200 <= na)
        by (pose proof (af_live_disj RT AF Σ2 mm arr 200 na 32 [] (rt_live RT Σ1) A LVB2 ltac:(cbn [app]; exact INA)) as X; clear - X; lia) end.
    walk_to AF MST [(usp - 32, usp); (na, na + 32)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists na, 32; split; [rewrite LVB2; right; exact INA| lia]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia)
    end.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    exists Σ2, na, arr.
    split; [| unfold numa_live, numa_cap; cbn [Z.eqb Z.mul Pos.mul]; rewrite LVB2, LVA; alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split; [intros a Ha _; apply AGF; exact Ha|].
    unfold numa_obj, numa_cap. cbn [Z.eqb length Z.of_nat].
    lazymatch goal with NA : rw_cells asegs ?mm na ?cs, AR : rw_cells asegs ?mm' arr ?cs' |- _ =>
      split; [eexists; exact NA|]; split; [eexists; exact AR|] end.
    split; [unfold chunk; split; [rewrite LVB2; right; exact INA| repeat split; first [assumption | lia]]|].
    split; [unfold chunk; split; [exact INB| repeat split; first [assumption | lia]]|].
    split; [clear - QAB; lia|]. split; [lia|]. cbn [length Z.of_nat]. lia.
  }
  (* [comment removed for export] *)
  assert (SW : bv_swrap 32 (n + 18446744073609551615) = n - 100000001).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 / 2) with 2147483648.
    replace (n + 18446744073609551615 + 2147483648) with ((n + 2047483647) + 4294967296 * 4294967296) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
  rewrite SW.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; unfold bv_ltu; rewrite (unsigned_lit_neg (n - 100000001)) by lia;
                                     rewrite (unsigned_lit_neg (-100000000)) by lia; apply Bool.negb_true_iff; apply Z.ltb_ge; lia] end.
    awalk [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    match goal with MUx : munch _ m ?mx |- _ => rename MUx into MU1; rename mx into m1 end.
    assert (UC1 : uctx m1 (Z_to_bv 64 usp) s0 ras).
    { unfold uctx in UC |- *. rewrite unsigned_lit by lia. unfold usp in UC |- *.
      apply (chain_ok_keep ras m m1 _ _ UC). intros a Ha. apply MU1. cbn [outside]. unfold USTACK_TOP in Ha. lia. }
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 32); rt_side idtac;
      [ unfold CALLOC_MAX; lia
      | eapply (numaCreate_unwind1 m1 (Z_to_bv 64 usp) s0 ras); [exact UC1 | exact TR | rewrite !unsigned_lit by lia; lia] ]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    change (1 * 32) with 32 in *. change (Z.to_nat 32) with 32%nat in *.
    lazymatch goal with H : rt_live RT ?S = (?p, 32) :: _ |- _ => rename H into LVA; rename S into Σ1; set (na := p) in * end.
    assert (INA : In (na, 32) (rt_live RT Σ1)) by (rewrite LVA; left; reflexivity).
    lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
      pose proof (af_live_range RT AF Σ1 mm na 32 A ltac:(rewrite LVA; left; reflexivity)) as (_ & PAHI & PASEG);
      pose proof (gp_live_hi RT GP Σ1 mm na 32 A ltac:(rewrite LVA; left; reflexivity)) as PASH;
      assert (NCA : forall a, PF a -> a < na \/ na + 32 <= a)
        by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mm na 32 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVA);
            [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *.
    walk_to AF MST [(usp - 32, usp); (na, na + 32)] [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists na, 32; split; [rewrite LVA; left; reflexivity| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia).
    unfold numa_cap in *. replace (n =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z_le_gt_dec (n * 4) 64512) as [PRIM|SEC].
    + eapply cps_seq.
      { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := n) (size := 4); rt_side idtac.
        - unfold CALLOC_MAX; lia.
        - rewrite LVA; cbn [length]; lia.
        - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_numaCreate_2| left; ul]. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
      replace (n * 4) with (4 * n) in * by lia.
      lazymatch goal with H : rt_live RT ?S = (?p, 4 * n) :: _ |- _ => rename H into LVB2; rename S into Σ2; set (arr := p) in * end.
      assert (INB : In (arr, 4 * n) (rt_live RT Σ2)) by (rewrite LVB2; left; reflexivity).
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
      unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
      refresh RT AF. unfold SHB in *.
      lazymatch goal with A : ART RT Σ2 ?mm |- cps _ (ASTA RT Σ2 _ _) _ =>
        assert (QAB : na + 32 <= arr \/ arr + 4 * n <= na)
          by (pose proof (af_live_disj RT AF Σ2 mm arr (4 * n) na 32 [] (rt_live RT Σ1) A LVB2 ltac:(cbn [app]; exact INA)) as X; clear - X; lia) end.
      walk_to AF MST [(usp - 32, usp); (na, na + 32)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                          intros zz Hzz; right; right; left; exists na, 32; split; [rewrite LVB2; right; exact INA| lia]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia)
      end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbv iota.
      exists Σ2, na, arr.
      split; [| unfold numa_live; rewrite LVB2, LVA; alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha _; apply AGF; exact Ha|].
      lazymatch goal with NA : rw_cells asegs ?mm na ?cs, AR : rw_cells asegs ?mm' arr ?cs' |- _ =>
        split; [eexists; exact NA|]; split; [eexists; apply (numa_arr_fresh _ arr n _ AR); lia|] end.
      split; [unfold chunk; split; [rewrite LVB2; right; exact INA| repeat split; first [assumption | lia]]|].
      split; [unfold chunk; split; [exact INB| repeat split; first [assumption | lia]]|].
      split; [lia|]. split; [lia|]. cbn [length Z.of_nat]. lia.
    + (* [comment removed for export] *)
      exfalso; lia.   (* [comment removed for export] *)
Qed.
End NUMAC.
