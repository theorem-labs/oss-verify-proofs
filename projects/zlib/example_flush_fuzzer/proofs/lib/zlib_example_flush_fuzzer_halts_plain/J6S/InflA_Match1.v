(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma match_copy_step : forall win ob put from cnt,
  1 <= cnt < 2 ^ 32 ->
  match_copy win (ob, put, from, cnt)
  = let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
    if cnt =? 1 then (arr_set ob put v, put + 1, from_succ from, 0)
    else match_copy win (arr_set ob put v, put + 1, from_succ from, cnt - 1).
Proof.
  intros win ob put from cnt Hc. rewrite match_copy_mc. cbn [snd]. rewrite loopZ_step by lia. unfold mc_step at 1.
  rewrite (wrap32_id (cnt - 1)) by lia.
  destruct (Z.eqb_spec cnt 1) as [E|NE].
  - subst cnt. cbn [Z.sub Z.eqb negb]. reflexivity.
  - replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rewrite match_copy_mc. cbn [snd]. reflexivity.
Qed.

Definition ilM : cfg := CFG [] [] arm_rets [0x1e8d8; 0x1e8f0] [].

Section MatchLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition faddr (from : fromptr) : Z := match from with FWin i => cv_WB v + i | FOut i => cv_P0 v + i end.
  Definition ffits (from : fromptr) (cnt put : Z) : Prop :=
    match from with FWin i => 0 <= i /\ i + cnt <= cv_WN v | FOut i => 0 <= i /\ i < put end.

  Lemma match_loop : forall n s c r R M from cnt,
    Z.of_nat n = cnt -> 1 <= cnt ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M ->
    0 <= ir_put r -> ir_put r + cnt <= cv_NO v -> arr_len (ic_outbuf c) = cv_NO v -> obytes (cv_NO v) (ic_outbuf c) ->
    arr_len (is_window s) = cv_WN v -> (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256) ->
    ffits from cnt (ir_put r) ->
    getr R 2 = zw (cv_sp v - 224) -> getr R 8 = zw (cv_S v) ->
    getr R 19 = zw (cv_P0 v + ir_put r) -> getr R 13 = zw (faddr from) -> getr R 14 = zw (faddr from + cnt) ->
    let '(ob', put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cnt) in
    exists R' M',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e8d8) M s6_rom) (mkst R' (Z_to_bv 64 0x1e8f0) M' s6_rom)
      /\ LMEM v (mkW s (icset_outbuf c ob') (irset_put r put')) M' /\ RETC v (mkW s c r) M'
      /\ getr R' 19 = zw (cv_P0 v + put')
      /\ (forall rg, reg_in rg [13; 14; 15; 16; 19]%bv = false -> getr R' rg = getr R rg)
      /\ MFRAME v (ir_put r) put' M M' /\ put' = ir_put r + cnt /\ arr_len ob' = cv_NO v /\ obytes (cv_NO v) ob'.
  Proof.
    induction n as [|n IH]; intros s c r R M from cnt Hn Hcnt HM HRC Hp0 Hpc Hol Hob Hwl Hwb HF G2 G25 G18 G13 G14; [lia|].
    open_ictx C. open_lmem HM. open_retc HRC. unfold mapped in *.
    assert (HNO : 0 < cv_NO v) by lia. specialize (CfP HNO). specialize (CoP HNO). specialize (CSP HNO). specialize (CPW HNO).
    assert (Hcnt32 : cnt < 2 ^ 32) by (clear - Hpc Hp0 CP0; lia).
    rewrite match_copy_step by lia.
    set (bv := match from with FWin i => arr_get (is_window s) i | FOut i => arr_get (ic_outbuf c) i end). cbv zeta.
    assert (Hbv : 0 <= bv < 256) by (subst bv; destruct from as [i|i]; cbn in HF; [apply Hwb; lia | apply Hob; lia]).
    assert (Hfa : 0 < faddr from /\ faddr from + cnt < 2 ^ 63).
    { destruct from as [i|i]; cbn in HF |- *; [| clear - HF CP0 Hpc Hp0; lia].
      destruct CWB as (W0 & W1 & [[Z1 Z2] | (W2 & W3 & W4)]); [clear - HF Z1 Hcnt; lia | clear - HF W1 W2 W3; lia]. }
    assert (Hsrc : cell s6_segs M (faddr from) 1 bv).
    { subst bv. destruct from as [i|i]; cbn in HF |- *.
      - assert (HWN : cv_WN v <> 0) by (clear - HF Hcnt; lia). specialize (Mwin HWN).
        pose proof (Mwin i ltac:(clear - HF Hcnt; lia)) as X. replace (cv_WB v + 1 * i) with (cv_WB v + i) in X by lia. exact X.
      - pose proof (Mout i ltac:(clear - HF; lia)) as X. replace (cv_P0 v + 1 * i) with (cv_P0 v + i) in X by lia. exact X. }
    destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    -
      symex s6_segs ilM 8%nat [false] [RVal (EVar 38%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (19, EAdd (EVar 34%nat) (EVar 35%nat)); (13, EVar 36%nat); (14, EVar 37%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 63); (38%nat, 256)]
        NoRegions [cv_sp v - 224; cv_S v; cv_P0 v; ir_put r; faddr from; faddr from + cnt; bv] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1e8d8) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTM1" G end.
      set (M1 := wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 bv)) in *.
      assert (HM1 : LMEM v (mkW s (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) bv)) (irset_put r (ir_put r + 1))) M1).
      { subst M1. apply (LMEM_store_out v C s c r _ M bv bv HM); [clear - Hp0 Hpc Hcnt; lia | exact Hol | reflexivity | reflexivity | reflexivity]. }
      exists R', M1. split; [subst M1; by_run Hms|].
      split; [exact HM1|]. split; [subst M1; apply (RETC_other v C); [exact HRC | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | unfold sep in CfP; clear - CfP Hp0 Hpc Hcnt; cbn; lia]|].
      symex_reg HR' (19%bv : reg) as G18'. split; [rewrite G18'; f_equal; lia|].
      split; [fr_weak Hfr|]. split.
      { subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1) M M); [apply MFRAME_refl | lia | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | right; right; right; clear - E1; cbn; lia]. }
      split; [lia|]. split; [rewrite arr_len_set; exact Hol | apply obytes_set; assumption].
    -
      symex s6_segs ilM 8%nat [true] [RVal (EVar 38%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (19, EAdd (EVar 34%nat) (EVar 35%nat)); (13, EVar 36%nat); (14, EVar 37%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 63); (38%nat, 256)]
        NoRegions [cv_sp v - 224; cv_S v; cv_P0 v; ir_put r; faddr from; faddr from + cnt; bv] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1e8d8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTM2" G end.
      set (M1 := wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 bv)) in *.
      set (c1 := icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) bv)). set (r1 := irset_put r (ir_put r + 1)).
      assert (HM1 : LMEM v (mkW s c1 r1) M1).
      { subst M1 c1 r1. apply (LMEM_store_out v C s c r _ M bv bv HM); [clear - Hp0 Hpc Hcnt; lia | exact Hol | reflexivity | reflexivity | reflexivity]. }
      assert (HRC1 : RETC v (mkW s c r) M1).
      { subst M1; apply (RETC_other v C); [exact HRC | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | unfold sep in CfP; clear - CfP Hp0 Hpc Hcnt; cbn; lia]. }
      pose proof (icset_outbuf_facts c (arr_set (ic_outbuf c) (ir_put r) bv)) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
      symex_reg HR1 (19%bv : reg) as Q19. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (14%bv : reg) as Q14.
      assert (HF' : ffits (from_succ from) (cnt - 1) (ir_put r1)) by (subst r1; destruct from as [i|i]; cbn in HF |- *; lia).
      specialize (IH s c1 r1 R1 M1 (from_succ from) (cnt - 1) ltac:(lia) ltac:(lia) HM1
                    ltac:(eapply RETC_regs; [exact HRC1 | reflexivity])
                    ltac:(subst r1; cbn; lia) ltac:(subst r1; cbn; lia) ltac:(subst c1; rewrite F6, arr_len_set; exact Hol)
                    ltac:(subst c1; rewrite F6; apply obytes_set; assumption) Hwl Hwb HF'
                    ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G25)
                    ltac:(subst r1; cbn; rewrite Q19; f_equal; lia)
                    ltac:(rewrite Q13; destruct from; cbn; f_equal; lia)
                    ltac:(rewrite Q14; destruct from; cbn in *; f_equal; lia)).
      subst c1 r1. rewrite F6 in IH. cbn [ir_put irset_put] in IH.
      replace (match from_succ from with FWin i => arr_get (is_window s) i | FOut i => arr_get (arr_set (ic_outbuf c) (ir_put r) bv) i end)
        with (match from_succ from with FWin i => arr_get (is_window s) i | FOut i => arr_get (arr_set (ic_outbuf c) (ir_put r) bv) i end) in IH by reflexivity.
      lazymatch type of IH with context [match_copy ?w ?st] =>
        lazymatch goal with |- context [match_copy w ?st'] => replace (match_copy w st') with (match_copy w st) by reflexivity end;
        revert IH; destruct (match_copy w st) as [[[ob' put'] fr'] c'] eqn:EM; intros IH
      end.
      destruct IH as (R' & M' & Hms2 & HM' & HRC' & G18' & Hfr' & HF2 & Hput' & Hlen' & Hob').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      split; [| split; [exact HRC'|]].
      { first [ exact HM'
              | match type of HM' with LMEM _ ?w _ => match goal with |- LMEM _ ?w' _ => replace w' with w; [exact HM'|] end end;
                f_equal; first [destruct c; reflexivity | destruct r; reflexivity] ]. }
      split; [exact G18'|]. split.
      { intros rg Hrg. rewrite (Hfr' rg Hrg). apply Hfr1. revert Hrg. clear. intros Hrg.
        unfold reg_in in *. cbn in *. destruct (bv_eqb rg 13%bv); [discriminate|]. destruct (bv_eqb rg 14%bv); [discriminate|].
        destruct (bv_eqb rg 15%bv); [discriminate|]. destruct (bv_eqb rg 16%bv); [discriminate|]. destruct (bv_eqb rg 19%bv); [discriminate|]. reflexivity. }
      split; [| split; [lia | split; [exact Hlen' | exact Hob']]].
      apply (MFRAME_trans v _ (ir_put r + 1) _ M M1 M'); [| exact HF2].
      subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1) M M); [apply MFRAME_refl | lia | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | right; right; right; clear; cbn; lia].
  Qed.
End MatchLoop.
End FXG.
