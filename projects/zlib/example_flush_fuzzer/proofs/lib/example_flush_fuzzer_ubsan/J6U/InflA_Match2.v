(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b.

Module InflA_Match1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

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

Definition ilM : cfg := CFG [] [] arm_rets [0x21128; 0x21158] [].

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
    getr R 2 = zw (cv_sp v - 256) -> getr R 8 = zw (cv_S v) ->
    getr R 9 = zw (cv_P0 v + ir_put r) -> getr R 11 = zw (faddr from) -> getr R 13 = zw (faddr from) -> getr R 14 = zw (cv_P0 v + ir_put r) ->
    getr R 12 = zw cnt ->
    let '(ob', put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cnt) in
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x21128) M s6u_rom) (mkst R' (Z_to_bv 64 0x21158) M' s6u_rom)
      /\ LMEM v (mkW s (icset_outbuf c ob') (irset_put r put')) M' /\ RETC v (mkW s c r) M'
      /\ getr R' 9 = zw (cv_P0 v + put') /\ getr R' 15 = zw (cv_P0 v + put')
      /\ (forall rg, reg_in rg [9; 11; 12; 13; 14; 15; 16]%bv = false -> getr R' rg = getr R rg)
      /\ MFRAME v (ir_put r) put' M M' /\ put' = ir_put r + cnt /\ arr_len ob' = cv_NO v /\ obytes (cv_NO v) ob'.
  Proof.
    induction n as [|n IH]; intros s c r R M from cnt Hn Hcnt HM HRC Hp0 Hpc Hol Hob Hwl Hwb HF G2 G27 G9 G11 G13 G14 G12; [lia|].
    open_ictx C. open_lmem HM. open_retc HRC. unfold mapped in *.
    assert (HNO : 0 < cv_NO v) by lia. specialize (CfP HNO). specialize (CoP HNO). specialize (CSP HNO). specialize (CPW HNO).
    assert (Hcnt32 : cnt < 2 ^ 32) by (clear - Hpc Hp0 CP0; lia).
    rewrite match_copy_step by lia.
    set (bv := match from with FWin i => arr_get (is_window s) i | FOut i => arr_get (ic_outbuf c) i end). cbv zeta.
    assert (Hbv : 0 <= bv < 256) by (subst bv; destruct from as [i|i]; cbn in HF; [apply Hwb; lia | apply Hob; lia]).
    assert (Hfa : 0 < faddr from /\ faddr from + cnt < 2 ^ 63).
    { destruct from as [i|i]; cbn in HF |- *; [| clear - HF CP0 Hpc Hp0; lia].
      destruct CWB as (W0 & W1 & [[Z1 Z2] | (W2 & W3 & W4)]); [clear - HF Z1 Hcnt; lia | clear - HF W1 W2 W3; lia]. }
    assert (Hsrc : cell s6u_segs M (faddr from) 1 bv).
    { subst bv. destruct from as [i|i]; cbn in HF |- *.
      - assert (HWN : cv_WN v <> 0) by (clear - HF Hcnt; lia). specialize (Mwin HWN).
        pose proof (Mwin i ltac:(clear - HF Hcnt; lia)) as X. replace (cv_WB v + 1 * i) with (cv_WB v + i) in X by lia. exact X.
      - pose proof (Mout i ltac:(clear - HF; lia)) as X. replace (cv_P0 v + 1 * i) with (cv_P0 v + i) in X by lia. exact X. }
    destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    -
      symex s6u_segs ilM 14%nat [false; false; false] [RVal (EVar 38%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (9, EAdd (EVar 34%nat) (EVar 35%nat)); (11, EVar 36%nat); (13, EVar 36%nat); (14, EAdd (EVar 34%nat) (EVar 35%nat)); (12, EVar 37%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 31); (38%nat, 256)]
        NoRegions [cv_sp v - 256; cv_S v; cv_P0 v; ir_put r; faddr from; cnt; bv] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x21128) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTM1" G end.
      set (M1 := wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 bv)) in *.
      assert (HM1 : LMEM v (mkW s (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) bv)) (irset_put r (ir_put r + 1))) M1).
      { subst M1. apply (LMEM_store_out v C s c r _ M bv bv HM); [clear - Hp0 Hpc Hcnt; lia | exact Hol | reflexivity | reflexivity | reflexivity | reflexivity]. }
      exists R', M1. split; [subst M1; by_run Hms|].
      split; [exact HM1|]. split; [subst M1; apply (RETC_other v C); [exact HRC | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | unfold sep in CfP; clear - CfP Hp0 Hpc Hcnt; cbn; lia]|].
      symex_reg HR' (9%bv : reg) as G9'. symex_reg HR' (15%bv : reg) as G15'. split; [rewrite G9'; f_equal; lia|]. split; [rewrite G15'; f_equal; lia|].
      split; [fr_weak Hfr|]. split.
      { subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1) M M); [apply MFRAME_refl | lia | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | right; right; right; clear - E1; cbn; lia]. }
      split; [lia|]. split; [rewrite arr_len_set; exact Hol | apply obytes_set; assumption].
    -
      symex s6u_segs ilM 14%nat [false; false; true] [RVal (EVar 38%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (9, EAdd (EVar 34%nat) (EVar 35%nat)); (11, EVar 36%nat); (13, EVar 36%nat); (14, EAdd (EVar 34%nat) (EVar 35%nat)); (12, EVar 37%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 31); (38%nat, 256)]
        NoRegions [cv_sp v - 256; cv_S v; cv_P0 v; ir_put r; faddr from; cnt; bv] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x21128) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTM2" G end.
      set (M1 := wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 bv)) in *.
      set (c1 := icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) bv)). set (r1 := irset_put r (ir_put r + 1)).
      assert (HM1 : LMEM v (mkW s c1 r1) M1).
      { subst M1 c1 r1. apply (LMEM_store_out v C s c r _ M bv bv HM); [clear - Hp0 Hpc Hcnt; lia | exact Hol | reflexivity | reflexivity | reflexivity | reflexivity]. }
      assert (HRC1 : RETC v (mkW s c r) M1).
      { subst M1; apply (RETC_other v C); [exact HRC | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | unfold sep in CfP; clear - CfP Hp0 Hpc Hcnt; cbn; lia]. }
      pose proof (icset_outbuf_facts c (arr_set (ic_outbuf c) (ir_put r) bv)) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
      symex_reg HR1 (9%bv : reg) as Q19. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (12%bv : reg) as Q12.
      assert (HF' : ffits (from_succ from) (cnt - 1) (ir_put r1)) by (subst r1; destruct from as [i|i]; cbn in HF |- *; lia).
      specialize (IH s c1 r1 R1 M1 (from_succ from) (cnt - 1) ltac:(lia) ltac:(lia) HM1
                    ltac:(eapply RETC_regs; [exact HRC1 | reflexivity])
                    ltac:(subst r1; cbn; lia) ltac:(subst r1; cbn; lia) ltac:(subst c1; rewrite F6, arr_len_set; exact Hol)
                    ltac:(subst c1; rewrite F6; apply obytes_set; assumption) Hwl Hwb HF'
                    ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G27)
                    ltac:(subst r1; cbn; rewrite Q19; f_equal; lia)
                    ltac:(rewrite Q11; destruct from; cbn; f_equal; lia)
                    ltac:(rewrite Q13; destruct from; cbn; f_equal; lia)
                    ltac:(subst r1; cbn; rewrite Q14; f_equal; lia)
                    ltac:(rewrite Q12; rewrite ?szwrap32_small by (clear - Hcnt Hcnt32 Hpc Hp0 CP0; lia); f_equal; lia)).
      subst c1 r1. rewrite F6 in IH. cbn [ir_put irset_put] in IH.
      replace (match from_succ from with FWin i => arr_get (is_window s) i | FOut i => arr_get (arr_set (ic_outbuf c) (ir_put r) bv) i end)
        with (match from_succ from with FWin i => arr_get (is_window s) i | FOut i => arr_get (arr_set (ic_outbuf c) (ir_put r) bv) i end) in IH by reflexivity.
      lazymatch type of IH with context [match_copy ?w ?st] =>
        lazymatch goal with |- context [match_copy w ?st'] => replace (match_copy w st') with (match_copy w st) by reflexivity end;
        revert IH; destruct (match_copy w st) as [[[ob' put'] fr'] c'] eqn:EM; intros IH
      end.
      destruct IH as (R' & M' & Hms2 & HM' & HRC' & G18' & G15' & Hfr' & HF2 & Hput' & Hlen' & Hob').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      split; [| split; [exact HRC'|]].
      { first [ exact HM'
              | match type of HM' with LMEM _ ?w _ => match goal with |- LMEM _ ?w' _ => replace w' with w; [exact HM'|] end end;
                f_equal; first [destruct c; reflexivity | destruct r; reflexivity] ]. }
      split; [exact G18'|]. split; [exact G15'|]. split.
      { intros rg Hrg. rewrite (Hfr' rg Hrg). apply Hfr1. revert Hrg. clear. intros Hrg.
        unfold reg_in in *. cbn in *. destruct (bv_eqb rg 9%bv); [discriminate|]. destruct (bv_eqb rg 11%bv); [discriminate|]. destruct (bv_eqb rg 12%bv); [discriminate|].
        destruct (bv_eqb rg 13%bv); [discriminate|]. destruct (bv_eqb rg 14%bv); [discriminate|].
        destruct (bv_eqb rg 15%bv); [discriminate|]. destruct (bv_eqb rg 16%bv); [discriminate|]. reflexivity. }
      split; [| split; [lia | split; [exact Hlen' | exact Hob']]].
      apply (MFRAME_trans v _ (ir_put r + 1) _ M M1 M'); [| exact HF2].
      subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1) M M); [apply MFRAME_refl | lia | clear - CP0 Hp0; lia | clear - CP0 Hp0 Hpc Hcnt; cbn; lia | right; right; right; clear; cbn; lia].
  Qed.
End MatchLoop.
End FXG.
End InflA_Match1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b. Import InflA_Match1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition msel (s : inflate_state) (r : iregs) : option (fromptr * Z) :=
  let cp := ir_out r - ir_left r in
  if cp <? is_offset s then
    let copy := is_offset s - cp in
    if is_whave s <? copy then None
    else
      let '(copy, from) :=
        if is_wnext s <? copy then (copy - is_wnext s, FWin (is_wsize s - (copy - is_wnext s)))
        else (copy, FWin (is_wnext s - copy)) in
      Some (from, if is_length s <? copy then is_length s else copy)
  else Some (FOut (ir_put r - is_offset s), is_length s).

Definition mclamp (r : iregs) (copy : Z) : Z := if ir_left r <? copy then ir_left r else copy.

Lemma arm_MATCH_eq : forall s c r,
  is_sane s = 1 -> 0 <= ir_out r - ir_left r < 2 ^ 32 -> 0 <= is_offset s < 2 ^ 32 -> 0 <= is_wnext s ->
  0 <= ir_left r < 2 ^ 32 -> 0 <= is_length s < 2 ^ 32 ->
  arm_MATCH ivar_ref (mkW s c r)
  = if ir_left r =? 0 then ALeave (mkW s c r)
    else match msel s r with
         | None => ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_distance_too_far_back) r)
         | Some (from, copy) =>
             let cpy := mclamp r copy in
             let '(ob, put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy) in
             let s1 := iset_length s (is_length s - cpy) in
             ARun tt (mkW (if is_length s - cpy =? 0 then iset_mode s1 LEN else s1) (icset_outbuf c ob)
                          (irset_put (irset_left r (ir_left r - cpy)) put'))
         end.
Proof.
  intros s c r Hsane Hcp Hoff Hwn Hlf Hlen. unfold arm_MATCH. mstep1 (@gr_eq iregs).
  destruct (ir_left r =? 0); [rewrite aleave_eq; reflexivity|].
  mstep1 (@gs_eq inflate_state). rewrite (wrap32_id (ir_out r - ir_left r)) by exact Hcp.
  unfold msel, mclamp. cbn [iv_aux ivar_ref]. rewrite Hsane. cbn [Z.eqb negb andb].
  assert (TAIL : forall from copy, 0 <= copy <= is_length s ->
    (abind (fun w : iw => ARun (Some (from, copy)) w)
      (fun fc => match fc with
       | Some (from, copy) =>
           (ur (fun r0 => irset_left r0 (wrap32 (ir_left r0 - (if ir_left r <? copy then ir_left r else copy)))) ;;
            us (fun s0 => iset_length s0 (wrap32 (is_length s0 - (if ir_left r <? copy then ir_left r else copy)))) ;;
            (fun w : iw => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, if ir_left r <? copy then ir_left r else copy) in
                           ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))) ;;
            do s0 <- gs (fun s0 => s0) ; if is_length s0 =? 0 then set_mode LEN else aret tt)%am
       | None => aret tt end)) (mkW s c r)
    = (let cpy := if ir_left r <? copy then ir_left r else copy in
       let '(ob, put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy) in
       let s1 := iset_length s (is_length s - cpy) in
       ARun tt (mkW (if is_length s - cpy =? 0 then iset_mode s1 LEN else s1) (icset_outbuf c ob) (irset_put (irset_left r (ir_left r - cpy)) put')))).
  { intros from copy Hcopy. rewrite abind_run. cbv beta iota. mstep1 ur_eq. mstep1 us_eq. rewrite abind_run. cbv beta. cbn [w_s w_c w_r]. irnorm.
    cbv zeta. rewrite !wrap32_id by (destruct (Z.ltb_spec (ir_left r) copy); lia).
    lazymatch goal with |- ?L = ?R =>
      lazymatch R with context [match_copy ?w2 ?st2] =>
      lazymatch L with context [match_copy ?w ?st] =>
        replace (match_copy w2 st2) with (match_copy w st) by reflexivity; destruct (match_copy w st) as [[[ob put'] fr'] c'] end end end.
    mstep1 (@gs_eq inflate_state). irnorm. cbn [is_length iset_length].
    destruct (_ =? 0); [rewrite set_mode_eq|unfold aret]; reflexivity. }
  destruct (Z.ltb_spec (ir_out r - ir_left r) (is_offset s)) as [LT|GE].
  - rewrite (wrap32_id (is_offset s - (ir_out r - ir_left r))) by lia. rewrite andb_true_r.
    destruct (is_whave s <? is_offset s - (ir_out r - ir_left r)).
    { rewrite abind_run. mstep1 go_bad_eq. unfold aret. cbv beta iota. reflexivity. }
    destruct (Z.ltb_spec (is_wnext s) (is_offset s - (ir_out r - ir_left r))) as [WR|NW].
    + rewrite (wrap32_id (is_offset s - (ir_out r - ir_left r) - is_wnext s)) by lia.
      unfold aret at 1. apply TAIL. destruct (Z.ltb_spec (is_length s) (is_offset s - (ir_out r - ir_left r) - is_wnext s)); lia.
    + unfold aret at 1. apply TAIL. destruct (Z.ltb_spec (is_length s) (is_offset s - (ir_out r - ir_left r))); lia.
  - unfold aret at 1. apply TAIL. lia.
Qed.


Lemma sr_sane : forall s, SRNGq s -> is_sane s = 1.
Proof. intros s H. do 27 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.
Lemma sr_winb : forall s, SRNGq s -> forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256.
Proof. intros s H. do 31 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.
Lemma sinv_wcur : forall s, sinv s -> 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s.
Proof. intros s H. destruct H as (A & B & _). exact (conj A B). Qed.
Lemma sinv_match : forall s, sinv s -> is_mode s = MATCH -> 1 <= is_length s <= 258 /\ 1 <= is_offset s <= 32768.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.


Definition ilMS : cfg := CFG [] [] arm_rets (0x21128 :: arm_stops) [].

Section MatchBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition tpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
     (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
     (26, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EAdd (EVar 37%nat) (EVar 38%nat))].

  Lemma match_tail : forall s c r R M R1 from cpy,
    is_mode s = MATCH -> 1 <= cpy <= is_length s -> cpy <= ir_left r -> is_length s <= 258 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    arr_len (is_window s) = cv_WN v -> (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256) ->
    ffits v from cpy (ir_put r) ->
    (forall rg, reg_in rg [10; 11; 12; 13; 14; 15; 16]%bv = false -> getr R1 rg = getr R rg) ->
    getr R1 11 = zw (faddr v from) -> getr R1 13 = zw (faddr v from) -> getr R1 12 = zw cpy -> getr R1 14 = zw (cv_P0 v + ir_put r) ->
    let M1 := wbytes (wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r - cpy))) (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - cpy)) in
    let '(ob, put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy) in
    let s1 := iset_length s (is_length s - cpy) in
    exists R' M' pc',
      msteps s6u_segs (mkst R1 (Z_to_bv 64 0x21128) M1 s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M
           (ARun tt (mkW (if is_length s - cpy =? 0 then iset_mode s1 LEN else s1) (icset_outbuf c ob)
                         (irset_put (irset_left r (ir_left r - cpy)) put'))) R' M' pc'.
  Proof.
    intros s c r R M R1 from cpy Hmode Hcpy Hcl Hl258 HM HRC HX HF HV RI CI Hwl Hwb HFF Hfr1 A11 A13 A12 A14. cbv zeta.
    open_ictx C. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hl32 : ir_left r < 2 ^ 31) by (clear - Rpl Rpt0 CP0; lia).
    set (s1 := iset_length s (is_length s - cpy)).
    set (r1 := irset_left r (ir_left r - cpy)).
    set (M0 := wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r - cpy))).
    set (M1 := wbytes M0 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - cpy))).
    assert (HM0 : LMEM v (mkW s c r1) M0).
    { subst M0. apply (LMEM_store_leftc v C s c r r1 M HM); subst r1; cbn [ir_put ir_left ir_out irset_left]; [exact Hput | reflexivity | clear - Hcl Hl32 Hcpy; lia | reflexivity]. }
    assert (HM1 : LMEM v (mkW s1 c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M0 108 _ HM0); [lia | cbn; lia | subst r1; exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M0 (cv_S v) _ s _ (lm_sc _ _ _ HM0)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW s1 c r1) M1) by (subst M1 M0; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | reflexivity]).
    pose proof (match_loop v C (Z.to_nat cpy) s1 c r1 R1 M1 from cpy ltac:(apply Z2Nat.id; lia) ltac:(lia) HM1 HRC1
                  ltac:(subst r1; exact Rpt0) ltac:(subst r1; cbn; clear - Hcl Rpl; lia) Col Coutb ltac:(subst s1; exact Hwl) ltac:(subst s1; exact Hwb) ltac:(subst r1; exact HFF)
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact P2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact P27)
                  ltac:(subst r1; rewrite (Hfr1 (9%bv : reg) eq_refl); exact P9) A11 A13 ltac:(subst r1; exact A14) A12) as ML.
    replace (is_window s1) with (is_window s) in ML by (subst s1; destruct s; reflexivity).
    replace (ir_put r1) with (ir_put r) in ML by (subst r1; reflexivity).
    destruct (match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy)) as [[[ob put'] fr'] c'] eqn:EM.
    destruct ML as (R2 & M2 & Hms2 & HM2 & HRC2 & Q9 & Q15 & Hfr2 & HF2 & Eput & Hol2 & Hob2).
    pose proof HM2 as HM2'. open_lmem HM2'. open_frame Mfr. unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. cbn [w_s] in C92. replace (is_length s1) with (is_length s - cpy) in C92 by (subst s1; destruct s; reflexivity).
    pose proof (is6_mode _ _ _ _ Msc) as C8. cbn [w_s] in C8. replace (is_mode s1) with MATCH in C8 by (subst s1; rewrite <- Hmode; destruct s; reflexivity).
    pose proof (icset_outbuf_facts c ob) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    set (r2 := mkIR (ir_next r) (ir_have r) put' (ir_left r - cpy) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r)).
    assert (Q2 : getr R2 2 = zw (cv_sp v - 256)) by (rewrite (Hfr2 (2%bv : reg) eq_refl), (Hfr1 (2%bv : reg) eq_refl); exact P2).
    assert (Q27 : getr R2 8 = zw (cv_S v)) by (rewrite (Hfr2 (8%bv : reg) eq_refl), (Hfr1 (8%bv : reg) eq_refl); exact P27).
    assert (Q8 : getr R2 18 = zw (cv_ZP v)) by (rewrite (Hfr2 (18%bv : reg) eq_refl), (Hfr1 (18%bv : reg) eq_refl); exact P8).
    assert (Q1 : getr R2 1 = zw 16209) by (rewrite (Hfr2 (1%bv : reg) eq_refl), (Hfr1 (1%bv : reg) eq_refl); exact P1).
    assert (Q24 : getr R2 23 = zw (ir_have r)) by (rewrite (Hfr2 (23%bv : reg) eq_refl), (Hfr1 (23%bv : reg) eq_refl); exact P24).
    assert (Q22 : getr R2 25 = zw (ir_hold r)) by (rewrite (Hfr2 (25%bv : reg) eq_refl), (Hfr1 (25%bv : reg) eq_refl); exact P22).
    assert (Q18 : getr R2 19 = zw (ir_bits r)) by (rewrite (Hfr2 (19%bv : reg) eq_refl), (Hfr1 (19%bv : reg) eq_refl); exact P18).
    assert (Q25 : getr R2 26 = zw (cv_I0 v + ir_next r)) by (rewrite (Hfr2 (26%bv : reg) eq_refl), (Hfr1 (26%bv : reg) eq_refl); exact P25).
    assert (Q9' : getr R2 9 = zw (cv_P0 v + ir_put r2)) by (subst r2; exact Q9).
    assert (Q15' : getr R2 15 = zw (cv_P0 v + ir_put r2)) by (subst r2; exact Q15).
    assert (Q3 : getr R2 3 = getr (cv_R0 v) 3) by (rewrite (Hfr2 (3%bv : reg) eq_refl), (Hfr1 (3%bv : reg) eq_refl); exact G3).
    assert (Q4 : getr R2 4 = getr (cv_R0 v) 4) by (rewrite (Hfr2 (4%bv : reg) eq_refl), (Hfr1 (4%bv : reg) eq_refl); exact G4).
    assert (Er3 : irset_put (irset_left r (ir_left r - cpy)) put' = irset_put r1 put') by (subst r1; reflexivity).
    destruct (Z.eqb_spec (is_length s - cpy) 0) as [L0|L0].
    -
      rewrite L0 in C92.
      arm_symexP tpins ilS 20%nat [true] [RVal (ELit 0); RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r2 (@nil Z) NoVals F0
        (mkst R2 (Z_to_bv 64 0x21158) M2 s6u_rom) R' HR' Hfr Hms.
      all: cbn [r2 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in *; try arm_side.
      all: match goal with |- ?G => idtac "LEFTT1" G end.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in *.
      assert (HM3 : LMEM v (mkW (iset_mode s1 LEN) (icset_outbuf c ob) (irset_put r1 put')) M3).
      { apply (LMEM_store_scalar v C s1 _ _ _ M2 8 _ HM2); [lia | cbn; lia | subst r1; cbn; clear - Eput Hput Hcl Rpl Hcpy; lia | | subst s1; reflexivity ..].
        apply (is6_upd_mode M2 (cv_S v) _ s1 LEN Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      arm_disp C HM3 Hfr R3 Hms3 G26' Hfr3.
      exists R3, M3, (arm6_pc (is_mode (iset_mode s1 LEN))). split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [| exact Hms3]; subst M3; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split].
      + split; [exact HM3|]. split; [subst M3; apply (RETC_regs v (mkW s1 c r1)); [apply (RETC_other v C); [exact HRC2 | clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia] | subst r1; reflexivity]|]. split.
        * apply (LX_step0 v s c r _ _ (irset_put r1 put') HX NH NB); subst s1 r1; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; exact Xmsg | bk_side].
        * unfold LREG_arm, LVARS; cbn [w_r]. subst r1. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_put irset_left].
          split; [| split; [| intros _; exact G26']].
          -- lfix_close2 Hfr3 Hfr HR'.
          -- regs_via2 Hfr3 Hfr. all: first [rewrite Eput in Q9; exact Q9 | symex_reg HR' (9%bv : reg) as G9'; rewrite G9'; f_equal; clear - Eput; lia | match goal with |- ?G => idtac "T1REG LEFT" G end].
      + subst s1. split; [destruct s; reflexivity | split; destruct s; reflexivity].
      + cbn [w_r]. subst M3 r1. cbn [ir_put irset_put irset_left].
        apply (MFRAME_store v (ir_put r) put' put'); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_trans v _ (ir_put r) _ M M1 M2); [| exact HF2].
        subst M1 M0. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
    -
      assert (HL : 0 < is_length s - cpy < 259) by (clear - L0 Hcpy Hl258; lia).
      arm_symexP tpins ilS 20%nat [false] [RVal (EVar 45%nat); RVal (EVar 35%nat)] (@nil (Z * expr)) [(45%nat, 259)] v r2
        [is_length s - cpy] NoVals F0
        (mkst R2 (Z_to_bv 64 0x21158) M2 s6u_rom) R' HR' Hfr Hms.
      all: cbn [r2 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in *; try arm_side.
      all: match goal with |- ?G => idtac "LEFTT2" G end.
      assert (HM3 : LMEM v (mkW s1 (icset_outbuf c ob) (irset_put r1 put')) M2) by exact HM2.
      arm_disp C HM3 Hfr R3 Hms3 G26' Hfr3.
      exists R3, M2, (arm6_pc (is_mode s1)). split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [| exact Hms3]; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split].
      + split; [exact HM3|]. split; [apply (RETC_regs v (mkW s1 c r1)); [exact HRC2 | subst r1; reflexivity]|]. split.
        * apply (LX_step0 v s c r _ _ (irset_put r1 put') HX NH NB); subst s1 r1; try reflexivity; [cbn [is_mode iset_length]; replace (is_mode s) with MATCH by (symmetry; exact Hmode); live_mode_tac | exact Xret | rewrite F11; exact Xmsg | bk_side].
        * unfold LREG_arm, LVARS; cbn [w_r]. subst r1. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_put irset_left].
          split; [| split; [| subst s1; cbn [w_s]; intros Hb; exfalso; replace (is_mode (iset_length s (is_length s - cpy))) with (is_mode s) in Hb by (destruct s; reflexivity); rewrite Hmode in Hb; cbv in Hb; discriminate]].
          -- lfix_close2 Hfr3 Hfr HR'.
          -- regs_via2 Hfr3 Hfr. all: first [rewrite Eput in Q9; exact Q9 | symex_reg HR' (9%bv : reg) as G9'; rewrite G9'; f_equal; clear - Eput; lia | match goal with |- ?G => idtac "T2REG LEFT" G end].
      + subst s1. split; [destruct s; reflexivity | split; destruct s; reflexivity].
      + cbn [w_r]. subst r1. cbn [ir_put irset_put irset_left].
        apply (MFRAME_trans v _ (ir_put r) _ M M1 M2); [| exact HF2].
        subst M1 M0. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End MatchBody.
End FXG.
