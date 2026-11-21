(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflA_Match1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


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


Definition ilMS : cfg := CFG [] [] arm_rets (0x1e8d8 :: arm_stops) [].

Section MatchBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma match_tail : forall s c r R M R1 from cpy,
    is_mode s = MATCH -> 1 <= cpy <= is_length s -> cpy <= ir_left r -> is_length s <= 258 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    arr_len (is_window s) = cv_WN v -> (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256) ->
    ffits v from cpy (ir_put r) ->
    (forall rg, reg_in rg [12; 13; 14; 15; 16]%bv = false -> getr R1 rg = getr R rg) ->
    getr R1 13 = zw (faddr v from) -> getr R1 12 = zw cpy -> getr R1 14 = zw (faddr v from + cpy) ->
    let M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - cpy)) in
    let '(ob, put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy) in
    let s1 := iset_length s (is_length s - cpy) in
    exists R' M' pc',
      msteps s6_segs (mkst R1 (Z_to_bv 64 0x1e8d8) M1 s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M
           (ARun tt (mkW (if is_length s - cpy =? 0 then iset_mode s1 LEN else s1) (icset_outbuf c ob)
                         (irset_put (irset_left r (ir_left r - cpy)) put'))) R' M' pc'.
  Proof.
    intros s c r R M R1 from cpy Hmode Hcpy Hcl Hl258 HM HRC HX HF HV RI CI Hwl Hwb HFF Hfr1 G13 G12 G14. cbv zeta.
    open_ictx C. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    set (s1 := iset_length s (is_length s - cpy)).
    set (M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - cpy))).
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M (cv_S v) _ s _ (lm_sc _ _ _ HM)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW s1 c r) M1) by (subst M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | reflexivity]).
    pose proof (match_loop v C (Z.to_nat cpy) s1 c r R1 M1 from cpy ltac:(apply Z2Nat.id; lia) ltac:(lia) HM1 HRC1
                  Rpt0 ltac:(clear - Hcl Rpl; lia) Col Coutb ltac:(subst s1; exact Hwl) ltac:(subst s1; exact Hwb) HFF
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact P2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact P25)
                  ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact P18) G13 G14) as ML.
    replace (is_window s1) with (is_window s) in ML by (subst s1; destruct s; reflexivity).
    destruct (match_copy (is_window s) (ic_outbuf c, ir_put r, from, cpy)) as [[[ob put'] fr'] c'] eqn:EM.
    destruct ML as (R2 & M2 & Hms2 & HM2 & HRC2 & Q19 & Hfr2 & HF2 & Eput & Hol2 & Hob2).
    pose proof HM2 as HM2'. open_lmem HM2'. unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. cbn [w_s] in C92. replace (is_length s1) with (is_length s - cpy) in C92 by (subst s1; destruct s; reflexivity).
    pose proof (is6_mode _ _ _ _ Msc) as C8. cbn [w_s] in C8. replace (is_mode s1) with MATCH in C8 by (subst s1; rewrite <- Hmode; destruct s; reflexivity).
    pose proof (icset_outbuf_facts c ob) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    set (r2 := mkIR (ir_next r) (ir_have r) put' (ir_left r) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r)).
    assert (Q2 : getr R2 2 = zw (cv_sp v - 224)) by (rewrite (Hfr2 (2%bv : reg) eq_refl), (Hfr1 (2%bv : reg) eq_refl); exact P2).
    assert (Q25 : getr R2 8 = zw (cv_S v)) by (rewrite (Hfr2 (8%bv : reg) eq_refl), (Hfr1 (8%bv : reg) eq_refl); exact P25).
    assert (Q10 : getr R2 10 = zw (cv_ZP v)) by (rewrite (Hfr2 (10%bv : reg) eq_refl), (Hfr1 (10%bv : reg) eq_refl); exact P10).
    assert (Q11 : getr R2 11 = zw (cv_flush v)) by (rewrite (Hfr2 (11%bv : reg) eq_refl), (Hfr1 (11%bv : reg) eq_refl); exact P11).
    assert (Q1 : getr R2 22 = zw (cv_S v + 168)) by (rewrite (Hfr2 (22%bv : reg) eq_refl), (Hfr1 (22%bv : reg) eq_refl); exact P21).
    assert (Q31 : getr R2 31 = zw (-16180)) by (rewrite (Hfr2 (31%bv : reg) eq_refl), (Hfr1 (31%bv : reg) eq_refl); exact P31).
    assert (Q29 : getr R2 29 = zw 30) by (rewrite (Hfr2 (29%bv : reg) eq_refl), (Hfr1 (29%bv : reg) eq_refl); exact P29).
    assert (Q30 : getr R2 25 = zw 0x12510) by (rewrite (Hfr2 (25%bv : reg) eq_refl), (Hfr1 (25%bv : reg) eq_refl); exact P24).
    assert (Q21 : getr R2 20 = zw 16209) by (rewrite (Hfr2 (20%bv : reg) eq_refl), (Hfr1 (20%bv : reg) eq_refl); exact P19).
    assert (Q24 : getr R2 18 = zw (ir_have r)) by (rewrite (Hfr2 (18%bv : reg) eq_refl), (Hfr1 (18%bv : reg) eq_refl); exact P9).
    assert (Q18 : getr R2 1 = zw (ir_left r)) by (rewrite (Hfr2 (1%bv : reg) eq_refl), (Hfr1 (1%bv : reg) eq_refl); exact P1).
    assert (Q23 : getr R2 23 = zw (ir_hold r)) by (rewrite (Hfr2 (23%bv : reg) eq_refl), (Hfr1 (23%bv : reg) eq_refl); exact P22).
    assert (Q8 : getr R2 24 = zw (ir_bits r)) by (rewrite (Hfr2 (24%bv : reg) eq_refl), (Hfr1 (24%bv : reg) eq_refl); exact P23).
    assert (Q26 : getr R2 27 = zw (cv_I0 v + ir_next r)) by (rewrite (Hfr2 (27%bv : reg) eq_refl), (Hfr1 (27%bv : reg) eq_refl); exact P26).
    assert (Q12 : getr R2 12 = zw cpy) by (rewrite (Hfr2 (12%bv : reg) eq_refl); exact G12).
    assert (Q19' : getr R2 19 = zw (cv_P0 v + ir_put r2)) by (subst r2; exact Q19).
    assert (Q3 : getr R2 3 = getr (cv_R0 v) 3) by (rewrite (Hfr2 (3%bv : reg) eq_refl), (Hfr1 (3%bv : reg) eq_refl); exact G3).
    assert (Q4 : getr R2 4 = getr (cv_R0 v) 4) by (rewrite (Hfr2 (4%bv : reg) eq_refl), (Hfr1 (4%bv : reg) eq_refl); exact G4).
    destruct (Z.eqb_spec (is_length s - cpy) 0) as [L0|L0].
    -
      rewrite L0 in C92.
      arm_symexP arm_pins ilS 20%nat [true; true] [RVal (ELit 0); RVal (ELit (JT LEN))] [(12, EVar 45%nat)] [(45%nat, 259)] v r2 [cpy] NoVals F0
        (mkst R2 (Z_to_bv 64 0x1e8f0) M2 s6_rom) R' HR' Hfr Hms.
      all: cbn [r2 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in *; try arm_side.
      all: match goal with |- ?G => idtac "LEFTT1" G end.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in *.
      set (r3 := irset_put (irset_left r (ir_left r - cpy)) put').
      assert (HM3 : LMEM v (mkW (iset_mode s1 LEN) (icset_outbuf c ob) r3) M3).
      { apply (LMEM_regs v (iset_mode s1 LEN) (icset_outbuf c ob) (irset_put r put') _ r3); [| subst r3; reflexivity ..].
        apply (LMEM_store_scalar v C s1 _ _ _ M2 8 _ HM2); [lia | cbn; lia | cbn; clear - Eput Hput Hcl Rpl Hcpy; lia | | subst s1; reflexivity ..].
        apply (is6_upd_mode M2 (cv_S v) _ s1 LEN Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R', M3, (arm6_pc LEN). split; [eapply msteps_trans; [exact Hms2|]; subst M3; by_run Hms|].
      cbn [arm_post]. split; [subst s1; destruct s; reflexivity|]. split; [| split].
      + split; [exact HM3|]. split; [subst M3; apply (RETC_regs v (mkW s c r)); [apply (RETC_other v C); [exact HRC2 | clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia] | subst r3; reflexivity]|]. split.
        * apply (LX_step0 v s c r _ _ r3 HX NH NB); subst s1 r3; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; exact Xmsg].
        * symex_reg HR' (9%bv : reg) as G8'. symex_reg HR' (1%bv : reg) as G1'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r3. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_put irset_left].
          split; [| split; [| intros _; exact G8']].
          -- unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr.
          -- regs_via Hfr. first [rewrite G1'; rewrite ?szwrap32_small by (clear - Hcl Rlf0 Rpl Rpt0 CP0 Hcpy; lia); reflexivity | rewrite Eput in Q19; exact Q19].
             all: first [rewrite Eput in Q19; exact Q19 | rewrite G1'; rewrite ?szwrap32_small by (clear - Hcl Rlf0 Rpl Rpt0 CP0 Hcpy; lia); reflexivity].
      + subst s1. split; [destruct s; reflexivity | split; destruct s; reflexivity].
      + cbn [w_r]. subst M3 r3. cbn [ir_put irset_put irset_left].
        apply (MFRAME_store v (ir_put r) put' put'); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_trans v _ (ir_put r) _ M M1 M2); [| exact HF2].
        subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      assert (HL : 0 < is_length s - cpy < 259) by (clear - L0 Hcpy Hl258; lia).
      replace MATCH with 16204 in C8 by reflexivity.
      arm_symexP arm_pins ilS 20%nat [false; true] [RVal (EVar 46%nat); RVal (ELit 16204); RVal (ELit (JT MATCH))] [(12, EVar 45%nat)] [(45%nat, 259); (46%nat, 259)] v r2
        [cpy; is_length s - cpy] NoVals F0
        (mkst R2 (Z_to_bv 64 0x1e8f0) M2 s6_rom) R' HR' Hfr Hms.
      all: cbn [r2 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in *; try arm_side.
      all: match goal with |- ?G => idtac "LEFTT2" G end.
      set (r3 := irset_put (irset_left r (ir_left r - cpy)) put').
      assert (HM3 : LMEM v (mkW s1 (icset_outbuf c ob) r3) M2) by (apply (LMEM_regs v s1 (icset_outbuf c ob) (irset_put r put') _ r3); [exact HM2 | subst r3; reflexivity ..]).
      exists R', M2, (arm6_pc MATCH). split; [eapply msteps_trans; [exact Hms2|]; by_run Hms|].
      cbn [arm_post]. split; [subst s1; rewrite <- Hmode; destruct s; reflexivity|]. split; [| split].
      + split; [exact HM3|]. split; [apply (RETC_regs v (mkW s c r)); [exact HRC2 | subst r3; reflexivity]|]. split.
        * apply (LX_step0 v s c r _ _ r3 HX NH NB); subst s1 r3; try reflexivity; [cbn [is_mode iset_length]; replace (is_mode s) with MATCH by (symmetry; exact Hmode); live_mode_tac | exact Xret | rewrite F11; exact Xmsg].
        * symex_reg HR' (9%bv : reg) as G8'. symex_reg HR' (1%bv : reg) as G1'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r3. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_put irset_left].
          split; [| split; [| subst s1; cbn [w_s]; intros Hb; exfalso; replace (is_mode (iset_length s (is_length s - cpy))) with (is_mode s) in Hb by (destruct s; reflexivity); rewrite Hmode in Hb; cbv in Hb; discriminate]].
          -- unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr.
          -- regs_via Hfr. all: first [rewrite Eput in Q19; exact Q19 | rewrite G1'; rewrite ?szwrap32_small by (clear - Hcl Rlf0 Rpl Rpt0 CP0 Hcpy; lia); reflexivity].
      + subst s1. split; [destruct s; reflexivity | split; destruct s; reflexivity].
      + cbn [w_r]. subst r3. cbn [ir_put irset_put irset_left].
        apply (MFRAME_trans v _ (ir_put r) _ M M1 M2); [| exact HF2].
        subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End MatchBody.
End FXG.
