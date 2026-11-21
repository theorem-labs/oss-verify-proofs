(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_CODELENS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeOK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeTY2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT1spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeIT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [inflate_table lenlens_while1 lenlens_while2 ll2 codelens_while codelens_body NEEDBITS_k DECODE_k].


Lemma ll_post_ok_intro : forall tbl next lenbits work,
  arr_len tbl = 1444 -> arr_len work = 288 -> 0 <= next <= 1444 -> 0 <= lenbits < 2 ^ 32 ->
  ty32 tbl -> ty16 work -> ll_post_ok tbl next lenbits work = true.
Proof.
  intros tbl next lenbits work L1 L2 Hn Hb T1 T2. unfold ll_post_ok.
  rewrite L1, L2, !Z.eqb_refl. rewrite (proj2 (Z.leb_le 0 next)) by lia. rewrite (proj2 (Z.leb_le next 1444)) by lia.
  rewrite (proj2 (Z.leb_le 0 lenbits)) by lia. rewrite (proj2 (Z.ltb_lt lenbits (2 ^ 32))) by lia. cbn [andb].
  rewrite (proj2 (forallb_forall _ _)).
  2:{ intros k _. cbv beta. pose proof (T1 (Z.of_nat k)) as X. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite (proj2 (forallb_forall _ _)).
  2:{ intros k _. cbv beta. pose proof (T2 (Z.of_nat k)) as X. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  reflexivity.
Qed.

Lemma lens15b_intro : forall lens lo hi, (forall i, lo <= i < hi -> arr_get lens i <= 15) -> lens15b lens lo hi = true.
Proof.
  intros lens lo hi H. unfold lens15b. apply (proj2 (forallb_forall _ _)). intros k _. cbv beta zeta.
  destruct (Z.ltb_spec (Z.of_nat k) lo); [reflexivity|]. destruct (Z.leb_spec hi (Z.of_nat k)); [reflexivity|]. cbn [orb].
  apply Z.leb_le. apply H. lia.
Qed.

Lemma inflate_table_fail : forall ty lens lens_ofs codes tbl table bits work,
  let '(ret, tbl', toff, bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  ret <> 0 -> toff = table /\ bits' = bits.
Proof.
  intros ty lens lens_ofs codes tbl table bits work. unfold inflate_table. cbv zeta.
  destruct (it_find_max _ =? 0); [intros X; exfalso; exact (X eq_refl)|].
  destruct (it_left_check _) as [lft|]; [|intros _; split; reflexivity].
  destruct ((0 <? lft) && _); [intros _; split; reflexivity|].
  destruct (it_sort lens lens_ofs codes _) as [offs' work1].
  destruct (it_not_enough _ _); [intros _; split; reflexivity|].
  destruct (it_loop _ _ _) as [st'|st']; [intros X; exfalso; exact (X eq_refl) | intros _; split; reflexivity].
Qed.

Lemma decode_okb_one : forall two ty s c r p root used,
  TBLg ty (code_at s p) root used -> used <= ctab_size p -> REGS c r ->
  (forall op, two op = false) ->
  decode_okb two s c r p root = true.
Proof.
  intros two ty s c r p root used HT HU HR Htwo.
  pose proof (T_root _ _ _ _ HT) as R15. pose proof (T_used _ _ _ _ HT) as RU.
  pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb Bh] & _).
  unfold decode_okb. cbv zeta.
  rewrite (proj2 (Z.leb_le 0 root)) by lia. rewrite (proj2 (Z.leb_le root 15)) by lia. cbn [andb].
  assert (I1 : forall h, 0 <= h -> 0 <= dec_idx1 root h < ctab_size p).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)). lia. }
  assert (N1 : forall h, 0 <= h -> 1 <= code_bits (code_at s p (dec_idx1 root h)) <= 15).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)).
    exact (proj1 (root_cell _ _ _ _ HT (BITSv h root) ltac:(lia))). }
  destruct (dchk_ok c 8 (dec_idx1 root) code_bits (ctab_size p) (code_at s p) r HR I1 N1 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
    as (r1 & E1 & HR1). rewrite E1.
  rewrite Htwo. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma ll2_eq : forall k s c r s2,
  lenlens_while2 k (mkW s c r) = ARun tt (mkW s2 c r) -> ll2 k s = s2.
Proof.
  intros k s c r s2 E. rewrite lenlens_while2_run in E.
  apply (f_equal (fun x => match x with ARun _ w => w_s w | _ => s end)) in E. cbn [w_s] in E. exact E.
Qed.


Section Lenlens.
  Variable s : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HW : WINV (mkW s c r).
  Hypothesis HA : ATY s.
  Hypothesis E : is_mode s = LENLENS.

  Lemma lenlens_facts :
    is_ncode s <= 19 /\
    match lenlens_while1 19 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) =>
        c1 = c /\
        exists lens19,
          ll2 19 s1 = iset_have (iset_lens s1 lens19) 19 /\ arr_len lens19 = 320
          /\ (forall i, 0 <= i < 19 -> 0 <= arr_get lens19 i <= 7) /\ ty16 lens19
          /\ CORE s1 /\ REGS c r1 /\ common s1 /\ ir_bits r1 < 8
          /\ 257 <= is_nlen s1 <= 286 /\ 1 <= is_ndist s1 <= 30
          /\ ir_out r1 = arr_len (ic_outbuf c) /\ (is_wbits s1 = 0 -> ir_put r1 = 0)
          /\ ATY s1
    | _ => True
    end.
  Proof.
    pose proof HW as HW0. winv_open2 HW0 E HC HR.
    destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
    split; [lia|].
    assert (HLL : LL s c r) by (unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    pose proof (lenlens_while1_spec c 19 s r HLL ltac:(cbn; lia)) as W1.
    pose proof (lenlens_while1_aty 19 (mkW s c r) HA) as A1.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact I|exact I].
    unfold ATYr, wof in A1. cbn [w_s] in A1.
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & P1 & Ep1 & Q1 & Ecd & Ewk).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    split; [reflexivity|].
    destruct (lenlens_while2_spec c 19 s1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    pose proof (lenlens_while2_aty 19 (mkW s1 c r1) A1) as A2. rewrite EQ2 in A2. unfold ATYr, wof in A2. cbn [w_s] in A2.
    exists lens19. split; [exact (ll2_eq _ _ _ _ _ EQ2)|]. split; [exact HL19|].
    split; [intros i Hi; destruct (order_a_onto i Hi) as [j [Hj <-]]; apply HLs19; exact Hj|].
    split; [exact (proj1 A2)|].
    repeat (split; [first [assumption | lia]|]). exact A1.
  Qed.

  Theorem WINV_lenlens_okb : lenlens_okb (mkW s c r) = true.
  Proof.
    pose proof lenlens_facts as F. unfold lenlens_okb. cbn [w_s].
    destruct F as [Hnc F]. rewrite (proj2 (Z.leb_le _ _) Hnc). cbn [andb].
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity].
    destruct F as (-> & lens19 & EL2 & HL19 & HLs & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
    rewrite EL2. unfold ll_call_ok. sacc.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    rewrite (proj2 (forallb_forall _ _)).
    2:{ intros k Hk. cbv beta. apply in_seq in Hk. apply Z.leb_le. pose proof (HLs (Z.of_nat k) ltac:(lia)). lia. }
    rewrite (it_safe_intro CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
               ltac:(lia) ltac:(rewrite CB2; lia) ltac:(rewrite CB2; lia) ltac:(lia) ltac:(rewrite HL19; lia)
               ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    pose proof (inflate_table_typed CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    pose proof (inflate_table_fail CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as TF.
    destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
    destruct TC as [[TC5 TC6] TC]. destruct TT as [TT1 TT2]. cbn [it_room] in TC. cbv beta iota.
    apply ll_post_ok_intro; [rewrite TC5, CB3; reflexivity | rewrite TC6, CB2; reflexivity | | | exact TT1 | exact TT2].
    - destruct (Z.eq_dec ret 0) as [R0|R0]; [destruct (TC R0) as (_ & X & _); pose proof (pow2_pos lb ltac:(lia)); lia | destruct (TF R0) as [-> _]; lia].
    - destruct (Z.eq_dec ret 0) as [R0|R0]; [destruct (TC R0) as (X & _); lia | destruct (TF R0) as [_ ->]; lia].
  Qed.

  Theorem lenlens_next_WINV : forall w2, lenlens_next (mkW s c r) = Some w2 ->
    WINV w2 /\ ATY (w_s w2) /\ is_mode (w_s w2) = CODELENS.
  Proof.
    intros w2 HN. pose proof lenlens_facts as [Hnc F]. unfold lenlens_next in HN.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
    destruct F as (-> & lens19 & EL2 & HL19 & HLs & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
    cbv zeta in HN. rewrite EL2 in HN. sacc_in HN.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    pose proof (inflate_table_typed CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
    destruct TC as [[TC5 TC6] TC]. destruct TT as [TT1 TT2]. cbn [it_room] in TC.
    destruct (Z.eqb_spec ret 0) as [R0|R0]; [|discriminate HN].
    specialize (TC R0). destruct TC as (TC1 & TC2 & TC3 & TC4).
    apply some_inj in HN. subst w2. unfold ll_s2, ll_tab. cbn [w_s].
    split; [|split].
    - winv_split.
      + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [left; exact Hb1|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros i Hi; exfalso; lia|].
        cbn [cpok]. split; [lia|]. exists (nxt - 0). split; [lia|]. exact TC3.
      + exact HWF1.
      + exact HWB1.
    - unfold ATY. sacc. split; [exact HT19|]. split; [exact TT2|exact TT1].
    - sacc. reflexivity.
  Qed.
End Lenlens.


Section Codelens.
  Variable c : icall.

  Lemma clw_chk_CL : forall k s r, CL s c r -> clw_chk k s c r = true.
  Proof.
    induction k as [|k IH]; intros s r HCL; [reflexivity|].
    cbn [clw_chk]. destruct (Z.ltb_spec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE]; [|reflexivity].
    pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & HU).
    rewrite (decode_okb_one cl_two CODES s c r (is_lencode s) (is_lenbits s) used HTg).
    2:{ destruct (is_lencode s) as [ofs| |]; cbn [ctab_size]; lia. }
    2:{ exact HR. }
    2:{ intros op. reflexivity. }
    cbn [andb].
    pose proof (codelens_body_spec c s r HCL LT) as B.
    destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity|reflexivity].
    destruct B as (-> & HCL1 & _). apply IH. exact HCL1.
  Qed.
End Codelens.

Section Codelens2.
  Variable flush : Z.
Variable s : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HW : WINV (mkW s c r).
  Hypothesis HA : ATY s.
  Hypothesis E : is_mode s = CODELENS.

  Lemma codelens_facts :
    CL s c r /\ is_have s < is_nlen s + is_ndist s /\
    match codelens_while 321 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) =>
        is_mode s1 = BAD
        \/ (c1 = c /\ CL s1 c r1 /\ is_have s1 = is_nlen s1 + is_ndist s1 /\ ir_bits r1 < 8 /\ ATY s1)
    | _ => True
    end.
  Proof.
    pose proof HW as HW0. winv_open2 HW0 E HC HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    assert (HCL : CL s c r) by (unfold CL; repeat (split; [first [assumption | lia]|]); exact HWB).
    split; [exact HCL|]. split; [lia|].
    pose proof (codelens_while_spec c 321 s r HCL ltac:(cbn; lia)) as W.
    pose proof (codelens_while_aty 321 (mkW s c r) HA) as A1.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact I|exact I].
    unfold ATYr, wof in A1. cbn [w_s] in A1.
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & P1 & Ep1 & Q1 & _)|(Hm1 & _)].
    - right. destruct (Q1 ltac:(lia)) as [_ Hb1]. split; [reflexivity|]. split; [exact HCL1|]. split; [exact Hh1|]. split; [exact Hb1|exact A1].
    - left. exact Hm1.
  Qed.

  Theorem WINV_codelens_okb : codelens_okb (mkW s c r) = true.
  Proof.
    pose proof codelens_facts as (HCL & Hlt & F). unfold codelens_okb. cbn [w_s w_c w_r].
    pose proof HCL as (_ & _ & _ & _ & _ & Hnl & Hnd & _).
    rewrite (proj2 (Z.leb_le _ 320)) by lia. rewrite (clw_chk_CL c 321 s r HCL). cbn [andb].
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity].
    destruct F as [Hm1 | (-> & HCL1 & Hh1 & Hb1 & HA1)]; [rewrite Hm1; reflexivity|].
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    rewrite E1. change (CODELENS =? BAD) with false. cbv iota.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    unfold cl_post_ok. destruct (arr_get (is_lens s1) 256 =? 0); [reflexivity|].
    rewrite (lens15b_intro (is_lens s1) 0 (is_nlen s1)) by (intros i Hi; pose proof (HLs1 i ltac:(lia)); lia).
    rewrite (it_safe_intro LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
               ltac:(lia) ltac:(rewrite CB2; lia) ltac:(rewrite CB2; lia) ltac:(lia) ltac:(rewrite CB1; lia)
               ltac:(intros i Hi; apply HLs1; lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    pose proof (inflate_table_typed LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    pose proof (inflate_table_fail LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as TF.
    destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[retL tblL] nextL] lenbitsL] workL].
    destruct TL as [[TL5 TL6] TL]. destruct TT as [TT1 TT2]. cbn [it_room] in TL. unfold ENOUGH_LENS in TL. cbv beta iota.
    rewrite (ll_post_ok_intro tblL nextL lenbitsL workL ltac:(rewrite TL5, CB3; reflexivity) ltac:(rewrite TL6, CB2; reflexivity)
               ltac:(destruct (Z.eq_dec retL 0) as [R0|R0]; [destruct (TL R0) as (_ & X & _); pose proof (pow2_pos lenbitsL ltac:(lia)); lia | destruct (TF R0) as [-> _]; lia])
               ltac:(destruct (Z.eq_dec retL 0) as [R0|R0]; [destruct (TL R0) as (X & _); lia | destruct (TF R0) as [_ ->]; lia])
               TT1 TT2).
    cbn [andb].
    destruct (Z.eqb_spec retL 0) as [RL0|RL0]; [|reflexivity].
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). pose proof (pow2_pos lenbitsL ltac:(lia)) as PL.
    unfold cl_tab1. sacc.
    rewrite (lens15b_intro (is_lens s1) (is_nlen s1) (is_nlen s1 + is_ndist s1)) by (intros i Hi; pose proof (HLs1 i ltac:(lia)); lia).
    rewrite (it_safe_intro DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
               ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(rewrite TL6, CB2; lia) ltac:(lia) ltac:(rewrite CB1; lia)
               ltac:(intros i Hi; apply HLs1; lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    pose proof (inflate_table_typed DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL TT1 TT2) as TTD.
    pose proof (inflate_table_fail DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as TFD.
    destruct (inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as [[[[retD tblD] nextD] distbitsD] workD].
    destruct TD as [[TD5 TD6] TD]. destruct TTD as [TTD1 TTD2]. cbn [it_room] in TD. unfold ENOUGH_DISTS in TD. cbv beta iota.
    apply ll_post_ok_intro; [rewrite TD5, TL5, CB3; reflexivity | rewrite TD6, TL6, CB2; reflexivity | | | exact TTD1 | exact TTD2].
    - destruct (Z.eq_dec retD 0) as [R0|R0]; [destruct (TD R0) as (_ & X & _); pose proof (pow2_pos distbitsD ltac:(lia)); lia | destruct (TFD R0) as [-> _]; lia].
    - destruct (Z.eq_dec retD 0) as [R0|R0]; [destruct (TD R0) as (X & _); lia | destruct (TFD R0) as [_ ->]; lia].
  Qed.

  Theorem codelens_next_WINV : forall w2, codelens_next flush (mkW s c r) = Some w2 ->
    WINV w2 /\ is_mode (w_s w2) = LEN_.
  Proof.
    intros w2 HN. pose proof codelens_facts as (HCL & Hlt & F). rewrite codelens_next_eq in HN.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
    destruct F as [Hm1 | (-> & HCL1 & Hh1 & Hb1 & HA1)]; [rewrite Hm1 in HN; discriminate HN|].
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    rewrite E1 in HN. change (CODELENS =? BAD) with false in HN. cbv iota in HN.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    unfold cl_post_next in HN. destruct (arr_get (is_lens s1) 256 =? 0); [discriminate HN|].
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[retL tblL] nextL] lenbitsL] workL].
    destruct TL as [[TL5 TL6] TL].
    destruct (Z.eqb_spec retL 0) as [RL0|RL0]; cbn [negb] in HN; [|discriminate HN].
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    cbv zeta in HN. unfold cl_tab1 in HN. sacc_in HN.
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    destruct (inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as [[[[retD tblD] nextD] distbitsD] workD].
    destruct TD as [[TD5 TD6] TD].
    destruct (Z.eqb_spec retD 0) as [RD0|RD0]; cbn [negb] in HN; [|discriminate HN].
    destruct (flush =? Z_TREES); [discriminate HN|].
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    apply some_inj in HN. subst w2. unfold cl_tab2. cbn [w_s]. split.
    - winv_split.
      + core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [exact Hb1|]. unfold tables. sacc. split.
        * cbn [cpok]. split; [lia|]. exists (nextL - 0). split; [lia|].
          apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        * cbn [cpok]. split; [lia|]. exists (nextD - nextL). split; [lia|]. exact TD3.
      + exact HWF1.
      + exact HWB1.
    - sacc. reflexivity.
  Qed.
End Codelens2.


Theorem WINV_codelens_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = CODELENS ->
  codelens_chain flush w = true.
Proof.
  intros flush [s c r] HW HA E. cbn [w_s] in HA, E. unfold codelens_chain.
  rewrite (WINV_codelens_okb s c r HW HA E).
  destruct (codelens_next flush (mkW s c r)) as [w2|] eqn:HN; [|reflexivity].
  destruct (codelens_next_WINV flush s c r HW HA E w2 HN) as [HW2 E2]. exact (WINV_len__chain w2 HW2 E2).
Qed.

Theorem WINV_lenlens_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = LENLENS ->
  lenlens_chain flush w = true.
Proof.
  intros flush [s c r] HW HA E. cbn [w_s] in HA, E. unfold lenlens_chain.
  rewrite (WINV_lenlens_okb s c r HW HA E).
  destruct (lenlens_next (mkW s c r)) as [w2|] eqn:HN; [|reflexivity].
  destruct (lenlens_next_WINV s c r HW HA E w2 HN) as (HW2 & HA2 & E2). exact (WINV_codelens_chain flush w2 HW2 HA2 E2).
Qed.

Lemma table_next_ATY : forall w w2, ATY (w_s w) -> table_next w = Some w2 -> ATY (w_s w2).
Proof.
  intros w w2 HA HN. unfold table_next in HN.
  pose proof (NEEDBITS_aty 14 w HA) as A1.
  destruct (NEEDBITS 14 w) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
  unfold ATYr, wof in A1. cbn [w_s] in A1.
  destruct (_ || _); [discriminate HN|]. apply some_inj in HN. subst w2. unfold tb_s2, tb_s. cbn [w_s].
  apply (ATY_same s1 _ A1); reflexivity.
Qed.

Theorem WINV_table_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = TABLE ->
  table_chain flush w = true.
Proof.
  intros flush w HW HA E. unfold table_chain.
  destruct (table_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (table_next_WINV w w2 HW E HN) as [HW2 E2].
  exact (WINV_lenlens_chain flush w2 HW2 (table_next_ATY w w2 HA HN) E2).
Qed.


Theorem okL_WINV : forall flush w, WINV w -> ATY (w_s w) -> RefInflateArms.okL flush w = true.
Proof.
  intros flush w HW HA. unfold RefInflateArms.okL. cbv zeta.
  destruct (Z.eqb_spec (is_mode (w_s w)) DICT) as [E1|N1]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) MEM) as [E2|N2]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) SYNC) as [E3|N3]; [reflexivity|]. cbn [orb].
  rewrite (WINV_leave_okb w HW N1 N2). cbn [andb].
  destruct (Z.eqb_spec (is_mode (w_s w)) DISTEXT) as [E4|N4]; [exact (WINV_distext_chain w HW E4)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) DIST) as [E5|N5]; [exact (WINV_dist_chain w HW E5)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LENEXT) as [E6|N6]; [exact (WINV_lenext_chain w HW E6)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) MATCH) as [E7|N7]; [exact (WINV_match_okb w HW E7)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LEN) as [E8|N8]; [exact (WINV_len_chain w HW E8)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LEN_) as [E9|N9]; [exact (WINV_len__chain w HW E9)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) TABLE) as [E10|N10]; [exact (WINV_table_chain flush w HW HA E10)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LENLENS) as [E11|N11]; [exact (WINV_lenlens_chain flush w HW HA E11)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) CODELENS) as [E12|N12]; [exact (WINV_codelens_chain flush w HW HA E12)|].
  reflexivity.
Qed.


