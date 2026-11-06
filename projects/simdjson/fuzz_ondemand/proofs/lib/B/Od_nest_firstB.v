(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_nest_plusB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section NestFirst.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Hypothesis HG : od_shb E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).
  Notation nhead_any := (nhead_any E pi).
  Notation nskip_kn := (nskip_kn E pi).

  Lemma skip_child_unf2 : forall st, (2 < o_depth st)%Z ->
    skip_child bs idxs 2 st =
      let c := tokT bs idxs (o_pos st) in
      if is_open c || (c =? C_COLON)%Z || (c =? C_COMMA)%Z then skip_loop bs idxs (Z.to_nat (n - (o_pos st + 1))) 2 (o_adv st 1)
      else if (c =? C_QUOTE)%Z && (tokT bs idxs (o_pos st + 1) =? C_COLON)%Z then skip_loop bs idxs (Z.to_nat (n - (o_pos st + 2))) 2 (o_adv st 2)
      else if (o_depth st - 1 <=? 2)%Z then o_setd (o_adv st 1) (o_depth st - 1)
      else skip_loop bs idxs (Z.to_nat (n - (o_pos st + 1))) 2 (o_setd (o_adv st 1) (o_depth st - 1)).
  Proof.
    intros st H. unfold skip_child, skip_first. replace (o_depth st <=? 2)%Z with false by (symmetry; apply Z.leb_gt; exact H). cbv zeta.
    destruct (is_open (tokT bs idxs (o_pos st)) || (tokT bs idxs (o_pos st) =? C_COLON)%Z || (tokT bs idxs (o_pos st) =? C_COMMA)%Z); [reflexivity|].
    destruct ((tokT bs idxs (o_pos st) =? C_QUOTE)%Z && (tokT bs idxs (o_pos st + 1) =? C_COLON)%Z); [reflexivity|].
    destruct (o_depth st - 1 <=? 2)%Z; reflexivity.
  Qed.

  Notation NSTe E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs4 xs5 xt3 xt5 xt6 xF xfc m :=
    (NSTb E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 ((oa_F E + 208) / 8)) xa5 xa6 xa7
          (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
          xs4 xs5 (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m).

  Lemma bn_skip_from : forall (Q : machine_state -> Prop) st0 st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs4 xs5 xt3 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st1 -> (pi < o_pos st1)%Z -> frm0 xfc -> NODp E pi st1 m1 ->
    skip_child bs idxs 2 st0 = skip_loop bs idxs (Z.to_nat (n - o_pos st1)) 2 st1 ->
    nskip_kn Q (fun st' => st' = skip_child bs idxs 2 st0 /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_child bs idxs 2 st0 /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (NSTe E 0x99fd4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs4 xs5 xt3 xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q st0 st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs4 xs5 xt3 xt5 xt6 xF xfc m1 SK HPP FRM INV EQ KN KE.
    pose proof SK as (HP & HD & HE & HA & HB).
    pose proof INV as INV0. nod_open INV. od_env OK.

    ostep. ostep. ostep. if_true.
    eapply evt_eq; [| eapply (bn_skip_loop E OK HLAST pi HPI HG Q (Z.to_nat (n - o_pos st1)) st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK HPP ltac:(lia) FRM INV0)].
    - od_st_eq.
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
  Qed.

  Lemma bn_skip_first : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa1 xa2 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1,
    od_plus_ok bs idxs 2 st -> (2 < o_depth st)%Z -> (pi < o_pos st)%Z -> frm0 xfc -> NODp E pi st m1 ->
    nskip_kn Q (fun st' => st' = skip_child bs idxs 2 st /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_child bs idxs 2 st /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (NSTp E 0x99e3c xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa1 xa2 (Z_to_bv 64 (o_depth st)) (Z_to_bv 64 ((oa_F E + 208) / 8)) xa5 xa6 xa7
                      xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q st xra xt0 xt1 xt2 xa1 xa2 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1 PO HDG HPP FRM INV KN KE.
    pose proof PO as (HP & HPD & HD & HE & HA & HB). specialize (HPD HDG).
    od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR1.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR1.
    pose proof (skip_child_unf2 st HDG) as UNF. cbv zeta in UNF.
    unfold is_open, C_LBRACKET, C_LBRACE, C_COLON, C_COMMA, C_QUOTE in UNF.
    set (c := tokT bs idxs (o_pos st)) in *. set (c1 := tokT bs idxs (o_pos st + 1)) in *.

    assert (K_L1 : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = true ->
              forall yra ya0 ya2 ya5 ya6 ya7 mm, NODp E pi (o_adv st 1) mm ->
              evt bsegs Q (NSTe E 0x99f1c yra xt0 xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 (Z_to_bv 64 (o_depth st)) ya5 ya6 ya7 xs4 xs5 xt3 xt5 xt6 xF xfc mm)).
    { intros CC yra ya0 ya2 ya5 ya6 ya7 mm INV2. rewrite CC in UNF.
      pose proof (od_skip_ok_first bs idxs S1 2 st (o_depth st) PO HDG ltac:(lia)) as SK2.
      ostep. gok.
      eapply (bn_skip_from Q st (o_adv st 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 ltac:(cbn [o_adv o_pos]; lia) FRM INV2); [exact UNF| exact KN| exact KE]. }

    assert (K_DEC0 : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall yra ya0 ya1 ya2 ya5 ya6 ya7 mm, NODp E pi (o_setd (o_adv st 1) (o_depth st - 1)) mm ->
              evt bsegs Q (NSTe E 0x99fd0 yra xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 (o_depth st - 1)) ya5 ya6 ya7 xs4 xs5 xt3 xt5 xt6 xF xfc mm)).
    { intros CC CQ yra ya0 ya1 ya2 ya5 ya6 ya7 mm INV2. rewrite CC, CQ in UNF.
      ostep.
      if_cases KD; zify_cond KD; odsig KD.
      - replace (o_depth st - 1 <=? 2)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
        eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1)))]; [od_st_eq| split; [symmetry; exact UNF| exact HE]| exact FRM| exact INV2].
      - replace (o_depth st - 1 <=? 2)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
        pose proof (od_skip_ok_first bs idxs S1 2 st (o_depth st - 1) PO HDG ltac:(lia)) as SK2.
        eapply evt_eq; [| eapply (bn_skip_from Q st (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 ltac:(cbn [o_setd o_adv o_pos]; lia) FRM INV2); [exact UNF| exact KN| exact KE]].
        od_st_eq. }

    assert (K_DEC : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall pc0 yra ya0 ya2 ya5 ya6 ya7 mm, (pc0 = 0x99fb8 \/ pc0 = 0x99f24)%Z -> NODp E pi (o_adv st 1) mm ->
              evt bsegs Q (NSTe E pc0 yra xt0 xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 (Z_to_bv 64 (o_depth st)) ya5 ya6 ya7 xs4 xs5 xt3 xt5 xt6 xF xfc mm)).
    { intros CC CQ pc0 yra ya0 ya2 ya5 ya6 ya7 mm HPC INV2.

      pose proof (K_DEC0 CC CQ) as KD0. clear CC CQ K_DEC0 K_L1 UNF.
      nod_open INV2.
      destruct HPC as [-> | ->].
      - ostep. gok. ostep. ostep. if_false. ostep. odnorm. ostep.
        eapply evt_eq; [| eapply KD0; nod_close]. od_st_eq.
      - ostep. gok. ostep. ostep. if_true. ostep. odnorm. ostep.
        eapply evt_eq; [| eapply KD0; nod_close]. od_st_eq. }
    clear K_DEC0.
    nod_open INV.

    ostep. ostep. ostep. ostep. if_true. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep. ual. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2. fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
    replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
    set (off := tokI bs idxs (o_pos st)) in *. set (off1 := tokI bs idxs (o_pos st + 1)) in *.
    od_cur_mem ltac:(fun mm => assert (INVA : NODp E pi (o_adv st 1) mm) by nod_close).

    ostep. gok. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep. unz. ostep. gok. ostep. gok.
    ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      ostep. ostep. if_cases K1; zify_cond K1.
      +
        ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep.
        if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c1 58)) by lia; apply andb_false_r) 0x99fb8%Z); [left; reflexivity| exact INVA]].
          od_st_eq.
        *
          replace ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z with false in UNF by (rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
          replace ((c =? 34) && (c1 =? 58))%Z with true in UNF by (rewrite (proj2 (Z.eqb_eq c 34)), (proj2 (Z.eqb_eq c1 58)) by lia; reflexivity).
          pose proof (od_skip_ok_key bs idxs S1 HLAST 2 st PO HDG ltac:(unfold C_COLON; fold c1; lia)) as SK2.
          ostep. gok. ostep. gok. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep. ostep.
          eapply evt_eq; [| eapply (bn_skip_from Q st (o_adv st 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 ltac:(cbn [o_adv o_pos]; lia) FRM); [| exact UNF| exact KN| exact KE]];
            [od_st_eq| nod_close].
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_L1 ltac:(rewrite (proj2 (Z.eqb_eq c 44)) by lia; rewrite !orb_true_r; reflexivity)); exact INVA]. od_st_eq.
        *
          ostep. ostep. if_cases K3; zify_cond K3.
          --
             eapply evt_eq; [| eapply (K_L1 ltac:(rewrite (proj2 (Z.eqb_eq c 58)) by lia; rewrite !orb_true_r; reflexivity)); exact INVA]. od_st_eq.
          -- ostep.
             eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity) 0x99fb8%Z); [left; reflexivity| exact INVA]].
             od_st_eq.
    -
      ostep. ostep. if_cases K1; zify_cond K1; odsig K1.
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity) 0x99f24%Z); [right; reflexivity| exact INVA]].
          od_st_eq.
        * ostep. ostep. if_cases K3; zify_cond K3.
          -- eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity) 0x99fb8%Z); [left; reflexivity| exact INVA]].
             od_st_eq.
          --
             eapply evt_eq; [| eapply (K_L1 ltac:(rewrite (proj2 (Z.eqb_eq c 123)) by lia; rewrite !orb_true_r; reflexivity)); exact INVA]. od_st_eq.
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_L1 ltac:(rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity)); exact INVA]. od_st_eq.
        * ostep. ostep. if_cases K3; zify_cond K3.
          -- eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity) 0x99fb8%Z); [left; reflexivity| exact INVA]].
             od_st_eq.
          --
             ostep.
             eapply evt_eq; [| eapply (K_DEC ltac:(rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity) ltac:(rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity) 0x99f24%Z); [right; reflexivity| exact INVA]].
             od_st_eq.
  Qed.

  Lemma bn_plus : forall (Q : machine_state -> Prop) st1 j272 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1,
    od_plus_ok bs idxs 2 st1 -> (pi < o_pos st1)%Z -> frm0 xfc ->
    NODb E pi (CB 8 j272) (C8 (wz ((oa_F E + 224) / 8 + 2147450880))) st1 m1 ->
    nhead_any Q (fun st' => od_next_ok bs idxs 2 st1 st') ->
    evt bsegs Q (NSTb E 0x99dd0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 ((oa_F E + 208) / 8)) xa5 xa6 xa7
                      (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) xs3 xs4 xs5 xs8 (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q st1 j272 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1 PO HPP FRM INV HK.
    od_env OK.
    pose proof PO as (HP & HPD & HD & HE & HA & HB).
    pose proof (od_plus_spec bs idxs S1 HLAST 2 st1 ltac:(lia) PO) as NEXT.

    assert (K_HN : nskip_kn Q (fun s1 => s1 = skip_child bs idxs 2 st1 /\ o_err s1 = 0%Z)).
    { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
      pose proof (skip_child_ok bs idxs S1 HLAST 2 st1 PO) as (S1a & S2 & S3 & S4 & S5 & S6). rewrite <- E1 in *.
      destruct S6 as [(_ & D1)|(E3 & _)]; [| rewrite E2 in E3; unfold TAPE_ERROR in E3; lia].
      assert (P1 : (pi < o_pos s1 <= n)%Z) by lia.
      eapply (bn_hasnext E OK pi HPI Q s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' I' F' P1 E2 D1 S2).
      intros s2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 E2' F2 I2.
      apply (HK s2); [| exact F2| exact I2].
      unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb] in NEXT. rewrite <- E2' in NEXT. exact NEXT. }
    assert (K_ER : nhead_any Q (fun s1 => s1 = skip_child bs idxs 2 st1 /\ o_err s1 = TAPE_ERROR)).
    { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
      apply (HK s1); [| exact F'| exact I'].
      unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb TAPE_ERROR] in NEXT. exact NEXT. }
    clear NEXT.
    nod_open INV.

    ostep. ostep. ostep. if_false. ostep. ostep. odnorm. ostep. ostep. gok. ostep. ostep.
    if_cases KE0; zify_cond KE0; [exfalso; lia|]. clear KE0.

    ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. gok. ostep. ostep. if_false. ostep. odnorm. ostep. goks. ostep. ostep. ostep.
    od_cur_mem ltac:(fun mm => assert (INVA : NODp E pi st1 mm) by nod_close).
    if_cases KD; zify_cond KD; odsig KD.
    -
      assert (SC : skip_child bs idxs 2 st1 = st1) by (unfold skip_child; replace (o_depth st1 <=? 2)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity).
      eapply evt_eq; [| eapply (K_HN st1); [split; [symmetry; exact SC| exact HE]| exact FRM| exact INVA]].
      od_st_eq.
    - eapply evt_eq; [| eapply (bn_skip_first Q st1); [exact PO| lia| exact HPP| exact FRM| exact INVA| exact K_HN| exact K_ER]].
      od_st_eq.
  Qed.
End NestFirst.
