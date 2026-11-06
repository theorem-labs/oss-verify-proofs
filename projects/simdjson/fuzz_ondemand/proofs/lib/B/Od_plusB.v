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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Sj_akit Od_defsB Od_pluslB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section Plus2.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HG : od_shb E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).
  Notation head_any := (Od_pluslB.head_any E).
  Notation skip_kn := (Od_pluslB.skip_kn E).

  Notation FST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xt3 xt4 xt5 xt6 xF xfc m :=
    (PST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 228))
         xt3 xt4 xt5 xt6 xF xfc m).

  Lemma skip_child_unf : forall st, (1 < o_depth st)%Z ->
    skip_child bs idxs 1 st =
      let c := tokT bs idxs (o_pos st) in
      if is_open c || (c =? C_COLON)%Z || (c =? C_COMMA)%Z then skip_loop bs idxs (Z.to_nat (n - (o_pos st + 1))) 1 (o_adv st 1)
      else if (c =? C_QUOTE)%Z && (tokT bs idxs (o_pos st + 1) =? C_COLON)%Z then skip_loop bs idxs (Z.to_nat (n - (o_pos st + 2))) 1 (o_adv st 2)
      else if (o_depth st - 1 <=? 1)%Z then o_setd (o_adv st 1) (o_depth st - 1)
      else skip_loop bs idxs (Z.to_nat (n - (o_pos st + 1))) 1 (o_setd (o_adv st 1) (o_depth st - 1)).
  Proof.
    intros st H. unfold skip_child, skip_first. replace (o_depth st <=? 1)%Z with false by (symmetry; apply Z.leb_gt; exact H). cbv zeta.
    destruct (is_open (tokT bs idxs (o_pos st)) || (tokT bs idxs (o_pos st) =? C_COLON)%Z || (tokT bs idxs (o_pos st) =? C_COMMA)%Z); [reflexivity|].
    destruct ((tokT bs idxs (o_pos st) =? C_QUOTE)%Z && (tokT bs idxs (o_pos st + 1) =? C_COLON)%Z); [reflexivity|].
    destruct (o_depth st - 1 <=? 1)%Z; reflexivity.
  Qed.

  Lemma od_skip_from : forall (Q : machine_state -> Prop) st0 st1 v352 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 1 st1 -> frm0 xfc -> ODINVp E v352 st1 m1 ->
    skip_child bs idxs 1 st0 = skip_loop bs idxs (Z.to_nat (n - o_pos st1)) 1 st1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (FST E 0x9a804 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HG HLAST.
    intros Q st0 st1 v352 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xt3 xt4 xt5 xt6 xF xfc m1 SK FRM INV EQ KN KE.
    pose proof SK as (HP & HD & HE & HA & HB).
    pose proof INV as INV0. od_open_inv INV. od_env OK.

    ostep. ostep. ostep. ostep. ostep. if_true.
    eapply evt_eq; [| eapply (od_skip_loop E OK HG HLAST Q (Z.to_nat (n - o_pos st1)) st1 v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK ltac:(lia) FRM INV0)].
    - od_st_eq.
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. eapply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. eapply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
  Qed.

  Lemma od_skip_first : forall (Q : machine_state -> Prop) st v352 xra xt1 xt2 xa1 xa2 xa4 xa5 xa6 xs4 xs6 xt3 xt4 xt5 xt6 xF xfc m1,
    od_plus_ok bs idxs 1 st -> (1 < o_depth st)%Z -> frm0 xfc -> ODINVp E v352 st m1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (PST E 0x9a664 xra xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa1 xa2 (Z_to_bv 64 (o_depth st)) xa4 xa5 xa6
                     xs4 xs6 (Z_to_bv 64 (oa_F E + 228)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HG HLAST.
    intros Q st v352 xra xt1 xt2 xa1 xa2 xa4 xa5 xa6 xs4 xs6 xt3 xt4 xt5 xt6 xF xfc m1 PO HDG FRM INV KN KE.
    pose proof PO as (HP & HPD & HD & HE & HA & HB). specialize (HPD HDG).
    od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR1.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR1.
    pose proof (skip_child_unf st HDG) as UNF. cbv zeta in UNF.
    unfold is_open, C_LBRACKET, C_LBRACE, C_COLON, C_COMMA, C_QUOTE in UNF.
    set (c := tokT bs idxs (o_pos st)) in *. set (c1 := tokT bs idxs (o_pos st + 1)) in *.

    assert (K_L1 : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = true ->
              forall ya0 ya2 ya3 ya4 ya5 ya6 mm, ODINVp E v352 (o_adv st 1) mm ->
              evt bsegs Q (FST E 0x9a744 xra xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 ya5 ya6 xs4
                               xt3 xt4 xt5 xt6 xF xfc mm)).
    { intros CC ya0 ya2 ya3 ya4 ya5 ya6 mm INV2. rewrite CC in UNF.
      pose proof (od_skip_ok_first bs idxs S1 1 st (o_depth st) PO HDG ltac:(lia)) as SK2.
      ostep. uok.
      eapply evt_eq; [| eapply (od_skip_from Q st (o_adv st 1) v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 FRM INV2); [exact UNF| exact KN| exact KE]].
      od_st_eq. }

    assert (K_DEC : forall pc, pc = 0x9a7e8%Z \/ pc = 0x9a74c%Z ->
              ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall ya0 ya2 ya4 ya5 mm, ODINVp E v352 (o_adv st 1) mm ->
              evt bsegs Q (FST E pc xra xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 (Z_to_bv 64 (o_depth st)) ya4 ya5 (Z_to_bv 64 1) xs4
                               xt3 xt4 xt5 xt6 xF xfc mm)).
    { intros pc PC CC CQ ya0 ya2 ya4 ya5 mm INV2. rewrite CC, CQ in UNF.
      od_open_inv INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

      destruct PC as [-> | ->].
      all: ostep; uok; ostep; ostep; first [if_true | if_false]; ostep; odnorm; ostep; ostep.
      all: if_cases KD; zify_cond KD; odsig KD.
      1,3:
        (replace (o_depth st - 1 <=? 1)%Z with true in UNF by (symmetry; apply Z.leb_le; lia);
         eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| od_close_inv]];
         od_st_eq).
      all: replace (o_depth st - 1 <=? 1)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
      all: pose proof (od_skip_ok_first bs idxs S1 1 st (o_depth st - 1) PO HDG ltac:(lia)) as SK2.
      all: (eapply evt_eq; [| eapply (od_skip_from Q st (o_setd (o_adv st 1) (o_depth st - 1)) v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]];
            [od_st_eq| od_close_inv]). }
    od_open_inv INV.

    ostep. ostep. ostep. if_true. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ual. ostep. ostep. if_true.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) ltac:(eassumption) ltac:(lia)) as RD2).
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) ltac:(eassumption) ltac:(lia)) as RD4).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2. fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
    replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
    set (off := tokI bs idxs (o_pos st)) in *. set (off1 := tokI bs idxs (o_pos st + 1)) in *.
    od_cur_mem ltac:(fun mm => assert (INVA : ODINVp E v352 (o_adv st 1) mm) by od_close_inv).

    ochkn. ostep. odnorm. ostep. ostep. uok.
    ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ochkn. ostep. odnorm. ostep. ostep. zstep.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        ochk. ostep. odnorm. ostep. ostep. uok. ostep. ochk. ostep. odnorm. ostep. zstep.
        if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_DEC 0x9a7e8%Z); [left; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c1 58)) by lia; apply andb_false_r| exact INVA]].
          od_st_eq.
        *
          replace ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z with false in UNF by (rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
          replace ((c =? 34) && (c1 =? 58))%Z with true in UNF by (rewrite (proj2 (Z.eqb_eq c 34)), (proj2 (Z.eqb_eq c1 58)) by lia; reflexivity).
          pose proof (od_skip_ok_key bs idxs S1 HLAST 1 st PO HDG ltac:(unfold C_COLON; fold c1; lia)) as SK2.
          ostep. uok. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ostep.
          eapply evt_eq; [| eapply (od_skip_from Q st (o_adv st 2) v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]].
          -- od_st_eq.
          -- od_close_inv.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply K_L1; [rewrite (proj2 (Z.eqb_eq c 44)) by lia; rewrite !orb_true_r; reflexivity| exact INVA]].
          od_st_eq.
        *
          zstep. zstep. if_cases K3; zify_cond K3.
          --
             eapply evt_eq; [| eapply K_L1; [rewrite (proj2 (Z.eqb_eq c 58)) by lia; rewrite !orb_true_r; reflexivity| exact INVA]].
             od_st_eq.
          -- zstep.
             eapply evt_eq; [| eapply (K_DEC 0x9a7e8%Z); [left; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA]].
             od_st_eq.
    -
      zstep. zstep. if_cases K1; zify_cond K1; odsig K1.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply (K_DEC 0x9a74c%Z); [right; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA]].
          od_st_eq.
        * zstep. zstep. if_cases K3; zify_cond K3.
          -- eapply evt_eq; [| eapply (K_DEC 0x9a7e8%Z); [left; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA]].
             od_st_eq.
          --
             eapply evt_eq; [| eapply K_L1; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; rewrite !orb_true_r; reflexivity| exact INVA]].
             od_st_eq.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          eapply evt_eq; [| eapply K_L1; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA]].
          od_st_eq.
        * zstep. zstep. if_cases K3; zify_cond K3.
          -- eapply evt_eq; [| eapply (K_DEC 0x9a7e8%Z); [left; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA]].
             od_st_eq.
          --
             zstep.
             eapply evt_eq; [| eapply (K_DEC 0x9a74c%Z); [right; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA]].
             od_st_eq.
  Qed.

  Theorem od_plus_top : forall (Q : machine_state -> Prop) st st' v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_arm_out bs idxs st st' -> frm0 xfc -> ODINVp E v352 st' m1 ->
    od_head_k E Q st' ->
    evt bsegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HG HLAST.
    intros Q st st' v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 [HPOS AO] FRM INV HK.
    od_env OK. unfold OD_PLUS.
    assert (HKH : forall P : ost -> Prop, (forall s, P s -> od_head_pre E st' s) -> head_any Q P).
    { intros P HP s' w352 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' PS F' I'. eapply (HK s' 1%Z w352); [apply HP; exact PS| exact F'| exact I']. }
    destruct AO as [PO|DEAD].
    -
      pose proof PO as (HP & HPD & HD & HE & HA & HB).
      pose proof (od_plus_spec bs idxs S1 HLAST 1 st' ltac:(lia) PO) as NEXT.

      assert (K_HN : skip_kn Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = 0%Z)).
      { intros s1 w352 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
        pose proof (skip_child_ok bs idxs S1 HLAST 1 st' PO) as (S1a & S2 & S3 & S4 & S5 & S6). rewrite <- E1 in *.
        destruct S6 as [(_ & D1)|(E3 & _)]; [| rewrite E2 in E3; unfold TAPE_ERROR in E3; lia].
        assert (P1 : (1 <= o_pos s1 <= n)%Z) by lia.
        eapply (od_hasnext E OK Q s1 w352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' I' F' P1 E2 D1 S2).
        apply HKH. intros s2 E2'. left.
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb] in NEXT. rewrite <- E2' in NEXT. exact NEXT. }
      assert (K_ER : head_any Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = TAPE_ERROR)).
      { apply HKH. intros s1 [E1 E2]. left.
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb TAPE_ERROR] in NEXT. exact NEXT. }
      od_open_inv INV.

      ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. uok. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. uok. ostep.
      if_cases KE0; zify_cond KE0; [| exfalso; lia]. clear KE0.

      ostep. ostep. if_true. ostep. ostep. ostep. ostep. uok.
      ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep.
      if_cases G; zify_cond G; odsig G; [|exfalso; lia]. clear G.
      ostep. zstep.
      if_cases KD; zify_cond KD; odsig KD.
      +
        assert (SC : skip_child bs idxs 1 st' = st') by (unfold skip_child; replace (o_depth st' <=? 1)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity).
        eapply evt_eq; [| eapply (K_HN st' v352); [split; [symmetry; exact SC| exact HE]| exact FRM| od_close_inv]].
        od_st_eq.
      + eapply evt_eq; [| eapply (od_skip_first Q st' v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PO ltac:(lia) FRM); [| exact K_HN| exact K_ER]].
        * od_st_eq.
        * od_close_inv.
    -
      destruct DEAD as (DA & DD & DE & DS). pose proof DE as DE3. unfold TAPE_ERROR in DE3.
      od_open_inv INV.
      ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. uok. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. uok. ostep.
      if_cases KE0; zify_cond KE0; [exfalso; lia|]. clear KE0.
      ostep.
      eapply (HK st' 1%Z v352); [right; repeat split; try assumption; lia| exact FRM| od_close_inv].
  Qed.
End Plus2.
