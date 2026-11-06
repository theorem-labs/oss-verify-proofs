(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section Plus.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition head_any (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m',
      P st' -> frm0 xfc -> ODINV E st' m' ->
      evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m').

  Lemma od_hasnext : forall (Q : machine_state -> Prop) st xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    ODINV E st m1 -> frm0 xfc -> (1 <= o_pos st <= n)%Z -> o_err st = 0%Z -> o_depth st = 1%Z -> o_alive st = true ->
    head_any Q (fun st' => st' = has_next bs idxs 1 st) ->
    evt asegs Q (ODST E 0x99100 (Z_to_bv 64 122) xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 ((oa_F E + 192) / 8)) xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros Q st xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 INV FRM HP HE HD HA HK.
    od_open_inv INV. od_env OK. unfold head_any, OD_HEAD in HK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.

    ostep. ostep. if_false. ostep. ostep. ostep. if_false. ostep. ostep. ostep. if_false. ostep. ostep. if_false.

    ostep. ostep. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2.
    assert (HN : has_next bs idxs 1 st =
                 if (tokT bs idxs (o_pos st) =? 93)%Z then o_setd (o_adv st 1) 0
                 else if (tokT bs idxs (o_pos st) =? 44)%Z then o_setd (o_adv st 1) 2 else o_sete (o_adv st 1) 3) by reflexivity.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    ochkn.

    ostep. odnorm. ostep. ochkn. ostep. odnorm. ostep. ostep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. if_false. ostep. ostep. ostep.
      replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? 44)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
      apply (HK (o_setd (o_adv st 1) 2)); [symmetry; exact HN| exact FRM| od_close_inv].
    -
      ostep. ostep.
      if_cases K2; zify_cond K2.
      +
        ostep. ostep. ostep. if_false. ostep. ostep. ostep.
        replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? 44)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        apply (HK (o_sete (o_adv st 1) 3)); [symmetry; exact HN| exact FRM| od_close_inv].
      +
        ostep. ostep. if_false. ostep. ostep. ostep.
        replace (c =? 93)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
        apply (HK (o_setd (o_adv st 1) 0)); [symmetry; exact HN| exact FRM| od_close_inv].
  Qed.

  Lemma skip_loop_unf : forall f st, (o_pos st < n)%Z ->
    skip_loop bs idxs (S f) 1 st =
      let c := tokT bs idxs (o_pos st) in
      if is_open c then skip_loop bs idxs f 1 (o_setd (o_adv st 1) (o_depth st + 1))
      else if is_close c then
             (if (o_depth st - 1 <=? 1)%Z then o_setd (o_adv st 1) (o_depth st - 1)
              else skip_loop bs idxs f 1 (o_setd (o_adv st 1) (o_depth st - 1)))
           else skip_loop bs idxs f 1 (o_adv st 1).
  Proof. intros f st H. cbn [skip_loop]. replace (n <=? o_pos st)%Z with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

  Lemma skip_loop_end : forall f st, (n <= o_pos st)%Z -> skip_loop bs idxs f 1 st = o_sete st TAPE_ERROR.
  Proof. intros [|f] st H; cbn [skip_loop]; [reflexivity|]. replace (n <=? o_pos st)%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

  Definition skip_kn (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m',
      P st' -> frm0 xfc -> ODINV E st' m' ->
      evt asegs Q (ODST E 0x99100 (Z_to_bv 64 122) xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 ((oa_F E + 192) / 8)) xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m').

  Lemma od_skip_err : forall (Q : machine_state -> Prop) st xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    frm0 xfc -> ODINV E st m1 ->
    head_any Q (fun st' => st' = o_sete st TAPE_ERROR) ->
    evt asegs Q (ODST E 0x99184 (Z_to_bv 64 122) xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros Q st xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 FRM INV KE.
    od_open_inv INV. od_env OK. unfold head_any, OD_HEAD in KE.

    ostep. ostep. ostep. if_true. ostep. ostep. ostep.
    apply (KE (o_sete st TAPE_ERROR)); [reflexivity| exact FRM| od_close_inv].
  Qed.

  Lemma od_skip_loop : forall (Q : machine_state -> Prop) (fuel : nat) st xt1 xt2 xa1 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_skip_ok bs idxs 1 st -> (o_pos st < n)%Z -> (n - o_pos st <= Z.of_nat fuel)%Z -> frm0 xfc -> ODINV E st m1 ->
    skip_kn Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = TAPE_ERROR) ->
    evt asegs Q (ODST E 0x99024 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa1 (Z_to_bv 64 (o_IDX E + 4 * n))
                      (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa6 xa7
                      xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST.
    intros Q fuel. induction fuel as [|f IH]; intros st xt1 xt2 xa1 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 SK HPN HF FRM INV KN KE; [exfalso; lia|].
    pose proof SK as (HP & HD & HE & HA & HB).
    od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (skip_loop_unf f st HPN) as UNF. cbv zeta in UNF.
    set (c := tokT bs idxs (o_pos st)) in *.

    assert (K_BOT : forall st2 ya1 ya6 ya7 mm,
              skip_loop bs idxs (S f) 1 st = skip_loop bs idxs f 1 st2 ->
              od_skip_ok bs idxs 1 st2 -> o_pos st2 = (o_pos st + 1)%Z -> ODINV E st2 mm ->
              evt asegs Q (ODST E 0x990c0 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) ya1 (Z_to_bv 64 (o_IDX E + 4 * n))
                                (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya6 ya7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros st2 ya1 ya6 ya7 mm EQ SK2 EP INV2.

      ostep. ostep.
      if_cases KB; zify_cond KB.
      -
        eapply evt_eq; [| eapply (IH st2 _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2); try lia; try exact FRM; try exact INV2].
        + rewrite EP. od_st_eq.
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
      -
        rewrite (skip_loop_end f st2) in EQ by lia.
        clear IH. ostep.
        eapply (od_skip_err Q st2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm FRM INV2).
        intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' E1 F' I'. apply (KE st'); [split; [rewrite E1; symmetry; exact EQ| rewrite E1; reflexivity]| exact F'| exact I']. }

    assert (K_OPEN : is_open c = true -> forall ya1 ya6 ya7 mm, ODINV E (o_adv st 1) mm ->
              evt asegs Q (ODST E 0x99090 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) ya1 (Z_to_bv 64 (o_IDX E + 4 * n))
                                (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya6 ya7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros OP ya1 ya6 ya7 mm INV2. rewrite OP in UNF.
      pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st + 1) SK HPN ltac:(lia)) as SK2.
      od_open_inv INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

      ostep. ostep. if_false. ostep. odnorm. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (K_BOT (o_setd (o_adv st 1) (o_depth st + 1)) _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
      od_st_eq. }

    assert (K_CLOSE : is_open c = false -> is_close c = true -> forall ya1 ya6 ya7 mm, ODINV E (o_adv st 1) mm ->
              evt asegs Q (ODST E 0x990a8 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) ya1 (Z_to_bv 64 (o_IDX E + 4 * n))
                                (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya6 ya7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros OP CL ya1 ya6 ya7 mm INV2. rewrite OP, CL in UNF.
      od_open_inv INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

      ostep. ostep. if_false. ostep. odnorm. ostep. odnorm. ostep. ostep.
      if_cases KD; zify_cond KD; odsig KD.
      -
        replace (o_depth st - 1 <=? 1)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
        eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| od_close_inv]].
        od_st_eq.
      - replace (o_depth st - 1 <=? 1)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
        pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st - 1) SK HPN ltac:(lia)) as SK2.
        eapply evt_eq; [| eapply (K_BOT (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
        od_st_eq. }

    assert (K_OTHER : is_open c = false -> is_close c = false -> forall ya1 ya6 ya7 mm, ODINV E (o_adv st 1) mm ->
              evt asegs Q (ODST E 0x990c0 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) ya1 (Z_to_bv 64 (o_IDX E + 4 * n))
                                (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya6 ya7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros OP CL ya1 ya6 ya7 mm INV2. rewrite OP, CL in UNF.
      pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st) SK HPN ltac:(lia)) as SK2.
      eapply (K_BOT (o_adv st 1) _ _ _ _ UNF SK2); [reflexivity| exact INV2]. }
    od_open_inv INV.

    ostep. ostep. if_true. ostep. ostep. ostep. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2.
    set (off := tokI bs idxs (o_pos st)) in *.
    ostep. ostep. ostep. if_false.

    ostep. odnorm. ostep. ochkn. ostep. odnorm. ostep.

    od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_adv st 1) mm) by od_close_inv).
    clear IH.
    unfold is_open, is_close, C_LBRACKET, C_LBRACE, C_RBRACKET, C_RBRACE in K_OPEN, K_CLOSE, K_OTHER.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      ostep. ostep. if_cases K1; zify_cond K1.
      +
        apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 125)) by lia; apply orb_true_r| exact INVA].
      + ostep. ostep. if_cases K2; zify_cond K2.
        * apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
        *
          apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; apply orb_true_r| exact INVA].
    -
      ostep. ostep. if_cases K1; zify_cond K1.
      +
        apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
      + ostep. ostep. if_cases K2; zify_cond K2.
        * apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
        *
          ostep.
          apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 93)) by lia; reflexivity| exact INVA].
  Qed.

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

  Lemma od_skip_entry : forall (Q : machine_state -> Prop) st0 st1 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_skip_ok bs idxs 1 st1 -> frm0 xfc -> ODINV E st1 m1 ->
    skip_child bs idxs 1 st0 = skip_loop bs idxs (Z.to_nat (n - o_pos st1)) 1 st1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = TAPE_ERROR) ->
    evt asegs Q (ODST E 0x98fa0 (Z_to_bv 64 122) xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) xa5 xa6 xa7
                      xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST.
    intros Q st0 st1 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 SK FRM INV EQ KN KE.
    pose proof SK as (HP & HD & HE & HA & HB).
    pose proof INV as INV0.
    od_env OK.
    assert (K_IN : forall ya1, (o_pos st1 < n)%Z ->
              evt asegs Q (ODST E 0x99024 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st1)) ya1 (Z_to_bv 64 (o_IDX E + 4 * n))
                                (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st1)) xa6 xa7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1)).
    { intros ya1 HLT.
      eapply (od_skip_loop Q (Z.to_nat (n - o_pos st1)) st1 _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK HLT ltac:(lia) FRM INV0).
      - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
      - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I']. }
    od_open_inv INV.
    rewrite HA in ITER.

    ostep. ostep. ostep. if_true.
    ostep. ostep. ochk. ostep. ostep. ochkn. ostep. ochk. ostep. ostep. if_true.

    ostep. odnorm. ostep. ostep. ostep. odnorm. ostep. ostep.
    if_cases KB; zify_cond KB.
    -
      rewrite (skip_loop_end _ st1) in EQ by lia.
      eapply evt_eq; [| eapply (od_skip_err Q st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]; [od_st_eq|].
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' E1 F' I'. apply (KE st'); [split; [rewrite E1; symmetry; exact EQ| rewrite E1; reflexivity]| exact F'| exact I'].
    -
      ostep.
      eapply evt_eq; [| eapply (K_IN _ ltac:(lia))]. od_st_eq.
  Qed.

  Lemma od_skip_first : forall (Q : machine_state -> Prop) st xt1 xt2 xa1 xa2 xa4 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_plus_ok bs idxs 1 st -> (1 < o_depth st)%Z -> frm0 xfc -> ODINV E st m1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = TAPE_ERROR) ->
    evt asegs Q (ODST E 0x98e8c (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa1 xa2 (Z_to_bv 64 ((oa_F E + 192) / 8)) xa4
                      (Z_to_bv 64 (o_depth st)) xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST.
    intros Q st xt1 xt2 xa1 xa2 xa4 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 PO HDG FRM INV KN KE.
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
              forall ya0 ya1 ya2 ya5 ya6 mm, ODINV E (o_adv st 1) mm ->
              evt asegs Q (ODST E 0x98fa0 (Z_to_bv 64 122) xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E)) ya5 ya6 xa7
                                xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros CC ya0 ya1 ya2 ya5 ya6 mm INV2. rewrite CC in UNF.
      pose proof (od_skip_ok_first bs idxs S1 1 st (o_depth st) PO HDG ltac:(lia)) as SK2.
      eapply (od_skip_entry Q st (o_adv st 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 FRM INV2); [exact UNF| exact KN| exact KE]. }

    assert (K_DEC : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall ya0 ya1 ya2 ya6 mm, ODINV E (o_adv st 1) mm ->
              evt asegs Q (ODST E 0x98f94 (Z_to_bv 64 122) xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 ((oa_F E + 192) / 8)) (Z_to_bv 64 (o_BUF E))
                                (Z_to_bv 64 (o_depth st)) ya6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc mm)).
    { intros CC CQ ya0 ya1 ya2 ya6 mm INV2. rewrite CC, CQ in UNF.
      pose proof INV2 as INV20.
      od_open_inv INV2.

      ostep. odnorm. ostep. ostep.
      if_cases KD; zify_cond KD; odsig KD.
      -
        replace (o_depth st - 1 <=? 1)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
        eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| od_close_inv]].
        od_st_eq.
      - replace (o_depth st - 1 <=? 1)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
        pose proof (od_skip_ok_first bs idxs S1 1 st (o_depth st - 1) PO HDG ltac:(lia)) as SK2.
        eapply evt_eq; [| eapply (od_skip_entry Q st (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]].
        + od_st_eq.
        + od_close_inv. }
    od_open_inv INV.

    ostep. ostep. ostep. if_true. ostep. ostep. if_true.
    ostep. ostep. ostep. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2. fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
    replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
    set (off := tokI bs idxs (o_pos st)) in *. set (off1 := tokI bs idxs (o_pos st + 1)) in *.
    od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_adv st 1) mm) by od_close_inv).
    ostep. ostep. ostep. if_false.

    ostep. odnorm. ostep. ochkn. ostep. odnorm. ostep. ostep.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      ostep. ostep. if_cases K1; zify_cond K1.
      +
        ochkn. ostep. odnorm. ostep. ochkn. ostep. odnorm. ostep. ostep.
        if_cases K2; zify_cond K2.
        *
          ostep. ostep. if_false.
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c1 58)) by lia; apply andb_false_r| exact INVA].
        *
          replace ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z with false in UNF by (rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
          replace ((c =? 34) && (c1 =? 58))%Z with true in UNF by (rewrite (proj2 (Z.eqb_eq c 34)), (proj2 (Z.eqb_eq c1 58)) by lia; reflexivity).
          pose proof (od_skip_ok_key bs idxs S1 HLAST 1 st PO HDG ltac:(unfold C_COLON; fold c1; lia)) as SK2.
          ostep. ostep. if_true. ostep. ostep. ostep.
          eapply (od_skip_entry Q st (o_adv st 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE].
          od_close_inv.
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 44)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
        *
          ostep. ostep. if_cases K3; zify_cond K3.
          --
             ostep. ostep. if_false.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
          --
             ostep.
             apply K_L1; [rewrite (proj2 (Z.eqb_eq c 58)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
    -
      ostep. if_cases K1; zify_cond K1; odsig K1.
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
        * ostep. ostep. if_cases K3; zify_cond K3.
          --
             ostep. ostep. if_false.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
          --
             ostep. ostep. if_true.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
      +
        ostep. ostep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
        * ostep. ostep. if_cases K3; zify_cond K3.
          --
             ostep. ostep. if_true.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
          --
             ostep. ostep. ostep. if_false.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
  Qed.

  Theorem od_plus_top : forall (Q : machine_state -> Prop) st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_arm_out bs idxs st st' -> frm0 xfc -> ODINV E st' m1 ->
    od_head_k E Q st' ->
    evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST.
    intros Q st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 [HPOS AO] FRM INV HK.
    od_env OK. unfold OD_PLUS.
    pose proof INV as INV0.
    assert (HKH : forall P : ost -> Prop, (forall s, P s -> od_head_pre E st' s) -> head_any Q P).
    { intros P HP s' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' PS F' I'. apply (HK s' 1%Z); [apply HP; exact PS| exact F'| exact I']. }
    destruct AO as [PO|DEAD].
    -
      pose proof PO as (HP & HPD & HD & HE & HA & HB).
      pose proof (od_plus_spec bs idxs S1 HLAST 1 st' ltac:(lia) PO) as NEXT.
      assert (K_HN : skip_kn Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = 0%Z)).
      { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
        pose proof (skip_child_ok bs idxs S1 HLAST 1 st' PO) as (S1a & S2 & S3 & S4 & S5 & S6). rewrite <- E1 in *.
        destruct S6 as [(_ & D1)|(E3 & _)]; [| rewrite E2 in E3; unfold TAPE_ERROR in E3; lia].
        assert (P1 : (1 <= o_pos s1 <= n)%Z) by lia.
        eapply (od_hasnext Q s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' I' F' P1 E2 D1 S2).
        apply HKH. intros s2 E2'. left.
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb] in NEXT. rewrite <- E2' in NEXT. exact NEXT. }
      assert (K_ER : head_any Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = TAPE_ERROR)).
      { apply HKH. intros s1 [E1 E2]. left.
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb TAPE_ERROR] in NEXT. exact NEXT. }
      od_open_inv INV.

      ostep. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. if_false.
      ostep. odnorm. ostep.
      if_cases KE0; zify_cond KE0; [| exfalso; lia]. clear KE0.

      ostep. ostep. if_true. ostep. ostep. ostep. if_false.
      ostep. odnorm. ostep. ostep.
      if_cases KD; zify_cond KD; odsig KD.
      +
        assert (SC : skip_child bs idxs 1 st' = st') by (unfold skip_child; replace (o_depth st' <=? 1)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity).
        eapply evt_eq; [| eapply (K_HN st'); [split; [symmetry; exact SC| exact HE]| exact FRM| exact INV0]].
        od_st_eq.
      + eapply evt_eq; [| eapply (od_skip_first Q st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PO ltac:(lia) FRM INV0 K_HN K_ER)].
        od_st_eq.
    -
      destruct DEAD as (DA & DD & DE & DS). pose proof DE as DE3. unfold TAPE_ERROR in DE3.
      od_open_inv INV.
      ostep. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. if_false.
      ostep. odnorm. ostep.
      if_cases KE0; zify_cond KE0; [exfalso; lia|]. clear KE0.

      ostep. ostep. lstep.
      apply (HK st' 1%Z); [right; repeat split; try assumption; lia| exact FRM| od_close_inv].
  Qed.
End Plus.
