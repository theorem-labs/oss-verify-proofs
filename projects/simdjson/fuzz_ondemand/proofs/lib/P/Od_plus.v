(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Plus.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition head_any (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m',
      P st' -> frm0 xfc -> ODINV E st' m' ->
      evt psegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m').

  Lemma od_hasnext : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    ODINV E st m1 -> frm0 xfc -> (1 <= o_pos st <= n)%Z -> o_err st = 0%Z -> o_depth st = 1%Z -> o_alive st = true ->
    head_any Q (fun st' => st' = has_next bs idxs 1 st) ->
    evt psegs Q (ODST E 0x2802c xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 INV FRM HP HE HD HA HK.
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    zstep. zstep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2.
    assert (HN : has_next bs idxs 1 st =
                 if (tokT bs idxs (o_pos st) =? 93)%Z then o_setd (o_adv st 1) 0
                 else if (tokT bs idxs (o_pos st) =? 44)%Z then o_setd (o_adv st 1) 2 else o_sete (o_adv st 1) 3) by reflexivity.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep.
      replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? 44)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
      apply (HK (o_setd (o_adv st 1) 2)); [symmetry; exact HN| exact FRM| od_close_inv].
    - zstep. zstep.
      if_cases K2; zify_cond K2.
      +
        zstep. zstep. zstep.
        replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? 44)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        apply (HK (o_sete (o_adv st 1) 3)); [symmetry; exact HN| exact FRM| od_close_inv].
      +
        zstep. zstep. zstep.
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
    forall st' xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m',
      P st' -> frm0 xfc -> ODINV E st' m' ->
      evt psegs Q (ODST E 0x2802c xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st')) xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m').

  Lemma od_skip_loop : forall (Q : machine_state -> Prop) (fuel : nat) st xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_skip_ok bs idxs 1 st -> (o_pos st < n)%Z -> (n - o_pos st <= Z.of_nat fuel)%Z -> frm0 xfc -> ODINV E st m1 ->
    skip_kn Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = TAPE_ERROR) ->
    evt psegs Q (ODST E 0x280d4 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_depth st))
                      (Z_to_bv 64 (o_IDX E + 4 * n)) xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK HLAST.
    intros Q fuel. induction fuel as [|f IH]; intros st xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 SK HPN HF FRM INV KN KE; [exfalso; lia|].
    pose proof SK as (HP & HD & HE & HA & HB).
    od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (skip_loop_unf f st HPN) as UNF. cbv zeta in UNF.
    set (c := tokT bs idxs (o_pos st)) in *.

    assert (K_BOT : forall st2 xa4' xa5' xa6' mm,
              skip_loop bs idxs (S f) 1 st = skip_loop bs idxs f 1 st2 ->
              od_skip_ok bs idxs 1 st2 -> o_pos st2 = (o_pos st + 1)%Z -> ODINV E st2 mm ->
              evt psegs Q (ODST E 0x28124 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st2))
                                (Z_to_bv 64 (o_IDX E + 4 * n)) xa4' xa5' xa6' xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros st2 xa4' xa5' xa6' mm EQ SK2 EP INV2.
      zstep.
      if_cases KB; zify_cond KB.
      -
        eapply evt_eq; [| eapply (IH st2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2); try lia; try exact FRM; try exact INV2].
        + rewrite EP. od_st_eq.
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
      -
        rewrite (skip_loop_end f st2) in EQ by lia.
        clear IH. pose proof SK2 as (HP2 & HD2 & HE2 & HA2 & HB2). od_open_inv INV2.
        zstep. zstep. zstep.
        apply (KE (o_sete st2 TAPE_ERROR)); [split; [symmetry; exact EQ| reflexivity]| exact FRM| od_close_inv]. }

    assert (K_OPEN : is_open c = true -> forall xa4' xa5' xa6' mm, ODINV E (o_adv st 1) mm ->
              evt psegs Q (ODST E 0x2810c xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st))
                                (Z_to_bv 64 (o_IDX E + 4 * n)) xa4' xa5' xa6' xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros OP xa4' xa5' xa6' mm INV2. rewrite OP in UNF.
      pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st + 1) SK HPN ltac:(lia)) as SK2.
      od_open_inv INV2.
      zstep. zstep. zstep.
      eapply evt_eq; [| eapply (K_BOT (o_setd (o_adv st 1) (o_depth st + 1)) _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
      od_st_eq. }

    assert (K_CLOSE : is_open c = false -> is_close c = true -> forall xa5' xa6' mm, ODINV E (o_adv st 1) mm ->
              evt psegs Q (ODST E 0x28118 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st))
                                (Z_to_bv 64 (o_IDX E + 4 * n)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa5' xa6' xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros OP CL xa5' xa6' mm INV2. rewrite OP, CL in UNF.
      od_open_inv INV2.
      zstep. odnorm. zstep. zstep.
      if_cases KD; zify_cond KD; odsig KD.
      -
        replace (o_depth st - 1 <=? 1)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
        zstep. zstep.
        eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| od_close_inv]].
        od_st_eq.
      - replace (o_depth st - 1 <=? 1)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
        pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st - 1) SK HPN ltac:(lia)) as SK2.
        eapply evt_eq; [| eapply (K_BOT (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
        od_st_eq. }

    assert (K_OTHER : is_open c = false -> is_close c = false -> forall xa4' xa5' xa6' mm, ODINV E (o_adv st 1) mm ->
              evt psegs Q (ODST E 0x28124 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st))
                                (Z_to_bv 64 (o_IDX E + 4 * n)) xa4' xa5' xa6' xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros OP CL xa4' xa5' xa6' mm INV2. rewrite OP, CL in UNF.
      pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st) SK HPN ltac:(lia)) as SK2.
      eapply (K_BOT (o_adv st 1) _ _ _ _ UNF SK2); [reflexivity| exact INV2]. }

    od_open_inv INV.
    zstep. zstep. zstep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2.
    set (off := tokI bs idxs (o_pos st)) in *.

    zstep. odnorm. zstep. zstep. odnorm. zstep.

    od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_adv st 1) mm) by od_close_inv).
    clear IH.
    unfold is_open, is_close, C_LBRACKET, C_LBRACE, C_RBRACKET, C_RBRACE in K_OPEN, K_CLOSE, K_OTHER.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      zstep. if_cases K1; zify_cond K1.
      +
        apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 125)) by lia; apply orb_true_r| exact INVA].
      + zstep. zstep. if_cases K2; zify_cond K2.
        * apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
        *
          apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; apply orb_true_r| exact INVA].
    - zstep. if_cases K1; zify_cond K1.
      +
        apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
      + zstep. zstep. if_cases K2; zify_cond K2.
        * apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
        *
          zstep.
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

  Lemma od_skip_entry : forall (Q : machine_state -> Prop) st0 st1 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_skip_ok bs idxs 1 st1 -> frm0 xfc -> ODINV E st1 m1 ->
    skip_child bs idxs 1 st0 = skip_loop bs idxs (Z.to_nat (n - o_pos st1)) 1 st1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st0 /\ o_err st' = TAPE_ERROR) ->
    evt psegs Q (ODST E 0x280b8 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st1)) (Z_to_bv 64 (o_depth st1))
                      xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK HLAST.
    intros Q st0 st1 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 SK FRM INV EQ KN KE.
    pose proof SK as (HP & HD & HE & HA & HB).
    od_env OK.
    assert (K_IN : forall xa4' mm, (o_pos st1 < n)%Z -> ODINV E st1 mm ->
              evt psegs Q (ODST E 0x280d4 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st1)) (Z_to_bv 64 (o_depth st1))
                                (Z_to_bv 64 (o_IDX E + 4 * n)) xa4' xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros xa4' mm HLT INV2.
      eapply (od_skip_loop Q (Z.to_nat (n - o_pos st1)) st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK HLT ltac:(lia) FRM INV2).
      - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
      - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I']. }
    od_open_inv INV.
    rewrite HA in ITER.

    zstep. zstep. zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    if_cases KB; zify_cond KB.
    -
      rewrite (skip_loop_end _ st1) in EQ by lia.
      zstep. zstep. zstep.
      apply (KE (o_sete st1 TAPE_ERROR)); [split; [symmetry; exact EQ| reflexivity]| exact FRM|].
      od_close_inv.
    - eapply evt_eq; [| eapply (K_IN _ _ ltac:(lia))]; [od_st_eq|].
      od_close_inv.
  Qed.

  Lemma od_skip_first : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa1 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_plus_ok bs idxs 1 st -> (1 < o_depth st)%Z -> frm0 xfc -> ODINV E st m1 ->
    skip_kn Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_child bs idxs 1 st /\ o_err st' = TAPE_ERROR) ->
    evt psegs Q (ODST E 0x27ffc xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) xa1 (Z_to_bv 64 (o_depth st)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                      xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK HLAST.
    intros Q st xt0 xt1 xt2 xa1 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 PO HDG FRM INV KN KE.
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
              forall xa3' xa4' xa5' mm, ODINV E (o_adv st 1) mm ->
              evt psegs Q (ODST E 0x280b8 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st))
                                xa3' xa4' xa5' xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros CC xa3' xa4' xa5' mm INV2. rewrite CC in UNF.
      pose proof (od_skip_ok_first bs idxs S1 1 st (o_depth st) PO HDG ltac:(lia)) as SK2.
      eapply evt_eq; [| eapply (od_skip_entry Q st (o_adv st 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 FRM INV2); [exact UNF| exact KN| exact KE]].
      od_st_eq. }

    assert (K_DEC : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall xa3' xa4' xa5' mm, ODINV E (o_adv st 1) mm ->
              evt psegs Q (ODST E 0x280ac xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) (Z_to_bv 64 (o_depth st))
                                xa3' xa4' xa5' xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc mm)).
    { intros CC CQ xa3' xa4' xa5' mm INV2. rewrite CC, CQ in UNF.
      od_open_inv INV2.
      zstep. odnorm. zstep. zstep.
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

    zstep. zstep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2. fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
    replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
    set (off := tokI bs idxs (o_pos st)) in *. set (off1 := tokI bs idxs (o_pos st + 1)) in *.
    od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_adv st 1) mm) by od_close_inv).
    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
        if_cases K2; zify_cond K2.
        *
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c1 58)) by lia; apply andb_false_r| exact INVA].
        *
          replace ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z with false in UNF by (rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
          replace ((c =? 34) && (c1 =? 58))%Z with true in UNF by (rewrite (proj2 (Z.eqb_eq c 34)), (proj2 (Z.eqb_eq c1 58)) by lia; reflexivity).
          pose proof (od_skip_ok_key bs idxs S1 HLAST 1 st PO HDG ltac:(unfold C_COLON; fold c1; lia)) as SK2.
          zstep. zstep. zstep.
          eapply evt_eq; [| eapply (od_skip_entry Q st (o_adv st 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]].
          -- od_st_eq.
          -- od_close_inv.
      + zstep. zstep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 44)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
        * zstep. zstep. if_cases K3; zify_cond K3.
          --
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
          --
             zstep.
             apply K_L1; [rewrite (proj2 (Z.eqb_eq c 58)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
    - zstep. if_cases K1; zify_cond K1; odsig K1.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
        * zstep.
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
      + zstep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
        * zstep. zstep.
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
  Qed.

  Theorem od_plus_top : forall (Q : machine_state -> Prop) st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_arm_out bs idxs st st' -> frm0 xfc -> ODINV E st' m1 ->
    od_head_k E Q st' ->
    evt psegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK HLAST.
    intros Q st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 [HPOS AO] FRM INV HK.
    od_env OK. unfold OD_PLUS.
    destruct AO as [PO|DEAD].
    -
      pose proof PO as (HP & HPD & HD & HE & HA & HB).
      pose proof (od_plus_spec bs idxs S1 HLAST 1 st' ltac:(lia) PO) as NEXT.

      assert (K_HN : skip_kn Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = 0%Z)).
      { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? xF' xfc' m' [E1 E2] F' I'.
        pose proof (skip_child_ok bs idxs S1 HLAST 1 st' PO) as (S1a & S2 & S3 & S4 & S5 & S6). rewrite <- E1 in *.
        destruct S6 as [(_ & D1)|(E3 & _)]; [| rewrite E2 in E3; unfold TAPE_ERROR in E3; lia].
        assert (P1 : (1 <= o_pos s1 <= n)%Z) by lia.
        eapply (od_hasnext Q s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' I' F' P1 E2 D1 S2).
        intros s2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 E2' F2 I2.
        apply (HK s2); [left| exact F2| exact I2].
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb] in NEXT. rewrite <- E2' in NEXT. exact NEXT. }
      assert (K_ER : head_any Q (fun s1 => s1 = skip_child bs idxs 1 st' /\ o_err s1 = TAPE_ERROR)).
      { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
        apply (HK s1); [left| exact F'| exact I'].
        unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb TAPE_ERROR] in NEXT. exact NEXT. }
      od_open_inv INV.

      zstep. zstep. if_false.
      zstep. odnorm. zstep. zstep.
      if_cases KE0; zify_cond KE0; try (exfalso; lia). clear KE0.

      zstep. zstep. odnorm. zstep. zstep.
      if_cases KD; zify_cond KD; odsig KD.
      +
        zstep.
        assert (SC : skip_child bs idxs 1 st' = st') by (unfold skip_child; replace (o_depth st' <=? 1)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity).
        eapply evt_eq; [| eapply (K_HN st'); [split; [symmetry; exact SC| exact HE]| exact FRM| od_close_inv]].
        od_st_eq.
      + eapply evt_eq; [| eapply (od_skip_first Q st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PO ltac:(lia) FRM); [| exact K_HN| exact K_ER]].
        * od_st_eq.
        * od_close_inv.
    -
      destruct DEAD as (DA & DD & DE & DS). pose proof DE as DE3. unfold TAPE_ERROR in DE3.
      od_open_inv INV.
      zstep. zstep. if_false.
      zstep. odnorm. zstep. zstep.
      if_cases KE0; zify_cond KE0; try (exfalso; lia). clear KE0.

      zstep. lstep.
      apply (HK st'); [right; repeat split; try assumption; lia| exact FRM| od_close_inv].
  Qed.
End Plus.
