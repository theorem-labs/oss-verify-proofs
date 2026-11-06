(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_plus.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation NSTu E P pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 10) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 2) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (FR_IT E)) xs7 (Z_to_bv 64 122)
           (Z_to_bv 64 4) (Z_to_bv 64 (o_IDX E + 4 * P)) (Z_to_bv 64 3) xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom usegs)).

Definition ON_HEAD : Z := 0x28a34.

Definition NODINV (E : odenv) (st : ost) (m1 : mem) : Prop :=
  ODINV E st m1 /\ rw_cells usegs m1 (bv_unsigned (o_sp E) + -328) [C8 (wz 1)].

Ltac nod_open H :=
  let F := fresh "F168" in
  destruct H as [H F]; od_open_inv H;
  match goal with HH : rw_cells _ _ (bv_unsigned (o_sp _) + -328)%Z [CB 8 _] |- _ => clear HH end;
  unfold wz in F.
Ltac nod_close :=
  lazymatch goal with
  | |- NODINV _ _ _ =>
      unfold NODINV; split;
      [ match goal with HH : rw_cells _ _ (bv_unsigned (o_sp _) + -328)%Z [C8 _] |- _ =>
          let F := fresh "FR168" in pose proof HH as F; od_forget F; clear HH end;
        od_close_inv
      | od_ass ]
  end.

Ltac gok := first [ if_true | uok ].
Ltac gtrap := first [ if_false | utrap ].

Section NestPlus.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition nhead_any (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> NODINV E st' m' ->
      evt usegs Q (NSTu E pi ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m').

  Lemma un_hasnext : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    NODINV E st m1 -> frm0 xfc -> (pi < o_pos st <= n)%Z -> o_err st = 0%Z -> o_depth st = 2%Z -> o_alive st = true ->
    nhead_any Q (fun st' => st' = has_next bs idxs 2 st) ->
    evt usegs Q (NSTu E pi 0x28c8c xra xt0 xt1 xt2 (Z_to_bv 64 2) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                      xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HPI.
    intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 INV FRM HP HE HD HA HK.
    nod_open INV. od_env OK. od_envu OKU. unfold nhead_any, ON_HEAD in HK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_al_it E OKU) as A8. pose proof (od_al_tok E OKU (o_pos st)) as A4.

    zstep. gtrap. zstep. gtrap. zstep. gtrap. zstep. gtrap.

    zstep. zstep. gtrap. zstep. zstep. ual. zstep. zstep. gtrap.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2.
    assert (HN : has_next bs idxs 2 st =
                 if (tokT bs idxs (o_pos st) =? 93)%Z then o_setd (o_adv st 1) 1
                 else if (tokT bs idxs (o_pos st) =? 44)%Z then o_setd (o_adv st 1) 3 else o_sete (o_adv st 1) 3) by reflexivity.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.

    zstep. odnorm. zstep. zstep. gtrap.
    zstep. zstep. zstep. unz. zstep. gtrap. zstep. gtrap.

    zstep. odnorm. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. zstep. gtrap. zstep. zstep. zstep.
      replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? 44)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
      apply (HK (o_setd (o_adv st 1) 3)); [symmetry; exact HN| exact FRM| nod_close].
    -
      zstep. zstep.
      if_cases K2; zify_cond K2.
      +
        zstep. gtrap. zstep. zstep. zstep. zstep.
        replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? 44)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        apply (HK (o_sete (o_adv st 1) 3)); [symmetry; exact HN| exact FRM| nod_close].
      +
        zstep. gtrap. zstep. zstep. zstep. zstep.
        replace (c =? 93)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
        apply (HK (o_setd (o_adv st 1) 1)); [symmetry; exact HN| exact FRM| nod_close].
  Qed.

  Lemma skip_loop_unf2 : forall f st, (o_pos st < n)%Z ->
    skip_loop bs idxs (S f) 2 st =
      let c := tokT bs idxs (o_pos st) in
      if is_open c then skip_loop bs idxs f 2 (o_setd (o_adv st 1) (o_depth st + 1))
      else if is_close c then
             (if (o_depth st - 1 <=? 2)%Z then o_setd (o_adv st 1) (o_depth st - 1)
              else skip_loop bs idxs f 2 (o_setd (o_adv st 1) (o_depth st - 1)))
           else skip_loop bs idxs f 2 (o_adv st 1).
  Proof. intros f st H. cbn [skip_loop]. replace (n <=? o_pos st)%Z with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

  Lemma skip_loop_end2 : forall f st, (n <= o_pos st)%Z -> skip_loop bs idxs f 2 st = o_sete st TAPE_ERROR.
  Proof. intros [|f] st H; cbn [skip_loop]; [reflexivity|]. replace (n <=? o_pos st)%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

  Definition nskip_kn (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> NODINV E st' m' ->
      evt usegs Q (NSTu E pi 0x28c8c xra xt0 xt1 xt2 (Z_to_bv 64 (o_depth st')) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st'))
                        xt3 xt4 xt5 xt6 xF xfc m').

  Lemma un_skip_top : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st -> frm0 xfc -> NODINV E st m1 ->
    ((n <= o_pos st)%Z -> nhead_any Q (fun st' => st' = o_sete st TAPE_ERROR)) ->
    ((o_pos st < n)%Z -> forall xra' xa0' xa1' xa2' xa3' xa4',
       evt usegs Q (NSTu E pi 0x28d94 xra' xt0 xt1 xt2 xa0' xa1' xa2' xa3' xa4' xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                         xt3 xt4 xt5 xt6 xF xfc m1)) ->
    evt usegs Q (NSTu E pi 0x28d64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                      xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 SK FRM INV KE KB.
    pose proof SK as (HP & HD & HE & HA & HB).
    pose proof INV as INV0.
    nod_open INV. od_env OK. od_envu OKU.
    pose proof (od_al_it E OKU) as A8. pose proof (od_al_pa E OKU) as A8p. destruct UIMPL as [UIMPL0 UIMPL8].
    rewrite HA in ITER.

    zstep. zstep. gtrap. zstep. ual. zstep. gtrap.
    zstep. zstep. gtrap. zstep. ual. zstep. gtrap.
    zstep. odnorm. zstep. zstep.
    eapply evt_eq; [| eapply (od_opidx E OK OKU Q n 0x28d90); [exact DPI| lia| lia| reflexivity| intros xa1' xa2' xa3' xa4']]; [unfold OD_OPIDX_; od_st_eq|].

    zstep.
    if_cases KC; zify_cond KC.
    -
      specialize (KE ltac:(lia)). unfold nhead_any, ON_HEAD in KE.
      zstep. zstep. gtrap. zstep. zstep. zstep. zstep. zstep.
      apply (KE (o_sete st TAPE_ERROR)); [reflexivity| exact FRM| nod_close].
    - eapply evt_eq; [| eapply (KB ltac:(lia))]. od_st_eq.
  Qed.

  Lemma un_skip_loop : forall (Q : machine_state -> Prop) (fuel : nat) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st -> (n - o_pos st <= Z.of_nat fuel)%Z -> frm0 xfc -> NODINV E st m1 ->
    nskip_kn Q (fun st' => st' = skip_loop bs idxs fuel 2 st /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_loop bs idxs fuel 2 st /\ o_err st' = TAPE_ERROR) ->
    evt usegs Q (NSTu E pi 0x28d64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                      xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST.
    intros Q fuel. induction fuel as [|f IH]; intros st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 SK HF FRM INV KN KE.
    all: apply (un_skip_top Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK FRM INV).
    1,3: (intros HGE st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' E1 F' I';
          apply (KE st'); [split; [rewrite E1; symmetry; apply skip_loop_end2; exact HGE| rewrite E1; reflexivity]| exact F'| exact I']).
    - intros HLT. exfalso. lia.
    - intros HPN xra' xa0' xa1' xa2' xa3' xa4'.
      pose proof SK as (HP & HD & HE & HA & HB).
      od_env OK. od_envu OKU.
      pose proof (od_al_it E OKU) as A8. pose proof (od_al_tok E OKU (o_pos st)) as A4.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_tokT_range E BOK (o_pos st)) as CR.
      pose proof (skip_loop_unf2 f st HPN) as UNF. cbv zeta in UNF.
      set (c := tokT bs idxs (o_pos st)) in *.

      assert (K_TOP : forall st2 xra2 ya0 ya1 ya2 ya3 ya4 mm,
                skip_loop bs idxs (S f) 2 st = skip_loop bs idxs f 2 st2 ->
                od_skip_ok bs idxs 2 st2 -> o_pos st2 = (o_pos st + 1)%Z -> NODINV E st2 mm ->
                evt usegs Q (NSTu E pi 0x28d64 xra2 xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                  xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros st2 xra2 ya0 ya1 ya2 ya3 ya4 mm EQ SK2 EP INV2.
        eapply evt_eq; [| eapply (IH st2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2); try lia; try exact FRM; try exact INV2].
        + rewrite EP. od_st_eq.
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I']. }

      assert (K_OPEN : is_open c = true -> forall ya0 ya1 ya2 ya3 mm, NODINV E (o_adv st 1) mm ->
                evt usegs Q (NSTu E pi 0x28d50 xra' xt0 xt1 xt2 ya0 ya1 ya2 ya3 xa4' xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                  xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP ya0 ya1 ya2 ya3 mm INV2. rewrite OP in UNF.
        pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st + 1) SK HPN ltac:(lia)) as SK2.
        nod_open INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        zstep. gtrap. zstep. odnorm. zstep. odnorm. zstep.
        if_cases G; zify_cond G; odsig G; [exfalso; lia|]. clear G.
        zstep.
        eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st + 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| nod_close]].
        od_st_eq. }

      assert (K_CLOSE : is_open c = false -> is_close c = true -> forall ya0 ya1 ya2 ya3 mm, NODINV E (o_adv st 1) mm ->
                evt usegs Q (NSTu E pi 0x28dec xra' xt0 xt1 xt2 ya0 ya1 ya2 ya3 xa4' xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                  xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP CL ya0 ya1 ya2 ya3 mm INV2. rewrite OP, CL in UNF.
        nod_open INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        zstep. gtrap. zstep. odnorm. zstep. odnorm. zstep.
        if_cases G; zify_cond G; odsig G; [exfalso; lia|]. clear G.
        zstep. zstep. zstep.
        if_cases KD; zify_cond KD; odsig KD.
        - replace (o_depth st - 1 <=? 2)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
          pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st - 1) SK HPN ltac:(lia)) as SK2.
          eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| nod_close]].
          od_st_eq.
        -
          replace (o_depth st - 1 <=? 2)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
          zstep.
          eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| nod_close]].
          od_st_eq. }

      assert (K_OTHER : is_open c = false -> is_close c = false -> forall ya0 ya1 ya2 ya3 mm, NODINV E (o_adv st 1) mm ->
                evt usegs Q (NSTu E pi 0x28d2c xra' xt0 xt1 xt2 ya0 ya1 ya2 ya3 xa4' xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                  xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP CL ya0 ya1 ya2 ya3 mm INV2. rewrite OP, CL in UNF.
        pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st) SK HPN ltac:(lia)) as SK2.
        zstep. gok.
        eapply (K_TOP (o_adv st 1) _ _ _ _ _ _ _ UNF SK2); [reflexivity| exact INV2]. }
      nod_open INV.

      zstep. zstep. zstep. gtrap. zstep. zstep. zstep. gtrap. zstep. ual. zstep. gtrap.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
      fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2.
      set (off := tokI bs idxs (o_pos st)) in *.

      zstep. odnorm. zstep. zstep. gtrap.
      zstep. zstep. zstep. unz. zstep. gtrap. zstep. gtrap.
      zstep. odnorm. zstep.
      od_cur_mem ltac:(fun mm => assert (INVA : NODINV E (o_adv st 1) mm) by nod_close).
      clear IH K_TOP.
      unfold is_open, is_close, C_LBRACKET, C_LBRACE, C_RBRACKET, C_RBRACE in K_OPEN, K_CLOSE, K_OTHER.
      if_cases KZ; zify_cond KZ; odsig KZ.
      +
        zstep. zstep. if_cases K1; zify_cond K1.
        *
          apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 125)) by lia; apply orb_true_r| exact INVA].
        * zstep. zstep. if_cases K2; zify_cond K2.
          -- apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
          --
             apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; apply orb_true_r| exact INVA].
      +
        zstep. zstep. if_cases K1; zify_cond K1.
        *
          apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
        * zstep. zstep. if_cases K2; zify_cond K2.
          -- apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA].
          --
             apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 93)) by lia; reflexivity| exact INVA].
  Qed.

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

  Lemma un_skip_from : forall (Q : machine_state -> Prop) st0 st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st1 -> frm0 xfc -> NODINV E st1 m1 ->
    skip_child bs idxs 2 st0 = skip_loop bs idxs (Z.to_nat (n - o_pos st1)) 2 st1 ->
    nskip_kn Q (fun st' => st' = skip_child bs idxs 2 st0 /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_child bs idxs 2 st0 /\ o_err st' = TAPE_ERROR) ->
    evt usegs Q (NSTu E pi 0x28d64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st1))
                      xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST.
    intros Q st0 st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 SK FRM INV EQ KN KE.
    pose proof SK as (HP & HD & HE & HA & HB).
    eapply (un_skip_loop Q (Z.to_nat (n - o_pos st1)) st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK ltac:(lia) FRM INV).
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
  Qed.

  Lemma un_skip_first : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_plus_ok bs idxs 2 st -> (2 < o_depth st)%Z -> frm0 xfc -> NODINV E st m1 ->
    nskip_kn Q (fun st' => st' = skip_child bs idxs 2 st /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_child bs idxs 2 st /\ o_err st' = TAPE_ERROR) ->
    evt usegs Q (NSTu E pi 0x28bb8 xra xt0 xt1 xt2 (Z_to_bv 64 (o_depth st)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa2 xa3 xa4 xa5 xa6 xa7 xs7
                      xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST.
    intros Q st xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m1 PO HDG FRM INV KN KE.
    pose proof PO as (HP & HPD & HD & HE & HA & HB). specialize (HPD HDG).
    od_env OK. od_envu OKU.
    pose proof (od_al_it E OKU) as A8. pose proof (od_al_tok E OKU (o_pos st)) as A4.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR1.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR1.
    pose proof (skip_child_unf2 st HDG) as UNF. cbv zeta in UNF.
    unfold is_open, C_LBRACKET, C_LBRACE, C_COLON, C_COMMA, C_QUOTE in UNF.
    set (c := tokT bs idxs (o_pos st)) in *. set (c1 := tokT bs idxs (o_pos st + 1)) in *.

    assert (K_L1 : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = true ->
              forall ya1 ya2 ya3 ya4 ya5 mm, NODINV E (o_adv st 1) mm ->
              evt usegs Q (NSTu E pi 0x28d2c xra xt0 xt1 xt2 (Z_to_bv 64 (o_depth st)) ya1 ya2 ya3 ya4 ya5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                xt3 xt4 xt5 xt6 xF xfc mm)).
    { intros CC ya1 ya2 ya3 ya4 ya5 mm INV2. rewrite CC in UNF.
      pose proof (od_skip_ok_first bs idxs S1 2 st (o_depth st) PO HDG ltac:(lia)) as SK2.
      zstep. gok.
      eapply evt_eq; [| eapply (un_skip_from Q st (o_adv st 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2 FRM INV2); [exact UNF| exact KN| exact KE]].
      od_st_eq. }

    assert (K_DEC : ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z = false -> ((c =? 34) && (c1 =? 58))%Z = false ->
              forall ya1 ya2 ya3 ya4 ya5 mm, NODINV E (o_adv st 1) mm ->
              evt usegs Q (NSTu E pi 0x28c80 xra xt0 xt1 xt2 (Z_to_bv 64 (o_depth st)) ya1 ya2 ya3 ya4 ya5 xa6 xa7 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4))
                                xt3 xt4 xt5 xt6 xF xfc mm)).
    { intros CC CQ ya1 ya2 ya3 ya4 ya5 mm INV2. rewrite CC, CQ in UNF.
      nod_open INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

      zstep. gtrap. zstep. odnorm. zstep. zstep. zstep.
      if_cases KD; zify_cond KD; odsig KD.
      - replace (o_depth st - 1 <=? 2)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
        pose proof (od_skip_ok_first bs idxs S1 2 st (o_depth st - 1) PO HDG ltac:(lia)) as SK2.
        eapply evt_eq; [| eapply (un_skip_from Q st (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]].
        + od_st_eq.
        + nod_close.
      -
        replace (o_depth st - 1 <=? 2)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
        zstep.
        eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| nod_close]].
        od_st_eq. }
    nod_open INV.

    zstep. zstep. gtrap. zstep. zstep. ual. zstep. zstep. gtrap.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
    fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2. fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
    replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
    set (off := tokI bs idxs (o_pos st)) in *. set (off1 := tokI bs idxs (o_pos st + 1)) in *.
    od_cur_mem ltac:(fun mm => assert (INVA : NODINV E (o_adv st 1) mm) by nod_close).

    zstep. odnorm. zstep. zstep. gtrap.
    zstep. zstep. zstep. unz. zstep. gtrap. zstep. gtrap.
    zstep. odnorm. zstep. zstep.
    if_cases KZ; zify_cond KZ; odsig KZ.
    -
      zstep. zstep. if_cases K1; zify_cond K1.
      +
        zstep. odnorm. zstep. zstep. gtrap. zstep. zstep. odnorm. zstep. zstep.
        if_cases K2; zify_cond K2.
        *
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c1 58)) by lia; apply andb_false_r| exact INVA].
        *
          replace ((c =? 91) || (c =? 123) || (c =? 58) || (c =? 44))%Z with false in UNF by (rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
          replace ((c =? 34) && (c1 =? 58))%Z with true in UNF by (rewrite (proj2 (Z.eqb_eq c 34)), (proj2 (Z.eqb_eq c1 58)) by lia; reflexivity).
          pose proof (od_skip_ok_key bs idxs S1 HLAST 2 st PO HDG ltac:(unfold C_COLON; fold c1; lia)) as SK2.
          zstep. gtrap. zstep. gtrap. zstep. zstep. gtrap. zstep. zstep. zstep.
          eapply evt_eq; [| eapply (un_skip_from Q st (o_adv st 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SK2 FRM); [| exact UNF| exact KN| exact KE]].
          -- od_st_eq.
          -- nod_close.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 44)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
        *
          zstep. zstep. if_cases K3; zify_cond K3.
          --
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
          --
             zstep.
             apply K_L1; [rewrite (proj2 (Z.eqb_eq c 58)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
    -
      zstep. if_cases K1; zify_cond K1; odsig K1.
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
        * zstep. zstep. if_cases K3; zify_cond K3.
          --
             apply K_L1; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; rewrite !orb_true_r; reflexivity| exact INVA].
          -- zstep.
             apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
      +
        zstep. zstep. if_cases K2; zify_cond K2.
        *
          apply K_L1; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA].
        * zstep. zstep.
          apply K_DEC; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_neq c 34)) by lia; reflexivity| exact INVA].
  Qed.

  Lemma un_plus : forall (Q : machine_state -> Prop) st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_plus_ok bs idxs 2 st1 -> (pi < o_pos st1)%Z -> frm0 xfc -> NODINV E st1 m1 ->
    nhead_any Q (fun st' => od_next_ok bs idxs 2 st1 st') ->
    evt usegs Q (NSTu E pi 0x28b90 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST HPI.
    intros Q st1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 PO HPP FRM INV HK.
    od_env OK. od_envu OKU.
    pose proof (od_al_it E OKU) as A8.
    pose proof PO as (HP & HPD & HD & HE & HA & HB).
    pose proof (od_plus_spec bs idxs S1 HLAST 2 st1 ltac:(lia) PO) as NEXT.

    assert (K_HN : nskip_kn Q (fun s1 => s1 = skip_child bs idxs 2 st1 /\ o_err s1 = 0%Z)).
    { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
      pose proof (skip_child_ok bs idxs S1 HLAST 2 st1 PO) as (S1a & S2 & S3 & S4 & S5 & S6). rewrite <- E1 in *.
      destruct S6 as [(_ & D1)|(E3 & _)]; [| rewrite E2 in E3; unfold TAPE_ERROR in E3; lia].
      assert (P1 : (pi < o_pos s1 <= n)%Z) by lia.
      eapply evt_eq; [| eapply (un_hasnext Q s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' I' F' P1 E2 D1 S2)]; [rewrite D1; od_st_eq|].
      intros s2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 E2' F2 I2.
      apply (HK s2); [| exact F2| exact I2].
      unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb] in NEXT. rewrite <- E2' in NEXT. exact NEXT. }
    assert (K_ER : nhead_any Q (fun s1 => s1 = skip_child bs idxs 2 st1 /\ o_err s1 = TAPE_ERROR)).
    { intros s1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' [E1 E2] F' I'.
      apply (HK s1); [| exact F'| exact I'].
      unfold od_plus in NEXT. rewrite <- E1, E2 in NEXT. cbn [Z.eqb TAPE_ERROR] in NEXT. exact NEXT. }
    pose proof INV as INV0.
    nod_open INV.

    zstep. odnorm. zstep. zstep. gtrap. zstep. zstep.
    if_cases KE0; zify_cond KE0; try (exfalso; lia). clear KE0.

    zstep. zstep. gtrap. zstep. odnorm. zstep.
    if_cases G; zify_cond G; odsig G; [exfalso; lia|]. clear G.
    zstep.
    if_cases KD; zify_cond KD; odsig KD.
    -
      zstep. zstep.
      assert (SC : skip_child bs idxs 2 st1 = st1) by (unfold skip_child; replace (o_depth st1 <=? 2)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity).
      eapply evt_eq; [| eapply (K_HN st1); [split; [symmetry; exact SC| exact HE]| exact FRM| exact INV0]].
      od_st_eq.
    - eapply evt_eq; [| eapply (un_skip_first Q st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PO ltac:(lia) FRM INV0 K_HN K_ER)].
      od_st_eq.
  Qed.
End NestPlus.
