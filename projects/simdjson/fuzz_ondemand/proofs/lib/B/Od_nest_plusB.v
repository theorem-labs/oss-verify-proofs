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

Notation NSTb E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 (Z_to_bv 64 (oa_F E + 200))
           (Z_to_bv 64 2147450880) xs8 xs9
           (Z_to_bv 64 (oa_F E + 228)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

Notation NSTh E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m :=
  (NSTb E pc xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 (oa_F E + 224)) xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5
        (Z_to_bv 64 (oa_F E + 228)) (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m).

Notation NSTp E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m :=
  (NSTb E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
        xs4 xs5 xs8 (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m).

Definition ON_HEAD : Z := 0x99a90.

Definition NODb (E : oaenv) (pi : Z) (c272 c320 : cell) (st : ost) (m1 : mem) : Prop :=
  ODINVc E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * pi)
         (C8 (wz 1)) (C8 (wz 1)) (C8 (wz 3)) (C8 (wz 0)) c272 (C8 (wz (oa_F E + 224))) c320 (C8 (wz (oa_F E + 208))) st m1.

Definition NODh (E : oaenv) (pi : Z) (st : ost) (m1 : mem) : Prop :=
  exists j272 j320, NODb E pi (CB 8 j272) (CB 8 j320) st m1.

Notation NODp E pi st m1 := (NODb E pi (C8 (wz ((oa_F E + 192) / 8))) (C8 (wz ((oa_F E + 224) / 8 + 2147450880))) st m1).

Ltac nod_open H := unfold NODb in H; od_open_invc H.
Ltac nod_close := lazymatch goal with |- NODb _ _ _ _ _ _ => unfold NODb; od_close_invc end.

Ltac nodh_close :=
  lazymatch goal with
  | |- NODh _ _ _ ?m =>
      repeat match goal with
      | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: C8 _ :: _) |- _ => od_forget_k H 4%nat
      | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ => od_forget_k H 10%nat
      end;
      unfold NODh, NODb; do 2 eexists; od_close_invc
  end.

Ltac gok := first [ if_true | uok ].
Ltac gtrap := first [ if_false | utrap ].

Ltac goks := let G := fresh "UG" in if_cases G; zify_cond G; odsig G; [| exfalso; lia]; try clear G.
Ltac gtraps := let G := fresh "UG" in if_cases G; zify_cond G; odsig G; [exfalso; lia|]; try clear G.

Section NestPlus.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Hypothesis HG : od_shb E.

  Definition nhead_any (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> NODh E pi st' m' ->
      evt bsegs Q (NSTh E ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m').

  Lemma bn_hasnext : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1,
    NODp E pi st m1 -> frm0 xfc -> (pi < o_pos st <= n)%Z -> o_err st = 0%Z -> o_depth st = 2%Z -> o_alive st = true ->
    nhead_any Q (fun st' => st' = has_next bs idxs 2 st) ->
    evt bsegs Q (NSTp E 0x9a220 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1).
  Proof using OK HPI.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m1 INV FRM HP HE HD HA HK.
    nod_open INV. od_env OK. unfold nhead_any, ON_HEAD in HK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.

    ostep. ostep. if_true. ostep. ostep. ostep. gok. ostep. ostep. if_false. ostep. odnorm. ostep. gok. ostep. gok.
    ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep. ual. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2.
    assert (HN : has_next bs idxs 2 st =
                 if (tokT bs idxs (o_pos st) =? 93)%Z then o_setd (o_adv st 1) 1
                 else if (tokT bs idxs (o_pos st) =? 44)%Z then o_setd (o_adv st 1) 3 else o_sete (o_adv st 1) 3) by reflexivity.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.

    ostep. gok. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep. unz. ostep. gok. ostep. gok.
    ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. ostep. gok. ostep. ostep. gok. ostep. ostep. if_false. ostep. ostep. ostep. ostep.
      replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? 44)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
      eapply evt_eq; [| eapply (HK (o_setd (o_adv st 1) 3))]; [od_st_eq| symmetry; exact HN| exact FRM| nodh_close].
    -
      ostep. ostep. ostep.
      if_cases K2; zify_cond K2.
      +
        ostep. gok. ostep. ostep. ostep. if_false. ostep. ostep. ostep. ostep.
        replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? 44)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        eapply evt_eq; [| eapply (HK (o_sete (o_adv st 1) 3))]; [od_st_eq| symmetry; exact HN| exact FRM| nodh_close].
      +
        ostep. gok. ostep. ostep. gok. ostep. ostep. if_false. ostep. ostep. ostep. ostep. ostep.
        replace (c =? 93)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
        eapply evt_eq; [| eapply (HK (o_setd (o_adv st 1) 1))]; [od_st_eq| symmetry; exact HN| exact FRM| nodh_close].
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
    forall st' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> NODp E pi st' m' ->
      evt bsegs Q (NSTp E 0x9a220 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xt3 xt5 xt6 xF xfc m').

  Notation NSTl E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (NSTb E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
          (Z_to_bv 64 ((oa_F E + 208) / 8 + 2147450880)) xs5 (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) xs9 xt3 xt4 xt5 xt6 xF xfc m).

  Lemma bn_skip_err : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> NODp E pi st m1 -> (pi < o_pos st <= n)%Z ->
    nhead_any Q (fun st' => st' = o_sete st TAPE_ERROR) ->
    evt bsegs Q (NSTl E 0x9a32c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 2) xs9 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HPI.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 xF xfc m1 FRM INV HPP KE.
    nod_open INV. od_env OK. unfold nhead_any, ON_HEAD in KE.

    ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. gok. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep.
    eapply evt_eq; [| eapply (KE (o_sete st TAPE_ERROR))]; [od_st_eq| reflexivity| exact FRM| nodh_close].
  Qed.

  Lemma bn_skip_top : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st -> (pi < o_pos st)%Z -> frm0 xfc -> NODp E pi st m1 ->
    ((n <= o_pos st)%Z -> nhead_any Q (fun st' => st' = o_sete st TAPE_ERROR)) ->
    ((o_pos st < n)%Z -> forall xra' xa0' xa1' xa2' xa3' xa4' m', NODp E pi st m' ->
       evt bsegs Q (NSTl E 0x9a068 xra' xt0 xt1 xt2 xa0' xa1' xa2' xa3' xa4' xa5 xa6 xa7 (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                         xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m')) ->
    evt bsegs Q (NSTl E 0x99fe4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK HPI HG.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt5 xt6 xF xfc m1 SK HPP FRM INV KE KB.
    pose proof SK as (HP & HD & HE & HA & HB).
    pose proof INV as INV0.
    nod_open INV. od_env OK.
    rewrite HA in ITER.

    ostep. ostep. ostep. gok. ostep. ual. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. gok. ostep. ual. ostep. gok.
    ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep.

    od_opidx_inline HG ST.
    od_cur_mem ltac:(fun mm => assert (I' : NODp E pi st mm) by nod_close).

    ostep.
    if_cases KC; zify_cond KC.
    -
      specialize (KE ltac:(lia)).
      eapply evt_eq; [| eapply (bn_skip_err Q st); [exact FRM| exact I'| lia| exact KE]]. od_st_eq.
    - eapply evt_eq; [| eapply (KB ltac:(lia)); exact I']. od_st_eq.
  Qed.

  Lemma bn_skip_loop : forall (Q : machine_state -> Prop) (fuel : nat) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 2 st -> (pi < o_pos st)%Z -> (n - o_pos st <= Z.of_nat fuel)%Z -> frm0 xfc -> NODp E pi st m1 ->
    nskip_kn Q (fun st' => st' = skip_loop bs idxs fuel 2 st /\ o_err st' = 0%Z) ->
    nhead_any Q (fun st' => st' = skip_loop bs idxs fuel 2 st /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (NSTl E 0x99fe4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q fuel. induction fuel as [|f IH]; intros st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt5 xt6 xF xfc m1 SK HPP HF FRM INV KN KE.
    all: apply (bn_skip_top Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK HPP FRM INV).
    1,3: (intros HGE st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' E1 F' I';
          apply (KE st'); [split; [rewrite E1; symmetry; apply skip_loop_end2; exact HGE| rewrite E1; reflexivity]| exact F'| exact I']).
    - intros HLT. exfalso. lia.
    - intros HPN xra' xa0' xa1' xa2' xa3' xa4' m' I'. clear INV.
      pose proof SK as (HP & HD & HE & HA & HB).
      od_env OK.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_tokT_range E BOK (o_pos st)) as CR.
      pose proof (skip_loop_unf2 f st HPN) as UNF. cbv zeta in UNF.
      set (c := tokT bs idxs (o_pos st)) in *.

      assert (K_TOP : forall st2 yra ya0 ya1 ya2 ya3 ya4 mm,
                skip_loop bs idxs (S f) 2 st = skip_loop bs idxs f 2 st2 ->
                od_skip_ok bs idxs 2 st2 -> o_pos st2 = (o_pos st + 1)%Z -> NODp E pi st2 mm ->
                evt bsegs Q (NSTl E 0x9a1a8 yra xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 2) (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc mm)).
      { intros st2 yra ya0 ya1 ya2 ya3 ya4 mm EQ SK2 EP INV2.
        pose proof INV2 as INV20. nod_open INV2.

        ostep. ostep. if_true.
        eapply evt_eq; [| eapply (IH st2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2); try lia; try exact FRM; try exact INV20].
        + od_st_eq.
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 [E1 E2] F' I2. apply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I2].
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 [E1 E2] F' I2. apply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I2]. }

      assert (K_OPEN : is_open c = true -> forall yra ya0 ya2 ya3 ya4 mm, NODp E pi (o_adv st 1) mm ->
                evt bsegs Q (NSTl E 0x9a13c yra xt0 xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 2) (Z_to_bv 64 4)
                                  xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc mm)).
      { intros OP yra ya0 ya2 ya3 ya4 mm INV2. rewrite OP in UNF. clear OP.
        pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st + 1) SK HPN ltac:(lia)) as SK2.
        nod_open INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        ostep. gok. ostep. ostep. if_false. ostep. odnorm. ostep. odnorm. ostep. goks. ostep. ostep. if_false. ostep. ostep.
        eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st + 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| nod_close]].
        od_st_eq. }

      assert (K_CLOSE : is_open c = false -> is_close c = true -> forall yra ya0 ya2 ya3 ya4 mm, NODp E pi (o_adv st 1) mm ->
                evt bsegs Q (NSTl E 0x9a16c yra xt0 xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 2) (Z_to_bv 64 4)
                                  xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc mm)).
      { intros OP CL yra ya0 ya2 ya3 ya4 mm INV2. rewrite OP, CL in UNF. clear OP CL.
        nod_open INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        ostep. gok. ostep. ostep. if_false. ostep. odnorm. ostep. odnorm. ostep. goks. ostep. ostep. if_false. ostep. ostep.
        if_cases KD; zify_cond KD; odsig KD.
        -
          replace (o_depth st - 1 <=? 2)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
          eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1)))]; [od_st_eq| split; [symmetry; exact UNF| exact HE]| exact FRM| nod_close].
        -
          replace (o_depth st - 1 <=? 2)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
          pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st - 1) SK HPN ltac:(lia)) as SK2.
          ostep.
          eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| nod_close]].
          od_st_eq. }

      assert (K_OTHER : is_open c = false -> is_close c = false -> forall yra ya0 ya2 ya3 ya4 mm, NODp E pi (o_adv st 1) mm ->
                evt bsegs Q (NSTl E 0x9a1a0 yra xt0 xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 xa7 (Z_to_bv 64 2) (Z_to_bv 64 4)
                                  xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc mm)).
      { intros OP CL yra ya0 ya2 ya3 ya4 mm INV2. rewrite OP, CL in UNF. clear OP CL.
        pose proof (od_skip_ok_step bs idxs S1 2 st (o_depth st) SK HPN ltac:(lia)) as SK2.
        ostep. gok.
        eapply (K_TOP (o_adv st 1) _ _ _ _ _ _ _ UNF SK2); [reflexivity| exact INV2]. }
      nod_open I'.

      ostep. ostep. if_true. ostep. ostep. ostep. if_true. ostep. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2).
      fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2.
      set (off := tokI bs idxs (o_pos st)) in *.

      ostep. gok. ostep. ual. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok.
      ostep. ostep. ostep. unz. ostep. gok. ostep. gok. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep.
      od_cur_mem ltac:(fun mm => assert (INVA : NODp E pi (o_adv st 1) mm) by nod_close).
      clear IH K_TOP.
      unfold is_open, is_close, C_LBRACKET, C_LBRACE, C_RBRACKET, C_RBRACE in K_OPEN, K_CLOSE, K_OTHER.
      if_cases KZ; zify_cond KZ; odsig KZ.
      +
        ostep. ostep. if_cases K1; zify_cond K1.
        *
          eapply evt_eq; [| apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 125)) by lia; apply orb_true_r| exact INVA]]. od_st_eq.
        * ostep. ostep. if_cases K2; zify_cond K2.
          -- eapply evt_eq; [| apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA]]. od_st_eq.
          --
             eapply evt_eq; [| apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; apply orb_true_r| exact INVA]]. od_st_eq.
      +
        ostep. ostep. if_cases K1; zify_cond K1.
        *
          eapply evt_eq; [| apply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA]]. od_st_eq.
        * ostep. ostep. if_cases K2; zify_cond K2.
          -- eapply evt_eq; [| apply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA]]. od_st_eq.
          --
             ostep.
             eapply evt_eq; [| apply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 93)) by lia; reflexivity| exact INVA]]. od_st_eq.
  Qed.
End NestPlus.
