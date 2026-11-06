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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Sj_akit Od_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Notation PST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 xs8 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (oa_F E + 200))
           (Z_to_bv 64 1) (Z_to_bv 64 ((oa_F E + 192) / 8)) xs4 (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) xs6
           (Z_to_bv 64 2147450880) xs8 (Z_to_bv 64 4)
           (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

Ltac od_opidx_inline HG ST :=
  lazymatch goal with
  | MU : munch _ ?m0 ?m, WM : wmono bsegs ?m0 ?m |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      let G1 := fresh "G1" in let G2 := fresh "G2" in
      destruct (HG m MU WM) as [G1 G2]; unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2;
      zstep; carve_frame 16%nat ST;

      ostep; lstep; ostep; ostep; ostep; ostep; ostep; ostep; ostep; if_false;

      ostep; ostep; ostep; odnorm; ostep; ostep; unz; ostep; if_false;

      ostep; ostep; ostep; ostep; ostep;
      match goal with
      | |- context [Z.shiftr ?x 62] =>
          replace (Z.shiftr x 62) with 0%Z by (symmetry; apply Z.shiftr_eq_0; [lia| apply Z.log2_lt_pow2; lia])
      end;
      if_false;

      ostep; utrap; ostep; utrap; ostep; ual; ostep; if_false; ostep; ostep; ostep;
      clear G1 G2;
      lazymatch type of ST with
      | stk _ _ _ (?S + -16)%Z =>
          match goal with
          | FRX : rw_cells bsegs _ (S + -16)%Z _ |- _ => release_frame FRX ST S
          end
      end
  end.

Section Plus.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HG : od_shb E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition head_any (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> ODINVp E v352 st' m' ->
      evt bsegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (oa_F E + 200))
                        (Z_to_bv 64 1) xs5 xs6 (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m').

  Lemma od_hasnext : forall (Q : machine_state -> Prop) st v352 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 xt3 xt4 xt5 xt6 xF xfc m1,
    ODINVp E v352 st m1 -> frm0 xfc -> (1 <= o_pos st <= n)%Z -> o_err st = 0%Z -> o_depth st = 1%Z -> o_alive st = true ->
    head_any Q (fun st' => st' = has_next bs idxs 1 st) ->
    evt bsegs Q (PST E 0x9aa60 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 (Z_to_bv 64 (oa_F E + 228)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q st v352 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 xt3 xt4 xt5 xt6 xF xfc m1 INV FRM HP HE HD HA HK.
    od_open_inv INV. od_env OK. unfold head_any, OD_HEAD in HK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    rewrite HD in ITER.

    ostep. ostep. if_true. ostep. ostep. ostep. ostep. uok.
    ostep. ostep. if_false. ostep. odnorm. ostep. ostep. ostep. ostep. ostep.
    if_true.

    ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. uok.
    ostep. ostep. if_true. ostep. ostep. ual. ostep. ostep. if_true.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD1).
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) ltac:(eassumption) ltac:(lia)) as RD2).
    fold (tokT bs idxs (o_pos st)) in RD2.
    assert (HN : has_next bs idxs 1 st =
                 if (tokT bs idxs (o_pos st) =? 93)%Z then o_setd (o_adv st 1) 0
                 else if (tokT bs idxs (o_pos st) =? 44)%Z then o_setd (o_adv st 1) 2 else o_sete (o_adv st 1) 3) by reflexivity.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.

    ochkn. ostep. odnorm. ostep. ostep. uok.
    ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ochkn. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. if_false. ostep. ostep. ostep.
      replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? 44)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
      eapply (HK (o_setd (o_adv st 1) 2)); [symmetry; exact HN| exact FRM| od_close_inv].
    -
      ostep. zstep.
      if_cases K2; zify_cond K2.
      +
        ostep. uok. ostep. ostep. ostep. if_false. ostep. ostep. ostep.
        replace (c =? 93)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? 44)%Z with false in HN by (symmetry; apply Z.eqb_neq; lia).
        eapply (HK (o_sete (o_adv st 1) 3)); [symmetry; exact HN| exact FRM| od_close_inv].
      +
        ostep. uok. ostep. ostep. if_false. ostep. ostep. ostep.
        replace (c =? 93)%Z with true in HN by (symmetry; apply Z.eqb_eq; lia).
        eapply (HK (o_setd (o_adv st 1) 0)); [symmetry; exact HN| exact FRM| od_close_inv].
  Qed.

  Definition skip_kn (Q : machine_state -> Prop) (P : ost -> Prop) : Prop :=
    forall st' v352 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 xt3 xt4 xt5 xt6 xF xfc m',
      P st' -> frm0 xfc -> ODINVp E v352 st' m' ->
      evt bsegs Q (PST E 0x9aa60 xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs6 (Z_to_bv 64 (oa_F E + 228)) xt3 xt4 xt5 xt6 xF xfc m').

  Lemma od_skip_top : forall (Q : machine_state -> Prop) st v352 xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 1 st -> frm0 xfc -> ODINVp E v352 st m1 ->
    ((n <= o_pos st)%Z -> head_any Q (fun st' => st' = o_sete st TAPE_ERROR)) ->
    ((o_pos st < n)%Z -> forall xra' xa0' xa1' xa2' xa3' xa4' xs8' m',
       ODINVp E v352 st m' ->
       evt bsegs Q (PST E 0x9a898 xra' xt1 xt2 xa0' xa1' xa2' xa3' xa4' xa5 xa6
                        (Z_to_bv 64 ((oa_F E + 208) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) xs8'
                        xt3 xt4 xt5 xt6 xF xfc m')) ->
    evt bsegs Q (PST E 0x9a81c xra xt1 xt2 (Z_to_bv 64 (oa_F E + 208)) xa1 xa2 xa3 xa4 xa5 xa6
                     (Z_to_bv 64 ((oa_F E + 208) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 228))
                     xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HG.
    intros Q st v352 xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1 SK FRM INV KE KB.
    pose proof SK as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    rewrite HA in ITER.

    ostep. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ochk. ostep. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_false.
    ostep. odnorm. ostep.
    od_opidx_inline HG ST.

    zstep.
    if_cases KC; zify_cond KC.
    -
      specialize (KE ltac:(lia)). unfold head_any, OD_HEAD in KE.
      ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. uok.
      ostep. ostep. ostep. if_true. ostep. ostep. ostep.
      eapply (KE (o_sete st TAPE_ERROR)); [reflexivity| exact FRM| od_close_inv].
    - eapply evt_eq; [| eapply (KB ltac:(lia)); od_close_inv]. od_st_eq.
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

  Notation LST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs8 xt3 xt4 xt5 xt6 xF xfc m :=
    (PST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6
         (Z_to_bv 64 ((oa_F E + 208) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 192) / 8 + 2147450880)) xs8 xt3 xt4 xt5 xt6 xF xfc m).

  Lemma od_skip_loop : forall (Q : machine_state -> Prop) (fuel : nat) st v352 xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1,
    od_skip_ok bs idxs 1 st -> (n - o_pos st <= Z.of_nat fuel)%Z -> frm0 xfc -> ODINVp E v352 st m1 ->
    skip_kn Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = 0%Z) ->
    head_any Q (fun st' => st' = skip_loop bs idxs fuel 1 st /\ o_err st' = TAPE_ERROR) ->
    evt bsegs Q (LST E 0x9a81c xra xt1 xt2 (Z_to_bv 64 (oa_F E + 208)) xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (oa_F E + 228))
                     xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HG HLAST.
    intros Q fuel. induction fuel as [|f IH]; intros st v352 xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1 SK HF FRM INV KN KE.
    all: apply (od_skip_top Q st v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 SK FRM INV).
    1,3: (intros HGE st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' E1 F' I';
          eapply (KE st'); [split; [rewrite E1; symmetry; apply skip_loop_end; exact HGE| rewrite E1; reflexivity]| exact F'| exact I']).
    - intros HLT. exfalso. lia.
    - intros HPN xra' xa0' xa1' xa2' xa3' xa4' xs8' m' INV'. clear INV.
      pose proof SK as (HP & HD & HE & HA & HB).
      od_env OK.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_tokT_range E BOK (o_pos st)) as CR.
      pose proof (skip_loop_unf f st HPN) as UNF. cbv zeta in UNF.
      set (c := tokT bs idxs (o_pos st)) in *.

      assert (K_TOP : forall st2 xra2 ya0 ya1 ya2 ya3 ya4 mm,
                skip_loop bs idxs (S f) 1 st = skip_loop bs idxs f 1 st2 ->
                od_skip_ok bs idxs 1 st2 -> o_pos st2 = (o_pos st + 1)%Z -> ODINVp E v352 st2 mm ->
                evt bsegs Q (LST E 0x9a9e0 xra2 xt1 xt2 ya0 ya1 ya2 ya3 ya4 xa5 xa6 (Z_to_bv 64 (oa_F E + 228))
                                 xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros st2 xra2 ya0 ya1 ya2 ya3 ya4 mm EQ SK2 EP INV2.
        pose proof INV2 as INV20. od_open_inv INV2.
        ostep. ostep. if_true. ostep. ostep.
        eapply evt_eq; [| eapply (IH st2 v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm SK2); try lia; try exact FRM; try exact INV20].
        + od_st_eq.
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m'' [E1 E2] F' I'. eapply (KN st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I'].
        + intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m'' [E1 E2] F' I'. eapply (KE st'); [split; [rewrite EQ; exact E1| exact E2]| exact F'| exact I']. }

      assert (K_OPEN : is_open c = true -> forall ya0 ya2 ya3 ya4 mm, ODINVp E v352 (o_adv st 1) mm ->
                evt bsegs Q (LST E 0x9a970 xra' xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 (Z_to_bv 64 (oa_F E + 228))
                                 xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP ya0 ya2 ya3 ya4 mm INV2. rewrite OP in UNF.
        pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st + 1) SK HPN ltac:(lia)) as SK2.
        od_open_inv INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        ostep. uok. ostep. ostep. if_false. ostep. odnorm. ostep. odnorm. ostep.
        if_cases G; zify_cond G; odsig G; [|exfalso; lia]. clear G.
        ostep. ostep. if_false. ostep. ostep.
        eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st + 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
        od_st_eq. }

      assert (K_CLOSE : is_open c = false -> is_close c = true -> forall ya0 ya2 ya3 ya4 mm, ODINVp E v352 (o_adv st 1) mm ->
                evt bsegs Q (LST E 0x9a9a0 xra' xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 (Z_to_bv 64 (oa_F E + 228))
                                 xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP CL ya0 ya2 ya3 ya4 mm INV2. rewrite OP, CL in UNF.
        od_open_inv INV2. cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo] in ITER.

        ostep. uok. ostep. ostep. if_false. ostep. odnorm. ostep. odnorm. ostep.
        if_cases G; zify_cond G; odsig G; [|exfalso; lia]. clear G.
        ostep. ostep. if_false. ostep. ostep. ostep.
        if_cases KD; zify_cond KD; odsig KD.
        -
          replace (o_depth st - 1 <=? 1)%Z with true in UNF by (symmetry; apply Z.leb_le; lia).
          eapply evt_eq; [| eapply (KN (o_setd (o_adv st 1) (o_depth st - 1))); [split; [symmetry; exact UNF| exact HE]| exact FRM| od_close_inv]].
          od_st_eq.
        - replace (o_depth st - 1 <=? 1)%Z with false in UNF by (symmetry; apply Z.leb_gt; lia).
          pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st - 1) SK HPN ltac:(lia)) as SK2.
          ostep.
          eapply evt_eq; [| eapply (K_TOP (o_setd (o_adv st 1) (o_depth st - 1)) _ _ _ _ _ _ _ UNF SK2); [reflexivity| od_close_inv]].
          od_st_eq. }

      assert (K_OTHER : is_open c = false -> is_close c = false -> forall ya0 ya2 ya3 ya4 mm, ODINVp E v352 (o_adv st 1) mm ->
                evt bsegs Q (LST E 0x9a9d8 xra' xt1 xt2 ya0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st + 4)) ya2 ya3 ya4 xa5 xa6 (Z_to_bv 64 (oa_F E + 228))
                                 xt3 xt4 xt5 xt6 xF xfc mm)).
      { intros OP CL ya0 ya2 ya3 ya4 mm INV2. rewrite OP, CL in UNF.
        pose proof (od_skip_ok_step bs idxs S1 1 st (o_depth st) SK HPN ltac:(lia)) as SK2.
        ostep. uok.
        eapply (K_TOP (o_adv st 1) _ _ _ _ _ _ _ UNF SK2); [reflexivity| exact INV2]. }
      od_open_inv INV'.

      ostep. ostep. ostep. if_true. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. uok.
      ostep. ostep. if_true. ostep. ostep. ostep. uok. ostep. ual. ostep. if_true.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD1).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st)) ltac:(eassumption) ltac:(lia)) as RD2).
      fold (tokT bs idxs (o_pos st)) in RD2. fold c in RD2.
      set (off := tokI bs idxs (o_pos st)) in *.

      ochkn. ostep. odnorm. ostep. ostep. uok.
      ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
      ochkn. ostep. odnorm. ostep. zstep.
      od_cur_mem ltac:(fun mm => assert (INVA : ODINVp E v352 (o_adv st 1) mm) by od_close_inv).
      clear IH K_TOP.
      unfold is_open, is_close, C_LBRACKET, C_LBRACE, C_RBRACKET, C_RBRACE in K_OPEN, K_CLOSE, K_OTHER.
      if_cases KZ; zify_cond KZ; odsig KZ.
      +
        zstep. zstep. if_cases K1; zify_cond K1.
        *
          eapply evt_eq; [| eapply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 125)) by lia; apply orb_true_r| exact INVA]].
          od_st_eq.
        * zstep. zstep. if_cases K2; zify_cond K2.
          -- eapply evt_eq; [| eapply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA]].
             od_st_eq.
          --
             eapply evt_eq; [| eapply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 123)) by lia; apply orb_true_r| exact INVA]].
             od_st_eq.
      +
        zstep. zstep. if_cases K1; zify_cond K1.
        *
          eapply evt_eq; [| eapply K_OPEN; [rewrite (proj2 (Z.eqb_eq c 91)) by lia; reflexivity| exact INVA]].
          od_st_eq.
        * zstep. zstep. if_cases K2; zify_cond K2.
          -- eapply evt_eq; [| eapply K_OTHER; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| exact INVA]].
             od_st_eq.
          --
             zstep.
             eapply evt_eq; [| eapply K_CLOSE; [rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity| rewrite (proj2 (Z.eqb_eq c 93)) by lia; reflexivity| exact INVA]].
             od_st_eq.
  Qed.
End Plus.
