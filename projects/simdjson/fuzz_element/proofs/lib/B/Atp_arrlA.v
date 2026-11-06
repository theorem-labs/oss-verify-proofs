(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma tix_shr61' : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_type : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7 by (rewrite length_map; lia).
  rewrite <- le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Section ArrLeaves.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma tix_cps : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp i RA : Z)
      (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    AINV_A E m -> 0 <= i < ae_n E ->
    shb_cells m -> (forall m', munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    stk bsegs m (ae_lo E) sp -> ae_lo E + 16 <= sp -> sp <= ae_hi E -> sp mod 16 = 0 -> mem_inv bsegs m ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (xa1 xa3 xa4 : word), munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) sp ->
       evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_TAPE E + 8 * i)) xa1 (wz (ae_TAPE E)) xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_DOC E)) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_TIX_A) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros AI IR [G1 G2] SHZD ST LO HI S16 MI RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold ATP_TIX_A, SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof AI as (_ & _ & _ & DOCC & _).
    pose proof (munch_refl [(sp + -16, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step.

    chk0 SHZD (ae_DOC E). step. if_false.
    step. astep. astep.

    astep. astep.
    replace (0 <? ae_TAPE E) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (ae_TAPE E + 8 * i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    step. if_false.

    astep. astep. astep. astep. rewrite tix_shr61' by lia. step. if_false.

    step. if_dead1 by IR TS. step. if_dead1 by TS. astep. step. if_dead1 by T16 IR TS.

    step. step. release_frame FR ST sp. step.
    name_mem m1. replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply HK; [exact MU| exact WM| exact MI1| exact ST1].
  Qed.

  Lemma substr_cps : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp SV A n pos cnt r1 RA : Z)
      (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells bsegs m SV [C8 (wz A); C8 (wz n)] -> sp <= SV -> SV + 16 <= ae_hi E -> SV mod 8 = 0 ->
    0 < A -> 0 <= pos <= n -> A + n < 2^47 ->
    ((cnt = 18446744073709551615 /\ r1 = n - pos) \/ (0 <= cnt <= n - pos /\ r1 = cnt)) ->
    shb_cells m -> (forall m', munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> shz m' SV 16) ->
    stk bsegs m (ae_lo E) sp -> ae_lo E + 16 <= sp -> sp <= ae_hi E -> sp mod 16 = 0 -> mem_inv bsegs m ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (xa2 xa3 xa4 xa5 : word), munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) sp ->
       evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (A + pos)) (wz r1) xa2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz SV) (wz pos) (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_SUBSTR_A) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros SVC QS SH S8 A0 POS AN CNT [G1 G2] SHZS ST LO HI S16 MI RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    unfold ATP_SUBSTR_A, SEGTOP_A, USTACK_TOP in *.
    pose proof (munch_refl [(sp + -16, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. astep.

    chk0 SHZS (SV + 8). step. if_false.
    step. step. if_dead1 by POS.

    chk0 SHZS SV. step. if_false.
    step. astep. step. if_dead1 by POS.
    astep. astep.
    replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
    first [ replace (pos + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (A + pos <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
    cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false.

    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (FIN : forall (av xa4 xa5 : word), av = wz r1 ->
        evt bsegs K (MS (mkR (wz RA) (wz (sp + -16)) gp (wz TPV) t0 t1 t2 s0 s1 (wz (pos + A)) av (wz cnt) (wz n) xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz 0xb691c) fc None mx (seg_rom bsegs))) end.
    { intros av xa4 xa5 ->. step. step. release_frame FR ST sp. step.
      name_mem m1. replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
      lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
      replace (pos + A) with (A + pos) by lia.
      eapply HK; [exact MU| exact WM| exact MI1| exact ST1]. }
    step. if_cases KC; zify_cond KC; rewrite ?land64_mod in KC.
    -
      eapply evt_eq; [| eapply FIN]; [atp_st_eq| ]. destruct CNT as [[C1 R1]|[C1 R1]]; subst r1; [reflexivity| exfalso; clear - KC C1 POS AN A0; lia].
    -
      step. eapply evt_eq; [| eapply FIN]; [atp_st_eq| ]. destruct CNT as [[C1 R1]|[C1 R1]]; subst r1; [exfalso; clear - KC C1 POS AN A0; lia| reflexivity].
  Qed.

  Lemma arr_digit_loopB : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (rest : list Z)
      (Pr Lr tz spv out node PB NPB : Z) (x1 x3 wa7 s6 s7 s8 s9 s10 s11 : word),
    bytes_at bsegs m Pr (map (Z_to_bv 8) rest) -> Forall (fun c => 0 <= c < 256) rest -> Lr = zlength rest ->
    0 < Pr -> Pr + Lr < 2^47 -> tz = - Lr -> mem_inv bsegs m ->
    acc bsegs m PB NPB -> PB <= Pr -> Pr + Lr <= PB + NPB ->
    (forall (code : Z) (xa0 xa1 xa2 xa4 xs2 xs3 xt4 xt5 xt6 : word), (code = 17 \/ code = 19 \/ code = 22) ->
       evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                          xa0 xa1 xa2 (wz tz) xa4 (wz 47) (wz 9) wa7
                          xs2 xs3 (wz 2147450880) (wz code) s6 s7 s8 s9 s10 s11 (wz 48) xt4 xt5 xt6)
                     F (wz 0xb8fbc) fc None m (seg_rom bsegs))) ->
    (forall (tok c3 : Z) (xa0 xa1 xa2 xa4 xs3 xt4 xt5 xt6 : word),
       0 <= tok <= Lr -> (forall j, (j < Z.to_nat tok)%nat -> nth j rest 0 <> 47) ->
       ((c3 = 47 /\ tok < Lr /\ nth (Z.to_nat tok) rest 0 = 47) \/ (c3 <> 47 /\ tok = Lr)) -> 0 <= c3 < 256 ->
       evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                          xa0 xa1 xa2 (wz tz) xa4 (wz 47) (wz 9) wa7
                          (wz tok) xs3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 (wz 48) xt4 xt5 xt6)
                     F (wz 0xb8f18) fc None m (seg_rom bsegs))) ->
    forall (n : nat) (cnt : Z) (xs3 xt5 xt6 : word),
      0 <= cnt < Lr -> Lr - cnt <= Z.of_nat n -> (forall j, (j < Z.to_nat cnt)%nat -> nth j rest 0 <> 47) ->
      evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                         (wz Pr) (wz (Pr + cnt)) (wz (- cnt)) (wz tz) (wz 1) (wz 47) (wz 9) wa7
                         (wz Lr) xs3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5 xt6)
                    F (wz 0xb8e80) fc None m (seg_rom bsegs)).
  Proof.
    intros K m F fc rest Pr Lr tz spv out node PB NPB x1 x3 wa7 s6 s7 s8 s9 s10 s11 RB RF EL P0 PL TZ MI ACC PB0 PB1 XERR XTOK.
    induction n as [|n IH]; intros cnt xs3 xt5 xt6 CR FUEL NOSL; [lia|].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zlength_nonneg rest) as ZL0.
    set (c := nth (Z.to_nat cnt) rest 0).
    assert (CB : 0 <= c < 256) by (subst c; apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    pose proof (zbytes_read1 m Pr rest cnt RB ltac:(lia)) as RD. fold c in RD.

    step. if_dead1 by CR.
    astep. replace (Pr + cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false.
    step. if_dead1 by P0.

    assert (J_ec : forall xt5' xt6' : word,
      evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                         (wz Pr) (wz (Pr + cnt)) (wz (- cnt)) (wz tz) (wz 1) (wz 47) (wz 9) wa7
                         (wz Lr) xs3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5' xt6')
                    F (wz 0xb8ea4) fc None m (seg_rom bsegs))).
    { intros xt5' xt6'.

      astep. step. if_cases KS; zify_cond KS.
      {
        step. if_cases KZ.
        - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
        - astep. eapply evt_eq; [| eapply (XTOK cnt 47)];
            [atp_st_eq| lia| exact NOSL| left; subst c; split; [reflexivity| split; [lia| exact KS]]| lia]. }

      step. if_dead1 by P0 CR.
      astep. astep. step. if_cases KD.
      {   astep. step. eapply evt_eq; [| eapply (XERR 17)]; [atp_st_eq| lia]. }

      assert (AT118 : forall xt5'' xt6'' : word,
        evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                           (wz Pr) (wz (Pr + cnt)) (wz (- cnt)) (wz tz) (wz 1) (wz 47) (wz 9) wa7
                           (wz Lr) xs3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5'' xt6'')
                      F (wz 0xb8ed0) fc None m (seg_rom bsegs))).
      { intros xt5'' xt6''.

        astep. astep. astep. step. if_cases KO.
        {   astep. eapply evt_eq; [| eapply (XERR 19)]; [atp_st_eq| lia]. }
        assert (NOSL1 : forall j, (j < Z.to_nat (cnt + 1))%nat -> nth j rest 0 <> 47).
        { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat cnt)) as [->|NE]; [exact KS| apply NOSL; lia]. }

        astep. astep. astep. astep. astep. step. if_cases KL; zify_cond KL; rewrite ?land64_mod in KL.
        -
          assert (NE : cnt + 1 <> Lr) by (intros EQ; apply KL; rewrite TZ, <- EQ; f_equal; lia).
          eapply evt_eq; [| eapply (IH (cnt + 1))]; [atp_st_eq| lia| lia| exact NOSL1].
        -
          assert (EQ : cnt + 1 = Lr) by (rewrite TZ in KL; lia).
          step. eapply evt_eq; [| eapply (XTOK Lr c)];
            [atp_st_eq| lia| rewrite <- EQ; exact NOSL1| right; split; [exact KS| reflexivity]| lia]. }

      step. if_cases KZ2.
      { eapply evt_eq; [| eapply AT118]; [atp_st_eq]. }

      pose proof (zbytes_read1 m Pr rest 0 RB ltac:(lia)) as RDZ. rewrite Z.add_0_r in RDZ.
      assert (C0B : 0 <= nth (Z.to_nat 0) rest 0 < 256) by (apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
      assert (J110 : forall xt5'' xt6'' : word,
        evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz node)
                           (wz Pr) (wz (Pr + cnt)) (wz (- cnt)) (wz tz) (wz 1) (wz 47) (wz 9) wa7
                           (wz Lr) xs3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5'' xt6'')
                      F (wz 0xb8ec8) fc None m (seg_rom bsegs))).
      { intros xt5'' xt6''.

        astep. step. if_cases KZ3.
        - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
        - eapply evt_eq; [| eapply AT118]; [atp_st_eq]. }

      destruct (acc_read1 m PB NPB Pr ACC ltac:(lia)) as (b1 & RDS1 & OK1).
      destruct (sh_ok_cases b1 Pr OK1) as [-> | (k1 & -> & K1 & KM1)].
      - step. shz_norm. step. if_false. eapply evt_eq; [| eapply J110]; [atp_st_eq].
      - step. rewrite (sxb_small7 k1) by lia. step. if_lia. step. if_lia. eapply evt_eq; [| eapply J110]; [atp_st_eq]. }

    destruct (acc_read1 m PB NPB (Pr + cnt) ACC ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 (Pr + cnt) OK0) as [-> | (k0 & -> & K0 & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J_ec]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_lia. astep. step. if_lia. step. eapply evt_eq; [| eapply J_ec]; [atp_st_eq].
  Qed.

  Lemma arr_iter_loopB : forall (K : machine_state -> Prop) (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (d : nat) (e cc spv out : Z)
      (x3 x5 x6 x7 x15 x16 x17 s10 s11 x28 x29 x30 x31 : word),
    e + 1 <= ae_n E - 1 ->
    (forall m, munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> AINV_A E m) ->
    (forall m, munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> shb_cells m) ->
    (forall m, munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> shz m (ae_DOC E) 16) ->
    (forall m, munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> shz m (ae_TAPE E) (8 * ae_n E)) ->
    ae_lo E + 16 <= spv -> spv <= ae_hi E -> spv mod 16 = 0 ->
    (forall (it j' : Z) (m : mem) (x1 xa0 xa1 xa2 xa3 xa4 xs2 : word),
       munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) spv ->
       elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
       evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) x5 x6 x7 (wz out) (wz (ae_DOC E)) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                          xs2 (wz it) (wz e) (wz 32) (wz 2147450880) (wz 4294967295) (wz 67240448) (wz 4294967297) s10 s11 x28 x29 x30 x31)
                     F (wz 0xb9878) fc None m (seg_rom bsegs))) ->
    (forall (m : mem) (x1 xa0 xa1 xa2 xa3 xa4 xs2 xs3 : word),
       munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) spv ->
       evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) x5 x6 x7 (wz out) (wz (ae_DOC E)) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                          xs2 xs3 (wz e) (wz 32) (wz 2147450880) (wz 4294967295) (wz 67240448) (wz 4294967297) s10 s11 x28 x29 x30 x31)
                     F (wz 0xb9794) fc None m (seg_rom bsegs))) ->
    forall (n : nat) (it c' : Z) (m : mem) (x1 xa0 xa1 xa2 xa3 xa4 xs2 : word),
      munch [(spv + -16, spv)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) spv ->
      tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt bsegs K (MS (mkR x1 (wz spv) x3 (wz TPV) x5 x6 x7 (wz out) (wz (ae_DOC E)) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                         xs2 (wz it) (wz e) (wz 32) (wz 2147450880) (wz 4294967295) (wz 67240448) (wz 4294967297) s10 s11 x28 x29 x30 x31)
                    F (wz 0xb97ec) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros K m0 F fc d e cc spv out x3 x5 x6 x7 x15 x16 x17 s10 s11 x28 x29 x30 x31 EN AIW SHBW SHZDW SHZTW LO HI S16 XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' m x1 xa0 xa1 xa2 xa3 xa4 xs2 MU0 WM0 MI ST TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct (array_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').

    astep. step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j' m)]; [atp_st_eq| exact MU0| exact WM0| exact MI| exact ST| exact EL| exact I0| lia]. }
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E it) < 256) by (unfold ttype; lia).

    step. step. step. clear MU WM.
    eapply (tix_cps K m F fc spv it 0xb9800); [exact (AIW m MU0 WM0)| lia| exact (SHBW m MU0 WM0)| | exact ST| lia| lia| exact S16| exact MI| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU0 MU') (wmono_trans bsegs _ _ _ WM0 WM')). }
    intros m1 ya1 ya3 ya4 MU01 WM01 MI1 ST1.
    pose proof (munch_trans _ _ _ _ MU0 MU01) as MU1. pose proof (wmono_trans bsegs _ _ _ WM0 WM01) as WM1. clear MU01 WM01 MU0 WM0 MI ST.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (AIW m1 MU1 WM1) as (TAPEB1 & _ & _ & _ & _).
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) it TAPEB1 ltac:(lia) TIR) as RDB.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB1 ltac:(lia)) as RDT.
    pose proof (SHZTW m1 MU1 WM1) as SHZT1.

    chk0 SHZT1 (ae_TAPE E + 8 * it). step. if_false.
    astep. astep.

    assert (NEXT : forall (pc : Z) (mx : mem) (y1 ya0 ya1' ya2 ya3' ya4' : word), (pc = 0xb982c \/ pc = 0xb9864 \/ pc = 0xb9870) ->
      munch [(spv + -16, spv)] m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) spv ->
      evt bsegs K (MS (mkR y1 (wz spv) x3 (wz TPV) x5 x6 x7 (wz out) (wz (ae_DOC E)) ya0 ya1' ya2 ya3' ya4' x15 x16 x17
                         (wz (bv_unsigned xs2 + -1)) (wz j') (wz e) (wz 32) (wz 2147450880) (wz 4294967295) (wz 67240448) (wz 4294967297) s10 s11 x28 x29 x30 x31)
                    F (wz pc) fc None mx (seg_rom bsegs))).
    { intros pc mx y1 ya0 ya1' ya2 ya3' ya4' PC MUx WMx MIx STx.
      pose proof (munch_refl ([] : list (Z * Z)) mx) as MU'. pose proof (wmono_refl bsegs mx) as WM'.
      destruct PC as [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply (IH j' (c' - 1) mx); [exact MUx| exact WMx| exact MIx| exact STx| exact TI'| exact KL| lia| lia]
        | step; eapply XNF; [exact MUx| exact WMx| exact MIx| exact STx] ]). }

    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0xb9870 m1)]; [atp_st_eq| do 2 right; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0xb982c m1)]; [atp_st_eq| left; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1]).
    -
      unfold t_str in TY. rewrite TY.
      step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0xb9870 m1)]; [atp_st_eq| do 2 right; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1].
    -
      unfold t_arr in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.

      step. step. step. clear MU WM.
      eapply (tix_cps K m1 F fc spv it 0xb984c); [exact (AIW m1 MU1 WM1)| lia| exact (SHBW m1 MU1 WM1)| | exact ST1| lia| lia| exact S16| exact MI1| lia| reflexivity|].
      { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU1 MU') (wmono_trans bsegs _ _ _ WM1 WM')). }
      intros m2 za1 za3 za4 MU12 WM12 MI2 ST2.
      pose proof (munch_trans _ _ _ _ MU1 MU12) as MU2. pose proof (wmono_trans bsegs _ _ _ WM1 WM12) as WM2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
      pose proof (AIW m2 MU2 WM2) as (TAPEB2 & _ & _ & _ & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB2 ltac:(lia)) as RDT2.
      pose proof (SHZTW m2 MU2 WM2) as SHZT2.
      chk0 SHZT2 (ae_TAPE E + 8 * it). step. if_false.
      step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb9864 m2)]; [atp_st_eq| right; left; reflexivity| exact MU2| exact WM2| exact MI2| exact ST2].
    -
      unfold t_obj in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.
      step. step. step. clear MU WM.
      eapply (tix_cps K m1 F fc spv it 0xb984c); [exact (AIW m1 MU1 WM1)| lia| exact (SHBW m1 MU1 WM1)| | exact ST1| lia| lia| exact S16| exact MI1| lia| reflexivity|].
      { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU1 MU') (wmono_trans bsegs _ _ _ WM1 WM')). }
      intros m2 za1 za3 za4 MU12 WM12 MI2 ST2.
      pose proof (munch_trans _ _ _ _ MU1 MU12) as MU2. pose proof (wmono_trans bsegs _ _ _ WM1 WM12) as WM2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
      pose proof (AIW m2 MU2 WM2) as (TAPEB2 & _ & _ & _ & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB2 ltac:(lia)) as RDT2.
      pose proof (SHZTW m2 MU2 WM2) as SHZT2.
      chk0 SHZT2 (ae_TAPE E + 8 * it). step. if_false.
      step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb9864 m2)]; [atp_st_eq| right; left; reflexivity| exact MU2| exact WM2| exact MI2| exact ST2].
  Qed.

End ArrLeaves.
