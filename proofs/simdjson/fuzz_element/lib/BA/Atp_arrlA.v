(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA.
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
  bytes_at asegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes asegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read asegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7 by (rewrite length_map; lia).
  rewrite <- le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Section ArrLoops.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma arr_digit_loopA : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (rest : list Z)
      (Pr Lr tz spv out PB NPB : Z) (x1 x3 xa1 wa7 s7 s8 s9 s10 s11 : word),
    bytes_at asegs m Pr (map (Z_to_bv 8) rest) -> Forall (fun c => 0 <= c < 256) rest -> Lr = zlength rest ->
    0 < Pr -> Pr + Lr < 2^47 -> tz = - Lr -> mem_inv asegs m ->
    acc asegs m PB NPB -> PB <= Pr -> Pr + Lr <= PB + NPB ->
    (forall (code : Z) (xa0 xa2 xa4 xs5 xs6 xt4 xt5 xt6 : word), (code = 17 \/ code = 19 \/ code = 22) ->
       evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                          xa0 xa1 xa2 (wz tz) xa4 (wz 47) (wz 9) wa7
                          (wz code) (wz 2147450880) (wz Lr) xs5 xs6 s7 s8 s9 s10 s11 (wz 48) xt4 xt5 xt6)
                     F (wz 0xb6b80) fc None m (seg_rom asegs))) ->
    (forall (tok c3 : Z) (xa0 xa2 xa4 xt4 xt5 xt6 : word),
       0 <= tok <= Lr -> (forall j, (j < Z.to_nat tok)%nat -> nth j rest 0 <> 47) ->
       ((c3 = 47 /\ tok < Lr /\ nth (Z.to_nat tok) rest 0 = 47) \/ (c3 <> 47 /\ tok = Lr)) -> 0 <= c3 < 256 ->
       evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                          xa0 xa1 xa2 (wz tz) xa4 (wz 47) (wz 9) wa7
                          (wz 22) (wz 2147450880) (wz Lr) (wz c3) (wz tok) s7 s8 s9 s10 s11 (wz 48) xt4 xt5 xt6)
                     F (wz 0xb6bd4) fc None m (seg_rom asegs))) ->
    forall (n : nat) (cnt : Z) (xa4 xs5 xs6 xt5 xt6 : word),
      0 <= cnt < Lr -> Lr - cnt <= Z.of_nat n -> (forall j, (j < Z.to_nat cnt)%nat -> nth j rest 0 <> 47) ->
      evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                         (wz (Pr + cnt)) xa1 (wz (- cnt)) (wz tz) xa4 (wz 47) (wz 9) wa7
                         (wz 22) (wz 2147450880) (wz Lr) xs5 xs6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5 xt6)
                    F (wz 0xb6aec) fc None m (seg_rom asegs)).
  Proof.
    intros K m F fc rest Pr Lr tz spv out PB NPB x1 x3 xa1 wa7 s7 s8 s9 s10 s11 RB RF EL P0 PL TZ MI ACC PB0 PB1 XERR XTOK.
    induction n as [|n IH]; intros cnt xa4 xs5 xs6 xt5 xt6 CR FUEL NOSL; [lia|].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    set (c := nth (Z.to_nat cnt) rest 0).
    assert (CB : 0 <= c < 256) by (subst c; apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    pose proof (zbytes_read1 m Pr rest cnt RB ltac:(lia)) as RD. fold c in RD.

    assert (J74 : forall xt5' xt6' : word,
      evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                         (wz (Pr + cnt)) xa1 (wz (- cnt)) (wz tz) xa4 (wz 47) (wz 9) wa7
                         (wz 22) (wz 2147450880) (wz Lr) xs5 xs6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5' xt6')
                    F (wz 0xb6afc) fc None m (seg_rom asegs))).
    { intros xt5' xt6'.

      astep. step. if_cases KS; zify_cond KS.
      {
        step. if_cases KZ.
        - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
        - astep. step. eapply evt_eq; [| eapply (XTOK cnt 47)];
            [atp_st_eq| lia| exact NOSL| left; subst c; split; [reflexivity| split; [lia| exact KS]]| lia]. }

      astep. astep. step. if_cases KD.
      {   astep. step. eapply evt_eq; [| eapply (XERR 17)]; [atp_st_eq| lia]. }

      assert (AT9c : forall xt5'' xt6'' : word,
        evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                           (wz (Pr + cnt)) xa1 (wz (- cnt)) (wz tz) xa4 (wz 47) (wz 9) wa7
                           (wz 22) (wz 2147450880) (wz Lr) (wz c) xs6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5'' xt6'')
                      F (wz 0xb6b24) fc None m (seg_rom asegs))).
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
          step. step. eapply evt_eq; [| eapply (XTOK Lr c)];
            [atp_st_eq| lia| rewrite <- EQ; exact NOSL1| right; split; [exact KS| reflexivity]| lia]. }

      step. if_cases KZ2.
      { eapply evt_eq; [| eapply AT9c]; [atp_st_eq]. }

      pose proof (zbytes_read1 m Pr rest 0 RB ltac:(lia)) as RDZ. rewrite Z.add_0_r in RDZ.
      assert (C0B : 0 <= nth (Z.to_nat 0) rest 0 < 256) by (apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
      assert (J94 : forall xt5'' xt6'' : word,
        evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 10) (wz (Pr / 8 + 2147450880)) (wz (Pr mod 8)) (wz out) (wz Pr)
                           (wz (Pr + cnt)) xa1 (wz (- cnt)) (wz tz) xa4 (wz 47) (wz 9) wa7
                           (wz 22) (wz 2147450880) (wz Lr) (wz c) xs6 s7 s8 s9 s10 s11 (wz 48) (wz (Pr + cnt)) xt5'' xt6'')
                      F (wz 0xb6b1c) fc None m (seg_rom asegs))).
      { intros xt5'' xt6''.

        astep. step. if_cases KZ3.
        - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
        - eapply evt_eq; [| eapply AT9c]; [atp_st_eq]. }

      destruct (acc_read1 m PB NPB Pr ACC ltac:(lia)) as (b1 & RDS1 & OK1).
      destruct (sh_ok_cases b1 Pr OK1) as [-> | (k1 & -> & K1 & KM1)].
      - step. shz_norm. step. if_false. eapply evt_eq; [| eapply J94]; [atp_st_eq].
      - step. rewrite (sxb_small7 k1) by lia. step. if_lia. step. if_lia. eapply evt_eq; [| eapply J94]; [atp_st_eq]. }

    destruct (acc_read1 m PB NPB (Pr + cnt) ACC ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 (Pr + cnt) OK0) as [-> | (k0 & -> & K0 & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J74]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_lia. astep. step. if_lia. eapply evt_eq; [| eapply J74]; [atp_st_eq].
  Qed.

  Lemma arr_iter_loopA : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e cc spv : Z)
      (x1 x3 x8 x9 xa0 x18 x20 x21 x22 s7 s8 s9 s10 s11 xt4 : word),
    bytes_at asegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> e + 1 <= Z.of_nat (length (ae_tws E)) - 1 -> mem_inv asegs m ->
    shz m (ae_TAPE E) (8 * ae_n E) -> 0 <= ae_TAPE E -> ae_TAPE E + 8 * ae_n E < 2^63 ->
    (forall (it j' : Z) (xa1 xa4 xt2 xt3 xt5 xt6 : word),
       elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' -> 0 <= it -> j' <= e ->
       evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 67240448) (wz 4294967297) xt2 x8 x9
                          xa0 xa1 (wz it) (wz (ae_TAPE E)) xa4 (wz e) (wz 32) (wz 4294967295)
                          x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (wz 0xb6d50) fc None m (seg_rom asegs))) ->
    (forall (xa1 xa2 xa4 xt2 xt3 xt5 xt6 : word),
       evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 67240448) (wz 4294967297) xt2 x8 x9
                          xa0 xa1 xa2 (wz (ae_TAPE E)) xa4 (wz e) (wz 32) (wz 4294967295)
                          x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (wz 0xb6c90) fc None m (seg_rom asegs))) ->
    forall (n : nat) (it c' : Z) (xa1 xa4 xt2 xt3 xt5 xt6 : word),
      tiles (elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 67240448) (wz 4294967297) xt2 x8 x9
                         xa0 xa1 (wz it) (wz (ae_TAPE E)) xa4 (wz e) (wz 32) (wz 4294967295)
                         x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                    F (wz 0xb6ce4) fc None m (seg_rom asegs)).
  Proof.
    intros K m F fc e cc spv x1 x3 x8 x9 xa0 x18 x20 x21 x22 s7 s8 s9 s10 s11 xt4 TAPEB EN MI SHZT T0 T63 XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' xa1 xa4 xt2 xt3 xt5 xt6 TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (array_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').

    astep. step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact EL| exact I0| lia]. }
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (Tf (ae_tws E) it) < 256) by (unfold ttype; lia).

    astep. astep.
    pose proof (SHZT (ae_TAPE E + 8 * it) ltac:(lia)) as SHRD.
    astep. astep. step. shz_norm. step. if_false.
    step. astep. astep.

    assert (NEXT : forall (pc : Z) (xt2' xt3' : word), (pc = 0xb6d24 \/ pc = 0xb6d3c \/ pc = 0xb6d48) ->
      evt asegs K (MS (mkR x1 (wz spv) x3 (wz TPV) (wz 67240448) (wz 4294967297) xt2' x8 x9
                         xa0 (wz (Tf (ae_tws E) it)) (wz j') (wz (ae_TAPE E)) (wz (bv_unsigned xa4 + -1)) (wz e) (wz 32) (wz 4294967295)
                         x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 xt3' xt4 xt5 xt6)
                    F (wz pc) fc None m (seg_rom asegs))).
    { intros pc xt2' xt3' [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply (IH j' (c' - 1)); [exact TI'| exact KL| lia| lia]
        | step; apply XNF ]). }

    destruct (elem_view_of (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any (fun c cv H => H) HSN d it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0xb6d48)]; [atp_st_eq| do 2 right; reflexivity]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0xb6d24)]; [atp_st_eq| left; reflexivity]).
    -
      unfold t_str in TY. rewrite TY.
      step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0xb6d48)]; [atp_st_eq| do 2 right; reflexivity].
    -
      unfold t_arr in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb6d3c)]; [atp_st_eq| right; left; reflexivity].
    -
      unfold t_obj in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb6d3c)]; [atp_st_eq| right; left; reflexivity].
  Qed.

End ArrLoops.
