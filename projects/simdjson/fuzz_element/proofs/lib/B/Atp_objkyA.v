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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_objkwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition atkey_frame (j0 : list byte) (sret Kp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 j0; C8 (wz sret); C8 (wz 4294967295); C8 (wz 4294967297); C8 (wz Kp)] ++ atkey_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Lemma key_word_rangeB : forall (T S : Z -> Z) (sn i : Z), is_str T S sn i -> sn < 2^56 ->
  0 <= T i < 2^64 /\ Z.land (T i) 72057594037927935 = tval (T i) /\ ttype (T i) = t_str.
Proof.
  intros T S sn i (o & l & X & (Y1 & Y2 & Y3 & _)) Hsn. rewrite X.
  split; [apply tword_range; [unfold t_str; lia| lia]|].
  split; [| apply ttype_tword; lia].
  change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
  unfold tval. reflexivity.
Qed.
Lemma shl_mod_smallB : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> (Z.shiftl b k) mod 18446744073709551616 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.
Lemma land_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_smallB; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_smallB; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4B : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_smallB b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_smallB b2 b3 8) by lia.
  rewrite (lor_shiftl_smallB (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.
Lemma land64_shl_smallB : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Section AtKeyY.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma atkey_nextseg : forall (K : machine_state -> Prop) (m0 m : mem) (F : bvmap 5 word) (fc : bv 32) (spk sret Kp Lk e it j' : Z)
      (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 oa ob oc od : list byte)
      (x1 gp x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x15 x16 x17 xs6 x28 x29 x30 x31 : word),
    e + 1 <= ae_n E - 1 -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> AINV_A E mx) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shb_cells mx) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shz mx (ae_DOC E) 16) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shz mx (ae_TAPE E) (8 * ae_n E)) ->
    ae_lo E + 160 <= spk -> spk + 16 <= ae_hi E -> spk mod 16 = 0 -> spk <= sret -> sret + 24 <= ae_hi E -> sret mod 8 = 0 ->
    munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (spk + -144) ->
    rw_cells bsegs m (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->

    (forall (mx : mem) (y1 ya0 ya1 ya2 ya3 ya4 ys6 : word),
       munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (spk + -144) ->
       rw_cells bsegs mx (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs mx sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> j' <> e ->
       evt bsegs K (MS (mkR y1 (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) ya0 ya1 ya2 ya3 ya4 x15 x16 x17
                          (wz 1) (wz (ae_DOC E)) (wz j') (wz (ae_DOC E + 8)) ys6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                          (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                     F (wz 0xb93b0) fc None mx (seg_rom bsegs))) ->

    (forall (mx : mem) (ya3 ya4 ys4 ys6 : word),
       munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (spk + -144) ->
       rw_cells bsegs mx (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs mx sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0xb9310) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz (sret + 16)) (wz sret) (wz 0) (wz 16) ya3 ya4 x15 x16 x17
                          (wz 1) (wz (ae_DOC E)) ys4 (wz (ae_DOC E + 8)) ys6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                          (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                     F (wz e_asan_memset) fc None mx (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                       (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                       (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                   F (wz 0xb94a4) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros EN EL I0 IJ AIW SHBW SHZDW SHZTW LO HI S16 QO OB O8 MU0 WM0 MI ST FR OUT XHEAD XNF.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP, e_asan_memset in *. unfold atkey_W in MU0.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).
    unfold atkey_frame, atkey_saved in FR. cbn [app] in FR.

    astep. step. step. step.
    eapply (tix_cps E OK K m F fc (spk + -144) (it + 1) 0xb94b4); [exact (AIW m MU0 WM0)| lia| exact (SHBW m MU0 WM0)| | exact ST| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM0 WM')). }
    intros m1 ya1 ya3 ya4 MU01 WM01 MI1 ST1.
    transport_after_call bsegs m m1 MU01 WM01. clear MU01 WM01. try clear MI. try clear ST. rename MU0 into MU1. rename WM0 into WM1.
    pose proof (AIW m1 MU1 WM1) as (TAPEB1 & _ & _ & _ & _).
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) (it + 1) TAPEB1 ltac:(lia) TIR) as RDB.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB1 ltac:(lia)) as RDT.
    pose proof (SHZTW m1 MU1 WM1) as SHZT1.
    lazymatch goal with H : rw_cells bsegs m1 (spk + -144) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : rw_cells bsegs m1 sret _ |- _ => rename H into OUT1 end.

    chk0 SHZT1 (ae_TAPE E + 8 * (it + 1)). step. if_false.
    astep. astep.

    assert (NEXT : forall (pc : Z) (mx : mem) (y1 ya0 ya1' ya2 ya3' ya4' : word), (pc = 0xb94e0 \/ pc = 0xb9520 \/ pc = 0xb952c) ->
      munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (spk + -144) ->
      rw_cells bsegs mx (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs mx sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      evt bsegs K (MS (mkR y1 (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) ya0 ya1' ya2 ya3' ya4' x15 x16 x17
                         (wz 1) (wz (ae_DOC E)) (wz j') (wz (ae_DOC E + 8)) (wz (it + 1)) (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                         (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                    F (wz pc) fc None mx (seg_rom bsegs))).
    { intros pc mx y1 ya0 ya1' ya2 ya3' ya4' PC MUx WMx MIx STx FRx OUTx.
      pose proof (munch_refl ([] : list (Z * Z)) mx) as MU'. pose proof (wmono_refl bsegs mx) as WM'.
      unfold atkey_frame, atkey_saved in FRx. cbn [app] in FRx.
      destruct PC as [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply (XHEAD mx); [exact MUx| exact WMx| exact MIx| exact STx| unfold atkey_frame, atkey_saved; cbn [app]; exact FRx| exact OUTx| rewrite ?land64_mod in KL; lia]
        | step; step; step; if_dead1 by QO LO LOW; astep; astep; astep; step;
          eapply evt_eq; [| eapply (XNF mx)]; [atp_st_eq| exact MUx| exact WMx| exact MIx| exact STx| unfold atkey_frame, atkey_saved; cbn [app]; exact FRx| exact OUTx] ]). }

    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_true; step; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0xb952c m1)]; [atp_st_eq| do 2 right; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1| unfold atkey_frame, atkey_saved; cbn [app]; exact FR1| exact OUT1]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0xb94e0 m1)]; [atp_st_eq| left; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1| unfold atkey_frame, atkey_saved; cbn [app]; exact FR1| exact OUT1]).
    -
      unfold t_str in TY. rewrite TY.
      step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0xb952c m1)]; [atp_st_eq| do 2 right; reflexivity| exact MU1| exact WM1| exact MI1| exact ST1| unfold atkey_frame, atkey_saved; cbn [app]; exact FR1| exact OUT1].
    -
      unfold t_arr in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. step. astep. astep. step. if_false.

      step. step. step.
      eapply (tix_cps E OK K m1 F fc (spk + -144) (it + 1) 0xb9504); [exact (AIW m1 MU1 WM1)| lia| exact (SHBW m1 MU1 WM1)| | exact ST1| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
      { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU1 (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM1 WM')). }
      intros m2 za1 za3 za4 MU12 WM12 MI2 ST2.
      transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12. rename MU1 into MU2. rename WM1 into WM2.
      pose proof (AIW m2 MU2 WM2) as (TAPEB2 & _ & _ & _ & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB2 ltac:(lia)) as RDT2.
      pose proof (SHZTW m2 MU2 WM2) as SHZT2.
      lazymatch goal with H : rw_cells bsegs m2 (spk + -144) _ |- _ => rename H into FR2 end.
      lazymatch goal with H : rw_cells bsegs m2 sret _ |- _ => rename H into OUT2 end.
      chk0 SHZT2 (ae_TAPE E + 8 * (it + 1)). step. if_false.
      step. step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb9520 m2)]; [atp_st_eq| right; left; reflexivity| exact MU2| exact WM2| exact MI2| exact ST2| unfold atkey_frame, atkey_saved; cbn [app]; exact FR2| exact OUT2].
    -
      unfold t_obj in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. step. astep. astep. step. if_false.
      step. step. step.
      eapply (tix_cps E OK K m1 F fc (spk + -144) (it + 1) 0xb9504); [exact (AIW m1 MU1 WM1)| lia| exact (SHBW m1 MU1 WM1)| | exact ST1| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
      { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU1 (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM1 WM')). }
      intros m2 za1 za3 za4 MU12 WM12 MI2 ST2.
      transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12. rename MU1 into MU2. rename WM1 into WM2.
      pose proof (AIW m2 MU2 WM2) as (TAPEB2 & _ & _ & _ & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB2 ltac:(lia)) as RDT2.
      pose proof (SHZTW m2 MU2 WM2) as SHZT2.
      lazymatch goal with H : rw_cells bsegs m2 (spk + -144) _ |- _ => rename H into FR2 end.
      lazymatch goal with H : rw_cells bsegs m2 sret _ |- _ => rename H into OUT2 end.
      chk0 SHZT2 (ae_TAPE E + 8 * (it + 1)). step. if_false.
      step. step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0xb9520 m2)]; [atp_st_eq| right; left; reflexivity| exact MU2| exact WM2| exact MI2| exact ST2| unfold atkey_frame, atkey_saved; cbn [app]; exact FR2| exact OUT2].
  Qed.
End AtKeyY.
