(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Z45 Z5k Z3v Z3t Z63 Z65.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section AtKeyH.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma sbs_byteB : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof using OK.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.

  Lemma atkey_headseg : forall (K : machine_state -> Prop) (m0 m : mem) (F : bvmap 5 word) (fc : bv 32) (spk sret Kp Lk e it : Z)
      (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 oa ob oc od : list byte)
      (x1 gp x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x15 x16 x17 xs6 x28 x29 x30 x31 : word),
    e + 1 <= ae_n E - 1 -> is_str (ae_T E) (ae_S E) (ae_sn E) it -> 0 <= it -> it + 1 <= e -> 0 <= Lk < 2^47 -> 0 <= Kp < 2^64 ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> AINV_A E mx) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shb_cells mx) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shz mx (ae_DOC E) 16) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shz mx (ae_TAPE E) (8 * ae_n E)) ->
    (forall mx, munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> shz mx (ae_SBUF E) (ae_NS E)) ->
    ae_lo E + 160 <= spk -> spk + 16 <= ae_hi E -> spk mod 16 = 0 -> spk <= sret -> sret + 24 <= ae_hi E -> sret mod 8 = 0 ->
    munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (spk + -144) ->
    rw_cells bsegs m (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->

    (forall (mx : mem) (l : Z) (ya0 ya1 ya2 ya3 ya4 : word),
       str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) l -> l <> Lk ->
       munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (spk + -144) ->
       rw_cells bsegs mx (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs mx sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0x9a7c8) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) ya0 ya1 ya2 ya3 ya4 x15 x16 x17
                          (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                          (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                     F (wz 0x9a8ac) fc None mx (seg_rom bsegs))) ->

    (forall (mx : mem) (l : Z) (ya3 ya4 : word),
       str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) l -> l = Lk ->
       munch (atkey_W spk sret) m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (spk + -144) ->
       rw_cells bsegs mx (spk + -144) (atkey_frame j0 sret Kp ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs mx sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0x9a8a8) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk)
                          (wz Kp) (wz (ae_SBUF E + tval (ae_T E it) + 4)) (wz Lk) ya3 ya4 x15 x16 x17
                          (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                          (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                     F (wz e_memcmp) fc None mx (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                       (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                       (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                   F (wz 0x9a7b8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros EN STR I0 IE LKR KPR AIW SHBW SHZDW SHZTW SHZSW LO HI S16 QO OB O8 MU0 WM0 MI ST FR OUT XNEQ XCMP.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] (SB16 & NS8 & SN & SS & SL) PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP, e_memcmp in *. unfold atkey_W in MU0.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (key_word_rangeB _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0' & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    assert (TIR : 0 <= ae_T E it < 2^64) by lia.
    unfold atkey_frame, atkey_saved in FR. cbn [app] in FR.

    step. if_false. step. step. step.
    eapply (tix_cps E OK K m F fc (spk + -144) it 0x9a7c8); [exact (AIW m MU0 WM0)| lia| exact (SHBW m MU0 WM0)| | exact ST| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM0 WM')). }
    intros m1 ya1 ya3 ya4 MU01 WM01 MI1 ST1.
    transport_after_call bsegs m m1 MU01 WM01. clear MU01 WM01. try clear MI. try clear ST. rename MU0 into MU1. rename WM0 into WM1.
    pose proof (AIW m1 MU1 WM1) as (TAPEB1 & SBUFB1 & _ & DOCC1 & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB1 ltac:(lia)) as RDT.
    pose proof (SHZTW m1 MU1 WM1) as SHZT1. pose proof (SHZDW m1 MU1 WM1) as SHZD1. pose proof (SHZSW m1 MU1 WM1) as SHZS1.
    lazymatch goal with H : rw_cells bsegs m1 (spk + -144) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : rw_cells bsegs m1 sret _ |- _ => rename H into OUT1 end.

    chk0 SHZT1 (ae_TAPE E + 8 * it). step. if_false.
    shz_pose SHZD1 (ae_DOC E + 8). step. shz_norm. step. if_false.

    step. step. astep. rewrite KM. astep.

    step. if_lia. astep. astep.
    replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
    first [ replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (o + ae_SBUF E <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
    cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false. step. if_lia.

    chk0 SHZS1 (ae_SBUF E + o). step. if_false.
    astep. chk0 SHZS1 (ae_SBUF E + o + 3). step. if_false.

    pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) o SBUFB1 ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB1 ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB1 ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB1 ltac:(lia)) as RB3.
    pose proof (sbs_byteB o ltac:(lia)) as Y0. pose proof (sbs_byteB (o + 1) ltac:(lia)) as Y1.
    pose proof (sbs_byteB (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteB (o + 3) ltac:(lia)) as Y3.
    hide FR1. hide OUT1. hide TAPEB1. hide SBUFB1. hide DOCC1. clear SHRD SHRD0 SHRD1 RDT.
    do 10 zstep.
    rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by lia.
    rewrite ?shl_mod_smallB by lia. rewrite ?land64_shl_smallB by lia. rewrite le32_of_lbu4B by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
    unhide FR1. unhide OUT1. unhide TAPEB1. unhide SBUFB1. unhide DOCC1. clear RB0 RB1 RB2 RB3.

    step. if_cases KEQ; zify_cond KEQ.
    { eapply evt_eq; [| eapply (XNEQ m1 l _ _ _ _ _ SA)]; [atp_st_eq| rewrite ?land64_mod in KEQ; lia| exact MU1| exact WM1| exact MI1| exact ST1| unfold atkey_frame, atkey_saved; cbn [app]; exact FR1| exact OUT1]. }
    assert (EL : l = Lk) by (rewrite ?land64_mod in KEQ; lia).

    step. step. step.
    eapply (tix_cps E OK K m1 F fc (spk + -144) it 0x9a864); [exact (AIW m1 MU1 WM1)| lia| exact (SHBW m1 MU1 WM1)| | exact ST1| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU1 (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM1 WM')). }
    intros m2 za1 za3 za4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12. try clear MI1. try clear ST1. rename MU1 into MU2. rename WM1 into WM2.
    try clear TAPEB1. try clear SBUFB1. try clear DOCC1. try clear SHZT1. try clear SHZD1. try clear SHZS1.
    pose proof (AIW m2 MU2 WM2) as (TAPEB2 & SBUFB2 & _ & DOCC2 & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB2 ltac:(lia)) as RDT2.
    pose proof (SHZTW m2 MU2 WM2) as SHZT2. pose proof (SHZDW m2 MU2 WM2) as SHZD2.
    lazymatch goal with H : rw_cells bsegs m2 (spk + -144) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : rw_cells bsegs m2 sret _ |- _ => rename H into OUT2 end.

    chk0 SHZT2 (ae_TAPE E + 8 * it). step. if_false.
    shz_pose SHZD2 (ae_DOC E + 8). step. shz_norm. step. if_false.
    step. step. if_lia. step. astep. rewrite KM. astep. astep. step. if_lia. step. if_lia.

    step. step. step.
    eapply evt_eq; [| eapply (XCMP m2 l _ _ SA EL)]; [atp_st_eq| exact MU2| exact WM2| exact MI2| exact ST2| unfold atkey_frame, atkey_saved; cbn [app]; exact FR2| exact OUT2].
  Qed.
End AtKeyH.
