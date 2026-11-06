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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA Atp_arratA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ArrAtN.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma arrat_walkN : forall (K : machine_state -> Prop) (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (i e c sq nd out RA : Z) (idx : word)
      (gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (oa ob oc od : list byte),
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    rw_cells bsegs m0 nd [C8 (wz (ae_DOC E)); C8 (wz i)] -> sq <= nd -> nd + 16 <= out -> nd mod 8 = 0 ->
    rw_cells bsegs m0 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> sq + 16 <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> AINV_A E m) ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> shb_cells m) ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> shz m (ae_DOC E) 16) ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> shz m (ae_TAPE E) (8 * ae_n E)) ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> shz m nd 16) ->
    (forall m, munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> shz m out 24) ->
    stk bsegs m0 (ae_lo E) sq -> ae_lo E + 112 <= sq -> sq + 16 <= ae_hi E -> sq mod 16 = 0 -> mem_inv bsegs m0 ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->

    (forall (m : mem) (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 x28 x29 x30 x31 : word) (j0 : list byte),
       munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (sq + -96) ->
       rw_cells bsegs m (sq + -96) (arrat_frame (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 j0) ->
       rw_cells bsegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0xb97ac) (wz (sq + -96)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) xa3 xa4 xa5 xa6 xa7
                          xs2 xs3 xs4 xs5 (wz 2147450880) xs7 xs8 xs9 s10 s11 x28 x29 x30 x31)
                     F (wz e_asan_memset) fc None m (seg_rom bsegs))) ->

    (forall (m : mem) (it j' : Z) (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
       munch (arrat_W sq out) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) sq ->
       elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
       rw_cells bsegs m out [C8 (wz (ae_DOC E)); C8 (wz it); C4 (wz 0); CB 4 od] ->
       evt bsegs K (MS (mkR (wz RA) (wz sq) gp (wz TPV) x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (wz RA) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz sq) gp (wz TPV) t0 t1 t2 s0 s1 (wz out) (wz nd) idx a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_ARRAT_A) fc None m0 (seg_rom bsegs)).
  Proof using OK.
    intros until od. intros TY NXT TILES I0 EN NODEC NLO NHI N8 OUTC NO OH O8 AIW SHBW SHZDW SHZTW SHZNW SHZOW ST LO HI S16 MI RA0 RA2 XSET XRET.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold ATP_ARRAT_A, SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.
    pose proof (munch_refl (arrat_W sq out) m0) as MU. pose proof (wmono_refl bsegs m0) as WM. unfold arrat_W in MU.

    step. carve_frame 96%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 11 step.

    pose proof (SHBW _ MU WM) as [G1 G2].
    step. step. step. step. step.
    name_mem m1.

    chk0 SHZNW nd. step. if_false.
    step. astep. chk0 SHZNW (nd + 8). step. if_false.

    step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS. step. step. step. step.
    lazymatch goal with H : rw_cells bsegs m1 (sq + -96) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 nd _ |- _ => rename H into NODE1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    eapply (tix_cps E OK _ m1 F fc (sq + -96) i 0xb96d8); [exact (AIW m1 MU WM)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU WM) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) i TAPEB2 ltac:(lia) TIR) as RDB2. rewrite TY in RDB2. unfold t_arr in RDB2.

    chk0 SHZTW (ae_TAPE E + 8 * i). step. if_false.
    astep. astep. astep. step. if_false. astep. astep. astep. astep. step. if_true.
    astep. astep. astep. astep. astep. step. if_false.

    shz_pose SHZNW nd. step. shz_norm. step. if_false.

    step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    shz_pose SHZNW (nd + 8). step. shz_norm. step. if_false.
    step. step.
    eapply (tix_cps E OK _ m2 F fc (sq + -96) i 0xb9760); [exact (AIW m2 MU WM)| lia| exact (SHBW m2 MU WM)| | exact ST2| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST2 MI2 TAPEB2 RDB2. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
    transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
    pose proof (AIW m3 MU WM) as (TAPEB3 & _ & _ & _ & _).
    pose proof (tape_read_lo32 E m3 i TAPEB3 ltac:(lia)) as RDL3.

    assert (NFB : forall (mx : mem) (y1 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys4 ys5 ys7 ys8 ys9 y28 y29 y30 y31 : word),
      munch [(sq + -112, sq); (out, out + 24)] m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (sq + -96) ->
      rw_cells bsegs mx (sq + -96) [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA)] ->
      rw_cells bsegs mx out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      evt bsegs K (MS (mkR y1 (wz (sq + -96)) gp (wz TPV) y5 y6 y7 (wz out) ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                         ys2 ys3 ys4 ys5 (wz 2147450880) ys7 ys8 ys9 s10 s11 y28 y29 y30 y31)
                    F (wz 0xb9794) fc None mx (seg_rom bsegs))).
    { intros until y31. intros MUx WMx MIx STx FRx OUTx.
      pose proof MUx as MU'. pose proof WMx as WM'.
      step. if_dead1 by NO LO LOW. astep. astep. step. astep. step.
      eapply evt_eq; [| eapply (XSET mx)]; [unfold e_asan_memset; atp_st_eq| exact MUx| exact WMx| exact MIx| exact STx| unfold arrat_frame; exact FRx| exact OUTx]. }

    assert (FDB : forall (mx : mem) (it j' : Z) (y1 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys7 ys8 ys9 y28 y29 y30 y31 : word),
      munch [(sq + -112, sq); (out, out + 24)] m0 mx -> wmono bsegs m0 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (sq + -96) ->
      rw_cells bsegs mx (sq + -96) [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA)] ->
      rw_cells bsegs mx out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
      evt bsegs K (MS (mkR y1 (wz (sq + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz (ae_DOC E)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                         ys2 (wz it) ys4 ys5 (wz 2147450880) ys7 ys8 ys9 s10 s11 y28 y29 y30 y31)
                    F (wz 0xb9878) fc None mx (seg_rom bsegs))).
    { intros until y31. intros MUx WMx MIx STx FRx OUTx EL IT0 JE.
      pose proof MUx as MU'. pose proof WMx as WM'.
      pose proof (elem_word_range _ _ _ _ _ _ EL IT0 ltac:(lia) HSN) as ITR.
      step. if_dead1 by NO LO LOW.
      chk0 SHZOW out. step. if_false. step.
      astep. chk0 SHZOW (out + 8). step. if_false. step.
      astep. chk0 SHZOW (out + 16). step. if_false. lstep.
      name_mem mF.
      lazymatch goal with H : rw_cells bsegs mF (sq + -96) _ |- _ => rename H into FRF end.
      lazymatch goal with H : stk bsegs mF _ _ |- _ => rename H into STF end.
      do 11 step. step. release_frame FRF STF sq. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs mF _ sq |- _ => rename H into STF' end.
      lazymatch goal with H : mem_inv bsegs mF |- _ => rename H into MIF end.
      lazymatch goal with H : rw_cells bsegs mF out _ |- _ => rename H into OUTF end.
      eapply evt_eq; [| eapply (XRET mF it j')]; [atp_st_eq| exact MU'| exact WM'| exact MIF| exact STF'| exact EL| exact IT0| exact JE| exact OUTF]. }

    chk0 SHZTW (ae_TAPE E + 8 * i). step. if_false.
    step. rewrite zx32_tnext by lia. rewrite NXT. step.
    astep. astep. clear TAPEB3 RDL3.
    lazymatch goal with H : rw_cells bsegs m3 (sq + -96) _ |- _ => rename H into FR3 end.
    lazymatch goal with H : rw_cells bsegs m3 out _ |- _ => rename H into OUT3 end.
    step. if_cases KE; zify_cond KE.
    2:{
        eapply NFB; [exact MU| exact WM| exact MI3| exact ST3| exact FR3| exact OUT3]. }

    do 9 astep.
    lazymatch goal with |- evt _ ?K' _ =>
    eapply evt_eq; [| eapply (arr_iter_loopB E OK K' m3 F fc d e c (sq + -96) out) with (n := S (Z.to_nat (e - (i + 1)))) (it := i + 1) (c' := c)];
      [ atp_st_eq
      | exact EN
      | intros m' MU' WM'; exact (AIW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHBW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHZTW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | lia| lia| clear - S16; Z.div_mod_to_equations; lia
      | |
      | apply munch_refl| apply wmono_refl| exact MI3| exact ST3| exact TILES| exact KE| lia| lia ]
    end.
    -
      intros it j' mx y1 yb0 yb1 yb2 yb3 yb4 ys2 MUx WMx MIx STx EL IT0 JE.
      hide MU. hide WM. transport_after_call bsegs m3 mx MUx WMx. unhide MU. unhide WM.
      eapply (FDB mx it j');
        [ exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MUx))| exact (wmono_trans bsegs _ _ _ WM WMx)
        | exact MIx| exact STx| exact FR3| exact OUT3| exact EL| exact IT0| exact JE].
    -
      intros mx y1 yb0 yb1 yb2 yb3 yb4 ys2 ys3 MUx WMx MIx STx.
      hide MU. hide WM. transport_after_call bsegs m3 mx MUx WMx. unhide MU. unhide WM.
      eapply (NFB mx);
        [ exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_tix sq out) MUx))| exact (wmono_trans bsegs _ _ _ WM WMx)
        | exact MIx| exact STx| exact FR3| exact OUT3].
  Qed.
End ArrAtN.
