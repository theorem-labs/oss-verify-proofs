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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA
     El_defsA El_armkitA El_haccA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section H7.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma gu64_specB : acc_stmtB E 0xb3800 64 G_int.
  Proof using OK.
    unfold acc_stmtB. intros until node. intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    pose proof (munch_refl [(q - 64, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep. carve_frame 48%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 6 lstep.

    pose proof (SHBW _ MU WM) as [G1 G2].
    astep. step. step. astep.
    name_mem m1.

    chk0 SZN node. step. if_false.
    step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    astep. chk0 SZN (node + 8). step. if_false. step. zstep.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -48) 1 0xb3868); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia)) as RDT1.

    astep. chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    shz_pose SZN node. step. shz_norm. step. if_false.

    step. step. astep. astep. astep. astep. astep. astep.
    replace (Z.land (Z.b2z (0 <? ae_DOC E)) (Z.b2z (ae_DOC E mod 8 <? 1))) with 1 by (rewrite D8; replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    lazymatch goal with H : rw_cells bsegs m2 (q + -48) _ |- _ => rename H into FR2 end.

    assert (EPI : forall (mx : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      munch [(q - 64, q)] m mx -> wmono bsegs m mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (q + -48) ->
      rw_cells bsegs mx (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      G_int (bv_unsigned x10) (bv_unsigned x11) ->
      evt bsegs (acc_postB E 64 G_int ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
        (MS (mkR x1 (wz (q + -48)) gp (wz TPV) x5 x6 x7 (wz (node + 8)) (wz node) x10 x11 x12 x13 x14 x15 x16 x17
                 (wz SHB) (wz (shad (node + 8))) (wz (shad node)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0xb38d4) fc None mx (seg_rom bsegs))).
    { intros until x31. intros MUx WMx MIx STx FRx HG.
      do 6 step. astep. release_frame FRx STx q. step.
      rewrite <- (Z_to_bv_bv_unsigned x10), <- (Z_to_bv_bv_unsigned x11).
      apply evt_done. unfold acc_postB. do 13 eexists. exists F, fc, mx. eexists. eexists.
      split; [atp_st_eq_goal|]. split; [exact FRM|]. split; [exact MUx|]. split; [exact WMx|]. split; [exact MIx|]. split; [assumption| exact HG]. }

    step. if_cases K1; zify_cond K1.
    -
      step. if_false. shz_pose SZN (node + 8). step. shz_norm. step. if_false. step. zstep.
      lazymatch goal with H : stk bsegs m2 _ _ |- _ => rename H into ST2' end.
      eapply (tix_cps E OK _ m2 F fc (q + -48) 1 0xb3908); [exact (AIW m2 MU)| lia| exact (SHBW m2 MU WM)| | exact ST2'| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
      { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
      clear ST2' MI2 TAPEB2 RDT1. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
      transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
      pose proof (AIW m3 MU) as (TAPEB3 & _ & _ & _ & _).
      pose proof (tape_read m3 (ae_TAPE E) (ae_tws E) 1 TAPEB3 ltac:(lia)) as RDT1.

      chk0 SZT (ae_TAPE E + 8 * 1). step. if_false. step. astep. astep.
      lazymatch goal with H : rw_cells bsegs m3 (q + -48) _ |- _ => rename H into FR3 end.
      step. if_cases K2; zify_cond K2.
      +
        astep. astep. zstep. eapply EPI; [exact MU| exact WM| exact MI3| exact ST3| exact FR3| g_int].
      +
        pose proof (ael_word_eq E _ _ _ t_i64 OK EL ltac:(lia) ltac:(lia) ltac:(exact K2) ltac:(auto)) as J3.
        shz_pose SZN node. step. shz_norm. step. if_false.
        step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
        shz_pose SZN (node + 8). step. shz_norm. step. if_false. step. astep. zstep.
        eapply (tix_cps E OK _ m3 F fc (q + -48) 2 0xb3954); [exact (AIW m3 MU)| lia| exact (SHBW m3 MU WM)| | exact ST3| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI3| lia| reflexivity|].
        { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
        clear ST3 MI3 TAPEB3 RDT1. intros m4 wa1 wa3 wa4 MU34 WM34 MI4 ST4.
        transport_after_call bsegs m3 m4 MU34 WM34. clear MU34 WM34.
        pose proof (AIW m4 MU) as (TAPEB4 & _ & _ & _ & _).
        pose proof (tape_read m4 (ae_TAPE E) (ae_tws E) 2 TAPEB4 ltac:(lia)) as RDT2.

        chk0 SZT (ae_TAPE E + 8 * 2). step. if_false. step.
        step. step. step. step. step. zstep.
        lazymatch goal with H : rw_cells bsegs m4 (q + -48) _ |- _ => rename H into FR4 end.
        eapply EPI; [exact MU| exact WM| exact MI4| exact ST4| exact FR4| g_int].
    -
      pose proof (ael_word_eq E _ _ _ t_u64 OK EL ltac:(lia) ltac:(lia) ltac:(exact K1) ltac:(auto)) as J3.
      step. if_false. shz_pose SZN (node + 8). step. shz_norm. step. if_false. step. astep. zstep.
      lazymatch goal with H : stk bsegs m2 _ _ |- _ => rename H into ST2' end.
      eapply (tix_cps E OK _ m2 F fc (q + -48) 2 0xb38c0); [exact (AIW m2 MU)| lia| exact (SHBW m2 MU WM)| | exact ST2'| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
      { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
      clear ST2' MI2 TAPEB2 RDT1. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
      transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
      pose proof (AIW m3 MU) as (TAPEB3 & _ & _ & _ & _).
      pose proof (tape_read m3 (ae_TAPE E) (ae_tws E) 2 TAPEB3 ltac:(lia)) as RDT2.

      chk0 SZT (ae_TAPE E + 8 * 2). step. if_false. step.
      lazymatch goal with H : rw_cells bsegs m3 (q + -48) _ |- _ => rename H into FR3 end.
      eapply EPI; [exact MU| exact WM| exact MI3| exact ST3| exact FR3| g_int].
  Qed.
End H7.
