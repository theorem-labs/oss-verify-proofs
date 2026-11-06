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
     Atp_objkyA Atp_h_gstrA El_defsA El_armkitA El_haccA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma bytes_read1 : forall m a (bs : list byte) k, bytes_at bsegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  exists b, ov_read_bytes bsegs m (wa (a + k)) 1 = Some [b].
Proof.
  intros m a bs k HB Hk Hl. destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:EN; [| apply nth_error_None in EN; lia].
  exists b. rewrite (bytes_at_read bsegs m a bs k 1 HB Hk ltac:(lia)). f_equal.
  apply nth_error_split in EN as (l1 & l2 & -> & L). rewrite skipn_app, <- L, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Section H3.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Local Ltac post48 :=
    lazymatch goal with |- evt _ _ (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FRx : rw_cells bsegs mx (?q + -48) _, STx : stk bsegs mx _ _, MUx : munch _ _ mx, WMx : wmono bsegs _ mx, MIx : mem_inv bsegs mx, FRMx : frm0 fc |- _ =>
        do 6 step; astep; release_frame FRx STx q; step;
        lazymatch goal with |- evt _ _ (MS (TNode (TNode (TNode _ _ (TNode _ (Some ?a1) _)) _ _) None (TNode _ _ (TNode (TNode _ (Some ?a0) _) _ _))) _ _ _ _ _ _) =>
          rewrite <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned a1) end;
        apply evt_done; unfold acc_postB; do 13 eexists; exists F, fc, mx; eexists; eexists;
        split; [atp_st_eq_goal|]; split; [exact FRMx|]; split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [assumption| exact I]
      end end.

  Lemma getcstr_specB : acc_stmtB E 0xb2fac 64 G_any.
  Proof using OK.
    unfold acc_stmtB. intros until node. intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] (S16 & NS8 & SNS & SPOS & SL) PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_tf_facts (ae_tws E) (ae_S E) (ae_sn E) _ 1 _ EL ltac:(lia) HSN ltac:(lia)) as (_ & TIR & STRF).
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
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
    eapply (tix_cps E OK _ m1 F fc (q + -48) 1 0xb3014); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep.
    step. if_cases K1; zify_cond K1.
    -
      astep. astep. post48.
    -
      pose proof (STRF ltac:(unfold t_str; exact K1)) as STR.
      pose proof (key_word_rangeB _ _ _ _ STR HSN) as (KR & KM & KT).
      destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
      pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).

      shz_pose SZN node. step. shz_norm. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
      shz_pose SZN (node + 8). step. shz_norm. step. if_false. step. zstep.
      eapply (tix_cps E OK _ m2 F fc (q + -48) 1 0xb3058); [exact (AIW m2 MU)| lia| exact (SHBW m2 MU WM)| | exact ST2| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
      { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
      clear ST2 MI2 TAPEB2 RDB1. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
      transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
      pose proof (AIW m3 MU) as (TAPEB3 & _ & _ & DOCC3 & _).
      pose proof (tape_read m3 (ae_TAPE E) (ae_tws E) 1 TAPEB3 ltac:(lia)) as RDT1.

      shz_pose SZN node. step. shz_norm. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
      chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
      astep. chk0 SZD (ae_DOC E + 8). step. if_false.
      step. step. if_dead1 by SPOS.

      step. astep. astep. rewrite KM. pose proof (Z.mod_pos_bound (ae_T E 1) (2^56) ltac:(lia)) as TV. unfold tval in *.
      astep. astep. step. if_dead1 by SPOS TV O0. step. if_dead1 by SPOS TV O0 SL LOW HL HT. astep. zstep.
      post48.
  Qed.

  Lemma getslen_specB : acc_stmtSB E 0xb3124 64 G_any.
  Proof using OK.
    unfold acc_stmtSB. intros until node. intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT SZS.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] (S16 & NS8 & SNS & SPOS & SL) PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_tf_facts (ae_tws E) (ae_S E) (ae_sn E) _ 1 _ EL ltac:(lia) HSN ltac:(lia)) as (_ & TIR & STRF).
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
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
    eapply (tix_cps E OK _ m1 F fc (q + -48) 1 0xb318c); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep.
    step. if_cases K1; zify_cond K1.
    -
      astep. astep. post48.
    -
      pose proof (STRF ltac:(unfold t_str; exact K1)) as STR.
      pose proof (key_word_rangeB _ _ _ _ STR HSN) as (KR & KM & KT).
      destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
      pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).

      shz_pose SZN node. step. shz_norm. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
      shz_pose SZN (node + 8). step. shz_norm. step. if_false. step. zstep.
      eapply (tix_cps E OK _ m2 F fc (q + -48) 1 0xb31d0); [exact (AIW m2 MU)| lia| exact (SHBW m2 MU WM)| | exact ST2| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
      { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_acc_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
      clear ST2 MI2 TAPEB2 RDB1. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
      transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
      pose proof (AIW m3 MU) as (TAPEB3 & _ & _ & DOCC3 & _).
      pose proof (tape_read m3 (ae_TAPE E) (ae_tws E) 1 TAPEB3 ltac:(lia)) as RDT1.

      shz_pose SZN node. step. shz_norm. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
      chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
      astep. chk0 SZD (ae_DOC E + 8). step. if_false.

      step. step. astep. astep. rewrite KM. pose proof (Z.mod_pos_bound (ae_T E 1) (2^56) ltac:(lia)) as TV. unfold tval in *.
      astep. step. if_dead1 by SPOS TV. astep. astep. astep.
      replace (Z.lxor (Z.b2z (0 <? ae_SBUF E)) (Z.b2z (ae_SBUF E + ae_T E 1 mod 72057594037927936 <? 1))) with 1
        by (replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia);
            replace (ae_SBUF E + ae_T E 1 mod 72057594037927936 <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      step. if_false. step. if_dead1 by SPOS.

      set (o := ae_T E 1 mod 72057594037927936) in *.
      chk0 SZS (ae_SBUF E + o). step. if_false.
      astep. chk0 SZS (ae_SBUF E + o + 3). step. if_false. astep.

      pose proof (AIW m3 MU) as (_ & SBUFB3 & _ & _ & _).
      destruct (bytes_read1 m3 (ae_SBUF E) _ o SBUFB3 ltac:(lia) ltac:(rewrite length_map; lia)) as [b0 R0].
      destruct (bytes_read1 m3 (ae_SBUF E) _ (o + 1) SBUFB3 ltac:(lia) ltac:(rewrite length_map; lia)) as [b1 R1].
      destruct (bytes_read1 m3 (ae_SBUF E) _ (o + 2) SBUFB3 ltac:(lia) ltac:(rewrite length_map; lia)) as [b2 R2].
      destruct (bytes_read1 m3 (ae_SBUF E) _ (o + 3) SBUFB3 ltac:(lia) ltac:(rewrite length_map; lia)) as [b3 R3].
      replace (ae_SBUF E + (o + 1)) with (ae_SBUF E + o + 1) in R1 by lia.
      replace (ae_SBUF E + (o + 2)) with (ae_SBUF E + o + 2) in R2 by lia.
      replace (ae_SBUF E + (o + 3)) with (ae_SBUF E + o + 3) in R3 by lia.
      step. step. step. step.

      Ltac hide_bits := repeat match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) =>
        match r with context [Some (Z_to_bv 64 (Z.lor ?x ?y))] => let w := fresh "lw" in set (w := Z.lor x y); clearbody w
                   | context [Some (Z_to_bv 64 (Z.shiftl ?x ?y))] => let w := fresh "lw" in set (w := Z.shiftl x y); clearbody w end end.
      astep. hide_bits. astep. hide_bits. astep. hide_bits. astep. hide_bits. astep. hide_bits. astep. hide_bits. zstep.
      post48.
  Qed.
End H3.
