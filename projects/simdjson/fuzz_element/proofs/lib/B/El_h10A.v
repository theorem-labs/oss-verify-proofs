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

Section H10.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Local Ltac post16 :=
    lazymatch goal with |- evt _ _ (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FRx : rw_cells bsegs mx (?q + -16) _, STx : stk bsegs mx _ _, MUx : munch _ _ mx, WMx : wmono bsegs _ mx, MIx : mem_inv bsegs mx, FRMx : frm0 fc |- _ =>
        step; step; astep; release_frame FRx STx q; step;
        apply evt_done; unfold acc_postB; do 13 eexists; exists F, fc, mx; eexists; eexists;
        split; [atp_st_eq_goal|]; split; [exact FRMx|]; split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [assumption| exact I]
      end end.

  Lemma isarr_specB : acc_stmtB E 0xb3da0 32 G_any.
  Proof using OK.
    unfold acc_stmtB; intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q node.
    intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
        pose proof OK as OK'; destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 32, q)] m) as MU; pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep; carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 2 lstep.
    pose proof (SHBW _ MU WM) as [G1 G2].
    astep; step; step.
    name_mem m1.

    chk0 SZN node; step; if_false.
    step; step; if_dead1 by DF DS; astep; step; if_dead1 by D8 DF DS.
    astep; chk0 SZN (node + 8); step; if_false; step; astep; zstep.
        lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -16) 1 0xb3df8); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_1 (q + -16 + -16) (q + -16) (q - 32) q ltac:(lia) ltac:(lia)) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1; intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12; clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia)) as RDT1.
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1); step; if_false.

    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep. astep.
    post16.
  Qed.

  Lemma isobj_specB : acc_stmtB E 0xb3e34 32 G_any.
  Proof using OK.
    unfold acc_stmtB; intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q node.
    intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
        pose proof OK as OK'; destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 32, q)] m) as MU; pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep; carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 2 lstep.
    pose proof (SHBW _ MU WM) as [G1 G2].
    astep; step; step.
    name_mem m1.

    chk0 SZN node; step; if_false.
    step; step; if_dead1 by DF DS; astep; step; if_dead1 by D8 DF DS.
    astep; chk0 SZN (node + 8); step; if_false; step; astep; zstep.
        lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -16) 1 0xb3e8c); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_1 (q + -16 + -16) (q + -16) (q - 32) q ltac:(lia) ltac:(lia)) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1; intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12; clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia)) as RDT1.
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1); step; if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep. astep.
    post16.
  Qed.

  Lemma isnull_specB : acc_stmtB E 0xb4068 32 G_any.
  Proof using OK.
    unfold acc_stmtB; intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q node.
    intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
        pose proof OK as OK'; destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 32, q)] m) as MU; pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep; carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 2 lstep.
    pose proof (SHBW _ MU WM) as [G1 G2].
    astep; step; step.
    name_mem m1.

    chk0 SZN node; step; if_false.
    step; step; if_dead1 by DF DS; astep; step; if_dead1 by D8 DF DS.
    astep; chk0 SZN (node + 8); step; if_false; step; astep; zstep.
        lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -16) 1 0xb40c0); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_1 (q + -16 + -16) (q + -16) (q - 32) q ltac:(lia) ltac:(lia)) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1; intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12; clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia)) as RDT1.
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1); step; if_false.

    step. astep. astep. astep. astep.
    post16.
  Qed.
End H10.
