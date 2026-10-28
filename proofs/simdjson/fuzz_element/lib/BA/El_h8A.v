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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA El_defsA El_armkitA El_haccA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section H8.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma gdbl_specB : acc_stmtB E 0xb2524 16 G_dbl.
  Proof using OK.
    unfold acc_stmtB. intros until node. intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep. carve_frame 16%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    lstep.

    pose proof (SHBW _ MU WM) as [G1 G2].
    astep. step. step. astep.
    name_mem m1.
    lazymatch goal with H : stk asegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells asegs m1 (q + -16) _ |- _ => rename H into FR1 end.
    pose proof (AIW m1 MU) as (TAPEB & _ & _ & DOCC & DOCS).
    pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT1.

    assert (EPI : forall (Fx : bvmap 5 word) (fcx : bv 32) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      frm0 fcx -> G_dbl (bv_unsigned x10) (bv_unsigned x11) ->
      evt asegs (acc_postB E 16 G_dbl ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
        (MS (mkR ra (wz (q + -16)) gp (wz TPV) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fx (wz 0xb25c0) fcx None m1 (seg_rom asegs))).
    { intros until x31. intros FRMx HG.
      step. astep. release_frame FR1 ST1 q. step.
      rewrite <- (Z_to_bv_bv_unsigned x10), <- (Z_to_bv_bv_unsigned x11).
      apply evt_done. unfold acc_postB. do 13 eexists. exists Fx, fcx, m1. eexists. eexists.
      split; [atp_st_eq_goal|]. split; [exact FRMx|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| exact HG]. }

    chk0 SZN node. step. if_false.
    astep. chk0 SZN (node + 8). step. if_false.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. astep.
    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    step. astep. astep.
    step. if_cases K1; zify_cond K1.
    -
      astep. astep. step. if_cases K2; zify_cond K2.
      +
        astep. astep. step. if_cases K3; zify_cond K3.
        *
          astep. step. step.
          eapply EPI; [first [exact FRM| apply frm0_slice_set_fflags; exact FRM]| g_dbl].
        *
          pose proof (ael_word_eq E _ _ _ t_i64 OK EL ltac:(lia) ltac:(lia) ltac:(exact K3) ltac:(auto)) as J3.
          pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
          astep. chk0 SZT (ae_TAPE E + 8 * 2). step. if_false. step. step. step.
          eapply EPI; [first [exact FRM| apply frm0_slice_set_fflags; exact FRM]| g_dbl].
      +
        pose proof (ael_word_eq E _ _ _ t_u64 OK EL ltac:(lia) ltac:(lia) ltac:(exact K2) ltac:(auto)) as J3.
        pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
        astep. chk0 SZT (ae_TAPE E + 8 * 2). step. if_false. step. step. step.
        eapply EPI; [first [exact FRM| apply frm0_slice_set_fflags; exact FRM]| g_dbl].
    -
      pose proof (ael_word_eq E _ _ _ t_dbl OK EL ltac:(lia) ltac:(lia) ltac:(exact K1) ltac:(auto)) as J3.
      pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
      astep. chk0 SZT (ae_TAPE E + 8 * 2). step. if_false. step. astep.
      eapply EPI; [first [exact FRM| apply frm0_slice_set_fflags; exact FRM]| g_dbl].
  Qed.
End H8.
