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
     El_defsA El_armkitA El_haccA El_h6A El_h7A El_h8A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma sub_fp_isnum : forall q, sub_fp [(q + -32 - 64, q + -32)] [(q - 96, q)].
Proof. intros q x Hx. cbn [outside] in *. lia. Qed.

Section H16.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma isnum_specB : acc_stmtB E 0xb3ec8 96 G_any.
  Proof using OK.
    unfold acc_stmtB. intros until node. intros ST LO HI Q16 MI FRM NODE N0 NQ NH AIW SHBW SZN SZD SZT.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (munch_refl [(q - 96, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    assert (TR : forall mA mB, munch [(q - 96, q)] m mA -> munch [(q + -32 - 64, q + -32)] mA mB -> munch [(q - 96, q)] m mB)
      by (intros mA mB MA MB; exact (munch_trans _ _ _ _ MA (munch_weaken _ _ _ _ (sub_fp_isnum q) MB))).

    astep. carve_frame 32%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 3 lstep. astep. zstep.
    name_mem m1.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 node _ |- _ => rename H into NODE1 end.

    assert (CALL : forall (H : Z) (G : Z -> Z -> Prop) (SPEC : acc_stmtB E H 64 G) (K : machine_state -> Prop) (mx : mem) (Fx : bvmap 5 word) (fcx : bv 32)
        (rax x5 x6 x7 x9 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
      munch [(q - 96, q)] m mx -> wmono bsegs m mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (q + -32) -> frm0 fcx -> rw_cells bsegs mx node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
      (forall ms', acc_postB E 64 G rax (q + -32) gp (wz node) x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mx ms' -> evt bsegs K ms') ->
      evt bsegs K (MS (mkR rax (wz (q + -32)) gp (wz TPV) x5 x6 x7 (wz node) x9 (wz node) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    Fx (wz H) fcx None mx (seg_rom bsegs))).
    { intros until x31. intros MUx WMx MIx STx FRMx NODEx HK.
      eapply evt_cut; [| exact HK].
      eapply (SPEC rax gp x5 x6 x7 (wz node) x9 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 Fx fcx mx (q + -32) node);
        [exact STx| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MIx| exact FRMx| exact NODEx| exact N0| clear - NQ; lia| exact NH
        | intros m' MU'; exact (AIW m' (TR _ _ MUx MU'))
        | intros m' MU' WM'; exact (SHBW m' (TR _ _ MUx MU') (wmono_trans bsegs _ _ _ WMx WM'))
        | intros m' MU' WM'; exact (SZN m' (TR _ _ MUx MU') (wmono_trans bsegs _ _ _ WMx WM'))
        | intros m' MU' WM'; exact (SZD m' (TR _ _ MUx MU') (wmono_trans bsegs _ _ _ WMx WM'))
        | intros m' MU' WM'; exact (SZT m' (TR _ _ MUx MU') (wmono_trans bsegs _ _ _ WMx WM'))]. }

    assert (EPI : forall (mx : mem) (Fx : bvmap 5 word) (fcx : bv 32) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      munch [(q - 96, q)] m mx -> wmono bsegs m mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (q + -32) -> frm0 fcx ->
      rw_cells bsegs mx (q + -32) [CB 8 (firstn 8 junk); C8 s1; C8 s0; C8 ra] ->
      evt bsegs (acc_postB E 96 G_any ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
        (MS (mkR x1 (wz (q + -32)) gp (wz TPV) x5 x6 x7 (wz node) x9 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fx (wz 0xb3f24) fcx None mx (seg_rom bsegs))).
    { intros until x31. intros MUx WMx MIx STx FRMx FRx.
      astep. do 3 step. astep. release_frame FRx STx q. step.
      rewrite <- (Z_to_bv_bv_unsigned x9), <- (Z_to_bv_bv_unsigned x11).
      apply evt_done. unfold acc_postB. do 13 eexists. exists Fx, fcx, mx. eexists. eexists.
      split; [atp_st_eq_goal|]. split; [exact FRMx|]. split; [exact MUx|]. split; [exact WMx|]. split; [exact MIx|]. split; [assumption| exact I]. }
    lazymatch goal with H : rw_cells bsegs m1 (q + -32) _ |- _ => rename H into FR1 end.

    apply (CALL 0xb3624 G_int (gi64_specB E OK) _ m1 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU WM MI1 ST1 FRM NODE1).
    intros ms' (u0 & u1 & u2 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & c0 & c1 & -> & FRM2 & MU2 & WM2 & MI2 & ST2 & HG2).
    rewrite ret_pc_even by (clear; lia). unfold G_int in HG2. destruct HG2 as [HG2a HG2b].
    hide MU. hide WM. transport_after_call bsegs m1 m2 MU2 WM2. unhide MU. unhide WM.
    pose proof (TR _ _ MU MU2) as MU2'. pose proof (wmono_trans bsegs _ _ _ WM WM2) as WM2'.
    lazymatch goal with H : rw_cells bsegs m2 (q + -32) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : rw_cells bsegs m2 node _ |- _ => rename H into NODE2 end.

    astep. astep. step. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in Kc by lia; clear - Kc HG2b; lia| clear Kc].
    astep. step. if_cases K1; zify_cond K1.
    {   eapply EPI; [exact MU2'| exact WM2'| exact MI2| exact ST2| exact FRM2| exact FR2]. }

    astep. zstep.
    apply (CALL 0xb3800 G_int (gu64_specB E OK) _ m2 F2 fc2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU2' WM2' MI2 ST2 FRM2 NODE2).
    intros ms' (w0 & w1 & w2 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & m3 & d0 & d1 & -> & FRM3 & MU3 & WM3 & MI3 & ST3 & HG3).
    rewrite ret_pc_even by (clear; lia). unfold G_int in HG3. destruct HG3 as [HG3a HG3b].
    hide MU. hide WM. hide MU2'. hide WM2'. transport_after_call bsegs m2 m3 MU3 WM3. unhide MU2'. unhide WM2'. unhide MU. unhide WM.
    pose proof (TR _ _ MU2' MU3) as MU3'. pose proof (wmono_trans bsegs _ _ _ WM2' WM3) as WM3'.
    lazymatch goal with H : rw_cells bsegs m3 (q + -32) _ |- _ => rename H into FR3 end.
    lazymatch goal with H : rw_cells bsegs m3 node _ |- _ => rename H into NODE3 end.

    astep. astep. step. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in Kc by lia; clear - Kc HG3b; lia| clear Kc].
    step. if_cases K2; zify_cond K2.
    { eapply EPI; [exact MU3'| exact WM3'| exact MI3| exact ST3| exact FRM3| exact FR3]. }

    astep. zstep.
    apply (CALL 0xb39dc G_dbl (gdbl_specB E OK) _ m3 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU3' WM3' MI3 ST3 FRM3 NODE3).
    intros ms' (z0 & z1 & z2 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & F4 & fc4 & m4 & g0 & g1 & -> & FRM4 & MU4 & WM4 & MI4 & ST4 & HG4).
    rewrite ret_pc_even by (clear; lia). unfold G_dbl in HG4. destruct HG4 as [HG4a HG4b].
    hide MU. hide WM. hide MU2'. hide WM2'. hide MU3'. hide WM3'. transport_after_call bsegs m3 m4 MU4 WM4. unhide MU3'. unhide WM3'. unhide MU2'. unhide WM2'. unhide MU. unhide WM.
    pose proof (TR _ _ MU3' MU4) as MU4'. pose proof (wmono_trans bsegs _ _ _ WM3' WM4) as WM4'.
    lazymatch goal with H : rw_cells bsegs m4 (q + -32) _ |- _ => rename H into FR4 end.

    astep. astep. step. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in Kc by lia; clear - Kc HG4a; lia| clear Kc].
    astep.
    eapply EPI; [exact MU4'| exact WM4'| exact MI4| exact ST4| exact FRM4| exact FR4].
  Qed.
End H16.
