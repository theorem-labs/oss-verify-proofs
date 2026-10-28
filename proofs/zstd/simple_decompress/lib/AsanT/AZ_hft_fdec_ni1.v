(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym AZ_hft_fdec_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Ltac kxa_unpZ ::=
  lazymatch goal with
  | |- unpZ ?mm ?lo1 ?hi1 =>
      first [ kxa_hyp
            | match goal with
              | U : unpoisoned mm ?X ?hi0 |- _ =>
                  lazymatch lo1 with context [X] => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia] end
              end
            | match goal with
              | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
              end
            | kxa_unp_hook ]
  end.
Local Ltac kxa_rng0 ::=
  kxa_norm;
  lazymatch goal with
  | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
      first [ match goal with
              | H : rng RG (shad ?X) ?N0 |- _ =>
                  lazymatch A with context [X] =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                  end
              end
            | match goal with
              | H : rng RG (shad ?A0) ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n (shad A0) N0 H);
                  [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              | H : rng RG ?A0 ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n A0 N0 H);
                  [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              end
            | lazymatch RG with
              | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
              end
            | kxa_rng_hook ]
  end.

Section ND.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FAST0 : fast = 0.
  Variable Q : machine_state -> Prop.
  Hypothesis QX : fd_exitK Q gp tp F fc mA SPV SPB lo DST cap FF.
  (* [comment removed for export] *)
  Hypothesis BITINIT : bit_init_stmtA_at APFSE_BITINIT.
  Hypothesis INITDS : fse_initds_stmtA.

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
             (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Ltac ids_call HY AN MU WM STC BDC FB STL MI :=
    eapply evtF_cut;
    [ eapply (INITDS RNG) with (lo := lo) (n := n - hs) (src := skipn (Z.to_nat hs) src) (tl := tl);
      lazymatch goal with
      | |- mem_inv _ _ => exact MI
      | |- stk bsegs _ lo _ => exact STL
      | |- rw_cells bsegs _ _ [CB 16 _] => exact STC
      | |- rw_cells bsegs _ _ (bitd_cells _ _ _ _ _) => exact BDC
      | |- rw_cells bsegs ?m DT _ => match goal with H : rw_cells bsegs m DT [C2 _; C2 _] |- _ => exact H end
      | |- fbit_ok _ _ _ _ => exact FB
      | |- bytes_at _ _ _ _ => exact (proj1 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- zlen _ = _ => exact (proj2 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- art ?m => match goal with H : art m |- _ => exact H end
      | |- astk _ _ _ => match goal with H : astk _ _ _ |- _ => exact H end
      | |- aro_client _ ?m => match goal with H : aro_client _ m |- _ => exact H end
      | |- aro _ _ DT 4 => exact (fd_aro_dtM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- 0 < _ -> aro _ _ _ _ => intros _; exact (fd_aro_srcM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- aro _ _ _ _ => eapply (fd_aro_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- app_blk _ _ => eapply (fd_app_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- _ => idtac
      end
    | ].

  (* [comment removed for export] *)
  Lemma ni_ini : (forall mm st1 st2 (cont : word) bc ptr pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok (SRC + hs) (n - hs) bc ptr ->
        evtF bsegs RNG Q (F0ST 0xac2f4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)) ->
    forall mm x1 bc ptr (cont x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) pad j1 j2,
    rw_cells bsegs mm (SPB + 48) [CB 16 j2] -> rw_cells bsegs mm (SPB + 64) [CB 16 j1] ->
    rw_cells bsegs mm (SPB + 80) (bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs)) ->
    stk bsegs mm DST (DST + cap) -> stk bsegs mm lo SPB -> mem_inv bsegs mm -> munch (FD_WB DST cap SPB) mA mm -> wmono bsegs mA mm ->
    fbit_ok (SRC + hs) (n - hs) bc ptr -> bc <= 64 ->
    evtF bsegs RNG Q (F0ST 0xac2d4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros KI. intros until j2. intros F2 F1 BDC STD STL MI MU WM FOK BC64. unfold bitd_cells in BDC.
    pose proof HY as HY'. open_hy HY'. fd_atP HY AN. destruct FOK as [BCR BOK].
    clear DSTWK DSTSRC WKSRC FFDST FFWK FFSRC RDST RSDST ABD F64 FFH FFT RFF RSFF. unfold KHIGH in *.
    (* [comment removed for export] *)
    do 4 zstep.
    fd_atM HY AN MU WM.
    ids_call HY AN MU WM F1 BDC (conj BCR BOK) STL MI.
    all: match goal with |- forall ms', _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BCR BC64 TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFSRC OFFWK; first [lia | Z.div_mod_to_equations; lia] end.
    intros ms' PO. unfold fse_initds_postA in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & st1 & cont1 & bc1 & ptr1 & -> & MU1 & WM1 & MI1 & STL1 & S1 & ST1 & BDC1 & FOK1 & BCB1 & DTH1).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (MU01 : munch (FD_WB DST cap SPB) mA m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    assert (WM01 : wmono bsegs mA m1) by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (F2' : rw_cells bsegs m1 (SPB + 48) [CB 16 j2]) by (eapply rw_cells_transport; [exact F2 | exact MU1 | exact WM1 | cbn; clear; lia]).
    assert (STD1 : stk bsegs m1 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact STD | exact MU1 | exact WM1 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]).
    clear MU WM MU1 WM1 STL F2 STD MI. fd_clearM DST SRC WK DT SPB. unfold bitd_cells in BDC1.
    (* [comment removed for export] *)
    do 4 zstep.
    destruct FOK1 as [BCR1 BOK1].
    fd_atM HY AN MU01 WM01.
    ids_call HY AN MU01 WM01 F2' BDC1 (conj BCR1 BOK1) STL1 MI1.
    all: match goal with |- forall ms', _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BCR1 BCB1 BC64 TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFSRC OFFWK; first [lia | Z.div_mod_to_equations; lia] end.
    intros ms' PO. unfold fse_initds_postA in PO.
    destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & st2 & cont2 & bc2 & ptr2 & -> & MU2 & WM2 & MI2 & STL2 & S2 & ST2 & BDC2 & FOK2 & BCB2 & DTH2).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (MU02 : munch (FD_WB DST cap SPB) mA m2).
    { eapply munch_trans; [exact MU01|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    assert (WM02 : wmono bsegs mA m2) by (eapply wmono_trans; [exact WM01| exact WM2]).
    assert (S1' : rw_cells bsegs m2 (SPB + 64) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))]) by (eapply rw_cells_transport; [exact S1 | exact MU2 | exact WM2 | cbn; clear; lia]).
    assert (STD2 : stk bsegs m2 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact STD1 | exact MU2 | exact WM2 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]).
    eapply KI; [close_fdm | exact ST1 | exact ST2 | exact FOK2].
  Qed.

  (* [comment removed for export] *)
  Lemma ni_bi : (forall mm st1 st2 (cont : word) bc ptr pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok (SRC + hs) (n - hs) bc ptr ->
        evtF bsegs RNG Q (F0ST 0xac2f4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)) ->
    fd_entK RNG Q gp tp F fc mA SPV SPB lo DST cap SRC n hs WK wksz DT FF 0xac2bc.
  Proof.
    intros KI. unfold fd_entK, fd_entst. intros until jb. intros F2 F1 FB0 STD STL MI MU WM.
    pose proof HY as HY'. open_hy HY'. fd_atP HY AN.
    clear DSTWK DSTSRC WKSRC FFDST FFWK FFSRC RDST RSDST ABD F64 FFH FFT RFF RSFF. unfold KHIGH in *.
    (* [comment removed for export] *)
    do 3 zstep.
    fd_atM HY AN MU WM.
    eapply evtF_cut;
    [ eapply (BITINIT RNG) with (lo := lo) (src := skipn (Z.to_nat hs) src);
      lazymatch goal with
      | |- mem_inv _ _ => exact MI
      | |- stk bsegs _ lo _ => exact STL
      | |- rw_cells bsegs _ _ [CB 40 _] => exact FB0
      | |- bytes_at _ _ _ _ => exact (proj1 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- zlen _ = _ => exact (proj2 (fd_src0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU))
      | |- art ?m => exact ART
      | |- astk _ _ _ => exact ASTK
      | |- aro _ _ (SRC + hs) _ => exact (fd_aro_srcM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- aro _ _ _ _ => eapply (fd_aro_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- ahull _ _ _ _ => eapply (fd_ahull_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- app_blk _ _ => eapply (fd_app_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- _ => idtac
      end
    | ].
    all: match goal with |- forall ms', _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA TLR WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 NH SPR OFFSRC OFFWK; first [lia | Z.div_mod_to_equations; lia] end.
    intros ms' PO. unfold bit_init_postA in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & r & -> & MU1 & WM1 & MI1 & STL1 & RES).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (MU01 : munch (FD_WB DST cap SPB) mA m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    assert (WM01 : wmono bsegs mA m1) by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (F2' : rw_cells bsegs m1 (SPB + 48) [CB 16 j2]) by (eapply rw_cells_transport; [exact F2 | exact MU1 | exact WM1 | cbn; clear; lia]).
    assert (F1' : rw_cells bsegs m1 (SPB + 64) [CB 16 j1]) by (eapply rw_cells_transport; [exact F1 | exact MU1 | exact WM1 | cbn; clear; lia]).
    assert (STD1 : stk bsegs m1 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact STD | exact MU1 | exact WM1 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]).
    clear MU WM MU1 WM1 STL F2 F1 FB0 STD MI. fd_clearM DST SRC WK DT SPB.
    assert (RR : 0 <= r < 2^64).
    { destruct RES as [(Er & NZ & REST) | (RE & RLT & REST)].
      - subst r. clear - NZ NH HS1. lia.
      - unfold zd_is_error, ZE_maxCode in RE. apply Z.ltb_lt in RE. clear - RE RLT. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct RES as [(-> & NZ & _) | (RE & RLT & bs & BDE)]; [exfalso; clear - K NH N0 HSN HS1; lia|].
      apply evtF_done. eapply QX; [| exact RR | left; exact RE].
      unfold EXB. split; [exact MU01|]. split; [exact WM01|]. split; [exact MI1|]. split; [exact STL1|]. split; [exact STD1|].
      eexists. split;
      [ eapply (proj2 (rw_cells_app bsegs m1 (SPB + 48) _ _)); split; [exact F2'|]; cbn [cells_size csize Nat.add];
        replace (SPB + 48 + Z.of_nat 16) with (SPB + 64) by (clear; lia);
        eapply (proj2 (rw_cells_app bsegs m1 (SPB + 64) _ _)); split; [exact F1'|]; cbn [cells_size csize Nat.add];
        replace (SPB + 64 + Z.of_nat 16) with (SPB + 80) by (clear; lia); exact BDE
      | reflexivity ].
    - (* [comment removed for export] *)
      destruct RES as [(-> & NZ & cont & bc & pad & BC & BC8 & BDC) | (RE & RLT & bs & BDE)].
      2:{ exfalso. unfold zd_is_error, ZE_maxCode in RE. apply Z.ltb_lt in RE. clear - K RE RLT. lia. }
      eapply (ni_ini KI); try eassumption; [| clear - BC; lia].
      unfold fbit_ok, bitd_ptr. destruct (Z.leb_spec 8 (n - hs)); clear - BC BC8 H NZ; split; intros; lia.
  Qed.
End ND.
End CANSEC2.
