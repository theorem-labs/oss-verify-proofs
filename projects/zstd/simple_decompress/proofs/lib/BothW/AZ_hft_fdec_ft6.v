(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_fse_bitinit AZ_fse_reloadi AZ_hft_dsym AZ_hft_fdec_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Section FD.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FAST1 : fast = 1.
  Variable Q : machine_state -> Prop.
  Hypothesis QX : fd_exitK Q gp tp F fc mA SPV SPB lo DST cap FF.
  (* [comment removed for export] *)
  Hypothesis BITINIT : bit_init_stmtA_at APFSE_BITINIT.
  Hypothesis INITDS : fse_initds_stmtA.
  Hypothesis RELOADI : fse_reload_int_stmtA.
  Hypothesis DSYMF : fse_dsymf_stmtA.

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 n) (Z_to_bv 64 WK)
             (Z_to_bv 64 wksz) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + hs)) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FNST pc mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Ltac dsf_call MU WM STC STH BDC STL MI TBV TBL TBY :=
    eapply evtF_cut;
    [ eapply (DSYMF RNG) with (lo := lo) (SRC := SRC + hs) (tb := tb) (tl := tl);
      lazymatch goal with
      | |- mem_inv _ _ => exact MI
      | |- stk bsegs _ lo _ => exact STL
      | |- rw_cells bsegs _ _ [C8 _; C8 _] => exact STC
      | |- 0 <= _ < 2 ^ tl => exact STH
      | |- rw_cells bsegs _ _ (bitd_cells _ _ _ _ _) => unfold bitd_cells; exact BDC
      | |- bytes_at _ _ (DT + 4) _ => exact (proj1 (fd_tbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM))
      | |- zlen tb = _ => exact TBL
      | |- Forall _ tb => exact TBY
      | |- forall u, _ -> fse_cell_ok _ _ _ _ => exact (proj2 (proj2 (proj2 TBV)))
      | |- art ?m => match goal with H : art m |- _ => exact H end
      | |- astk _ _ _ => match goal with H : astk _ _ _ |- _ => exact H end
      | |- aro_client _ ?m => match goal with H : aro_client _ m |- _ => exact H end
      | |- aro _ _ (DT + 4) _ => exact (fd_aro_tbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU)
      | |- aro _ _ _ _ => eapply (fd_aro_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- app_blk _ _ => eapply (fd_app_frameM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ _ _ MU WM); clear; lia
      | |- _ => idtac
      end
    | ].
  (* [comment removed for export] *)
  Lemma ft_f1 : (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 109 -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (FNST 0xb13f8 mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31)).
  Proof.
    intros until i. intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 FD ST1 ST2 BC J0 I0 JC.
    pose proof HY as HY'. open_hy HY'. assert (TBV : fd_tblv tl fast tb) by (pose proof AN as AN'; open_an AN'; exact TBV). rewrite FAST1 in TBV. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 I0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX DSYMF TBV S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ART AZ AC ASTK ST1 ST2 BC J0 I0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH WKA DTE ROOM LO0 LOS SPR KLO SPB0 SPB1 SPBA OFFWK OFFDST SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV B_WK TBL TBL' TBY SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    (* [comment removed for export] *)
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) (@nil kza) [0xb21a0; 0xb1508] 30%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange bc 0 109; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536; KZWr (SPB + 112) 40] ++ kzb)
      (@nil (Z * Z)) [(SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear UD UW RWK RSWK.
    kx_mem. kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF1" pc | |- ?G => idtac "SIDE1" G end.
    fd_clearM DST SRC WK DT SPB. try clear ART AZ AC DTH TB WS WKLO SRCB FA FB SK0 SK1 SK2.
    lazymatch goal with M : munch _ mA ?m, W : wmono bsegs mA ?m |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      fd_atM HY AN M W;
      lazymatch goal with SC : rw_cells bsegs m (SPB + 80) _, BC' : rw_cells bsegs m (SPB + 112) _, SL : stk bsegs m lo SPB, MI' : mem_inv bsegs m |- _ =>
        dsf_call M W SC ST2 BC' SL MI' TBV TBL TBY end end.
    all: match goal with |- forall ms', _ => idtac | |- evtF _ _ _ _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BC TLR FAST1 WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFWK B_WK; first [lia | Z.div_mod_to_equations; lia] end.
    all: match goal with |- forall ms', _ => idtac | |- ?G => idtac "CALL-LEFT" G end.
    intros ms' PO. unfold fse_dsym_postA in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & stn & bcn & -> & MU1 & WM1 & MI1 & STL1 & SC1 & STN & BDC1 & BCB).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    lazymatch goal with M : munch _ mA ?m0, W : wmono bsegs mA ?m0, MU1 : munch _ ?m0 m1 |- _ =>
      assert (MU01 : munch (FD_WB DST cap SPB) mA m1) by (eapply munch_trans; [exact M|]; eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside app] in *; clear - Hx; lia);
      assert (WM01 : wmono bsegs mA m1) by (eapply wmono_trans; [exact W| exact WM1]);
      lazymatch goal with SO : rw_cells bsegs m0 (SPB + 96) ?cs, FA0 : rw_cells bsegs m0 (SPB + 24) ?fa, SD0 : stk bsegs m0 DST (DST + cap) |- _ =>
        assert (SO' : rw_cells bsegs m1 (SPB + 96) cs) by (eapply rw_cells_transport; [exact SO | exact MU1 | exact WM1 | cbn; clear; lia]);
        assert (FA1 : rw_cells bsegs m1 (SPB + 24) fa) by (eapply rw_cells_transport; [exact FA0 | exact MU1 | exact WM1 | cbn; clear; lia]);
        assert (STD1 : stk bsegs m1 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact SD0 | exact MU1 | exact WM1 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]);
        clear M W MU1 WM1 SO FA0 SD0 end end.
    fd_clearM DST SRC WK DT SPB.
    repeat match goal with H : rw_cells bsegs ?m0 _ _, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | mA => fail | _ => clear H end end.
    repeat match goal with H : stk bsegs ?m0 _ _, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | _ => clear H end end.
    repeat match goal with H : mem_inv bsegs ?m0, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | _ => clear H end end.
    unfold bitd_cells in BDC1.
    (* [comment removed for export] *)
    fd_atM HY AN MU01 WM01.
    try clear US; try clear UW; try clear RSRC; try clear RSSRC; try clear RWK; try clear RSWK; try clear SP_DS; try clear SP_BS.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (SO', SC1, BDC1, FA) [KAUnp DST cap; KAApp DST cap] [0xafb48; 0xb1508] 40%nat
      ([KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536; KZDisj DST cap SPB 152] ++ kzb)
      (@nil (Z * Z)) [(DST, cap); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear UD RDST RSDST RSTK RSFR.
    all: kx_mem; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R | |- ?G => idtac "SIDE2" G end.
    all: apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear - J0 I0 JC CAPH; lia | right; clear - J0 I0 JC; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma ft_f2 : (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 109 -> 0 <= j -> 0 <= i -> j + i + 3 <= cap ->
        evtF bsegs RNG Q (FNST 0xb1434 mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31)).
  Proof.
    intros until i. intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 FD ST1 ST2 BC J0 I0 JC.
    pose proof HY as HY'. open_hy HY'. assert (TBV : fd_tblv tl fast tb) by (pose proof AN as AN'; open_an AN'; exact TBV). rewrite FAST1 in TBV. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 I0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX DSYMF TBV S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ART AZ AC ASTK ST1 ST2 BC J0 I0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH WKA DTE ROOM LO0 LOS SPR KLO SPB0 SPB1 SPBA OFFWK OFFDST SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV B_WK TBL TBL' TBY SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    (* [comment removed for export] *)
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) (@nil kza) [0xb21a0; 0xb1508] 30%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange bc 0 109; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 3 65536; KZWr (SPB + 112) 40] ++ kzb)
      (@nil (Z * Z)) [(SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear UD UW RWK RSWK.
    kx_mem. kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF1" pc | |- ?G => idtac "SIDE1" G end.
    fd_clearM DST SRC WK DT SPB. try clear ART AZ AC DTH TB WS WKLO SRCB FA FB SK0 SK1 SK2.
    lazymatch goal with M : munch _ mA ?m, W : wmono bsegs mA ?m |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      fd_atM HY AN M W;
      lazymatch goal with SC : rw_cells bsegs m (SPB + 96) _, BC' : rw_cells bsegs m (SPB + 112) _, SL : stk bsegs m lo SPB, MI' : mem_inv bsegs m |- _ =>
        dsf_call M W SC ST1 BC' SL MI' TBV TBL TBY end end.
    all: match goal with |- forall ms', _ => idtac | |- evtF _ _ _ _ => idtac | _ => clear - LO0 LOS SPB0 SPB1 SPBA BC TLR FAST1 WKA DTE WKL WKH ROOM P2 SRCL SRCH HS1 HSN SP_BS SP_BT N0 SPR OFFWK B_WK; first [lia | Z.div_mod_to_equations; lia] end.
    all: match goal with |- forall ms', _ => idtac | |- ?G => idtac "CALL-LEFT" G end.
    intros ms' PO. unfold fse_dsym_postA in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & stn & bcn & -> & MU1 & WM1 & MI1 & STL1 & SC1 & STN & BDC1 & BCB).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    lazymatch goal with M : munch _ mA ?m0, W : wmono bsegs mA ?m0, MU1 : munch _ ?m0 m1 |- _ =>
      assert (MU01 : munch (FD_WB DST cap SPB) mA m1) by (eapply munch_trans; [exact M|]; eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside app] in *; clear - Hx; lia);
      assert (WM01 : wmono bsegs mA m1) by (eapply wmono_trans; [exact W| exact WM1]);
      lazymatch goal with SO : rw_cells bsegs m0 (SPB + 80) ?cs, FA0 : rw_cells bsegs m0 (SPB + 24) ?fa, SD0 : stk bsegs m0 DST (DST + cap) |- _ =>
        assert (SO' : rw_cells bsegs m1 (SPB + 80) cs) by (eapply rw_cells_transport; [exact SO | exact MU1 | exact WM1 | cbn; clear; lia]);
        assert (FA1 : rw_cells bsegs m1 (SPB + 24) fa) by (eapply rw_cells_transport; [exact FA0 | exact MU1 | exact WM1 | cbn; clear; lia]);
        assert (STD1 : stk bsegs m1 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact SD0 | exact MU1 | exact WM1 | cbn; clear - OFFDST LOS SPB0 SPB1 CAP0; lia]);
        clear M W MU1 WM1 SO FA0 SD0 end end.
    fd_clearM DST SRC WK DT SPB.
    repeat match goal with H : rw_cells bsegs ?m0 _ _, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | mA => fail | _ => clear H end end.
    repeat match goal with H : stk bsegs ?m0 _ _, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | _ => clear H end end.
    repeat match goal with H : mem_inv bsegs ?m0, MU01 : munch _ mA ?m1 |- _ => lazymatch m0 with m1 => fail | _ => clear H end end.
    unfold bitd_cells in BDC1.
    (* [comment removed for export] *)
    fd_atM HY AN MU01 WM01.
    try clear US; try clear UW; try clear RSRC; try clear RSSRC; try clear RWK; try clear RSWK; try clear SP_DS; try clear SP_BS.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (SO', SC1, BDC1, FA) [KAUnp DST cap; KAApp DST cap] [0xafb48; 0xb1508] 40%nat
      ([KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 3 65536; KZDisj DST cap SPB 152] ++ kzb)
      (@nil (Z * Z)) [(DST, cap); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear UD RDST RSDST RSTK RSFR.
    all: kx_mem; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R | |- ?G => idtac "SIDE2" G end.
    all: apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear - J0 I0 JC CAPH; lia | right; clear - J0 I0 JC; lia].
  Qed.
End FD.
End CANSEC2.
