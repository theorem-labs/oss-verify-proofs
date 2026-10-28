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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
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

Section FD.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FAST1 : fast = 1.
  Variable Q : machine_state -> Prop.
  Hypothesis QX : fd_exitK Q gp tp F fc mA SPV SPB lo DST cap FF.
  (* [comment removed for export] *)
  Hypothesis INITDS : fse_initds_stmtA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation TLST pc mm ptr bc st1 st2 j cont x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 cont x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) x11 x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 st1) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation TBST pc mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) x11 x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bc) (Z_to_bv 64 st1) x30 cont)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Lemma ft_fdms_st : forall mm (w2 w1 c b p : word) j92,
      rw_cells bsegs mm (SPB + 48) [C8 w2; C8 (Z_to_bv 64 (DT + 4))] ->
      rw_cells bsegs mm (SPB + 64) [C8 w1; C8 (Z_to_bv 64 (DT + 4))] ->
      rw_cells bsegs mm (SPB + 80) [C8 c; C4 b; CB 4 j92; C8 p; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] ->
      stk bsegs mm DST (DST + cap) -> stk bsegs mm lo SPB -> mem_inv bsegs mm ->
      munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mm -> wmono bsegs mA mm ->
      FDMS mA SPV SPB lo DST cap SRC hs DT (cells_bytes [C8 w2]) (cells_bytes [C8 w1]) (cells_bytes [C8 c]) (cells_bytes [C4 b]) j92 (cells_bytes [C8 p]) mm.
  Proof.
    intros mm w2 w1 c b p j92 C48 C64 C80 HD HL HM HU HW.
    pose proof (rw_cells_merge bsegs mm (SPB + 48) [] [C8 w2] [C8 (Z_to_bv 64 (DT + 4))] C48) as X48.
    pose proof (rw_cells_merge bsegs mm (SPB + 64) [] [C8 w1] [C8 (Z_to_bv 64 (DT + 4))] C64) as X64.
    pose proof (rw_cells_merge bsegs mm (SPB + 80) [] [C8 c] [C4 b; CB 4 j92; C8 p; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] C80) as Y1.
    cbn [app cells_size csize Nat.add] in X48, X64, Y1.
    pose proof (rw_cells_merge bsegs mm (SPB + 80) [CB 8 (cells_bytes [C8 c])] [C4 b] [CB 4 j92; C8 p; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] Y1) as Y2.
    cbn [app cells_size csize Nat.add] in Y2.
    pose proof (rw_cells_merge bsegs mm (SPB + 80) [CB 8 (cells_bytes [C8 c]); CB 4 (cells_bytes [C4 b]); CB 4 j92] [C8 p] [C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] Y2) as Y3.
    cbn [app cells_size csize Nat.add] in Y3.
    exact (FDMS_close _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X48 X64 Y3 HD HL HM HU HW).
  Qed.

  (* [comment removed for export] *)
  Lemma ft_e1 : (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)) ->
    (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j (x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xad444 mm ptr bc st1 st2 j cont x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31)).
  Proof.
    intros KB. intros until j. intros x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 FD ST1 ST2 BC BP JC.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (J0 : 0 <= j) by (clear - JC; lia).
    clear - HY AN FAST1 QX KB S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 BC BP J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear UD US UW RDST RSDST RSRC RSSRC SP_DS SP_BS. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) (@nil kza) [0xad4a8; 0xac208] 60%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange bc 0 100; KZRange j 0 65536; KZRange (cap - j) 0 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40] ++ kzb)
      (@nil (Z * Z)) [(SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             eapply (KB _ _ _ st1 st2 _ _ _ _ _ _ _ j 0); try (eapply ft_fdms_st; eassumption); try eassumption; fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-B" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; eapply ft_fdms_st; eassumption | clear; lia | left; reflexivity]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma ft_e0 : (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)) ->
    (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j (x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xad7f0 mm ptr bc st1 st2 j cont x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31)).
  Proof.
    intros KB. intros until j. intros x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 FD ST1 ST2 BC JC.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (J0 : 0 <= j) by (clear - JC; lia).
    clear - HY AN FAST1 QX KB S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 BC J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear UD US UW RDST RSDST RSRC RSSRC SP_DS SP_BS. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) (@nil kza) [0xad4a8; 0xac208] 60%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange bc 65 100; KZRange j 0 65536; KZRange (cap - j) 0 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40] ++ kzb)
      (@nil (Z * Z)) [(SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             eapply (KB _ _ _ st1 st2 _ _ _ _ _ _ _ j 0); try (eapply ft_fdms_st; eassumption); try eassumption; try (left; clear - BC; lia); fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-B" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; eapply ft_fdms_st; eassumption | clear; lia | left; reflexivity]
         end.
  Qed.
End FD.
End CANSEC2.
