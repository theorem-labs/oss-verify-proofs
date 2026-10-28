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
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
             (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation HDST pc mm ptr bc st1 st2 j cont x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) cont x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 st1) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac hd_sync :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
      lazymatch goal with C : rw_cells bsegs m (SPB + 80) [_; _; _; C8 (Z_to_bv 64 ?PC); _; _] |- _ =>
        first [ constr_eq P PC | replace P with PC by (fd_clear_or; lia) ]
      end
    end.
  Ltac fi_hd KH :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let FD' := fresh "FD'" in let FS' := fresh "FS'" in
      assert (FD' : exists st1' st2' (cont' : word) bc' ptr' pad', FDM mA SPV SPB lo DST cap SRC hs DT st1' st2' cont' bc' ptr' pad' m)
        by (do 6 eexists; close_fdm);
      destruct FD' as (? & ? & ? & ? & ? & ? & FD');
      apply fdm_to_fdms in FD'; destruct FD' as (? & ? & ? & ? & ? & ? & FS');
      eapply KH; [exact FS' | ..]
    end.

  Definition fi_r0T (d q r : Z) : Prop := (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
        evtF bsegs RNG Q (HDST 0xad08c mm ptr bc st1 st2 j cont x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31)) ->
    forall mm x1 st1 st2 (cont x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    evtF bsegs RNG Q (F0ST 0xac560 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma fi_r0_0 : forall d q r, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> fi_r0T d q r.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold fi_r0T. intros KH. intros until pad. intros FD ST1 ST2.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KH S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW RDST RSDST SP_DB SP_DT SP_DS SP_BT. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xad08c; 0xad7ec; 0xac208] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH DTE WKL WKH ROOM P2 ST1 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad7ec) _ _ _ _) => exfalso; fd_clear_or; lia end).
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; clear; lia).
    all: try hd_sync.
    all: fi_hd KH; try eassumption; try (unfold fl_ptr; clear - DR DN QD QR; lia); clear - QR RR BC64 DR QD CAP0; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fi_r0_c : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> fi_r0T d q r.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold fi_r0T. intros KH. intros until pad. intros FD ST1 ST2.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KH S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW RDST RSDST SP_DB SP_DT SP_DS SP_BT. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xad08c; 0xad7ec; 0xac208] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511;
        KZRange d 1 7; KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH DTE WKL WKH ROOM P2 ST1 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad7ec) _ _ _ _) => exfalso; fd_clear_or; lia end).
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; clear; lia).
    all: try hd_sync.
    all: fi_hd KH; try eassumption; try (unfold fl_ptr; clear - DR DN QD QR; lia); clear - QR RR BC64 DR QD CAP0; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fi_r0_k : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> fi_r0T d q r.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold fi_r0T. intros KH. intros until pad. intros FD ST1 ST2.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KH S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW RDST RSDST SP_DB SP_DT SP_DS SP_BT. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xad08c; 0xad7ec; 0xac208] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH DTE WKL WKH ROOM P2 ST1 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad7ec) _ _ _ _) => exfalso; fd_clear_or; lia end).
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; clear; lia).
    all: try hd_sync.
    all: fi_hd KH; try eassumption; try (unfold fl_ptr; clear - DR DN QD QR; lia); clear - QR RR BC64 DR QD CAP0; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fi_r0_n : forall d q r, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> fi_r0T d q r.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold fi_r0T. intros KH. intros until pad. intros FD ST1 ST2.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KH S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64 ART AZ AC ASTK LO0 OFFSRC OFFWK OFFDST B_SRC WKA.
    clear UD UW RDST RSDST SP_DB SP_DT SP_DS SP_BT. unfold KHIGH in *.
    (* [comment removed for export] *)
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xad08c; 0xad7ec; 0xac208] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511;
        KZRange d 8 (2^32); KZRange (d - q) 0 (2^32); KZRange (hs + d) 9 (2^32); KZRange (n - hs - d) 8 (2^32);
        KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 16);
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH DTE WKL WKH ROOM P2 ST1 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    (* [comment removed for export] *)
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad7ec) _ _ _ _) => exfalso; fd_clear_or; lia end).
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; clear; lia).
    all: try hd_sync.
    all: fi_hd KH; try eassumption; try (unfold fl_ptr; clear - DR DN QD QR; lia); clear - QR RR BC64 DR QD CAP0; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fi_r0 : (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
        evtF bsegs RNG Q (HDST 0xad08c mm ptr bc st1 st2 j cont x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31)) -> (forall mm st1 st2 (cont : word) bc ptr pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok (SRC + hs) (n - hs) bc ptr ->
        evtF bsegs RNG Q (F0ST 0xac560 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)).
  Proof.
    intros KH. intros until pad. intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FD ST1 ST2 FB. destruct FB as [BCR BOK].
    destruct (Z_lt_le_dec 64 bc) as [OV | LE].
    { (* [comment removed for export] *)
      pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
      clear - HY AN FAST1 QX S1 S2 BDC FA STD STL MI MU WM RSTK ST1 ST2 OV BCR TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA P2 B_SPV.
      unfold KHIGH in *.
      let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
      kx_autoFLAc (S1, S2, BDC, FA) (@nil kza) [0xac208] 20%nat
        ([KZRange bc 65 4096; KZRange st1 0 511; KZRange st2 0 511] ++ kzb) (@nil (Z * Z)) [(SPB, 120)].
      all: try (kx_side_pre; kx_lia).
      all: kx_mem; kx_tidy_run.
      all: apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity]. }
    specialize (BOK LE).
    assert (QQ : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - BCR LE; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & -> & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (SRC + hs) with (SRC + hs + 0) in FD by (clear; lia). eapply (fi_r0_0 0 q r); try eassumption; try exact I; try reflexivity; clear - LE QR RR; lia. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); clear - BOK NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (fi_r0_k d q r); try eassumption; clear - LE QR RR D1 D7 QD DN; lia.
      + eapply (fi_r0_c d q r); try eassumption; clear - LE QR RR D1 D7 QD DN; lia.
    - eapply (fi_r0_n d q r); try eassumption; try exact I; clear - LE QR RR D8 DN; lia.
  Qed.
End FD.
End CANSEC2.
