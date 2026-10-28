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
  (* [comment removed for export] *)
  Notation P1ST pc mm ptr st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + i)) x12 (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 (Z_to_bv 64 nb) x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bco) (Z_to_bv 64 nx) (Z_to_bv 64 (bco + nb)) cont)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation D2ST pc mm ptr bc cont st2 j i conto bco nx nb x1 x12 x22 x23 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + i)) x12 (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont (Z_to_bv 64 nb) x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bco) (Z_to_bv 64 nx) (Z_to_bv 64 bc) conto)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac c8_forget :=
    match goal with C : rw_cells bsegs ?m (SPB + 80) (C8 ?v :: ?rest) |- _ =>
      let C' := fresh "BDC" in
      assert (C' : rw_cells bsegs m (SPB + 80) (CB 8 (le8 v) :: rest))
        by (eapply rw_cells_recell; [exact C | split; [exact (length_le8 v) | destruct C as [[[_ W] _] _]; exact W] | reflexivity]);
      clear C
    end.
  Definition ft_r1T (d q r B : Z) : Prop := (forall mm ptr bc (cont : word) st2 j i (conto : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> 0 <= bc <= 64 ->
        fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xad5dc mm ptr bc cont st2 j i conto bco nx nb x1 x12 x22 x23 x25 x26)) ->
    forall mm st2 j i (cont : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x20 x22 x23 x25 x26 : word),
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> bco + nb = 8 * q + r ->
    0 <= j -> 0 <= i -> j + i + 2 <= cap -> B <= i ->
    evtF bsegs RNG Q (P1ST 0xad514 mm (SRC + hs + d) st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26).
  (* [comment removed for export] *)
  Lemma ft_r1_0 : forall d q r B, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 BQ J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NXR : nx <= 511) by (pose proof (Z.pow_pos_nonneg 2 nb) as PP; pose proof (Z.pow_le_mono_r 2 tl 9) as PT; clear - PP PT NB1 NXT TLR; change (2^9) with 512 in PT; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NB1 NX0 NXT NXR BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64. rewrite BQ.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad5dc; 0xac208; 0xad860] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st2 0 511; KZRange bco 0 100; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: try c8_forget.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad5dc) _ _ _ _) =>
             eapply (KN _ _ _ _ st2 j i _ bco nx nb); try close_fdms; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_n : forall d q r B, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 BQ J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NXR : nx <= 511) by (pose proof (Z.pow_pos_nonneg 2 nb) as PP; pose proof (Z.pow_le_mono_r 2 tl 9) as PT; clear - PP PT NB1 NXT TLR; change (2^9) with 512 in PT; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NB1 NX0 NXT NXR BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64. rewrite BQ.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad5dc; 0xac208; 0xad860] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st2 0 511; KZRange bco 0 100; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: try c8_forget.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad5dc) _ _ _ _) =>
             eapply (KN _ _ _ _ st2 j i _ bco nx nb); try close_fdms; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_c : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 BQ J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NXR : nx <= 511) by (pose proof (Z.pow_pos_nonneg 2 nb) as PP; pose proof (Z.pow_le_mono_r 2 tl 9) as PT; clear - PP PT NB1 NXT TLR; change (2^9) with 512 in PT; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NB1 NX0 NXT NXR BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64. rewrite BQ.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad5dc; 0xac208; 0xad860] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st2 0 511; KZRange bco 0 100; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: try c8_forget.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad5dc) _ _ _ _) =>
             eapply (KN _ _ _ _ st2 j i _ bco nx nb); try close_fdms; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_k : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 BQ J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NXR : nx <= 511) by (pose proof (Z.pow_pos_nonneg 2 nb) as PP; pose proof (Z.pow_le_mono_r 2 tl 9) as PT; clear - PP PT NB1 NXT TLR; change (2^9) with 512 in PT; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NB1 NX0 NXT NXR BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64. rewrite BQ.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad5dc; 0xac208; 0xad860] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st2 0 511; KZRange bco 0 100; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: try c8_forget.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad5dc) _ _ _ _) =>
             eapply (KN _ _ _ _ st2 j i _ bco nx nb); try close_fdms; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_f : (forall mm ptr st2 j i (cont : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x20 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (P1ST 0xad860 mm ptr st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26)) ->
    forall mm ptr st2 j i (cont : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x20 x22 x23 x25 x26 : word),
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> 64 < bco + nb ->
    0 <= j -> 0 <= i -> j + i + 2 <= cap ->
    evtF bsegs RNG Q (P1ST 0xad514 mm ptr st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26).
  Proof.
    intros KF. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 OV J0 I0 JC.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    assert (NXR : nx <= 511) by (pose proof (Z.pow_pos_nonneg 2 nb) as PP; pose proof (Z.pow_le_mono_r 2 tl 9) as PT; clear - PP PT NB1 NXT TLR; change (2^9) with 512 in PT; lia).
    clear - HY AN FAST1 QX KF S1 S2 BDC FA STD STL MI MU WM RSTK RSFR ST2 NB1 NX0 NXT NXR BC0 OV J0 I0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA P2 B_SPV.
    unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) (@nil kza) [0xad860] 20%nat
      ([KZRange (bco + nb) 65 109; KZRange bco 0 100; KZRange nb 1 9; KZRange nx 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536] ++ kzb) (@nil (Z * Z)) [(SPB, 120)].
    all: try (kx_side_pre; kx_lia).
    all: clear RSTK RSFR.
    all: kx_mem; kx_tidy_run.
    all: eapply (KF _ ptr st2 j i cont bco nx nb); try close_fdms; try eassumption; clear - J0 I0 JC; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ft_r1 : forall B, (forall mm ptr st2 j i (cont : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x20 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (P1ST 0xad860 mm ptr st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26)) -> (forall mm ptr bc (cont : word) st2 j i (conto : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> 0 <= bc <= 64 ->
        fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xad5dc mm ptr bc cont st2 j i conto bco nx nb x1 x12 x22 x23 x25 x26)) -> (forall mm ptr st2 j i (cont : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x20 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> (64 < bco + nb \/ fl_ptr SRC n hs ptr) ->
        0 <= j -> 0 <= i -> j + i + 2 <= cap -> B <= i ->
        evtF bsegs RNG Q (P1ST 0xad514 mm ptr st2 j i cont bco nx nb x1 x12 x20 x22 x23 x25 x26)).
  Proof.
    intros B KF KN. intros until x26. intros FD ST2 NB1 NX0 NXT BC0 BP J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'.
    destruct (Z_lt_le_dec 64 (bco + nb)) as [OV | LE].
    { eapply (ft_r1_f KF); [exact FD | exact ST2 | exact NB1 | exact NX0 | exact NXT | exact BC0 | exact OV | exact J0 | exact I0 | exact JC]. }
    assert (PTR : fl_ptr SRC n hs ptr) by (destruct BP as [X|X]; [exfalso; clear - X LE; lia | exact X]).
    assert (QQ : exists q r, bco + nb = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists ((bco + nb) / 8), ((bco + nb) mod 8); clear - NB1 BC0 LE; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & BQ & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (Z_to_bv 64 (SRC + hs)) with (Z_to_bv 64 (SRC + hs + 0)) by (f_equal; clear; lia).
      eapply (ft_r1_0 0 q r B); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST2 | exact NB1
                                | exact NX0 | exact NXT | exact BC0 | exact BQ | exact J0 | exact I0 | exact JC | exact JB]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (ft_r1_k d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST2 | exact NB1
                                  | exact NX0 | exact NXT | exact BC0 | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
      + eapply (ft_r1_c d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST2 | exact NB1
                                  | exact NX0 | exact NXT | exact BC0 | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
    - eapply (ft_r1_n d q r B); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST2 | exact NB1
                                | exact NX0 | exact NXT | exact BC0 | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
  Qed.
End FD.
End CANSEC2.
