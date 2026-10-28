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
  Notation TBST pc mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) x11 x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bc) (Z_to_bv 64 st1) x30 cont)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation P2ST pc mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + i)) x12 (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont x21 (Z_to_bv 64 nx) x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 st1) (Z_to_bv 64 bc) x31)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac fl_lowbits name Hname TLR :=
    match goal with |- context [bv_unsigned ?w / 2 ^ (((-1 * ?nb) mod 2 ^ 64) mod 64)] =>
      set (name := bv_unsigned w / 2 ^ (((-1 * nb) mod 2 ^ 64) mod 64)) in *;
      assert (Hname : 0 <= name < 2 ^ nb)
        by (subst name; apply fast_bits_ltK; [apply (bv_unsigned_in_range 64) | match goal with N : 1 <= nb <= _ |- _ => clear - N TLR; lia end]);
      clearbody name
    end.
  Lemma fd_c8_as_cb8 : forall segs m A (w : word) post,
    rw_cells segs m A (C8 w :: post) -> rw_cells segs m A (CB 8 (le8 w) :: post).
  Proof.
    intros segs m A w post H. pose proof H as [[WF _] _]. destruct WF as [_ WF2].
    eapply rw_cells_recell; [exact H | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact WF2] | reflexivity].
  Qed.
  Ltac fd_cb_back :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with H : rw_cells bsegs m (SPB + 80) (C8 _ :: _) |- _ => apply fd_c8_as_cb8 in H end
    end.
  Definition ft_r2T (d q r B : Z) : Prop := (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap -> B + 2 <= i ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)) ->
    forall mm bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bc <= 64 -> bc + nb = 8 * q + r -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
    evtF bsegs RNG Q (P2ST 0xad654 mm (SRC + hs + d) bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31).
  (* [comment removed for export] *)
  Lemma ft_r2_0 : forall d q r B, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r2T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r2T. intros KN. intros until x31. intros FD ST1 NB NX0 NXB BC0 BQ J0 I0 JC JB.
    rewrite BQ. pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NBP : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia). assert (T9 : 2^tl <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia). assert (NXR : nx <= 511) by (clear - NXB NBP T9; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 NB NX0 NXB NXR NBP T9 BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad4a8; 0xac208; 0xad8f4] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange bc 0 64; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 BC0 NB SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             try fl_lowbits lba LB TLR;
             eapply (KN _ _ _ st1 _ _ _ _ _ _ _ _ j (i + 2)); try close_fdms; try eassumption; try (right; unfold fl_ptr; fd_clear_or; lia); try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r2_n : forall d q r B, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r2T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r2T. intros KN. intros until x31. intros FD ST1 NB NX0 NXB BC0 BQ J0 I0 JC JB.
    rewrite BQ. pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NBP : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia). assert (T9 : 2^tl <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia). assert (NXR : nx <= 511) by (clear - NXB NBP T9; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 NB NX0 NXB NXR NBP T9 BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad4a8; 0xac208; 0xad8f4] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange bc 0 64; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 BC0 NB SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             try fl_lowbits lba LB TLR; try fd_cb_back;
             eapply (KN _ _ _ st1 _ _ _ _ _ _ _ _ j (i + 2)); try close_fdms; try eassumption; try (right; unfold fl_ptr; fd_clear_or; lia); try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             try fd_cb_back; apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r2_c : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r2T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r2T. intros KN. intros until x31. intros FD ST1 NB NX0 NXB BC0 BQ J0 I0 JC JB.
    rewrite BQ. pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NBP : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia). assert (T9 : 2^tl <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia). assert (NXR : nx <= 511) by (clear - NXB NBP T9; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 NB NX0 NXB NXR NBP T9 BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad4a8; 0xac208; 0xad8f4] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange bc 0 64; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 BC0 NB SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             try fl_lowbits lba LB TLR; try fd_cb_back;
             eapply (KN _ _ _ st1 _ _ _ _ _ _ _ _ j (i + 2)); try close_fdms; try eassumption; try (right; unfold fl_ptr; fd_clear_or; lia); try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             try fd_cb_back; apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r2_k : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r2T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r2T. intros KN. intros until x31. intros FD ST1 NB NX0 NXB BC0 BQ J0 I0 JC JB.
    rewrite BQ. pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (NBP : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia). assert (T9 : 2^tl <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia). assert (NXR : nx <= 511) by (clear - NXB NBP T9; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 NB NX0 NXB NXR NBP T9 BC0 BQ J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xad4a8; 0xac208; 0xad8f4] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange bc 0 64; KZRange nb 1 9; KZRange nx 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 BC0 NB SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad4a8) _ _ _ _) =>
             try fl_lowbits lba LB TLR; try fd_cb_back;
             eapply (KN _ _ _ st1 _ _ _ _ _ _ _ _ j (i + 2)); try close_fdms; try eassumption; try (right; unfold fl_ptr; fd_clear_or; lia); try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | Z.div_mod_to_equations; lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac208) _ _ _ _) =>
             try fd_cb_back; apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r2_f : (forall mm ptr bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm -> 0 <= st1 < 2^tl ->
        0 <= j -> 0 <= i -> j + i + 3 <= cap -> evtF bsegs RNG Q (P2ST 0xad8f4 mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31)) ->
    forall mm ptr bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 1 <= nb <= tl -> 0 <= bc <= 64 -> 64 < bc + nb -> 0 <= j -> 0 <= i -> j + i + 3 <= cap ->
    evtF bsegs RNG Q (P2ST 0xad654 mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31).
  Proof.
    intros KF. intros until x31. intros FD ST1 NB BC OV J0 I0 JC.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    clear - HY AN FAST1 QX KF S1 S2 BDC FA STD STL MI MU WM RSTK RSFR ST1 NB BC OV J0 I0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA P2 B_SPV.
    unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) (@nil kza) [0xad8f4] 20%nat
      ([KZRange (bc + nb) 65 73; KZRange st1 0 511; KZRange j 0 65536; KZRange i 0 65536] ++ kzb) (@nil (Z * Z)) [(SPB, 120)].
    all: try (kx_side_pre; kx_lia).
    all: clear RSTK RSFR.
    all: kx_mem; kx_tidy_run.
    all: eapply (KF _ ptr bc cont st1 j i nx nb); try close_fdms; try eassumption; clear - J0 I0 JC; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ft_r2 : forall B, (forall mm ptr bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm -> 0 <= st1 < 2^tl ->
        0 <= j -> 0 <= i -> j + i + 3 <= cap -> evtF bsegs RNG Q (P2ST 0xad8f4 mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31)) -> (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap -> B + 2 <= i ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)) -> (forall mm ptr bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm -> 0 <= st1 < 2^tl ->
        1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i ->
        j + i + 3 <= cap -> B <= i -> evtF bsegs RNG Q (P2ST 0xad654 mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31)).
  Proof.
    intros B KF KN. intros until x31. intros FD ST1 NB NX0 NXB BC PTR J0 I0 JC JB.
    destruct (Z_lt_le_dec 64 (bc + nb)) as [OV | LE].
    { eapply (ft_r2_f KF); [exact FD | exact ST1 | exact NB | exact BC | exact OV | exact J0 | exact I0 | exact JC]. }
    assert (QQ : exists q r, bc + nb = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists ((bc + nb) / 8), ((bc + nb) mod 8); clear - BC NB LE; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & BQ & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (Z_to_bv 64 (SRC + hs)) with (Z_to_bv 64 (SRC + hs + 0)) by (f_equal; clear; lia).
      eapply (ft_r2_0 0 q r B); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST1 | exact NB
                                | exact NX0 | exact NXB | exact BC | exact BQ | exact J0 | exact I0 | exact JC | exact JB]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (ft_r2_k d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST1 | exact NB
                                  | exact NX0 | exact NXB | exact BC | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
      + eapply (ft_r2_c d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST1 | exact NB
                                  | exact NX0 | exact NXB | exact BC | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
    - eapply (ft_r2_n d q r B); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BQ LE; lia | exact KN | exact FD | exact ST1 | exact NB
                                | exact NX0 | exact NXB | exact BC | exact BQ | exact J0 | exact I0 | exact JC | exact JB].
  Qed.
End FD.
End CANSEC2.
