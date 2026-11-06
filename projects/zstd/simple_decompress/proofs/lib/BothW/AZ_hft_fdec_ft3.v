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
  Notation TBST pc mm ptr bc st1 st2 j i cont x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 ptr) x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 st2) (Z_to_bv 64 st1) (Z_to_bv 64 bc))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation P1ST pc mm ptr bc st1 st2 j i cont x1 x13 x14 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 ptr) x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 st2) (Z_to_bv 64 st1) (Z_to_bv 64 bc))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation D2ST pc mm ptr bc st1 st2 j i cont x1 x12 x14 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (DST + cap - 2)) x12 (Z_to_bv 64 ptr) x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 (SRC + hs + 8)) x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 st2) (Z_to_bv 64 st1) (Z_to_bv 64 bc))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FNST pc mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac d2_sync :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B)) _ _ _ _ ?m _) =>
      lazymatch goal with C : rw_cells bsegs m (SPB + 112) [_; C4 (Z_to_bv 64 ?BC); _; C8 (Z_to_bv 64 ?PC); _; _] |- _ =>
        first [ constr_eq P PC | replace P with PC by (fd_clear_or; lia) ];
        first [ constr_eq B BC | replace B with BC by (fd_clear_or; lia) ]
      end
    end.
  Ltac tb_sync :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B)) _ _ _ _ ?m _) =>
      lazymatch goal with C : rw_cells bsegs m (SPB + 112) [_; C4 (Z_to_bv 64 ?BC); _; C8 (Z_to_bv 64 ?PC); _; _] |- _ =>
        first [ constr_eq P PC | replace P with PC by (fd_clear_or; lia) ];
        first [ constr_eq B BC | replace B with BC by (fd_clear_or; lia) ]
      end
    end.
  Definition ft_r1T (d q r B : Z) : Prop := (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x12 x14 x23 x24 x25 x26 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xb0cd0 mm ptr bc st1 st2 j i cont x1 x12 x14 x23 x24 x25 x26)) ->
    forall mm st1 st2 (cont : word) pad j i (x1 x13 x14 x22 x23 x24 x25 x26 : word),
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= j -> 0 <= i -> j + i + 2 <= cap -> B <= i ->
    evtF bsegs RNG Q (P1ST 0xb0bb0 mm (SRC + hs + d) (8 * q + r) st1 st2 j i cont x1 x13 x14 x22 x23 x24 x25 x26).
  (* [comment removed for export] *)
  Lemma ft_r1_0 : forall d q r B, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xb0cd0; 0xafb48; 0xb13f8; 0xb1508] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb0cd0) _ _ _ _) =>
             d2_sync; eapply (KN _ _ _ st1 st2 _ _ j i); try close_fdm; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xafb48) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_n : forall d q r B, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xb0cd0; 0xafb48; 0xb13f8; 0xb1508] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb0cd0) _ _ _ _) =>
             d2_sync; eapply (KN _ _ _ st1 st2 _ _ j i); try close_fdm; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xafb48) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_c : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xb0cd0; 0xafb48; 0xb13f8; 0xb1508] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb0cd0) _ _ _ _) =>
             d2_sync; eapply (KN _ _ _ st1 st2 _ _ j i); try close_fdm; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xafb48) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_k : forall d q r B, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> ft_r1T d q r B.
  Proof.
    intros d q r B DR DN QD QR RR BC64. unfold ft_r1T. intros KN. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST1 QX KN S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) [KAUnp SRC n] [0xb0cd0; 0xafb48; 0xb13f8; 0xb1508] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run; try kx_sx3.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb0cd0) _ _ _ _) =>
             d2_sync; eapply (KN _ _ _ st1 st2 _ _ j i); try close_fdm; try eassumption; try (unfold fl_ptr; fd_clear_or; lia); fd_clear_or;
             first [ lia | match goal with |- ?G => idtac "LEFT-N" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xafb48) _ _ _ _) =>
             apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_r1_f : (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 109 -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (FNST 0xb13f8 mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31)) ->
    forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x13 x14 x22 x23 x24 x25 x26 : word),
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 109 -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
    evtF bsegs RNG Q (P1ST 0xb0bb0 mm ptr bc st1 st2 j i cont x1 x13 x14 x22 x23 x24 x25 x26).
  Proof.
    intros KF. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 BC J0 I0 JC.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    clear - HY AN FAST1 QX KF S1 S2 BDC FA STD STL MI MU WM RSTK RSFR ST1 ST2 BC J0 I0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA P2 B_SPV.
    unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC) (@nil kza) [0xb13f8; 0xb1508] 20%nat
      ([KZRange bc 65 109; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange i 0 65536] ++ kzb) (@nil (Z * Z)) [(SPB, 152)].
    all: try (kx_side_pre; kx_lia).
    all: clear RSTK RSFR.
    all: kx_mem; kx_tidy_run.
    all: eapply (KF _ ptr bc st1 st2); try close_fdm; try eassumption; clear - BC J0 I0 JC; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ft_r1 : forall B, (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 109 -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (FNST 0xb13f8 mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31)) -> (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x12 x14 x23 x24 x25 x26 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xb0cd0 mm ptr bc st1 st2 j i cont x1 x12 x14 x23 x24 x25 x26)) -> (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x13 x14 x22 x23 x24 x25 x26 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 109 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap -> B <= i ->
        evtF bsegs RNG Q (P1ST 0xb0bb0 mm ptr bc st1 st2 j i cont x1 x13 x14 x22 x23 x24 x25 x26)).
  Proof.
    intros B KF KN. intros until i. intros x1 x13 x14 x22 x23 x24 x25 x26 FD ST1 ST2 BC BP J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'.
    destruct (Z_lt_le_dec 64 bc) as [OV | LE].
    { eapply (ft_r1_f KF); [exact FD | exact ST1 | exact ST2 | clear - BC OV; lia | exact J0 | exact I0 | exact JC]. }
    assert (PTR : fl_ptr SRC n hs ptr) by (destruct BP as [X|X]; [exfalso; clear - X LE; lia | exact X]).
    assert (QQ : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - BC LE; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & -> & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (Z_to_bv 64 (SRC + hs)) with (Z_to_bv 64 (SRC + hs + 0)) by (f_equal; clear; lia).
      replace (SRC + hs) with (SRC + hs + 0) in FD by (clear; lia).
      eapply (ft_r1_0 0 q r B); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BC LE; lia | exact KN | exact FD | exact ST1 | exact ST2
                                | exact J0 | exact I0 | exact JC | exact JB]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (ft_r1_k d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC LE; lia | exact KN | exact FD | exact ST1 | exact ST2
                                  | exact J0 | exact I0 | exact JC | exact JB].
      + eapply (ft_r1_c d q r B); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC LE; lia | exact KN | exact FD | exact ST1 | exact ST2
                                  | exact J0 | exact I0 | exact JC | exact JB].
    - eapply (ft_r1_n d q r B); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BC LE; lia | exact KN | exact FD | exact ST1 | exact ST2
                                | exact J0 | exact I0 | exact JC | exact JB].
  Qed.
End FD.
End CANSEC2.
