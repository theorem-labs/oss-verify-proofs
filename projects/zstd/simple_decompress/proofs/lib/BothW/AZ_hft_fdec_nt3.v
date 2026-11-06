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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_fse_bitinit AZ_fse_reloadi AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_nt1 AZ_hft_fdec_nt2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fd_lowbits_in T :=
  match T with
  | context [Z.land ?x ((2 ^ ?nb + -1) mod 2 ^ 64)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x ((2 ^ nb + -1) mod 2 ^ 64)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt; lia); clearbody lb
  | context [Z.land ?x (2 ^ ?nb - 1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb - 1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt2; lia); clearbody lb
  | context [Z.land ?x (2 ^ ?nb + -1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb + -1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; replace (2 ^ nb + -1) with (2 ^ nb - 1) by (clear; lia); apply fuland_mask_lt2; lia); clearbody lb
  end.
(* [comment removed for export] *)
Ltac fd_lowbits :=
  repeat match goal with
  | |- ?G => fd_lowbits_in G
  | H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => fd_lowbits_in T end
  end.
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
  Hypothesis RELOADI : fse_reload_int_stmtA.
  Hypothesis DSYM : fse_dsym_stmtA.

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 n) (Z_to_bv 64 WK)
             (Z_to_bv 64 wksz) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + hs)) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac nt_w2 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ ?x13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x13 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdw2 HY AN MU WM W st STR.
  (* [comment removed for export] *)
  Ltac nt_nx11 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ ?x11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x11 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdnx HY AN MU WM W st STR.
  Ltac nl_nb sy nb SYR NBR TLR :=
    try replace (65536 * (sy + 256 * nb) / 16777216) with nb in * by (clear - SYR NBR TLR; Z.div_mod_to_equations; lia);
    try replace ((65536 * (sy + 256 * nb)) mod 2 ^ 64 / 16777216) with nb in * by (clear - SYR NBR TLR; rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia).
  Ltac nl_addr :=
    try match goal with |- context [Z_to_bv 64 (DT + 4 * ?st + 4)] => replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) by (clear; lia) end;
    try match goal with |- context [Z_to_bv 64 (4 * ?st + DT + 4)] => replace (4 * st + DT + 4) with (DT + 4 + 4 * st) by (clear; lia) end.
  Ltac nt_opaddr j :=
    try match goal with |- context [Z_to_bv 64 (DST + j + (?i + 1))] => replace (DST + j + (i + 1)) with (DST + j + i + 1) by (clear; lia) end;
    try match goal with |- context [Z_to_bv 64 (DST + (j + ?i))] => replace (DST + (j + i)) with (DST + j + i) by (clear; lia) end.
  (* [comment removed for export] *)
  Ltac nt_keepmu MU WM := pose proof MU as MU0; pose proof WM as WM0; hide MU0; hide WM0.
  (* [comment removed for export] *)
  Ltac nt_nxcell C MU0 WM0 st STR W :=
    unfold hidden in MU0, WM0;
    lazymatch type of C with context [ev ?E ?j] => kx_read_eq j W end; fd_rdnx HY AN MU0 WM0 W st STR; rewrite W in *; clear W MU0 WM0.
  Ltac nl_hyps :=
    lazymatch goal with
    | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
    | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
    | |- _ = 0 => exact FAST0
    | |- fd_exitK _ _ _ _ _ _ _ _ _ _ _ _ => exact QX
    | |- bit_init_stmtA_at _ => exact BITINIT
    | |- fse_initds_stmtA => exact INITDS
    | |- fse_reload_int_stmtA => exact RELOADI
    | |- fse_dsym_stmtA => exact DSYM
    | |- _ => idtac
    end.
  Ltac nl_trap29 SYR NBR TLR :=
    exfalso;
    match goal with
    | H : context [536870912] |- _ => revert H; clear - SYR NBR TLR; intros H; rewrite ?unsigned_lit in H by lia;
                                     rewrite ?Z.mod_small in H by lia; Z.div_mod_to_equations; lia
    end.
  (* [comment removed for export] *)
  Definition nt_headI (j i : Z) : Prop :=
    forall mm ptr bc st1 st2 (cont : word) pad (x1 x11 x12 x13 x19 x20 x21 x23 x24 x25 x26 x27 x31 : word),
      FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
      0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= i -> j + i + 2 <= cap -> 0 <= j ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 x13 (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 x21 (Z_to_bv 64 (0x7fff8000)) x23 x24 x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb0fcc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Lemma nt_d : forall mm ptr j i st1 st2 bc1 (cont x1 x11 x12 x13 x19 x22 x23 x25 x26 x27 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc1 ptr pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc1 <= 64 -> fl_ptr SRC n hs ptr ->
    0 <= i -> j + i + 3 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 x13 (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SRC + hs + 8)))
          F (Z_to_bv 64 0xb11c8) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC1 PTR I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R.
    assert (PW2 : 1 <= 2 ^ fc_nb tb st2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2)) as PP; clear - NB2R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st2) 9) as PP; clear - NB2R PP TLR; cbn in *; lia]).
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC1 PTR NB2R NX20 NX2R SY2R PW2 PTR I0 IC J0.
    hide PTR.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl)]
      [0xb122c; 0xb1508] 60%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange (2^tl - st2) 1 512; KZRange bc1 0 64;
        KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SP_BS SPB0 SPB1 B_SPV SPR LOS SRCL SRCH HS1 HSN; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: try (nt_w2 MU WM st2 ST2 RW2).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => rewrite RW2 in *; nl_trap29 SY2R NB2R TLR end).
    all: try clear UD; try clear UW; try clear UM; try clear RM; try clear RSM; try clear RDST; try clear RSDST; try clear RWK; try clear RSWK; try clear RSTK; try clear RSFR; try clear RI; try clear BK.
    all: kx_mem; try (rewrite RW2 in *; clear RW2).
    all: rewrite ?(unsigned_lit (fc_sy tb st2 + 256 * fc_nb tb st2)) in * by (clear - SY2R NB2R TLR P2; lia).
    all: nl_nb (fc_sy tb st2) (fc_nb tb st2) SY2R NB2R TLR.
    all: try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr; nt_opaddr j.
    all: eapply nt_e; nl_hyps; first [close_fdm | exact PTR | exact HT | reflexivity | (fd_clear_or; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_0 : forall d q r, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 (cont x1 x11 x12 x19 x22 x23 x25 x26 x27 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 (Z_to_bv 64 (8 * q + r)) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb10ac) fc None mm (seg_rom bsegs)).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until pad. intros FD ST1 ST2 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW UM RM RSM SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xb11c8; 0xafb48; 0xb1508] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 112) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d; first [close_fdm | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_n : forall d q r, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 (cont x1 x11 x12 x19 x22 x23 x25 x26 x27 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 (Z_to_bv 64 (8 * q + r)) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb10ac) fc None mm (seg_rom bsegs)).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until pad. intros FD ST1 ST2 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW UM RM RSM SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xb11c8; 0xafb48; 0xb1508] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 112) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d; first [close_fdm | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_c : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 (cont x1 x11 x12 x19 x22 x23 x25 x26 x27 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 (Z_to_bv 64 (8 * q + r)) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb10ac) fc None mm (seg_rom bsegs)).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until pad. intros FD ST1 ST2 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW UM RM RSM SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xb11c8; 0xafb48; 0xb1508] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 112) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d; first [close_fdm | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_k : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 (cont x1 x11 x12 x19 x22 x23 x25 x26 x27 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont (8 * q + r) (SRC + hs + d) pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 (Z_to_bv 64 (8 * q + r)) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb10ac) fc None mm (seg_rom bsegs)).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until pad. intros FD ST1 ST2 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW UM RM RSM SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xb11c8; 0xafb48; 0xb1508] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 112) 40; KZDisj (SPB + 80) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 112) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d; first [close_fdm | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdm; close_fdm | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c : forall mm ptr j i st1 st2 bc (cont x1 x11 x12 x19 x22 x23 x25 x26 x27 x31 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 x12 (Z_to_bv 64 (bc)) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 (Z_to_bv 64 (0x7fff8000)) x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) x31)
          F (Z_to_bv 64 0xb10ac) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC PTR I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'.
    assert (QQ : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - BC; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & -> & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (SRC + hs) with (SRC + hs + 0) in FD by (clear; lia).
      eapply (nt_c_0 0 q r); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact I0 | exact IC | exact J0 | exact HT]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (nt_c_k d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact I0 | exact IC | exact J0 | exact HT].
      + eapply (nt_c_c d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact I0 | exact IC | exact J0 | exact HT].
    - eapply (nt_c_n d q r); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact I0 | exact IC | exact J0 | exact HT].
  Qed.

End ND.
End CANSEC2.
