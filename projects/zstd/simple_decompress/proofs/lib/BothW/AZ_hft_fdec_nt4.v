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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_fse_bitinit AZ_fse_reloadi AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_nt1 AZ_hft_fdec_nt2 AZ_hft_fdec_nt3.
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
  Lemma nt_b : forall mm ptr j i st1 st2 bc nb1 sy1 (cont x1 x11 x19 x20 x21 x23 x24 x25 x26 x27 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> nb1 = fc_nb tb st1 -> sy1 = fc_sy tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 (Z_to_bv 64 (DT + 4 + 4 * st1)) (Z_to_bv 64 (65536 * (sy1 + 256 * nb1))) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 x21 (Z_to_bv 64 (0x7fff8000)) x23 x24 x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (nb1)))
          F (Z_to_bv 64 0xb1030) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC PTR NB1 SY1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1 ST1) as (NB1R & NX10 & NX1R & SY1R & _ & _ & _). rewrite FAST0 in NB1R.
    assert (PW1 : 1 <= 2 ^ fc_nb tb st1 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1)) as PP; clear - NB1R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st1) 9) as PP; clear - NB1R PP TLR; cbn in *; lia]).
    rewrite <- NB1 in *.
    rewrite <- SY1 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb1 MI ltac:(clear - NB1R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC PTR NB1R NX10 NX1R SY1R PW1 BK PTR I0 IC J0.
    hide PTR.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140512 128]
      [0xb147c; 0xb10ac; 0xb1508] 100%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange (2^tl - st1) 1 512; KZRange bc 0 64; KZRange nb1 0 9; KZRange sy1 0 255; KZRange (2 ^ nb1) 1 512; KZWord (140512 + 4 * nb1) 4 (2 ^ nb1 - 1);
        KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152); (140512, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SP_BS SPB0 SPB1 B_SPV SPR LOS SRCL SRCH HS1 HSN; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: nt_keepmu MU WM.
    all: try clear UD; try clear UW; try clear UM; try clear RM; try clear RSM; try clear RDST; try clear RSDST; try clear RWK; try clear RSWK; try clear RSTK; try clear RSFR; try clear RI; try clear BK.
    all: kx_mem.
    all: try (lazymatch goal with C : rw_cells bsegs ?m (SPB + 96) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => nt_nxcell C MU0 WM0 st1 ST1 RNX end).
    all: rewrite ?(unsigned_lit (fc_nx tb st1)) in * by (clear - NX10 NX1R TLR P2 PW1; lia).
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr; nt_opaddr j.
    all: hide PTR.
    all: first [ eapply nt_fin2; nl_hyps; first [close_fdm | (fd_clear_or; lia)]
               | unhide; eapply nt_c; nl_hyps; first [close_fdm | exact PTR | exact HT | (fd_clear_or; lia)] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_b0 : forall mm ptr j i st1 st2 bc nb1 sy1 (cont x1 x11 x19 x20 x21 x23 x24 x25 x26 x27 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> nb1 = fc_nb tb st1 -> sy1 = fc_sy tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (i)) (Z_to_bv 64 18446744073709411103) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 18446744073709551546) x11 (Z_to_bv 64 (DT + 4 + 4 * st1)) (Z_to_bv 64 (65536 * (sy1 + 256 * nb1))) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 x21 (Z_to_bv 64 (0x7fff8000)) x23 x24 x25 x26 x27 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (nb1)))
          F (Z_to_bv 64 0xb1030) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC NB1 SY1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1 ST1) as (NB1R & NX10 & NX1R & SY1R & _ & _ & _). rewrite FAST0 in NB1R.
    assert (PW1 : 1 <= 2 ^ fc_nb tb st1 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1)) as PP; clear - NB1R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st1) 9) as PP; clear - NB1R PP TLR; cbn in *; lia]).
    rewrite <- NB1 in *.
    rewrite <- SY1 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb1 MI ltac:(clear - NB1R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 QX DSYM HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC NB1R NX10 NX1R SY1R PW1 BK I0 IC J0.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140512 128]
      [0xb147c; 0xb10ac; 0xb1508] 100%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange (2^tl - st1) 1 512; KZRange bc 65 100; KZRange nb1 0 9; KZRange sy1 0 255; KZRange (2 ^ nb1) 1 512; KZWord (140512 + 4 * nb1) 4 (2 ^ nb1 - 1);
        KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152); (140512, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SP_BS SPB0 SPB1 B_SPV SPR LOS SRCL SRCH HS1 HSN; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: nt_keepmu MU WM.
    all: try clear UD; try clear UW; try clear UM; try clear RM; try clear RSM; try clear RDST; try clear RSDST; try clear RWK; try clear RSWK; try clear RSTK; try clear RSFR; try clear RI; try clear BK.
    all: kx_mem.
    all: try (lazymatch goal with C : rw_cells bsegs ?m (SPB + 96) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => nt_nxcell C MU0 WM0 st1 ST1 RNX end).
    all: rewrite ?(unsigned_lit (fc_nx tb st1)) in * by (clear - NX10 NX1R TLR P2 PW1; lia).
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr; nt_opaddr j.
    all: first [ eapply nt_fin2; nl_hyps; first [close_fdm | (fd_clear_or; lia)] | (exfalso; fd_clear_or; lia) ].
  Qed.

End ND.
End CANSEC2.
