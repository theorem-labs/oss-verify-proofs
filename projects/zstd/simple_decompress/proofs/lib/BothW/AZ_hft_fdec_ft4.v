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
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac fl_read1 MU WM j st1 ST1 st2 ST2 :=
    let H := fresh "RD" in
    kx_read_eq j H;
    first [ fd_rdnx HY AN MU WM H st1 ST1 | fd_rdw2 HY AN MU WM H st1 ST1 | fd_rdnx HY AN MU WM H st2 ST2 | fd_rdw2 HY AN MU WM H st2 ST2 | clear H ].
  Ltac fl_read_loop MU WM j k st1 ST1 st2 ST2 :=
    lazymatch k with O => idtac | S ?k' => try (fl_read1 MU WM j st1 ST1 st2 ST2); fl_read_loop MU WM (S j) k' st1 ST1 st2 ST2 end.
  Ltac fl_reads MU WM st1 ST1 st2 ST2 :=
    lazymatch goal with KXRD : reads_ok _ _ ?nz ?reads _ |- _ => let k := eval vm_compute in (length reads) in fl_read_loop MU WM nz k st1 ST1 st2 ST2 end.
  (* [comment removed for export] *)
  Ltac fl_lowbits name Hname TLR :=
    match goal with |- context [bv_unsigned ?w / 2 ^ (((-1 * ?nb) mod 2 ^ 64) mod 64)] =>
      set (name := bv_unsigned w / 2 ^ (((-1 * nb) mod 2 ^ 64) mod 64)) in *;
      assert (Hname : 0 <= name < 2 ^ nb)
        by (subst name; apply fast_bits_ltK; [apply (bv_unsigned_in_range 64) | match goal with N : 1 <= nb <= _ |- _ => clear - N TLR; lia end]);
      clearbody name
    end.
  (* [comment removed for export] *)
  Ltac fl_abs_cells :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with A : rw_cells bsegs m (SPB + 96) _ |- _ => kx_abs_hyp A end;
      match goal with B : rw_cells bsegs m (SPB + 80) _ |- _ => kx_abs_hyp B end;
      match goal with C : rw_cells bsegs m (SPB + 112) _ |- _ => kx_abs_hyp C end
    end.
  (* [comment removed for export] *)
  Ltac ec_sync :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _) _ _ _ _ ?m _) =>
      lazymatch goal with C : rw_cells bsegs m (SPB + 112) [_; C4 (Z_to_bv 64 ?BC); _; _; _; _] |- _ =>
        first [ constr_eq B BC | replace B with BC by (fd_clear_or; lia) ]
      end
    end.
  (* [comment removed for export] *)
  Ltac tp_sync :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B)) _ _ _ _ ?m _) =>
      lazymatch goal with C : rw_cells bsegs m (SPB + 112) [_; C4 (Z_to_bv 64 ?BC); _; _; _; _] |- _ =>
        first [ constr_eq B BC | replace B with BC by (fd_clear_or; lia) ]
      end
    end.
  Lemma ft_d2 : forall B, (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x12 x14 x23 x24 x25 x26 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 73 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xb0d6c mm ptr bc st1 st2 j i cont x1 x12 x14 x23 x24 x25 x26)) -> (forall mm ptr bc st1 st2 (cont : word) pad j i (x1 x12 x14 x23 x24 x25 x26 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xb0cd0 mm ptr bc st1 st2 j i cont x1 x12 x14 x23 x24 x25 x26)).
  Proof.
    intros B KP. intros until i. intros x1 x12 x14 x23 x24 x25 x26 FD ST1 ST2 BC BP J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 I0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX KP S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 BC BP J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap]
      [0xb0d6c; 0xb1508] 150%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange (2^tl - st1) 1 512; KZRange (2^tl - st2) 1 512; KZRange bc 0 100;
        KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    (* [comment removed for export] *)
    all: fl_reads MU WM st1 ST1 st2 ST2.
    all: pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB1R & NX10 & NX1R & SY1R & _ & _ & _); rewrite FAST1 in NB1R.
    all: set (nb1 := fc_nb tb st2) in *; set (nx1 := fc_nx tb st2) in *; set (sy1 := fc_sy tb st2) in *; clearbody nb1 nx1 sy1.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR.
    all: kx_mem.
    all: repeat match goal with H : ev _ _ = Z_to_bv 64 _ |- _ => rewrite H in *; clear H end.
    all: rewrite ?(unsigned_lit nx1), ?(unsigned_lit (sy1 + 256 * nb1)) in * by (clear - NB1R NX10 NX1R SY1R TLR P2; lia).
    all: assert (NBE1 : (65536 * (sy1 + 256 * nb1)) mod 2 ^ 64 / 16777216 = nb1) by (change 16777216 with (2^24); apply dsym_nb_of_w2; clear - NB1R SY1R TLR; lia);
         rewrite ?NBE1 in *; clear NBE1.
    all: fl_abs_cells.
    all: kx_tidy_run.
    all: try kx_sx3.
    all: fl_lowbits lba LBa TLR.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAFM" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 112) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: try replace (i + (DST + j)) with (DST + j + i) by (clear; lia).
    all: tp_sync.
    all: eapply KP; try close_fdm; try eassumption.
    all: try (right; exact BP).
    all: try (destruct BP as [BPL|BPR]; [left; clear - BPL NB1R; lia | right; exact BPR]).
    all: try (fd_clear_or; lia).
    all: match goal with |- ?G => idtac "LEFT" G end.
  Qed.
End FD.
End CANSEC2.
