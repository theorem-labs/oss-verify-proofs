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
  Notation HDST pc mm ptr bc st1 st2 j cont x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) cont x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 st1) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation ECST pc mm ptr bc s1 nb1 nb2 nx2 j cont x1 x13 x21 x22 x23 x26 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) cont (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 + 4 * s1)) x13 (Z_to_bv 64 nb2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 nb1) x29 x30 (Z_to_bv 64 nx2))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FCST pc mm ptr bc s2 nb2 nx3 nb3 j cont x1 x7 x13 x21 x22 x23 x26 x28 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) cont x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 + 4 * s2)) x13 (Z_to_bv 64 nb2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 nx3) (Z_to_bv 64 nb3) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation TLST pc mm ptr bc st1 st2 j cont x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 cont x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) x11 x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 st1) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac fd_rdsy HY AN MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 1 false =>
    rewrite (fd_rd_syA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
  (* [comment removed for export] *)
  Ltac fl_read1 MU WM j st1 ST1 st2 ST2 :=
    let H := fresh "RD" in
    kx_read_eq j H;
    first [ fd_rdnx HY AN MU WM H st1 ST1 | fd_rdsy HY AN MU WM H st1 ST1 | fd_rdnb HY AN MU WM H st1 ST1
          | fd_rdnx HY AN MU WM H st2 ST2 | fd_rdsy HY AN MU WM H st2 ST2 | fd_rdnb HY AN MU WM H st2 ST2 | clear H ].
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
      match goal with A : rw_cells bsegs m (SPB + 64) _ |- _ => kx_abs_hyp A end;
      match goal with B : rw_cells bsegs m (SPB + 48) _ |- _ => kx_abs_hyp B end;
      match goal with C : rw_cells bsegs m (SPB + 80) _ |- _ => kx_abs_hyp C end
    end.
  (* [comment removed for export] *)
  Lemma fl_d3 : forall B, (forall mm ptr bc s2 nb2 nx3 nb3 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x7 x13 x21 x22 x23 x26 x28 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= s2 < 2^tl -> 1 <= nb2 <= tl -> 1 <= nb3 <= tl -> 0 <= nx3 -> nx3 + 2^nb3 <= 2^tl -> 0 <= bc <= 73 ->
        SRC + hs <= ptr -> ptr + 8 <= SRC + n -> 0 <= j -> j + 4 <= cap -> B <= j ->
        evtF bsegs RNG Q (FCST 0xad2c0 mm ptr bc s2 nb2 nx3 nb3 j cont x1 x7 x13 x21 x22 x23 x26 x28 x31)) -> (forall mm ptr bc s1 nb1 nb2 nx2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x13 x21 x22 x23 x26 x29 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= s1 < 2^tl -> 1 <= nb1 <= tl -> 1 <= nb2 <= tl -> 0 <= nx2 -> nx2 + 2^nb2 <= 2^tl -> 0 <= bc <= 64 ->
        SRC + hs <= ptr -> ptr + 8 <= SRC + n -> 0 <= j -> j + 4 <= cap -> B <= j ->
        evtF bsegs RNG Q (ECST 0xad244 mm ptr bc s1 nb1 nb2 nx2 j cont x1 x13 x21 x22 x23 x26 x29 x30)).
  Proof.
    intros B KF. intros until j. intros x1 x13 x21 x22 x23 x26 x29 x30 FD ST1 NB1R NB2R NX20 NX2R BC PLO PHI J0 J4 JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX KF S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 NB1R NB2R NX20 NX2R BC PLO PHI J0 J4 JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap]
      [0xad2c0] 200%nat
      ([KZRange s1 0 511; KZRange (2^tl - s1) 1 512; KZRange bc 0 64; KZRange nb1 1 9; KZRange nb2 1 9;
        KZRange ptr 4096 (2^47); KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: fl_reads MU WM s1 ST1 s1 ST1.
    all: pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN s1 ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _); rewrite FAST1 in NB3R.
    all: set (nb3 := fc_nb tb s1) in *; set (nx3 := fc_nx tb s1) in *; set (sy3 := fc_sy tb s1) in *; clearbody nb3 nx3 sy3.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR.
    all: kx_mem.
    all: repeat match goal with H : ev _ _ = Z_to_bv 64 _ |- _ => rewrite H in *; clear H end.
    all: rewrite ?(unsigned_lit nx3), ?(unsigned_lit sy3), ?(unsigned_lit nb3), ?(unsigned_lit nb1), ?(unsigned_lit nb2), ?(unsigned_lit nx2) in * by (clear - NB1R NB2R NX20 NX2R NB3R NX30 NX3R SY3R TLR P2; lia).
    all: fl_abs_cells.
    all: kx_tidy_run.
    all: fl_lowbits lbb LBb TLR. all: try fl_lowbits lbc LBc TLR.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAFM" pc R end.
    all: kx_setreg 12 (DT + 4 + 4 * (nx2 + lbb)).
    all: eapply (KF _ _ _ (nx2 + lbb) nb2 nx3 nb3); try close_fdms; try eassumption; fd_clear_or;
         first [ lia | rewrite Z.mod_small by lia; lia | match goal with |- ?G => idtac "LEFT" G end; fail ].
  Qed.
  Lemma fl_d34 : forall B, (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap -> B + 4 <= j ->
        evtF bsegs RNG Q (HDST 0xad08c mm ptr bc st1 st2 j cont x1 x7 x12 x13 x21 x22 x23 x26 x28 x30 x31)) -> (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xad7f0 mm ptr bc st1 st2 j cont x1 x5 x7 x11 x12 x13 x21 x22 x23 x25 x26 x28 x30 x31)) -> (forall mm ptr bc s2 nb2 nx3 nb3 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x7 x13 x21 x22 x23 x26 x28 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= s2 < 2^tl -> 1 <= nb2 <= tl -> 1 <= nb3 <= tl -> 0 <= nx3 -> nx3 + 2^nb3 <= 2^tl -> 0 <= bc <= 73 ->
        SRC + hs <= ptr -> ptr + 8 <= SRC + n -> 0 <= j -> j + 4 <= cap -> B <= j ->
        evtF bsegs RNG Q (FCST 0xad2c0 mm ptr bc s2 nb2 nx3 nb3 j cont x1 x7 x13 x21 x22 x23 x26 x28 x31)).
  Proof.
    intros B KH KT0. intros until j. intros x1 x7 x13 x21 x22 x23 x26 x28 x31 FD ST2 NB2R NB3R NX30 NX3R BC PLO PHI J0 J4 JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX KH KT0 S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NB2R NB3R NX30 NX3R BC PLO PHI J0 J4 JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap]
      [0xad08c; 0xad7f0] 250%nat
      ([KZRange s2 0 511; KZRange (2^tl - s2) 1 512; KZRange bc 0 73; KZRange nb2 1 9; KZRange nb3 1 9;
        KZRange ptr 4096 (2^47); KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    (* [comment removed for export] *)
    all: fl_reads MU WM s2 ST2 s2 ST2.
    all: pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN s2 ST2) as (NB4R & NX40 & NX4R & SY4R & _ & _ & _); rewrite FAST1 in NB4R.
    all: set (nb4 := fc_nb tb s2) in *; set (nx4 := fc_nx tb s2) in *; set (sy4 := fc_sy tb s2) in *; clearbody nb4 nx4 sy4.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR.
    all: kx_mem.
    all: repeat match goal with H : ev _ _ = Z_to_bv 64 _ |- _ => rewrite H in *; clear H end.
    all: rewrite ?(unsigned_lit nx4), ?(unsigned_lit sy4), ?(unsigned_lit nb4), ?(unsigned_lit nb2), ?(unsigned_lit nb3), ?(unsigned_lit nx3) in * by (clear - NB2R NB3R NX30 NX3R NB4R NX40 NX4R SY4R TLR P2; lia).
    all: fl_abs_cells.
    all: kx_tidy_run.
    all: try kx_sx3.
    all: fl_lowbits lba LBa TLR. all: fl_lowbits lbb LBb TLR.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAFM" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: replace (DST + j + 4) with (DST + (j + 4)) by (clear; lia).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad08c) _ _ _ _) =>
             eapply KH; try close_fdms; try eassumption; try (unfold fl_ptr; right; clear - PLO PHI; lia); fd_clear_or;
             first [ lia | rewrite Z.mod_small by lia; lia | match goal with |- ?G => idtac "LEFT-H" G end; fail ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad7f0) _ _ _ _) =>
             eapply KT0; try close_fdms; try eassumption; fd_clear_or;
             first [ lia | rewrite Z.mod_small by lia; lia | match goal with |- ?G => idtac "LEFT-T" G end; fail ]
         end.
  Qed.
End FD.
End CANSEC2.
