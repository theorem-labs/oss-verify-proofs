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
  (* [comment removed for export] *)
  Notation D2ST pc mm ptr bc cont st2 j i conto bco nx nb x1 x12 x22 x23 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + i)) x12 (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont (Z_to_bv 64 nb) x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bco) (Z_to_bv 64 nx) (Z_to_bv 64 bc) conto)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation P2ST pc mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + i)) x12 (Z_to_bv 64 (DST + j + i + 1)) (Z_to_bv 64 nb) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) cont x21 (Z_to_bv 64 nx) x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (bc + nb)) (Z_to_bv 64 st1) (Z_to_bv 64 bc) x31)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac fl_rdsy MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 1 false =>
    rewrite (fd_rd_syA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
  Ltac fl_read1 MU WM j st ST :=
    let H := fresh "RD" in
    kx_read_eq j H;
    first [ fd_rdnx HY AN MU WM H st ST | fd_rdnb HY AN MU WM H st ST | fl_rdsy MU WM H st ST | clear H ].
  Ltac fl_read_loop MU WM j k st ST :=
    lazymatch k with O => idtac | S ?k' => try (fl_read1 MU WM j st ST); fl_read_loop MU WM (S j) k' st ST end.
  Ltac fl_reads MU WM st ST :=
    lazymatch goal with KXRD : reads_ok _ _ ?nz ?reads _ |- _ => let k := eval vm_compute in (length reads) in fl_read_loop MU WM nz k st ST end.
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
  (* [comment removed for export] *)
  Lemma ft_d2 : forall B, (forall mm ptr bc (cont : word) st1 j i nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x21 x23 x25 x26 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm -> 0 <= st1 < 2^tl ->
        1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i ->
        j + i + 3 <= cap -> B <= i -> evtF bsegs RNG Q (P2ST 0xad654 mm ptr bc cont st1 j i nx nb x1 x12 x21 x23 x25 x26 x31)) ->
      (forall mm ptr bc (cont : word) st2 j i (conto : word) bco nx nb (j48 j64 j80 j88 j92 j96 : list byte) (x1 x12 x22 x23 x25 x26 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st2 < 2^tl -> 1 <= nb <= tl -> 0 <= nx -> nx + 2^nb <= 2^tl -> 0 <= bco <= 100 -> 0 <= bc <= 64 ->
        fl_ptr SRC n hs ptr -> 0 <= j -> 0 <= i -> j + i + 3 <= cap -> B <= i ->
        evtF bsegs RNG Q (D2ST 0xad5dc mm ptr bc cont st2 j i conto bco nx nb x1 x12 x22 x23 x25 x26)).
  Proof.
    intros B KP mm ptr bc cont st2 j i conto bco nx nb j48 j64 j80 j88 j92 j96 x1 x12 x22 x23 x25 x26 FD ST2 NBR NX0 NXR BCO BC BP J0 I0 JC JB.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    assert (CP : 0 < cap) by (clear - J0 I0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear - HY AN FAST1 QX KP S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST2 NBR NX0 NXR BCO BC BP J0 I0 JC JB TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB.
    clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap]
      [0xad654] 150%nat
      ([KZRange st2 0 511; KZRange (2^tl - st2) 1 512; KZRange bc 0 64; KZRange bco 0 100; KZRange nb 1 9;
        KZRange j 0 65536; KZRange i 0 65536; KZRange (cap - j - i) 2 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 I0 JC DTE WKL WKH ROOM P2 ST2 NBR BCO BC TLR SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    (* [comment removed for export] *)
    all: fl_reads MU WM st2 ST2.
    all: pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _); rewrite FAST1 in NB2R.
    all: set (nb2 := fc_nb tb st2) in *; set (nx2 := fc_nx tb st2) in *; set (sy2 := fc_sy tb st2) in *; clearbody nb2 nx2 sy2.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR.
    all: kx_mem.
    all: repeat match goal with H : ev _ _ = Z_to_bv 64 _ |- _ => rewrite H in *; clear H end.
    all: rewrite ?(unsigned_lit nx2), ?(unsigned_lit nb2), ?(unsigned_lit sy2) in * by (clear - NB2R NX20 NX2R SY2R TLR P2; lia).
    all: fl_abs_cells.
    all: kx_tidy_run.
    all: try kx_sx3.
    all: fl_lowbits lba LBa TLR.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAFM" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: try replace (i + (DST + j)) with (DST + j + i) by (clear; lia).
    all: try replace (nb2 + bc) with (bc + nb2) by (clear; lia).
    all: eapply KP; try close_fdms; try eassumption.
    all: try (fd_clear_or; lia).
    all: match goal with |- ?G => idtac "LEFT" G end.
  Qed.
End FD.
End CANSEC2.
