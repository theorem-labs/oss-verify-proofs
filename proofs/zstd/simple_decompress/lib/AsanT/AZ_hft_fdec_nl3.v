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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_nl1 AZ_hft_fdec_nl2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fd_lowbits :=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?nb + -1) mod 2 ^ 64)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x ((2 ^ nb + -1) mod 2 ^ 64)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt; lia); clearbody lb
  | |- context [Z.land ?x (2 ^ ?nb - 1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb - 1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt2; lia); clearbody lb
  | |- context [Z.land ?x (2 ^ ?nb + -1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb + -1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; replace (2 ^ nb + -1) with (2 ^ nb - 1) by (clear; lia); apply fuland_mask_lt2; lia); clearbody lb
  end.
(* [comment removed for export] *)
Ltac nl_kz SRC n hs cap DST tl DT WK wksz SPB SPV := constr:(
  [KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange n 0 65536; KZRange hs 1 65536;
   KZRange cap 0 65536; KZRange DST 4096 (2^47); KZRange (DST + cap) 4096 (2^47); KZRange (2^tl) 32 512; KZRange tl 5 9;
   KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange (WK + wksz) 4096 (2^47); KZRange wksz 0 (2^32);
   KZRange SPB 17594333495296 (2^47 - 256); KZAlign SPB 32; KZRange SPV 17594333495296 (2^47 - 16);
   KZWr DST cap; KZImg 0x22660 0x226e0]).
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

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
             (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation NHDST pc mm ptr bc st1 st2 cont j x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 (Z_to_bv 64 st1) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) x21 x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation NTLST pc mm bc st1 st2 cont j x1 x10 x11 x12 x15 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 (Z_to_bv 64 st1) (Z_to_bv 64 (SRC + hs + 8)) x15 (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 (Z_to_bv 64 (DST + cap)) x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Hypothesis TAILK : (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x11 x12 x15 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j <= cap ->
        evtF bsegs RNG Q (NTLST 0xacae8 mm bc st1 st2 cont j x1 (Z_to_bv 64 ptr) x11 x12 x15 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31)).
  Hypothesis OVFK : (forall mm bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x10 x11 x12 x15 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (NTLST 0xacaec mm bc st1 st2 cont j x1 x10 x11 x12 x15 (Z_to_bv 64 0x22700) x21 x22 x23 x25 x26 x28 x29 x30 x31)).
  (* [comment removed for export] *)
  Definition nl_headJ (j : Z) : Prop :=
    forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 (x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 : word),
      FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
      0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
      evtF bsegs RNG Q (NHDST 0xac678 mm ptr bc st1 st2 cont j x1 x12 x21 x22 x23 x26 x28 x29 x30 x31).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac nl_xr i :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                                              ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
      eval cbn [nth] in (nth i [x1; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                                x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] x1)
    end.
  (* [comment removed for export] *)
  Ltac nl_rdx i MU WM st STR W :=
    let v := nl_xr i in lazymatch v with context [ev ?E ?j] => kx_read_eq j W end;
    fd_rdnx HY AN MU WM W st STR.
  Ltac nl_rdb i MU WM st STR W :=
    let v := nl_xr i in lazymatch v with context [ev ?E ?j] => kx_read_eq j W end;
    fd_rdnb HY AN MU WM W st STR.
  Ltac nl_rdy i MU WM st STR W :=
    let v := nl_xr i in lazymatch v with context [ev ?E ?j] => kx_read_eq j W end;
    lazymatch type of W with _ = rdval _ ?mx (wa ?a) 1 false =>
      rewrite (fd_rd_syA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM STR ltac:(clear; lia)) in W end.
  (* [comment removed for export] *)
  Ltac nl_aset i st :=
    let v := nl_xr i in
    lazymatch v with Z_to_bv 64 ?A =>
      replace A with (DT + 4 + 4 * st) by (fd_clear_or; rewrite ?Z.mod_small by lia; lia) end.
  (* [comment removed for export] *)
  Ltac nl_addr :=
    try match goal with |- context [Z_to_bv 64 (DT + 4 * ?st + 4)] => replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) by (clear; lia) end;
    try match goal with |- context [Z_to_bv 64 (4 * ?st + DT + 4)] => replace (4 * st + DT + 4) with (DT + 4 + 4 * st) by (clear; lia) end.
  (* [comment removed for export] *)
  Ltac nl_hyps :=
    lazymatch goal with
    | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
    | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
    | |- _ = 0 => exact FAST0
    | |- fd_exitK _ _ _ _ _ _ _ _ _ _ _ _ => exact QX
    | |- bit_init_stmtA_at _ => exact BITINIT
    | |- fse_initds_stmtA => exact INITDS
    | |- _ => first [exact TAILK | exact OVFK | idtac]
    end.
  (* [comment removed for export] *)
  Ltac nl_side := fd_clear_or; first [lia | (rewrite ?Z.mod_small by lia; lia) | (Z.div_mod_to_equations; lia)].
  (* [comment removed for export] *)

  Definition nl_hT (d q r RLO RHI : Z) : Prop :=
    forall mm st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 : word),
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= j -> RLO <= cap - j <= RHI -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q (NHDST 0xac678 mm (SRC + hs + d) (8 * q + r) st1 st2 cont j x1 x12 x21 x22 x23 x26 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma nl_h0 : forall d q r, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 0 65536.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 0 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma nl_hn : forall d q r, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 4 65536.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - J0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma nl_hn_x : forall d q r, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 0 3.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 0 3;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma nl_hc : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 4 65536.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - J0 JC; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma nl_hc_x : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 0 3.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 0 3;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma nl_hk : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 -> nl_hT d q r 0 65536.
  Proof.
    intros d q r DR DN QD QR RR BC64. unfold nl_hT. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 J0 JC HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HJ TAILK OVFK S1 S2 BDC FA TB SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR ST1 ST2 J0 JC TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB DR DN QD QR RR BC64.
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xac748; 0xacae8] 150%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange j 0 65536; KZRange (cap - j) 0 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZWr (SPB + 80) 40; KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 JC DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "BDC" cs end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xac748) _ _ _ _) =>
             eapply nl_d1; nl_hyps; first [close_fdms | nl_side | exact HJ | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia]) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia)]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xacae8) _ _ _ _) =>
             eapply (TAILK _ _ _ st1 st2); first [close_fdms | nl_side | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma nl_step : forall j, nl_headJ (j + 4) ->
    forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 (x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 : word),
      FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
      0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
      evtF bsegs RNG Q (NHDST 0xac678 mm ptr bc st1 st2 cont j x1 x12 x21 x22 x23 x26 x28 x29 x30 x31).
  Proof.
    intros j HJ. intros until j96. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 BC PTR JC.
    pose proof HY as HY'. open_hy HY'.
    assert (QQ : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - BC; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & -> & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (Z_to_bv 64 (SRC + hs)) with (Z_to_bv 64 (SRC + hs + 0)) by (f_equal; clear; lia).
      eapply (nl_h0 0 q r); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                            | clear - JC; lia | clear - JC CAPH; lia | exact HJ]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (nl_hk d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                               | clear - JC; lia | clear - JC CAPH; lia | exact HJ].
      + destruct (Z_lt_le_dec (cap - j) 4) as [RM | RM].
        * eapply (nl_hc_x d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                                   | clear - JC; lia | clear - JC RM; lia | exact HJ].
        * eapply (nl_hc d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                                 | clear - JC; lia | clear - JC RM CAPH; lia | exact HJ].
    - destruct (Z_lt_le_dec (cap - j) 4) as [RM | RM].
      + eapply (nl_hn_x d q r); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                                 | clear - JC; lia | clear - JC RM; lia | exact HJ].
      + eapply (nl_hn d q r); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2
                               | clear - JC; lia | clear - JC RM CAPH; lia | exact HJ].
  Qed.

  (* [comment removed for export] *)
  Lemma nl_loop : forall (k : nat) j, cap - j <= Z.of_nat k -> nl_headJ j.
  Proof.
    induction k as [|k IH]; intros j HK; unfold nl_headJ; intros until j96; intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 BC PTR JC.
    - eapply nl_step; try eassumption. unfold nl_headJ. intros. exfalso. match goal with J : 0 <= j + 4 <= cap |- _ => clear - HK J; lia end.
    - eapply nl_step; try eassumption. apply IH. clear - HK. lia.
  Qed.
  Lemma nl_loop_head : (forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 j (x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
        evtF bsegs RNG Q (NHDST 0xac678 mm ptr bc st1 st2 cont j x1 x12 x21 x22 x23 x26 x28 x29 x30 x31)).
  Proof. intros until j. intros x1 x12 x21 x22 x23 x26 x28 x29 x30 x31 FD ST1 ST2 BC PTR JC. eapply (nl_loop (Z.to_nat (cap - j + 1)) j); try eassumption. clear - JC. lia. Qed.
End ND.
End CANSEC2.
