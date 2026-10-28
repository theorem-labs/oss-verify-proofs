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
  Ltac nl_addr := try match goal with |- context [Z_to_bv 64 (DT + 4 * ?st + 4)] => replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) by (clear; lia) end.
  (* [comment removed for export] *)
  Ltac nl_side := fd_clear_or; first [lia | (rewrite ?Z.mod_small by lia; lia) | (Z.div_mod_to_equations; lia)].
  (* [comment removed for export] *)
  Lemma nl_d5 : forall mm ptr j st1n st2n bc2 nb3 nx3 nb4 sy4 nx4 (cont x1 x12 x13 x22 x23 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1n < 2^tl -> 0 <= st2n < 2^tl -> 0 <= bc2 <= 82 -> nb3 = fc_nb tb st1n -> nx3 = fc_nx tb st1n ->
    nb4 = fc_nb tb st2n -> sy4 = fc_sy tb st2n -> nx4 = fc_nx tb st2n ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 nb3) (Z_to_bv 64 nx3) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 bc2) x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 nx4) (Z_to_bv 64 (2 ^ nb3 - 1)) (Z_to_bv 64 sy4) (Z_to_bv 64 nb4))
          F (Z_to_bv 64 0xac950) fc None mm (seg_rom bsegs)).
  Proof.
    intros until j96. intros FD ST1 ST2 BC2 NB3 NX3 NB4 SY4 NX4 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R. rewrite <- NB3 in NB3R, NX3R. rewrite <- NX3 in NX30, NX3R.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2n ST2) as (NB4R & NX40 & NX4R & SY4R & _ & _ & _). rewrite FAST0 in NB4R. rewrite <- NB4 in NB4R, NX4R. rewrite <- NX4 in NX40, NX4R. rewrite <- SY4 in SY4R.
    assert (P3 : 1 <= 2 ^ nb3 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb3) as P1; clear - NB3R P1; lia | pose proof (Z.pow_le_mono_r 2 nb3 9) as P1; clear - NB3R P1 TLR; cbn in *; lia]).
    assert (P4 : 1 <= 2 ^ nb4 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb4) as P1; clear - NB4R P1; lia | pose proof (Z.pow_le_mono_r 2 nb4 9) as P1; clear - NB4R P1 TLR; cbn in *; lia]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb4 MI ltac:(clear - NB4R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC2 NB3R NX30 NX3R NB4R NX40 NX4R SY4R J0 J4 PTR BK P3 P4.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140896 128]
      [0xac678; 0xacaec] 80%nat
      ([KZRange st1n 0 511; KZRange st2n 0 511; KZRange bc2 0 82; KZRange nb3 0 9; KZRange nx3 0 511; KZRange (2^nb3) 1 512;
        KZRange nb4 0 9; KZRange sy4 0 255; KZRange nx4 0 511; KZRange (2^nb4) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap;
        KZImg 0x22660 0x226e0; KZWord (140896 + 4 * nb4) 4 (2^nb4 - 1)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120); (140896, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    (* [comment removed for export] *)
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI BK.
    all: kx_mem.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: replace (DST + j + 4) with (DST + (j + 4)) by (clear; lia).
    all: unhide.
    all: first [ eapply HJ; first [close_fdms | exact PTR | nl_side]
               | eapply OVFK; first [close_fdms | nl_side] ].
  Qed.
  Lemma nl_d4r : forall mm ptr j st1n st2n bc2 nb3 nx3 (cont x1 x13 x22 x23 x26 x28 x30 x31 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1n < 2^tl -> 0 <= st2n < 2^tl -> 0 <= bc2 <= 82 -> nb3 = fc_nb tb st1n -> nx3 = fc_nx tb st1n ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 nb3) (Z_to_bv 64 nx3) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 + 4 * st2n)) x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 bc2) x22 x23 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
               x28 (Z_to_bv 64 (2 ^ nb3 - 1)) x30 x31)
          F (Z_to_bv 64 0xac90c) fc None mm (seg_rom bsegs)).
  Proof.
    intros until j96. intros FD ST1 ST2 BC2 NB3 NX3 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R. rewrite <- NB3 in NB3R, NX3R. rewrite <- NX3 in NX30, NX3R.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2n ST2) as (NB4R & NX40 & NX4R & SY4R & _ & _ & _). rewrite FAST0 in NB4R.
    assert (P3 : 1 <= 2 ^ nb3 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb3) as P1; clear - NB3R P1; lia | pose proof (Z.pow_le_mono_r 2 nb3 9) as P1; clear - NB3R P1 TLR; cbn in *; lia]).
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC2 NB3 NX3 NB3R NX30 NX3R NB4R NX40 NX4R SY4R J0 J4 PTR P3.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap]
      [0xac950] 80%nat
      ([KZRange st1n 0 511; KZRange st2n 0 511; KZRange (2^tl - st2n) 1 512; KZRange bc2 0 82; KZRange nb3 0 9; KZRange nx3 0 511; KZRange (2^nb3) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap;
        KZImg 0x22660 0x226e0] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: nl_rdx 28%nat MU WM st2n ST2 RNX. all: nl_rdy 30%nat MU WM st2n ST2 RSY. all: nl_rdb 31%nat MU WM st2n ST2 RNB.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR RI.
    all: kx_mem; rewrite RNX, RSY, RNB in *; clear RNX RSY RNB.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide.
    all: eapply (nl_d5 _ _ _ st1n st2n); first [close_fdms | reflexivity | eassumption | exact PTR | exact HJ | nl_side].
  Qed.
  (* [comment removed for export] *)
  Lemma nl_d4 : forall mm ptr j st1n st2 bc1 nb2 nx2 nb3 nx3 sy3 (cont x1 x12 x13 x26 x29 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1n < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc1 <= 73 -> nb2 = fc_nb tb st2 -> nx2 = fc_nx tb st2 ->
    nb3 = fc_nb tb st1n -> nx3 = fc_nx tb st1n -> sy3 = fc_sy tb st1n ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 nb3) (Z_to_bv 64 nx3) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 nb2) (Z_to_bv 64 (2 ^ nb2 - 1)) (Z_to_bv 64 bc1) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 (DT + 4)) x29 (Z_to_bv 64 nx2) (Z_to_bv 64 sy3))
          F (Z_to_bv 64 0xac8b8) fc None mm (seg_rom bsegs)).
  Proof.
    intros until j96. intros FD ST1 ST2 BC1 NB2 NX2 NB3 NX3 SY3 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R. rewrite <- NB2 in NB2R, NX2R. rewrite <- NX2 in NX20, NX2R.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R. rewrite <- NB3 in NB3R, NX3R. rewrite <- NX3 in NX30, NX3R. rewrite <- SY3 in SY3R.
    assert (P2N : 1 <= 2 ^ nb2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb2) as P1; clear - NB2R P1; lia | pose proof (Z.pow_le_mono_r 2 nb2 9) as P1; clear - NB2R P1 TLR; cbn in *; lia]).
    assert (P3 : 1 <= 2 ^ nb3 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb3) as P1; clear - NB3R P1; lia | pose proof (Z.pow_le_mono_r 2 nb3 9) as P1; clear - NB3R P1 TLR; cbn in *; lia]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb3 MI ltac:(clear - NB3R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC1 NB3 NX3 NB2R NX20 NX2R NB3R NX30 NX3R SY3R J0 J4 PTR BK P2N P3.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140896 128]
      [0xac90c] 80%nat
      ([KZRange st1n 0 511; KZRange st2 0 511; KZRange bc1 0 73; KZRange nb2 0 9; KZRange nx2 0 511; KZRange (2^nb2) 1 512;
        KZRange nb3 0 9; KZRange nx3 0 511; KZRange sy3 0 255; KZRange (2^nb3) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap;
        KZImg 0x22660 0x226e0; KZWord (140896 + 4 * nb3) 4 (2^nb3 - 1)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120); (140896, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI BK.
    all: kx_mem.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide.
    all: lazymatch goal with LB : 0 <= ?lb < 2 ^ ?k |- _ => nl_aset 12%nat (nx2 + lb); eapply (nl_d4r _ _ _ st1n (nx2 + lb)) end.
    all: first [close_fdms | reflexivity | eassumption | exact PTR | exact HJ | nl_side].
  Qed.
  Lemma nl_d3r : forall mm ptr j st1n st2 bc1 nb2 nx2 (cont x6 x7 x13 x26 x27 x29 x31 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1n < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc1 <= 73 -> nb2 = fc_nb tb st2 -> nx2 = fc_nx tb st2 ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 SPB) gp tp cont x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 + 4 * st1n)) x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 nb2) (Z_to_bv 64 (2 ^ nb2 - 1)) (Z_to_bv 64 bc1) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) x26 x27
               (Z_to_bv 64 (DT + 4)) x29 (Z_to_bv 64 nx2) x31)
          F (Z_to_bv 64 0xac870) fc None mm (seg_rom bsegs)).
  Proof.
    intros until j96. intros FD ST1 ST2 BC1 NB2 NX2 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R. rewrite <- NB2 in NB2R, NX2R. rewrite <- NX2 in NX20, NX2R.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R.
    assert (P2N : 1 <= 2 ^ nb2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb2) as P1; clear - NB2R P1; lia | pose proof (Z.pow_le_mono_r 2 nb2 9) as P1; clear - NB2R P1 TLR; cbn in *; lia]).
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC1 NB2 NX2 NB2R NX20 NX2R NB3R NX30 NX3R SY3R J0 J4 PTR P2N.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap]
      [0xac8b8] 80%nat
      ([KZRange st1n 0 511; KZRange st2 0 511; KZRange (2^tl - st1n) 1 512; KZRange bc1 0 73; KZRange nb2 0 9; KZRange nx2 0 511; KZRange (2^nb2) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap;
        KZImg 0x22660 0x226e0] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: nl_rdx 7%nat MU WM st1n ST1 RNX. all: nl_rdy 31%nat MU WM st1n ST1 RSY. all: nl_rdb 6%nat MU WM st1n ST1 RNB.
    all: clear UD UW RDST RSDST RWK RSWK RSTK RSFR RI.
    all: kx_mem; rewrite RNX, RSY, RNB in *; clear RNX RSY RNB.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide.
    all: eapply (nl_d4 _ _ _ st1n st2); first [close_fdms | reflexivity | eassumption | exact PTR | exact HJ | nl_side].
  Qed.
  (* [comment removed for export] *)
  Lemma nl_d3 : forall mm ptr j st1 st2 bc nb1 nx1 nb2 sy2 nx2 (cont x1 x12 x13 x22 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    nb2 = fc_nb tb st2 -> sy2 = fc_sy tb st2 -> nx2 = fc_nx tb st2 ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc) (Z_to_bv 64 sy2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 64) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 nb2) x22 (Z_to_bv 64 nb1) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 (2 ^ nb1 - 1)) (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 nx2) (Z_to_bv 64 nx1))
          F (Z_to_bv 64 0xac818) fc None mm (seg_rom bsegs)).
  Proof.
    intros until j96. intros FD ST1 ST2 BC NB1 NX1 NB2 SY2 NX2 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1 ST1) as (NB1R & NX10 & NX1R & SY1R & _ & _ & _). rewrite FAST0 in NB1R. rewrite <- NB1 in NB1R, NX1R. rewrite <- NX1 in NX10, NX1R.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R. rewrite <- NB2 in NB2R, NX2R. rewrite <- NX2 in NX20, NX2R. rewrite <- SY2 in SY2R.
    assert (PW1 : 1 <= 2 ^ nb1 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb1) as P1; clear - NB1R P1; lia | pose proof (Z.pow_le_mono_r 2 nb1 9) as P1; clear - NB1R P1 TLR; cbn in *; lia]).
    assert (PW2 : 1 <= 2 ^ nb2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb2) as P1; clear - NB2R P1; lia | pose proof (Z.pow_le_mono_r 2 nb2 9) as P1; clear - NB2R P1 TLR; cbn in *; lia]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb2 MI ltac:(clear - NB2R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC NB2 NX2 NB1R NX10 NX1R NB2R NX20 NX2R SY2R J0 J4 PTR BK PW1 PW2.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140896 128]
      [0xac870] 80%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange bc 0 64; KZRange nb1 0 9; KZRange nx1 0 511; KZRange (2^nb1) 1 512;
        KZRange nb2 0 9; KZRange sy2 0 255; KZRange nx2 0 511; KZRange (2^nb2) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 48) 16; KZWr (SPB + 64) 16; KZWr (SPB + 80) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 40 DST cap;
        KZImg 0x22660 0x226e0; KZWord (140896 + 4 * nb2) 4 (2^nb2 - 1)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 120); (140896, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI BK.
    all: kx_mem.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide.
    all: lazymatch goal with LB : 0 <= ?lb < 2 ^ ?k |- _ => nl_aset 12%nat (nx1 + lb); eapply (nl_d3r _ _ _ (nx1 + lb) st2) end.
    all: first [close_fdms | reflexivity | eassumption | exact PTR | exact HJ | nl_side].
  Qed.

End ND.
End CANSEC2.
