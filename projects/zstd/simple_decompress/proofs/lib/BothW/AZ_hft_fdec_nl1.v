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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_fse_bitinit AZ_fse_reloadi AZ_hft_dsym AZ_hft_fdec_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
   KZRange SPB 17594333495296 (2^47 - 288); KZAlign SPB 32; KZRange SPV 17594333495296 (2^47 - 16);
   KZWr DST cap; KZImg 0x224e0 0x22560]).
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
  (* [comment removed for export] *)
  Notation NHDST pc mm ptr bc st1 st2 j x1 x10 x11 x14 x23 x24 x25 x26 x28 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 (Z_to_bv 64 ptr) (Z_to_bv 64 bc) x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512)
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 st2) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 st1) x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 0x7fff8000) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation NTLST pc mm j x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512)
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) x20 (Z_to_bv 64 (DST + cap)) x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Hypothesis TAILK : (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j <= cap ->
        evtF bsegs RNG Q (NTLST 0xb0f28 mm j x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)).
  Hypothesis OVFK : (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (NTLST 0xb0f1c mm j x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)).
  (* [comment removed for export] *)
  Definition nl_headJ (j : Z) : Prop :=
    forall mm ptr bc st1 st2 (cont : word) pad (x1 x10 x11 x14 x23 x24 x25 x26 x28 x31 : word),
      FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
      0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
      evtF bsegs RNG Q (NHDST 0xb054c mm ptr bc st1 st2 j x1 x10 x11 x14 x23 x24 x25 x26 x28 x31).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac nl_w2 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?x14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x14 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdw2 HY AN MU WM W st STR.
  (* [comment removed for export] *)
  Ltac nl_nx20 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x20 _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x20 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdnx HY AN MU WM W st STR.
  Ltac nl_nx22 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x22 _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x22 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdnx HY AN MU WM W st STR.
  (* [comment removed for export] *)
  Ltac nl_nb sy nb SYR NBR TLR :=
    try replace (65536 * (sy + 256 * nb) / 16777216) with nb in * by (clear - SYR NBR TLR; Z.div_mod_to_equations; lia);
    try replace ((65536 * (sy + 256 * nb)) mod 2 ^ 64 / 16777216) with nb in * by (clear - SYR NBR TLR; rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  Ltac nl_addr := try match goal with |- context [Z_to_bv 64 (DT + 4 * ?st + 4)] => replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) by (clear; lia) end.
  (* [comment removed for export] *)
  Ltac nl_trap29 SYR NBR TLR :=
    exfalso;
    match goal with
    | H : context [536870912] |- _ => revert H; clear - SYR NBR TLR; intros H; rewrite ?unsigned_lit in H by lia;
                                     rewrite ?Z.mod_small in H by lia; Z.div_mod_to_equations; lia
    end.
  (* [comment removed for export] *)
  Lemma nl_d5 : forall mm ptr j st1nn st2n bc3 nb4 sy4 (cont x10 x11 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1nn st2n cont bc3 ptr pad mm ->
    0 <= st1nn < 2^tl -> 0 <= st2n < 2^tl -> 0 <= bc3 <= 91 -> nb4 = fc_nb tb st2n -> sy4 = fc_sy tb st2n ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (bc3)) (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 (Z_to_bv 64 (ptr)) (Z_to_bv 64 (DT + 4 + 4 * st2n)) (Z_to_bv 64 (65536 * (sy4 + 256 * nb4))) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 (nb4)) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (st1nn)) (Z_to_bv 64 (18446744073709411103)) (Z_to_bv 64 (1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (0x7fff8000)) cont)
          F (Z_to_bv 64 0xb0934) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC3 NB4 SY4 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2n ST2) as (NB4R & NX40 & NX4R & SY4R & _ & _ & _). rewrite FAST0 in NB4R. rewrite <- NB4 in NB4R, NX4R. rewrite <- SY4 in SY4R.
    assert (P4 : 1 <= 2 ^ nb4 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 nb4) as P1; clear - NB4R P1; lia | pose proof (Z.pow_le_mono_r 2 nb4 9) as P1; clear - NB4R P1 TLR; cbn in *; lia]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb4 MI ltac:(clear - NB4R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC3 NB4R NX40 NX4R SY4R J0 J4 PTR BK P4.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140512 128]
      [0xb054c; 0xb0f1c; 0xb1508] 80%nat
      ([KZRange st1nn 0 511; KZRange st2n 0 511; KZRange (2^tl - st2n) 1 512; KZRange bc3 0 91; KZRange nb4 0 9; KZRange sy4 0 255; KZRange (2^nb4) 1 512;
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560; KZWord (140512 + 4 * nb4) 4 (2^nb4 - 1)] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152); (140512, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    (* [comment removed for export] *)
    all: try (nl_nx20 MU WM st2n ST2 RNX).
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI BK.
    all: kx_mem; try (rewrite RNX in *; clear RNX).
    all: rewrite ?(unsigned_lit (fc_nx tb st2n)) in * by (clear - NX40 NX4R TLR P2 P4; lia).
    all: set (nx4 := fc_nx tb st2n) in *; clearbody nx4.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPB + 80) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "S2" cs end.
    all: replace (DST + j + 4) with (DST + (j + 4)) by (clear; lia).
    all: unhide.
    all: first [ eapply HJ; first [close_fdm | exact PTR | (fd_clear_or; lia)]
               | eapply (OVFK _ ptr); first [close_fdm | (fd_clear_or; lia)] ].
  Qed.
  (* [comment removed for export] *)
  Lemma nl_d4 : forall mm ptr j st1n st2n bc2 nb3 sy3 (cont x10 x11 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1n st2n cont bc2 ptr pad mm ->
    0 <= st1n < 2^tl -> 0 <= st2n < 2^tl -> 0 <= bc2 <= 82 -> nb3 = fc_nb tb st1n -> sy3 = fc_sy tb st1n ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (bc2)) (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 (Z_to_bv 64 (ptr)) (Z_to_bv 64 (DT + 4 + 4 * st1n)) (Z_to_bv 64 (65536 * (sy3 + 256 * nb3))) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 (st2n)) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (nb3)) (Z_to_bv 64 (18446744073709411103)) (Z_to_bv 64 (1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (0x7fff8000)) cont)
          F (Z_to_bv 64 0xb086c) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC2 NB3 SY3 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R.
    assert (PW3 : 1 <= 2 ^ fc_nb tb st1n <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1n)) as PP; clear - NB3R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st1n) 9) as PP; clear - NB3R PP TLR; cbn in *; lia]).
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2n ST2) as (NB4R & NX40 & NX4R & SY4R & _ & _ & _). rewrite FAST0 in NB4R.
    assert (PW4 : 1 <= 2 ^ fc_nb tb st2n <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2n)) as PP; clear - NB4R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st2n) 9) as PP; clear - NB4R PP TLR; cbn in *; lia]).
    rewrite <- NB3 in *.
    rewrite <- SY3 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb3 MI ltac:(clear - NB3R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC2 NB3R NX30 NX3R SY3R PW3 NB4R NX40 NX4R SY4R PW4 BK J0 J4 PTR.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140512 128]
      [0xb0934; 0xb1508] 100%nat
      ([KZRange st1n 0 511; KZRange st2n 0 511; KZRange (2^tl - st1n) 1 512; KZRange (2^tl - st2n) 1 512; KZRange bc2 0 82; KZRange nb3 0 9; KZRange sy3 0 255; KZRange (2 ^ nb3) 1 512; KZWord (140512 + 4 * nb3) 4 (2 ^ nb3 - 1);
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152); (140512, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: try (nl_nx22 MU WM st1n ST1 RNX). all: try (nl_w2 MU WM st2n ST2 RW2).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => rewrite RW2 in *; nl_trap29 SY4R NB4R TLR end).
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI; try clear BK.
    all: kx_mem; try (rewrite RNX in *; clear RNX); try (rewrite RW2 in *; clear RW2).
    all: rewrite ?(unsigned_lit (fc_nx tb st1n)), ?(unsigned_lit (fc_sy tb st2n + 256 * fc_nb tb st2n)) in * by (clear - NX30 NX3R SY4R NB4R TLR P2 PW3; lia).
    all: nl_nb (fc_sy tb st2n) (fc_nb tb st2n) SY4R NB4R TLR.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr.
    all: eapply nl_d5; first [close_fdm | reflexivity | exact PTR | exact HJ | (fd_clear_or; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma nl_d3 : forall mm ptr j st1n st2 bc1 nb2 sy2 (cont x11 x28 : word) pad,
    FDM mA SPV SPB lo DST cap SRC hs DT st1n st2 cont bc1 ptr pad mm ->
    0 <= st1n < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc1 <= 73 -> nb2 = fc_nb tb st2 -> sy2 = fc_sy tb st2 ->
    0 <= j -> j + 4 <= cap -> fl_ptr SRC n hs ptr -> nl_headJ (j + 4) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (bc1)) (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 (0x7fff8000)) x11 (Z_to_bv 64 (ptr)) (Z_to_bv 64 (DT + 4 + 4 * st2)) (Z_to_bv 64 (65536 * (sy2 + 256 * nb2))) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 140512) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 (nb2)) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (st1n)) (Z_to_bv 64 (18446744073709411103)) (Z_to_bv 64 (1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (1)) x28 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (0x7fff8000)) cont)
          F (Z_to_bv 64 0xb07b4) fc None mm (seg_rom bsegs)).
  Proof.
    intros until pad. intros FD ST1 ST2 BC1 NB2 SY2 J0 J4 PTR HJ.
    pose proof HY as HY'. open_hy HY'. open_fdm FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    destruct (fd_aro_maskM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mm MU WM) as (UM & RM & RSM). unfold FBITMASK in UM, RM, RSM.
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R.
    assert (PW2 : 1 <= 2 ^ fc_nb tb st2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2)) as PP; clear - NB2R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st2) 9) as PP; clear - NB2R PP TLR; cbn in *; lia]).
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st1n ST1) as (NB3R & NX30 & NX3R & SY3R & _ & _ & _). rewrite FAST0 in NB3R.
    assert (PW3 : 1 <= 2 ^ fc_nb tb st1n <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1n)) as PP; clear - NB3R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st1n) 9) as PP; clear - NB3R PP TLR; cbn in *; lia]).
    rewrite <- NB2 in *.
    rewrite <- SY2 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (fbitmask_know mx nb2 MI ltac:(clear - NB2R TLR; lia)) as BK end. unfold FBITMASK in BK.
    clear - HY AN FAST0 HJ TAILK OVFK S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW UM RM RSM RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC1 NB2R NX20 NX2R SY2R PW2 NB3R NX30 NX3R SY3R PW3 BK J0 J4 PTR.
    assert (CP : 0 < cap) by (clear - J0 J4; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *. hide PTR.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl); KAUnp DST cap; KAApp DST cap; KAUnp 140512 128]
      [0xb086c; 0xb1508] 100%nat
      ([KZRange st1n 0 511; KZRange st2 0 511; KZRange (2^tl - st1n) 1 512; KZRange (2^tl - st2) 1 512; KZRange bc1 0 73; KZRange nb2 0 9; KZRange sy2 0 255; KZRange (2 ^ nb2) 1 512; KZWord (140512 + 4 * nb2) 4 (2 ^ nb2 - 1);
        KZRange j 0 65536; KZRange (cap - j) 4 65536;
        KZWr (SPB + 80) 16; KZWr (SPB + 96) 16; KZWr (SPB + 112) 40;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 152; KZDisj (SPB + 80) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 24) 40 DST cap;
        KZImg 0x224e0 0x22560] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, cap); (SPB, 152); (140512, 128)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH J0 J4 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SPB0 SPB1 B_SPV SPR LOS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI. all: try (fd_rdS (fbitmask_at mm MI)).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => kx_trap_fast end).
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: try (nl_nx20 MU WM st2 ST2 RNX). all: try (nl_w2 MU WM st1n ST1 RW2).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb1508) _ _ _ _) => rewrite RW2 in *; nl_trap29 SY3R NB3R TLR end).
    all: clear UD UW UM RM RSM RDST RSDST RWK RSWK RSTK RSFR RI; try clear BK.
    all: kx_mem; try (rewrite RNX in *; clear RNX); try (rewrite RW2 in *; clear RW2).
    all: rewrite ?(unsigned_lit (fc_nx tb st2)), ?(unsigned_lit (fc_sy tb st1n + 256 * fc_nb tb st1n)) in * by (clear - NX20 NX2R SY3R NB3R TLR P2 PW2; lia).
    all: nl_nb (fc_sy tb st1n) (fc_nb tb st1n) SY3R NB3R TLR.
    all: try kx_abs_hyp BDC; try kx_abs_hyp S2; try kx_abs_hyp S1; kx_tidy_run.
    all: fd_lowbits.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr.
    all: eapply nl_d4; first [close_fdm | reflexivity | exact PTR | exact HJ | (fd_clear_or; lia)].
  Qed.

End ND.
End CANSEC2.
