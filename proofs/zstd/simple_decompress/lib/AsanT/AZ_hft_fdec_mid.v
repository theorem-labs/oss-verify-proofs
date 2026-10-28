(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_fdec_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
Ltac kx_autoFLAcF CH AKS STOPS FUEL KZS REGIONS WINDOWS :=
  let ks := eval cbv beta iota delta [app] in KZS in
  kx_autoFLA CH AKS STOPS FUEL ks REGIONS WINDOWS.

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

Section MD.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Variable Q : machine_state -> Prop.
  Hypothesis FASTH : fast = 1 -> fd_entK RNG Q gp tp F fc mA SPV SPB lo DST cap SRC n hs WK wksz DT FF 0xac0c4.
  Hypothesis NONFH : fast = 0 -> fd_entK RNG Q gp tp F fc mA SPV SPB lo DST cap SRC n hs WK wksz DT FF 0xac2bc.

  (* [comment removed for export] *)
  Lemma fd_mid : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j1 j2 jb,
    rw_cells bsegs mA (SPB + 48) [CB 16 j2] -> rw_cells bsegs mA (SPB + 64) [CB 16 j1] -> rw_cells bsegs mA (SPB + 80) [CB 40 jb] ->
    stk bsegs mA DST (DST + cap) -> stk bsegs mA lo SPB ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 cap) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
               (Z_to_bv 64 WK) (Z_to_bv 64 wksz) (Z_to_bv 64 hs) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xac084) fc None mA (seg_rom bsegs)).
  Proof.
    intros until jb. intros F2 F1 FB0 STD STL.
    pose proof HY as HY'. open_hy HY'. pose proof AN as AN'. open_an AN'. clear SRCLEN. fd_atP HY AN.
    pose proof (munch_refl (FD_WB DST cap SPB) mA) as MU. pose proof (wmono_refl bsegs mA) as WM.
    assert (FV : fast = 0 \/ fast = 1) by (destruct TBV as (_ & FR & _); clear - FR; lia).
    destruct ABD as (AB1 & AB2 & AB3).
    clear - HY AN FASTH NONFH F2 F1 FB0 STD STL MIj MU WM FV UWj DTHj FAj RWK RSWK RSTK RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA P2 B_SPV B_WK.
    unfold KHIGH in *.
    rewrite DTE in DTHj.   (* [comment removed for export] *)
    destruct FV as [FV | FV]; rewrite FV in DTHj; [specialize (NONFH FV) | specialize (FASTH FV)].
    all: let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
      kx_autoFLAcF (FAj, DTHj) [KAUnp (WK + 512) 4] [0xac0c4; 0xac2bc] 60%nat
        ([KZRange 0 0 0] ++ kzb) (@nil (Z * Z)) [(SPB + 8, 16); (WK + 512, 4)].
    all: try (kx_side_pre; kx_lia).
    all: clear UWj RWK RSWK RSTK RI.
    all: kx_mem; kx_tidy_run.
    all: replace (n + -1 * hs) with (n - hs) by (clear; lia); replace (cap + DST + -3) with (DST + cap - 3) by (clear; lia); replace (cap + DST) with (DST + cap) by (clear; lia).
    1: eapply NONFH; first [exact F2 | exact F1 | exact FB0 | exact STD | exact STL | exact MIj | exact MU | exact WM].
    eapply FASTH; first [exact F2 | exact F1 | exact FB0 | exact STD | exact STL | exact MIj | exact MU | exact WM].
  Qed.
End MD.
End CANSEC2.
