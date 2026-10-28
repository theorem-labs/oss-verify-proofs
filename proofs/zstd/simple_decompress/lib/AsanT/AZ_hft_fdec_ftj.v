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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_ft2 AZ_hft_fdec_ft3 AZ_hft_fdec_ft4 AZ_hft_fdec_ft5 AZ_hft_fdec_ft6.
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
  Notation TBST pc mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 ptr) x11 x12 x13 (Z_to_bv 64 st2) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 bc) (Z_to_bv 64 st1) x30 cont)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fd_hyps :=
    lazymatch goal with
    | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
    | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
    | |- _ = 1 => exact FAST1
    | |- fd_exitK _ _ _ _ _ _ _ _ _ _ _ _ => exact QX
    | |- fse_initds_stmtA => exact INITDS
    | |- _ => idtac
    end.

  Definition KBB (B : Z) : Prop := (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap -> B <= i ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)).

  Lemma ft_loopB : forall (k : nat) B, cap + 1 - 2 * Z.of_nat k <= B -> KBB B.
  Proof.
    induction k as [|k IH]; intros B HB; unfold KBB.
    - intros until i. intros x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 FD ST1 ST2 BC BP J0 I0 JC JB. exfalso. clear - HB J0 JC JB. lia.
    - eapply ft_d1. all: fd_hyps.
      eapply ft_r1. all: fd_hyps. 1: eapply ft_f1; fd_hyps.
      eapply ft_d2. all: fd_hyps.
      eapply ft_r2. all: fd_hyps. 1: eapply ft_f2; fd_hyps.
      apply (IH (B + 2)). clear - HB. lia.
  Qed.

  Lemma ft_loop : (forall mm ptr bc st1 st2 (cont : word) (j48 j64 j80 j88 j92 j96 : list byte) j i (x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 : word),
        FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j -> 0 <= i -> j + i + 2 <= cap ->
        evtF bsegs RNG Q (TBST 0xad4a8 mm ptr bc st1 st2 j i cont x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30)).
  Proof.
    intros until i. intros x1 x11 x12 x13 x20 x21 x22 x23 x25 x26 x30 FD ST1 ST2 BC BP J0 I0 JC.
    assert (HB : cap + 1 - 2 * Z.of_nat (Z.to_nat (cap + 1)) <= 0) by (rewrite Z2Nat.id by (clear - J0 I0 JC; lia); clear - J0 I0 JC; lia).
    pose proof (ft_loopB _ 0 HB) as L.
    unfold KBB in L. eapply (L _ _ _ st1 st2); try eassumption; clear - I0; lia.
  Qed.
End FD.
End CANSEC2.
