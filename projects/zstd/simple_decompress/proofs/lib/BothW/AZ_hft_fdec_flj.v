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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_fse_bitinit AZ_fse_reloadi AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_fl1 AZ_hft_fdec_fl2 AZ_hft_fdec_fl3.
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
  Notation HDST pc mm ptr bc st1 st2 j x1 x11 x14 x22 x23 x24 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551613) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j)) x11 (Z_to_bv 64 ptr) (Z_to_bv 64 bc) x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 st1) (Z_to_bv 64 (DST + cap)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 18446744073709551612) (Z_to_bv 64 18446744073709551611) (Z_to_bv 64 st2) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation DCST pc mm ptr bc st1 st2 j cont x1 x13 x14 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551613) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) (Z_to_bv 64 ptr) x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 st1) (Z_to_bv 64 (DST + cap)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 18446744073709551612) (Z_to_bv 64 18446744073709551611) (Z_to_bv 64 st2) cont)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation ECST pc mm ptr bc st1 st2 j cont x1 x11 x13 x14 x27 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551613) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j)) x11 (Z_to_bv 64 ptr) x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 st1) (Z_to_bv 64 (DST + cap))
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 bc) x27
             (Z_to_bv 64 18446744073709551612) (Z_to_bv 64 18446744073709551611) (Z_to_bv 64 st2) cont)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation TLST pc mm j x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 x13 x14 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + cap - 3)) x20 (Z_to_bv 64 (DST + cap)) x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Ltac fl_hyps KT KT0 :=
    lazymatch goal with
    | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
    | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
    | |- _ = 1 => exact FAST1
    | |- fd_exitK _ _ _ _ _ _ _ _ _ _ _ _ => exact QX
    | |- bit_init_stmtA_at _ => exact BITINIT
    | |- fse_initds_stmtA => exact INITDS
    | |- fse_reload_int_stmtA => exact RELOADI
    | |- fse_dsymf_stmtA => exact DSYMF
    | |- _ => first [exact KT | exact KT0 | idtac]
    end.

  Definition KHB (B : Z) : Prop := (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x11 x14 x22 x23 x24 x25 x26 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap -> B <= j ->
        evtF bsegs RNG Q (HDST 0xb0038 mm ptr bc st1 st2 j x1 x11 x14 x22 x23 x24 x25 x26 x31)).

  (* [comment removed for export] *)
  Lemma fl_loopB : forall (k : nat) B, (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xb0ab8 mm j x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31)) -> (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xb0aac mm j x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31)) -> cap + 1 - 4 * Z.of_nat k <= B -> KHB B.
  Proof.
    induction k as [|k IH]; intros B KT KT0 HB; unfold KHB.
    - intros until j. intros x1 x11 x14 x22 x23 x24 x25 x26 x31 FD ST1 ST2 BC PTR JC JB. exfalso. clear - HB JC JB. lia.
    - eapply fl_head. all: fl_hyps KT KT0.
      eapply fl_d12. all: fl_hyps KT KT0.
      eapply fl_d34. all: fl_hyps KT KT0.
      apply (IH (B + 4) KT KT0). clear - HB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_loop : (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xb0ab8 mm j x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31)) -> (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
        evtF bsegs RNG Q (TLST 0xb0aac mm j x1 x5 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31)) -> (forall mm ptr bc st1 st2 (cont : word) pad j (x1 x11 x14 x22 x23 x24 x25 x26 x31 : word),
        FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mm ->
        0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> fl_ptr SRC n hs ptr -> 0 <= j <= cap ->
        evtF bsegs RNG Q (HDST 0xb0038 mm ptr bc st1 st2 j x1 x11 x14 x22 x23 x24 x25 x26 x31)).
  Proof.
    intros KT KT0. intros until j. intros x1 x11 x14 x22 x23 x24 x25 x26 x31 FD ST1 ST2 BC PTR JC.
    assert (HB : cap + 1 - 4 * Z.of_nat (Z.to_nat (cap + 1)) <= 0) by (rewrite Z2Nat.id by (clear - JC; lia); clear - JC; lia).
    pose proof (fl_loopB _ 0 KT KT0 HB) as L.
    unfold KHB in L. eapply L; try eassumption; clear - JC; lia.
  Qed.
End FD.
End CANSEC2.
