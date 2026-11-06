(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module names changed; 426 of its 465 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R8.v, with its addresses and numbers changed; 234 of its 320 lines of code are new or changed and 379 lines of the source are left out. *)
(* lib/A/ACtlG/R5.v -- GLUE for stage seg_R5 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:487,
   `Hypothesis seg_R5 : forall POST, CF POST (ix_cut C_A815cc_at [Z.of_nat 0]) -> CF POST C_A81588`).  Written by
   a Theorem Labs lane's glue lane (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A2.v.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R5 : forall POST, CF POST (ix_cut C_A815cc_at [Z.of_nat 0]) -> CF POST C_A81588
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R5.  Segment R5 is 0x81588 -> 0x815cc (Seg/R5.v:1-18), turn b = 0 of the round trip: s7 = 0, six 8-byte stores
   into the spill block [A, A + 120) of the prologue save area ([A + 8] = mrow + 16, [A + 112] = mrow, [A] = mrow +
   20, [A + 104] = 0x21140, [A + 96] = 0x1234, [A + 64] = 0xe38f0000), s8 = 36, a0 = [A + 128] = fr + 544.

   RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28 20:16:23Z
   from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM: the released ASan
   donor is cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e; its walk lifts no outside-proved run, so this
   glue has no donor counterpart.  Its pieces are the donor's SRr (YA0n) and ajournal (YCbq), a Theorem Labs lane's kit and
   bridge (YA0nR.SRr_xregs_eqv; ProgBridge; ProgWorldVisWin through KitMem), a Theorem Labs lane's ProgWorld
   (ajournal_of_fsteps, pws_fsteps_mem), the segment's footprint run, and the shared kits lib/A/ACtlG/Kit.v and
   lib/A/ACtlG/KitMem.v.

   THE RUN.  Seg/R5.v states no run lemma (seg_R5 steps its run inline, Seg/R5.v:508-583), so the footprint run is
   A.Prog.Seg.R5Fs.r5_evt_F (lib/A/Prog/Seg/R5Fs.v, this lane's file in a Theorem Labs lane's _F convention), Required, not
   assumed: R5.v's inline run re-stepped under StepF with RNG first and two rng premises, [A, A + 120) and
   [A + 128, A + 136) (R5Fs.rng.tsv (a working note, not in this delivery)).  Its pin is R5Fs.seg_R5_of_F, which re-derives R5.v's own seg_R5 from it at
   ExecF.RNG_all (constr_eq-checked to state R5.seg_R5 term for term).  It is register-and-spill-only: no callee, no
   runtime premise.  It is stated over ctrl's lib/A/Reusable/YK11 class FPState; its fx is instantiated with
   `AK11.mkFP CK11.fp_regs CK11.fp_csr` and its post rewritten with `change` to the core's fp_regs / fp_csr / seg_rom,
   as A2.v does.

   THE PROOF, step by step (glue-pattern.md section 3, a run that writes memory)
   G1  unfold the entry cut C_A81588 (ACtlCutP.v:1252-1271): 30 conjuncts; FRAC's pins (s1 = A, sp, the stack
       bounds; destructed by position up to c_sp <= APPMEM_END, the rest left in `_`); ctl_rt_C unread.
   G2  r5_evt_F's premises: s1 = A (FRAC), s2 = mrow (c_in cx) (the body's rgv 18), 0 <= A < 2^60 (FRAC's
       A + 416 <= c_sp <= APPMEM_END), the spill block writable (ULMem.wr_at from the journal's present LLVMF stack window,
       KitMem.kitmem_stk_of_journal: c_sp - LLVMF_STK < sp <= A and A + 416 <= c_sp), [A + 128] = fr + 544 (the
       body's spill 128); footprint RNG_W (w_H W3), both ranges by KitMem.kitmem_rng_win (the same window).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  KitMem.kitmem_lift at RNG_W (w_H W3), fp_avoids by ProgBridge.fp_avoids_RNG_W; its continuation gives the
       run's fsteps (ProgWorld.pws_fsteps_mem: mem_grows) and same_but_materialized.
   G5  the exit cut C_A815cc_at at b = 0 (ACtlCutP.v:1276-1297) at the run's end map R, memory m' (the six stores over
       mem3; munch WR mem3 m' with WR = [(A, A + 16); (A + 32, A + 120)], the spill block without FRAC's two spill
       cells) and model md', the same cx, fr, k, ly3, S3, W3, index [Z.of_nat 0]:
         journal  ProgWorld.ajournal_of_fsteps over WR, every written byte in the LLVMF stack window
                  (KitMem.kitmem_awr_win);
         frames, frame law   unchanged (own6 on both cuts); k bound: kmax 0 at the entry, 2 * 0 at the exit;
         body     live list unchanged; FRAC by shape across the stores (KitMem.kitmem_frac_keep: its three spills
                  [A + 16, A + 32) / [A + 304, A + 312), the frame header / trailer words and the saved registers
                  are off the stores) and across the register map (Kit.kit_frac_move, registers 2 3 4 8 9 19 26
                  kept); every spill through the store chain (the six written cells by the store at their address,
                  the others missed by each store), as ctrl's seg_R5 does (Seg/R5.v:686-746); the frame bytes /
                  cells (all below fr + FRAME_BYTES <= A) by KitMem.kitmem_bytes_munch / Lib.Frame.rw_cells_transport;
                  addressable facts by KitMem.kitmem_addr_munch (the stores are application memory); the input
                  bytes by KitMem.kitmem_bytes_munch (the input block lies below alloc_ceiling <= c_sp - LLVMF_STK, or
                  is empty: ctl_base's two cases, AR's block law YG0d.al_blocks); s7 = 0, s8 = 36, a0 = fr + 544 and
                  the kept registers from the run's post;
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR (same ly3 S3, memory m'), with the
                  entry's arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal, RELRO_IMG) and made
                  arodata_okP by ProgWorld.arodata_okP_of_S.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The run has no runtime premise, so
   the entry's ctl_rt_C is not read; the exit's comes from AR.

   SECTION HYPOTHESES (each is ACtl.v's Section hypothesis of the same name and text; the top supplies it)
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a -- for the exit's arodata_okS.
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record, which kitmem_own6, al_blocks,
     ajournal_of_fsteps and ctl_rt_C_of_AR take.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the core's symbol record, which ctl_rt_C_of_AR takes.
   The run is Required from Seg/R5Fs.v and has no premise the cut does not give.

   READS NO STAND-IN VALUE: no ts_gp / TFIB_GP, pc_wrap_*, pc_stack_malloc, ts_zsh / AF0m row or port_core_refused
   literal; gp passes through FRAC symbolically.
   NOT USED: rt_of_core (the run has no runtime premise); kit_frame6_above_img (the stores lie in the stack window,
   above every frame and block).

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier.  The twin modules (YK11 YK1b YM05
   YO09) and lib/Lib are named absolutely and written through the aliases below; ctrl's YK11 (the run's) through
   AK11.  Frame-route files of record in the closure come through Seg/R5Fs.v -> Seg/R5.v (SlotInv, SlotModel,
   AsanRTInv, Contract, FrameAPI, MemNorm, Tac_slot, RcPro); their blobs are named in the commit.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (through CK11 / AK11) or Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R5.v   -- hits only inside comments.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_R5: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
(* route (C): the cut's runtime conjunct, its producer from AR, the symbol record it takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R5Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module KM := A.ACtlG.KitMem.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v bind it; ctrl's runs' list (= segs by reflexivity,
   ProgBridge.tfibsegs_rsegs). *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local facts (proof-internal, no world vocabulary; none is a Kit / KitMem helper). *)

(* A spill whose base register 9 holds A reads its word at A + off. *)
Lemma r5g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  A.ACtlCutP.spill regs m off v -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  A.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A1 & HA1 & Hq) HA H0 Hoff Hhi.
  assert (EA : A1 = A).
  { unfold A.ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* An 8-byte cell after an 8-byte store: the store at its address gives it, a store elsewhere keeps it (the two
   cases of Seg/R5.v's r5_q64_same / r5_q64_other, over the cut layer's q64). *)
Lemma r5g_q64_other : forall (m : word -> option byte) a (w : word) c v,
  A.ACtlCutP.q64 m c v -> 0 <= a -> a + 8 <= 2 ^ 64 -> (c + 8 <= a \/ a + 8 <= c) ->
  A.ACtlCutP.q64 (write_to_mem m (LMem.wa a) (LMem.le8 w)) c v.
Proof.
  intros m a w c v H Ha Hb Hd.
  pose proof (LMem.length_le8 w) as L1. pose proof (LMem.length_le8 (Z_to_bv 64 v)) as L2.
  unfold A.ACtlCutP.q64 in *. apply LMem.bytes_at_write_other; [exact H | lia | lia | lia].
Qed.

Lemma r5g_q64_same : forall (m : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  A.ACtlCutP.q64 (write_to_mem m (LMem.wa a) (LMem.le8 (Z_to_bv 64 v))) a v.
Proof.
  intros m a v Ha Hb. pose proof (LMem.length_le8 (Z_to_bv 64 v)) as L1. unfold A.ACtlCutP.q64.
  exact (LMem.bytes_at_write_same segs m a (LMem.le8 (Z_to_bv 64 v)) Ha ltac:(lia)).
Qed.

(* An 8-byte cell across a chain of 8-byte stores, store by store (outermost first), the lemma picked from the
   syntactic store address (Seg/R5.v's r5_q, over the cut layer's q64). *)
Ltac r5g_q :=
  repeat lazymatch goal with
  | |- A.ACtlCutP.q64 (write_to_mem ?m (LMem.wa ?a) (LMem.le8 ?w)) ?c ?v =>
      tryif constr_eq a c then exact (r5g_q64_same m a v ltac:(lia) ltac:(lia))
      else refine (r5g_q64_other m a w c v _ ltac:(lia) ltac:(lia) ltac:(lia))
  end.

Section GlueR5.

(* ACtl.v's Section shape (ACtl.v:170-176), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:215, :219-220, :234-235), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation C_A81588 := (ACtlCutP.C_A81588 B).
Local Notation C_A815cc_at := (ACtlCutP.C_A815cc_at B).

(* ACtl.v's Section hypotheses this stage reads, same names and texts: the read-only span is image bytes
   (RELRO_IMG, for the exit's arodata_okS), the core's AR laws (LAWS) and symbol record (TFIB_SYMS, for
   ctl_rt_C_of_AR). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R5 : forall POST, CF POST (ix_cut C_A815cc_at [Z.of_nat 0]) -> CF POST C_A81588.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81588 (ACtlCutP.v:1252-1271), 30 conjuncts. *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81588] in Hbody.
  destruct Hbody as (HP & HFRAC & Hcn & HCUR & HOUR & HOUTA & HIDB & HFGB & S128 & HPRO & R21 & S152 & S144 &
    S192 & RW38 & RW72 & S280 & S240 & RW1 & RW32 & S48 & S56 & S88 & S80 & S72 & S200 & S216 & HAD2256 &
    HAD2176 & R18).
  pose proof HFRAC as (A & sp & R2 & Hs16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  (* G2: the numbers *)
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hceil0 Hceil1] _].
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* the journal: AR and the owned frame's bounds (4096 <= fr, fr + 4096 <= alloc_ceiling <= c_sp - LLVMF_STK) *)
  pose proof HJ as (HAR & _).
  destruct (KM.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr6 & Hfr4096 & _ & Hfrceil & Hceilsp).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfrceil. rewrite HSTKv in Hceilsp.
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= A) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HAr : 0 <= A < 2 ^ 60) by lia.
  (* the input block lies below A, or is empty (ctl_base's two cases; AR's block law) *)
  assert (HINP : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> x < A).
  { pose proof Hbase as (Hpre & _). destruct Hpre as (_ & _ & _ & _ & Hcase & Hlen & _).
    intros x Hx. rewrite <- Hlen in Hx.
    destruct Hcase as [(E0 & _) | (Hn & Hin)]; [lia|].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hin).
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & _ & Hceil & _).
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as [_ Hrs].
    lia. }
  (* G2: the run's premises *)
  pose proof (r5g_spill_q64 regs3 mem3 128 (fr + 544) A S128 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq128.
  assert (Hstk : LFrame.stk rsegs mem3 A (A + 120)).
  { eapply KM.kitmem_stk_of_journal; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (Hwr : ULMem.wr_at rsegs mem3 A 120).
  { destruct Hstk as (Hw0 & Hw1 & Hwv). split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hwv (A + i) ltac:(lia))). }
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RA : LEF.rng RNG A 120).
  { eapply KM.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (R128 : LEF.rng RNG (A + 128) 8).
  { eapply KM.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81588) with 0x81588.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81588) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4: the run (ctrl's YK11 instance built from the core's fp state) and the lift *)
  pose proof (@A.Prog.Seg.R5Fs.r5_evt_F (AK11.mkFP CK11.fp_regs CK11.fp_csr) RNG regs3 mem3 A fr
    (ACtlCut.c_in cx) R9 R18 HAr Hwr Hq128 RA R128) as HRUN.
  change (@AK11.fp_regs (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_regs fx) in HRUN.
  change (@AK11.fp_csr (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_csr fx) in HRUN.
  change (@AK11.seg_rom) with (@CK11.seg_rom) in HRUN.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HRUN.
  apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HRUN (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' Hrun HQ0 Hsbm.
  pose proof (proj1 (A.ProgWorld.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) _ _ _ Hrun
                       (A.ProgBridge.fp_avoids_RNG_W _))) as Hgrow.
  destruct HQ0 as (R & pc' & m' & Ems & Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E22 & E25 & E21 & E23 & E24 &
    E10 & Hmem).
  subst ms' pc'. cbn [ms_mem LMState.MS] in Hgrow.
  destruct Hmem as (w16 & w112 & w8 & w104 & w96 & w64 & Em' & Ew104 & Ew96 & Ew64 & Ew112 & Ew16 & Ew8).
  subst w104 w96 w64 w112 w16 w8.
  assert (E18 : Sem.reg_get regs3 18 = Z_to_bv 64 (SM.mrow (ACtlCut.c_in cx))) by exact R18.
  rewrite E18 in Em'.
  change ULMem.wa with LMem.wa in Em'. change ULMem.le8 with LMem.le8 in Em'.
  (* G5: the end state is the exit cut's state at the run's map R and memory m'. *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A815cc_at [Z.of_nat 0])) R m' md') (POST cx)).
  (* the kept registers, over the core's getr *)
  assert (G2 : CK11.getr R 2 = CK11.getr regs3 2) by exact E2.
  assert (G3 : CK11.getr R 3 = CK11.getr regs3 3) by exact E3.
  assert (G4 : CK11.getr R 4 = CK11.getr regs3 4) by exact E4.
  assert (G8 : CK11.getr R 8 = CK11.getr regs3 8) by exact E8.
  assert (G9 : CK11.getr R 9 = CK11.getr regs3 9) by exact E9.
  assert (G19 : CK11.getr R 19 = CK11.getr regs3 19) by exact E19.
  assert (G26 : CK11.getr R 26 = CK11.getr regs3 26) by exact E26.
  assert (G22 : CK11.getr R 22 = CK11.getr regs3 22) by exact E22.
  assert (G25 : CK11.getr R 25 = CK11.getr regs3 25) by exact E25.
  assert (G21 : CK11.getr R 21 = CK11.getr regs3 21) by exact E21.
  assert (R9' : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv; rewrite G9; exact R9).
  (* the write set: the spill block [A, A + 120) without FRAC's two spill cells [A + 16, A + 32) *)
  set (WR := [(A, A + 16); (A + 32, A + 120)]).
  assert (MU : LFrame.munch WR mem3 m').
  { rewrite Em'.
    apply LFrame.munch_write; [ apply LFrame.munch_write; [ apply LFrame.munch_write; [ apply LFrame.munch_write;
      [ apply LFrame.munch_write; [ apply LFrame.munch_write; [ apply LFrame.munch_refl | | | ] | | | ] | | | ] | | | ]
      | | | ] | | | ];
      try (rewrite LMem.length_le8); try (cbn [LFrame.inside WR]); lia. }
  assert (WM : LFrame.wmono rsegs mem3 m').
  { rewrite Em'. repeat apply LFrame.wmono_write. apply LFrame.wmono_refl. }
  assert (HWin : forall x, ~ LFrame.outside WR x -> A <= x < A + 120).
  { intros x Hx. destruct (KM.kitmem_not_outside _ _ Hx) as (lo & hi & Hin & Hr).
    destruct Hin as [Ei | [Ei | []]]; injection Ei as <- <-; lia. }
  assert (Hout : forall x, (x < A \/ A + 120 <= x \/ A + 16 <= x < A + 32) -> LFrame.outside WR x).
  { intros x Hx. cbn [LFrame.outside WR]. split; [lia|]. split; [lia | exact I]. }
  assert (Happ : forall x, A <= x < A + 120 -> A.AsanRT.app_mem x).
  { intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia. }
  assert (Hsh_out : forall x, A.AsanRT.in_shadow x -> LFrame.outside WR x).
  { intros x Hx. apply Hout.
    destruct (Z_lt_le_dec x A) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec x (A + 120)) as [H2|H2]; [|right; left; exact H2].
    exfalso. exact (A.AsanRTFacts.app_not_shadow x (Happ x (conj H1 H2)) Hx). }
  (* the journal across the run (ProgWorld.ajournal_of_fsteps): every written byte is in the LLVMF stack window *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFrame.outside WR a ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3)
              ly3 (ACtlCut.own6 cx) a).
  { intros a _ Hno. pose proof (HWin a Hno) as Ha.
    apply KM.kitmem_awr_win. rewrite HSTKv. lia. }
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { match type of Hrun with Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
               (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
               (ACtlCut.own6 cx) ly3 S3 W3 s0 s1 md3 md' k _ WR HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm
               Hawr)
    end. }
  (* the keep facts: a spill of the entry above the spill block, bytes, cells and addressability off the stores *)
  assert (KSP : forall off v, 120 <= off -> off + 8 <= 416 -> ACtlCutP.spill regs3 mem3 off v ->
            ACtlCutP.spill R m' off v).
  { intros off v Ho1 Ho2 Hs.
    exact (KM.kitmem_spill_munch WR regs3 R mem3 m' off v A Hs R9 ltac:(lia) ltac:(lia) ltac:(lia) MU G9
             (fun x Hx => Hout x ltac:(lia))). }
  assert (KBY : forall a bs, a + Z.of_nat (length bs) <= A ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 Hb. exact (KM.kitmem_bytes_munch WR mem3 m' a bs Hb MU (fun x Hx => Hout x ltac:(lia))). }
  assert (KAD : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Hadr; exact (KM.kitmem_addr_munch WR mem3 m' p n Hadr MU Hsh_out)).
  assert (KRW : forall a n bs, 0 <= a -> a + Z.of_nat n <= A ->
            LStep.rw_cells segs mem3 a [LCells.CB n bs] -> LStep.rw_cells segs m' a [LCells.CB n bs]).
  { intros a n bs H1 H2 Hc. apply (LFrame.rw_cells_transport rsegs WR mem3 m' a _ Hc MU WM).
    cbn [LCells.cells_size LCells.csize LFrame.disjoint_from WR]. rewrite Nat.add_0_r.
    split; [lia|]. split; [lia | exact I]. }
  apply (HX cx [Z.of_nat 0] fr k ly3 S3 W3 R m' md' Hbase).
  - (* journal *)
    exact HJ'.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 0 at the entry, 2 * b = 0 at the exit *)
    cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.C_A81588 ACtlCutP.ixn
      nth] in Hk |- *.
    cbn [Z.of_nat Z.to_nat Z.mul]. lia.
  - (* the exit body, C_A815cc_at at b = 0 (ACtlCutP.v:1276-1297), 25 conjuncts *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn nth].
    change (Z.to_nat (Z.of_nat 0)) with 0%nat.
    split; [reflexivity|].
    split; [exact HP|].
    split.
    { (* FRAC: by shape across the stores (its spills, header, trailer and saved registers are off them), then
         across the register map *)
      apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact G2 | exact G3 | exact G4 | exact G8 |
        exact G9 | exact G19 | exact G26].
      apply (KM.kitmem_frac_keep B cx fr fr regs3 mem3 m' WR HFRAC MU Hgrow ltac:(lia)).
      - intros A0 HA0 x Hx. apply Hout.
        (* register 9 holds A, so A0 = A modulo 2^64 *)
        unfold ACtlCut.rgv in HA0, R9. rewrite R9 in HA0.
        apply (f_equal bv_unsigned) in HA0. rewrite !Z_to_bv_unsigned in HA0. unfold bv_wrap in HA0.
        change (bv_modulus 64) with (2 ^ 64) in HA0. Z.div_mod_to_equations. lia.
      - intros x Hx. apply Hout. left. lia.
      - intros x Hx. apply Hout. right. left. lia. }
    split; [exact Hcn|].
    split.
    { (* RS at b = 0 *)
      unfold ACtlCutP.RS, ACtlCutP.RB.
      split; [lia|].
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
        split; [unfold ACtlCut.rgv in *; rewrite G22; exact Hc22 | unfold ACtlCut.rgv in *; rewrite G25; exact Hc25]. }
      split; [unfold ACtlCutP.OURb in *; apply KBY; [rewrite SM.OUR_length; lia | exact HOUR]|].
      split; [exact E23|].
      split.
      { unfold ACtlCutP.IDBr in *. apply KBY; [| exact HIDB].
        change (SM.RID (ACtlCut.c_in cx) 0) with (repeat (Z_to_bv 8 0) 38); rewrite repeat_length; lia. }
      { unfold ACtlCutP.FGBr in *. apply KBY; [| exact HFGB].
        change (SM.RFG (ACtlCut.c_in cx) 0) with (repeat (Z_to_bv 8 0) 72); rewrite repeat_length; lia. } }
    split; [unfold ACtlCutP.OUTA in *; exact (KAD _ _ HOUTA)|].
    split; [exact (KSP 128 _ ltac:(lia) ltac:(lia) S128)|].
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA6 & PIN & PINB &
        P184 & P256 & P264 & P272 & P32).
      split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 40 _ A P40 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
      split; [exact (KSP 120 _ ltac:(lia) ltac:(lia) P120)|].
      split; [exact (KSP 136 _ ltac:(lia) ltac:(lia) P136)|].
      split; [exact (KSP 160 _ ltac:(lia) ltac:(lia) P160)|].
      split; [exact (KSP 168 _ ltac:(lia) ltac:(lia) P168)|].
      split; [exact (KSP 176 _ ltac:(lia) ltac:(lia) P176)|].
      split; [exact (KSP 208 _ ltac:(lia) ltac:(lia) P208)|].
      split; [exact (KSP 248 _ ltac:(lia) ltac:(lia) P248)|].
      split; [exact (KAD _ _ PA6)|].
      split; [exact (KM.kitmem_bytes_munch WR mem3 m' _ _ PIN MU (fun x Hx => Hout x (or_introl (HINP x Hx))))|].
      split; [intros Hn0; exact (KAD _ _ (PINB Hn0))|].
      split; [exact (KSP 184 _ ltac:(lia) ltac:(lia) P184)|].
      split; [exact (KSP 256 _ ltac:(lia) ltac:(lia) P256)|].
      split; [exact (KSP 264 _ ltac:(lia) ltac:(lia) P264)|].
      split; [exact (KSP 272 _ ltac:(lia) ltac:(lia) P272)|].
      exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 32 _ A P32 R9 ltac:(lia) ltac:(lia) ltac:(lia))]. }
    (* the four written round-trip spills, s8 = 36, a0 = fr + 544 *)
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q]|].
    split; [exact E10|].
    split; [exact E24|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q]|].
    split; [unfold ACtlCut.rgv; rewrite G21; exact R21|].
    split; [exact (KSP 152 _ ltac:(lia) ltac:(lia) S152)|].
    split; [exact (KSP 144 _ ltac:(lia) ltac:(lia) S144)|].
    split; [exact (KAD _ _ HAD2176)|].
    split; [exact (KSP 192 _ ltac:(lia) ltac:(lia) S192)|].
    split; [destruct RW38 as (idb & Hc); exists idb; apply KRW; [lia | lia | exact Hc]|].
    split; [destruct RW72 as (jk & Hc); exists jk; apply KRW; [lia | lia | exact Hc]|].
    split; [exact (KSP 280 _ ltac:(lia) ltac:(lia) S280)|].
    split; [exact (KSP 240 _ ltac:(lia) ltac:(lia) S240)|].
    split; [destruct RW1 as (jy & Hc); exists jy; apply KRW; [lia | lia | exact Hc]|].
    split; [destruct RW32 as (jk & Hc); exists jk; apply KRW; [lia | lia | exact Hc]|].
    (* RXS: the five carried spills, this segment's [A + 8] = mrow + 16 and [A + 0] = mrow + 20, the two carried
       spills, the 72 fragment bytes addressable *)
    unfold ACtlCutP.RXS.
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 48 _ A S48 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 56 _ A S56 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 88 _ A S88 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 80 _ A S80 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q; exact (r5g_spill_q64 regs3 mem3 72 _ A S72 R9 ltac:(lia) ltac:(lia) ltac:(lia))]|].
    split; [exists A; split; [exact R9' | rewrite Em'; r5g_q]|].
    split; [exists A; split; [exact R9' | rewrite Z.add_0_r, Em'; r5g_q]|].
    split; [exact (KSP 200 _ ltac:(lia) ltac:(lia) S200)|].
    split; [exact (KSP 216 _ ltac:(lia) ltac:(lia) S216)|].
    exact (KAD _ _ HAD2256).
  - (* ctl_rt_C at the exit (same ly3 S3, memory m'): ctl_rt_C_of_AR at the exit journal's AR, with the entry's
       arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal) *)
    pose proof Hbase as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
    pose proof HJ' as (HAR' & _).
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m' md' HAR'
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _
                (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' HROS)
                (Z.le_refl _) (Z.le_refl _))).
Qed.

End GlueR5.
