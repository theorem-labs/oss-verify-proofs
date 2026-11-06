(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths and module names changed; 364 of its 379 lines of code are new or changed and 544 lines of the source are left out. *)
(* lib/A/ACtlG/F5_e10.v -- GLUE for stage seg_F5_e10 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:757), plus three SHARED lemmas of the F5 glue lanes (f5g_move, f5g_keep, f5g_pf_keep; the
   contract in a Theorem Labs lane's brief <lane notes> f5-glue-context.md (a working note, not in this delivery), owner a Theorem Labs lane).  Written by
   a Theorem Labs lane; single writer.  rule 24: no function proved (kind: segment lemma; a glue
   stage of image A's entry walk, not a whole function).  Template: lib/A/ACtlG/A5.v (steps G1-G5) and
   glue-pattern.md sections 2-4 and 6 (a working note, not in this delivery).

   WHAT IT PROVES
     f5g_move    FLSI / LK / b5_C (ACtlCutP.v:677, :556, :820) move along a register map that keeps registers
                 2 9 18 21 23 (the only ones they read: rgv 9 for every spill, 18 / 23 in b5_C, 21 in LK, 2 through
                 b5_PH's spZ).
     f5g_keep    HB / FLSI / LK / b5_C / IDj across a write W that misses [0, A + 240) and [A + 248, A + 280),
                 together with such a register move.  The cut-layer port of Seg/F5.v's f5_keep (:295-537).
     f5g_pf_keep b5_PF (ACtlCutP.v:854) across a write that misses [0, A + 240), with register 9 kept.  The
                 cut-layer port of Seg/F5.v's f5_pf_keep (:543-633).
     glue_seg_F5_e10 : forall POST (j : nat),
         CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea8_at [Z.of_nat j])
       with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): ACtl.v's Section hypothesis
       seg_F5_e10, character for character.  Segment 0x81ea8 -> 0x81ec0 is six register-only instructions
       (li a1,0; addi a0,s6,-1; addi a2,s7,18; and s6,a0,s9; li a3,32; mv a0,a2), the run
       A.Prog.Seg.F5F.seg_F5_e10_run_F (F5F.v:172-195), memory unchanged.

   THE PORT OF f5_keep / f5_pf_keep (no FRA in the cut layer)
     Same per-conjunct steps as Seg/F5.v: Seg.F5.f5_spill_keep for every spill, f5_q64_keep for the b5_SPILL
     words, RcAsanFPLib.fl_bytes for every byte list, fl_stk for the frame window, Tac_slot.sl_addr_keep for every
     addressable range, f5_bytes_first / f5_mcmp_firstn for b5_PF's prefixes, f5_tID_len / f5_fsb_len /
     fr50_length / OUR_length for the lengths, f5_sh_below for the four metadata bytes.  Every bound Seg/F5.v takes
     from FRA (the spill base A identified with f5_id, the record block below stklo from a_laws_blocks, the frame
     below A) is a premise of the lemma instead: HIGHMEM_BEG <= A, A + 416 <= APPMEM_END, fr + FRAME_BYTES <= A,
     phi + a_size (flen cx j) <= A, c_p cx + length (c_in cx) <= A.  The kind-name table is bounded by computation
     (KIND_NAME = 0x9e760, 112 bytes).  Two Seg/F5.v helpers name ctrl's ghost record and are inlined here:
     f5_idj_keep (fl_bytes + f5_tID_len) and f5_tphi_len (its two-line proof over c_in cx).  Seg/F5.v's thread-word
     steps (f5_word_eq) have no counterpart: ACtlCutP's b5_C has no FakeStack conjunct and its b5_PH has no tp-word
     conjunct (ACtlCutP.v:771-780).  Each keep is proved at the old map first and then moved with f5g_move.

   THE PROOF OF THE STAGE, step by step (A5.v's G1-G5)
   G1  unfold the entry cut: ix_cut's index equation, then C_A81ea8_at (ACtlCutP.v:2064-2074) with ixn and nth,
       Nat2Z.id for the index; b5_body's phi, its seven conjuncts and the ten of the cut's P.
   G2  the run's premises: rgv 22 0, rgv 25 (phi + 18) from P, rgv 23 phi from b5_C; 0 <= phi + 18 < 2 ^ 64 from
       HB's addressable bounds (phi + a_size <= APPMEM_END).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv moves the walk to the run's start map mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, YA0nR.SRr_fevt at Kit.kit_RNG0 (fp_avoids vacuous).
       The run's FPState is ctrl's class: instantiated with A.Reusable.YK11.mkFP of the core's fp_regs / fp_csr.
   G5  the run's end map R is the exit cut's map; ctl_from of C_A81ec0_at at the same cx, fr, k, ly3, S3, W3, mem3:
         journal  ajournal_exec with the empty write set (A5.v:206-208);
         frames, frame law, k bound   exact (own6 and the same kmax on both cuts);
         body     FRAC by Kit.kit_frac_move; Permutation / c_n / j / HB / u32 / IDj unchanged (same memory);
                  FLSI / LK / b5_C by f5g_move; rgv 10 11 12 13 from the run's post, rgv 22 through
                  Seg.F5.f5_and_ones; rgv 24 25 kept; b5_sp 240, b5_F17, b5_W240, b5_PF through register 9;
        ctl_rt_C unchanged: the exit cut is applied at the same ly3 S3 and the same memory, so Hrt itself.

   SECTION HYPOTHESES: ACtl.v's Section Ctl shape (ACtl.v:170-194) copied; only LAWS (YCbq.v:207, for
   ajournal_exec) is used, the others vanish at End Section.  The run is REQUIRED (A.Prog.Seg.F5F), not assumed.

   NAMES: the core's twin modules are Required from ...lib.Reusable and written lib.Reusable.<X> (YK11 YK1b YM05
   YO09); ctrl's are Required from ...lib.A.Reusable and written A.Reusable.<X> (a Theorem Labs lane's measured rule and the
   porter amendment, 2026-10-29 04:2xZ / 04:33Z: in a file that Requires A.ACtlCutP the unprefixed two-part
   spelling of a twin resolves to ctrl's copy).  lib/Lib modules are Required from ...lib.Lib and written
   lib.Lib.<X> (lib/A/Bz/Lib has files of the same names).  The contract's getr and Lib.Frame names are these
   same constants (lib.Reusable.YK11.getr and the lib.Lib.Frame names).  getr / mkst / seg_rom / cfg_at are qualified
   everywhere; check
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F5_e10.v   -- hits only inside comments.
   The scratch build's Locate output (log below) confirms lib.Reusable.YK11 / YK1b / YM05 / YO09 are the core's
   lib.Reusable modules, A.Reusable.YK11 is ctrl's, lib.Lib.Frame / Mem / Regs6ss are lib/Lib's.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); the frame-route lemmas
   (Seg/F5.v, Tac_slot.v, RcAsanFPLib.v) are cited only inside proofs and are in the closure of Seg/F5F.v; no
   statement here names a frame-route identifier.

   ROUTE (C) L3 (a Theorem Labs lane, 2026-10-29; recipe L3-recipe.md (a working note, not in this delivery)):
   ctl_from hands the stage Hrt : A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch's shell).  The stage never opens Hrt
   (no destruct, no use of a shadow part); the exit needs ctl_rt_C B ly3 S3 mem3 again (same state, same memory),
   so the proof is unchanged: `exact Hrt`.  No VIS0 / OWNED_RO / AR_VIS0 / AR_OWNED_RO hypothesis and no
   stage-level ctlrt_of_AR.  The run's contract takes no mem_inv premise.

   BUILD STATE: type-check with cb build --fresh (BASE 23b918fe0c2e) on a working branch 1899bed1aee merged with
   a working branch; the lane report names the build log, the .vo mtime and Print Assumptions of
   glue_seg_F5_e10, f5g_keep, f5g_pf_keep and f5g_move (Rocq primitives and functional_extensionality_dep only).
   No Axiom, Parameter, Admitted or admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACfn A.AF0m A.ACeh A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.RcAsanFPLib A.Prog.Seg.Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F5 A.Prog.Seg.F5F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The shared lemmas (contract of the F5 glue lanes).  They take no Section argument. *)
Section F5gShared.

(* A register fact moves along a map that keeps that register. *)
Lemma f5g_rgv : forall (regs regs' : bvmap 5 word) (r : bv 5) (v : Z),
  lib.Reusable.YK11.getr regs' r = lib.Reusable.YK11.getr regs r -> ACtlCut.rgv regs r v -> ACtlCut.rgv regs' r v.
Proof. intros regs regs' r v E H. exact (eq_trans E H). Qed.

Lemma f5g_move : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 21 = lib.Reusable.YK11.getr regs 21 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.b5_C cx j phi fr regs m ->
  ACtlCutP.FLSI cx j fr regs' m /\ ACtlCutP.LK cx fr j regs' m /\ ACtlCutP.b5_C cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E2 E9 E18 E21 E23 H1 H2 H3.
  unfold ACtlCutP.FLSI, ACtlCutP.LK, ACtlCutP.b5_C in *.
  unfold ACtlCutP.FLSH, ACtlCutP.FLC, ACtlCutP.b5_PH, ACtlCutP.FSj in *.
  unfold ACtlCutP.PRO, ACtlCutP.FSb in *.
  unfold ACtlCutP.spill in *.
  unfold ACtlCut.rgv, Reusable.YG0d.spZ in *.
  (* the cut layer mixes the core's and ctrl's getr (same body): one form for the rewrites *)
  unfold lib.Reusable.YK11.getr, A.Reusable.YK11.getr in *.
  rewrite E2, E9, E18, E21, E23.
  exact (conj H1 (conj H2 H3)).
Qed.

Lemma f5g_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (W : list lib.Lib.Frame.ivl),
  ACtlCutP.HB m phi (ACtlCutP.flen cx j) -> ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m ->
  ACtlCutP.b5_C cx j phi fr regs m -> ACtlCutP.IDj cx fr j m ->
  ACtlCut.rgv regs 9 A -> A.AsanRT.HIGHMEM_BEG <= A -> A + 416 <= A.AsanRT.APPMEM_END ->
  fr + ACtlCutP.FRAME_BYTES <= A -> phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A ->
  ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono A.Img0.rsegs m m' -> A.AsanRTFacts.all_app W ->
  (forall x, x < A + 240 -> lib.Lib.Frame.outside W x) ->
  (forall x, A + 248 <= x < A + 280 -> lib.Lib.Frame.outside W x) ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 21 = lib.Reusable.YK11.getr regs 21 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\ ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\
  ACtlCutP.b5_C cx j phi fr regs' m' /\ ACtlCutP.IDj cx fr j m'.
Proof.
  intros cx j phi fr A regs regs' m m' W HHB HFLSI HLK HC HID H9 HAhi HAapp Hfa Hpa Hin MU WM HAW Hlo Hmid
    E2 E9 E18 E21 E23.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  assert (Hasz1 : 1 <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  assert (Hasz : ACtlCutP.flen cx j <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  (* the keeps, once each (Seg/F5.v's f5_spill_keep, f5_q64_keep, fl_bytes, sl_addr_keep), at the old map *)
  assert (SPK : forall off v, 0 <= off <= 408 -> ACtlCutP.spill regs m off v ->
            (forall x, A + off <= x < A + off + 8 -> lib.Lib.Frame.outside W x) -> ACtlCutP.spill regs m' off v).
  { intros off v Hoff Hs HW.
    exact (A.Prog.Seg.F5.f5_spill_keep regs regs A off v m m' W Hs H9 HA HAapp Hoff eq_refl MU HW). }
  assert (SPL : forall off v, 0 <= off <= 232 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v).
  { intros off v Hoff Hs. apply (SPK off v ltac:(lia) Hs). intros x Hx. apply Hlo. lia. }
  assert (SPM : forall off v, 248 <= off <= 272 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v).
  { intros off v Hoff Hs. apply (SPK off v ltac:(lia) Hs). intros x Hx. apply Hmid. lia. }
  assert (QL : forall a v, a + 8 <= A + 240 -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha Hq. exact (A.Prog.Seg.F5.f5_q64_keep W m m' a v Hq MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (QM : forall a v, A + 248 <= a -> a + 8 <= A + 280 -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha1 Ha2 Hq.
    exact (A.Prog.Seg.F5.f5_q64_keep W m m' a v Hq MU (fun x Hx => Hmid x ltac:(lia))). }
  assert (BL : forall a bs, a + Z.of_nat (length bs) <= A + 240 ->
            lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs).
  { intros a bs Ha Hb. exact (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (AK : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H. exact (A.Prog.Seg.Tac_slot.sl_addr_keep m m' W p n H MU HAW). }
  (* HB: the record block's addressable bytes *)
  assert (HHB' : ACtlCutP.HB m' phi (ACtlCutP.flen cx j)).
  { destruct HHB as (Hnz & Had). split; [exact Hnz | exact (AK _ _ Had)]. }
  (* FLSI at the old map *)
  assert (HFLSIm : ACtlCutP.FLSI cx j fr regs m').
  { destruct HFLSI as ((HPRO & Hf128 & Hfstk & Hf144 & Hfa17) & Hf216 & Hf224 & Hf248 & (HINa & HINb) & HFLC).
    destruct HPRO as (Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hp248 & Hfout6 & Hinb & Hing &
      Hp184 & Hp256 & Hp264 & Hp272 & Hp32).
    destruct HFLC as (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & Hcfg & Hcid & Hc72 & Hc64 &
      Hc56 & Hc48).
    (* the harness input block lies below A (premise) *)
    assert (HINb' := BL (ACtlCut.c_p cx) (ACtlCut.c_in cx) ltac:(lia) HINb).
    split.
    { split.
      { split; [exact (SPL 40 _ ltac:(lia) Hf40)|].
        split; [exact (SPL 120 _ ltac:(lia) Hf120)|].
        split; [exact (SPL 136 _ ltac:(lia) Hf136)|].
        split; [exact (SPL 160 _ ltac:(lia) Hf160)|].
        split; [exact (SPL 168 _ ltac:(lia) Hf168)|].
        split; [exact (SPL 176 _ ltac:(lia) Hf176)|].
        split; [exact (SPL 208 _ ltac:(lia) Hf208)|].
        split; [exact (SPM 248 _ ltac:(lia) Hp248)|].
        split; [exact (AK _ _ Hfout6)|].
        split; [exact (BL (ACtlCut.c_p cx) (ACtlCut.c_in cx) ltac:(lia) Hinb)|].
        split; [intros Hn; exact (AK _ _ (Hing Hn))|].
        split; [exact (SPL 184 _ ltac:(lia) Hp184)|].
        split; [exact (SPM 256 _ ltac:(lia) Hp256)|].
        split; [exact (SPM 264 _ ltac:(lia) Hp264)|].
        split; [exact (SPM 272 _ ltac:(lia) Hp272)|].
        exact (SPL 32 _ ltac:(lia) Hp32). }
      split; [exact (SPL 128 _ ltac:(lia) Hf128)|].
      split.
      { apply (A.Prog.RcAsanFPLib.fl_stk W m m' fr (fr + ACtlCutP.FRAME_BYTES) Hfstk MU WM).
        intros x Hx. left. apply Hlo. lia. }
      split; [exact (SPL 144 _ ltac:(lia) Hf144)|].
      exact (AK _ _ Hfa17). }
    split; [exact (SPL 216 _ ltac:(lia) Hf216)|].
    split; [exact (SPL 224 _ ltac:(lia) Hf224)|].
    split; [exact (SPM 248 _ ltac:(lia) Hf248)|].
    split; [split; [exact (AK _ _ HINa) | exact HINb']|].
    split; [exact (SPM 256 _ ltac:(lia) Hc256)|].
    split; [exact (SPL 184 _ ltac:(lia) Hc184)|].
    split; [exact (SPL 192 _ ltac:(lia) Hc192)|].
    split; [exact (SPL 80 _ ltac:(lia) Hc80)|].
    split; [exact (SPL 88 _ ltac:(lia) Hc88)|].
    split; [exact (SPL 96 _ ltac:(lia) Hc96)|].
    split; [exact (SPM 272 _ ltac:(lia) Hc272)|].
    split; [exact (SPM 264 _ ltac:(lia) Hc264)|].
    split; [exact (AK _ _ Hcfg)|].
    split; [exact (AK _ _ Hcid)|].
    split; [exact (SPL 72 _ ltac:(lia) Hc72)|].
    split; [exact (SPL 64 _ ltac:(lia) Hc64)|].
    split; [exact (SPL 56 _ ltac:(lia) Hc56)|].
    exact (SPL 48 _ ltac:(lia) Hc48). }
  (* LK at the old map: out[]'s six bytes at fr + 2624 are frame body *)
  assert (HLKm : ACtlCutP.LK cx fr j regs m').
  { destruct HLK as (Hj255 & H21 & HOURb).
    split; [exact Hj255|]. split; [exact H21|].
    refine (BL (fr + 2624) (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) _ HOURb).
    rewrite A.Prog.SlotModel.OUR_length. lia. }
  (* b5_C at the old map *)
  assert (HCm : ACtlCutP.b5_C cx j phi fr regs m').
  { destruct HC as (Hs23 & Hs18 & (A1 & H9a & HA1 & HSP & H232) & HPH & HFR & HKN & HFG & HFSj).
    assert (EA : A1 = A).
    { unfold ACtlCut.rgv in H9, H9a. apply A.Prog.Seg.F5.f5_id; [exact HA1 | exact HA |].
      rewrite <- H9a. exact H9. }
    subst A1.
    split; [exact Hs23|]. split; [exact Hs18|].
    split.
    { exists A. split; [exact H9|]. split; [exact HA|].
      destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
      split; [|exact (QL (A + 232) _ ltac:(lia) H232)].
      split; [exact (QM (A + 248) _ ltac:(lia) ltac:(lia) Hq248)|].
      split; [exact (QM (A + 256) _ ltac:(lia) ltac:(lia) Hq256)|].
      split; [exact (QL (A + 144) _ ltac:(lia) Hq144)|].
      split; [exact (QL (A + 184) _ ltac:(lia) Hq184)|].
      split; [exact (QL (A + 192) _ ltac:(lia) Hq192)|].
      split; [exact (QL (A + 80) _ ltac:(lia) Hq80)|].
      split; [exact (QL (A + 88) _ ltac:(lia) Hq88)|].
      split; [exact (QL (A + 96) _ ltac:(lia) Hq96)|].
      split; [exact (QM (A + 272) _ ltac:(lia) ltac:(lia) Hq272)|].
      exact (QM (A + 264) _ ltac:(lia) ltac:(lia) Hq264). }
    (* b5_PH: the record's 50 frame bytes lie in the record block, below A *)
    destruct HPH as (HPHb & HPHp).
    split.
    { split; [|exact HPHp].
      intros Hlen. refine (BL phi (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) _ (HPHb Hlen)).
      unfold A.Prog.SlotModel.t_g. rewrite A.Prog.SlotModel.fr50_length. lia. }
    (* b5_FR: the fragment record (72 bytes at fragb fr) and the identity record are frame body *)
    destruct HFR as (HFRa & HFRb & HFRc & HFRd).
    split.
    { split; [exact (AK _ _ HFRa)|]. split; [exact (AK _ _ HFRb)|]. split; [|exact HFRd].
      refine (BL (ACtlCutP.fragb fr) _ _ HFRc). rewrite HFRd. unfold ACtlCutP.fragb. lia. }
    (* b5_KN: the kind-name table is image data far below HIGHMEM_BEG <= A *)
    destruct HKN as (HKNa & HKNb).
    split.
    { split; [|exact (AK _ _ HKNb)].
      refine (BL _ _ _ HKNa).
      assert (Hknl : (length A.Prog.reac_ctrl_kind_name_c.kind_name_bytes <= 4096)%nat) by (vm_compute; lia).
      unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME. lia. }
    (* FGj: the 72 fragment bytes at fr + 2768 *)
    destruct HFG as (HFGb & HFGok).
    split.
    { split; [|exact HFGok]. unfold ACtlCutP.FGBe in *.
      refine (BL (fr + 2768) _ _ HFGb). rewrite HFRd. lia. }
    (* FSj: the two first-fragment spills and the first fragment's body (at most 23 bytes at fr + 2880) *)
    destruct HFSj as (Hq104 & Hq112 & Hfsb & Hfsa & HFI).
    split; [exact (SPL 104 _ ltac:(lia) Hq104)|].
    split; [exact (SPL 112 _ ltac:(lia) Hq112)|].
    split; [|split; [exact (AK _ _ Hfsa) | exact HFI]].
    refine (BL (fr + 2880) _ _ Hfsb).
    pose proof (A.Prog.Seg.F5.f5_fsb_len (ACtlCut.c_in cx) j) as Hbl. lia. }
  (* IDj: the 38 identity bytes at fr + 2688 are frame body *)
  assert (HIDm : ACtlCutP.IDj cx fr j m').
  { destruct HID as (Hb & Hok). split; [|exact Hok].
    refine (BL (fr + 2688) _ _ Hb). rewrite A.Prog.Seg.F5.f5_tID_len. lia. }
  (* the register move *)
  destruct (f5g_move cx j phi fr regs regs' m' E2 E9 E18 E21 E23 HFLSIm HLKm HCm) as (HF' & HL' & HC').
  exact (conj HHB' (conj HF' (conj HL' (conj HC' HIDm)))).
Qed.

Lemma f5g_pf_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (W : list lib.Lib.Frame.ivl),
  ACtlCutP.b5_PF cx j phi fr regs m -> ACtlCut.rgv regs 9 A ->
  A.AsanRT.HIGHMEM_BEG <= A -> A + 416 <= A.AsanRT.APPMEM_END -> 0 <= fr ->
  fr + ACtlCutP.FRAME_BYTES <= A -> phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A ->
  lib.Lib.Frame.munch W m m' -> A.AsanRTFacts.all_app W -> (forall x, x < A + 240 -> lib.Lib.Frame.outside W x) ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.b5_PF cx j phi fr regs' m'.
Proof.
  intros cx j phi fr A regs regs' m m' W HPF H9 HAhi HAapp Hfr0 Hfa Hpa MU HAW Hlo E9.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (EK : A.ACtlK.ASAN_K = A.AsanRT.ASAN_K) by reflexivity.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  assert (Hasz1 : 1 <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  assert (Hasz : ACtlCutP.flen cx j <= A.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold A.ACtlK.a_size; lia).
  assert (QL : forall a v, a + 8 <= A + 240 -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha Hq. exact (A.Prog.Seg.F5.f5_q64_keep W m m' a v Hq MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (BL : forall a bs, a + Z.of_nat (length bs) <= A + 240 ->
            lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs).
  { intros a bs Ha Hb. exact (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU (fun x Hx => Hlo x ltac:(lia))). }
  assert (AK : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H. exact (A.Prog.Seg.Tac_slot.sl_addr_keep m m' W p n H MU HAW). }
  destruct HPF as (A1 & H9a & HA1 & Hlong & H8819).
  assert (EA : A1 = A).
  { unfold ACtlCut.rgv in H9, H9a. apply A.Prog.Seg.F5.f5_id; [exact HA1 | exact HA |].
    rewrite <- H9a. exact H9. }
  subst A1.
  exists A. split; [exact (f5g_rgv regs regs' 9 A E9 H9)|]. split; [exact HA|].
  split.
  - (* the record's 38-byte prefix and t_phi lie in the record block, below A *)
    intros Hle. destruct (Hlong Hle) as ((rb & Hrb & Hrbl) & Hphib).
    split.
    + exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
      refine (BL phi _ _ (A.Prog.Seg.F5.f5_bytes_first m phi rb 38 Hrb)).
      rewrite length_firstn. lia.
    + refine (BL phi _ _ Hphib).
      (* Seg/F5.v's f5_tphi_len, over c_in cx: t_phi j is a firstn of flen j bytes *)
      assert (Hl : Z.of_nat (length (A.Prog.SlotModel.t_phi (ACtlCut.c_in cx) j)) <= ACtlCutP.flen cx j).
      { assert (H0 : 0 <= ACtlCutP.flen cx j) by lia.
        unfold ACtlCutP.flen, A.Prog.SlotModel.t_len, A.Prog.SlotModel.t_phi, A.Prog.SlotModel.f_phi in *.
        rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia. }
      lia.
  - intros Ht. destruct (H8819 Ht) as
      ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & Hv14 & Hv15 & Hv16 & Hv17 &
        Hs14 & Hs15 & Hs16 & Hs17 & Ef & Ek) &
       (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcm & Had) &
       (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Had2)).
    unfold ACtlCutP.u16, ACtlCutP.b8 in *.
    (* the metadata bytes of phi + 14 .. phi + 17 lie below HIGHMEM_BEG <= A *)
    pose proof (lib.Lib.Mem.bytes_at_bound segs m (phi + 14) _ Hb14) as (Hp14 & _).
    assert (Hshk : forall k, 14 <= k <= 17 -> Z.shiftr (phi + k) 3 + A.AsanRT.ASAN_K + 1 <= A).
    { intros k Hk. apply A.Prog.Seg.F5.f5_sh_below; [lia | exact HAhi]. }
    pose proof (Hshk 14 ltac:(lia)) as Hk14. pose proof (Hshk 15 ltac:(lia)) as Hk15.
    pose proof (Hshk 16 ltac:(lia)) as Hk16. pose proof (Hshk 17 ltac:(lia)) as Hk17.
    split; [|split].
    + exists field16, v14, v15, v16, v17.
      split; [refine (BL _ _ _ Hu16); rewrite lib.Lib.Mem.length_le2; lia|].
      split; [refine (BL _ _ _ Hb14); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb15); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb16); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hb17); cbn [length]; lia|].
      split; [exact Hv14|]. split; [exact Hv15|]. split; [exact Hv16|]. split; [exact Hv17|].
      split; [refine (BL _ _ _ Hs14); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs15); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs16); cbn [length]; lia|].
      split; [refine (BL _ _ _ Hs17); cbn [length]; lia|].
      split; [exact Ef | exact Ek].
    + exists (firstn 6 ls), (firstn 6 rs).
      split; [exact (QL (A + 72) _ ltac:(lia) Hq72)|].
      split; [refine (BL (fr + 186) _ _ (A.Prog.Seg.F5.f5_bytes_first m (fr + 186) ls 6 Hls));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [refine (BL phi _ _ (A.Prog.Seg.F5.f5_bytes_first m phi rs 6 Hrs)); rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite A.Prog.Seg.F5.f5_mcmp_firstn; exact Hcm|].
      exact (AK _ _ Had).
    + exists (firstn 6 ls2), (firstn 6 rs2).
      split; [exact (QL (A + 64) _ ltac:(lia) Hq64)|].
      split; [refine (BL (fr + 180) _ _ (A.Prog.Seg.F5.f5_bytes_first m (fr + 180) ls2 6 Hls2));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [refine (BL (phi + 6) _ _ (A.Prog.Seg.F5.f5_bytes_first m (phi + 6) rs2 6 Hrs2));
              rewrite length_firstn; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite A.Prog.Seg.F5.f5_mcmp_firstn; exact Hcm2|].
      exact (AK _ _ Had2).
Qed.

End F5gShared.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Section GlueF5e10.

(* ACtl.v's Section Ctl shape (ACtl.v:170-194), with the core's twin modules spelled lib.Reusable.<X>. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :270-271), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ea8_at := (ACtlCutP.C_A81ea8_at B).
Local Notation C_A81ec0_at := (ACtlCutP.C_A81ec0_at B).

Lemma glue_seg_F5_e10 : forall POST (j : nat), CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea8_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBASE HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A81ea8_at, ACtlCutP.v:2064-2074) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ea8_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & R22 & R24 & R25 & Hsp240 &
    Hu32 & HID & HF17 & HW240 & HPF).
  (* G2: the run's premises; phi + 18 in range from HB's addressable bounds *)
  pose proof HC as (Hs23 & _).
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hphi18 : 0 <= phi + 18 < 2 ^ 64).
  { pose proof HHB as (_ & Had). destruct Had as (Hp0 & Hn0 & Hpn & _). lia. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's start map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81ea8_at [Z.of_nat j])) with 0x81ea8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81ea8) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run (ctrl's FPState class at the core's fp registers), lifted at the empty footprint *)
  pose proof (@A.Prog.Seg.F5F.seg_F5_e10_run_F
                (A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr)
                regs3 mem3 phi A.ACtlG.Kit.kit_RNG0 R22 Hs23 R25) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the continuation at the run's end state; its map R is the exit cut's map *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 &
    K24 & K25 & K22 & K10 & K12 & K11 & K13).
  subst ms' pc' mem'.
  rewrite (A.Prog.Seg.F5.f5_and_ones (phi + 18) Hphi18) in K22.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81ec0_at [Z.of_nat j])) R mem3 md') (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HBASE).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81ec0_at (ACtlCutP.v:2078-2090), at the same turn j *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81ec0_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    unfold ACtlCutP.b5_body.
    exists phi.
    split; [exact Hperm|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    destruct (f5g_move cx j phi fr regs3 R mem3 K2 K9 K18 K21 K23 HFLSI HLK HC) as (HFLSI' & HLK' & HC').
    split; [exact HFLSI'|]. split; [exact HLK'|]. split; [exact HC'|].
    split; [exact Hlen50|].
    split; [exact K10|]. split; [exact K11|]. split; [exact K12|]. split; [exact K13|].
    split; [exact K22|].
    split; [exact (f5g_rgv regs3 R 24 _ K24 R24)|].
    split; [exact (f5g_rgv regs3 R 25 _ K25 R25)|].
    split.
    { destruct Hsp240 as (A0 & H90 & HA0 & Hq0). exists A0.
      exact (conj (f5g_rgv regs3 R 9 A0 K9 H90) (conj HA0 Hq0)). }
    split; [exact Hu32|]. split; [exact HID|].
    split.
    { destruct HF17 as (A7 & H97 & HA7 & Hq7). exists A7.
      exact (conj (f5g_rgv regs3 R 9 A7 K9 H97) (conj HA7 Hq7)). }
    split.
    { destruct HW240 as (A8 & H98 & HA8 & HW8). exists A8.
      exact (conj (f5g_rgv regs3 R 9 A8 K9 H98) (conj HA8 HW8)). }
    destruct HPF as (A9 & H99 & HPF9). exists A9.
    exact (conj (f5g_rgv regs3 R 9 A9 K9 H99) HPF9).
  - (* ctl_rt_C: the same ly3 S3 and the entry cut's memory *)
    exact Hrt.
Qed.

End GlueF5e10.
