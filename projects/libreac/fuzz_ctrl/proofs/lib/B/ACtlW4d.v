(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module names and numbers changed; 997 of its 1098 lines of code are new or changed and 3011 lines of the source are left out. *)
(* lib/B/ACtlW4d.v -- piece W4d (frame turn, part 4: S_F17b) of fuzz_ctrl image B's (asan-ubsan) walk of
   LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane.
   rule 24: no function proved (stage glue of a walk).

   WHAT THIS FILE PROVES: the stage lemma of cut-table row 60, POINTWISE in the frame-loop index j
   (ACtlCut.ix_cut, a Theorem Labs lane 22:47Z):
     B82468_at j (0x82468, own6, k <= 14+2j+1, live list entry ++ [(phi, flen cx j)]) --S_F17b--> B82634_at j
   S_F17b is the opens_record body: the length-and-sum guard, eleven UBSan pointer checks and nine instrumented byte
   checks of the record bytes Phi + 16 .. 26, then (f_opens) have = 1 at fr + 2880, n = gg[26] at fr + 2884 and
   __asan_memcpy(fr + 2885, Phi + 27, n) @0x82630.  Every failed test branches to 0x82634.
   The cut table's superseded note ("no segment _F twin, so the F17b stretch is re-proved inside the walk unless the
   lead allows mechanical _F re-runs") is OVERRULED by route (a) (lead FINAL 22:18Z via a Theorem Labs lane 22:29Z): seg_F17b is
   proved at UB (Seg/F17b.v :706 with Tac_f17b.v; plan 4 M12: no B gap), so this stage is glue over its `_F`.

   ROUTE, BUILD STATE, SHELL GAPS (G1) / (G2), the shared Section hypotheses tfibsegs_rsegs / Hwx / RTP / rt_of_core
   (FEVT is deleted: B.ProgBridge.fevt_of_evtF states it up to conversion) and
   the PENDING KIT / BRIDGE FACTS: exactly as lib/B/ACtlW0.v's header.

   THE PROOF of seg_F17b (closed with Qed):
   G1  the entry body C_B82468_at at index [Z.of_nat j]; the spill base A of the body is FRAC's (w4d_bv_eq), the frame
       is the journal's class-6 frame (frame law + layout_le), fr >= IMG_TOP (YG0t.hull_below_F, ALedger.al_img at
       rsegs' last segment, YG0s.frame_facts), fr + 4096 <= alloc_ceiling <= the stack window's floor (frames_bounds,
       astk_ok), the live blocks apart from the frame (YCbq.sep_block_frame) and below the ceiling (al_blocks).
   G2  the run's premises: registers from the body; the record gg := t_g j on a long frame and a 50-byte literal with a
       non-zero block sum on a short one, so that its block-sum test is t_sum_ok j in both; every footprint range is
       visible in W3 (RNG := ProgBridge.RNG_W (w_H W3)): the spills in the journal's stack window, Phi's bytes and
       their shadow by al_blocks / al_shadow (long frame only: F17bF's guarded premise), `first` by al_frames.
   G3/G4  SRr_xregs_eqv to mkR_of regs3, ProgBridge.fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt_hid.
   ARM 1 (a failed test or the guard: pc 0x82634, memory unchanged): the journal by ajournal_exec with no write; the
       exit body by w4d_exit_body (V := everything) with FSj (S j) = FSj j (w4d_fsj_false: f_opens is false).
   ARM 2 (f_opens): the journal across the two stores of `first` by ajournal_exec (Wr = [fr + 2880, fr + 2885), the
       owned frame); the call by YCbq.aj_intrin_at with AMEMCPY (d = fr + 2885, x = Phi + 27, n = gg[26] in [1, 22],
       o = sp - c_sp, raw = 0x82634; dest = owned frame, src = Phi's live block, both shadows visible and addressable,
       apart from each other and from the callee window); its post through B.ProgWorld.ctl_post_memcpy; the exit body by
       w4d_exit_body (V := visible in W3) with FSj (S j) = (1, gg[26], gg[27 .. 27 + gg[26])) (w4d_fsj_true), the
       frame's stk rebuilt over the stores and the copy, KIND_NAME's addressability from the post-call AR
       (ctl_kind_name_addressable), and ctl_rt_C (route (C), a working branch 78699c46fe7) by B.ProgWorldCtlRtC.ctl_rt_C_of_AR
       (PROVED) at the post AR with the post view's arodata_okP from ctl_base's arodata_okS
       (B.ProgWorld.arodata_okP_of_S, then Reusable.APostBase.arodata_ok_journalP across the whole journal).
       Neither arm reads a shadow_rw fact: arm 1 passes the entry's ctl_rt_C on (same ly3 S3 mem3).
   w4d_exit_body re-establishes FRAC (all its memory words incl. the trailer word q64 m (fr + 4088) .., carried as a
   frame word below [fr + 2880, fr + 2920)), HB, LK / FLI, FM, the 8819 facts, FTURN and IFS (S j) at the exit map and
   memory.  Model facts (turn, FI, t_FG / t_ID / t_g lengths, t_phi) are the pure lemmas of Seg/F17b.v and SlotInv.v;
   no run of Seg/F17b.v is cited, only a Theorem Labs lane's F17bF.seg_F17b_pre_F.

   SECTION HYPOTHESES the closed lemmas use (Print Assumptions at the end):
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR laws (YCbq Section d0's hypothesis); obligation: the core's
     AR_laws for B; owner: the top (a Theorem Labs lane; from the core / CtrlBB).  Same text as lib/B/ACtlW1.v, ACtlW4e1.v.
   - Hwx : wx_segs_nowrap segs -- the kit's once-per-unit fact (owner a Theorem Labs lane kit / the top; a Theorem Labs lane's
     rsegs_wx_nowrap is its proof).
   - AMEMCPY -- below.
   - RELRO_IMG, RO_OFL (a Context), TFIB_SYMS -- the route (C) texts (RELRO_IMG / TFIB_SYMS: lib/B/ACtl.v; RO_OFL
     a Theorem Labs lane 06:46Z); obligation: ctl_rt_C_of_AR's premise and arodata_ok_journalP's instance; owner: the top
     (RO_OFL by computation at SK := Reusable.YE2k.tfib_sink_head).
   - ctl_kind_name_addressable -- the shared RtPost V6 twin (owner a Theorem Labs lane, lib/B/ProgBridgeData.v).
   Unused here (kept as the shared header): tfibsegs_rsegs, RTP / rt_of_core (ProgBridge's proved lemmas are used).

   SECTION HYPOTHESES OF THIS FILE (sources):
   - AMEMCPY : __asan_memcpy @0x82630 (0x52164), the core's rule `aintrin_realizes segs B OCpy <pc>` (donor
     YG0d.v:317-335) at the catalogue NAME Reusable.YB1w.tfib_A_asan_memcpy (porter 23:00Z), through
     Reusable.YCbq.aj_intrin_at (YCbq.v:1953).
   - CITED, not a Section hypothesis (RTPOST-SHARED-B.txt (a working note, not in this delivery), its 15:40Z swap, a working branch 3131914eb3ca):
     B.ProgWorld.ctl_post_memcpy (lib/B/ProgWorld.v:765), the conversion of AMEMCPY's world-form post into
     visible-address facts; WR = the written range plus the callee window [sp - ESTACK, sp).  Used at 0x82630
     (seg_F17b step 2).  The former FEVT hypothesis is deleted too: B.ProgBridge.fevt_of_evtF (ProgBridge.v:30) states
     it up to conversion (Reusable.YB1v.tfibsegs = B.Img0.rsegs by B.ProgBridge.tfibsegs_rsegs, reflexivity).
   `_F` LEMMAS (a Theorem Labs lane; all image-B `_F` now on ONE branch, a working branch 12a7ea50807, cited from
   there; a Theorem Labs lane: a working branch d511d09bbd7 (the F17b fix); texts in
   F17bF.md (a working note, not in this delivery) as of 02:09Z; Required qualified, never
   Imported, a Theorem Labs lane 23:38Z; split at EVERY call):
   - F17bF.seg_F17b_pre_F (seg_F17b :706, stepped :782-1049: 0x82468 -> 0x82634 when f_opens is false, memory
     unchanged; or -> __asan_memcpy 0x52164 with ra = 0x82634, a0 = fr + 2885, a1 = phi + 27, a2 = bat gg 26 and
     F17b.f17_mid (the two stores of `first`) when f_opens is true; its premises restate the cut facts over regs / mem /
     Z and name AC.GT; CHANGED 00:3xZ by fix (b) of gap G3: the long-frame premises are one premise under
     `50 <= len ->`, and the short arm reads only [A + 248]; CHANGED 2026-10-29 by a Theorem Labs lane's fix round fixa
     (F17bF.v:225 (written on a working branch df21f34ec20); auditor a Theorem Labs lane's REFUSED verdict on P-W4 (a working note, not in this delivery)): the
     Phi/frame disjointness inside that premise is the cut's own form `phi + 50 <= fr + 2880 \/ fr + 2920 <= phi`
     (was `phi + 50 <= fr \/ fr + FRAME_BYTES <= phi`); CHANGED 2026-10-29 by a Theorem Labs lane's fix round fixf (asked by this
     lane): the Phi-side footprint premises are under `50 <= len ->` too.  This tree's F17bF.v is taken BY PATH from
     a working branch 3e6380b9029 (blob af9e4f20842 (the blob this tree had at release c5e779efe8c)))                                  PUBLISHED, proved
   - Tac_f17bF.f17_post_F (zero steps at the return 0x82634 over the memcpy's post memory, premises F17b.f17_mid /
     F17b.f17_cp; NOT applied, rule (2) of a Theorem Labs lane 00:4xZ: see seg_F17b step 2)                      PUBLISHED, proved
   - F17bF.f17_lu_evt_F (the lib.Lib -> UL engine bridge; steps nothing; not needed by this glue)   PUBLISHED, proved
   PROVENANCE: cut table row 60; plan 2.3 row 60, 4 (M12), 6.1 ("F17b's trap rows use HB, not rec_inv"), 6.2 row
   S_F17b, F.4.1 rows 27-40; runs at 3803efccea0 (F17b.v, Tac_f17b.v); objdump L85094-L85210.

   ABORT-SINK / TRAP OBLIGATIONS ON W4d (all branches into 0x82fa4 / 0x82fa0 in 0x82468-0x82634): the 14 UBSan
   branches 0x82478, 0x82480, 0x82488, 0x824b0, 0x824f8, 0x8251c, 0x82540, 0x82568, 0x82588, 0x825b0, 0x825d0, 0x825f0,
   0x82614, 0x82620 (F.4.1 rows 27-40, all -> 0x82fa0); no branch to 0x82fa4. *)

From Coq Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
(* lib/Lib's raw-memory vocabulary of the call-post fact below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F17bF Tac_f17bF.
(* Closure only (porter 23:38Z / 23:40Z): seg_F17b_pre_F names AC.GT (lib/B/Contract.v); the one bridging lemma below
   keeps it out of every statement.  Reusable.YImgTop arrives with the next planning-core sha. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Contract Reusable.YImgTop.
(* The closure the seg_F17b proof adds (Required, never Imported): the kit's lift and register move (YA0nR,
   Lib.Regs6ss), ProgBridge-B's lift names, the core's layout / AR / journal facts, and the PURE model lemmas of
   Seg/F17b.v and SlotInv.v (turn, FI, t_phi lengths; no run of those files is cited, only a Theorem Labs lane's F17bF run). *)
From Coq Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0t Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge B.AsanRT B.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.YF0m B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel B.Prog.SlotInv B.Prog.Seg.F17b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcFragLib Prog.RcModel.
Import ListNotations.
Local Open Scope Z_scope.

Section W4d.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING (see ACtlW0.v): the only lines that name ACtlCut's / ACtlCutP's argument lists. ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation C_B82468_at := (ACtlCutP.C_B82468_at B).
Local Notation C_B82634_at := (ACtlCutP.C_B82634_at B).

(* ---- Section hypotheses (sources in the header and in ACtlW0.v's) ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* rt_of_core, placeholder form (a Theorem Labs lane 22:44Z; no APIf, a Theorem Labs lane 23:05Z).  TODO: B's bridge statement verbatim. *)
Variable RTP : (word -> option byte) -> Prop.
Hypothesis rt_of_core : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> RTP mem.

(* __asan_memcpy @0x82630: the core's memcpy rule at B's catalogue name. *)
Hypothesis AMEMCPY :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy.

(* munch_vis / wmono_vis / rt_post_frame: the local notations of B.ProgWorld's Definitions of the same names (the
   walk's shared RtPost text); the memcpy post at site 0x82630 (return 0x82634 = the cut) is CITED:
   B.ProgWorld.ctl_post_memcpy. *)
Local Notation munch_vis H WR m m' :=
  (forall x : word, H x = false -> lib.Lib.Frame.outside WR (bv_unsigned x) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' x = lib.Lib.Mem.mrd B.Img0.rsegs m x).
Local Notation wmono_vis H m m' :=
  (forall x : word, H x = false -> wview B.Img0.rsegs m x <> None -> wview B.Img0.rsegs m' x <> None).
Local Notation rt_post_frame W mem mem' WR :=
  ((forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' a =
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a) /\
   (forall a, Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a ->
      Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem' a)).

(* ---- Section hypotheses the seg_F17b proof adds (each named; obligation and owner in the header) ---- *)
(* LAWS: the core's AR laws (YG0d.v:496-511), the hypothesis of YCbq's Section d0 under which ajournal_exec,
   aj_intrin_at and frames_bounds are stated; the same text as lib/B/ACtlW1.v / ACtlW3a.v / ACtlW4e1.v. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* Route (C) (a working branch 78699c46fe7; brief w4C-brief.md (a working note, not in this delivery)): ctl_rt_C at the exit state by B.ProgWorldCtlRtC.ctl_rt_C_of_AR
   (CtrlTSyms + AR_laws + AR + arodata_okP; no vis0-shadow or owned-ro premise); arodata_okP at the state
   from ctl_base's arodata_okS through Reusable.APostBase.arodata_ok_journalP (which finds RO_OFL as an instance).
   Texts token for token from lib/B/RTPOST-SHARED-B.txt (TFIB_SYMS, RELRO_IMG, RO_OFL); the top discharges them:
   TFIB_SYMS := Reusable.YD2l.CtrlB_syms, RELRO_IMG := relro_img_CtrlB, RO_OFL by computation at
   SK := Reusable.YE2k.tfib_sink_head. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* V6 twin for the KIND_NAME table (added 04:35Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as V6): FLI's KNT (ACtlCutP.v, `addressable m KNA.KIND_NAME 112`, carried by every LK cut) crosses a runtime
   call only through AR, since the image's shadow is allocator-owned. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* seg_F17b_pre_F names AC.GT (its premise `AC.GT <= fr`).  Porter 23:40Z: a stage file that applies an `_F` naming
   AC.GT states ONE lemma AC.GT = IMG_TOP and rewrites with it, so its statements say IMG_TOP only.
   lib/B/Contract.v:73 `Definition GT : Z := 0x5fe000`. *)
Lemma w4d_gt_img_top : B.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof.
  (* both unfold to 0x5fe000: lib/B/Contract.v:73 GT, lib/Reusable/YImgTop.v:9 IMG_TOP (only-parsing). *)
  unfold B.Contract.GT. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Local helpers of seg_F17b.  No statement below names a frame-route identifier. *)

(* The image placement premise of YCbq's Section d0 (the planning core's tfib_segs_low), from rsegs' spans. *)
Lemma w4d_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold Reusable.YG0f.kLowMemEnd.
  pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin) as H.
  cbv beta in H. rewrite B.ProgBridge.tfibsegs_rsegs, B.ProgBridge.rsegs_spans in H.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

(* Two Z values of one 64-bit word, the second a small address and the first above -2^63, are equal. *)
Lemma w4d_bv_eq : forall x y : Z, Z_to_bv 64 x = Z_to_bv 64 y -> 0 <= y < 2 ^ 63 -> - 2 ^ 63 <= x < 2 ^ 64 ->
  x = y.
Proof.
  intros x y E Hy Hx. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  rewrite (Z.mod_small y) in E by lia.
  destruct (Z_lt_le_dec x 0) as [Hn | Hp].
  - rewrite <- (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)) in E by lia. lia.
  - rewrite Z.mod_small in E by lia. exact E.
Qed.

Lemma w4d_q64_bounds : forall m a v, ACtlCutP.q64 m a v -> 0 <= a /\ a + 8 <= 2 ^ 64.
Proof. intros m a v (H0 & H1 & _). rewrite lib.Lib.Mem.length_le8 in H1. lia. Qed.

(* A spilled word read at the cut's spill base A (the F17b.v f17_spq argument, over ACtlCutP's names). *)
Lemma w4d_spq : forall regs m off v A, ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A ->
  0 <= A < 2 ^ 62 -> 0 <= off <= 440 -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HAb Hoff.
  pose proof (w4d_q64_bounds _ _ _ Hq) as HB'.
  assert (E : A' = A).
  { apply w4d_bv_eq; [unfold ACtlCut.rgv in HA, HA'; rewrite <- HA, <- HA'; reflexivity | lia | lia]. }
  subst A'. exact Hq.
Qed.

(* One 8-byte cell holds one word value. *)
Lemma w4d_q64_eq : forall m a v v', ACtlCutP.q64 m a v -> ACtlCutP.q64 m a v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
  intros m a v v' (_ & _ & H1) (_ & _ & H2) Hv Hv'.
  assert (E : lib.Lib.Mem.le8 (Z_to_bv 64 v) = lib.Lib.Mem.le8 (Z_to_bv 64 v')).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi | Hi].
    - rewrite <- (H1 i), <- (H2 i) by (rewrite lib.Lib.Mem.length_le8; lia). reflexivity.
    - assert (N1 : nth_error (lib.Lib.Mem.le8 (Z_to_bv 64 v)) i = None)
        by (apply nth_error_None; rewrite lib.Lib.Mem.length_le8; lia).
      assert (N2 : nth_error (lib.Lib.Mem.le8 (Z_to_bv 64 v')) i = None)
        by (apply nth_error_None; rewrite lib.Lib.Mem.length_le8; lia).
      rewrite N1, N2. reflexivity. }
  apply (f_equal le_bytes_to_word) in E. rewrite !lib.Lib.Mem.le_bytes_to_word_le8 in E.
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* Carrying a byte range, and the addressability of a range, to a memory that reads the same bytes there. *)
Lemma w4d_bytes_keep : forall m m' a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (a + i)) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (a + i))) ->
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite K by lia. exact (H i Hi).
Qed.

Lemma w4d_addr_keep : forall m m' p n,
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. split; [|exact Hok]. rewrite <- Hb. exact (K i Hi).
Qed.

Lemma w4d_ba_firstn : forall m a bs n, lib.Lib.Mem.bytes_at segs m a bs -> (n <= length bs)%nat ->
  lib.Lib.Mem.bytes_at segs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H) Hn.
  assert (Lf : length (firstn n bs) = n) by (rewrite length_firstn; lia).
  split; [exact H0|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi. rewrite H by lia. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec0 i n) as [_|C]; [reflexivity | lia].
Qed.

Lemma w4d_ba_sub : forall m a bs k n, lib.Lib.Mem.bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  lib.Lib.Mem.bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (Lf : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i n) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* The shadow of p + x for an 8-aligned p. *)
Lemma w4d_sh_add : forall p x, p mod 8 = 0 -> 0 <= x ->
  B.AsanRT.shadow_addr (p + x) = B.AsanRT.shadow_addr p + x / 8.
Proof.
  intros p x Hp Hx. unfold B.AsanRT.shadow_addr.
  replace (p + x) with (p / 8 * 8 + x) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  rewrite Z.div_add_l by lia. replace (p / 8 * 8 / 8) with (p / 8) by (rewrite Z.div_mul; lia). lia.
Qed.

(* A byte the core's view reads is visible (a Theorem Labs lane's vis_of_aview, lib/A/ProgWorldVisFrame.v, restated). *)
Lemma w4d_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

(* Turn j's record length is not negative (SlotInv.v t_phi_length's argument). *)
Lemma w4d_tlen_nn : forall inp j, 0 <= B.Prog.SlotModel.t_len inp j.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_len, B.Prog.SlotModel.f_len, B.Prog.SlotModel.f_h, B.Prog.SlotModel.f_L.
  pose proof (B.Prog.SlotInv.inb_range inp (B.Prog.SlotModel.fc inp j)).
  pose proof (B.Prog.SlotInv.inb_range inp (B.Prog.SlotModel.fc inp j + 1)).
  destruct (2 <=? B.Prog.SlotModel.f_left inp (B.Prog.SlotModel.fc inp j)); lia.
Qed.

(* The first-fragment state of turn S j (SlotModel.turn), on both arms of f_opens: the FI part (Seg/F17b.v
   f17_fi_false / f17_fi_true, restated over the input list; proofs from F17b.v's model lemmas). *)
Lemma w4d_fi_false : forall inp j,
  B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j) = false ->
  B.Prog.SlotModel.FI (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.fst_at inp j) ->
  B.Prog.SlotModel.FI (B.Prog.SlotModel.t_FG inp (S j)) (B.Prog.SlotModel.fst_at inp (S j)).
Proof.
  intros inp j Hop HFI.
  rewrite B.Prog.Seg.F17b.f17_tFG_S. unfold B.Prog.SlotModel.fg_st. rewrite B.Prog.SlotModel.fst_at_S.
  destruct (B.Prog.Seg.F17b.f17_turn_false (B.Prog.SlotModel.fst_at inp j) (B.Prog.SlotModel.t_len inp j)
              (B.Prog.SlotModel.t_g inp j) Hop) as (E1 & E2 & E3).
  unfold B.Prog.SlotModel.FI in *. rewrite E1, E2, E3.
  destruct (B.Prog.Seg.F17b.f17_next_clear_or_same (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_FG inp j)
              (B.Prog.SlotModel.t_g inp j) Hop (B.Prog.Seg.F17b.f18_FG_length inp j)
              (B.Prog.Seg.F17b.f17_g_length inp j)) as [Hsame | Hz].
  - rewrite Hsame. exact HFI.
  - intros H6. rewrite Hz in H6. discriminate H6.
Qed.

Lemma w4d_fi_true : forall inp j,
  B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j) = true ->
  B.Prog.SlotModel.FI (B.Prog.SlotModel.t_FG inp (S j)) (B.Prog.SlotModel.fst_at inp (S j)).
Proof.
  intros inp j Hop.
  pose proof (B.Prog.Seg.F17b.f17_g_length inp j) as HG.
  assert (HFR : Prog.RcFrag.fg_fr (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j) = true /\
                (Prog.RcFrag.bat (B.Prog.SlotModel.t_g inp j) 19 =? 1) = true).
  { unfold B.Prog.SlotModel.f_opens in Hop. apply andb_prop in Hop. exact Hop. }
  destruct HFR as (HFR1 & H19).
  pose proof (B.Prog.Seg.F17b.f18_fg_n _ _ HFR1) as Hn.
  assert (ECL : B.Prog.SlotModel.fcls (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_FG inp j)
                  (B.Prog.SlotModel.t_g inp j) = Prog.RcFrag.FgFirst).
  { unfold B.Prog.SlotModel.fcls. rewrite Prog.RcFragLib.rf_class_nn by lia. rewrite HFR1. cbn [negb].
    rewrite H19. reflexivity. }
  rewrite B.Prog.Seg.F17b.f17_tFG_S. unfold B.Prog.SlotModel.fg_st. rewrite ECL.
  cbn [B.Prog.SlotModel.fg_next]. rewrite B.Prog.SlotModel.fst_at_S.
  destruct (B.Prog.Seg.F17b.f17_turn_true (B.Prog.SlotModel.fst_at inp j) (B.Prog.SlotModel.t_len inp j)
              (B.Prog.SlotModel.t_g inp j) Hop) as (E1 & E2 & E3).
  unfold B.Prog.SlotModel.FI. rewrite E1, E2, E3.
  rewrite (B.Prog.Seg.F17b.f17_first_bat7 (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j)
             ltac:(lia)).
  intros _. split; [reflexivity|]. split; [reflexivity|].
  symmetry. apply (B.Prog.Seg.F17b.f17_first_body (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j)
                     HG Hn).
Qed.

(* FSj of turn S j: turn j's when the record does not open (memory unchanged), and (1, gg[26], gg[27 ..]) when
   it does (Seg/F17b.v f17_fsj_false / f17_fsj_true over ACtlCutP's FSj). *)
Lemma w4d_fsj_false : forall cx fr j (regs regs' : bvmap 5 word) m,
  B.Prog.SlotModel.f_opens (ACtlCutP.flen cx j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = false ->
  ACtlCutP.FSj cx fr j regs m -> ACtlCutP.FSj cx fr (S j) regs' m.
Proof.
  intros cx fr j regs regs' m Hop (H0 & H4 & Hbody & Had & HFI).
  pose proof (w4d_fi_false _ j Hop HFI) as HFI'.
  unfold ACtlCutP.FSj, ACtlCutP.FSb. rewrite B.Prog.SlotModel.fst_at_S in *.
  destruct (B.Prog.Seg.F17b.f17_turn_false (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)
              (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) Hop)
    as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H0|]. split; [exact H4|]. split; [exact Hbody|]. split; [exact Had | exact HFI'].
Qed.

Lemma w4d_fsj_true : forall cx fr j (regs : bvmap 5 word) m,
  B.Prog.SlotModel.f_opens (ACtlCutP.flen cx j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = true ->
  ACtlCutP.u32 m (fr + 2880) 1 ->
  ACtlCutP.b8 m (fr + 2884) (Prog.RcFrag.bat (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 26) ->
  lib.Lib.Mem.bytes_at segs m (fr + 2885)
    (firstn (Z.to_nat (Prog.RcFrag.bat (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 26))
            (skipn 27 (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))) ->
  B.AsanRT.addressable m (fr + 2880) 40 -> ACtlCutP.FSj cx fr (S j) regs m.
Proof.
  intros cx fr j regs m Hop H0 H4 Hbody Had.
  pose proof (w4d_fi_true _ j Hop) as HFI.
  unfold ACtlCutP.FSj, ACtlCutP.FSb. rewrite B.Prog.SlotModel.fst_at_S in *.
  destruct (B.Prog.Seg.F17b.f17_turn_true (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)
              (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) Hop)
    as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H0|]. split; [exact H4|]. split; [exact Hbody|]. split; [exact Had | exact HFI].
Qed.

(* An image byte lies below the image top 0x5fe000 (rsegs' spans), so no byte at or above it is read-only data. *)
Lemma w4d_img_hi : forall a, Reusable.YG0d.in_img segs a -> a < 0x5fe000.
Proof.
  intros a (sg & Hin & Hr).
  pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin) as H.
  cbv beta in H. rewrite B.ProgBridge.tfibsegs_rsegs, B.ProgBridge.rsegs_spans in H.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

Lemma w4d_mrd_some : forall m a, 0x5fe000 <= a < 2 ^ 64 ->
  lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a) <> None -> m (lib.Lib.Mem.wa a) <> None.
Proof.
  intros m a Ha H Hm. unfold lib.Lib.Mem.mrd in H. rewrite Hm in H.
  assert (Hi : Reusable.YG0d.in_img segs a).
  { apply (Reusable.YG0s.seg_rom_in_img segs a ltac:(lia)). exact H. }
  pose proof (w4d_img_hi a Hi). lia.
Qed.

(* At a visible address the core's view is lib/Lib's mrd read (the content of the shared aview_vis_mrd, proved here
   from the definitions: YG0n.aview reads YP09.mbyte of the restricted memory). *)
Lemma w4d_aview_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a)).
Proof.
  intros W mem a Hh.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  rewrite Hh. reflexivity.
Qed.

(* The core's view is unchanged where a raw munch keeps the memory. *)
Lemma w4d_aview_munch : forall (H : word -> bool) W0 m m' s, lib.Lib.Frame.munch W0 m m' -> 0 <= s < 2 ^ 64 ->
  lib.Lib.Frame.outside W0 s -> Reusable.YG0n.aview segs H m' s = Reusable.YG0n.aview segs H m s.
Proof.
  intros H W0 m m' s MU Hs Ho. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
  rewrite (MU (Z_to_bv 64 s)); [reflexivity|]. rewrite lib.Lib.MState.unsigned_lit by lia. exact Ho.
Qed.

(* A shadow byte of non-negative signed value reads the same unsigned. *)
Lemma w4d_signed_nn : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 `div` 2) with 128 in *.
  destruct (Z_lt_le_dec (bv_unsigned b) 128) as [Hl | Hl].
  - rewrite Z.mod_small in * by lia. lia.
  - rewrite <- (Z.mod_unique (bv_unsigned b + 128) 256 1 (bv_unsigned b - 128)) in H by lia. lia.
Qed.

(* ctrl's addressable range, with its shadow bytes visible, is the core's range_addressable over the view. *)
Lemma w4d_range_addr : forall (W : Reusable.YA0n.world segs) m p n,
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  B.AsanRT.addressable m p n ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m)
    Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n HV (H0 & H1 & H2 & H) x Hx.
  destruct (H (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  replace (p + (x - p)) with x in Hb, Hok by ring.
  pose proof (HV (x - p) ltac:(lia)) as Hv. replace (p + (x - p)) with x in Hv by ring.
  exists (bv_unsigned b).
  replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x) with (B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite (w4d_aview_mrd W m _ Hv). rewrite Hb. split; [reflexivity|].
  unfold B.AsanRT.shadow_ok in Hok. unfold Reusable.YG0v.saddr_ok.
  destruct Hok as [Hz | (Hlt & Hle)].
  - left. rewrite w4d_signed_nn by lia. exact Hz.
  - right. rewrite w4d_signed_nn by lia. pose proof (Z.mod_pos_bound x 8). lia.
Qed.

Lemma w4d_ba_some : forall m a bs i, lib.Lib.Mem.bytes_at segs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (a + i)) <> None.
Proof.
  intros m a bs i (_ & _ & H) Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite H by lia. intros E. apply nth_error_None in E. lia.
Qed.

(* A spill (ACtlCutP.spill) at a map that keeps s1 and a memory that keeps the spilled word. *)
Lemma w4d_spill_keep : forall (regs regs' : bvmap 5 word) m m' off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 62 -> 0 <= off <= 440 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall i, 0 <= i < 8 ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (A + off + i)) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (A + off + i))) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' off v A Hs HA HAb Hoff E9 K.
  pose proof (w4d_spq _ _ _ _ _ Hs HA HAb Hoff) as Hq.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA |].
  unfold ACtlCutP.q64 in *. apply (w4d_bytes_keep m m'); [|exact Hq].
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. apply K. lia.
Qed.

Local Ltac w4d_carry m m' KK H :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  apply (w4d_bytes_keep m m');
  [ intros i Hi; rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4 in Hi; cbn [length] in Hi; apply KK; lia
  | exact H ].

Local Ltac w4d_carry_ad m m' KK H :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  apply (w4d_addr_keep m m'); [ intros i Hi; apply KK; lia | exact H ].

Local Ltac w4d_sp regs regs' m m' A R9 E9 KS :=
  match goal with
  | H : ACtlCutP.spill regs m ?off ?v |- ACtlCutP.spill regs' m' ?off ?v =>
      apply (w4d_spill_keep regs regs' m m' off v A H R9 ltac:(lia) ltac:(lia) E9);
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply KS; lia
  end.

Local Ltac w4d_sb m m' KBS H :=
  apply (w4d_bytes_keep m m');
  [ let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi; cbn [length] in Hi;
    match goal with |- context [lib.Lib.Mem.wa (Z.shiftr ?x 3 + _ + i)] =>
      replace (Z.shiftr x 3 + B.ACtlK.ASAN_K + i) with (B.AsanRT.shadow_addr x)
        by (rewrite Z.shiftr_div_pow2 by lia; unfold B.AsanRT.shadow_addr, B.ACtlK.ASAN_K;
            change (2 ^ 3) with 8; lia);
      apply KBS; lia
    end
  | exact H ].

(* THE EXIT BODY.  C_B82634_at's body from C_B82468_at's at a register map that keeps the callee-saved registers the
   bodies read and a memory that reads the same bytes at every V-address outside `first` [fr + 2880, fr + 2920) and
   the callee window [sp - ESTACK, sp) (V: the visible addresses on the memcpy arm, every address on the others),
   given turn S j's first-fragment state FSj (S j), the frame's stk, and KIND_NAME's addressability at the exit
   memory.  V covers the stack window, the owned frame and its shadow, the live blocks and their shadow, the image;
   the live blocks lie apart from the frame and, with the frame, below Cl, the stack window's floor. *)
Lemma w4d_exit_body : forall (V : Z -> Prop) (Cl : Z) cx (j : nat) bl fr (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCut.cut_body C_B82468_at cx [Z.of_nat j] bl fr fr regs m ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 20 = lib.Reusable.YK11.getr regs 20 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  (forall a, 0 <= a < 2 ^ 64 -> V a -> ~ (fr + 2880 <= a < fr + 2920) ->
     ~ (Reusable.YG0d.spZ regs - Reusable.YG0d.ESTACK <= a < Reusable.YG0d.spZ regs) ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)) ->
  (forall a, ACtlCut.c_sp cx - Reusable.YG0d.ESTACK <= a < ACtlCut.c_sp cx -> V a) ->
  (forall a, fr <= a < fr + 4096 -> V a) ->
  (forall i, 0 <= i < 512 -> V (B.AsanRT.shadow_addr fr + i)) ->
  (forall p n a, In (p, n) bl -> p <= a < p + Reusable.YG00.req_size n -> V a) ->
  (forall p n i, In (p, n) bl -> 0 <= i < (Reusable.YG00.req_size n + 7) / 8 ->
     V (B.AsanRT.shadow_addr p + i)) ->
  (forall a, 0x10000 <= a < 0x5fe000 -> V a) ->
  (forall p n, In (p, n) bl -> p mod 8 = 0 /\ (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p) /\
     p + Reusable.YG00.req_size n <= Cl) ->
  0x5fe000 <= fr -> fr + 4096 <= Cl -> Cl <= Reusable.YG0d.spZ regs - Reusable.YG0d.ESTACK ->
  0x7fff7f800000 <= Cl <= 0x7fffff800000 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  B.AsanRT.addressable m' B.ACtlCutP.KNA.KIND_NAME 112 ->
  ACtlCutP.FSj cx fr (S j) regs' m' ->
  ACtlCut.cut_body C_B82634_at cx [Z.of_nat j] bl fr fr regs' m'.
Proof.
  intros V Cl cx j bl fr regs regs' m m' Hb E2 E3 E4 E8 E9 E18 E19 E20 E22 E24 E25 E26 E27 K
    HVs HVf HVfs HVb HVbs HVi HBF Hfr0 HfrC HCsp HCl HSTK HKN HFS.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82468_at ACtlCutP.fcutp_body ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & R18 & R20 & HFTURN & HLK & HFM & HFSj & HLONG & R27 &
    (A & kp & R9 & Q280 & Happ & (w272 & Q272 & Hw272 & Hw1 & Hw2) & R24 & Hkpfr & Hkpsp & HPHI & H8819) &
    HRECS & HFS9).
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82634_at ACtlCutP.ixn nth]. rewrite Nat2Z.id.
  destruct HFRAC as (A' & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9' & R3 & R19 & R26 & Hfr32 & HA32 & HAsp & HspA &
    HfrA & HA448 & Hsp4096 & HspApp & Q336 & Q48 & Q40 & Qfr & Qfr16 & (sh & Hsh & Hshl) & Hsaved & Qtr).
  unfold ACtlCutP.flen in *.
  unfold ACtlCutP.FRAME_BYTES, B.AsanRT.APPMEM_END, Reusable.YG0d.ESTACK in *.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as Hsp0.
  change (bv_unsigned (lib.Reusable.YK11.getr regs 2)) with (Reusable.YG0d.spZ regs) in Hsp0.
  rewrite Hspz in Hsp0. unfold bv_modulus in Hsp0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hsp0.
  assert (HspZ' : Reusable.YG0d.spZ regs' = sp) by (unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz).
  assert (EA : A = A').
  { pose proof (w4d_q64_bounds _ _ _ Q280) as HQ.
    apply w4d_bv_eq; [unfold ACtlCut.rgv in R9, R9'; rewrite <- R9, <- R9'; reflexivity | lia | lia]. }
  subst A'.
  destruct HLK as (Hj' & S240 & HOUR & HFLI).
  pose proof HFLI as (_ & _ & S96 & S112 & _ & _ & _ & _ & _ & S280 & _).
  (* ---- the memory kept, region by region ---- *)
  assert (KS : forall a, A <= a < ACtlCut.c_sp cx ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)).
  { intros a Ha. apply K; [lia | apply HVs; lia | lia | rewrite Hspz; lia]. }
  assert (KF : forall a, fr <= a < fr + 4096 -> ~ (fr + 2880 <= a < fr + 2920) ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)).
  { intros a Ha Hn1. apply K; [lia | apply HVf; lia | exact Hn1 | rewrite Hspz; lia]. }
  assert (HappLH : fr + 2920 <= 0x7fff8000 \/ 0x10007fff8000 <= fr + 2880).
  { pose proof (Happ (fr + 2880) ltac:(lia)) as H1. pose proof (Happ (fr + 2919) ltac:(lia)) as H2.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG in H1, H2. lia. }
  assert (KSH : forall y, 0 <= y < Cl -> V (B.AsanRT.shadow_addr y) ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y)) =
            lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y))).
  { intros y Hy HV. apply K; [ | exact HV | | rewrite Hspz ];
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia. }
  assert (KFS : forall y, fr <= y < fr + 4096 ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y)) =
            lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y))).
  { intros y Hy. apply KSH; [lia |].
    replace y with (fr + (y - fr)) by ring. rewrite (w4d_sh_add fr (y - fr)) by lia.
    apply HVfs. lia. }
  assert (Hinb : In (phi, B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) bl).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (HBF _ _ Hinb) as (Hphi8 & Hphifr & HphiC).
  pose proof (w4d_tlen_nn (ACtlCut.c_in cx) j) as Hlen0.
  assert (Hrq : B.ACtlK.a_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) =
                Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)).
  { unfold Reusable.YG00.req_size, B.ACtlK.a_size.
    destruct (Z.eqb_spec (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) 0); lia. }
  assert (Hrq1 : B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j <=
                 Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)).
  { rewrite <- Hrq. unfold B.ACtlK.a_size. lia. }
  destruct HHB as (Hphinz & HphiA).
  pose proof HphiA as (Hphi0 & _ & _ & _).
  assert (KB : forall a, phi <= a < phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)).
  { intros a Ha. apply K; [lia | apply (HVb _ _ a Hinb Ha) | lia | rewrite Hspz; lia]. }
  assert (KBS : forall y, phi <= y < phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y)) =
            lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr y))).
  { intros y Hy. apply KSH; [lia |].
    replace y with (phi + (y - phi)) by ring. rewrite (w4d_sh_add phi (y - phi)) by lia.
    apply (HVbs _ _ _ Hinb). lia. }
  assert (KI : forall a, 0x10000 <= a < 0x5fe000 ->
            lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)).
  { intros a Ha. apply K; [lia | apply HVi; lia | lia | rewrite Hspz; lia]. }
  assert (HB' : ACtlCutP.HB m' phi (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)).
  { split; [exact Hphinz|]. apply (w4d_addr_keep m m'); [|exact HphiA].
    intros i Hi. apply KBS. rewrite Hrq in Hi. lia. }
  (* ---- the exit body ---- *)
  exists phi. split; [exact Hperm|].
  split.
  { (* FRAC *)
    unfold ACtlCutP.FRAC. exists A, sp.
    split; [rewrite E2; exact R2|]. split; [exact Hsp16|]. split; [exact HspZ'|].
    split; [rewrite E4; exact R4|]. split; [unfold ACtlCut.rgv; rewrite E8; exact R8|].
    split; [unfold ACtlCut.rgv; rewrite E9; exact R9|]. split; [rewrite E3; exact R3|].
    split; [unfold ACtlCut.rgv; rewrite E19; exact R19|]. split; [unfold ACtlCut.rgv; rewrite E26; exact R26|].
    unfold ACtlCutP.FRAME_BYTES, B.AsanRT.APPMEM_END.
    split; [exact Hfr32|]. split; [exact HA32|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|].
    split; [w4d_carry m m' KS Q336|]. split; [w4d_carry m m' KS Q48|]. split; [w4d_carry m m' KS Q40|].
    split; [w4d_carry m m' KF Qfr|]. split; [w4d_carry m m' KF Qfr16|].
    split.
    - exists sh. split; [|exact Hshl]. apply (w4d_bytes_keep m m'); [|exact Hsh].
      intros i Hi. rewrite Hshl in Hi. change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Hi.
      unfold ACtlCutP.Sfr. apply K; [ | apply HVfs; lia | | rewrite Hspz];
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia.
    - assert (LSB : length (ACtlCutP.saved_bytes cx) = 104%nat).
      { unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
      split.
      + apply (w4d_bytes_keep m m'); [|exact Hsaved].
        intros i Hi. rewrite LSB in Hi. apply KS. lia.
      + w4d_carry m m' KF Qtr. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [exact HB'|].
  split.
  { (* LK *)
    split; [exact Hj'|]. split; [w4d_sp regs regs' m m' A R9 E9 KS|].
    split.
    - unfold ACtlCutP.OURb in *.
      assert (LO : length (B.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat).
      { unfold B.Prog.SlotModel.OUR. rewrite length_map, length_seq. reflexivity. }
      apply (w4d_bytes_keep m m'); [intros i Hi; rewrite LO in Hi; apply KF; lia | exact HOUR].
    - unfold ACtlCutP.FLI in HFLI |- *.
      destruct HFLI as (R27f & HFLI). split; [unfold ACtlCut.rgv; rewrite E27; exact R27f|].
      decompose [and] HFLI. clear HFLI.
      repeat match goal with |- _ /\ _ => split end;
        try (w4d_sp regs regs' m m' A R9 E9 KS).
      + match goal with H : ACtlCutP.ART.addressable m (fr + 2624) 6 |- _ => w4d_carry_ad m m' KFS H end.
      + exact HSTK.
      + match goal with H : ACtlCutP.RAD fr m |- _ => rename H into HRAD end.
        unfold ACtlCutP.RAD in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
        split; [w4d_carry_ad m m' KFS Ra1|]. split; [unfold ACtlCutP.fragb in *; w4d_carry_ad m m' KFS Ra2|].
        w4d_carry_ad m m' KFS Ra3.
      + match goal with H : ACtlCutP.KNT m |- _ => rename H into HKNT end.
        unfold ACtlCutP.KNT in *. destruct HKNT as (Kb & Ka). split; [|exact HKN].
        assert (LKN : length B.ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
        apply (w4d_bytes_keep m m'); [|exact Kb].
        intros i Hi. rewrite LKN in Hi. apply KI. unfold B.ACtlCutP.KNA.KIND_NAME. lia. }
  split; [unfold ACtlCut.rgv; rewrite E20; exact R20|].
  split.
  { (* FM *)
    destruct HFM as (S184 & R24' & R22 & R25 & S312).
    split; [w4d_sp regs regs' m m' A R9 E9 KS|]. split; [unfold ACtlCut.rgv; rewrite E24; exact R24'|].
    split; [unfold ACtlCut.rgv; rewrite E22; exact R22|]. split; [unfold ACtlCut.rgv; rewrite E25; exact R25|].
    w4d_sp regs regs' m m' A R9 E9 KS. }
  split.
  { (* the spill base, kp, w272 and the 8819 facts *)
    exists A, kp, w272.
    split; [unfold ACtlCut.rgv; rewrite E9; exact R9|]. split; [lia|]. split; [rewrite HspZ'; lia|].
    split; [unfold ACtlCut.rgv; rewrite E18; exact R18|]. split; [unfold ACtlCut.rgv; rewrite E24; exact R24|].
    split; [w4d_carry m m' KS Q280|]. split; [w4d_carry m m' KS Q272|]. split; [exact Hw272|].
    split; [exact Hw2|].
    intros Ht.
    destruct (H8819 Ht) as (HRI & (L & ls & rs & QL & BL & LL & BR & LR & Hcmp & AL & AL6 & AL7 & HLsp & HLfr) &
                            (L2 & ls2 & rs2 & QL2 & BL2 & LL2 & BR2 & LR2 & Hcmp2 & AL2 & AL26 & AL27 & HL2sp & HL2fr)).
    pose proof (w4d_spq _ _ _ _ _ S280 R9 ltac:(lia) ltac:(lia)) as Q280'.
    pose proof (w4d_spq _ _ _ _ _ S112 R9 ltac:(lia) ltac:(lia)) as Q112'.
    pose proof (w4d_spq _ _ _ _ _ S96 R9 ltac:(lia) ltac:(lia)) as Q96'.
    destruct HRI as (Hphi0' & Hphi50 & Hfl50 & Htk & Happphi & Q312 & Hblk & Hbsl &
                     (f16 & v14 & v15 & v16 & v17 & Q248 & U16 & Hkp22 & Hkp0 & B14 & B15 & B16 & B17 &
                      Rv14 & Rv15 & Rv16 & Rv17 & S14 & S15 & S16 & S17 & Ef16 & Ek)).
    unfold ACtlCutP.flen in Hfl50.
    pose proof BL as (BL0 & BL1 & _). pose proof BL2 as (BL20 & BL21 & _).
    assert (Ekp : kp = fr + 176) by (apply (w4d_q64_eq m (A + 280)); [exact Q280 | exact Q280' | lia | lia]).
    assert (EL : L = fr + 186) by (apply (w4d_q64_eq m (A + 112)); [exact QL | exact Q112' | lia | lia]).
    assert (EL2 : L2 = fr + 180) by (apply (w4d_q64_eq m (A + 96)); [exact QL2 | exact Q96' | lia | lia]).
    subst kp L L2.
    destruct (HPHI ltac:(unfold ACtlCutP.flen; lia)) as (_ & HPsp).
    rewrite Hspz in HPsp, HLsp, HL2sp, Hkpsp.
    pose proof (B.Prog.Seg.F17b.f17_bsl_len_le (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 18 32) as Lb1.
    pose proof (B.Prog.Seg.F17b.f17_bsl_len_le (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 34 6) as Lb2.
    change (Z.to_nat 32) with 32%nat in Lb1. change (Z.to_nat 6) with 6%nat in Lb2.
    split; [exact (Hw1 Ht)|].
    split.
    - (* rec_inv at the exit memory *)
      unfold ACtlCutP.rec_inv.
      split; [exact Hphi0'|]. split; [exact Hphi50|]. split; [unfold ACtlCutP.flen; exact Hfl50|].
      split; [exact Htk|]. split; [exact Happphi|].
      split; [w4d_carry m m' KS Q312|].
      split; [apply (w4d_bytes_keep m m'); [intros i Hi; unfold B.Prog.SlotModel.t_blk in Hi; apply KB; lia
                                            | exact Hblk]|].
      split; [apply (w4d_bytes_keep m m'); [intros i Hi; apply KB; lia | exact Hbsl]|].
      exists f16, v14, v15, v16, v17.
      split; [w4d_carry m m' KS Q248|].
      split; [unfold ACtlCutP.u16 in *; apply (w4d_bytes_keep m m');
              [intros i Hi; unfold lib.Lib.Mem.le2 in Hi;
               rewrite LinuxProcessSemantics.LinuxProcessSem.BvBase.length_Z_to_le_bytes in Hi; apply KF; lia
              | exact U16]|].
      split; [exact Hkp22|]. split; [exact Hkp0|].
      split; [w4d_carry m m' KB B14|]. split; [w4d_carry m m' KB B15|].
      split; [w4d_carry m m' KB B16|]. split; [w4d_carry m m' KB B17|].
      split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
      split; [w4d_sb m m' KBS S14|]. split; [w4d_sb m m' KBS S15|].
      split; [w4d_sb m m' KBS S16|]. split; [w4d_sb m m' KBS S17|].
      split; [exact Ef16 | exact Ek].
    - exists (fr + 186), (fr + 180), (firstn 6 ls), (firstn 6 rs), (firstn 6 ls2), (firstn 6 rs2).
      assert (Hpa : B.AsanRT.addressable m' phi (B.ACtlK.a_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)))
        by exact (proj2 HB').
      rewrite HspZ'.
      split; [w4d_carry m m' KS Q112'|]. split; [lia|].
      split; [apply (w4d_bytes_keep m m');
              [intros i Hi; rewrite length_firstn in Hi; apply KF; lia | apply w4d_ba_firstn; [exact BL | lia]]|].
      split; [rewrite length_firstn; lia|].
      split; [apply (w4d_bytes_keep m m');
              [intros i Hi; rewrite length_firstn in Hi; apply KB; lia | apply w4d_ba_firstn; [exact BR | lia]]|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite B.Prog.Seg.F17b.f17_memcmp_firstn; exact Hcmp|].
      split; [w4d_carry_ad m m' KFS AL|].
      split; [pose proof (B.AsanRTFacts.addressable_sub m' phi _ 0 6 Hpa ltac:(lia) ltac:(lia)
                            ltac:(unfold B.ACtlK.a_size; lia)) as Hs; rewrite Z.add_0_r in Hs; exact Hs|].
      split; [exact AL6|]. split; [exact AL7|].
      split; [apply Happphi; lia|]. split; [apply Happphi; lia|].
      split; [exact HLsp|].
      split; [unfold ACtlCutP.BWA.BCMP_WRAP_K in *; lia|].
      split; [exact HPsp|].
      split; [exact Hkpsp|].
      split; [w4d_carry m m' KS Q96'|]. split; [lia|].
      split; [apply (w4d_bytes_keep m m');
              [intros i Hi; rewrite length_firstn in Hi; apply KF; lia | apply w4d_ba_firstn; [exact BL2 | lia]]|].
      split; [rewrite length_firstn; lia|].
      split; [apply (w4d_bytes_keep m m');
              [intros i Hi; rewrite length_firstn in Hi; apply KB; lia | apply w4d_ba_firstn; [exact BR2 | lia]]|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite B.Prog.Seg.F17b.f17_memcmp_firstn; exact Hcmp2|].
      split; [w4d_carry_ad m m' KFS AL2|].
      split; [exact (B.AsanRTFacts.addressable_sub m' phi _ 6 6 Hpa ltac:(lia) ltac:(lia)
                       ltac:(unfold B.ACtlK.a_size; lia))|].
      split; [exact AL26|]. split; [exact AL27|].
      split; [apply Happphi; lia|]. split; [apply Happphi; lia|].
      split; [exact HL2sp|].
      unfold ACtlCutP.BWA.BCMP_WRAP_K in *; lia. }
  split.
  { (* FTURN *)
    destruct HFTURN as (S224 & S232 & Hphib & Hplen).
    split; [w4d_sp regs regs' m m' A R9 E9 KS|]. split; [w4d_sp regs regs' m m' A R9 E9 KS|].
    split; [|exact Hplen].
    apply (w4d_bytes_keep m m'); [intros i Hi; apply KB; lia | exact Hphib]. }
  { (* IFS (S j): turn S j's records (the entry's RECS) and its first-fragment state *)
    unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.FGj, ACtlCutP.IDb, ACtlCutP.FGb.
    unfold ACtlCutP.RECS, ACtlCutP.FREC, ACtlCutP.IDb, ACtlCutP.FGb in HRECS.
    destruct HRECS as ((HID & HIDok) & (HFG & HFGok)).
    split; [split; [|exact HIDok] | split; [split; [|exact HFGok] | exact HFS]].
    - unfold ACtlCutP.IDBe in *. pose proof (B.Prog.Seg.F17b.f18_ID_length (ACtlCut.c_in cx) (S j)) as LI.
      apply (w4d_bytes_keep m m'); [intros i Hi; rewrite LI in Hi; apply KF; lia | exact HID].
    - unfold ACtlCutP.FGBe in *. pose proof (B.Prog.Seg.F17b.f18_FG_length (ACtlCut.c_in cx) (S j)) as LF.
      apply (w4d_bytes_keep m m'); [intros i Hi; rewrite LF in Hi; apply KF; lia | exact HFG]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82468_at j (0x82468) --S_F17b--> B82634_at j. *)
Lemma seg_F17b : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82634_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82468_at [Z.of_nat j]).
Proof.
  intros POST j H34 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBase HJ HF HL Hk Hbody HRT.
  destruct Hbody as [Hidx Hb]. subst idx.
  pose proof Hb as Hb0.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82468_at ACtlCutP.fcutp_body ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & R18 & R20 & HFTURN & HLK & HFM & HFSj & HLONG & R27 &
    (A & kp & R9 & Q280 & Happ & HW272 & R24 & Hkpfr & Hkpsp & HPHI & H8819) & HRECS & HFS9).
  unfold ACtlCutP.flen in *.
  destruct HFRAC as (A' & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9' & R3 & R19 & R26 & Hfr32 & HA32 & HAsp & HspA &
    HfrA & HA448 & Hsp4096 & HspApp & _).
  unfold ACtlCutP.FRAME_BYTES, B.AsanRT.APPMEM_END in HfrA, HspApp.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as Hsp0.
  change (bv_unsigned (lib.Reusable.YK11.getr regs3 2)) with (Reusable.YG0d.spZ regs3) in Hsp0.
  rewrite Hspz in Hsp0. unfold bv_modulus in Hsp0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hsp0.
  assert (EA : A = A').
  { pose proof (w4d_q64_bounds _ _ _ Q280) as HQ.
    apply w4d_bv_eq; [unfold ACtlCut.rgv in R9, R9'; rewrite <- R9, <- R9'; reflexivity | lia | lia]. }
  subst A'.
  destruct HLK as (Hj' & S240 & HOUR & HFLI).
  pose proof HFLI as (_ & S168 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & HSTK0 & _ & (_ & HKN0) & _ & S88).
  destruct HFM as (S184 & R24' & R22 & R25 & S312).
  destruct HFSj as (FU0 & FB0 & FBody0 & FAd0 & FFI0).
  (* ---- the journal, the frame and the layout ---- *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKp & Hastk & _ & _).
  assert (EF3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF.
    reflexivity. }
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & HFB & HFS).
  rewrite EF3, FB6 in HFB, HFS.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & HfC & _).
  rewrite EF3 in Hf4096. rewrite EF3, FB6 in HfC.
  assert (Himg : 0x5fe000 <= fr).
  { pose proof HAR as (HM & HLd & _).
    pose proof (Reusable.YG0t.hull_below_F ly3 (Reusable.YG0n.am_layout _ _ _ _ HM)) as HH.
    assert (Hlast : In (0xa2000, 0x55c000)
                      (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
    { rewrite B.ProgBridge.tfibsegs_rsegs, B.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
    apply in_map_iff in Hlast as (sg & Esg & Hsg).
    destruct (Reusable.YG0n.al_img _ _ _ _ HLd sg Hsg) as (_ & HC).
    injection Esg as E1 E2. rewrite E1, E2 in HC.
    pose proof (Reusable.YG0s.frame_facts B ly3 S3 _ 6 (ACtlCut.c_fpos cx) HM Hin6) as (_ & _ & _ & _ & _ & Hoff & _).
    rewrite <- EF3. unfold Reusable.YG0f.frame_addr. unfold Reusable.YG0f.kFakeFramesOff in Hoff. lia. }
  pose proof Hastk as (Hsp016 & _ & HCceil & Hslo & _).
  assert (ESTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite ESTK in Hslo, HSTKp.
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & _).
  pose proof (@Reusable.YCbq.asan_consts rc) as (HCe & _).
  assert (HCsp : lib.Reusable.YM05.alloc_ceiling <= Reusable.YG0d.spZ regs3 - Reusable.YG0d.ESTACK).
  { rewrite Hspz. unfold Reusable.YG0d.ESTACK. lia. }
  (* the live blocks: apart from the frame, below the stack window *)
  assert (HBF : forall p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p mod 8 = 0 /\
             (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p) /\
             p + Reusable.YG00.req_size n <= lib.Reusable.YM05.alloc_ceiling).
  { intros p n Hpn.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn) as (Hp16 & _ & HpC & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hpn Hin6)
      as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, FB6 in Hd.
    split; [lia|]. split; [lia | exact HpC]. }
  assert (Hinb : In (phi, B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (HBF _ _ Hinb) as (Hphi8 & Hphifr & HphiC).
  pose proof (w4d_tlen_nn (ACtlCut.c_in cx) j) as Hlen0.
  destruct HHB as (Hphinz & HphiA).
  pose proof HphiA as (Hphi0 & _ & HphiE & _).
  (* ---- the visible bytes of W3 ---- *)
  set (V3 := fun a : Z => Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  assert (HVs : forall a, ACtlCut.c_sp cx - Reusable.YG0d.ESTACK <= a < ACtlCut.c_sp cx -> V3 a).
  { intros a Ha. unfold Reusable.YG0d.ESTACK in Ha. exact (proj1 (HSTKp a ltac:(lia))). }
  assert (HVf : forall a, fr <= a < fr + 4096 -> V3 a).
  { intros a Ha. exact (proj1 (proj1 (HFB a Ha))). }
  assert (HVfs : forall i, 0 <= i < 512 -> V3 (B.AsanRT.shadow_addr fr + i)).
  { intros i Hi. destruct (HFS i ltac:(lia)) as ((Hv & _) & _). unfold V3.
    replace (B.AsanRT.shadow_addr fr + i) with (Reusable.YG0f.shadow_addr fr + i)
      by (unfold B.AsanRT.shadow_addr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia).
    exact Hv. }
  assert (HVb : forall p n a, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
             p <= a < p + Reusable.YG00.req_size n -> V3 a).
  { intros p n a Hpn Ha.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn) as (_ & _ & _ & _ & Hb & _).
    exact (proj1 (proj1 (Hb a Ha))). }
  assert (HVbs : forall p n i, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
             0 <= i < (Reusable.YG00.req_size n + 7) / 8 -> V3 (B.AsanRT.shadow_addr p + i)).
  { intros p n i Hpn Hi.
    destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn) as ((_ & _ & Hsh) & _).
    pose proof (Hsh i Hi) as Hs. unfold Reusable.YG0v.shadow_of_addr in Hs.
    apply (w4d_vis_of_aview W3 mem3).
    replace (B.AsanRT.shadow_addr p + i) with (Reusable.YG0f.SHADOW_OFF + p / 8 + i)
      by (unfold B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia).
    rewrite Hs. discriminate. }
  assert (HVi : forall a, 0x10000 <= a < 0x5fe000 -> V3 a).
  { intros a Ha. destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hv).
    apply Hv. unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI. lia. }
  (* ---- the run: F17bF.seg_F17b_pre_F, at a 50-byte record whose block-sum test is t_sum_ok j ---- *)
  set (len := B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) in *.
  set (gg := if 50 <=? len then B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j else repeat (Z_to_bv 8 1) 50).
  assert (Hgl : length gg = 50%nat).
  { unfold gg. destruct (50 <=? len); [apply B.Prog.Seg.F17b.f17_g_length | reflexivity]. }
  assert (Hss : (Prog.RcModel.blocksum (skipn 18 gg) =? 0) = B.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j).
  { unfold gg, B.Prog.SlotModel.t_sum_ok, B.Prog.SlotModel.t_big. fold len.
    destruct (50 <=? len); cbv iota;
      [rewrite Bool.andb_true_l; reflexivity | rewrite Bool.andb_false_l; vm_compute; reflexivity]. }
  pose proof (w4d_spq _ _ _ _ _ HFS9 R9 ltac:(lia) ltac:(lia)) as Q248.
  rewrite <- Hss in Q248.
  pose proof (w4d_spq _ _ _ _ _ S168 R9 ltac:(lia) ltac:(lia)) as Q168.
  pose proof (w4d_spq _ _ _ _ _ S88 R9 ltac:(lia) ltac:(lia)) as Q88.
  assert (HLONG' : 50 <= len -> 0 < phi /\ phi + 50 <= B.AsanRT.APPMEM_END /\
     (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\ lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 phi gg /\
     B.AsanRT.addressable mem3 phi 50 /\ ACtlCutP.q64 mem3 (A + 312) (phi + 18)).
  { intros H50. destruct (HLONG H50) as (Had50 & _). pose proof Had50 as (_ & _ & Had50E & _).
    destruct (HPHI H50) as (Hpfr & _).
    assert (Egg : gg = B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)
      by (unfold gg; replace (50 <=? len) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    rewrite Egg.
    split; [lia|]. split; [exact Had50E|]. split; [exact Hpfr|].
    split; [apply B.Prog.SlotInv.t_g_of_phi; [exact (proj1 (proj2 (proj2 HFTURN))) | exact H50]|].
    split; [exact Had50|].
    pose proof (w4d_spq _ _ _ _ _ S312 R9 ltac:(lia) ltac:(lia)) as Q312.
    unfold B.Prog.SlotModel.t_big in Q312. fold len in Q312.
    replace (50 <=? len) with true in Q312 by (symmetry; apply Z.leb_le; lia). exact Q312. }
  assert (HWR : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (fr + 2880) 40).
  { destruct HSTK0 as (_ & _ & Hst). split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (Hst (fr + 2880 + i) ltac:(unfold ACtlCutP.FRAME_BYTES; lia))). }
  assert (Hrv : forall lo n, lo <= lo + n -> (forall a, lo <= a < lo + n -> V3 a) -> 0 <= lo -> lo + n <= 2 ^ 64 ->
            lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo n).
  { intros lo n _ Hv H0 H1. apply B.ProgBridge.rng_of_visible. split; [exact H0|]. split; [exact H1|].
    intros a Ha. exact (Hv a Ha). }
  pose proof (F17bF.seg_F17b_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3
                lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 A phi fr len gg
                (Prog.RcModel.blocksum (skipn 18 gg) =? 0)
                R9 R18 R20 R22 R26 R27
                ltac:(unfold B.AsanRT.APPMEM_END; lia) ltac:(unfold B.AsanRT.APPMEM_END, B.ACtlK.a_size in *; lia)
                ltac:(rewrite w4d_gt_img_top; lia) ltac:(unfold B.AsanRT.APPMEM_END; lia)
                ltac:(unfold B.Prog.SlotInv.FRAME_BYTES; lia)
                eq_refl Q248 Hgl HLONG' Q168 Q88 HWR Happ
                (Hrv (A + 248) 8 ltac:(lia) ltac:(intros a Ha; apply HVs; unfold Reusable.YG0d.ESTACK; lia)
                   ltac:(lia) ltac:(lia))
                (Hrv (A + 312) 8 ltac:(lia) ltac:(intros a Ha; apply HVs; unfold Reusable.YG0d.ESTACK; lia)
                   ltac:(lia) ltac:(lia))
                (Hrv (A + 168) 8 ltac:(lia) ltac:(intros a Ha; apply HVs; unfold Reusable.YG0d.ESTACK; lia)
                   ltac:(lia) ltac:(lia))
                (Hrv (A + 88) 8 ltac:(lia) ltac:(intros a Ha; apply HVs; unfold Reusable.YG0d.ESTACK; lia)
                   ltac:(lia) ltac:(lia))) as HRUN0.
  assert (HRNGL : 50 <= len ->
     lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (phi + 16) 11 /\
     lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
       (Z.shiftr (phi + 16) 3 + B.AsanRT.ASAN_K) (Z.shiftr (phi + 26) 3 - Z.shiftr (phi + 16) 3 + 1)).
  { intros H50.
    assert (Hrq : Reusable.YG00.req_size len = len)
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec len 0); lia).
    pose proof HphiC as HphiC'. rewrite Hrq in HphiC'.
    split.
    - apply Hrv; [lia | | lia | lia]. intros a Ha. apply (HVb _ _ a Hinb). rewrite Hrq. lia.
    - rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      apply Hrv; [lia | | unfold B.AsanRT.ASAN_K; lia | unfold B.AsanRT.ASAN_K; lia].
      intros a Ha. replace a with (B.AsanRT.shadow_addr phi + (a - B.AsanRT.shadow_addr phi)) by ring.
      apply (HVbs _ _ _ Hinb). rewrite Hrq.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
  pose proof (HRUN0 HRNGL
                (Hrv (fr + 2880) 5 ltac:(lia) ltac:(intros a Ha; apply HVf; lia) ltac:(lia) ltac:(lia))) as HRUN.
  clear HRUN0.
  (* ---- the lift (G3, G4) ---- *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_B82468_at [Z.of_nat j])) with 0x82468.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82468) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  pose proof (B.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS0.
  rewrite <- B.ProgBridge.tfibsegs_rsegs in HFS0.
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
           HFS0 (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' HQ Hhid Hsbm.  destruct HQ as (R & m' & HARM & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K22 & K24 & K25 & K26 & K27).
  assert (K2' : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact K2.
  assert (K3' : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact K3.
  assert (K4' : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact K4.
  assert (K8' : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact K8.
  assert (K9' : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
  assert (K18' : lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18) by exact K18.
  assert (K19' : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact K19.
  assert (K20' : lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20) by exact K20.
  assert (K22' : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by exact K22.
  assert (K24' : lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24) by exact K24.
  assert (K25' : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by exact K25.
  assert (K26' : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact K26.
  assert (K27' : lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27) by exact K27.
  clear K2 K3 K4 K8 K9 K18 K19 K20 K22 K24 K25 K26 K27.
  destruct HARM as [(Ems & Em & Hop) | (Ems & Hop & R1 & R10 & R11 & R12 & Hmid)]; subst ms'.
  - (* ===== ARM 1: a failed test (or the guard): 0x82634 with the memory unchanged ===== *)
    subst m'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_B82634_at [Z.of_nat j])) R mem3 md') (POST cx)).
    assert (Hop' : B.Prog.SlotModel.f_opens len (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = false).
    { destruct (Z.leb_spec 50 len) as [H50 | H50].
      - unfold gg in Hop. replace (50 <=? len) with true in Hop by (symmetry; apply Z.leb_le; lia). exact Hop.
      - apply B.Prog.Seg.F17b.f17_fopens_false. left. apply Z.leb_gt. exact H50. }
    apply (H34 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HBase).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS w4d_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbn [ACtlCut.cut_body ACtlCut.ix_cut]. split; [reflexivity|].
      apply (w4d_exit_body (fun _ => True) lib.Reusable.YM05.alloc_ceiling cx j _ fr regs3 R mem3 mem3 Hb0
               K2' K3' K4' K8' K9' K18' K19' K20' K22' K24' K25' K26' K27');
        try (intros; exact I); try (intros; reflexivity).
      * exact HBF.
      * exact Himg.
      * exact HfC.
      * exact HCsp.
      * exact HCe.
      * exact HSTK0.
      * exact HKN0.
      * apply (w4d_fsj_false cx fr j regs3 R mem3 Hop').
        exact (conj FU0 (conj FB0 (conj FBody0 (conj FAd0 FFI0)))).
    + exact HRT.
  - (* ===== ARM 2: every test passed (f_opens): the stores of `first`, then __asan_memcpy ===== *)
    destruct (Z.leb_spec 50 len) as [H50 | H50];
      [| exfalso; rewrite B.Prog.Seg.F17b.f17_fopens_false in Hop;
         [discriminate | left; apply Z.leb_gt; exact H50]].
    assert (Egg : gg = B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)
      by (unfold gg; replace (50 <=? len) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    rewrite Egg in Hop, R12, Hmid.
    destruct HLONG' as (_ & _ & Hpfr & Hgg & Had50 & _); [exact H50|]. rewrite Egg in Hgg.
    destruct (HPHI H50) as (_ & HPsp). rewrite Hspz in HPsp.
    pose proof Had50 as (HphiB0 & _ & HphiB1 & _). unfold B.AsanRT.APPMEM_END in HphiB1.
    set (g := B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) in *.
    set (n := Prog.RcFrag.bat g 26) in *.
    assert (Lg : length g = 50%nat) by exact (B.Prog.Seg.F17b.f17_g_length (ACtlCut.c_in cx) j).
    assert (Hn26 : 1 <= n <= 22).
    { unfold B.Prog.SlotModel.f_opens in Hop. apply andb_prop in Hop as (Hfr' & _).
      exact (B.Prog.Seg.F17b.f18_fg_n _ _ Hfr'). }
    destruct Hmid as (MU1 & WM1 & U1 & B1).
    set (src := firstn (Z.to_nat n) (skipn 27 g)).
    assert (Lsrc : Z.of_nat (length src) = n).
    { unfold src. rewrite length_firstn, length_skipn, Lg. lia. }
    (* the memory after the two stores of `first`, outside [fr + 2880, fr + 2885) *)
    assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (fr + 2880 <= a < fr + 2885) ->
              lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
    { intros a Ha Hna. unfold lib.Lib.Mem.mrd. rewrite (MU1 (lib.Lib.Mem.wa a)); [reflexivity|].
      rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
    assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                    (ACtlCut.cut_own C_B82468_at cx) ly3 S3 W3 m' md' k).
    { apply (Reusable.YCbq.ajournal_exec segs B LAWS w4d_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (fun a => fr + 2880 <= a < fr + 2885) HJ).
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1 x); [reflexivity|].
        cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
      - intros x Hx. unfold Reusable.YK04.mrestrict in *.
        destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx|].
        pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
        change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
        destruct (Z_lt_le_dec (bv_unsigned x) (fr + 2880)) as [Lx | Lx];
          [rewrite (MU1 x) by (cbn [lib.Lib.Frame.outside]; split; [lia | exact I]); exact Hx |].
        destruct (Z_lt_le_dec (bv_unsigned x) (fr + 2885)) as [Lx2 | Lx2];
          [| rewrite (MU1 x) by (cbn [lib.Lib.Frame.outside]; split; [lia | exact I]); exact Hx].
        replace x with (lib.Lib.Mem.wa (bv_unsigned x)) by (unfold lib.Lib.Mem.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
        apply w4d_mrd_some; [lia|].
        destruct (Z_lt_le_dec (bv_unsigned x) (fr + 2884)) as [Lx3 | Lx3].
        + replace (bv_unsigned x) with (fr + 2880 + (bv_unsigned x - (fr + 2880))) by ring.
          apply (w4d_ba_some m' (fr + 2880) _ _ U1).
          match goal with |- 0 <= _ < Z.of_nat (length ?l) => assert (Z.of_nat (length l) = 4) by (vm_compute; reflexivity) end; lia.
        + replace (bv_unsigned x) with (fr + 2884 + 0) by lia.
          apply (w4d_ba_some m' (fr + 2884) _ _ B1). cbn [length]. lia.
      - intros x Hx. exact (Hhid x Hx).
      - exact Hsbm.
      - intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF3, FB6. lia. }
    (* ---- the call: __asan_memcpy through the core's journal-form rule aj_intrin_at, with AMEMCPY ---- *)
    assert (HappLH : fr + 2920 <= 0x7fff8000 \/ 0x10007fff8000 <= fr + 2880).
    { pose proof (Happ (fr + 2880) ltac:(lia)) as H1. pose proof (Happ (fr + 2919) ltac:(lia)) as H2.
      unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG in H1, H2. lia. }
    assert (HphiLH : phi + 50 <= 0x7fff8000 \/ 0x10007fff8000 <= phi).
    { pose proof Had50 as (_ & _ & _ & Hab).
      destruct (Hab 0 ltac:(lia)) as (H1 & _). destruct (Hab 49 ltac:(lia)) as (H2 & _).
      unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG in H1, H2. lia. }
    assert (HspNW : forall y, 0 <= y < 0x800000000000 ->
              ~ (fr + 2880 <= B.AsanRT.shadow_addr y < fr + 2920)).
    { intros y Hy. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. lia. }
    assert (Hsp' : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite K2'; exact Hspz).
    pose proof HBase as ((Hafn & _) & _). pose proof Hafn as (_ & _ & _ & Hgp & _).
    (* the bytes the call reads, at the memory after the two stores *)
    assert (FAd1 : B.AsanRT.addressable m' (fr + 2880) 40).
    { apply (w4d_addr_keep mem3 m'); [|exact FAd0]. intros i Hi.
      apply KM1; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia|].
      pose proof (HspNW (fr + 2880 + i) ltac:(lia)). lia. }
    assert (Had1 : B.AsanRT.addressable m' phi 50).
    { apply (w4d_addr_keep mem3 m'); [|exact Had50]. intros i Hi.
      apply KM1; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia|].
      pose proof (HspNW (phi + i) ltac:(lia)). lia. }
    assert (Hgg1 : lib.Lib.Mem.bytes_at segs m' phi g).
    { apply (w4d_bytes_keep mem3 m'); [|exact Hgg]. intros i Hi.
      rewrite Lg in Hi. apply KM1; lia. }
    assert (Hsrc : lib.Lib.Mem.bytes_at segs m' (phi + 27) src).
    { pose proof (w4d_ba_sub m' phi g 27 (Z.to_nat n) Hgg1
                    ltac:(rewrite Lg; lia)) as H.
      replace (phi + Z.of_nat 27) with (phi + 27) in H by reflexivity. exact H. }
    change (Reusable.YA0n.SRr segs W3
              {| cfg_ms := lib.Reusable.YK11.mkst R (Z_to_bv 64 Reusable.YB1w.tfib_A_asan_memcpy) m'
                           (lib.Reusable.YK11.seg_rom segs); cfg_model := md' |} (POST cx)).
    eapply Reusable.YA0n.SRr_bind.
    { apply (Reusable.YCbq.aj_intrin_at segs B LAWS w4d_segs_low Reusable.YG0d.OCpy
               Reusable.YB1w.tfib_A_asan_memcpy AMEMCPY W3 R m' Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
               (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
               (ACtlCut.cut_own C_B82468_at cx) ly3 S3 md' k (fr + 2885) (phi + 27) n
               (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82634) HJ1).
      - exact R10.
      - exact R11.
      - exact R12.
      - lia.
      - lia.
      - lia.
      - rewrite Hsp'. ring.
      - lia.
      - lia.
      - unfold Reusable.YG0d.ESTACK. rewrite ESTK. lia.
      - rewrite K3', R3. exact Hgp.
      - rewrite K4'. exact R4.
      - exact R1.
      - unfold lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
      - intros a Ha. split.
        + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF3, FB6. lia.
        + replace (ACtlCut.c_sp cx + (sp - ACtlCut.c_sp cx)) with sp by ring.
          unfold Reusable.YG0d.ESTACK. lia.
      - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
          Reusable.YG0f.kHighMemEnd. lia.
      - apply w4d_range_addr.
        + intros i Hi. replace (fr + 2885 + i) with (fr + (2885 + i)) by ring.
          rewrite (w4d_sh_add fr (2885 + i)) by lia. apply HVfs. lia.
        + pose proof (B.AsanRTFacts.addressable_sub m' (fr + 2880) 40 5 n FAd1 ltac:(lia) ltac:(lia) ltac:(lia)) as H.
          replace (fr + 2880 + 5) with (fr + 2885) in H by ring. exact H.
      - intros _ s Hs.
        assert (Hsi : 0 <= s - Reusable.YG0f.shadow_addr fr < 512).
        { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia. }
        destruct (HFS (s - Reusable.YG0f.shadow_addr fr) ltac:(lia)) as (Hp & _).
        replace (Reusable.YG0f.shadow_addr fr + (s - Reusable.YG0f.shadow_addr fr)) with s in Hp by ring.
        rewrite (w4d_aview_munch _ _ mem3 m' s MU1).
        + exact (Reusable.YCbq.aview_some_of_apresent segs _ mem3 s Hp).
        + unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia.
        + cbn [lib.Lib.Frame.outside]. split; [|exact I].
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia.
      - cbv iota.
        destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi len HAR Hinb) as (_ & _ & _ & _ & Hbp & _).
        assert (Hrqlen : Reusable.YG00.req_size len = len).
        { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec len 0); lia. }
        rewrite Hrqlen in Hbp, HphiC.
        split; [lia|]. split; [lia|].
        split.
        { intros a Ha. split.
          - rewrite (w4d_aview_munch _ _ mem3 m' a MU1); [ | lia | cbn [lib.Lib.Frame.outside]; split; [lia | exact I]].
            exact (Reusable.YCbq.aview_some_of_apresent segs _ mem3 a (proj1 (Hbp a ltac:(lia)))).
          - rewrite Hsp'. unfold Reusable.YG0d.ESTACK. lia. }
        split; [lia|].
        split; [unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
                  Reusable.YG0f.kHighMemEnd; lia|].
        split.
        { apply w4d_range_addr.
          - intros i Hi. replace (phi + 27 + i) with (phi + (27 + i)) by ring.
            rewrite (w4d_sh_add phi (27 + i)) by lia. apply (HVbs _ _ _ Hinb). rewrite Hrqlen. lia.
          - pose proof (B.AsanRTFacts.addressable_sub m' phi 50 27 n Had1 ltac:(lia) ltac:(lia) ltac:(lia)) as H.
            exact H. }
        intros Hn0 s Hs.
        pose proof (Reusable.YCbq.shadow_hull_vis_of_block segs B LAWS ly3 S3 W3 mem3 md3 phi len (phi + 27) n
                      HAR Hinb ltac:(lia) ltac:(rewrite Hrqlen; lia) Hn0 s Hs) as Hv.
        rewrite (w4d_aview_munch _ _ mem3 m' s MU1); [exact Hv | |].
        + unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia.
        + cbn [lib.Lib.Frame.outside]. split; [|exact I].
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia. }
    intros W2 c2 _ (EW2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & R10' & Hcopy & Hframe & Hpresent).
    subst W2 c2.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_B82634_at [Z.of_nat j])) regs2 mem2 md2) (POST cx)).
    replace (ACtlCut.c_sp cx + (sp - ACtlCut.c_sp cx)) with sp in Hframe by ring.
    (* the memcpy's world-form post over raw memory (the shared ctl_post_memcpy) *)
    assert (HapD : forall a, fr + 2885 <= a < fr + 2885 + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) m' a).
    { intros a Ha. destruct (proj1 (HFB a ltac:(lia))) as (Hv & b & Hb). split; [exact Hv|].
      exists b. rewrite (MU1 (Z_to_bv 64 a)); [exact Hb|].
      rewrite lib.Lib.MState.unsigned_lit by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
    destruct (B.ProgWorld.ctl_post_memcpy W3 m' mem2 sp (fr + 2885) (phi + 27) n src
                ltac:(lia) ltac:(lia) ltac:(lia) Lsrc HapD Hsrc
                (fun i Hi => HVb _ _ (phi + 27 + i) Hinb ltac:(unfold Reusable.YG00.req_size; destruct (Z.eqb_spec len 0); lia))
                Hcopy
                (conj (fun a Ha Hout => Hframe a Ha (proj1 Hout) (proj1 (proj2 Hout))) Hpresent))
      as (Hmv & Hwv & Hrw).
    assert (Hbs : lib.Lib.Mem.bytes_at segs mem2 (fr + 2885) src).
    { destruct Hrw as ((_ & Hcb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hcb.
      rewrite app_nil_r in Hcb. exact Hcb. }
    assert (Kmv : forall a, 0 <= a < 2 ^ 64 -> V3 a -> ~ (fr + 2885 <= a < fr + 2885 + n) -> ~ (sp - 4096 <= a < sp) ->
              lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a)).
    { intros a Ha HVa Hn1 Hn2. apply (Hmv (lib.Lib.Mem.wa a) HVa).
      rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside]. unfold Reusable.YG0d.ESTACK.
      split; [lia|]. split; [lia | exact I]. }
    assert (Kall : forall a, 0 <= a < 2 ^ 64 -> V3 a -> ~ (fr + 2880 <= a < fr + 2920) ->
              ~ (Reusable.YG0d.spZ regs3 - Reusable.YG0d.ESTACK <= a < Reusable.YG0d.spZ regs3) ->
              lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
    { intros a Ha HVa Hn1 Hn2. rewrite Hspz in Hn2. unfold Reusable.YG0d.ESTACK in Hn2.
      rewrite (Kmv a Ha HVa ltac:(lia) ltac:(lia)). apply KM1; lia. }
    (* the frame's stk after the stores and the copy *)
    assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
    { pose proof HSTK0 as (Hs0 & Hs1 & Hst). split; [exact Hs0|]. split; [exact Hs1|].
      intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
      split.
      - apply (Hwv (lib.Lib.Mem.wa a)); [apply HVf; lia|].
        apply WM1. exact (proj1 (Hst a ltac:(unfold ACtlCutP.FRAME_BYTES; lia))).
      - destruct (lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso].
        destruct (Z_lt_le_dec a (fr + 2885)) as [L1 | L1].
        + destruct (Z_lt_le_dec a (fr + 2880)) as [L0 | L0].
          * rewrite (Kall a ltac:(lia) ltac:(apply HVf; lia) ltac:(lia) ltac:(rewrite Hspz; unfold Reusable.YG0d.ESTACK; lia)) in Eb.
            destruct (proj2 (Hst a ltac:(unfold ACtlCutP.FRAME_BYTES; lia))) as (b0 & Hbb0).
            rewrite Hbb0 in Eb. discriminate.
          * rewrite (Kmv a ltac:(lia) ltac:(apply HVf; lia) ltac:(lia) ltac:(lia)) in Eb.
            destruct (Z_lt_le_dec a (fr + 2884)) as [L2 | L2].
            -- replace a with (fr + 2880 + (a - (fr + 2880))) in Eb by ring.
               exact (w4d_ba_some m' (fr + 2880) _ (a - (fr + 2880)) U1 ltac:(match goal with |- 0 <= _ < Z.of_nat (length ?l) => assert (Z.of_nat (length l) = 4) by (vm_compute; reflexivity) end; lia) Eb).
            -- replace a with (fr + 2884 + 0) in Eb by lia.
               exact (w4d_ba_some m' (fr + 2884) _ 0 B1 ltac:(cbn [length]; lia) Eb).
        + destruct (Z_lt_le_dec a (fr + 2885 + n)) as [L2 | L2].
          * replace a with (fr + 2885 + (a - (fr + 2885))) in Eb by ring.
            exact (w4d_ba_some mem2 (fr + 2885) _ (a - (fr + 2885)) Hbs ltac:(lia) Eb).
          * rewrite (Kmv a ltac:(lia) ltac:(apply HVf; lia) ltac:(lia) ltac:(lia)) in Eb.
            rewrite (KM1 a ltac:(lia) ltac:(lia)) in Eb.
            destruct (proj2 (Hst a ltac:(unfold ACtlCutP.FRAME_BYTES; lia))) as (b0 & Hbb0).
            rewrite Hbb0 in Eb. discriminate. }
    (* turn S j's first-fragment state at the exit memory *)
    assert (HFS2 : ACtlCutP.FSj cx fr (S j) regs2 mem2).
    { apply (w4d_fsj_true cx fr j regs2 mem2 Hop).
      - apply (w4d_bytes_keep m' mem2); [|exact U1]. intros i Hi.
        match type of Hi with _ <= _ < Z.of_nat (length ?l) => assert (Z.of_nat (length l) = 4) by (vm_compute; reflexivity) end.
        apply Kmv; [lia | apply HVf; lia | lia | lia].
      - apply (w4d_bytes_keep m' mem2); [|exact B1]. intros i Hi. cbn [length] in Hi.
        apply Kmv; [lia | apply HVf; lia | lia | lia].
      - exact Hbs.
      - apply (w4d_addr_keep mem3 mem2); [|exact FAd0]. intros i Hi.
        apply Kall; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia | | apply HspNW; lia
                    | rewrite Hspz; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0d.ESTACK; lia].
        replace (fr + 2880 + i) with (fr + (2880 + i)) by ring.
        rewrite (w4d_sh_add fr (2880 + i)) by lia. apply HVfs. lia. }
    assert (P2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (rewrite <- K2'; exact (Hpres 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (rewrite <- K3'; exact (Hpres 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (rewrite <- K4'; exact (Hpres 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (rewrite <- K8'; exact (Hpres 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (rewrite <- K9'; exact (Hpres 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
      by (rewrite <- K18'; exact (Hpres 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (rewrite <- K19'; exact (Hpres 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
      by (rewrite <- K20'; exact (Hpres 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (rewrite <- K22'; exact (Hpres 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
      by (rewrite <- K24'; exact (Hpres 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (rewrite <- K25'; exact (Hpres 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (rewrite <- K26'; exact (Hpres 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (rewrite <- K27'; exact (Hpres 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    apply (H34 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HBase HJ2 HF HL Hk).
    + cbn [ACtlCut.cut_body ACtlCut.ix_cut]. split; [reflexivity|].
      exact (w4d_exit_body V3 lib.Reusable.YM05.alloc_ceiling cx j _ fr regs3 regs2 mem3 mem2 Hb0
               P2 P3 P4 P8 P9 P18 P19 P20 P22 P24 P25 P26 P27 Kall HVs HVf HVfs HVb HVbs HVi HBF
               Himg HfC HCsp HCe HSTK2 (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) HFS2).
    + (* ctl_rt_C after the call (route (C)): B.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post journal's AR, with the
         read-only view kept from the entry's arodata_okS by APostBase.arodata_ok_journalP *)
      pose proof HBase as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
      exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem2 md2 (proj1 HJ2)
               (Reusable.APostBase.arodata_ok_journalP (SK := SK) (RO := RO_OFL) segs RLO RHI RELRO_IMG B
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2
                  (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS (Z.le_refl _) (Z.le_refl _)))).
Qed.

End W4d.

(* Stage lemma of this file (Qed), named and stated exactly as ACtl.v's Hypothesis seg_F17b (576147dfd46; frozen
   981c1faff75), generic in SK and FP:
     seg_F17b (B82468_at) : forall POST j, ctl_from POST (ix_cut C_B82634_at [Z.of_nat j]) ->
                            ctl_from POST (ix_cut C_B82468_at [Z.of_nat j])
   Trap obligations (branch -> 0x82fa0: refuting step), all with HB / LEN50 / FM / s11, never rec_inv:
     0x82478 (T29), 0x82480 (T30), 0x82488 (T31), 0x824b0 (T32), 0x824f8 (T33), 0x8251c (T34), 0x82540 (T35),
     0x82568 (T36), 0x82588 (T37), 0x825b0 (T38), 0x825d0 (T39) : seg_F17b step 1
     0x825f0 (T40), 0x82614 (NEW), 0x82620 (NEW)               : seg_F17b step 2
   No branch to 0x82fa4 in the stretch. *)

(* The stages of this file and their assumptions (gate checklist, a Theorem Labs lane 04:22Z). *)
Check w4d_gt_img_top.
Print Assumptions w4d_gt_img_top.
Check seg_F17b.
Print Assumptions seg_F17b.
