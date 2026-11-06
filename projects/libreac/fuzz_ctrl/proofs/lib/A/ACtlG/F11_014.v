(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v; 654 of its 695 lines of code are new or changed and 925 lines of the source are left out. *)
(* lib/A/ACtlG/F11_014.v -- GLUE for stage seg_F11_014 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:776).  Written by a Theorem Labs lane; single writer.  rule 24: no
   function proved (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery),
   worked example lib/A/ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_F11_014 : forall POST (j : nat),
       CF POST (ix_cut C_A820f8_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F11_014.  Segment F11_014 is 0x820ac -> 0x820f8 (Seg/F11.v:638-1351): the checks of the record bytes phi+36 /
   phi+37, the 16-bit compare against the reply cell at fr+256, and the call of reac_identity_ingest at 0x820f4, which
   writes its stack window [sp-32, sp) and the 38 identity bytes [fr+2688, fr+2726).

   NO LIFT IS CITED.  This stage cites no <f>_SRr_at and no <f>_SRr_at_hid: the segment's _F run covers the whole
   segment INCLUDING the call and discharges the callee's footprint contract itself, so the caller obligations are
   the run's own premises, paid below, and the whole run is lifted ONCE with Reusable.YA0nR.SRr_fevt_hid at
   RNG := A.ProgBridge.RNG_W (w_H W3).  ROUTE (C) (a working branch 1899bed1aee): the run is
   A.Prog.Seg.F11Fon.f11_014_evt_F_on, this lane's twin of a Theorem Labs lane's Seg/F11F.v f11_014_evt_F WITHOUT its
   `shadow_rw m` premise (Seg/F11F.v unchanged apart from comment text); it cuts the call through the narrowed
   reac_identity_ingestF.reac_identity_ingest_F_holds_on.  The cut now carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at index [Z.of_nat j]: ix_cut's index equation, then C_A820ac_at's body (ACtlCutP.v:2185-2199:
       FRAC and b5_body with its 13-conjunct tail).
   G2  the run's 38 premises, from the body and visible state only: registers from the body's rgv facts; the record
       block, the reply cell, the identity record, the payload and the placements from b5_C / b5_RPost / IDj; the
       callee's stack window [sp-32, sp) as a Lib.Frame.stk from the journal's presence conjunct (local lemma
       Hstk_of); asan_cells from ctl_rt_C (the run takes no shadow premise); the numeric bounds from FRAC, the journal's frame
       (frames_bounds + the frame law + layout_le's ly_F), the journal's astk_ok and the run ceiling; every footprint
       range from a Theorem Labs lane's visibility lemmas (heap_vis / heap_sh_vis, frame_vis, win_vis, img_vis_W), the shadow
       ranges through the local lemma sh_byte_vis (8-aligned word cover -> byte-exact range).
   G3  ProgBridge.cfg_at_MS, then the walk moved from regs3 to mkR_of regs3 (YA0nR.SRr_xregs_eqv), mkR_of expanded
       (mkR_expand) and the five slots the run pins (9 12 13 22 26) rewritten to their carried values.
   G4  the lift: f11_014_evt_F_on, ProgBridge.fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt_hid at RNG_W (w_H W3)
       (fp_avoids by ProgBridge.fp_avoids_RNG_W).
   G5  the run's end map R is the exit cut's map; the exit cut C_A820f8_at at the same cx, fr, k, ly3, S3, W3:
         journal  YCbq.ajournal_exec with Wr = the callee's two intervals: memory equal outside them (the run's munch),
                  mem_grows (a byte of the two intervals is in no segment, so its wview fact gives a memory byte),
                  the hidden bytes (SRr_fevt_hid), every written byte awr_byte (stack window / owned class-6 frame);
         frames, frame law, k bound   unchanged (own6, same kmax on both cuts);
         body     FRAC and every memory conjunct moved across the munch by Lib.Frame.bytes_at_transport (each range
                  shown apart from the two intervals: spill area, frame bytes, live heap blocks, shadow, image),
                  addressable by AsanRTFacts.addressable_kept / munch_meta, the frame stk by RcReplyLib.rc_stk_after;
                  the identity record is the run's rw_cells, = ID1 cx j because ir holds (SlotModel.rp_id), id_ok by
                  RcIdentLib.ING_id_ok; a0 = fst (ING ..) in {0, 1} (RcIdentModel.ING_ret).  This mirrors the source
                  segment proof Seg/F11.v:844-1350 over the cut's vocabulary;
         ctl_rt_C asan_cells (image bytes), the two shadow regions cut_shadow / img_shadow kept by
                  A.ShadowRwOnK.fl_shadow_rw_on (no shadow byte lies in the app-memory write; the state ly3 S3 is
                  the entry cut's), and ro_agree (a read-only byte is an image byte, outside the write).

   SECTION HYPOTHESES (exact text below)
   - LAWS : the core's AR law record (YCbq.v:207, ACtl.v:183), for ajournal_exec, frames_bounds, frm_img,
     sep_block_frame, al_blocks and the visibility lemmas.  ACtl.v discharges it in section 9.  No other.
   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied): Kit.kit_wx (SRr_fevt_hid's image
   premise) and Kit.kit_segs_low (ajournal_exec's image placement; also: a byte of the callee's stack window is no
   image byte).  Kit.kit_frac_move is NOT used: FRAC moves here across a memory write as well as a register change,
   so it is rebuilt directly at the exit (its register part by conversion, its memory part by the munch transport).
   LOCAL LEMMAS (Qed): mkR_expand, z64_eq_near, img_in, sh_byte_vis, wview_of_some, mrd_of_some, wview_eq, mrd_eq,
   mem_of_wview -- candidates for Kit.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (the _F run's closure reaches the
   frame route through Seg/F11F.v, allowed by the glue closure rule 1).  SHADOWED NAMES: once Seg/F11F.v's closure is
   loaded, the core modules YI04 / YI16 / YK11 / YK1b / YM05 / YO09 have twins in lib/A/Reusable and Lib.Mem /
   Lib.MState / Lib.Step / Lib.Cells have twins in lib/A/Bz/Lib (measured: Locate in the build of this file), so
   every one of those is written with its FULL path OSSVerify.Proofs.libreac.fuzz_ctrl.lib.* (as A5.v and
   ACtl.v:172 do).  getr / seg_rom / fp_regs / fp_csr / FPState are the CORE's lib/Reusable/YK11; cfg_at is
   Reusable.YG0d.cfg_at.

   BUILD STATE: type-check on a working branch 1899bed1aee (interim core 5da74c9c931, no stand-in) plus the four callee _on files
   taken by path from a working branch 36bfd511da3.  No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap A.ProgWorldVisFrame A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel Prog.RcParse Prog.RcReply Prog.RcReplyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcIdentModel Prog.RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_identity_ingest_c A.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F11 A.Prog.Seg.F11F A.Prog.Seg.F11Fon.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local lemmas. *)

(* mkR_of regs is definitionally the explicit 31-slot map (the analogue of Seg/F11.v:256-262 over the core's YK11). *)
Lemma mkR_expand : forall regs, Lib.Regs6ss.mkR_of regs =
  Lib.Frame.mkR (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 1)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 5)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 6)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 7)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 8)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 10)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 11)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 12)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 13)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 14)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 15)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 16)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 17)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 19)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 20)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 26)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 27)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 28)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 29)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 30)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Two register values that agree as words agree as numbers when one may sit up to 300 below 0 (a spill base read
   off a q64 at a small offset) and the other is a sane address. *)
Lemma z64_eq_near : forall a b, -300 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 47 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite (Z.mod_small b) in E by lia.
  destruct (Z_le_gt_dec 0 a) as [H0|H0].
  - rewrite Z.mod_small in E by lia. exact E.
  - exfalso. rewrite <- (Z.mod_add a 1 (2 ^ 64)) in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.

(* Every address of [IMG_LO, IMG_HI) = [0x10000, 0x5fe000) is an image byte: the four loaded segments tile it
   (ProgBridge.rsegs_spans). *)
Lemma img_in : forall x, 0x10000 <= x < 0x5fe000 -> Reusable.YG0d.in_img segs x.
Proof.
  intros x Hx. unfold Reusable.YG0d.in_img.
  assert (HT : forall b sz,
    In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) -> b <= x < b + sz ->
    exists sg, In sg segs /\ Z.of_N (seg_base sg) <= x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
  { intros b sz Hin Hb. apply in_map_iff in Hin as (s & Es & Hs). injection Es as E1 E2.
    exists s. split; [exact Hs | lia]. }
  rewrite A.ProgBridge.rsegs_spans in HT.
  destruct (Z_lt_le_dec x 0x30000) as [h1 | h1].
  { apply (HT 0x10000 0x20000); [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0x9e000) as [h2 | h2].
  { apply (HT 0x30000 0x6e000); [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0xa1000) as [h3 | h3].
  { apply (HT 0x9e000 0x3000); [right; right; left; reflexivity | lia]. }
  apply (HT 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

(* The byte-exact shadow span [p / 8 + ASAN_K, (p + n - 1) / 8 + ASAN_K] that an _F run reads lies inside the
   8-aligned shadow word cover [sh_al8_lo p, sh_al8_hi p n) that the visibility lemmas state. *)
Lemma sh_byte_vis : forall H p n, 0 < n ->
  A.ProgBridge.range_visible H (A.Prog.rng_asan.sh_al8_lo p)
    (A.Prog.rng_asan.sh_al8_hi p n - A.Prog.rng_asan.sh_al8_lo p) ->
  A.ProgBridge.range_visible H (p / 8 + A.AsanRT.ASAN_K) ((p + n - 1) / 8 - p / 8 + 1).
Proof.
  intros H p n Hn V. apply (A.ProgBridge.range_visible_sub _ _ _ _ _ V);
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.

(* A byte the memory holds is a writable view byte and a readable byte (wview / Lib.Mem.mrd read memory first). *)
Lemma wview_of_some : forall (sg : list Segment) (m : word -> option byte) x b, m x = Some b -> wview sg m x <> None.
Proof. intros sg m x b H. unfold wview. rewrite H. discriminate. Qed.

Lemma mrd_of_some : forall (sg : list Segment) (m : word -> option byte) x b,
  m x = Some b -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd sg m x = Some b.
Proof. intros sg m x b H. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma wview_eq : forall (sg : list Segment) (m m' : word -> option byte) x, m' x = m x -> wview sg m' x = wview sg m x.
Proof. intros sg m m' x H. unfold wview. rewrite H. reflexivity. Qed.

Lemma mrd_eq : forall (sg : list Segment) (m m' : word -> option byte) x,
  m' x = m x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd sg m' x =
                OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd sg m x.
Proof. intros sg m m' x H. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

(* Off every segment, a writable view byte is a memory byte. *)
Lemma mem_of_wview : forall (sg : list Segment) (m : word -> option byte) x,
  find_segment sg (bv_unsigned x) 1 = None -> wview sg m x <> None -> m x <> None.
Proof. intros sg m x Hf Hv Hn. apply Hv. unfold wview. rewrite Hn, Hf. reflexivity. Qed.

Section GlueF11_014.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :278-279), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A820ac_at := (ACtlCutP.C_A820ac_at B).
Local Notation C_A820f8_at := (ACtlCutP.C_A820f8_at B).

(* Proof-local abbreviations of the model terms (syntactic, so lia and rewrite see one term). *)
Local Notation RNGW W := (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W)).
Local Notation GG cx j := (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j).
Local Notation LEN cx j := (Prog.RcReply.ir_s (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) - 13).
Local Notation PB cx j := (firstn (Z.to_nat (LEN cx j)) (skipn 38 (GG cx j))).
Local Notation IDB cx j := (A.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j).
Local Notation AD cx j := (Prog.RcParse.cp_v (GG cx j) 36 * 256 + Prog.RcParse.cp_v (GG cx j) 37).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F11_014 : forall POST (j : nat), CF POST (ix_cut C_A820f8_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A820ac_at, ACtlCutP.v:2185-2199). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A820ac_at ACtlCutP.ixn nth ACtlCutP.b5_body] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hcn & Hj & HHB & HFLSI & HLK & HC & HbK & HbRC & H50 & Hsum & Hok & HbRP &
    R11 & R12 & R13 & HIDj & H17 & H240 & HPF).
  (* G2: the journal (AR, layout_le, the stack window's presence and astk_ok), the frame, the run ceiling. *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & _ & _ & _).
  unfold A.ACfn.LLVMF_STK in Hpres, Hstklo.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[HC0 HC1] _].
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efr3 in Hf4096. rewrite Efr3, HFB6 in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
  (* FRAC's pins and bounds; its spill base is b5_C's A. *)
  (* FRAC's last conjunct is the class-6 frame's trailer word, `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos
     cx))` (a Theorem Labs lane's glue base batch 3); it is Htrail. *)
  pose proof HFRAC as (A0 & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA416 & HS4 & HSapp & Hq304 & Hq24 & Hq16 & Hhdr1 & Hhdr2 & Hsh & Hsaved & Htrail).
  assert (HfrA' : fr + 3136 <= A0) by exact HfrA.
  (* FRAC's top of the entry sp is NON-STRICT (ACtlCutP.v:1111-1114, batch 4 item B5.4). *)
  assert (HSapp' : ACtlCut.c_sp cx <= 0x800000000000) by exact HSapp.
  assert (Hspu : bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) = sp)
    by exact Hspz.
  pose proof (bv_unsigned_in_range _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2)) as Rsp.
  change (bv_modulus 64) with (2 ^ 64) in Rsp. rewrite Hspu in Rsp.
  destruct HC as (R23 & R18 & (A & R9 & HA64 & HSPILL & Hq232) & HPH & HFR & HKN & HFGj & HFSj).
  assert (EA0 : A = A0) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym R9) Hr9)]).
  subst A0.
  (* the record block (phi, flen) is live in the current block list *)
  destruct HHB as (Hphinz & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _).
  assert (Hasz : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j) by (unfold A.ACtlK.a_size; lia).
  rewrite Hasz in Hpe. unfold A.AsanRT.APPMEM_END in Hpe.
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { eapply Permutation_in; [exact (Permutation_sym HP) | apply in_or_app; right; left; reflexivity]. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (_ & Hphi4096 & Hphiceil & _).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  rewrite Hreq in Hphiceil.
  destruct HPH as (HPHg & HPHpl).
  pose proof (HPHg H50) as P6.
  pose proof (HPHpl H50) as (Hplfr & Hplsp).
  unfold ACtlCutP.FRAME_BYTES in Hplfr. rewrite Hspz in Hplsp.
  unfold A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in Hplsp.
  (* ir holds on this arm (reply_ok), so 14 <= ir_s <= 23 and the record is the long one *)
  unfold Prog.RcReply.reply_ok in Hok. apply andb_prop in Hok. destruct Hok as [_ Hir].
  destruct (Prog.RcReply.ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _).
  assert (Hbig : A.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true)
    by (unfold A.Prog.SlotModel.t_big; apply Z.leb_le; exact H50).
  destruct HbK as (R20 & R22 & R24 & R25 & Hsp280 & Hu176 & Hargs).
  assert (R22' : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22 = Z_to_bv 64 (phi + 18)).
  { unfold ACtlCut.rgv in R22. rewrite Hbig in R22. exact R22. }
  destruct HSPILL as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
  destruct HbRP as (HRP256 & HRP272 & HRP304).
  destruct HIDj as (HIDB & HIDok).
  pose proof (A.Prog.Seg.F11.f11_tID_len (ACtlCut.c_in cx) j) as Hidbl.
  destruct HFLSI as ((HPRO & sp128 & Hfrstk & sp144 & Hid17) & sp216 & sp224 & sp248 & HIN & HFLC).
  destruct HFR as (HfgA & HidA & HFGb & HFGl).
  pose proof Hrt as (Hcells & Hcut & Himgsh & Hro).
  (* The callee's stack window as a Lib.Frame.stk: every byte of the journal's window is present (YCbq.v:368). *)
  assert (Hstk_of : forall lo hi, ACtlCut.c_sp cx - 32768 <= lo -> hi <= ACtlCut.c_sp cx -> 0 <= lo ->
            Lib.Frame.stk segs mem3 lo hi).
  { intros lo hi Hlo Hhi H0. split; [exact H0|]. split; [lia|].
    intros a Ha. destruct (Hpres a ltac:(lia)) as (_ & b & Hb).
    split; [exact (wview_of_some _ _ _ _ Hb) | exists b; exact (mrd_of_some _ _ _ _ Hb)]. }
  (* G2: the 38 premises of f11_014_evt_F (F11F.v:302-348), in its order. *)
  assert (P1 : length (GG cx j) = 50%nat) by apply A.Prog.Seg.F11.f11_tg_len.
  assert (P2 : 0 < phi) by lia.
  assert (P3 : phi + 50 <= 2 ^ 64) by lia.
  assert (P7 : A.AsanRT.addressable mem3 phi 50).
  { pose proof (A.AsanRTFacts.addressable_sub mem3 phi _ 0 50 HAd ltac:(lia) ltac:(lia) ltac:(rewrite Hasz; lia))
      as H. rewrite Z.add_0_r in H. exact H. }
  pose proof (A.Prog.Seg.F11.f11_lrwB mem3 (fr + 256) 2 _ HRP256) as P11.
  assert (P12 : 0 < fr) by lia.
  assert (P13 : fr + 3136 <= 2 ^ 64) by lia.
  assert (P14 : (fr + 2688) mod 2 = 0).
  { pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite Hfr32 in X.
    replace (fr + 2688) with ((16 * (fr / 32) + 1344) * 2) by lia. apply Z_mod_mult. }
  pose proof (A.Prog.Seg.F11.f11_rwb mem3 (fr + 2688) 38 _ fr (fr + ACtlCutP.FRAME_BYTES) Hfrstk
                ltac:(lia) ltac:(unfold ACtlCutP.FRAME_BYTES; lia) Hidbl HIDB) as P15.
  assert (P16 : length (PB cx j) = Z.to_nat (LEN cx j)) by (apply A.Prog.Seg.F11.f11_pb_len; [exact P1 | lia]).
  assert (P17 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (phi + 38) (PB cx j)).
  { apply Prog.RcReplyLib.rc_bytes_first.
    pose proof (Prog.RcReplyLib.rc_bytes_skip segs mem3 phi (GG cx j) 38 P6 ltac:(rewrite P1; lia)) as HH.
    exact HH. }
  assert (P18 : phi + 38 + LEN cx j <= fr + 2688 \/ fr + 2688 + 38 <= phi + 38) by lia.
  assert (P19 : Lib.Frame.stk segs mem3 (sp - 32)
                  (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2)))
    by (rewrite Hspu; apply Hstk_of; lia).
  assert (P20 : sp - 32 + 32 <= bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2))
    by (rewrite Hspu; lia).
  assert (P21 : fr + 2688 + 38 <= bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) - 32 \/
                bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) <= fr + 2688)
    by (rewrite Hspu; left; lia).
  assert (P22 : phi + 38 + LEN cx j <=
                  bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) - 32 \/
                bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) <= phi + 38)
    by (rewrite Hspu; lia).
  assert (P26 : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                          A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
            Lib.Frame.outside (A.Prog.reac_identity_ingest_c.reac_identity_ingest_W
                                 (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2))
                                 (fr + 2688)) x).
  { intros x Hx. rewrite Hspu.
    unfold A.Prog.reac_identity_ingest_c.reac_identity_ingest_W,
      A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME.
    cbn [Lib.Frame.outside].
    destruct Hx as [Hx | [Hx | Hx]].
    - unfold A.AsanRT.GOT_CELL_K in Hx. split; [lia|]. split; [|exact I]. intros Hxf.
      apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x HAR Hin6);
        [rewrite Efr3, HFB6; lia | apply img_in; lia].
    - unfold A.AsanRT.CELL_K in Hx. split; [lia|]. split; [|exact I]. intros Hxf.
      apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x HAR Hin6);
        [rewrite Efr3, HFB6; lia | apply img_in; lia].
    - unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in Hx.
      split; [lia|]. split; [lia | exact I]. }
  (* the footprint ranges, at RNG := RNG_W (w_H W3), from a Theorem Labs lane's visibility lemmas *)
  assert (P27 : Lib.ExecF.rng (RNGW W3) phi 50).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 50 HAR Hinphi);
      [lia | rewrite Hreq; lia]. }
  assert (P28 : Lib.ExecF.rng (RNGW W3) (A.AsanRT.shadow_addr phi)
                  (A.AsanRT.shadow_addr (phi + 49) - A.AsanRT.shadow_addr phi + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 50 HAR Hinphi
                ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(lia)) as [E|V]; [lia|].
    pose proof (sh_byte_vis _ phi 50 ltac:(lia) V) as V'.
    replace (phi + 50 - 1) with (phi + 49) in V' by lia.
    unfold A.AsanRT.shadow_addr.
    replace ((phi + 49) / 8 + A.AsanRT.ASAN_K - (phi / 8 + A.AsanRT.ASAN_K) + 1)
      with ((phi + 49) / 8 - phi / 8 + 1) by lia.
    exact V'. }
  assert (P29 : Lib.ExecF.rng (RNGW W3) (A + 256) 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 256) 8 HJ); unfold A.ACfn.LLVMF_STK; lia. }
  assert (P30 : Lib.ExecF.rng (RNGW W3) (A + 144) 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 144) 8 HJ); unfold A.ACfn.LLVMF_STK; lia. }
  assert (P31 : Lib.ExecF.rng (RNGW W3) (fr + 256) 2).
  { apply A.ProgBridge.rng_of_visible.
    exact (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 256) 2 HAR Hin6
                    ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, HFB6; lia))). }
  assert (P32 : Lib.ExecF.rng (RNGW W3)
                  (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) -
                   A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME)
                  A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME).
  { rewrite Hspu. unfold A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME.
    apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 32) 32 HJ); unfold A.ACfn.LLVMF_STK; lia. }
  assert (P33 : Lib.ExecF.rng (RNGW W3) A.AsanRT.GOT_CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, A.AsanRT.GOT_CELL_K; lia. }
  assert (P34 : Lib.ExecF.rng (RNGW W3) A.AsanRT.CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, A.AsanRT.CELL_K; lia. }
  assert (P35 : Lib.ExecF.rng (RNGW W3) (fr + 2688) 38).
  { apply A.ProgBridge.rng_of_visible.
    exact (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2688) 38
                    HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, HFB6; lia))). }
  assert (P36 : Lib.ExecF.rng (RNGW W3) ((fr + 2688) / 8 + A.AsanRT.ASAN_K)
                  ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (proj2 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2688) 38
                       HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, HFB6; lia))
                ltac:(lia) ltac:(rewrite Efr3; Z.div_mod_to_equations; lia)
                ltac:(rewrite Efr3, HFB6; Z.div_mod_to_equations; lia)) as [E|V]; [lia|].
    pose proof (sh_byte_vis _ (fr + 2688) 38 ltac:(lia) V) as V'.
    replace (fr + 2688 + 38 - 1) with (fr + 2688 + 37) in V' by lia. exact V'. }
  assert (P37 : Lib.ExecF.rng (RNGW W3) (phi + 38) (LEN cx j)).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 38) (LEN cx j)
             HAR Hinphi); [lia | rewrite Hreq; lia]. }
  assert (P38 : Lib.ExecF.rng (RNGW W3) ((phi + 38) / 8 + A.AsanRT.ASAN_K)
                  ((phi + 38 + LEN cx j - 1) / 8 - (phi + 38) / 8 + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 38)
                (LEN cx j) HAR Hinphi ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(lia)) as [E|V]; [lia|].
    exact (sh_byte_vis _ (phi + 38) (LEN cx j) ltac:(lia) V). }
  (* G3: the cut's configuration in the run's state form, the walk moved to mkR_of regs3, mkR_of expanded and the
     five slots the run pins rewritten to their carried values. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A820ac_at [Z.of_nat j])) with 0x820ac.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x820ac)
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  rewrite mkR_expand.
  unfold ACtlCut.rgv in R9, R12, R13, Hr26.
  rewrite R9, R12, R13, R22', Hr26.
  (* G4: the run (F11F.v:302-348) and the lift (one SRr_fevt_hid over the whole segment, call included). *)
  match goal with
  | |- context [Lib.Frame.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 _ ?x10 ?x11 _ _ ?x14 ?x15 ?x16 ?x17
                  ?x18 ?x19 ?x20 ?x21 _ ?x23 ?x24 ?x25 _ ?x27 ?x28 ?x29 ?x30 ?x31] =>
    pose proof (A.Prog.Seg.F11Fon.f11_014_evt_F_on (RNGW W3) x1 x2 x3 x4 x5 x6 x7 x8 x18 x19 x20 x21 x23 x24 x25 x27
                  x28 x29 x30 x31 x10 x11 x14 x15 x16 x17 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr mem3
                  phi fr A (sp - 32) (LEN cx j) (GG cx j) (IDB cx j) (PB cx j)
                  P1 P2 P3 eq_refl Hsr P6 P7 HA64 Hq256 Hq144 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22
                  Hcells HidA P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38) as HRUN
  end.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (RNGW W3) _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
  (* G5: the continuation at the run's end state; its map is the exit cut's map. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & _ & ST' & HRW).
  subst ms'.
  match goal with
  | |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (Rend := R)
  end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A820f8_at [Z.of_nat j])) Rend m' md') (POST cx)).
  assert (EW : A.Prog.reac_identity_ingest_c.reac_identity_ingest_W
                 (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2))
                 (fr + 2688) = [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)])
    by (rewrite Hspu; reflexivity).
  rewrite EW in MU. rewrite Hspu in ST'.
  (* the run's post names F11F's munch / wmono, which resolve to lib/A/Tk/UL/Frame.v's (measured: Locate); restate
     them over lib/Lib/Frame.v's, whose bodies are the same (conversion) *)
  assert (MU' : Lib.Frame.munch [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] mem3 m') by exact MU.
  assert (WM' : Lib.Frame.wmono segs mem3 m') by exact WM.
  clear MU WM. rename MU' into MU. rename WM' into WM.
  (* the write set [sp-32, sp) u [fr+2688, fr+2726) and what lies apart from it *)
  assert (Hout : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
            Lib.Frame.outside [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] x).
  { intros x H1 H2. cbn [Lib.Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (Hdj : forall a n, 0 <= n -> (a + n <= sp - 32 \/ sp <= a) -> (a + n <= fr + 2688 \/ fr + 2688 + 38 <= a) ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a n).
  { intros a n H0 H1 H2. cbn [Lib.Frame.disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (Hbt : forall a bs, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 a bs ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a (Z.of_nat (length bs)) ->
            OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs m' a bs)
    by (intros a bs H D; exact (Lib.Frame.bytes_at_transport segs _ mem3 m' a bs H MU D)).
  assert (Zsp : forall a n, A <= a -> 0 <= n ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a n)
    by (intros a n H1 H2; apply Hdj; lia).
  assert (Zfr : forall a n, fr <= a -> 0 <= n -> a + n <= fr + 4096 ->
            (a + n <= fr + 2688 \/ fr + 2688 + 38 <= a) ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a n)
    by (intros a n H1 H2 H3 H4; apply Hdj; [exact H2 | left; lia | exact H4]).
  assert (Zblk : forall p n a q, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= a -> 0 <= q ->
            a + q <= p + Reusable.YG00.req_size n ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a q).
  { intros p n a q Hin Hpa Hq Haq.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & _ & Hpc & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hin Hin6)
      as Hz.
    unfold Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Efr3, HFB6 in Hz.
    apply Hdj; [exact Hq | left; lia | destruct Hz; [left | right]; lia]. }
  assert (Zsh : forall a n, 0x7fff8000 <= a -> 0 <= n -> a + n <= 0x10007fff8000 ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a n)
    by (intros a n H1 H2 H3; apply Hdj; lia).
  assert (Zimg : forall a n, 0x10000 <= a < 0x5fe000 -> 0 <= n -> a + n <= 0x5fe000 ->
            Lib.Frame.disjoint_from [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] a n).
  { intros a n H1 H2 H3. apply Hdj; [exact H2 | left; lia |].
    destruct (Z_le_gt_dec (a + n) (fr + 2688)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (fr + 2688 + 38) a) as [h'|h']; [right; exact h'|].
    exfalso.
    destruct (Z_le_gt_dec a (fr + 2688)) as [ha|ha].
    - apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2688) HAR Hin6);
        [rewrite Efr3, HFB6; lia | apply img_in; lia].
    - apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) a HAR Hin6);
        [rewrite Efr3, HFB6; lia | apply img_in; lia]. }
  assert (Tq : forall off v, 0 <= off -> ACtlCutP.q64 mem3 (A + off) v -> ACtlCutP.q64 m' (A + off) v).
  { intros off v Ho Hq. unfold ACtlCutP.q64 in Hq |- *. apply Hbt; [exact Hq | apply Zsp; lia]. }
  assert (Tsp : forall off v, 0 <= off <= 300 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill Rend m' off v).
  { intros off v Ho (A' & HA' & Hq).
    pose proof Hq as (Hq0 & Hq1 & _). rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in Hq1.
    assert (EA' : A' = A) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym HA') R9)]).
    subst A'. exists A. split; [exact eq_refl | apply Tq; [lia | exact Hq]]. }
  assert (AW : A.AsanRTFacts.all_app [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  { cbn [A.AsanRTFacts.all_app]. unfold A.AsanRTFacts.app_ivl.
    split; [|split; [|exact I]]; intros a Ha;
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END; lia. }
  pose proof (A.AsanRTFacts.munch_meta _ mem3 m' MU AW) as MK.
  assert (Ta : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n H; exact (A.AsanRTFacts.addressable_kept mem3 m' p n H MK)).
  (* no byte of the write set is an image byte, so none lies in a segment *)
  assert (Hnoimg : forall a, (sp - 32 <= a < sp \/ fr + 2688 <= a < fr + 2688 + 38) ->
            ~ Reusable.YG0d.in_img segs a).
  { intros a Ha Hi. pose proof (A.ACtlG.Kit.kit_segs_low a Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl.
    destruct Ha as [Ha|Ha]; [lia|].
    apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) a HAR Hin6);
      [rewrite Efr3, HFB6; lia | exact Hi]. }
  assert (Hnoseg : forall x : word,
            (sp - 32 <= bv_unsigned x < sp \/ fr + 2688 <= bv_unsigned x < fr + 2688 + 38) ->
            find_segment segs (bv_unsigned x) 1 = None).
  { intros x Hx. destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:Ef; [|reflexivity].
    exfalso. destruct (Reusable.YK04.find_segment_some_spec _ _ _ _ Ef) as (Hs & H1 & H2).
    apply (Hnoimg (bv_unsigned x) Hx). exists s. split; [exact Hs | lia]. }
  (* the frame's stk across the write, and the input bytes *)
  assert (Tfrstk : Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (Prog.RcReplyLib.rc_stk_after segs _ mem3 m' fr (fr + ACtlCutP.FRAME_BYTES) Hfrstk MU WM).
    intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
    destruct (Z_lt_le_dec x (fr + 2688)) as [h1|h1]; [left; apply Hout; lia|].
    destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [h2|h2]; [|left; apply Hout; lia].
    right. exact (Prog.RcReplyLib.rc_rw_mrd segs m' (fr + 2688) 38 _ x HRW ltac:(lia)). }
  assert (TINb : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { destruct HIN as (_ & HINb).
    apply Hbt; [exact HINb|].
    destruct (proj1 HBase) as (_ & _ & _ & _ & Hpn & Hnl & _).
    rewrite <- Hnl.
    destruct Hpn as [(Hn0 & Hpe0) | (Hnpos & Hinp)].
    - rewrite Hn0, Hpe0. apply Zimg; unfold A.ACfn.A_EMPTY; lia.
    - assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { eapply Permutation_in; [exact (Permutation_sym HP) | apply in_or_app; left; exact Hinp]. }
      apply (Zblk _ _ _ _ Hin3); [lia | lia |].
      unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  (* the exit cut C_A820f8_at (ACtlCutP.v:2203-2213) at the same cx, fr, k, ly3, S3, W3, the map Rend, m', md' *)
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 Rend m' md' HBase).
  - (* journal: ajournal_exec (YCbq.v:636-643) with Wr = the callee's two intervals *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => sp - 32 <= a < sp \/ fr + 2688 <= a < fr + 2688 + 38).
    + exact HJ.
    + intros x Hx. cbv beta in Hx. unfold Reusable.YK04.mrestrict.
      rewrite (MU x); [reflexivity|]. apply Hout; lia.
    + intros x. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x) eqn:EH; intros Hx; [exact Hx|].
      pose proof (bv_unsigned_in_range _ x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      assert (Hc : (sp - 32 <= bv_unsigned x < sp \/ fr + 2688 <= bv_unsigned x < fr + 2688 + 38) \/
                   ((bv_unsigned x < sp - 32 \/ sp <= bv_unsigned x) /\
                    (bv_unsigned x < fr + 2688 \/ fr + 2688 + 38 <= bv_unsigned x))) by lia.
      destruct Hc as [Hw | (H1 & H2)].
      * apply (mem_of_wview segs m' x (Hnoseg x Hw)).
        destruct Hw as [Hs | Hf].
        -- destruct ST' as (_ & _ & Hst). destruct (Hst (bv_unsigned x) Hs) as (Hv & _).
           unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa in Hv. rewrite Z_to_bv_bv_unsigned in Hv. exact Hv.
        -- pose proof HRW as (_ & (_ & _ & Hwr)).
           cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_size
                OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.csize] in Hwr.
           pose proof (Hwr (bv_unsigned x - (fr + 2688)) ltac:(lia)) as Hv.
           replace (fr + 2688 + (bv_unsigned x - (fr + 2688))) with (bv_unsigned x) in Hv by lia.
           unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa in Hv. rewrite Z_to_bv_bv_unsigned in Hv. exact Hv.
      * rewrite (MU x (Hout _ H1 H2)). exact Hx.
    + exact Hhid.
    + exact Hsbm.
    + intros a [Ha | Ha].
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, HFB6. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax on both cuts *)
    exact Hk.
  - (* the exit body *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A820f8_at ACtlCutP.ixn nth
                              ACtlCutP.b5_body].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    split.
    { (* FRAC at the end map and the written memory *)
      exists A, sp.
      split; [exact Hr2|]. split; [exact Hsp16|]. split; [exact Hspz|]. split; [exact Hr4|].
      split; [exact Hr8|]. split; [exact eq_refl|]. split; [exact Hr3|]. split; [exact Hr19|].
      split; [exact eq_refl|].
      split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAS|]. split; [exact HspA|].
      split; [exact HfrA|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HSapp|].
      split; [apply Tq; [lia | exact Hq304]|].
      split; [apply Tq; [lia | exact Hq24]|].
      split; [apply Tq; [lia | exact Hq16]|].
      split; [unfold ACtlCutP.q64 in Hhdr1 |- *; apply Hbt;
              [exact Hhdr1 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; apply Zfr; lia]|].
      split; [unfold ACtlCutP.q64 in Hhdr2 |- *; apply Hbt;
              [exact Hhdr2 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; apply Zfr; lia]|].
      split.
      { destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
        apply Hbt; [exact Hshb|].
        assert (E392 : Z.of_nat (length sh) = 392) by (rewrite Hshl; reflexivity).
        rewrite E392. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
        pose proof (Z.mul_div_le fr 8 ltac:(lia)) as D1. pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)) as D2.
        apply Zsh; lia. }
      split; [apply Hbt; [exact Hsaved | apply Zsp; lia]|].
      (* the trailer word [fr + 4088, fr + 4096): a frame range apart from the identity record, so the munch kept it *)
      unfold ACtlCutP.q64 in Htrail |- *; apply Hbt;
        [exact Htrail | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; apply Zfr; lia]. }
    exists phi.
    split; [exact HP|]. split; [exact Hcn|]. split; [exact Hj|].
    split; [split; [exact Hphinz | exact (Ta _ _ HAd)]|].
    split.
    { (* FLSI *)
      destruct HPRO as (sp40 & sp120 & sp136 & sp160 & sp168 & sp176 & sp208 & sp248p & Hour6 & HINb0 & HINp0 &
        sp184p & sp256p & sp264p & sp272p & sp32p).
      split.
      { split.
        { split; [apply Tsp; [lia | exact sp40]|]. split; [apply Tsp; [lia | exact sp120]|].
          split; [apply Tsp; [lia | exact sp136]|]. split; [apply Tsp; [lia | exact sp160]|].
          split; [apply Tsp; [lia | exact sp168]|]. split; [apply Tsp; [lia | exact sp176]|].
          split; [apply Tsp; [lia | exact sp208]|]. split; [apply Tsp; [lia | exact sp248p]|].
          split; [exact (Ta _ _ Hour6)|]. split; [exact TINb|].
          split; [intros Hn; exact (Ta _ _ (HINp0 Hn))|].
          split; [apply Tsp; [lia | exact sp184p]|]. split; [apply Tsp; [lia | exact sp256p]|].
          split; [apply Tsp; [lia | exact sp264p]|].
          split; [apply Tsp; [lia | exact sp272p] | apply Tsp; [lia | exact sp32p]]. }
        split; [apply Tsp; [lia | exact sp128]|]. split; [exact Tfrstk|].
        split; [apply Tsp; [lia | exact sp144] | exact (Ta _ _ Hid17)]. }
      split; [apply Tsp; [lia | exact sp216]|]. split; [apply Tsp; [lia | exact sp224]|].
      split; [apply Tsp; [lia | exact sp248]|].
      split; [destruct HIN as (HINa & _); split; [exact (Ta _ _ HINa) | exact TINb]|].
      destruct HFLC as (fc256 & fc184 & fc192 & fc80 & fc88 & fc96 & fc272 & fc264 & fcfg & fcid & fc72 & fc64 &
        fc56 & fc48).
      split; [apply Tsp; [lia | exact fc256]|]. split; [apply Tsp; [lia | exact fc184]|].
      split; [apply Tsp; [lia | exact fc192]|]. split; [apply Tsp; [lia | exact fc80]|].
      split; [apply Tsp; [lia | exact fc88]|]. split; [apply Tsp; [lia | exact fc96]|].
      split; [apply Tsp; [lia | exact fc272]|]. split; [apply Tsp; [lia | exact fc264]|].
      split; [exact (Ta _ _ fcfg)|]. split; [exact (Ta _ _ fcid)|].
      split; [apply Tsp; [lia | exact fc72]|]. split; [apply Tsp; [lia | exact fc64]|].
      split; [apply Tsp; [lia | exact fc56] | apply Tsp; [lia | exact fc48]]. }
    split.
    { (* LK *)
      destruct HLK as (Hj255 & R21 & HOUR). split; [exact Hj255|]. split; [exact R21|].
      unfold ACtlCutP.OURb in HOUR |- *. apply Hbt; [exact HOUR|].
      rewrite A.Prog.SlotModel.OUR_length. apply Zfr; lia. }
    split.
    { (* b5_C *)
      split; [exact R23|]. split; [exact R18|].
      split.
      { exists A. split; [exact eq_refl|]. split; [exact HA64|]. split.
        - split; [apply Tq; [lia | exact Hq248]|]. split; [apply Tq; [lia | exact Hq256]|].
          split; [apply Tq; [lia | exact Hq144]|]. split; [apply Tq; [lia | exact Hq184]|].
          split; [apply Tq; [lia | exact Hq192]|]. split; [apply Tq; [lia | exact Hq80]|].
          split; [apply Tq; [lia | exact Hq88]|]. split; [apply Tq; [lia | exact Hq96]|].
          split; [apply Tq; [lia | exact Hq272] | apply Tq; [lia | exact Hq264]].
        - apply Tq; [lia | exact Hq232]. }
      split.
      { split; [|exact HPHpl].
        intros _. apply Hbt; [exact P6|]. apply (Zblk _ _ _ _ Hinphi); [lia | lia | rewrite Hreq, P1; lia]. }
      split.
      { split; [exact (Ta _ _ HfgA)|]. split; [exact (Ta _ _ HidA)|].
        split; [|exact HFGl]. unfold ACtlCutP.fragb in HFGb |- *. apply Hbt; [exact HFGb|].
        rewrite HFGl. apply Zfr; lia. }
      split.
      { destruct HKN as (HKNb & HKNa). split; [|exact (Ta _ _ HKNa)].
        apply Hbt; [exact HKNb|]. rewrite A.Prog.Seg.F11.f11_kn_len.
        apply Zimg; unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia. }
      split.
      { destruct HFGj as (HFGB & HFGok). split; [|exact HFGok].
        unfold ACtlCutP.FGBe in HFGB |- *. apply Hbt; [exact HFGB|]. rewrite HFGl. apply Zfr; lia. }
      destruct HFSj as (Hf104 & Hf112 & Hfbody & Hfaddr & HFI).
      split; [apply Tsp; [lia | exact Hf104]|]. split; [apply Tsp; [lia | exact Hf112]|].
      split; [|split; [exact (Ta _ _ Hfaddr) | exact HFI]].
      apply Hbt; [exact Hfbody|].
      pose proof (A.Prog.Seg.F11.f11_fs_body_len (ACtlCut.c_in cx) j) as Hbl. apply Zfr; lia. }
    (* the cut's own tail: b5_K, b5_RC, 50 <= flen, the ingest result, IDb1, b5_F17, b5_W240, b5_PF *)
    split.
    { split; [exact R20|]. split; [unfold ACtlCut.rgv; rewrite Hbig; exact eq_refl|].
      split; [exact R24|]. split; [exact R25|].
      split.
      { destruct Hsp280 as (A2 & H9b & HA2 & Hq280).
        assert (EA2 : A2 = A) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym H9b) R9)]).
        subst A2. exists A. split; [exact eq_refl|]. split; [exact HA64|]. apply Tq; [lia | exact Hq280]. }
      split; [|exact Hargs].
      unfold ACtlCutP.u32 in Hu176 |- *. apply Hbt; [exact Hu176|].
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4. apply Zfr; lia. }
    split.
    { destruct HbRC as (Hpa2 & Hpp8 & Hpn8). split; [exact (Ta _ _ Hpa2)|].
      split; [exact (Ta _ _ Hpp8) | exact (Ta _ _ Hpn8)]. }
    split; [exact H50|].
    split.
    { exists (fst (Prog.RcIdentModel.ING (IDB cx j) (AD cx j) (PB cx j))). split; [exact eq_refl|].
      destruct (Prog.RcIdentModel.ING_ret (IDB cx j) (AD cx j) (PB cx j)) as [E|E]; rewrite E; lia. }
    split.
    { assert (EID : ACtlCutP.ID1 cx j = snd (Prog.RcIdentModel.ING (IDB cx j) (AD cx j) (PB cx j))).
      { unfold ACtlCutP.ID1, A.Prog.SlotModel.rp_id. rewrite Hir. reflexivity. }
      unfold ACtlCutP.IDb1, ACtlCutP.IDBe. rewrite EID. split.
      - exact (A.Prog.Seg.F11.f11_lrwB m' (fr + 2688) 38 _ HRW).
      - exact (Prog.RcIdentLib.ING_id_ok (IDB cx j) (AD cx j) (PB cx j) Hidbl HIDok). }
    split.
    { destruct H17 as (A3 & H9c & HA3 & Hq200).
      assert (EA3 : A3 = A) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym H9c) R9)]).
      subst A3. exists A. split; [exact eq_refl|]. split; [exact HA64|]. apply Tq; [lia | exact Hq200]. }
    split.
    { destruct H240 as (A4 & H9d & HA4 & w240 & Hqw & Hw0 & Hwt & Hwf).
      assert (EA4 : A4 = A) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym H9d) R9)]).
      subst A4. exists A. split; [exact eq_refl|]. split; [exact HA64|].
      exists w240. split; [apply Tq; [lia | exact Hqw]|]. split; [exact Hw0|]. split; [exact Hwt | exact Hwf]. }
    destruct HPF as (A5 & H9e & HA5 & Hrec & Hcmp).
    assert (EA5 : A5 = A) by (apply z64_eq_near; [lia | lia | exact (eq_trans (eq_sym H9e) R9)]).
    subst A5. exists A. split; [exact eq_refl|]. split; [exact HA64|]. split.
    + intros Hle. destruct (Hrec Hle) as (_ & Hphib). split.
      * exists (GG cx j).
        split; [apply Hbt; [exact P6 | apply (Zblk _ _ _ _ Hinphi); [lia | lia | rewrite Hreq, P1; lia]]|].
        rewrite P1. lia.
      * apply Hbt; [exact Hphib|]. apply (Zblk _ _ _ _ Hinphi); [lia | lia |]. rewrite Hreq.
        assert (Hphl : (length (A.Prog.SlotModel.t_phi (ACtlCut.c_in cx) j) <= Z.to_nat (ACtlCutP.flen cx j))%nat).
        { unfold A.Prog.SlotModel.t_phi, A.Prog.SlotModel.f_phi, ACtlCutP.flen, A.Prog.SlotModel.t_len.
          rewrite length_firstn. apply Nat.le_min_l. }
        lia.
    + intros H8819. destruct (Hcmp H8819) as
        ((field16 & v14 & v15 & v16 & v17 & Hru16 & Hrb14 & Hrb15 & Hrb16 & Hrb17 &
          Hrv14 & Hrv15 & Hrv16 & Hrv17 & Hrs14 & Hrs15 & Hrs16 & Hrs17 & Erf & Erk)
         & (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcm & Haddr)
         & (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Haddr2)).
      assert (Tb8 : forall a v, phi <= a -> a + 1 <= phi + 50 -> ACtlCutP.b8 mem3 a v -> ACtlCutP.b8 m' a v).
      { intros a v H1 H2 H. unfold ACtlCutP.b8 in H |- *. apply Hbt; [exact H|].
        apply (Zblk _ _ _ _ Hinphi); cbn [length]; [lia | lia | rewrite Hreq; lia]. }
      assert (Tsh8 : forall x v, phi <= x < phi + 50 ->
                ACtlCutP.b8 mem3 (Z.shiftr x 3 + A.ACtlK.ASAN_K) v ->
                ACtlCutP.b8 m' (Z.shiftr x 3 + A.ACtlK.ASAN_K) v).
      { intros x v Hx H. unfold ACtlCutP.b8 in H |- *. apply Hbt; [exact H|].
        rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        unfold A.ACtlK.ASAN_K, A.AsanRT.ASAN_K.
        pose proof (Z.mul_div_le x 8 ltac:(lia)) as D1. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D2.
        cbn [length]. apply Zsh; lia. }
      split; [|split].
      * exists field16, v14, v15, v16, v17.
        split; [unfold ACtlCutP.u16 in Hru16 |- *; apply Hbt;
                [exact Hru16 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le2; apply Zfr; lia]|].
        split; [apply Tb8; [lia | lia | exact Hrb14]|].
        split; [apply Tb8; [lia | lia | exact Hrb15]|].
        split; [apply Tb8; [lia | lia | exact Hrb16]|].
        split; [apply Tb8; [lia | lia | exact Hrb17]|].
        split; [exact Hrv14|]. split; [exact Hrv15|]. split; [exact Hrv16|]. split; [exact Hrv17|].
        split; [apply Tsh8; [lia | exact Hrs14]|].
        split; [apply Tsh8; [lia | exact Hrs15]|].
        split; [apply Tsh8; [lia | exact Hrs16]|].
        split; [apply Tsh8; [lia | exact Hrs17]|].
        split; [exact Erf | exact Erk].
      * exists (firstn 6 ls), (firstn 6 rs).
        split; [apply Tq; [lia | exact Hq72]|].
        split; [apply Hbt; [exact (A.Prog.Seg.F11.f11_bytes_first mem3 (fr + 186) ls 6 Hls)
                           | rewrite length_firstn; apply Zfr; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [apply Hbt; [exact (A.Prog.Seg.F11.f11_bytes_first mem3 phi rs 6 Hrs)
                           | rewrite length_firstn; apply (Zblk _ _ _ _ Hinphi); [lia | lia | rewrite Hreq; lia]]|].
        split; [rewrite length_firstn; lia|].
        split; [rewrite A.Prog.Seg.F11.f11_mcmp_firstn; exact Hcm|].
        exact (Ta _ _ Haddr).
      * exists (firstn 6 ls2), (firstn 6 rs2).
        split; [apply Tq; [lia | exact Hq64]|].
        split; [apply Hbt; [exact (A.Prog.Seg.F11.f11_bytes_first mem3 (fr + 180) ls2 6 Hls2)
                           | rewrite length_firstn; apply Zfr; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [apply Hbt; [exact (A.Prog.Seg.F11.f11_bytes_first mem3 (phi + 6) rs2 6 Hrs2)
                           | rewrite length_firstn; apply (Zblk _ _ _ _ Hinphi); [lia | lia | rewrite Hreq; lia]]|].
        split; [rewrite length_firstn; lia|].
        split; [rewrite A.Prog.Seg.F11.f11_mcmp_firstn; exact Hcm2|].
        exact (Ta _ _ Haddr2).
  - (* ctl_rt_C across the write, at the entry cut's state ly3 S3 *)
    assert (HshOut : forall x, A.AsanRT.in_shadow x ->
              Lib.Frame.outside [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] x).
    { intros x Hx.
      unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in Hx.
      apply Hout; lia. }
    split; [|split; [|split]].
    + unfold A.ACtlK.asan_cells_at, A.AsanRT.asan_cells in Hcells |- *.
      destruct Hcells as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & c16 &
        c17).
      assert (TI : forall a bs, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 a bs ->
                0x10000 <= a /\ a + Z.of_nat (length bs) <= 0x5fd000 ->
                OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs m' a bs).
      { intros a bs H (H1 & H2). apply Hbt; [exact H | apply Zimg; lia]. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
                (conj _ (conj _ (conj _ (conj _ _))))))))))))))));
        (apply TI; [assumption | split; apply Z.leb_le; vm_compute; reflexivity]).
    + exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Hcut MU WM HshOut).
    + exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Himgsh MU WM HshOut).
    + unfold A.ACtlK.ro_agree_at in Hro |- *. intros a Ha.
      rewrite <- (Hro a Ha).
      assert (Himg : Reusable.YG0d.in_img segs (bv_unsigned a)).
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr in Ha.
        destruct (find_segment A.Img0.rsegs (bv_unsigned a) 1) as [s|] eqn:Ef; [|discriminate].
        destruct (Reusable.YK04.find_segment_some_spec _ _ _ _ Ef) as (Hs & H1 & H2).
        exists s. split; [exact Hs | lia]. }
      pose proof (bv_unsigned_in_range _ a) as Ra.
      assert (HnW : ~ (sp - 32 <= bv_unsigned a < sp \/ fr + 2688 <= bv_unsigned a < fr + 2688 + 38))
        by (intro Hw; exact (Hnoimg _ Hw Himg)).
      apply mrd_eq. apply MU. apply Hout; lia.
Qed.

End GlueF11_014.

Print Assumptions glue_seg_F11_014.
