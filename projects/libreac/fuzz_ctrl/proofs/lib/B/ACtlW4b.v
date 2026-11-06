(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* lib/B/ACtlW4b.v -- piece W4b (frame turn, part 2: S_F7 .. S_F12_298) of fuzz_ctrl image B's (asan-ubsan) walk of
   LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  Stage file written by a Theorem Labs lane on
   a Theorem Labs lane's frozen interface (ACtlCut.v / ACtlCutP.v / ACtl.v).
   rule 24: no function proved (kind: segment lemma; stage glue of a walk).

   WHAT THIS FILE PROVES: one stage lemma per cut of W4b (cut-table rows 47-53; all own6, k <= 14+2j+1, live list
   entry ++ [(phi, flen cx j)]), POINTWISE in the frame-loop index j (ACtlCut.ix_cut), each named and stated exactly as
   lib/B/ACtl.v's Section hypothesis of the same name, generic in SK and FP.  No allocator site, no fake-stack call.
     B8215c_at j --S_F7-->  B82174_at j     F7F.f7_pre_F + reac_ctrl_kind_name @0x82170, lifted once
     B82174_at j --S_F8-->  B82180_at j     F8F.f8_pre_F + reac_ctrl_kind_name @0x8217c, lifted once
     B82180_at j --S_F9-->  B821ec_at j     F9F.f9_evtA_F + f9_evtB_pre_F, then reac_ctrl_identity_reply @0x821e8 (CUT:
                                           the callee takes its own class-1 fake frame; shared spec TREPLY)
     B821ec_at j --S_F10--> B8226c_at j     F10F.seg_F10_ok_F (reply_ret = 1)
                         | B82308_at j     F10F.seg_F10_ne_F (reply_ret = 0, the ir-false arm)
     B8226c_at j --S_F11--> B82304_at j     F11F.seg_F11_pre_F + record_sum_closes @0x82284, F11F.seg_F11_pre2_F +
                                           reac_identity_ingest @0x82300, each pair lifted once
     B82304_at j --S_F12--> B82340_at j     F12F.f12_pre_F_on (on MemNorm.normalize, moved back by
     B82308_at j --S_F12_298--> B82340_at j   MemNormF.evtF_normalize_ro) + __asan_memcpy @0x8233c (AMEMCPY, aj_intrin_at)
   Every SINK / TRAP branch of 0x8215c-0x82340 (0x8215c, 0x82168, 0x82174, 0x821b4, 0x821ec, 0x821f4, 0x82200, 0x82208,
   0x8221c, 0x8223c, 0x82268, 0x82288, 0x822e8, 0x82304 -> 0x82fa4; T20-T25 -> 0x82fa0) is a not-taken step of the
   `_F` run that contains it, its premise from the cut body.

   THE GLUE (each stage): unpack the cut; move the walk to the run's canonical register map (YA0nR.SRr_xregs_eqv);
   run the `_F` stretch and the callee's closed footprint theorem (composed by ExecF.evtF_cut) at the footprint
   ProgBridge.RNG_W (w_H W3), every rng premise a visibility fact (kit w4b_*_vis: journal stack window, owned frame,
   live heap block and its shadow, image); lift with YA0nR.SRr_fevt(_hid); re-establish the successor's journal
   (YCbq.ajournal_exec), the runtime conjunct and body (FRAC with its trailer word included) across the run's and the
   callee's write sets.  ROUTE (C) (a working branch shell, a Theorem Labs lane): a cut carries B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (the
   cells, shadow_rw_on the cut's own shadow and the image's, ro_agree), not the universal ctl_rt; a stage reads
   the frame shadow from the cut_shadow conjunct (seg_F9, seg_F12) and the ro_agree conjunct (seg_F7 / F8 / F12);
   at a successor cut ctl_rt_C is kept across a stack-only write (w4b_ctl_rt_munch, w4b11_rt_mv) or rebuilt from the
   post journal's AR by a Theorem Labs lane's proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w4b_ctlrt_C; seg_F9, seg_F12).
   CALLEES (route (C): the `_on` forms, shadow premise dropped), cited by their CLOSED theorems
   (Required qualified): record_sum_closesF_on.record_sum_closes_holds_F_on, reac_identity_ingestF
   .reac_identity_ingest_F_holds_on, reac_ctrl_kind_name_F.reac_ctrl_kind_name_holds_F_on; __asan_memcpy by AMEMCPY +
   B.ProgWorld.ctl_post_memcpy; F12F's run by a Theorem Labs lane's F12F.f12_pre_F_on (5f08e560663).  Bridges by proved
   lemmas: ProgBridge.fevt_of_evtF, ProgBridge.img_vis_W, w4b_wx (the Section hypotheses Hwx / tfibsegs_rsegs / RTP /
   rt_of_core stay in the header, unused by the proofs; the former FEVT / img_vis_W hypotheses are deleted: the two
   lemmas state them up to conversion, Reusable.YB1v.tfibsegs = B.Img0.rsegs by B.ProgBridge.tfibsegs_rsegs,
   reflexivity, and range_visible / B.Prog.ImgBounds.IMG_LO / IMG_HI unfold to the written-out bounds).

   SECTION HYPOTHESES THE PROOFS USE (Print Assumptions at the end of the file, per stage):
   - LAWS (ACtlW0.v's text): the core's AR laws for B.  Owner: the top (core's AsanAPI aa_laws / TFIB_LIB).
   - AMEMCPY (seg_F12 / seg_F12_298): the core's memcpy rule at B's catalogue name; its world-form post is converted
     by the CITED B.ProgWorld.ctl_post_memcpy (lib/B/ProgWorld.v:765; RTPOST-SHARED-B.txt's 15:40Z swap).
   - ctl_kind_name_shadow_vis (seg_F7, F8, F12, F12_298), ctl_kind_name_str_shadow, ctl_kind_name_addressable,
     ctl_kind_name_not_owned (seg_F9): shared RTPOST-SHARED-B.txt (a working note, not in this delivery) texts, owner a Theorem Labs lane (the first three proved in
     lib/B/ProgBridgeData.v at a working branch fbe168f4d89; the top discharges them).
   - TFIB_SYMS, RELRO_IMG, RO_OFL (seg_F9, seg_F12, seg_F12_298): the premises of ctl_rt_C_of_AR and of
     arodata_ok_journalP (RTPOST-SHARED-B.txt's ctl_rt block, VIS0 / OWNED_RO deleted by route (C)); the top
     discharges them (CtrlB_syms, relro_img_CtrlB, RO_OFL by computation).
   - TREPLY (seg_F9): a Theorem Labs lane's shared world spec of reac_ctrl_identity_reply
     (B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec RLO RHI B, the cut call at a0 = phi, a1 = len,
     a2..a4 = fr + 256 / 272 / 304).  Owner a Theorem Labs lane; discharged by its pb_reac_ctrl_identity_reply.

   PROVENANCE: cut table cut-table-B.tsv rows 47-53 (a working note, not in this delivery); plan (a working note, not in this delivery) 2.3 rows 47-53, 6.2
   rows S_F10 / S_F11, F.4.1 rows 19-24; the `_F` runs of a Theorem Labs lane (lib/B/Prog/Seg/F7F.v .. F12F.v), source runs at
   3803efccea0 (F7-F12); objdump L84900-L85020. *)

From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six modules that exist twice (core lib/Reusable/<X> and ctrl's lib/B/Reusable/<X>: YI04 YI16 YK11 YK1b YM05
   YO09) are Required by the core's own path and named lib.Reusable.<X> (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YI16 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn Reusable.YImgTop.
(* lib/Lib's raw-memory vocabulary of the call-post fact below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's published `_F` modules (Required qualified, never Imported, a Theorem Labs lane 23:38Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F7F F8F F9F F10F F11F F12F.
(* record_sum_closes' `_on` footprint contract and its proof (a Theorem Labs lane, 3ea30e6571b: the accepted contract_F with
   the shadow premise dropped), Required qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c record_sum_closes_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closesF_on.
(* The glue's kit and bridge (Required qualified, never Imported): the world-walk lift (YA0nR), the register-map
   move (Regs6ss), lib/Lib's state form, the image-B bridge (ProgBridge: cfg_at_MS, RNG_W, rng_of_visible), the
   core's state vocabulary, and the pure models / runtime facts the stage arithmetic reads. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge B.AsanRT B.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel Prog.RcReply Prog.RcParse.
(* The evtF transfer from the normalized memory to the cut's own memory under ro_agree (in a Theorem Labs lane's `_F` closure:
   F29F / F30F / F34F Require it), for a run whose premise is mem_inv. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm B.MemNormF.
(* The footprint contracts of the two lifted callees, `_on` forms (route (C), Required qualified): reac_ctrl_kind_name
   (0x83d98; a Theorem Labs lane 924cd2205f6) and reac_identity_ingest (0x87e0c; a Theorem Labs lane ebcd94ed838). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_kind_name_c reac_ctrl_kind_name_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_ingest_c reac_identity_ingestF.
(* seg_F9's cut call of reac_ctrl_identity_reply: a Theorem Labs lane's shared world spec (statement only), and the pieces of
   ctl_rt_C at a successor cut (route (C)): a Theorem Labs lane's proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR, fed with the kept
   read-only view (Reusable.APostBase.arodata_ok_journalP, B.ProgWorld.arodata_okP_of_S), the symbol record
   YF0m.CtrlTSyms; the narrowed shadow predicate and its transports (B.ShadowRwOn, B.ShadowRwOnT), all Required
   qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m Reusable.APostBase B.ProgWorld B.ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC ShadowRwOn ShadowRwOnT.
Import ListNotations.
Local Open Scope Z_scope.

Section W4b.

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
Local Notation C_B8215c_at := (ACtlCutP.C_B8215c_at B).
Local Notation C_B82174_at := (ACtlCutP.C_B82174_at B).
Local Notation C_B82180_at := (ACtlCutP.C_B82180_at B).
Local Notation C_B821ec_at := (ACtlCutP.C_B821ec_at B).
Local Notation C_B8226c_at := (ACtlCutP.C_B8226c_at B).
Local Notation C_B82304_at := (ACtlCutP.C_B82304_at B).
Local Notation C_B82308_at := (ACtlCutP.C_B82308_at B).
Local Notation C_B82340_at := (ACtlCutP.C_B82340_at B).

(* ---- Section hypotheses (sources in the header and in ACtlW0.v's) ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* rt_of_core, placeholder form (a Theorem Labs lane 22:44Z; no APIf, a Theorem Labs lane 23:05Z).  TODO: B's bridge statement verbatim. *)
Variable RTP : (word -> option byte) -> Prop.
Hypothesis rt_of_core : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> RTP mem.

(* V6 twin for the KIND_NAME table (added 04:35Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as V6): FLI's KNT (ACtlCutP.v, `addressable m KNA.KIND_NAME 112`, carried by every LK cut) crosses a runtime
   call only through AR, since the image's shadow is allocator-owned. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* KIND_NAME's 14 shadow bytes are VISIBLE (added 05:00Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same
   file as V6): the kind_name calls (W4b seg_F7 / seg_F8, W3b seg_P11) need the callee premise
   `rng RNG (shadow_addr KIND_NAME) 14`; ctl_kind_name_addressable gives raw addressability only. *)
Hypothesis ctl_kind_name_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr B.ACtlCutP.KNA.KIND_NAME) 14.

(* The kind-name STRING's first byte is addressable and its shadow byte visible (added 05:12Z; drafted by a Theorem Labs lane
   for seg_F9's first check; W3b's seg_P11 likely the same; owner a Theorem Labs lane, V6 family).  The bound on v
   is the cut's own (`0 <= v < 2 ^ 31`, ACtlCutP.v C_B821ec_at / C_B8226c_at bodies), which keeps the fact weakest. *)
Hypothesis ctl_kind_name_str_shadow : forall ly S (W : Reusable.YA0n.world segs) mem md v,
  Reusable.YG0n.AR segs B ly S W mem md -> 0 <= v < 2 ^ 31 ->
  B.AsanRT.addressable mem (B.ACtlCutP.KNA.kind_name_addr v) 1 /\
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr (B.ACtlCutP.KNA.kind_name_addr v)) 1.

(* T10 twin for the KIND_NAME table (added 05:24Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as T10): KNT's 112 bytes at KIND_NAME (RELRO) are neither a static owned extent nor the errno cell, so
   ctl_post_acall_kept's image arm keeps them across an allocator call or a reac_ctrl_parse call. *)
Hypothesis ctl_kind_name_not_owned : forall a : Z,
  B.ACtlCutP.KNA.KIND_NAME <= a < B.ACtlCutP.KNA.KIND_NAME + 112 ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

(* ctl_rt route (C) (a Theorem Labs lane 11:03Z; replaces the 06:45Z one-form block): a stage that needs ctl_rt_C at a post / cut
   state cites B.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms B -> AR_laws -> AR ... -> arodata_okP ... -> ctl_rt_C B ly S m)
   and carries these, token for token; it supplies arodata_okP from ctl_base's arodata_okS through
   Reusable.APostBase.arodata_ok_journalP (which finds RO_OFL as an instance).  VIS0 / OWNED_RO are GONE (VIS0 is false
   at an AR state; OWNED_RO is not needed by ctl_rt_C_of_AR).  The top discharges: TFIB_SYMS := Reusable.YD2l.CtrlB_syms,
   RELRO_IMG := relro_img_CtrlB, RO_OFL by computation at SK := Reusable.YE2k.tfib_sink_head. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* __asan_memcpy @0x8233c: the core's memcpy rule at B's catalogue name. *)
Hypothesis AMEMCPY :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy.

(* munch_vis / wmono_vis / rt_post_frame: the local notations of B.ProgWorld's Definitions of the same names (the
   walk's shared RtPost text); the memcpy post itself is CITED: B.ProgWorld.ctl_post_memcpy. *)
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

(* The core's AR laws (YCbq.v Section a0's hypothesis), the same named hypothesis as lib/B/ACtlW0.v's LAWS: the
   journal step (ajournal_exec) and the visibility facts below read them. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   GLUE KIT (local to this file).  Image-B twins, over this file's segs, of a Theorem Labs lane's lib/A/ACtlG/Kit.v helpers
   (kit_segs_low, kit_frac_move, kit_RNG0) and of the image-A visibility lemmas lib/A/ProgWorldVisHeap.v /
   ProgWorldVisFrame.v / ProgWorldVisWin.v (heap_vis, frame_vis, win_vis, vis_of_aview), plus the register and
   memory moves the stages repeat. *)

(* The kit's once-per-unit premise of YA0nR.SRr_fevt, proved on B's segments (a Theorem Labs lane's kit_wx proof); the
   stages use it instead of the Section hypothesis Hwx. *)
Lemma w4b_wx : Reusable.YK04.wx_segs_nowrap segs.
Proof. apply Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The image placement premise of YCbq.ajournal_exec: every segment byte lies below kLowMemEnd (B's spans,
   ProgBridge.rsegs_spans). *)
Lemma w4b_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold Reusable.YG0f.kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ sg Hin).
  rewrite B.ProgBridge.rsegs_spans in H.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

(* Two literals below 2^64 are equal iff their words are. *)
Lemma w4b_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !lib.Lib.MState.unsigned_lit in E by lia. exact E.
Qed.

(* FRAC (ACtlCutP.v) reads registers 2 (also through spZ), 3, 4, 8, 9, 19 and 26 only (kit_frac_move). *)
Lemma w4b_frac_move : forall cx fr sel (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs' m.
Proof.
  intros cx fr sel regs regs' m H E2 E3 E4 E8 E9 E19 E26.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

(* f10_K (ACtlCutP.v) reads registers 9 (the spills), 18, 20, 22, 24, 25 and 27 (FLI's -8) only. *)
Lemma w4b_f10K_move : forall cx j phi fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.f10_K cx j phi fr regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 20 = lib.Reusable.YK11.getr regs 20 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  ACtlCutP.f10_K cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m H E9 E18 E20 E22 E24 E25 E27.
  unfold ACtlCutP.f10_K, ACtlCutP.FLVsp, ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv in *.
  rewrite E9, E18, E20, E22, E24, E25, E27. exact H.
Qed.

(* FTURN and F272 read register 9 (the spill base) only. *)
Lemma w4b_fturn_move : forall cx j phi (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FTURN cx j phi regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> ACtlCutP.FTURN cx j phi regs' m.
Proof.
  intros cx j phi regs regs' m H E9. unfold ACtlCutP.FTURN, ACtlCutP.spill, ACtlCut.rgv in *. rewrite E9. exact H.
Qed.

Lemma w4b_f272_move : forall cx j (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.F272 cx j regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> ACtlCutP.F272 cx j regs' m.
Proof.
  intros cx j regs regs' m H E9. unfold ACtlCutP.F272, ACtlCutP.spill, ACtlCut.rgv in *. rewrite E9. exact H.
Qed.

(* The empty footprint: a run with no data access is lifted with fp_avoids vacuous (kit_RNG0). *)
Definition w4b_RNG0 : Lib.ExecF.footprint := fun _ _ => False.

Lemma w4b_fp_RNG0 : forall H, Reusable.YK04R.fp_avoids H w4b_RNG0.
Proof. intros H a n Hr. destruct Hr. Qed.

(* A byte the view reads is visible: a hidden byte lies in no segment (w_Hoff), so the view reads None there
   (lib/A/ProgWorldVisFrame.v vis_of_aview, over this file's segs). *)
Lemma w4b_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

(* win_vis (lib/A/ProgWorldVisWin.v): a range inside the journal's stack window is visible at the cut. *)
Lemma w4b_win_vis : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
    (Wc : Reusable.YA0n.world segs) memc mdc k lo len,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H Wc) lo len.
Proof.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k lo len HJ Hlo Hhi.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  change (2 ^ 47) with 140737488355328 in H47.
  unfold B.ProgBridge.range_visible. change (2 ^ 64) with 18446744073709551616.
  split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* frame_vis (lib/A/ProgWorldVisFrame.v, first part): the bytes of a live fake frame are visible. *)
Lemma w4b_frame_vis : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos lo len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly cid pos <= lo ->
  lo + len <= Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) lo len.
Proof.
  intros ly S W mem md cid pos lo len HAR Hin Hlo Hhi.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hal & Happ & Hby & Hsh).
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  set (F := Reusable.YG0f.frame_addr ly cid pos) in *.
  set (sz := Reusable.YG00.fs_frame_bytes cid) in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HF : 4096 <= F /\ F + sz <= 0x7fffff800000) by lia.
  split; [lia |]. split; [rewrite P64; lia |]. intros a Ha.
  destruct (Hby a ltac:(lia)) as [[Hv _] _]. exact Hv.
Qed.

(* heap_vis (lib/A/ProgWorldVisHeap.v): a sub-range of a live heap block is visible. *)
Lemma w4b_heap_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> lo + len <= p + Reusable.YG00.req_size n ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) lo len.
Proof.
  intros ly S W mem md p n lo len HAR Hin Hlo Hhi.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & Hpres & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (Hpres a ltac:(lia)) as [[Hv _] _]. exact Hv.
Qed.

(* The shadow byte of one byte of a live heap block is visible (AR_shadow_law's shadow_hull_vis). *)
Lemma w4b_heap_sh1 : forall ly S (W : Reusable.YA0n.world segs) mem md p n x,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= x < p + Reusable.YG00.req_size n ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (Z.shiftr x 3 + B.AsanRT.ASAN_K) 1.
Proof.
  intros ly S W mem md p n x HAR Hin Hx.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [_ Hh].
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold B.ProgBridge.range_visible, B.AsanRT.ASAN_K.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hx8.
  pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)) as Hx8'.
  split; [lia|]. split; [lia|].
  intros s Hs. replace s with (x / 8 + 2147450880) by lia.
  apply (w4b_vis_of_aview W mem). apply Hh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)) as M1.
  pose proof (Z.div_le_mono x (p + Reusable.YG00.req_size n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
  Z.div_mod_to_equations. lia.
Qed.

(* An 8-byte cell of a rw_cells fact as carried bytes (Seg/F10.v f10_lrw8, over lib/Lib's cells). *)
Lemma w4b_lrw8 : forall m a v,
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB 8 (lib.Lib.Mem.le8 v)] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 v).
Proof.
  intros m a v [[_ H] _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

(* One byte of a carried byte list. *)
Lemma w4b_bytes_at_nth : forall m a bs (i : nat), lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> (i < length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat i) [nth i bs Prog.RcParse.cp_z].
Proof.
  intros m a bs i (H0 & H1 & H) Hi. split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. cbn [nth_error].
  rewrite Z.add_0_r. rewrite (H i Hi). apply nth_error_nth'. exact Hi.
Qed.

(* The shadow byte of phi + 26 is 0 when the heap block (phi, len) with 50 <= len is addressable: the 8-byte granule
   of phi + 26 lies in the block (Seg/F10.v f10_sh26, over ACtlK.a_size). *)
Lemma w4b_sh26 : forall m phi L, B.AsanRT.addressable m phi (B.ACtlK.a_size L) -> 50 <= L ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (Z.shiftr (phi + 26) 3 + B.AsanRT.ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L HA HL.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + 26) 8 ltac:(lia)) as Hr.
  assert (H8 : B.AsanRT.addressable m (phi + (26 - (phi + 26) mod 8)) 8)
    by (apply (B.AsanRTFacts.addressable_sub m phi (B.ACtlK.a_size L));
        [exact HA | lia | lia | unfold B.ACtlK.a_size; lia]).
  destruct (B.AsanRTFacts.meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (26 - (phi + 26) mod 8)) 3 = Z.shiftr (phi + 26) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + 26) 8 ltac:(lia)) as D.
    replace (phi + (26 - (phi + 26) mod 8)) with ((phi + 26) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* The frame base fr of an own6 cut is the class-6 frame of the cut's layout (the journal's layout_le keeps ly_F). *)
Lemma w4b_fr_ly3 : forall (cx : ACtlCut.ctlcx) ly3 fr,
  Reusable.YG0f.layout_le (length (Reusable.YG00.st_secs (ACtlCut.c_S cx))) (ACtlCut.c_ly cx) ly3 ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr.
Proof.
  intros cx ly3 fr Hly ->. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity.
Qed.

(* The journal across a raw-memory write confined to a sub-range [lo, hi) of its stack window (a lifted callee's
   frame, written by the callee and present after it): YCbq.ajournal_exec with Wr = [lo, hi). *)
Lemma w4b_aj_munch : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
    (Wc : Reusable.YA0n.world segs) memc mdc k memc' mdc' lo hi,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 ->
  lib.Lib.Frame.munch [(lo, hi)] memc memc' ->
  (forall x : word, lo <= bv_unsigned x < hi -> memc' x <> None) ->
  (forall x : word, Reusable.YA0n.w_H Wc x = true -> memc' x = memc x) ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' lo hi HJ Hlo Hhi Hm Hp Hh Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k
           memc' mdc' (fun a => lo <= a < hi) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (Hm x); [reflexivity|]. cbn. split; [exact Hx | exact I].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H Wc x); [exact Hx|].
    destruct (Z_le_gt_dec lo (bv_unsigned x)) as [H1|H1];
      [destruct (Z_lt_ge_dec (bv_unsigned x) hi) as [H2|H2]|].
    + apply Hp. lia.
    + rewrite (Hm x); [exact Hx | cbn; split; [lia | exact I]].
    + rewrite (Hm x); [exact Hx | cbn; split; [lia | exact I]].
  - exact Hh.
  - exact Hs.
  - intros a Ha. left. lia.
Qed.

(* A carried byte list survives a munch that misses each of its bytes. *)
Lemma w4b_bytes_at_munch : forall W m m' a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> lib.Lib.Frame.outside W (a + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) Hm Ho. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold lib.Lib.Mem.mrd. rewrite (Hm (lib.Lib.Mem.wa (a + Z.of_nat i))); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by lia. apply Ho. lia.
Qed.

(* The segment bytes of image B lie below 0x5fe000 (ProgBridge.rsegs_spans). *)
Lemma w4b_find_segment_low : forall x seg, find_segment B.Img0.rsegs x 1 = Some seg -> x < 0x5fe000.
Proof.
  intros x seg Hf.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.kb_find_segment B.Img0.rsegs x 1 seg Hf)
    as (Hin & Hb & He).
  assert (H : In (Z.of_N (seg_base seg), Z.of_N (seg_size seg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ seg Hin).
  rewrite B.ProgBridge.rsegs_spans in H.
  remember (Z.of_N (seg_base seg)) as b eqn:Eb. remember (Z.of_N (seg_size seg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

(* ctl_rt_C (the image cells, the cut's and the image's shadow, the read-only image bytes) survives a munch that misses
   every address below HIGHMEM_BEG (a write inside the machine stack, which lies above alloc_ceiling), at the same
   layout and state (route (C): the keep narrows with the predicate). *)
Lemma w4b_ctl_rt_munch : forall ly S W m m',
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < B.AsanRT.HIGHMEM_BEG -> lib.Lib.Frame.outside W x) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S W m m' (Hc & Hs & Him & Hr) Hm Ho.
  assert (Hb : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a + Z.of_nat (length bs) <= 0x5fe000 ->
                 lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H Hl. apply (w4b_bytes_at_munch W m m' a bs H Hm). intros i Hi.
    pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ H) as Hbd.
    apply Ho. unfold B.AsanRT.HIGHMEM_BEG. lia. }
  assert (Hx : forall x : word, bv_unsigned x < B.AsanRT.HIGHMEM_BEG -> m' x = m x).
  { intros x Hx. apply Hm. apply Ho. pose proof (bv_unsigned_in_range 64 x) as [Hx0 _]. lia. }
  assert (Hsh : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').
  { intros P HP a Hp Ha.
    assert (Ea : m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)).
    { apply Hx. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
        B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Ha.
      rewrite lib.Lib.Mem.wa_unsigned by lia. unfold B.AsanRT.HIGHMEM_BEG. lia. }
    unfold wview, lib.Lib.Mem.mrd. rewrite Ea. exact (HP a Hp Ha). }
  split; [|split; [exact (Hsh _ Hs) | split; [exact (Hsh _ Him) |]]].
  - unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells in *.
    destruct Hc as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
    refine (conj (Hb _ _ C1 _) (conj (Hb _ _ C2 _) (conj (Hb _ _ C3 _) (conj (Hb _ _ C4 _) (conj (Hb _ _ C5 _)
      (conj (Hb _ _ C6 _) (conj (Hb _ _ C7 _) (conj (Hb _ _ C8 _) (conj (Hb _ _ C9 _) (conj (Hb _ _ C10 _)
      (conj (Hb _ _ C11 _) (conj (Hb _ _ C12 _) (conj (Hb _ _ C13 _) (conj (Hb _ _ C14 _) (conj (Hb _ _ C15 _)
      (conj (Hb _ _ C16 _) (Hb _ _ C17 _)))))))))))))))));
      cbn [length]; rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4;
      unfold B.AsanRT.CELL_K, B.AsanRT.GOT_CELL_K, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.GOT_REPLACE,
        B.AsanRT.UAR, B.AsanRT.GOT_UAR, B.AsanRT.CANPOISON, B.AsanRT.HIEND, B.AsanRT.GOT_HIEND, B.AsanRT.MIDBEG,
        B.AsanRT.GOT_MIDBEG, B.AsanRT.MIDEND, B.AsanRT.GOT_MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
        B.AsanRT.GOT_REAL_MEMSET; cbn; lia.
  - unfold B.ACtlK.ro_agree_at in *. intros a Ha.
    assert (Ea : m' a = m a).
    { apply Hx. unfold lib.Lib.Mem.ro_addr in Ha.
      destruct (find_segment B.Img0.rsegs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
      pose proof (w4b_find_segment_low _ _ Ef). unfold B.AsanRT.HIGHMEM_BEG. lia. }
    unfold lib.Lib.Mem.mrd. rewrite Ea. exact (Hr a Ha).
Qed.

(* ctl_rt_C at a successor cut (route (C)): the journal's AR and the entry's read-only view (ctl_base's arodata_okS)
   kept along the journal (Reusable.APostBase.arodata_ok_journalP), into a Theorem Labs lane's proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (the same proof as W5's w5_ctlrt). *)
Lemma w4b_ctlrt_C : forall (cx : ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _) & _).
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 (proj1 HJ)).
  eapply (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B); [exact HJ|].
  apply (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro0); lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   HELPERS w4b7_ (seg_F7 / seg_F8): the transports across a lifted reac_ctrl_kind_name call.  The callee writes only
   its window [sp - 16, sp) of the machine stack; every body byte lies at or above sp (the spill area [A, A + 448)
   and the saved registers below c_sp, sp <= A), or below sp - 16 (the class-6 frame, phi's heap block, the image
   and every shadow byte of app memory: all below alloc_ceiling <= the journal's stack window). *)

(* A byte list ending below L survives a munch that misses [0, L). *)
Lemma w4b7_bk : forall W m m' a bs L,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> a + Z.of_nat (length bs) <= L ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs L H Hm Hlow Hl.
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ H) as Hb.
  apply (w4b_bytes_at_munch W m m' a bs H Hm). intros i Hi. apply Hlow. lia.
Qed.

(* A byte list starting at or above A survives a munch that misses [A, oo). *)
Lemma w4b7_bkh : forall W m m' a bs A,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall x, A <= x -> lib.Lib.Frame.outside W x) -> A <= a ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs A H Hm Hout Ha.
  apply (w4b_bytes_at_munch W m m' a bs H Hm). intros i Hi. apply Hout. lia.
Qed.

(* Addressability reads only the shadow bytes of app memory, all below HIGHMEM_BEG. *)
Lemma w4b7_ak : forall W m m' p n L,
  B.AsanRT.addressable m p n -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> B.AsanRT.HIGHMEM_BEG <= L ->
  B.AsanRT.addressable m' p n.
Proof.
  intros W m m' p n L (H0 & H1 & H2 & H) Hm Hlow HL.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as [Happ (b & Hb & Hok)].
  split; [exact Happ|]. exists b. split; [|exact Hok].
  assert (Hs : 0 <= B.AsanRT.shadow_addr (p + i) < B.AsanRT.HIGHMEM_BEG).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG.
    unfold B.AsanRT.APPMEM_END in H2. Z.div_mod_to_equations. lia. }
  rewrite <- Hb. unfold lib.Lib.Mem.mrd.
  rewrite (Hm (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by (unfold B.AsanRT.HIGHMEM_BEG in Hs; lia).
  apply Hlow. lia.
Qed.

(* A spill base A' with a carried cell at A' + off is FRAC's spill base A (F7.v f7_base_eq, over ACtlCutP.q64). *)
Lemma w4b7_base_eq : forall (A A' off v : Z) (m : word -> option byte),
  Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  ACtlCutP.q64 m (A' + off) v -> A' = A.
Proof.
  intros A A' off v m E HA0 HA1 Hoff Hq.
  destruct Hq as (Hq0 & Hq1 & _).
  rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !lib.Lib.MState.unsigned_lit_wrap in E.
  rewrite (Z.mod_small A) in E by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* One spill cell [A + off] survives a munch that misses [A, oo) (F7.v f7_spill_keep). *)
Lemma w4b7_spill : forall (regs regs' : bvmap 5 word) m m' W off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  0 <= off < 448 -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  (forall x, A <= x -> lib.Lib.Frame.outside W x) -> lib.Lib.Frame.munch W m m' ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A (A' & HA' & Hq) HA E9 Hoff HA0 HA1 Hout Hm.
  assert (EA : A' = A).
  { apply (w4b7_base_eq A A' off v m); [| exact HA0 | exact HA1 | exact Hoff | exact Hq].
    unfold ACtlCut.rgv in HA', HA. rewrite <- HA'. exact HA. }
  subst A'. exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  unfold ACtlCutP.q64 in *. apply (w4b7_bkh W m m' _ _ A Hq Hm Hout). lia.
Qed.

(* FRAC across the call: its registers are kept, its spills / saved registers lie at or above sp, its frame words
   (header, entry, trailer) and the frame shadow below L. *)
Lemma w4b7_frac : forall cx fr sel (regs regs' : bvmap 5 word) m m' W L,
  ACtlCutP.FRAC B cx fr sel regs m ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  lib.Lib.Frame.munch W m m' ->
  (forall x, Reusable.YG0d.spZ regs <= x -> lib.Lib.Frame.outside W x) ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) ->
  fr + 4096 <= L -> B.AsanRT.HIGHMEM_BEG <= L ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' W L HF E2 E3 E4 E8 E9 E19 E26 Hm Hout Hlow HfL HHL.
  apply (w4b_frac_move cx fr sel regs regs' m');
    [| exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26].
  destruct HF as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA448 & HS4096 & HSapp & H336 & H48 & H40 & Hhdr & H16 & (sh & Hsh & Hshl) & Hsv & Htr).
  rewrite HspZ in Hout.
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hhdr) as [Hfr0 _].
  pose proof HfrA as HfrA'. unfold ACtlCutP.FRAME_BYTES in HfrA'.
  pose proof HSapp as HSapp'. unfold B.AsanRT.APPMEM_END in HSapp'.
  exists A, sp.
  do 17 (split; [assumption|]).
  unfold ACtlCutP.q64 in *.
  split; [apply (w4b7_bkh W m m' _ _ sp H336 Hm Hout); lia|].
  split; [apply (w4b7_bkh W m m' _ _ sp H48 Hm Hout); lia|].
  split; [apply (w4b7_bkh W m m' _ _ sp H40 Hm Hout); lia|].
  split; [apply (w4b7_bk W m m' _ _ L Hhdr Hm Hlow); rewrite lib.Lib.Mem.length_le8; lia|].
  split; [apply (w4b7_bk W m m' _ _ L H16 Hm Hlow); rewrite lib.Lib.Mem.length_le8; lia|].
  split.
  { exists sh. split; [|exact Hshl]. apply (w4b7_bk W m m' _ _ L Hsh Hm Hlow).
    rewrite Hshl. change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. unfold B.AsanRT.HIGHMEM_BEG in HHL.
    Z.div_mod_to_equations. lia. }
  split; [apply (w4b7_bkh W m m' _ _ sp Hsv Hm Hout); lia|].
  apply (w4b7_bk W m m' _ _ L Htr Hm Hlow). rewrite lib.Lib.Mem.length_le8. lia.
Qed.

(* FLI: s11, the spills, the frame's records addressable, the frame body's stk and KNT (image bytes, shadow). *)
Lemma w4b7_fli : forall cx fr (regs regs' : bvmap 5 word) m m' W A L,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> lib.Lib.Frame.outside W x) ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> fr + 4096 <= L -> B.AsanRT.HIGHMEM_BEG <= L ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m m' ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' W A L HF HA E9 E27 HA0 HA1 Hout Hlow HfL HHL Hm Hw.
  unfold ACtlCutP.FLI, ACtlCutP.RAD, ACtlCutP.KNT in HF |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    first
      [ match goal with |- ACtlCutP.spill _ _ _ _ =>
          eapply w4b7_spill; [eassumption | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact Hm]
        end
      | match goal with |- ACtlCut.rgv _ _ _ => unfold ACtlCut.rgv in *; rewrite E27; assumption end
      | match goal with |- B.AsanRT.addressable _ _ _ =>
          eapply w4b7_ak; [eassumption | exact Hm | exact Hlow | exact HHL]
        end
      | match goal with Hs : lib.Lib.Frame.stk _ m ?lo ?hi |- lib.Lib.Frame.stk _ m' ?lo ?hi =>
          pose proof Hs as (Hs0 & _);
          apply (lib.Lib.Frame.stk_transport B.Img0.rsegs W m m' lo hi Hs Hm Hw);
          intros x Hx; left; apply Hlow; unfold ACtlCutP.FRAME_BYTES in *; lia
        end
      | match goal with Hb : lib.Lib.Mem.bytes_at _ m ?a ?bs |- lib.Lib.Mem.bytes_at _ m' ?a ?bs =>
          apply (w4b7_bk W m m' a bs L Hb Hm Hlow);
          change (length ACtlCutP.KNA.kind_name_bytes) with 112%nat;
          unfold ACtlCutP.KNA.KIND_NAME, B.AsanRT.HIGHMEM_BEG in *; lia
        end ].
Qed.

Lemma w4b7_lk : forall cx fr j (regs regs' : bvmap 5 word) m m' W A L,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> lib.Lib.Frame.outside W x) ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> fr + 4096 <= L -> B.AsanRT.HIGHMEM_BEG <= L ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m m' ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' W A L (Hj & H240 & HOUR & HFLI) HA E9 E27 HA0 HA1 Hout Hlow HfL HHL Hm Hw.
  split; [exact Hj|].
  split; [exact (w4b7_spill regs regs' m m' W 240 _ A H240 HA E9 ltac:(lia) HA0 HA1 Hout Hm)|].
  split.
  - unfold ACtlCutP.OURb in *. pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ HOUR) as [H0 _].
    apply (w4b7_bk W m m' _ _ L HOUR Hm Hlow). rewrite ACtlCutP.SM.OUR_length. lia.
  - exact (w4b7_fli cx fr regs regs' m m' W A L HFLI HA E9 E27 HA0 HA1 Hout Hlow HfL HHL Hm Hw).
Qed.

Lemma w4b7_fm : forall cx j phi fr (regs regs' : bvmap 5 word) m m' W A,
  ACtlCutP.FM cx j phi fr regs m -> ACtlCut.rgv regs 9 A ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> lib.Lib.Frame.outside W x) -> lib.Lib.Frame.munch W m m' ->
  ACtlCutP.FM cx j phi fr regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' W A (H184 & H24 & H22 & H25 & H312) HA E9 E22 E24 E25 HA0 HA1 Hout Hm.
  unfold ACtlCut.rgv in H24, H22, H25.
  split; [exact (w4b7_spill regs regs' m m' W 184 _ A H184 HA E9 ltac:(lia) HA0 HA1 Hout Hm)|].
  split; [unfold ACtlCut.rgv; rewrite E24; exact H24|].
  split; [unfold ACtlCut.rgv; rewrite E22; exact H22|].
  split; [unfold ACtlCut.rgv; rewrite E25; exact H25|].
  exact (w4b7_spill regs regs' m m' W 312 _ A H312 HA E9 ltac:(lia) HA0 HA1 Hout Hm).
Qed.

(* FSj: the local `first` [fr + 2880, fr + 2920) (its body is at most 23 bytes, F7.v f7_body_length). *)
Lemma w4b7_fsj : forall cx fr j (regs regs' : bvmap 5 word) m m' W L,
  ACtlCutP.FSj cx fr j regs m -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> fr + 4096 <= L -> B.AsanRT.HIGHMEM_BEG <= L ->
  ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' W L (Hh & Hn & Hb & Ha & HFI) Hm Hlow HfL HHL.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F7.f7_body_length (ACtlCut.c_in cx) j) as Hbl.
  unfold ACtlCutP.u32, ACtlCutP.b8 in *.
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hh) as [H0 _].
  split; [apply (w4b7_bk W m m' _ _ L Hh Hm Hlow); rewrite lib.Lib.Mem.length_le4; lia|].
  split; [apply (w4b7_bk W m m' _ _ L Hn Hm Hlow); cbn [length]; lia|].
  split; [apply (w4b7_bk W m m' _ _ L Hb Hm Hlow); lia|].
  split; [exact (w4b7_ak W m m' _ _ L Ha Hm Hlow HHL) | exact HFI].
Qed.

Lemma w4b7_fturn : forall cx j phi (regs regs' : bvmap 5 word) m m' W A L,
  ACtlCutP.FTURN cx j phi regs m -> ACtlCut.rgv regs 9 A ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> lib.Lib.Frame.outside W x) ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= L ->
  lib.Lib.Frame.munch W m m' -> ACtlCutP.FTURN cx j phi regs' m'.
Proof.
  intros cx j phi regs regs' m m' W A L (H224 & H232 & Hb & Hl) HA E9 HA0 HA1 Hout Hlow HL Hm.
  split; [exact (w4b7_spill regs regs' m m' W 224 _ A H224 HA E9 ltac:(lia) HA0 HA1 Hout Hm)|].
  split; [exact (w4b7_spill regs regs' m m' W 232 _ A H232 HA E9 ltac:(lia) HA0 HA1 Hout Hm)|].
  split; [apply (w4b7_bk W m m' _ _ L Hb Hm Hlow); lia | exact Hl].
Qed.

(* REC0: the identity record (38 bytes at fr + 2688) and the fragment record (72 bytes at fr + 2768). *)
Lemma w4b7_rec0 : forall cx fr j m m' W L,
  ACtlCutP.REC0 cx fr j m -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> fr + 4096 <= L ->
  ACtlCutP.REC0 cx fr j m'.
Proof.
  intros cx fr j m m' W L ((Hi & Hok) & (Hg & Hfok)) Hm Hlow HfL.
  unfold ACtlCutP.IDBe, ACtlCutP.FGBe in *.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F7.f7_ID_length (ACtlCut.c_in cx) j) as HIl.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F7.f7_FG_length (ACtlCut.c_in cx) j) as HGl.
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hi) as [H0 _].
  split; split; [| exact Hok | | exact Hfok].
  - apply (w4b7_bk W m m' _ _ L Hi Hm Hlow). rewrite HIl. lia.
  - apply (w4b7_bk W m m' _ _ L Hg Hm Hlow). rewrite HGl. lia.
Qed.

(* FPS: the parse record (36 bytes at fr + 176) and its 36 addressable bytes. *)
Lemma w4b7_fps : forall cx fr j m m' W L,
  ACtlCutP.FPS cx fr j m -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < L -> lib.Lib.Frame.outside W x) -> fr + 4096 <= L -> B.AsanRT.HIGHMEM_BEG <= L ->
  ACtlCutP.FPS cx fr j m'.
Proof.
  intros cx fr j m m' W L (Hb & Ha) Hm Hlow HfL HHL.
  unfold ACtlCutP.pBb in *.
  pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Hb) as [H0 _].
  split; [| exact (w4b7_ak W m m' _ _ L Ha Hm Hlow HHL)].
  apply (w4b7_bk W m m' _ _ L Hb Hm Hlow).
  unfold ACtlCutP.SM.t_B. rewrite ACtlCutP.RPA.ctrlparse_length. lia.
Qed.

Lemma w4b7_flvsp : forall A fr (regs regs' : bvmap 5 word) m m' W,
  ACtlCutP.FLVsp A fr regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x -> lib.Lib.Frame.outside W x) -> lib.Lib.Frame.munch W m m' ->
  ACtlCutP.FLVsp A fr regs' m'.
Proof.
  intros A fr regs regs' m m' W (H9 & H120 & H128 & H256 & H304 & H296) E9 Hout Hm.
  unfold ACtlCutP.q64 in *.
  split; [unfold ACtlCut.rgv in *; rewrite E9; exact H9|].
  split; [apply (w4b7_bkh W m m' _ _ A H120 Hm Hout); lia|].
  split; [apply (w4b7_bkh W m m' _ _ A H128 Hm Hout); lia|].
  split; [apply (w4b7_bkh W m m' _ _ A H256 Hm Hout); lia|].
  split; [apply (w4b7_bkh W m m' _ _ A H304 Hm Hout); lia|].
  apply (w4b7_bkh W m m' _ _ A H296 Hm Hout); lia.
Qed.

(* The geometry of an own6 frame-loop cut: FRAC's spill base and sp, and the bounds that put the frame, phi's
   block and every shadow byte below the callee window [sp - 16, sp). *)
Lemma w4b7_geom : forall cx own k ly3 S3 (W3 : Reusable.YA0n.world segs) (regs3 : bvmap 5 word) mem3 md3 fr sel
    phi n,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  ACtlCutP.FRAC B cx fr sel regs3 mem3 ->
  In (phi, n) (Reusable.YG0d.ablocks B ly3 S3) -> 0 <= n ->
  exists AF sp, ACtlCut.rgv regs3 9 AF /\ lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp /\
    Reusable.YG0d.spZ regs3 = sp /\ ACtlCut.c_sp cx - 4096 < sp /\ sp <= AF /\ AF + 448 <= ACtlCut.c_sp cx /\
    ACtlCut.c_sp cx <= B.AsanRT.APPMEM_END /\ B.AsanRT.HIGHMEM_BEG <= sp - 16 /\ fr + 4096 <= sp - 16 /\
    phi + n <= sp - 16 /\ 0 <= fr.
Proof.
  intros cx own k ly3 S3 W3 regs3 mem3 md3 fr sel phi n HJ Hin6 Hfr HFRAC Hphi Hn.
  pose proof HJ as (HAR & Hly & _).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr) by (apply w4b_fr_ly3; [exact Hly | exact Hfr]).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf0 & Hfc & _).
  rewrite Efr in Hf0, Hfc. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfc.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi n HAR Hphi) as (_ & H4096 & Hbc & _).
  pose proof (Reusable.YCbq.req_size_pos n Hn) as [_ Hrq].
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hsp0 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  destruct HFRAC as (AF & sp & Hr2 & _ & HspZ & _ & _ & Hr9 & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA448 &
    HS4096 & HSapp & _).
  exists AF, sp.
  unfold Reusable.YCfn.LLVMF_STK in Hsp0.
  split; [exact Hr9|]. split; [exact Hr2|]. split; [exact HspZ|].
  split; [exact HS4096|]. split; [exact HspA|]. split; [exact HA448|]. split; [exact HSapp|].
  unfold B.AsanRT.HIGHMEM_BEG.
  split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

(* The callee's stk premise: a sub-range of the journal's stack window is present (wview and mrd defined). *)
Lemma w4b7_stk_win : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
    (Wc : Reusable.YA0n.world segs) memc mdc k lo hi,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 -> 0 <= lo ->
  lib.Lib.Frame.stk B.Img0.rsegs memc lo hi.
Proof.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k lo hi HJ Hlo Hhi Hlo0.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  change (2 ^ 47) with 140737488355328 in H47.
  split; [exact Hlo0|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
  intros a Ha. destruct (Hpres a ltac:(lia)) as [_ (b & Hb)].
  split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

(* After the call the callee window is defined in raw memory (the post's stk, outside the image). *)
Lemma w4b7_nn_of_stk : forall m lo hi, lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> 0x5fe000 <= lo ->
  forall x : word, lo <= bv_unsigned x < hi -> m x <> None.
Proof.
  intros m lo hi (_ & _ & H) Hlo x Hx Hn.
  destruct (H (bv_unsigned x) Hx) as [_ (b & Hb)]. revert Hb.
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hn.
  unfold lib.Lib.PropExec.seg_rom, memory_read.
  destruct (find_segment B.Img0.rsegs (bv_unsigned x) (Z.of_N 1)) as [seg|] eqn:Ef; [|discriminate].
  intros _. pose proof (w4b_find_segment_low _ _ Ef). lia.
Qed.

(* Every address of the kind-name table is a nonzero image address. *)
Lemma w4b7_kna_range : forall v, 0x211e0 <= ACtlCutP.KNA.kind_name_addr v <= 0x213c0.
Proof.
  intros v. unfold ACtlCutP.KNA.kind_name_addr.
  assert (HQ : ACtlCutP.KNA.QMARK = 0x211e0) by reflexivity.
  destruct (v <=? 13); [|rewrite HQ; lia].
  destruct (Nat.lt_ge_cases (Z.to_nat v) (length ACtlCutP.KNA.kind_name_addrs)) as [Hl|Hl];
    [|rewrite (nth_overflow _ _ Hl), HQ; lia].
  pose proof (nth_In _ ACtlCutP.KNA.QMARK Hl) as H.
  revert H. generalize (nth (Z.to_nat v) ACtlCutP.KNA.kind_name_addrs ACtlCutP.KNA.QMARK). intros y H.
  unfold ACtlCutP.KNA.kind_name_addrs in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [subst y; lia|]). destruct H.
Qed.

Lemma w4b7_kna_nz : forall v, bv_eqb (Z_to_bv 64 (ACtlCutP.KNA.kind_name_addr v)) (Z_to_bv 64 0) = false.
Proof.
  intros v. pose proof (w4b7_kna_range v) as Hr.
  unfold bv_eqb. apply Z.eqb_neq. rewrite !lib.Lib.MState.unsigned_lit by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8215c_at j (0x8215c) --S_F7--> B82174_at j.
   S_F7 (Seg/F7.v seg_F7 :419): `bne a0,s8,0x82fa4`; a0 = [[A + 280]] = [fr + 176]; `bne s8,a0,0x82fa4`;
   reac_ctrl_kind_name(v) @0x82170 returning at 0x82174. *)
Lemma seg_F7 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82174_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B8215c_at [Z.of_nat j]).
Proof.
  (* Plan (kept): run F7F.f7_pre_F (0x8215c -> kind_name's entry 0x83d98, ra = 0x82174, a0 = v; SINKS 0x8215c and
     0x82168 not taken: a0 = s8 = v, [fr + 176] = v with 0 <= v < 2^31), composed (evtF_cut) with the callee's closed
     theorem's `_on` form B.Prog.reac_ctrl_kind_name_F.reac_ctrl_kind_name_holds_F_on at lo = sp - 16, one lift (SRr_fevt_hid) over
     RNG_W.  The callee writes only [sp - 16, sp): journal by w4b_aj_munch, the body and ctl_rt by the w4b7_
     transports. *)
  intros POST j H74 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B8215c_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HLK & H18 & H20 & HFM & HFS & HKB & HKA & H248 & HGb &
    HFT & HREC & HFPS & H272 & A & v & HFL & H10 & H24 & Hv & Hq280 & Hu176).
  pose proof HJ as (HAR & Hly & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Hfr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr) by (apply w4b_fr_ly3; [exact Hly | exact Hfr]).
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  pose proof HFT as (_ & _ & _ & Hphil).
  assert (Hfl0 : 0 <= ACtlCutP.flen cx j) by (unfold ACtlCutP.flen; lia).
  destruct (w4b7_geom cx _ k ly3 S3 W3 regs3 mem3 md3 fr fr phi (ACtlCutP.flen cx j) HJ Hin6 Hfr HFRAC Hphi Hfl0)
    as (AF & sp & Hr9 & Hr2 & HspZ & HS4096 & HspA & HA448 & HSapp & HHL & HfL & HphL & Hfr0).
  pose proof HFL as (H9 & H120 & _).
  assert (EA : A = AF).
  { apply (w4b7_base_eq AF A 120 (ACtlCutP.fragb fr + 15) mem3);
      [| unfold B.AsanRT.HIGHMEM_BEG in HHL; lia | unfold B.AsanRT.APPMEM_END in HSapp; lia | lia | exact H120].
    unfold ACtlCut.rgv in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst AF.
  assert (HA0 : 0 <= A) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (HA1 : A + 448 <= 2 ^ 64) by (unfold B.AsanRT.APPMEM_END in HSapp; lia).
  assert (Hw1 : ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= sp - 16) by (unfold Reusable.YCfn.LLVMF_STK; lia).
  assert (Hw2 : sp <= ACtlCut.c_sp cx) by lia.
  assert (Hw3 : 0 <= sp - 16) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (Hw4 : 0x5fe000 <= sp - 16) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (Hout : forall x, A <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  assert (Hout' : forall x, Reusable.YG0d.spZ regs3 <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  assert (Hlow : forall x, 0 <= x < sp - 16 -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  (* the cut's configuration in the run's state form, the walk moved to the canonical map mkR_of regs3 *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8215c_at [Z.of_nat j])) with 0x8215c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8215c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  match goal with
  | |- context [lib.Lib.Frame.mkR _ ?s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
      assert (Esp2 : bv_unsigned s2 = sp)
  end.
  { change (bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp). rewrite Hr2.
    apply lib.Lib.MState.unsigned_lit. unfold B.AsanRT.APPMEM_END in HSapp. lia. }
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (R280 : Lib.ExecF.rng RNG (A + 280) 8)
    by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]).
  assert (R176 : Lib.ExecF.rng RNG (fr + 176) 4)
    by (apply B.ProgBridge.rng_of_visible; eapply w4b_frame_vis;
        [exact HAR | exact Hin6 | rewrite Efr; lia | rewrite Efr, HFB; lia]).
  assert (RIMG : Lib.ExecF.rng RNG 0x10000 0x5ee000)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
  assert (RWIN : Lib.ExecF.rng RNG (sp - 16) 16)
    by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | exact Hw1 | lia]).
  assert (RSH : Lib.ExecF.rng RNG (B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME) 14)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (ctl_kind_name_shadow_vis _ _ _ _ _ HAR)).
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md3 RNG _ (POST cx)).
  - apply B.ProgBridge.fevt_of_evtF.
    eapply Lib.ExecF.evtF_cut.
    + eapply (F7F.f7_pre_F RNG) with (A := A) (kp := fr + 176) (v := v);
        [exact H9 | exact Hq280 | exact H10 | exact H24 | exact Hv | exact Hu176 | exact R280 | exact R176].
    + intros ms1 Hms1. cbv beta in Hms1. subst ms1.
      eapply (B.Prog.reac_ctrl_kind_name_F.reac_ctrl_kind_name_holds_F_on RNG).
      * exact HKB.
      * exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F7.kn_strings_ro mem3 (proj2 (proj2 (proj2 Hrt)))).
      * rewrite Esp2. eapply w4b7_stk_win with (lo := sp - 16) (hi := sp); [exact HJ | exact Hw1 | exact Hw2 | exact Hw3].
      * rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME. lia.
      * rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME, ACtlCutP.KNA.KIND_NAME. lia.
      * exact (proj1 Hrt).
      * exact HKA.
      * intros x Hx. rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME. cbn. split; [|exact I].
        unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in *.
        lia.
      * exact RIMG.
      * rewrite Esp2. exact RWIN.
      * exact RSH.
  - exact (B.ProgBridge.fp_avoids_RNG_W _).
  - intros ms' md' HQ Hhid Hsbm.
    destruct HQ as (a1' & a2' & a3' & m' & Ems & HMU & HWM & _ & HST & HNM).
    subst ms'.
    assert (Ev : bv_unsigned (Z_to_bv 64 v) = v) by (apply lib.Lib.MState.unsigned_lit; lia).
    rewrite Ev in HNM |- *.
    rewrite Esp2 in HMU, HST. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME in HMU.
    replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x82174)) with (Z_to_bv 64 0x82174)
      by (apply bv_eq; vm_compute; reflexivity).
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R3 := R) end.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82174_at [Z.of_nat j])) R3 m' md')
              (POST cx)).
    apply (H74 cx [Z.of_nat j] fr k ly3 S3 W3 R3 m' md' HB).
    + eapply w4b_aj_munch with (lo := sp - 16) (hi := sp);
        [exact HJ | exact Hw1 | exact Hw2 | exact HMU | | exact Hhid | exact Hsbm].
      intros x Hx. exact (w4b7_nn_of_stk m' (sp - 16) sp HST Hw4 x Hx).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82174_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split.
      { exact (w4b7_frac cx fr fr regs3 R3 mem3 m' _ (sp - 16) HFRAC eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl HMU Hout' Hlow HfL HHL). }
      split; [exact Hn|]. split; [exact Hj|].
      split.
      { destruct HHB as [Hp0 HAd]. split; [exact Hp0 | exact (w4b7_ak _ _ _ _ _ _ HAd HMU Hlow HHL)]. }
      split; [exact (w4b7_lk cx fr j regs3 R3 mem3 m' _ A (sp - 16) HLK H9 eq_refl eq_refl HA0 HA1 Hout Hlow
                       HfL HHL HMU HWM)|].
      split; [exact H18|]. split; [exact H20|].
      split; [exact (w4b7_fm cx j phi fr regs3 R3 mem3 m' _ A HFM H9 eq_refl eq_refl eq_refl eq_refl HA0 HA1 Hout
                       HMU)|].
      split; [exact (w4b7_fsj cx fr j regs3 R3 mem3 m' _ (sp - 16) HFS HMU Hlow HfL HHL)|].
      split.
      { apply (w4b7_bk _ mem3 m' _ _ (sp - 16) HKB HMU Hlow).
        change (length ACtlCutP.KNA.kind_name_bytes) with 112%nat.
        unfold ACtlCutP.KNA.KIND_NAME. unfold B.AsanRT.HIGHMEM_BEG in HHL. lia. }
      split; [exact (w4b7_ak _ _ _ _ _ _ HKA HMU Hlow HHL)|].
      split; [exact (w4b7_spill regs3 R3 mem3 m' _ 248 _ A H248 H9 eq_refl ltac:(lia) HA0 HA1 Hout HMU)|].
      split.
      { intros H50. apply (w4b7_bk _ mem3 m' _ _ (sp - 16) (HGb H50) HMU Hlow).
        unfold ACtlCutP.SM.t_g. rewrite ACtlCutP.SM.fr50_length. lia. }
      split; [exact (w4b7_fturn cx j phi regs3 R3 mem3 m' _ A (sp - 16) HFT H9 eq_refl HA0 HA1 Hout Hlow HphL
                       HMU)|].
      split; [exact (w4b7_rec0 cx fr j mem3 m' _ (sp - 16) HREC HMU Hlow HfL)|].
      split; [exact (w4b7_fps cx fr j mem3 m' _ (sp - 16) HFPS HMU Hlow HfL HHL)|].
      split; [exact (w4b7_spill regs3 R3 mem3 m' _ 272 _ A H272 H9 eq_refl ltac:(lia) HA0 HA1 Hout HMU)|].
      exists A, v.
      split; [exact (w4b7_flvsp A fr regs3 R3 mem3 m' _ HFL eq_refl Hout HMU)|].
      split; [exact eq_refl|].
      split; [exact H24|]. split; [exact Hv|].
      split; [apply (w4b7_bkh _ mem3 m' _ _ A Hq280 HMU Hout); lia|].
      apply (w4b7_bk _ mem3 m' _ _ (sp - 16) Hu176 HMU Hlow). rewrite lib.Lib.Mem.length_le4. lia.
    + apply (w4b_ctl_rt_munch _ _ _ mem3 m' Hrt HMU). intros x Hx. cbn. split; [|exact I].
      unfold B.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82174_at j (0x82174) --S_F8--> B82180_at j.
   S_F8 (Seg/F8.v seg_F8 :352): `beqz a0,0x82fa4`; a0 = s8 = v; reac_ctrl_kind_name(v) @0x8217c returning at
   0x82180 with the name's bytes. *)
Lemma seg_F8 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82180_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82174_at [Z.of_nat j]).
Proof.
  (* Plan (kept): SINK 0x82174 (`beqz a0`) not taken: a0 = kind_name_addr v, a nonzero table address
     (w4b7_kna_nz); run F8F.f8_pre_F (0x82174 -> 0x83d98, ra = 0x82180, a0 = v; no memory access) composed with the
     callee's closed theorem exactly as seg_F7; the exit adds the callee's name bytes. *)
  intros POST j H80 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82174_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HLK & H18 & H20 & HFM & HFS & HKB & HKA & H248 & HGb &
    HFT & HREC & HFPS & H272 & A & v & HFL & H10 & H24 & Hv & Hq280 & Hu176).
  pose proof HJ as (HAR & Hly & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Hfr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  pose proof HFT as (_ & _ & _ & Hphil).
  assert (Hfl0 : 0 <= ACtlCutP.flen cx j) by (unfold ACtlCutP.flen; lia).
  destruct (w4b7_geom cx _ k ly3 S3 W3 regs3 mem3 md3 fr fr phi (ACtlCutP.flen cx j) HJ Hin6 Hfr HFRAC Hphi Hfl0)
    as (AF & sp & Hr9 & Hr2 & HspZ & HS4096 & HspA & HA448 & HSapp & HHL & HfL & HphL & Hfr0).
  pose proof HFL as (H9 & H120 & _).
  assert (EA : A = AF).
  { apply (w4b7_base_eq AF A 120 (ACtlCutP.fragb fr + 15) mem3);
      [| unfold B.AsanRT.HIGHMEM_BEG in HHL; lia | unfold B.AsanRT.APPMEM_END in HSapp; lia | lia | exact H120].
    unfold ACtlCut.rgv in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst AF.
  assert (HA0 : 0 <= A) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (HA1 : A + 448 <= 2 ^ 64) by (unfold B.AsanRT.APPMEM_END in HSapp; lia).
  assert (Hw1 : ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= sp - 16) by (unfold Reusable.YCfn.LLVMF_STK; lia).
  assert (Hw2 : sp <= ACtlCut.c_sp cx) by lia.
  assert (Hw3 : 0 <= sp - 16) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (Hw4 : 0x5fe000 <= sp - 16) by (unfold B.AsanRT.HIGHMEM_BEG in HHL; lia).
  assert (Hout : forall x, A <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  assert (Hout' : forall x, Reusable.YG0d.spZ regs3 <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  assert (Hlow : forall x, 0 <= x < sp - 16 -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82174_at [Z.of_nat j])) with 0x82174.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82174) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  match goal with
  | |- context [lib.Lib.Frame.mkR _ ?s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
      assert (Esp2 : bv_unsigned s2 = sp)
  end.
  { change (bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp). rewrite Hr2.
    apply lib.Lib.MState.unsigned_lit. unfold B.AsanRT.APPMEM_END in HSapp. lia. }
  match goal with
  | |- context [lib.Lib.Frame.mkR _ _ _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
      assert (Hnz : bv_eqb a0 (Z_to_bv 64 0) = false)
  end.
  { change (bv_eqb (lib.Reusable.YK11.getr regs3 10) (Z_to_bv 64 0) = false).
    unfold ACtlCut.rgv in H10. rewrite H10. apply w4b7_kna_nz. }
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RIMG : Lib.ExecF.rng RNG 0x10000 0x5ee000)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
  assert (RWIN : Lib.ExecF.rng RNG (sp - 16) 16)
    by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | exact Hw1 | lia]).
  assert (RSH : Lib.ExecF.rng RNG (B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME) 14)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (ctl_kind_name_shadow_vis _ _ _ _ _ HAR)).
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md3 RNG _ (POST cx)).
  - apply B.ProgBridge.fevt_of_evtF.
    eapply Lib.ExecF.evtF_cut.
    + eapply (F8F.f8_pre_F RNG) with (v := v); [exact Hnz | exact H24].
    + intros ms1 Hms1. cbv beta in Hms1. subst ms1.
      eapply (B.Prog.reac_ctrl_kind_name_F.reac_ctrl_kind_name_holds_F_on RNG).
      * exact HKB.
      * exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F7.kn_strings_ro mem3 (proj2 (proj2 (proj2 Hrt)))).
      * rewrite Esp2. eapply w4b7_stk_win with (lo := sp - 16) (hi := sp); [exact HJ | exact Hw1 | exact Hw2 | exact Hw3].
      * rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME. lia.
      * rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME, ACtlCutP.KNA.KIND_NAME. lia.
      * exact (proj1 Hrt).
      * exact HKA.
      * intros x Hx. rewrite Esp2. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME. cbn. split; [|exact I].
        unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in *.
        lia.
      * exact RIMG.
      * rewrite Esp2. exact RWIN.
      * exact RSH.
  - exact (B.ProgBridge.fp_avoids_RNG_W _).
  - intros ms' md' HQ Hhid Hsbm.
    destruct HQ as (a1' & a2' & a3' & m' & Ems & HMU & HWM & _ & HST & HNM).
    subst ms'.
    assert (Ev : bv_unsigned (Z_to_bv 64 v) = v) by (apply lib.Lib.MState.unsigned_lit; lia).
    rewrite Ev in HNM |- *.
    rewrite Esp2 in HMU, HST. unfold ACtlCutP.KNA.REAC_CTRL_KIND_NAME_FRAME in HMU.
    replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x82180)) with (Z_to_bv 64 0x82180)
      by (apply bv_eq; vm_compute; reflexivity).
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R3 := R) end.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82180_at [Z.of_nat j])) R3 m' md')
              (POST cx)).
    apply (H80 cx [Z.of_nat j] fr k ly3 S3 W3 R3 m' md' HB).
    + eapply w4b_aj_munch with (lo := sp - 16) (hi := sp);
        [exact HJ | exact Hw1 | exact Hw2 | exact HMU | | exact Hhid | exact Hsbm].
      intros x Hx. exact (w4b7_nn_of_stk m' (sp - 16) sp HST Hw4 x Hx).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82180_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split.
      { exact (w4b7_frac cx fr fr regs3 R3 mem3 m' _ (sp - 16) HFRAC eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl HMU Hout' Hlow HfL HHL). }
      split; [exact Hn|]. split; [exact Hj|].
      split.
      { destruct HHB as [Hp0 HAd]. split; [exact Hp0 | exact (w4b7_ak _ _ _ _ _ _ HAd HMU Hlow HHL)]. }
      split; [exact (w4b7_lk cx fr j regs3 R3 mem3 m' _ A (sp - 16) HLK H9 eq_refl eq_refl HA0 HA1 Hout Hlow
                       HfL HHL HMU HWM)|].
      split; [exact H18|]. split; [exact H20|].
      split; [exact (w4b7_fm cx j phi fr regs3 R3 mem3 m' _ A HFM H9 eq_refl eq_refl eq_refl eq_refl HA0 HA1 Hout
                       HMU)|].
      split; [exact (w4b7_fsj cx fr j regs3 R3 mem3 m' _ (sp - 16) HFS HMU Hlow HfL HHL)|].
      split.
      { apply (w4b7_bk _ mem3 m' _ _ (sp - 16) HKB HMU Hlow).
        change (length ACtlCutP.KNA.kind_name_bytes) with 112%nat.
        unfold ACtlCutP.KNA.KIND_NAME. unfold B.AsanRT.HIGHMEM_BEG in HHL. lia. }
      split; [exact (w4b7_ak _ _ _ _ _ _ HKA HMU Hlow HHL)|].
      split; [exact (w4b7_spill regs3 R3 mem3 m' _ 248 _ A H248 H9 eq_refl ltac:(lia) HA0 HA1 Hout HMU)|].
      split.
      { intros H50. apply (w4b7_bk _ mem3 m' _ _ (sp - 16) (HGb H50) HMU Hlow).
        unfold ACtlCutP.SM.t_g. rewrite ACtlCutP.SM.fr50_length. lia. }
      split; [exact (w4b7_fturn cx j phi regs3 R3 mem3 m' _ A (sp - 16) HFT H9 eq_refl HA0 HA1 Hout Hlow HphL
                       HMU)|].
      split; [exact (w4b7_rec0 cx fr j mem3 m' _ (sp - 16) HREC HMU Hlow HfL)|].
      split; [exact (w4b7_fps cx fr j mem3 m' _ (sp - 16) HFPS HMU Hlow HfL HHL)|].
      split; [exact (w4b7_spill regs3 R3 mem3 m' _ 272 _ A H272 H9 eq_refl ltac:(lia) HA0 HA1 Hout HMU)|].
      exists A, v.
      split; [exact (w4b7_flvsp A fr regs3 R3 mem3 m' _ HFL eq_refl Hout HMU)|].
      split; [exact eq_refl|].
      split; [exact H24|]. split; [exact Hv|].
      split; [apply (w4b7_bkh _ mem3 m' _ _ A Hq280 HMU Hout); lia|].
      split; [apply (w4b7_bk _ mem3 m' _ _ (sp - 16) Hu176 HMU Hlow); rewrite lib.Lib.Mem.length_le4; lia|].
      exact HNM.
    + apply (w4b_ctl_rt_munch _ _ _ mem3 m' Hrt HMU). intros x Hx. cbn. split; [|exact I].
      unfold B.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   seg_F9's Section hypothesis and helpers (a Theorem Labs lane, helper prefixes w4b9_ / w4b9t_). *)

(* TREPLY -- reac_ctrl_identity_reply @0x821e8 (callee 0x848fc), S_F9's CUT call: the SHARED world spec
   B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (lib/B/Prog/C_reac_ctrl_identity_reply.v:61-118),
   owner a Theorem Labs lane, STATEMENT ONLY (cited by the walk owner a Theorem Labs lane's decision; no other argument). *)
Hypothesis TREPLY : B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec RLO RHI B.

(* The segment bytes of image B lie in [0x10000, 0x5fe000): an address outside has no segment. *)
Lemma w4b9_noseg : forall x, (x < 0x10000 \/ 0x5fe000 <= x) -> find_segment B.Img0.rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment B.Img0.rsegs x 1) as [seg|] eqn:Hf; [exfalso | reflexivity].
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.kb_find_segment B.Img0.rsegs x 1 seg Hf)
    as (Hin & Hb & He).
  assert (H : In (Z.of_N (seg_base seg), Z.of_N (seg_size seg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ seg Hin).
  rewrite B.ProgBridge.rsegs_spans in H.
  remember (Z.of_N (seg_base seg)) as b eqn:Eb. remember (Z.of_N (seg_size seg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

(* Every address of [0x10000, 0x5fe000) is an image byte (the four segments tile it, ProgBridge.rsegs_spans). *)
Lemma w4b9_in_img : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (Hex : exists b z, In (b, z) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s)))
                                         B.Img0.rsegs) /\ b <= a < b + z).
  { rewrite B.ProgBridge.rsegs_spans.
    destruct (Z_lt_le_dec a 200704); [exists 65536, 135168; split; [left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 651264); [exists 200704, 450560; split; [right; left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 663552); [exists 651264, 12288; split; [right; right; left; reflexivity | lia]|].
    exists 663552, 5619712. split; [right; right; right; left; reflexivity | lia]. }
  destruct Hex as (b & z & Hin & Hr). apply in_map_iff in Hin as (sg & E & Hsg). injection E as Eb Ez.
  exists sg. split; [exact Hsg | lia].
Qed.

Lemma w4b9_spq : forall regs m off v A, ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HA0 HA1 Hoff.
  assert (E : A' = A).
  { apply (w4b7_base_eq A A' off v m); [| exact HA0 | exact HA1 | exact Hoff | exact Hq].
    unfold ACtlCut.rgv in HA', HA. rewrite <- HA', <- HA. reflexivity. }
  subst A'. exact Hq.
Qed.

(* Pairwise disjointness of two members of a list (YCbq.pairwise_zdisjoint_split). *)
Lemma w4b9_pw_app : forall L1 L2 (x y : Z * Z), Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint (L1 ++ L2) ->
  In x L1 -> In y L2 -> Reusable.YG0f.zdisjoint x y.
Proof.
  intros L1 L2 x y Hp Hx Hy. apply in_split in Hx as (a & b & ->). apply in_split in Hy as (c & d & ->).
  apply (Reusable.YCbq.pairwise_zdisjoint_split _ x y Hp). exists a, (b ++ c), d. left.
  rewrite <- app_assoc. cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.

(* f9_evtA's six writes (f9_WA) miss an app byte off the three cells, and the shadow byte of an app byte off the
   cells' three granules. *)
Lemma w4b9_f9_app : forall S3 fr x,
  fr = 8 * (S3 - 2147450880) -> 4096 <= fr -> fr + 4096 <= 140737488355328 ->
  (0 <= x < 2147446784 \/ 17594333495296 <= x) ->
  (x < fr + 256 \/ fr + 258 <= x) -> (x < fr + 272 \/ fr + 280 <= x) -> (x < fr + 304 \/ fr + 312 <= x) ->
  lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3 fr) x.
Proof.
  intros S3 fr x H1 H2 H3 H4 H5 H6 H7. cbv [B.Prog.Seg.F9.f9_WA]. cbn [lib.Lib.Frame.outside].
  repeat split; try exact I; lia.
Qed.

Lemma w4b9_f9_sh : forall S3 fr y,
  fr = 8 * (S3 - 2147450880) -> 4096 <= fr -> fr + 4096 <= 140737488355328 ->
  (fr + 4096 <= 2147446784 \/ 17594333495296 <= fr) ->
  (0 <= y < 2147446784 \/ 17594333495296 <= y < 140737488355328) ->
  (y < fr + 256 \/ fr + 264 <= y) -> (y < fr + 272 \/ fr + 280 <= y) -> (y < fr + 304 \/ fr + 312 <= y) ->
  lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3 fr) (B.AsanRT.shadow_addr y).
Proof.
  intros S3 fr y H1 H2 H3 H4 H5 H6 H7 H8. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  cbv [B.Prog.Seg.F9.f9_WA]. cbn [lib.Lib.Frame.outside]. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

(* A byte of a carried byte list is readable. *)
Lemma w4b9_rd : forall m a bs x, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m a bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E.
  - exists b. rewrite <- E. rewrite <- (H (Z.to_nat (x - a)) ltac:(lia)). f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

(* ---- TREPLY glue (helper prefix w4b9t_) ---- *)

(* At a visible address the core's byte reader over the restricted memory is ctrl's mrd (ProgWorld.aview_vis_mrd's
   proof, without the option_map). *)
Lemma w4b9t_mbyte_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict H m) a = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a).
Proof.
  intros H m a Hh. unfold lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd. rewrite Hh. reflexivity.
Qed.

(* A carried byte list at visible addresses is a garr8 over the restricted memory (the spec's P10 message). *)
Lemma w4b9t_garr8 : forall (H : word -> bool) (m : word -> option byte) (a : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> H (Z_to_bv 64 x) = false) ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict H m) a (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros H m a bs (Ha & Hl & Hb) Hv j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned b)
    by (apply nth_error_nth; rewrite nth_error_map, En; reflexivity).
  rewrite Hnth. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
  change (2 ^ 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  rewrite (w4b9t_mbyte_mrd H m (a + Z.of_nat j) (Hv (a + Z.of_nat j) ltac:(lia))).
  specialize (Hb j Hj). unfold lib.Lib.Mem.wa in Hb. rewrite Hb, En. f_equal.
  unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* One shadow byte carried at a visible address q makes a range of its granule addressable in the core's view (the
   spec's P11 range_addressable of a cell). *)
Lemma w4b9t_rad : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (p n q : Z) (bs : list byte)
    (b : byte),
  Reusable.YA0n.w_H W (Z_to_bv 64 q) = false ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m q bs -> nth_error bs 0 = Some b ->
  (forall x, p <= x < p + n -> Reusable.YG0f.SHADOW_OFF + x / 8 = q /\ Reusable.YG0v.saddr_ok x (bv_unsigned b)) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n q bs b Hv (_ & _ & Hb) Hn Hx. unfold Reusable.YG0v.range_addressable. intros x Hr.
  destruct (Hx x Hr) as [Eq Hok].
  exists (bv_unsigned b). split; [|exact Hok].
  unfold Reusable.YG0v.shadow_of_addr. rewrite Eq.
  rewrite (B.ProgWorld.aview_vis_mrd W m q Hv).
  assert (H0 : (0 < length bs)%nat) by (destruct bs; [discriminate Hn | cbn [length]; lia]).
  specialize (Hb 0%nat H0). change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb.
  unfold lib.Lib.Mem.wa in Hb. rewrite Hb, Hn. reflexivity.
Qed.

(* The spec's P11 frame clause of a cell byte: it lies in the owned class-6 frame (cid = 6, stated explicitly) and
   it is an awr_byte through the in_frames arm (own6). *)
Lemma w4b9t_p11 : forall (cx : ACtlCut.ctlcx) ly3 S3 fr (bl0 bl : list (Z * Z)) STK sp0 (FPj : list (Z * Z)) a,
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr -> fr <= a < fr + 4096 ->
  exists cid pos, cid = 6 /\ In (cid, pos) (Reusable.YG01.frames S3) /\
    Reusable.YG0n.in_zr a (Reusable.YCbq.frame_rng ly3 (cid, pos)) /\
    Reusable.YCbq.awr_byte STK sp0 FPj bl0 bl ly3 (ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 S3 fr bl0 bl STK sp0 FPj a Hin Efr Ha. exists 6, (ACtlCut.c_fpos cx).
  assert (Hr : Reusable.YG0n.in_zr a (Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx), Reusable.YG00.fs_frame_bytes 6)).
  { unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  split; [reflexivity|]. split; [exact Hin|]. split; [exact Hr|].
  right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity | left; exact Hr].
Qed.

(* The post's garr8 / val_mem of a cell, at present (visible) bytes, is the cell's rw_cells (f10_RPost). *)
Lemma w4b9t_cb_garr8 : forall (H : word -> bool) (m : word -> option byte) (o : Z) (bs : list byte) (k : nat),
  length bs = k -> 0 <= o -> o + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> Reusable.YG0n.apresent H m (o + i)) ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict H m) o (map (fun b : byte => bv_unsigned b) bs) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m o [lib.Lib.Cells.CB k bs].
Proof.
  intros H m o bs k Hl Ho Hk Hp Hg.
  apply B.ProgWorld.rw_cells_CB_of_present; [exact Hl | exact Ho | exact Hk | |].
  - intros i Hi.
    assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; lia).
    pose proof (lib.Reusable.YI00.garr8_mbyte segs _ _ _ i Hg Hi') as Hv.
    destruct (nth_error bs i) as [b|] eqn:En; [|apply nth_error_None in En; lia].
    assert (Hnth : nth i (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned b)
      by (apply nth_error_nth; rewrite nth_error_map, En; reflexivity).
    rewrite Hnth, Z_to_bv_bv_unsigned in Hv.
    destruct (Hp (Z.of_nat i) ltac:(lia)) as [Hh _].
    rewrite (w4b9t_mbyte_mrd H m (o + Z.of_nat i) Hh) in Hv. exact Hv.
  - intros i Hi. destruct (Hp i Hi) as [_ (b & Hb)]. rewrite Hb. discriminate.
Qed.

Lemma w4b9t_cb_val8 : forall (H : word -> bool) (m : word -> option byte) (o v : Z),
  0 <= o -> o + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> Reusable.YG0n.apresent H m (o + i)) ->
  lib.Reusable.YI04.val_mem segs (Reusable.YK04.mrestrict H m) o 8 v ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m o [lib.Lib.Cells.CB 8 (lib.Lib.Mem.le8 (Z_to_bv 64 v))].
Proof.
  intros H m o v Ho Hk Hp Hv.
  apply B.ProgWorld.rw_cells_CB_of_present; [apply lib.Lib.Mem.length_le8 | exact Ho | exact Hk | |].
  - intros i Hi. specialize (Hv i Hi).
    destruct (Hp (Z.of_nat i) ltac:(lia)) as [Hh _].
    rewrite (w4b9t_mbyte_mrd H m (o + Z.of_nat i) Hh) in Hv. rewrite Hv.
    pose proof (B.ProgWorldCtlRt.le8_eq v v eq_refl) as E8. unfold lib.Lib.Mem.wa in E8. rewrite E8.
    rewrite (B.ProgWorldCtlRt.nth_Z_to_le_bytes 8 v i Hi).
    exact (f_equal Some (B.ProgWorldCtlRt.le_byte_shiftr v 8 i Hi)).
  - intros i Hi. destruct (Hp i Hi) as [_ (b & Hb)]. rewrite Hb. discriminate.
Qed.

(* A core shadow value (saddr_ok, unsigned) passes ctrl's signed shadow check. *)
Lemma w4b9t_sok8 : forall x s, Reusable.YG0v.saddr_ok x s -> B.AsanRT.shadow_ok x (bv_signed (Z_to_bv 8 s)).
Proof.
  intros x s Hok. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
  unfold Reusable.YG0v.saddr_ok in Hok.
  assert (E : bv_signed (Z_to_bv 8 s) = s).
  { assert (Hc : s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6 \/ s = 7) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity. }
  rewrite E. unfold B.AsanRT.shadow_ok. lia.
Qed.

(* A sub-range of a live heap block is addressable at any AR state: AR_shadow_law's block_shadow, read through the
   view (ProgWorldCtlRt.mrd_of_aview).  A heap block's shadow is not a kept class of acall_kept, so the exit reads
   it from the post's AR. *)
Lemma w4b9t_blk_addr : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> 0 <= len -> lo + len <= p + Reusable.YG00.req_size n ->
  B.AsanRT.addressable mem lo len.
Proof.
  intros ly S W mem md p n lo len HAR Hin Hlo Hlen Hhi.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & P4 & Pc & Papp & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
  pose proof (Reusable.YG0v.block_shadow_range _ _ p (Reusable.YG00.req_size n) lo len Hbs Hlo Hhi) as Hra.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _]. unfold Reusable.YG0f.ASAN_CEIL in Hce.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Papp.
  unfold B.AsanRT.addressable. split; [lia|]. split; [exact Hlen|].
  split; [unfold B.AsanRT.APPMEM_END; lia|].
  intros i Hi. destruct (Hra (lo + i) ltac:(lia)) as (s & Hs & Hok).
  unfold B.AsanRT.addr_byte. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
  - exists (Z_to_bv 8 s). split; [|exact (w4b9t_sok8 (lo + i) s Hok)].
    pose proof (B.ProgWorldCtlRt.mrd_of_aview W mem _ s Hs) as Hm.
    replace (B.AsanRT.shadow_addr (lo + i)) with (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (lo + i))
      by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
    exact Hm.
Qed.

(* Present bytes are byte-backed (the twin of w4b11_stk_pres, which comes later in the file). *)
Lemma w4b9t_stk_pres : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Hp a Ha) as [_ (b & Hb)]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* Two-step transports: f9_evtA's raw munch, then the call's kept class C (ctl_post_acall_kept's mrd form). *)
Lemma w4b9t_mrd2 : forall W1 (H : word -> bool) (C : Z -> Prop) m m1 m2 x,
  lib.Lib.Frame.munch W1 m m1 ->
  (forall y : word, H y = false -> C (bv_unsigned y) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m2 y = lib.Lib.Mem.mrd B.Img0.rsegs m1 y) ->
  0 <= x < 2 ^ 64 ->
  (lib.Lib.Frame.outside W1 x /\ C x) /\ H (Z_to_bv 64 x) = false ->
  lib.Lib.Mem.mrd B.Img0.rsegs m2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x).
Proof.
  intros W1 H C m m1 m2 x Hm Hv Hx ((Ho1 & Hc) & Hh).
  assert (Ex : bv_unsigned (lib.Lib.Mem.wa x) = x) by (apply lib.Lib.Mem.wa_unsigned; exact Hx).
  rewrite (Hv (lib.Lib.Mem.wa x) Hh ltac:(rewrite Ex; exact Hc)).
  unfold lib.Lib.Mem.mrd. rewrite (Hm (lib.Lib.Mem.wa x) ltac:(rewrite Ex; exact Ho1)). reflexivity.
Qed.

Lemma w4b9t_bt2 : forall W1 (H : word -> bool) (C : Z -> Prop) m m1 m2 a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W1 m m1 ->
  (forall y : word, H y = false -> C (bv_unsigned y) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m2 y = lib.Lib.Mem.mrd B.Img0.rsegs m1 y) ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     (lib.Lib.Frame.outside W1 x /\ C x) /\ H (Z_to_bv 64 x) = false) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m2 a bs.
Proof.
  intros W1 H C m m1 m2 a bs (H0 & H1 & Hb) Hm Hv Hc. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  apply (w4b9t_mrd2 W1 H C m m1 m2); [exact Hm | exact Hv | lia | apply Hc; lia].
Qed.

Lemma w4b9t_ad2 : forall W1 (H : word -> bool) (C : Z -> Prop) m m1 m2 p n,
  B.AsanRT.addressable m p n -> lib.Lib.Frame.munch W1 m m1 ->
  (forall y : word, H y = false -> C (bv_unsigned y) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m2 y = lib.Lib.Mem.mrd B.Img0.rsegs m1 y) ->
  (forall y, p <= y < p + n ->
     (lib.Lib.Frame.outside W1 (B.AsanRT.shadow_addr y) /\ C (B.AsanRT.shadow_addr y)) /\
     H (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false) ->
  B.AsanRT.addressable m2 p n.
Proof.
  intros W1 H C m m1 m2 p n (H0 & H1 & H2 & Ha) Hm Hv Hc.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (Ha i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  rewrite <- Hb. apply (w4b9t_mrd2 W1 H C m m1 m2); [exact Hm | exact Hv | | apply Hc; lia].
  unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in Happ.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* One-step transports (the call's kept class only, for the bytes f9_evtA wrote). *)
Lemma w4b9t_ad1 : forall (H : word -> bool) (C : Z -> Prop) m m2 p n,
  B.AsanRT.addressable m p n ->
  (forall y : word, H y = false -> C (bv_unsigned y) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m2 y = lib.Lib.Mem.mrd B.Img0.rsegs m y) ->
  (forall y, p <= y < p + n -> C (B.AsanRT.shadow_addr y) /\ H (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false) ->
  B.AsanRT.addressable m2 p n.
Proof.
  intros H C m m2 p n HA Hv Hc.
  apply (w4b9t_ad2 [] H C m m m2 p n HA (lib.Lib.Frame.munch_refl [] m) Hv).
  intros y Hy. destruct (Hc y Hy) as [Hc' Hh]. split; [split; [exact I | exact Hc'] | exact Hh].
Qed.

Lemma w4b9t_mrd1 : forall (H : word -> bool) (C : Z -> Prop) m m2 x,
  (forall y : word, H y = false -> C (bv_unsigned y) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m2 y = lib.Lib.Mem.mrd B.Img0.rsegs m y) ->
  0 <= x < 2 ^ 64 -> C x /\ H (Z_to_bv 64 x) = false ->
  lib.Lib.Mem.mrd B.Img0.rsegs m2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x).
Proof.
  intros H C m m2 x Hv Hx (Hc & Hh).
  assert (Ex : bv_unsigned (lib.Lib.Mem.wa x) = x) by (apply lib.Lib.Mem.wa_unsigned; exact Hx).
  exact (Hv (lib.Lib.Mem.wa x) Hh ltac:(rewrite Ex; exact Hc)).
Qed.

(* S_F9's two runs as one footprint run: F9F.f9_evtA_F (0x82180 -> 0x821e0) joined by ExecF.evtF_cut to
   F9F.f9_evtB_pre_F (0x821e0 -> the reply's entry 0x848fc, ra = 0x821ec), from the cut's canonical register map. *)
Lemma w4b9_run : forall (RNG : Lib.ExecF.footprint) (regs Fr : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (X A S3 fr phi len : Z) (b c0 : byte),
  ACtlCut.rgv regs 9 A -> ACtlCut.rgv regs 10 X -> ACtlCut.rgv regs 18 phi ->
  ACtlCut.rgv regs 19 S3 -> ACtlCut.rgv regs 20 len -> ACtlCut.rgv regs 26 B.AsanRT.ASAN_K ->
  0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
  fr + 3136 <= A -> A + 448 <= 2 ^ 64 -> S3 + 392 <= A -> (S3 + 392 <= fr \/ fr + 3136 <= S3) ->
  ov_read_bytes B.Img0.rsegs m (lib.Lib.Mem.wa (X / 8 + B.AsanRT.ASAN_K)) 1 = Some [b] ->
  (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
  ov_read_bytes B.Img0.rsegs m (lib.Lib.Mem.wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m S3 392 ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m (fr + 256) 2 -> lib.Lib.Mem.wr_at B.Img0.rsegs m (fr + 272) 8 ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m (fr + 304) 8 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (A + 288) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 256))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (A + 304) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 272))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (A + 296) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 304))) ->
  Lib.ExecF.rng RNG (X / 8 + B.AsanRT.ASAN_K) 1 -> Lib.ExecF.rng RNG X 1 ->
  Lib.ExecF.rng RNG (S3 + 32) 1 -> Lib.ExecF.rng RNG (S3 + 34) 1 -> Lib.ExecF.rng RNG (S3 + 38) 1 ->
  Lib.ExecF.rng RNG (A + 288) 8 -> Lib.ExecF.rng RNG (A + 296) 8 -> Lib.ExecF.rng RNG (A + 304) 8 ->
  Lib.ExecF.rng RNG (fr + 256) 2 -> Lib.ExecF.rng RNG (fr + 272) 8 -> Lib.ExecF.rng RNG (fr + 304) 8 ->
  Lib.ExecF.evtF B.Img0.rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte),
       ms' = lib.Lib.MState.MS R Fr (Z_to_bv 64 0x848fc) fc None m1 (lib.Reusable.YK11.seg_rom segs) /\
       ACtlCut.rgv R 1 0x821ec /\
       lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 /\
       lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 /\
       lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 /\
       lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 /\
       ACtlCut.rgv R 9 A /\ ACtlCut.rgv R 10 phi /\ ACtlCut.rgv R 11 len /\ ACtlCut.rgv R 12 (fr + 256) /\
       ACtlCut.rgv R 13 (fr + 272) /\ ACtlCut.rgv R 14 (fr + 304) /\ ACtlCut.rgv R 18 phi /\
       ACtlCut.rgv R 19 S3 /\ ACtlCut.rgv R 20 len /\
       lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs 21 /\
       lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs 22 /\
       lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs 23 /\
       lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs 24 /\
       lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs 25 /\
       ACtlCut.rgv R 26 B.AsanRT.ASAN_K /\
       lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs 27 /\
       lib.Lib.Frame.munch (B.Prog.Seg.F9.f9_WA S3 fr) m m1 /\ lib.Lib.Frame.wmono B.Img0.rsegs m m1 /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (S3 + 32) (lib.Lib.Mem.le1 (Z_to_bv 64 2)) /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (S3 + 34) (lib.Lib.Mem.le1 (Z_to_bv 64 0)) /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (S3 + 38) (lib.Lib.Mem.le1 (Z_to_bv 64 0)) /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (fr + 256) (lib.Lib.Mem.le2 (Z_to_bv 64 0)) /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (fr + 272) (lib.Lib.Mem.le8 (Z_to_bv 64 0)) /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (fr + 304) (lib.Lib.Mem.le8 (Z_to_bv 64 0)) /\
       lib.Lib.Mem.wr_at B.Img0.rsegs m1 (fr + 256) 2 /\ lib.Lib.Mem.wr_at B.Img0.rsegs m1 (fr + 272) 8 /\
       lib.Lib.Mem.wr_at B.Img0.rsegs m1 (fr + 304) 8)
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x82180) fc None m
       (lib.Reusable.YK11.seg_rom segs)).
Proof.
  intros RNG regs Fr fc m X A S3 fr phi len b c0 E9 E10 E18 E19 E20 E26 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 Rsh Rx R32 R34 R38 R288 R296 R304 R256 R272 R304f.
  assert (E9' : Sem.reg_get regs 9 = Z_to_bv 64 A) by exact E9.
  assert (E10' : Sem.reg_get regs 10 = Z_to_bv 64 X) by exact E10.
  assert (E18' : Sem.reg_get regs 18 = Z_to_bv 64 phi) by exact E18.
  assert (E19' : Sem.reg_get regs 19 = Z_to_bv 64 S3) by exact E19.
  assert (E20' : Sem.reg_get regs 20 = Z_to_bv 64 len) by exact E20.
  assert (E26' : Sem.reg_get regs 26 = Z_to_bv 64 B.AsanRT.ASAN_K) by exact E26.
  unfold Lib.Regs6ss.mkR_of. rewrite E9', E10', E18', E19', E20', E26'.
  match goal with |- Lib.ExecF.evtF ?sg ?R ?Q ?ms0 =>
    apply (Lib.ExecF.evtF_cut sg R (fun ms => Lib.ExecF.evtF sg R Q ms) Q ms0); [| intros ms' Hm; exact Hm] end.
  eapply B.Prog.Seg.F9F.f9_evtA_F with (X := X) (A := A) (S3 := S3) (fr := fr) (phi := phi) (len := len)
    (b := b) (c0 := c0); try eassumption.
  intros m1 MU WM _ B32 B34 B38 Ba Bp Bn Wa1 Wp1 Wn1. cbv beta.
  eapply Lib.ExecF.evtF_mono; [apply B.Prog.Seg.F9F.f9_evtB_pre_F |].
  intros ms' ->. eexists _, m1. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  repeat (split; [assumption|]). assumption.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82180_at j (0x82180) --S_F9--> B821ec_at j.
   S_F9 (Seg/F9.v seg_F9 :3462): the checked read of the first name byte (not '?': `bne a1,63` to 0x821b8), the
   three frame shadow bytes of the reply cells and the cells' zero stores, then reac_ctrl_identity_reply(phi, len)
   @0x821e8 returning at 0x821ec.  CUT at the call (the callee's own class-1 fake frame). *)
Lemma seg_F9 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B821ec_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82180_at [Z.of_nat j]).
Proof.
  (* Plan: F9F.f9_evtA_F joined to F9F.f9_evtB_pre_F (w4b9_run), lifted to the reply's entry 0x848fc; the cut call
     by the shared world spec TREPLY (P1 the journal, P2 ctl_base's read-only view carried by
     APostBase.arodata_ok_journalP, P10 / P11 from the run's post: the message as garr8, the cells in the owned
     class-6 frame, their shadow bytes); the exit body at the post world W2: transports across f9_evtA's writes (raw
     munch f9_WA) and the call's kept classes (acall_kept through ProgWorld.ctl_post_acall_kept at W3-visible
     addresses: stack window, owned frame and its shadow, phi's block, image), phi's shadow / the frame's stk / KNT's
     addressability from the post's AR, the cells (f10_RPost) from the post's garr8 / val_mem, ctl_rt_C by
     ProgWorldCtlRtC.ctl_rt_C_of_AR (route (C)).  The first name byte's addressability and its shadow byte's visibility come from
     ctl_kind_name_str_shadow only (no start-up table is read).  SINK 0x821b4 is not reached (first name byte <> '?',
     inside the run). *)
  intros POST j Hec cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82180_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HLK & Hs2 & Hs4 & HFM & HFS & HKNb & HKNa & H248 & HGb &
    HFT & HREC & HFPS & H272 & A & v & HFL & Ha0 & Hs8 & Hv & H280 & Hu32 & Hname).
  pose proof HFL as (H9 & Hq120 & Hq128 & Hq256 & Hq304 & Hq296).
  pose proof HFRAC as (AF & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9F & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & Hq336 & Hq48 & Hq40 & Hhdr & Hent & Hsh & Hsaved & Htrl).
  pose proof HLK as (Hj' & H240 & HOUR & HFLI).
  pose proof HFLI as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 &
    S200 & S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & Hstkfr & HRAD & HKNT & S168b & S88).
  pose proof HFM as (H184 & H24 & H22 & H25 & H312).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  assert (EAF : A = AF).
  { apply (w4b7_base_eq AF A 120 (ACtlCutP.fragb fr + 15) mem3);
      [| lia | unfold B.AsanRT.APPMEM_END in HSapp; lia | lia | exact Hq120].
    unfold ACtlCut.rgv in H9, Hr9F. rewrite <- H9, <- Hr9F. reflexivity. }
  subst AF.
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 448 <= 2 ^ 64) by (unfold B.AsanRT.APPMEM_END in HSapp; lia).
  (* the journal's stack window and the core's ceiling *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  pose proof Hastk as (Hc16 & _ & Hceil & HstkS & HShi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in HstkS.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as [[HAC0 HAC1] _].
  assert (Hspc : lib.Reusable.YM05.alloc_ceiling + 28672 < sp) by lia.
  assert (Hsp47 : sp <= 140737488355328) by (unfold B.AsanRT.APPMEM_END in HSapp; lia).
  (* the owned frame and phi's live block (AR laws) *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4b_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 _ HAR Hin6) as (Fm & Fapp & Fby & Fsh).
  rewrite Efr in Fm. rewrite Efr, HFB6 in Fapp. rewrite Efr, HFB6 in Fby. rewrite Efr, HFB6 in Fsh.
  change (4096 / 8) with 512 in Fsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Fapp.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi)
    as (Pm & P4 & Pc & Papp & Pby & _ & Pn).
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Papp.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as [HN1 HN2].
  destruct (Reusable.YG0d.al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as (Spw & Sfa).
  assert (Hdj : phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) <= fr \/ fr + 4096 <= phi).
  { pose proof (w4b9_pw_app _ _ _ _ Spw
       (in_map (fun b => (fst b, Reusable.YG00.req_size (snd b))) _ _ Hphi)
       (in_map (fun f => (Reusable.YG0f.frame_addr ly3 (fst f) (snd f), Reusable.YG00.fs_frame_bytes (fst f)))
          _ _ Hin6)) as Hz.
    unfold Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Efr, HFB6 in Hz. exact Hz. }
  assert (Hfrc : fr + 4096 <= lib.Reusable.YM05.alloc_ceiling).
  { rewrite Forall_forall in Sfa. destruct (Sfa _ Hin6) as [_ Hc]. cbn [fst snd] in Hc.
    rewrite Efr, HFB6 in Hc. exact Hc. }
  set (N := Reusable.YG00.req_size (ACtlCutP.flen cx j)) in *.
  assert (HNe : N = Reusable.YG00.req_size (ACtlCutP.flen cx j)) by reflexivity.
  assert (Fimg : fr + 4096 <= 65536 \/ 6283264 <= fr).
  { destruct (Z_le_gt_dec (fr + 4096) 65536) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec 6283264 fr) as [Hh|Hh]; [right; exact Hh|]. exfalso.
    apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 _ (Z.max fr 65536) HAR Hin6);
      [rewrite Efr, HFB6; lia | apply w4b9_in_img; lia]. }
  set (S3' := B.AsanRT.shadow_addr fr).
  assert (HS3e : S3' = B.AsanRT.shadow_addr fr) by reflexivity.
  assert (HS3 : fr = 8 * (S3' - 2147450880)).
  { rewrite HS3e. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hfr32. Z.div_mod_to_equations. lia. }
  (* the kind name (the body's v is t_k j, so 0 <= v <= 13) *)
  assert (Ev : v = B.Prog.SlotModel.t_k (ACtlCut.c_in cx) j).
  { pose proof (Prog.RcParse.ctrlparse_kind_range (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
                  (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) as Hkr.
    unfold ACtlCut.rgv in Hs8, H24. apply w4b_lit_inj; [lia | unfold B.Prog.SlotModel.t_k; lia |].
    rewrite <- Hs8, <- H24. reflexivity. }
  assert (Hv13 : 0 <= v <= 13).
  { rewrite Ev. unfold B.Prog.SlotModel.t_k.
    pose proof (Prog.RcParse.ctrlparse_kind_range (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
                  (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)). lia. }
  pose proof (w4b7_kna_range v) as HXr.
  destruct (ctl_kind_name_str_shadow ly3 S3 W3 mem3 md3 v HAR Hv) as (HXa & HXv).
  set (X := B.ACtlCutP.KNA.kind_name_addr v) in *.
  destruct (B.Prog.Seg.F9.sl_shadow1 mem3 X HXa) as (bX & RK & OK & _).
  rewrite Z.shiftr_div_pow2 in RK by lia. change (2 ^ 3) with 8 in RK.
  destruct (B.Prog.Seg.F9.l9_name0 v Hv13) as (c0 & Hc1 & Hc2).
  pose proof (lib.Lib.Mem.bytes_at_ov_read _ mem3 X _ 0 1 Hname
    ltac:(unfold B.ACtlCutP.RKN.cstr_bytes; rewrite length_app; cbn [length]; lia)) as RC0.
  rewrite Hc1 in RC0. cbn [Z.of_nat] in RC0. rewrite Z.add_0_r in RC0.
  (* visibility of the five byte classes the stage reads *)
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Vstk : forall lo len, A <= lo -> lo + len <= ACtlCut.c_sp cx ->
                   B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2. eapply w4b_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | exact H2]. }
  assert (Vfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
                  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2.
    eapply w4b_frame_vis; [exact HAR | exact Hin6 | rewrite Efr; lia | rewrite Efr, HFB6; lia]. }
  assert (Vfrsh : forall y, fr <= y < fr + 4096 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false).
  { intros y Hy. assert (Hi : 0 <= y / 8 - fr / 8 < 512) by (clear - Hy Hfr32; Z.div_mod_to_equations; lia).
    destruct (Fsh _ Hi) as [[Hh _] _].
    replace (B.AsanRT.shadow_addr y) with (Reusable.YG0f.shadow_addr fr + (y / 8 - fr / 8)); [exact Hh|].
    unfold B.AsanRT.shadow_addr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K. lia. }
  assert (Vphi : forall lo len, phi <= lo -> lo + len <= phi + N ->
                   B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2. eapply w4b_heap_vis; [exact HAR | exact Hphi | exact H1 | exact H2]. }
  assert (Vimg : forall x, 65536 <= x < 6283264 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hi). apply Hi.
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI. lia. }
  assert (Vsh : forall c, 0 <= c < 512 -> B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (S3' + c) 1).
  { intros c Hc. split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (B.AsanRT.shadow_addr (fr + 8 * c))
      by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - HS3 Hc Ha; Z.div_mod_to_equations; lia).
    apply Vfrsh. lia. }
  (* the run's footprint and memory premises *)
  assert (Rsh : Lib.ExecF.rng RNG (X / 8 + B.AsanRT.ASAN_K) 1) by exact (B.ProgBridge.rng_of_visible _ _ _ HXv).
  assert (Rx : Lib.ExecF.rng RNG X 1).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply Vimg. lia. }
  assert (Rs32 : Lib.ExecF.rng RNG (S3' + 32) 1) by exact (B.ProgBridge.rng_of_visible _ _ _ (Vsh 32 ltac:(lia))).
  assert (Rs34 : Lib.ExecF.rng RNG (S3' + 34) 1) by exact (B.ProgBridge.rng_of_visible _ _ _ (Vsh 34 ltac:(lia))).
  assert (Rs38 : Lib.ExecF.rng RNG (S3' + 38) 1) by exact (B.ProgBridge.rng_of_visible _ _ _ (Vsh 38 ltac:(lia))).
  assert (R288 : Lib.ExecF.rng RNG (A + 288) 8)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vstk (A + 288) 8 ltac:(lia) ltac:(lia))).
  assert (R296 : Lib.ExecF.rng RNG (A + 296) 8)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vstk (A + 296) 8 ltac:(lia) ltac:(lia))).
  assert (R304 : Lib.ExecF.rng RNG (A + 304) 8)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vstk (A + 304) 8 ltac:(lia) ltac:(lia))).
  assert (R256 : Lib.ExecF.rng RNG (fr + 256) 2)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vfr (fr + 256) 2 ltac:(lia) ltac:(lia))).
  assert (R272 : Lib.ExecF.rng RNG (fr + 272) 8)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vfr (fr + 272) 8 ltac:(lia) ltac:(lia))).
  assert (R304f : Lib.ExecF.rng RNG (fr + 304) 8)
    by exact (B.ProgBridge.rng_of_visible _ _ _ (Vfr (fr + 304) 8 ltac:(lia) ltac:(lia))).
  assert (Wsh : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 S3' 392).
  { (* route (C): the frame shadow from ctl_rt_C's cut_shadow (frames disjunct, the owned frame (6, c_fpos cx)) *)
    destruct Hrt as (_ & Hcut & _ & _). split; [lia|]. split; [lia|]. intros i Hi.
    refine (proj1 (Hcut (S3' + i) _ _)).
    - left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr, HFB6.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. clear - HS3 Hi. Z.div_mod_to_equations. lia.
    - unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
        B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG; lia. }
  assert (Wcell : forall c n, 256 <= c -> c + n <= 3136 -> lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (fr + c) n).
  { intros c n Hc Hcn. destruct Hstkfr as (_ & _ & Hst). split; [lia|]. split; [lia|]. intros i Hi.
    apply (proj1 (Hst (fr + c + i) ltac:(unfold ACtlCutP.FRAME_BYTES; lia))). }
  assert (Q256 : ACtlCutP.q64 mem3 (A + 288) (fr + 256)) by exact (w4b9_spq _ _ 288 _ A S288 H9 HA0 HA1 ltac:(lia)).
  (* ---- the run 0x82180 -> 0x848fc (ra = 0x821ec), lifted ---- *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82180_at [Z.of_nat j])) with 0x82180.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82180) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  pose proof (B.ProgBridge.fevt_of_evtF _ _ _
    (w4b9_run RNG regs3 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 X A S3' fr phi
       (ACtlCutP.flen cx j) bX c0 H9 Ha0 Hs2 Hr19 Hs4 Hr26 ltac:(lia) ltac:(lia) ltac:(lia) HA0 ltac:(lia) HA1
       ltac:(lia) ltac:(lia) RK OK RC0 Hc2 Wsh (Wcell 256 2 ltac:(lia) ltac:(lia))
       (Wcell 272 8 ltac:(lia) ltac:(lia)) (Wcell 304 8 ltac:(lia) ltac:(lia)) Q256 Hq304 Hq296
       Rsh Rx Rs32 Rs34 Rs38 R288 R296 R304 R256 R272 R304f)) as HFSt.
  apply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md3 RNG _ (POST cx) HFSt (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & m1 & Ems & HR1 & HR2 & HR3 & HR4 & HR8 & HR9 & HR10 & HR11 & HR12 & HR13 & HR14 &
    HR18 & HR19 & HR20 & HR21 & HR22 & HR23 & HR24 & HR25 & HR26 & HR27 & MU & WM & B32 & B34 & B38 & Ba & Bp & Bn &
    Wa1 & Wp1 & Wn1).
  subst ms'.
  (* the journal at the call (f9_evtA writes the owned frame's three cells and three of its shadow bytes) *)
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
       (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
       (ACtlCut.own6 cx) ly3 S3 W3 m1 md' k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md'
             (fun a => (S3' + 32 <= a < S3' + 33) \/ (fr + 256 <= a < fr + 258) \/ (S3' + 34 <= a < S3' + 35) \/
                       (fr + 272 <= a < fr + 280) \/ (S3' + 38 <= a < S3' + 39) \/ (fr + 304 <= a < fr + 312)) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity|].
      cbv [B.Prog.Seg.F9.f9_WA]. cbn [lib.Lib.Frame.outside]. repeat split; try exact I; lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Hh; try rewrite Hh in Hx; [exact Hx|].
      destruct (mem3 x) as [b0|] eqn:E3; [|exfalso; exact (Hx eq_refl)].
      intros E1.
      assert (Hw3 : wview B.Img0.rsegs mem3 x <> None) by (unfold wview; rewrite E3; discriminate).
      apply (WM x Hw3). unfold wview. rewrite E1.
      pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
      destruct (Z_lt_le_dec (bv_unsigned x) 65536) as [Hl|Hl];
        [rewrite (w4b9_noseg _ (or_introl Hl)); reflexivity|].
      destruct (Z_lt_le_dec (bv_unsigned x) 6283264) as [Hm|Hm];
        [|rewrite (w4b9_noseg _ (or_intror Hm)); reflexivity].
      exfalso. rewrite (MU x) in E1; [congruence|].
      cbv [B.Prog.Seg.F9.f9_WA]. cbn [lib.Lib.Frame.outside]. repeat split; try exact I; lia.
    - intros x Hx. exact (Hhid x Hx).
    - exact Hsbm.
    - intros a Ha. right. right. right. exists 6, (ACtlCut.c_fpos cx).
      split; [unfold ACtlCut.own6; left; reflexivity|].
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr, HFB6.
      assert (Hd : Reusable.YG0f.shadow_addr fr = S3')
        by (rewrite HS3e; unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr,
              B.AsanRT.ASAN_K; lia).
      rewrite Hd. change (4096 / 8) with 512. lia. }
  (* the three cells addressable after the shadow stores (S(fr) + 32 = 2, + 34 = 0, + 38 = 0) *)
  assert (Happ : forall a, fr <= a < fr + 4096 -> B.AsanRT.app_mem a)
    by (intros a Ha; unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  assert (HRCA1 : ACtlCutP.RCA fr m1).
  { unfold ACtlCutP.RCA. split; [|split].
    - eapply (B.Prog.Seg.F9.l7_addr_cell m1 fr 256 2); [exact Hfr32 | lia | reflexivity | lia | lia
        | intros a Ha; apply Happ; lia | unfold B.AsanRT.APPMEM_END; lia | exact B32 |].
      match goal with |- _ \/ (_ <= bv_signed ?bb <= _) =>
        assert (E : bv_signed bb = 2) by (vm_compute; reflexivity) end. lia.
    - eapply (B.Prog.Seg.F9.l7_addr_cell m1 fr 272 8); [exact Hfr32 | lia | reflexivity | lia | lia
        | intros a Ha; apply Happ; lia | unfold B.AsanRT.APPMEM_END; lia | exact B34 |].
      match goal with |- bv_signed ?bb = 0 \/ _ =>
        assert (E : bv_signed bb = 0) by (vm_compute; reflexivity) end. lia.
    - eapply (B.Prog.Seg.F9.l7_addr_cell m1 fr 304 8); [exact Hfr32 | lia | reflexivity | lia | lia
        | intros a Ha; apply Happ; lia | unfold B.AsanRT.APPMEM_END; lia | exact B38 |].
      match goal with |- bv_signed ?bb = 0 \/ _ =>
        assert (E : bv_signed bb = 0) by (vm_compute; reflexivity) end. lia. }
  (* ---- the cut call: reac_ctrl_identity_reply (the shared world spec TREPLY) ---- *)
  assert (EspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite HR2; exact HspZ).
  assert (Hgp : lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B)).
  { destruct HB as ((HAF & _) & _). destruct HAF as (_ & _ & _ & Hg & _). exact Hg. }
  (* the read-only view: ctl_base's arodata_okS, carried along the journal (P2 here, ctl_rt after the call) *)
  assert (HaroP0 : Reusable.APostBase.arodata_okP segs RLO RHI B
                     (Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))).
  { destruct HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro0 & _) & _).
    exact (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Haro0 (Z.le_refl _) (Z.le_refl _)). }
  pose proof (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG (RO := RO_OFL) B
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 HaroP0) as HaroP1.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs B.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP R m1 md')
            (POST cx)).
  eapply Reusable.YA0n.SRr_bind.
  { apply (TREPLY Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m1 md' k R phi (ACtlCutP.flen cx j)
             (fr + 256) (fr + 272) (fr + 304) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) HJ1 HaroP1).
    - unfold ACtlCut.rgv in HR1. rewrite HR1. unfold lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
    - unfold Reusable.YG0d.raZ. unfold ACtlCut.rgv in HR1. rewrite HR1.
      rewrite lib.Lib.MState.unsigned_lit by lia. lia.
    - rewrite HR3, Hr3. exact Hgp.
    - rewrite HR4. exact Hr4.
    - exact HR10.
    - exact HR11.
    - exact HR12.
    - exact HR13.
    - exact HR14.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite EspR. exact Hsp16.
    - rewrite EspR. unfold B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK, Reusable.YCfn.LLVMF_STK.
      lia.
    - rewrite EspR. lia.
    - rewrite HF. vm_compute. reflexivity.
    - exact (B.Prog.Seg.F7.f7_g_len _ _).
    - (* P10: phi's live block and the message bytes, visible *)
      intros _ H50. split.
      + exists (ACtlCutP.flen cx j). split; [exact Hphi | lia].
      + apply (w4b9t_garr8 (Reusable.YA0n.w_H W3) m1 phi (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
        * apply (w4b_bytes_at_munch _ mem3 m1 phi _ (HGb H50) MU). intros i Hi.
          rewrite B.Prog.Seg.F7.f7_g_len in Hi. apply w4b9_f9_app; lia.
        * intros x Hx. rewrite B.Prog.Seg.F7.f7_g_len in Hx.
          destruct (Vphi x 1 ltac:(lia) ltac:(lia)) as (_ & _ & Hh). apply Hh. lia.
    - (* P11: the three cells, aligned and apart, in the owned class-6 frame, their shadow bytes stored by the run *)
      intros _.
      assert (Hcell : forall a, B.Prog.C_reac_ctrl_identity_reply.treply_out (fr + 256) (fr + 272) (fr + 304) a ->
                        fr <= a < fr + 4096)
        by (intros a Ha; unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ha; lia).
      split; [clear - Hfr32; Z.div_mod_to_equations; lia|].
      split; [clear - Hfr32; Z.div_mod_to_equations; lia|].
      split; [clear - Hfr32; Z.div_mod_to_equations; lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split.
      { intros a Ha.
        destruct (w4b9t_p11 cx ly3 S3 fr (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx))
                    (Reusable.YG0d.ablocks B ly3 S3) Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP a Hin6 Efr
                    (Hcell a Ha))
          as (cid & pos & Ecid & Hinc & Hrc & Haw).
        split; [exists cid, pos; split; [exact Hinc | split; [subst cid; lia | exact Hrc]] | exact Haw]. }
      split; [|split].
      + apply (w4b9t_rad W3 m1 (fr + 256) 2 (S3' + 32) (lib.Lib.Mem.le1 (Z_to_bv 64 2)) (Z_to_bv 8 2)
                 (proj2 (proj2 (Vsh 32 ltac:(lia))) (S3' + 32) ltac:(lia)) B32 eq_refl).
        intros x Hx. split.
        * unfold Reusable.YG0f.SHADOW_OFF. clear - HS3 Hx. Z.div_mod_to_equations. lia.
        * unfold Reusable.YG0v.saddr_ok. right. change (bv_unsigned (Z_to_bv 8 2)) with 2.
          clear - HS3 Hx. Z.div_mod_to_equations. lia.
      + apply (w4b9t_rad W3 m1 (fr + 272) 8 (S3' + 34) (lib.Lib.Mem.le1 (Z_to_bv 64 0)) (Z_to_bv 8 0)
                 (proj2 (proj2 (Vsh 34 ltac:(lia))) (S3' + 34) ltac:(lia)) B34 eq_refl).
        intros x Hx. split.
        * unfold Reusable.YG0f.SHADOW_OFF. clear - HS3 Hx. Z.div_mod_to_equations. lia.
        * unfold Reusable.YG0v.saddr_ok. left. reflexivity.
      + apply (w4b9t_rad W3 m1 (fr + 304) 8 (S3' + 38) (lib.Lib.Mem.le1 (Z_to_bv 64 0)) (Z_to_bv 8 0)
                 (proj2 (proj2 (Vsh 38 ltac:(lia))) (S3' + 38) ltac:(lia)) B38 eq_refl).
        intros x Hx. split.
        * unfold Reusable.YG0f.SHADOW_OFF. clear - HS3 Hx. Z.div_mod_to_equations. lia.
        * unfold Reusable.YG0v.saddr_ok. left. reflexivity. }
  intros W2 c2 _ (Hwle & ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hpres & HF2 & HP2 & Ha0' & HAK & Hcells).
  subst c2.
  unfold B.Prog.C_reac_ctrl_identity_reply.EV_REPLY in HJ2. rewrite Z.add_0_r in HJ2.
  rewrite EspR in HAK.
  set (ok := Prog.RcReply.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
               (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) in *.
  (* the call's kept classes (acall_kept): a W3-visible byte of a kept class reads the same after the call *)
  pose (KC := fun x => B.ProgWorld.kept_class B ly3 S3 (sp - 9072) sp
                (fun a => ok = true /\ B.Prog.C_reac_ctrl_identity_reply.treply_out (fr + 256) (fr + 272) (fr + 304) a)
                x).
  assert (HKV : forall x : word, Reusable.YA0n.w_H W3 x = false -> KC (bv_unsigned x) ->
                  lib.Lib.Mem.mrd B.Img0.rsegs mem2 x = lib.Lib.Mem.mrd B.Img0.rsegs m1 x)
    by exact (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m1 mem2 (sp - 9072) sp _ HAK Hwle).
  (* the transportable classes: outside f9_evtA's writes, of a kept class, and visible at W3 (each arithmetic side
     condition in a cleared context: the case splits of the disjunctive facts stay local) *)
  assert (Hfr4 : 4096 <= fr) by (clear - Fapp; lia).
  assert (Hfrlh : fr + 4096 <= 2147446784 \/ 17594333495296 <= fr) by (clear - Fapp; lia).
  assert (HACh : 17594333495296 <= lib.Reusable.YM05.alloc_ceiling) by (clear - HAC0; lia).
  assert (HACs : lib.Reusable.YM05.alloc_ceiling + 9072 <= sp) by (clear - Hspc; lia).
  assert (Hfr47 : fr + 4096 <= 140737488355328) by (clear - Hfrc HAC1; lia).
  assert (Hcsp : ACtlCut.c_sp cx <= 140737488355328) by (clear - HShi H47; lia).
  assert (KS : forall x, A <= x < ACtlCut.c_sp cx ->
     (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) x /\ KC x) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. split; [split|].
    - apply w4b9_f9_app; clear - HS3 Hfr4 Hfr47 Hx HspA HACs HACh Hfrc; lia.
    - unfold KC; cbv beta; unfold B.ProgWorld.kept_class. left. clear - Hx HspA HACs Hcsp. lia.
    - destruct (Vstk x 1 ltac:(clear - Hx; lia) ltac:(clear - Hx; lia)) as (_ & _ & Hh).
      apply Hh. clear - Hx. lia. }
  assert (KF : forall x, fr <= x < fr + 4096 -> (x < fr + 256 \/ fr + 312 <= x) ->
     (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) x /\ KC x) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx Hc. split; [split|].
    - apply w4b9_f9_app; clear - HS3 Hfr4 Hfr47 Hfrlh Hx Hc; lia.
    - unfold KC; cbv beta; unfold B.ProgWorld.kept_class. right. right. right.
      exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      + left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr, HFB6.
        clear - Hx. lia.
      + intros (_ & Ht). unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ht. clear - Hx Hc Ht. lia.
    - destruct (Vfr x 1 ltac:(clear - Hx; lia) ltac:(clear - Hx; lia)) as (_ & _ & Hh).
      apply Hh. clear - Hx. lia. }
  assert (KCsh : forall y, fr <= y < fr + 4096 -> KC (B.AsanRT.shadow_addr y)).
  { intros y Hy. unfold KC; cbv beta; unfold B.ProgWorld.kept_class. right. right. right.
    exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr, HFB6. change (4096 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      clear - Hy Hfr32. Z.div_mod_to_equations. lia.
    - intros (_ & Ht).
      unfold B.Prog.C_reac_ctrl_identity_reply.treply_out, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ht.
      clear - Hy Ht Hfr4 Hfrlh Hfr47. Z.div_mod_to_equations. lia. }
  assert (KFS : forall y, fr <= y < fr + 4096 ->
     (y < fr + 256 \/ fr + 264 <= y) -> (y < fr + 272 \/ fr + 280 <= y) -> (y < fr + 304 \/ fr + 312 <= y) ->
     (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) (B.AsanRT.shadow_addr y) /\ KC (B.AsanRT.shadow_addr y)) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false).
  { intros y Hy H1 H2 H3. split; [split|].
    - apply (w4b9_f9_sh S3' fr y HS3 Hfr4 Hfr47 Hfrlh ltac:(clear - Hy Hfr4 Hfrlh Hfr47; lia) H1 H2 H3).
    - exact (KCsh y Hy).
    - apply Vfrsh. exact Hy. }
  assert (KFS2 : forall y, fr <= y < fr + 4096 ->
     KC (B.AsanRT.shadow_addr y) /\ Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false)
    by (intros y Hy; exact (conj (KCsh y Hy) (Vfrsh y Hy))).
  assert (KP : forall x, phi <= x < phi + N ->
     (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) x /\ KC x) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. split; [split|].
    - apply w4b9_f9_app; clear - HS3 Hfr4 Hfr47 Hx Papp P4 Hdj HNe; lia.
    - unfold KC; cbv beta; unfold B.ProgWorld.kept_class. right. left.
      exists phi, (ACtlCutP.flen cx j), (x - phi). split; [exact Hphi|]. split; [clear - Hx HNe; lia|].
      split; [lia|]. intros (_ & Ht). unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ht.
      clear - Hx Ht Hdj HNe. lia.
    - destruct (Vphi x 1 ltac:(clear - Hx; lia) ltac:(clear - Hx; lia)) as (_ & _ & Hh).
      apply Hh. clear - Hx. lia. }
  assert (KK : forall x, 652672 <= x < 652784 ->
     (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) x /\ KC x) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
  { intros x Hx. split; [split|].
    - apply w4b9_f9_app; clear - HS3 Hfr4 Hfr47 Hx Fimg; lia.
    - unfold KC; cbv beta; unfold B.ProgWorld.kept_class. right. right. left.
      assert (HkN : B.ACtlCutP.KNA.KIND_NAME <= x < B.ACtlCutP.KNA.KIND_NAME + 112)
        by (change B.ACtlCutP.KNA.KIND_NAME with 652672; clear - Hx; lia).
      destruct (ctl_kind_name_not_owned x HkN) as [Ho He].
      split; [apply w4b9_in_img; clear - Hx; lia|]. split; [exact Ho | exact He].
    - apply Vimg. clear - Hx. lia. }
  (* the disjunctive facts are no longer needed: keep lia's case splits small *)
  clear Fapp Papp Hdj Fimg Hfrlh Hc2.
  (* the transports *)
  assert (TB : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs ->
     (forall x, a <= x < a + Z.of_nat (length bs) ->
        (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) x /\ KC x) /\
        Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false) ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs)
    by (intros a bs H Hc; exact (w4b9t_bt2 _ (Reusable.YA0n.w_H W3) KC mem3 m1 mem2 a bs H MU HKV Hc)).
  assert (TA : forall p n, B.AsanRT.addressable mem3 p n ->
     (forall y, p <= y < p + n ->
        (lib.Lib.Frame.outside (B.Prog.Seg.F9.f9_WA S3' fr) (B.AsanRT.shadow_addr y) /\
         KC (B.AsanRT.shadow_addr y)) /\
        Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr y)) = false) ->
     B.AsanRT.addressable mem2 p n)
    by (intros p n H Hc; exact (w4b9t_ad2 _ (Reusable.YA0n.w_H W3) KC mem3 m1 mem2 p n H MU HKV Hc)).
  assert (TQ : forall off v0, 0 <= off <= 440 -> ACtlCutP.q64 mem3 (A + off) v0 -> ACtlCutP.q64 mem2 (A + off) v0).
  { intros off v0 Hoff Hq. unfold ACtlCutP.q64 in *. apply TB; [exact Hq|].
    intros x Hx. rewrite lib.Lib.Mem.length_le8 in Hx. apply KS. clear - Hx Hoff HA448. lia. }
  assert (TFr : forall c bs, 0 <= c -> c + Z.of_nat (length bs) <= 256 \/ 312 <= c ->
     c + Z.of_nat (length bs) <= 4096 ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (fr + c) bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + c) bs).
  { intros c bs Hq0 Hq1 Hq2 H. apply TB; [exact H|]. intros x Hx. apply KF; clear - Hx Hq0 Hq1 Hq2; lia. }
  assert (TFA : forall c n, 0 <= c -> 0 <= n -> c + n <= 4096 ->
     (c + n <= 256 \/ 264 <= c) -> (c + n <= 272 \/ 280 <= c) -> (c + n <= 304 \/ 312 <= c) ->
     B.AsanRT.addressable mem3 (fr + c) n -> B.AsanRT.addressable mem2 (fr + c) n).
  { intros c n Hq0 Hn0 Hq1 Hq2 Hq3 Hq4 H. apply TA; [exact H|]. intros y Hy.
    apply KFS; clear - Hy Hq0 Hn0 Hq1 Hq2 Hq3 Hq4; lia. }
  (* the callee-saved registers *)
  assert (GP : forall r : Z, Reusable.YG0d.acallee_saved r ->
     lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr R (Z_to_bv 5 r)) by exact Hpres.
  assert (G2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- HR2; exact (GP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- HR3; exact (GP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- HR4; exact (GP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- HR8; exact (GP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9).
  { unfold ACtlCut.rgv in HR9, H9. rewrite H9, <- HR9. exact (GP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (G18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18).
  { unfold ACtlCut.rgv in HR18, Hs2. rewrite Hs2, <- HR18.
    exact (GP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (G19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19).
  { transitivity (lib.Reusable.YK11.getr R 19); [exact (GP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    unfold ACtlCut.rgv in HR19, Hr19. rewrite HR19, Hr19. reflexivity. }
  assert (G20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20).
  { transitivity (lib.Reusable.YK11.getr R 20); [exact (GP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    unfold ACtlCut.rgv in HR20, Hs4. rewrite HR20, Hs4. reflexivity. }
  assert (G22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by (rewrite <- HR22; exact (GP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (rewrite <- HR24; exact (GP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- HR25; exact (GP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26).
  { transitivity (lib.Reusable.YK11.getr R 26); [exact (GP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    unfold ACtlCut.rgv in HR26, Hr26. rewrite HR26, Hr26. reflexivity. }
  assert (G27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
    by (rewrite <- HR27; exact (GP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (TSP : forall off v0, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v0 -> ACtlCutP.spill regs2 mem2 off v0).
  { intros off v0 Hoff Hs. exists A. split; [unfold ACtlCut.rgv; rewrite G9; exact H9|].
    exact (TQ off v0 Hoff (w4b9_spq _ _ _ _ A Hs H9 HA0 HA1 ltac:(clear - Hoff; lia))). }
  (* the post's AR: the owned frame present, phi's block live *)
  pose proof HJ2 as (HAR2 & Hly2 & _).
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite HF2; exact Hin6).
  assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4b_fr_ly3; [exact Hly2 | apply HL; left; reflexivity]).
  assert (Fpr2 : forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W2) mem2 a).
  { intros a Ha. destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 _ HAR2 Hin62) as (_ & _ & Fby2 & _).
    exact (proj1 (Fby2 a ltac:(rewrite Efr2, HFB6; exact Ha))). }
  assert (Hphi2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym HP2) Hphi).
  (* ---- the exit cut C_B821ec_at, at the post world W2 ---- *)
  assert (HR1' : lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x821ec) by exact HR1.
  rewrite HR1'.
  change (Reusable.YA0n.SRr segs W2
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B821ec_at [Z.of_nat j])) regs2 mem2 md2)
            (POST cx)).
  apply (Hec cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - exact HJ2.
  - rewrite HF2. exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B821ec_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    exists phi.
    split; [exact (Permutation_trans HP2 HP)|].
    split.
    { (* FRAC *)
      unfold ACtlCutP.FRAC. exists A, sp.
      split; [rewrite G2; exact Hr2|]. split; [exact Hsp16|].
      split; [unfold Reusable.YG0d.spZ; rewrite G2; exact HspZ|]. split; [rewrite G4; exact Hr4|].
      split; [unfold ACtlCut.rgv; rewrite G8; exact Hr8|]. split; [unfold ACtlCut.rgv; rewrite G9; exact H9|].
      split; [rewrite G3; exact Hr3|]. split; [unfold ACtlCut.rgv; rewrite G19; exact Hr19|].
      split; [unfold ACtlCut.rgv; rewrite G26; exact Hr26|].
      split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAS|]. split; [exact HspA|].
      split; [unfold ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA448|]. split; [exact HS4096|].
      split; [exact HSapp|].
      split; [exact (TQ 336 _ ltac:(lia) Hq336)|]. split; [exact (TQ 48 _ ltac:(lia) Hq48)|].
      split; [exact (TQ 40 _ ltac:(lia) Hq40)|].
      split; [unfold ACtlCutP.q64 in *; rewrite <- (Z.add_0_r fr) at 1; apply TFr;
              [lia | rewrite lib.Lib.Mem.length_le8; lia | rewrite lib.Lib.Mem.length_le8; lia
              | rewrite Z.add_0_r; exact Hhdr]|].
      split; [unfold ACtlCutP.q64 in *; apply TFr;
              [lia | rewrite lib.Lib.Mem.length_le8; lia | rewrite lib.Lib.Mem.length_le8; lia | exact Hent]|].
      split.
      { destruct Hsh as (sh0 & Hsh0 & Hlsh).
        unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hlsh |- *.
        change (Z.to_nat (3136 / 8)) with 392%nat in Hlsh |- *.
        assert (Hshb : forall y, 0 <= y < 140737488355328 -> 0 <= B.AsanRT.shadow_addr y < 2 ^ 64)
          by (intros y Hy; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hy; Z.div_mod_to_equations; lia).
        assert (Hrd : forall i : nat, (i < 392)%nat ->
                  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa (S3' + Z.of_nat i)) = Some b).
        { intros i Hi.
          assert (Ey : S3' + Z.of_nat i = B.AsanRT.shadow_addr (fr + 8 * Z.of_nat i)).
          { rewrite HS3e. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hfr32. Z.div_mod_to_equations. lia. }
          set (y := fr + 8 * Z.of_nat i) in *.
          assert (Hy : fr <= y < fr + 4096) by (unfold y; lia).
          rewrite Ey.
          destruct (Z.eq_dec (Z.of_nat i) 32) as [E32|N32];
            [| destruct (Z.eq_dec (Z.of_nat i) 34) as [E34|N34];
               [| destruct (Z.eq_dec (Z.of_nat i) 38) as [E38|N38]]].
          - rewrite (w4b9t_mrd1 (Reusable.YA0n.w_H W3) KC m1 mem2 (B.AsanRT.shadow_addr y) HKV (Hshb y ltac:(lia))
                       (KFS2 y Hy)).
            apply (w4b9_rd _ _ _ _ B32). rewrite lib.Lib.Mem.length_le1. rewrite <- Ey. lia.
          - rewrite (w4b9t_mrd1 (Reusable.YA0n.w_H W3) KC m1 mem2 (B.AsanRT.shadow_addr y) HKV (Hshb y ltac:(lia))
                       (KFS2 y Hy)).
            apply (w4b9_rd _ _ _ _ B34). rewrite lib.Lib.Mem.length_le1. rewrite <- Ey. lia.
          - rewrite (w4b9t_mrd1 (Reusable.YA0n.w_H W3) KC m1 mem2 (B.AsanRT.shadow_addr y) HKV (Hshb y ltac:(lia))
                       (KFS2 y Hy)).
            apply (w4b9_rd _ _ _ _ B38). rewrite lib.Lib.Mem.length_le1. rewrite <- Ey. lia.
          - assert (Hy1 : y < fr + 256 \/ fr + 264 <= y) by (unfold y; lia).
            assert (Hy2 : y < fr + 272 \/ fr + 280 <= y) by (unfold y; lia).
            assert (Hy3 : y < fr + 304 \/ fr + 312 <= y) by (unfold y; lia).
            rewrite (w4b9t_mrd2 _ (Reusable.YA0n.w_H W3) KC mem3 m1 mem2 (B.AsanRT.shadow_addr y) MU HKV
                       (Hshb y ltac:(lia)) (KFS y Hy Hy1 Hy2 Hy3)).
            apply (w4b9_rd _ _ _ _ Hsh0). rewrite Hlsh. rewrite <- Ey. change (ACtlCutP.Sfr fr) with S3'. lia. }
        destruct (B.Prog.Seg.F9.f9_bytes_ex mem2 392 S3' ltac:(lia) ltac:(lia) Hrd) as (sh2 & Hb2 & Hl2).
        exists sh2. split; [exact Hb2 | exact Hl2]. }
      split.
      { apply TB; [exact Hsaved|]. intros x Hx.
        assert (Ls : length (ACtlCutP.saved_bytes cx) = 104%nat)
          by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
        rewrite Ls in Hx. apply KS. lia. }
      unfold ACtlCutP.q64 in *. apply TFr;
        [lia | rewrite lib.Lib.Mem.length_le8; lia | rewrite lib.Lib.Mem.length_le8; lia | exact Htrl]. }
    split.
    { (* f10_K *)
      unfold ACtlCutP.f10_K.
      split; [exact Hn|]. split; [exact Hj|].
      split.
      { (* phi's shadow is not a kept class of the call: from the post's AR *)
        destruct HHB as (Hphi0 & _). split; [exact Hphi0|].
        exact (w4b9t_blk_addr ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) phi (B.ACtlK.a_size (ACtlCutP.flen cx j))
                 HAR2 Hphi2 (Z.le_refl _) ltac:(unfold B.ACtlK.a_size; lia) ltac:(unfold B.ACtlK.a_size; lia)). }
      split.
      { (* LK *)
        unfold ACtlCutP.LK. split; [exact Hj'|]. split; [exact (TSP 240 _ ltac:(lia) H240)|].
        split.
        { unfold ACtlCutP.OURb in *.
          apply TFr; [lia | lia | | exact HOUR].
          unfold B.Prog.SlotModel.OUR. rewrite length_map, length_seq. lia. }
        unfold ACtlCutP.FLI.
        split; [unfold ACtlCut.rgv; rewrite G27; exact H27|].
        split; [exact (TSP 168 _ ltac:(lia) S168)|]. split; [exact (TSP 96 _ ltac:(lia) S96)|].
        split; [exact (TSP 112 _ ltac:(lia) S112)|]. split; [exact (TSP 120 _ ltac:(lia) S120)|].
        split; [exact (TSP 128 _ ltac:(lia) S128)|]. split; [exact (TSP 136 _ ltac:(lia) S136)|].
        split; [exact (TSP 144 _ ltac:(lia) S144)|]. split; [exact (TSP 152 _ ltac:(lia) S152)|].
        split; [exact (TSP 280 _ ltac:(lia) S280)|]. split; [exact (TSP 160 _ ltac:(lia) S160)|].
        split; [exact (TSP 176 _ ltac:(lia) S176)|]. split; [exact (TSP 192 _ ltac:(lia) S192)|].
        split; [exact (TSP 200 _ ltac:(lia) S200)|]. split; [exact (TSP 216 _ ltac:(lia) S216)|].
        split; [exact (TSP 208 _ ltac:(lia) S208)|]. split; [exact (TSP 104 _ ltac:(lia) S104)|].
        split; [exact (TSP 256 _ ltac:(lia) S256)|]. split; [exact (TSP 264 _ ltac:(lia) S264)|].
        split; [exact (TSP 288 _ ltac:(lia) S288)|]. split; [exact (TSP 296 _ ltac:(lia) S296)|].
        split; [exact (TSP 304 _ ltac:(lia) S304)|].
        split; [exact (TFA 2624 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HA2624)|].
        split.
        { (* the frame body's stk: the owned frame is present at the post (its AR) *)
          unfold ACtlCutP.FRAME_BYTES in *.
          apply (w4b9t_stk_pres (Reusable.YA0n.w_H W2) mem2 fr (fr + 3136)); [lia | lia |].
          intros a Ha. apply Fpr2. lia. }
        split.
        { unfold ACtlCutP.RAD in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
          split; [exact (TFA 2688 38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ra1)|].
          split; [unfold ACtlCutP.fragb in *;
                  exact (TFA 2768 72 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ra2)|].
          exact (TFA 2880 40 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ra3). }
        split.
        { unfold ACtlCutP.KNT in *. destruct HKNT as (Hk1 & _).
          split; [| exact (ctl_kind_name_addressable _ _ _ _ _ HAR2)].
          apply TB; [exact Hk1|]. intros x Hx.
          assert (Lk : length B.ACtlCutP.KNA.kind_name_bytes = 112%nat) by reflexivity.
          rewrite Lk in Hx. change B.ACtlCutP.KNA.KIND_NAME with 652672 in Hx. apply KK. lia. }
        split; [exact (TSP 168 _ ltac:(lia) S168b)|]. exact (TSP 88 _ ltac:(lia) S88). }
      split.
      { exists A. split.
        - unfold ACtlCutP.FLVsp. split; [unfold ACtlCut.rgv; rewrite G9; exact H9|].
          split; [exact (TQ 120 _ ltac:(lia) Hq120)|]. split; [exact (TQ 128 _ ltac:(lia) Hq128)|].
          split; [exact (TQ 256 _ ltac:(lia) Hq256)|]. split; [exact (TQ 304 _ ltac:(lia) Hq304)|].
          exact (TQ 296 _ ltac:(lia) Hq296).
        - split; [lia|].
          split; [exact (TQ 288 _ ltac:(lia) Q256)|].
          split; [exact (TQ 176 _ ltac:(lia) (w4b9_spq _ _ 176 _ A S176 H9 HA0 HA1 ltac:(lia)))|].
          split; [exact (TQ 200 _ ltac:(lia) (w4b9_spq _ _ 200 _ A S200 H9 HA0 HA1 ltac:(lia)))|].
          split; [exact (TQ 208 _ ltac:(lia) (w4b9_spq _ _ 208 _ A S208 H9 HA0 HA1 ltac:(lia)))|].
          split; [exact (TQ 248 _ ltac:(lia) (w4b9_spq _ _ 248 _ A H248 H9 HA0 HA1 ltac:(lia)))|].
          exact (TQ 312 _ ltac:(lia) (w4b9_spq _ _ 312 _ A H312 H9 HA0 HA1 ltac:(lia))). }
      split; [unfold ACtlCut.rgv; rewrite G18; exact Hs2|].
      split; [unfold ACtlCut.rgv; rewrite G20; exact Hs4|].
      split; [unfold ACtlCut.rgv; rewrite G25; exact H25|].
      split; [unfold ACtlCut.rgv; rewrite G24; exact H24|].
      split; [exact (TSP 184 _ ltac:(lia) H184)|].
      split; [unfold ACtlCut.rgv; rewrite G22; exact H22|].
      unfold Prog.RcReply.reply_args.
      replace (phi =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (fr + 256 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (fr + 272 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (fr + 304 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      reflexivity. }
    split.
    { (* FSj *)
      unfold ACtlCutP.FSj, ACtlCutP.FSb in *. destruct HFS as (Hh1 & Hn1 & Hb1 & Had1 & HFI1).
      pose proof (B.Prog.Seg.F7.f7_body_length (ACtlCut.c_in cx) j) as Hbl.
      unfold ACtlCutP.u32, ACtlCutP.b8 in *.
      split; [apply TFr; [lia | rewrite lib.Lib.Mem.length_le4; lia | rewrite lib.Lib.Mem.length_le4; lia
                         | exact Hh1]|].
      split; [apply TFr; [lia | cbn [length]; lia | cbn [length]; lia | exact Hn1]|].
      split; [apply TFr; [lia | lia | lia | exact Hb1]|].
      split; [exact (TFA 2880 40 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Had1)|].
      exact HFI1. }
    split.
    { intros H50. apply TB; [exact (HGb H50)|]. intros x Hx.
      rewrite B.Prog.Seg.F7.f7_g_len in Hx. apply KP. lia. }
    split; [exact Ha0'|].
    split.
    { (* the three cells, from the post's garr8 / val_mem at the present (visible) frame bytes *)
      intros Hok. destruct (Hcells Hok) as (Hg & Hvp & Hvn).
      unfold ACtlCutP.f10_RPost. split; [|split].
      - apply (w4b9t_cb_garr8 (Reusable.YA0n.w_H W2) mem2 (fr + 256)
                 (Prog.RcReply.reply_addr (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) 2 eq_refl
                 ltac:(lia) ltac:(lia)); [|exact Hg].
        intros i Hi. apply Fpr2. lia.
      - apply (w4b9t_cb_val8 (Reusable.YA0n.w_H W2) mem2 (fr + 272) (phi + 38) ltac:(lia) ltac:(lia)); [|exact Hvp].
        intros i Hi. apply Fpr2. lia.
      - apply (w4b9t_cb_val8 (Reusable.YA0n.w_H W2) mem2 (fr + 304)
                 (Prog.RcReply.ir_s (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) - 13) ltac:(lia) ltac:(lia));
          [|exact Hvn].
        intros i Hi. apply Fpr2. lia. }
    split.
    { (* FTURN *)
      unfold ACtlCutP.FTURN in *. destruct HFT as (T224 & T232 & Tphi & Tlen).
      split; [exact (TSP 224 _ ltac:(lia) T224)|]. split; [exact (TSP 232 _ ltac:(lia) T232)|].
      split; [| exact Tlen]. apply TB; [exact Tphi|]. intros x Hx. apply KP.
      unfold ACtlCutP.flen in *. lia. }
    split.
    { (* REC0 *)
      unfold ACtlCutP.REC0, ACtlCutP.FREC, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGb, ACtlCutP.FGBe in *.
      destruct HREC as ((Hi1 & Hi2) & (Hg1 & Hg2)).
      pose proof (B.Prog.Seg.F7.f7_ID_length (ACtlCut.c_in cx) j) as LI.
      pose proof (B.Prog.Seg.F7.f7_FG_length (ACtlCut.c_in cx) j) as LG.
      split; split; [| exact Hi2 | | exact Hg2].
      - apply TFr; [lia | rewrite LI; lia | rewrite LI; lia | exact Hi1].
      - apply TFr; [lia | rewrite LG; lia | rewrite LG; lia | exact Hg1]. }
    split.
    { (* FPS *)
      unfold ACtlCutP.FPS, ACtlCutP.pBb in *. destruct HFPS as (Hp1 & Hp2).
      assert (LB : length (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j) = 36%nat)
        by (unfold B.Prog.SlotModel.t_B; apply Prog.RcParse.ctrlparse_length).
      split; [apply TFr; [lia | rewrite LB; lia | rewrite LB; lia | exact Hp1]|].
      exact (TFA 176 36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp2). }
    split; [exact (TSP 272 _ ltac:(lia) H272)|].
    (* RCA: the cells addressable at m1 (step 1's shadow stores), across the call (the owned frame's shadow) *)
    unfold ACtlCutP.RCA in *. destruct HRCA1 as (Rc1 & Rc2 & Rc3).
    split; [apply (w4b9t_ad1 (Reusable.YA0n.w_H W3) KC m1 mem2 _ _ Rc1 HKV); intros y Hy; apply KFS2; lia|].
    split; [apply (w4b9t_ad1 (Reusable.YA0n.w_H W3) KC m1 mem2 _ _ Rc2 HKV); intros y Hy; apply KFS2; lia|].
    apply (w4b9t_ad1 (Reusable.YA0n.w_H W3) KC m1 mem2 _ _ Rc3 HKV); intros y Hy; apply KFS2; lia.
  - (* ctl_rt_C at the post (route (C)): a Theorem Labs lane's proved ctl_rt_C_of_AR on the post journal's AR *)
    assert (HaroP2 : Reusable.APostBase.arodata_okP segs RLO RHI B
                       (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2))
      by exact (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG (RO := RO_OFL) B
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HaroP0).
    exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2 HaroP2).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B821ec_at j (0x821ec) --S_F10--> B8226c_at j | B82308_at j.
   S_F10 (Seg/F10.v seg_F10 :189, inline, no call, no memory write): the checks on the reply result and cells. *)
Lemma seg_F10 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8226c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82308_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B821ec_at [Z.of_nat j]).
Proof.
  (* Plan (kept): run F10F.seg_F10_ok_F (reply_ret = 1, -> 0x8226c) or F10F.seg_F10_ne_F (reply_ret = 0, -> 0x82308);
     no write, so the journal moves by the model's materialization only, and ctl_rt / frames / k are unchanged.
     Every SINK / TRAP of 0x821ec-0x82268 is a not-taken step of the run, its premise from the body. *)
  intros POST j H6c H08 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B821ec_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & HK & HFS & HGb & Ha0 & Hpost & HFT & HREC & HFPS & H272 & HRCA).
  pose proof HK as (Hn & Hj & HHB & HLK & (A & HFL & HA & Hq288 & Hq176 & Hq200 & Hq208 & Hq248 & Hq312) &
    Hs2 & Hs4 & Hs9 & Hs8 & Hs184 & Hs6 & Hargs).
  pose proof HFL as (H9 & Hq120 & Hq128 & Hq256 & Hq304 & Hq296).
  pose proof HFRAC as (AF & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9F & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  assert (EAF : AF = A).
  { apply w4b_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | exact HA |].
    unfold ACtlCut.rgv in Hr9F, H9. rewrite <- Hr9F, <- H9. reflexivity. }
  subst AF.
  (* the world facts of the cut *)
  pose proof HJ as (HAR & Hly & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4b_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  (* the cut's configuration in the run's state form, the walk moved to the canonical map mkR_of regs3 *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B821ec_at [Z.of_nat j])) with 0x821ec.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x821ec) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  destruct (Prog.RcReply.ir (ACtlCutP.flen cx j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) eqn:Hir.
  - (* ---- reply_ret = 1 (reply_ok): fall through to 0x8226c ---- *)
    assert (Hok : Prog.RcReply.reply_ok phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = true)
      by (unfold Prog.RcReply.reply_ok; rewrite Hargs, Hir; reflexivity).
    assert (Hr1 : Prog.RcReply.reply_ret phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = 1)
      by (unfold Prog.RcReply.reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr1 in Ha0.
    pose proof (Hpost Hok) as HRP. pose proof HRP as (RWa & RWp & RWn).
    destruct (Prog.RcReply.ir_bytes _ _ Hir) as (H50 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & Hbs & _).
    assert (Hbig : B.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true)
      by (unfold B.Prog.SlotModel.t_big; apply Z.leb_le; exact H50).
    assert (Hsum : B.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j = true).
    { unfold B.Prog.SlotModel.t_sum_ok. rewrite Hbig. unfold Prog.RcReply.ir_blk in Hbs.
      unfold ACtlCutP.flen in Hbs. rewrite Hbs. reflexivity. }
    rewrite Hbig in Hq312. rewrite Hsum in Hs9.
    pose proof (HGb H50) as HG.
    pose proof HHB as (Hphi0 & HAd).
    pose proof HAd as (Hp0 & _ & Hpe & _).
    unfold B.ACtlK.a_size, B.AsanRT.APPMEM_END in Hpe. rewrite Z.max_l in Hpe by lia.
    assert (Hglen : length (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = 50%nat).
    { unfold B.Prog.SlotModel.t_g, B.Prog.SlotModel.fr50. rewrite length_firstn, length_app, repeat_length. lia. }
    pose proof (w4b_bytes_at_nth mem3 phi (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 26 HG ltac:(lia)) as Hb26.
    change (Z.of_nat 26) with 26 in Hb26.
    pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as [_ Hrq].
    set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
    assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    assert (Hpb : 0 < phi /\ phi + 64 <= 2 ^ 64) by lia.
    assert (Hlen : 50 <= ACtlCutP.flen cx j < 2 ^ 64) by lia.
    assert (Hirs : 13 <= Prog.RcReply.ir_s (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) <= 23) by lia.
    assert (R296 : Lib.ExecF.rng RNG (A + 296) 8)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]).
    assert (R304 : Lib.ExecF.rng RNG (A + 304) 8)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]).
    assert (R312 : Lib.ExecF.rng RNG (A + 312) 8)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]).
    assert (Rpp : Lib.ExecF.rng RNG (fr + 272) 8)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_frame_vis;
          [exact HAR | exact Hin6 | rewrite Efr; lia | rewrite Efr, HFB; lia]).
    assert (Rpn : Lib.ExecF.rng RNG (fr + 304) 8)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_frame_vis;
          [exact HAR | exact Hin6 | rewrite Efr; lia | rewrite Efr, HFB; lia]).
    assert (Rsh : Lib.ExecF.rng RNG (Z.shiftr (phi + 26) 3 + B.AsanRT.ASAN_K) 1)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_heap_sh1; [exact HAR | exact Hphi | lia]).
    assert (R26 : Lib.ExecF.rng RNG (phi + 26) 1)
      by (apply B.ProgBridge.rng_of_visible; eapply w4b_heap_vis; [exact HAR | exact Hphi | lia | lia]).
    pose proof (B.ProgBridge.fevt_of_evtF _ _ _ (F10F.seg_F10_ok_F lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr RNG regs3 mem3
      A phi (ACtlCutP.flen cx j) (fr + 272) (fr + 304) (Prog.RcReply.ir_s (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))
      (nth 26 (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) Prog.RcParse.cp_z)
      Ha0 Hs2 Hs4 H9 Hr26 Hs6 Hs9 Hpb Hlen Hirs
      Hq304 Hq296 Hq312 (w4b_lrw8 _ _ _ RWp) (w4b_lrw8 _ _ _ RWn)
      (w4b_sh26 mem3 phi (ACtlCutP.flen cx j) HAd H50) Hb26 eq_refl
      R296 R304 R312 Rpp Rpn Rsh R26)) as HFSt.
    apply (Reusable.YA0nR.SRr_fevt segs w4b_wx W3 _ md3 RNG _ (POST cx) HFSt (B.ProgBridge.fp_avoids_RNG_W _)).
    intros ms' md' HQ Hsbm.
    destruct HQ as (R & pc' & mem' & Ems & Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR19 & HR21 & HR22 & HR24 & HR25 &
      HR27 & HR9 & HR26 & HR18 & HR20 & HR11).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8226c_at [Z.of_nat j])) R mem3 md')
              (POST cx)).
    apply (H6c cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B8226c_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact (eq_trans HR9 (eq_sym H9)).
      exists phi.
      split; [exact HP|].
      split.
      { apply (w4b_frac_move cx fr fr regs3 R mem3 HFRAC);
          [exact HR2 | exact HR3 | exact HR4 | exact HR8 | exact E9 | exact HR19 | exact (eq_trans HR26 (eq_sym Hr26))]. }
      split.
      { apply (w4b_f10K_move cx j phi fr regs3 R mem3 HK);
          [exact E9 | exact (eq_trans HR18 (eq_sym Hs2)) | exact (eq_trans HR20 (eq_sym Hs4))
          | exact HR22 | exact HR24 | exact HR25 | exact HR27]. }
      split; [exact HFS|].
      split; [lia|]. split; [lia|]. split; [exact H50|]. split; [exact Hsum|]. split; [exact HG|].
      split; [exact Hok|]. split; [exact HRP|]. split; [exact HR11|].
      split; [exact (w4b_fturn_move cx j phi regs3 R mem3 HFT E9)|].
      split; [exact HREC|]. split; [exact HFPS|].
      split; [exact (w4b_f272_move cx j regs3 R mem3 H272 E9)|].
      exact HRCA.
    + exact Hrt.
  - (* ---- reply_ret = 0 (ir false): `bne a0,s6` taken to 0x82308 ---- *)
    assert (Hr0 : Prog.RcReply.reply_ret phi (ACtlCutP.flen cx j) (fr + 256) (fr + 272) (fr + 304)
                    (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = 0)
      by (unfold Prog.RcReply.reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr0 in Ha0.
    pose proof (B.ProgBridge.fevt_of_evtF _ _ _ (F10F.seg_F10_ne_F lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr w4b_RNG0 regs3 mem3
                              Ha0 Hs6)) as HFSt.
    apply (Reusable.YA0nR.SRr_fevt segs w4b_wx W3 _ md3 w4b_RNG0 _ (POST cx) HFSt (w4b_fp_RNG0 _)).
    intros ms' md' HQ Hsbm.
    destruct HQ as (R & pc' & mem' & Ems & Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR20 & HR21 &
      HR22 & HR24 & HR25 & HR26 & HR27).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82308_at [Z.of_nat j])) R mem3 md')
              (POST cx)).
    apply (H08 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82308_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split; [apply (w4b_frac_move cx fr fr regs3 R mem3 HFRAC);
               [exact HR2 | exact HR3 | exact HR4 | exact HR8 | exact HR9 | exact HR19 | exact HR26]|].
      split; [apply (w4b_f10K_move cx j phi fr regs3 R mem3 HK);
               [exact HR9 | exact HR18 | exact HR20 | exact HR22 | exact HR24 | exact HR25 | exact HR27]|].
      split; [exact HFS|]. split; [exact HGb|]. split; [exact Hir|].
      split; [exact (w4b_fturn_move cx j phi regs3 R mem3 HFT HR9)|].
      split.
      { (* RECR = REC0 on the ir-false arm: t_IDr j = rp_id (t_ID j) .. = t_ID j (F10.v f10_rec0_recr) *)
        unfold ACtlCutP.RECR, ACtlCutP.REC0, B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.rp_id.
        unfold ACtlCutP.flen in Hir. rewrite Hir. exact HREC. }
      split; [exact HFPS|].
      split; [exact (w4b_f272_move cx j regs3 R mem3 H272 HR9)|].
      exact HRCA.
    + exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Helpers (prefix w4b11_): memory transports across the two callee write sets of S_F11, the record lengths
   of the turn model, the shadow facts of the record bytes, and the journal across the two windows. *)

(* A sub-list of a byte list (Seg/F11.v f11_nth_sub / f11_sub, over lib/Lib). *)
Lemma w4b11_nth_sub : forall (l : list byte) k n i, (i < n)%nat ->
  nth_error (firstn n (skipn k l)) i = nth_error l (k + i).
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l n i Hi.
  - cbn [skipn Nat.add]. revert n i Hi. induction l as [|x l IHl]; intros n i Hi.
    + rewrite firstn_nil. destruct i; reflexivity.
    + destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IHl. lia.
  - destruct l as [|x l].
    + rewrite skipn_nil, firstn_nil. destruct i; reflexivity.
    + cbn [skipn Nat.add nth_error]. apply IH. exact Hi.
Qed.

Lemma w4b11_sub : forall m a (bs : list byte) k n, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (k + n <= length bs)%nat -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite w4b11_nth_sub by exact Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

(* Byte values, and the u16 of the reply address cell (Seg/F11.v f11_ubv / f11_le2). *)
Lemma w4b11_ubv : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma w4b11_le2 : forall b0 b1 : byte,
  [b0; b1] = lib.Lib.Mem.le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)).
Proof.
  intros b0 b1. pose proof (w4b11_ubv b0) as R0. pose proof (w4b11_ubv b1) as R1.
  unfold lib.Lib.Mem.le2. rewrite lib.Lib.MState.unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b0 + 256 * bv_unsigned b1) / 256) with (bv_unsigned b1)
    by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    change (2 ^ 8) with 256.
  - rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The shadow byte of phi + c (7 <= c <= 42) is 0 when the heap block (phi, L), 50 <= L, is addressable
   (Seg/F11.v f11_sh; the twin of w4b_sh26). *)
Lemma w4b11_shc : forall m phi L c, B.AsanRT.addressable m phi (B.ACtlK.a_size L) -> 50 <= L -> 7 <= c <= 42 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (Z.shiftr (phi + c) 3 + B.AsanRT.ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L c HA HL Hc.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + c) 8 ltac:(lia)) as Hr.
  assert (H8 : B.AsanRT.addressable m (phi + (c - (phi + c) mod 8)) 8)
    by (apply (B.AsanRTFacts.addressable_sub m phi (B.ACtlK.a_size L));
        [exact HA | lia | lia | unfold B.ACtlK.a_size; lia]).
  destruct (B.AsanRTFacts.meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (c - (phi + c) mod 8)) 3 = Z.shiftr (phi + c) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + c) 8 ltac:(lia)) as D.
    replace (phi + (c - (phi + c) mod 8)) with ((phi + c) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* The shadow byte of an application byte is a shadow address. *)
Lemma w4b11_sh_in : forall a, B.AsanRT.app_mem a -> B.AsanRT.in_shadow (Z.shiftr a 3 + B.AsanRT.ASAN_K).
Proof.
  intros a Ha. assert (Ha0 : 0 <= a)
    by (unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in Ha; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. exact (B.AsanRTFacts.shadow_of_app a Ha).
Qed.

(* Cells: the bytes of a CB cell; the cell of a writable byte range (Seg/F11.v f11_cb_bytes / f11_cb_rw /
   f11_wr_of_stk / f11_stk_tr / f11_present, over lib/Lib). *)
Lemma w4b11_cb_bytes : forall m a n bs,
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros m a n bs [[_ H] _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

Lemma w4b11_cb_rw : forall m a n bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> length bs = n ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m a (Z.of_nat n) -> lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes].
    rewrite app_nil_r. exact Hb.
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma w4b11_wr_of_stk : forall m m' lo hi a n, lib.Lib.Frame.stk B.Img0.rsegs m lo hi ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> lo <= a -> a + n <= hi -> 0 <= n -> lib.Lib.Mem.wr_at B.Img0.rsegs m' a n.
Proof.
  intros m m' lo hi a n (H0 & H1 & H) WM Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. apply WM. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

Lemma w4b11_stk_tr : forall W m m' lo hi,
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m m' ->
  (forall x, lo <= x < hi -> lib.Lib.Frame.outside W x \/
     (exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some b)) ->
  lib.Lib.Frame.stk B.Img0.rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HK.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb).
  split; [exact (WM (lib.Lib.Mem.wa a) Hw)|].
  destruct (HK a Ha) as [Ho|Hp].
  - exists b. unfold lib.Lib.Mem.mrd in *. rewrite (MU (lib.Lib.Mem.wa a)); [exact Hb|].
    unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia. exact Ho.
  - exact Hp.
Qed.

Lemma w4b11_present : forall m a bs q, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa q) = Some b.
Proof.
  intros m a bs q (Ha & Hl & H) Hq.
  assert (Hk : (Z.to_nat (q - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (q - a)) Hk) as HH.
  replace (a + Z.of_nat (Z.to_nat (q - a))) with q in HH by lia.
  destruct (nth_error bs (Z.to_nat (q - a))) as [b|] eqn:Eb.
  - exists b. exact HH.
  - apply nth_error_None in Eb. lia.
Qed.

(* The image segments tile [0x10000, 0x5fe000) (ProgBridge.rsegs_spans). *)
Lemma w4b11_in_img : forall x, 0x10000 <= x < 0x5fe000 -> Reusable.YG0d.in_img segs x.
Proof.
  intros x Hx.
  assert (HS : forall b z, In (b, z) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs) ->
               b <= x < b + z -> Reusable.YG0d.in_img segs x).
  { intros b z Hin Hb. apply in_map_iff in Hin as (s & Es & Hs). injection Es as Eb Ez.
    exists s. split; [exact Hs | lia]. }
  rewrite B.ProgBridge.rsegs_spans in HS.
  destruct (Z_lt_le_dec x 0x31000); [apply (HS 0x10000 0x21000); [left; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0x9f000); [apply (HS 0x31000 0x6e000); [right; left; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0xa2000); [apply (HS 0x9f000 0x3000); [right; right; left; reflexivity | lia]|].
  apply (HS 0xa2000 0x55c000); [right; right; right; left; reflexivity | lia].
Qed.

(* A byte that find_segment places in a segment is an image byte. *)
Lemma w4b11_fseg_img : forall x seg, find_segment B.Img0.rsegs x 1 = Some seg -> Reusable.YG0d.in_img segs x.
Proof.
  intros x seg Hf.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.kb_find_segment B.Img0.rsegs x 1 seg Hf)
    as (Hin & Hb & He).
  exists seg. split; [exact Hin | lia].
Qed.

(* A byte list carried outside a munch's write set survives it (range form of w4b_bytes_at_munch). *)
Lemma w4b11_bmv : forall W m m' a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof. intros W m m' a bs H Hm Ho. apply (w4b_bytes_at_munch W m m' a bs H Hm). intros i Hi. apply Ho. lia. Qed.

Lemma w4b11_qmv : forall W m m' a v, ACtlCutP.q64 m a v -> lib.Lib.Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> lib.Lib.Frame.outside W x) -> ACtlCutP.q64 m' a v.
Proof.
  intros W m m' a v H Hm Ho. unfold ACtlCutP.q64 in *. apply (w4b11_bmv W m m' a _ H Hm).
  rewrite lib.Lib.Mem.length_le8. exact Ho.
Qed.

(* A spill word sits at the spill base A that register 9 holds (A < 2^63, so the spill's own base is A). *)
Lemma w4b11_spill_q : forall (regs : bvmap 5 word) m off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 63 -> 0 <= off <= 440 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold ACtlCut.rgv in *; rewrite <- HA', <- HA; reflexivity).
  pose proof Hq as (Hq0 & Hq1 & _). unfold ACtlCutP.q64 in Hq1. rewrite lib.Lib.Mem.length_le8 in Hq1.
  assert (EA : A' = A).
  { apply (f_equal bv_unsigned) in E. rewrite lib.Lib.MState.unsigned_lit_wrap in E.
    rewrite (lib.Lib.MState.unsigned_lit A) in E by lia.
    destruct (Z_lt_le_dec A' 0) as [Hn|Hn].
    - rewrite <- (Z.mod_add A' 1 (2 ^ 64)) in E by lia. rewrite Z.mod_small in E by lia. lia.
    - rewrite Z.mod_small in E by lia. exact E. }
  subst A'. exact Hq.
Qed.

(* A spill moves to a register map with the same base and a memory that keeps the spill area. *)
Lemma w4b11_spmv : forall W (regs R : bvmap 5 word) m m' off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 63 -> 0 <= off <= 440 ->
  ACtlCut.rgv R 9 A -> lib.Lib.Frame.munch W m m' ->
  (forall x, A <= x < A + 448 -> lib.Lib.Frame.outside W x) -> ACtlCutP.spill R m' off v.
Proof.
  intros W regs R m m' off v A Hs HA H0 H1 Hoff HR Hm Ho. exists A. split; [exact HR|].
  apply (w4b11_qmv W m m' _ _ (w4b11_spill_q regs m off v A Hs HA H0 H1 Hoff) Hm).
  intros x Hx. apply Ho. lia.
Qed.

(* The shadow bytes survive a munch that misses every shadow address; so does every addressable fact. *)
Lemma w4b11_meta : forall W m m', lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) -> B.AsanRTFacts.meta_kept m m'.
Proof.
  intros W m m' Hm Ho a Ha. unfold lib.Lib.Mem.mrd.
  destruct (B.AsanRTFacts.in_shadow_range a Ha) as [R0 R1].
  rewrite (Hm (lib.Lib.Mem.wa a)); [reflexivity|]. rewrite lib.Lib.Mem.wa_unsigned by lia. exact (Ho a Ha).
Qed.

Lemma w4b11_amv : forall W m m' p n, B.AsanRT.addressable m p n -> lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) -> B.AsanRT.addressable m' p n.
Proof. intros W m m' p n H Hm Ho. exact (B.AsanRTFacts.addressable_kept m m' p n H (w4b11_meta W m m' Hm Ho)). Qed.

(* ctl_rt_C survives a munch that misses every image byte and every shadow byte (w4b_ctl_rt_munch, with the image
   and the shadow in place of the whole range below HIGHMEM_BEG: S_F11 also writes an owned-frame range). *)
Lemma w4b11_rt_mv : forall ly S W m m',
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch W m m' ->
  (forall x, Reusable.YG0d.in_img segs x \/ B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S W m m' (Hc & Hs & Him & Hr) Hm Ho.
  assert (Hb : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> 0x10000 <= a ->
                 a + Z.of_nat (length bs) <= 0x5fe000 -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H Hl0 Hl. apply (w4b11_bmv W m m' a bs H Hm). intros x Hx.
    apply Ho. left. apply w4b11_in_img. lia. }
  assert (Hx : forall x : word, Reusable.YG0d.in_img segs (bv_unsigned x) \/ B.AsanRT.in_shadow (bv_unsigned x) ->
                 m' x = m x).
  { intros x Hx. apply Hm. apply Ho. exact Hx. }
  assert (Hsh : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').
  { intros P HP a Hp Ha.
    assert (Ea : m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)).
    { apply Hx. right. destruct (B.AsanRTFacts.in_shadow_range a Ha) as [R0 R1].
      rewrite lib.Lib.Mem.wa_unsigned by lia. exact Ha. }
    unfold wview, lib.Lib.Mem.mrd. rewrite Ea. exact (HP a Hp Ha). }
  split; [|split; [exact (Hsh _ Hs) | split; [exact (Hsh _ Him) |]]].
  - unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells in *.
    destruct Hc as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
    refine (conj (Hb _ _ C1 _ _) (conj (Hb _ _ C2 _ _) (conj (Hb _ _ C3 _ _) (conj (Hb _ _ C4 _ _)
      (conj (Hb _ _ C5 _ _) (conj (Hb _ _ C6 _ _) (conj (Hb _ _ C7 _ _) (conj (Hb _ _ C8 _ _)
      (conj (Hb _ _ C9 _ _) (conj (Hb _ _ C10 _ _) (conj (Hb _ _ C11 _ _) (conj (Hb _ _ C12 _ _)
      (conj (Hb _ _ C13 _ _) (conj (Hb _ _ C14 _ _) (conj (Hb _ _ C15 _ _) (conj (Hb _ _ C16 _ _)
      (Hb _ _ C17 _ _)))))))))))))))));
      cbn [length]; rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4;
      unfold B.AsanRT.CELL_K, B.AsanRT.GOT_CELL_K, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.GOT_REPLACE,
        B.AsanRT.UAR, B.AsanRT.GOT_UAR, B.AsanRT.CANPOISON, B.AsanRT.HIEND, B.AsanRT.GOT_HIEND, B.AsanRT.MIDBEG,
        B.AsanRT.GOT_MIDBEG, B.AsanRT.MIDEND, B.AsanRT.GOT_MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
        B.AsanRT.GOT_REAL_MEMSET; cbn; lia.
  - unfold B.ACtlK.ro_agree_at in *. intros a Ha.
    assert (Ea : m' a = m a).
    { apply Hx. left. unfold lib.Lib.Mem.ro_addr in Ha.
      destruct (find_segment B.Img0.rsegs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
      exact (w4b11_fseg_img _ _ Ef). }
    unfold lib.Lib.Mem.mrd. rewrite Ea. exact (Hr a Ha).
Qed.

(* The record lengths of the turn model: the first-fragment body (<= 23), the identity record (38) and the
   fragment record (72) (Seg/F13.v fst_body_len, Seg/F16.v t_ID_length, Seg/Tac_ro.v tr_FG_length). *)
Lemma w4b11_body_len : forall inp j,
  (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j));
    cbn [B.Prog.SlotModel.fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold B.Prog.SlotModel.t_g. rewrite B.Prog.SlotModel.fr50_length. lia.
Qed.

Lemma w4b11_ID_len : forall inp j, length (B.Prog.SlotModel.t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold B.Prog.SlotModel.t_ID in *. rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
  assert (Hr : length (B.Prog.SlotModel.rp_id (B.Prog.SlotModel.fs_id (B.Prog.SlotModel.fst_at inp j))
                 (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j)) = 38%nat).
  { unfold B.Prog.SlotModel.rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply lib.Prog.RcIdentModel.ING_length; exact IH | exact IH]. }
  assert (Hf : length (B.Prog.SlotModel.fg_id (B.Prog.SlotModel.rp_id (B.Prog.SlotModel.fs_id
                 (B.Prog.SlotModel.fst_at inp j)) (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j))
                 (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.fs_fg (B.Prog.SlotModel.fst_at inp j))
                 (B.Prog.SlotModel.t_g inp j)) = 38%nat).
  { unfold B.Prog.SlotModel.fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply lib.Prog.RcIdentModel.ING_length; exact Hr | exact Hr]. }
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j));
    cbn [B.Prog.SlotModel.fs_id]; exact Hf.
Qed.

Lemma w4b11_first_len : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= lib.Prog.RcFrag.fg_n g <= 22 ->
  length (lib.Prog.RcFrag.fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold lib.Prog.RcFrag.fg_first, lib.Prog.RcFrag.fg_body.
  rewrite !length_app, length_skipn, (lib.Prog.RcFragLib.rf_bsl_length g 6 6),
    (lib.Prog.RcFragLib.rf_bsl_length g 27 (lib.Prog.RcFrag.fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma w4b11_next_len : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (B.Prog.SlotModel.fg_next st g (lib.Prog.RcFrag.fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold lib.Prog.RcFrag.fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0));
    [cbn [B.Prog.SlotModel.fg_next]; exact HL|].
  destruct (lib.Prog.RcFrag.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [B.Prog.SlotModel.fg_next]; exact HL].
  assert (Hn : 1 <= lib.Prog.RcFrag.fg_n g <= 22).
  { unfold lib.Prog.RcFrag.fg_fr in FR. rewrite !andb_true_iff in FR.
    destruct FR as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia. }
  destruct (lib.Prog.RcFrag.bat g 19 =? 1).
  - cbn [B.Prog.SlotModel.fg_next]. apply w4b11_first_len; assumption.
  - destruct (lib.Prog.RcFrag.fg_keep st g) eqn:KEEP; cbn [negb];
      [|cbn [B.Prog.SlotModel.fg_next]; apply lib.Prog.RcFragLib.rf_clear_length; exact HL].
    assert (HT : lib.Prog.RcFrag.fg_T st g <= 64).
    { unfold lib.Prog.RcFrag.fg_keep in KEEP. rewrite !andb_true_iff in KEEP. destruct KEEP as (_ & KEEP).
      apply Z.leb_le in KEEP. lia. }
    destruct (lib.Prog.RcFrag.fg_close st g); cbn [negb B.Prog.SlotModel.fg_next];
      apply lib.Prog.RcFragLib.rf_clear_length, lib.Prog.RcFragLib.rf_fg_join_length; assumption.
Qed.

Lemma w4b11_FG_len : forall inp j, length (B.Prog.SlotModel.t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold B.Prog.SlotModel.t_FG in *. rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn.
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j));
    cbn [B.Prog.SlotModel.fs_fg]; unfold B.Prog.SlotModel.fg_st, B.Prog.SlotModel.fcls;
    apply (w4b11_next_len 1 1 1 1 1); solve [exact IH | unfold B.Prog.SlotModel.t_g; apply B.Prog.SlotModel.fr50_length].
Qed.

(* Visibility: the shadow span of a sub-range of a live heap block (AR_shadow_law's shadow_hull_vis), a range of a
   live frame's shadow (AR_frames_law), and an image range (ProgBridge.img_vis_W). *)
Lemma w4b11_heap_shr : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> lo + len <= p + Reusable.YG00.req_size n -> 1 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (lo / 8 + B.AsanRT.ASAN_K) ((lo + len - 1) / 8 - lo / 8 + 1).
Proof.
  intros ly S W mem md p n lo len HAR Hin Hlo Hhi Hlen.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [_ Hh].
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  unfold B.ProgBridge.range_visible, B.AsanRT.ASAN_K.
  pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)) as Hl8.
  pose proof (Z.div_le_mono lo (lo + len - 1) 8 ltac:(lia) ltac:(lia)) as M0.
  pose proof (Z.div_le_upper_bound (lo + len - 1) 8 (lo + len - 1) ltac:(lia) ltac:(lia)) as Hu.
  split; [lia|]. split; [lia|].
  intros s Hs.
  apply (w4b_vis_of_aview W mem). apply Hh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  pose proof (Z.div_le_mono p lo 8 ltac:(lia) ltac:(lia)) as M1.
  pose proof (Z.div_le_mono (lo + len - 1) (p + Reusable.YG00.req_size n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4b11_frame_shr : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos o len,
  Reusable.YG0n.AR segs B ly S W mem md ->
  In (cid, pos) (Reusable.YG01.frames S) ->
  0 <= o -> 0 <= len -> o + len <= Reusable.YG00.fs_frame_bytes cid / 8 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W)
    (Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly cid pos) + o) len.
Proof.
  intros ly S W mem md cid pos o len HAR Hin Ho Hl Hol.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hal & Happ & Hby & Hsh).
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  set (F := Reusable.YG0f.frame_addr ly cid pos) in *.
  set (sz := Reusable.YG00.fs_frame_bytes cid) in *.
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
  pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)) as HF8'.
  pose proof (Z.div_le_upper_bound sz 8 sz ltac:(lia) ltac:(lia)) as Hs8.
  unfold B.ProgBridge.range_visible, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [lia|]. split; [rewrite P64; lia|].
  intros a Ha. destruct (Hsh (a - (0x7fff8000 + F / 8)) ltac:(lia)) as [[Hv _] _].
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hv.
  replace (0x7fff8000 + F / 8 + (a - (0x7fff8000 + F / 8))) with a in Hv by lia. exact Hv.
Qed.

Lemma w4b11_img_rng : forall (W : Reusable.YA0n.world segs) lo len,
  0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 ->
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W lo len H0 H1 H2. apply B.ProgBridge.rng_of_visible.
  apply (B.ProgBridge.range_visible_sub _ B.Prog.ImgBounds.IMG_LO (B.Prog.ImgBounds.IMG_HI - B.Prog.ImgBounds.IMG_LO));
    [exact (B.ProgBridge.img_vis_W W) | | | ]; unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia.
Qed.

(* The journal across a raw-memory write confined to a sub-range [lo, hi) of its stack window and a range
   [flo, fhi) of an owned frame (YCbq.ajournal_exec with Wr = the two ranges; w4b_aj_munch with a second range). *)
Lemma w4b11_aj2 : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
    (Wc : Reusable.YA0n.world segs) memc mdc k memc' mdc' lo hi flo fhi,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 ->
  (forall a, flo <= a < fhi -> Reusable.YCbq.in_frames lyc own a) ->
  lib.Lib.Frame.munch [(lo, hi); (flo, fhi)] memc memc' ->
  (forall x : word, lo <= bv_unsigned x < hi \/ flo <= bv_unsigned x < fhi -> memc' x <> None) ->
  (forall x : word, Reusable.YA0n.w_H Wc x = true -> memc' x = memc x) ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' lo hi flo fhi HJ Hlo Hhi Hfr Hm Hp Hh Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k
           memc' mdc' (fun a => lo <= a < hi \/ flo <= a < fhi) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (Hm x); [reflexivity|]. cbn.
    split; [intros H; apply Hx; left; exact H|]. split; [intros H; apply Hx; right; exact H | exact I].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H Wc x); [exact Hx|].
    assert (D : (lo <= bv_unsigned x < hi \/ flo <= bv_unsigned x < fhi) \/
                ((bv_unsigned x < lo \/ hi <= bv_unsigned x) /\ (bv_unsigned x < flo \/ fhi <= bv_unsigned x))) by lia.
    destruct D as [D | [D1 D2]]; [apply Hp; exact D|].
    rewrite (Hm x); [exact Hx|]. cbn. split; [lia|]. split; [lia | exact I].
  - exact Hh.
  - exact Hs.
  - intros a [Ha|Ha]; [left; lia | right; right; right; exact (Hfr a Ha)].
Qed.

(* A byte the raw-or-image reader mrd finds outside the image is in the raw memory. *)
Lemma w4b11_raw : forall m (x : word) b, lib.Lib.Mem.mrd B.Img0.rsegs m x = Some b ->
  ~ Reusable.YG0d.in_img segs (bv_unsigned x) -> m x = Some b.
Proof.
  intros m x b H Hn. unfold lib.Lib.Mem.mrd in H. destruct (m x) as [b'|] eqn:E; [exact H|].
  exfalso. apply Hn. unfold lib.Lib.PropExec.seg_rom, memory_read in H.
  destruct (find_segment B.Img0.rsegs (bv_unsigned x) (Z.of_N 1)) as [seg|] eqn:Ef; [|discriminate H].
  exact (w4b11_fseg_img _ _ Ef).
Qed.

(* A byte-backed range outside the image is present in the raw memory. *)
Lemma w4b11_some : forall m lo hi (x : word), lib.Lib.Frame.stk B.Img0.rsegs m lo hi ->
  lo <= bv_unsigned x < hi -> ~ Reusable.YG0d.in_img segs (bv_unsigned x) -> m x <> None.
Proof.
  intros m lo hi x (_ & _ & H) Hx Hn. destruct (H _ Hx) as [_ (b & Hb)].
  unfold lib.Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
  rewrite (w4b11_raw m x b Hb Hn). discriminate.
Qed.

(* Present bytes are byte-backed (the journal's stack window gives stk). *)
Lemma w4b11_stk_pres : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Hp a Ha) as [_ (b & Hb)]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* The class-6 frame's shadow bytes are shadow addresses (the frame lies in low or high application memory). *)
Lemma w4b11_sfr_shadow : forall fr x, 4096 <= fr ->
  (fr + 4096 <= 0x7fff7000 \/ (0x10007fff8000 <= fr /\ fr + 4096 <= 0x7fffff800000)) ->
  ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> B.AsanRT.in_shadow x.
Proof.
  intros fr x H0 H1 Hx.
  unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES, B.AsanRT.ASAN_K in Hx.
  change (3136 / 8) with 392 in Hx.
  unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG.
  Z.div_mod_to_equations. lia.
Qed.

(* Movers of the cut bundles across a munch: spill words by SP (one base A on both sides), frame bytes / shadow /
   image bytes by the caller's outside facts. *)
Lemma w4b11_FLI_mv : forall W cx fr (regs R : bvmap 5 word) m m',
  ACtlCutP.FLI cx fr regs m ->
  (forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v) ->
  lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs 27 ->
  lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  (forall x, Reusable.YG0d.in_img segs x -> lib.Lib.Frame.outside W x) ->
  lib.Lib.Frame.stk B.Img0.rsegs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr R m'.
Proof.
  intros W cx fr regs R m m' H SP E27 Hm HOS HOI Hstk.
  destruct H as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & Had & _ & (R1 & R2 & R3) & (K1 & K2) & S168b & S88).
  unfold ACtlCutP.FLI.
  split; [unfold ACtlCut.rgv in *; rewrite E27; exact H27|].
  refine (conj (SP 168 _ _ S168) (conj (SP 96 _ _ S96) (conj (SP 112 _ _ S112) (conj (SP 120 _ _ S120)
    (conj (SP 128 _ _ S128) (conj (SP 136 _ _ S136) (conj (SP 144 _ _ S144) (conj (SP 152 _ _ S152)
    (conj (SP 280 _ _ S280) (conj (SP 160 _ _ S160) (conj (SP 176 _ _ S176) (conj (SP 192 _ _ S192)
    (conj (SP 200 _ _ S200) (conj (SP 216 _ _ S216) (conj (SP 208 _ _ S208) (conj (SP 104 _ _ S104)
    (conj (SP 256 _ _ S256) (conj (SP 264 _ _ S264) (conj (SP 288 _ _ S288) (conj (SP 296 _ _ S296)
    (conj (SP 304 _ _ S304) (conj (w4b11_amv W m m' _ _ Had Hm HOS) (conj Hstk
    (conj (conj (w4b11_amv W m m' _ _ R1 Hm HOS) (conj (w4b11_amv W m m' _ _ R2 Hm HOS)
                                                    (w4b11_amv W m m' _ _ R3 Hm HOS)))
    (conj (conj _ (w4b11_amv W m m' _ _ K2 Hm HOS)) (conj (SP 168 _ _ S168b) (SP 88 _ _ S88)))))))))))))))))))))))))));
    try lia.
  apply (w4b11_bmv W m m' _ _ K1 Hm). intros x Hx. apply HOI. apply w4b11_in_img.
  change (Z.of_nat (length ACtlCutP.KNA.kind_name_bytes)) with 112 in Hx.
  unfold ACtlCutP.KNA.KIND_NAME in Hx. lia.
Qed.

Lemma w4b11_LK_mv : forall W cx fr j (regs R : bvmap 5 word) m m',
  ACtlCutP.LK cx fr j regs m ->
  (forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v) ->
  lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs 27 ->
  lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  (forall x, Reusable.YG0d.in_img segs x -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> lib.Lib.Frame.outside W x) ->
  lib.Lib.Frame.stk B.Img0.rsegs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j R m'.
Proof.
  intros W cx fr j regs R m m' (Hj & S240 & HOUR & HFLI) SP E27 Hm HOS HOI HOO Hstk.
  split; [exact Hj|]. split; [exact (SP 240 _ ltac:(lia) S240)|]. split.
  - unfold ACtlCutP.OURb in *. apply (w4b11_bmv W m m' _ _ HOUR Hm).
    rewrite B.Prog.SlotModel.OUR_length. intros x Hx. apply HOO. lia.
  - exact (w4b11_FLI_mv W cx fr regs R m m' HFLI SP E27 Hm HOS HOI Hstk).
Qed.

(* FRAC across a munch that keeps its memory words: the spill words at [A, c_sp), the frame header / entry /
   trailer words, and the frame's shadow; registers 2 3 4 8 9 19 26 kept. *)
Lemma w4b11_frac_mv : forall W cx fr sel (regs R : bvmap 5 word) m m' A0,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  lib.Lib.Frame.munch W m m' ->
  (forall x, A0 <= x < ACtlCut.c_sp cx -> lib.Lib.Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096 -> lib.Lib.Frame.outside W x) ->
  (forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> lib.Lib.Frame.outside W x) ->
  ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros W cx fr sel regs R m m' A0 H HA0 HA0r E2 E3 E4 E8 E9 E19 E26 Hm HOA HOF HOS.
  pose proof (w4b_frac_move cx fr sel regs R m H E2 E3 E4 E8 E9 E19 E26) as H'.
  destruct H' as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & (sh & Hsh & Hshl) & Hsv & Q4088).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr R 2)) as [Hb0 _]. exact Hb0. }
  assert (EA : A = A0).
  { apply w4b_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | exact HA0r |].
    unfold ACtlCut.rgv in Hr9, HA0. rewrite <- Hr9, <- HA0. exact E9. }
  subst A.
  exists A0, sp.
  repeat (split; [assumption|]).
  split; [apply (w4b11_qmv W m m' _ _ Q336 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4b11_qmv W m m' _ _ Q48 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4b11_qmv W m m' _ _ Q40 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4b11_qmv W m m' _ _ Qhdr Hm); intros x Hx; apply HOF; lia|].
  split; [apply (w4b11_qmv W m m' _ _ Q16 Hm); intros x Hx; apply HOF; lia|].
  split; [exists sh; split; [apply (w4b11_bmv W m m' _ _ Hsh Hm); rewrite Hshl; intros x Hx; apply HOS;
          unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in *; lia | exact Hshl]|].
  split.
  - apply (w4b11_bmv W m m' _ _ Hsv Hm). intros x Hx. apply HOA.
    unfold ACtlCutP.saved_bytes in Hx. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
  - apply (w4b11_qmv W m m' _ _ Q4088 Hm); intros x Hx; apply HOF; lia.
Qed.

(* Abbreviations of the turn's frame terms (syntactic only). *)
Local Notation w4b11_G cx j := (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j).
Local Notation w4b11_S cx j := (Prog.RcReply.ir_s (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
Local Notation w4b11_AD cx j := (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 36 * 256 +
                                 Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 37).
Local Notation w4b11_PB cx j := (lib.Prog.RcFrag.bsl (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 38
                                   (Prog.RcReply.ir_s (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) - 13)).

Local Notation w4b11_W2 sp fr := ((sp - 32, sp) :: (fr + 2688, fr + 2688 + 38) :: nil).

(* ---------------------------------------------------------------------------------------------------------
   B8226c_at j (0x8226c) --S_F11--> B82304_at j.
   S_F11 (Seg/F11.v seg_F11 :659): T23, record_sum_closes(phi + 34, ir_s - 8) @0x82284, T24 / T25, the reply
   address u16 check, then reac_identity_ingest(fr + 2688, ad, phi + 38, ir_s - 13) @0x82300 returning at 0x82304. *)
Lemma seg_F11 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82304_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B8226c_at [Z.of_nat j]).
Proof.
  (* Plan (kept): run 1 = F11F.seg_F11_pre_F (T23 not taken: blk = [A + 312] = phi + 18) then record_sum_closes
     (record_sum_closesF_on.record_sum_closes_holds_F_on at a0 = phi + 34, a1 = ir_s - 8, bs = ir_rec (t_g j)), lifted whole
     by YA0nR.SRr_fevt_hid; run 2 = F11F.seg_F11_pre2_F (0x82288 beqz: a0 = 1 as recsum = 0; T24 / T25; the
     reply-address compare 0x822e8) then reac_identity_ingest (reac_identity_ingestF.reac_identity_ingest_F_holds_on at
     fr + 2688, the u16 at fr + 256, phi + 38, ir_s - 13), lifted whole.  Footprint RNG_W (w_H W3) (stack window,
     owned frame and its shadow, phi's block and its shadow, image).  Write set [sp - 32, sp) (both callee windows)
     and the identity record [fr + 2688, fr + 2726): journal by w4b11_aj2, ctl_rt by w4b11_rt_mv, every other exit
     conjunct carried across it; RECR's identity record = t_IDr j (the ingest post), FS9 from f10_K's [A + 248]. *)
  intros POST j H04 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B8226c_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & HK & HFS & Hphi0 & Hphi50 & H50 & Hsum & HG & Hok & HRP & H11 & HFT &
    HREC & HFPS & H272 & HRCA).
  pose proof HK as (Hn & Hj & HHB & HLK & (A & HFL & HA & Hq288 & Hq176 & Hq200 & Hq208 & Hq248 & Hq312) &
    Hs2 & Hs4 & Hs9 & Hs8 & Hs184 & Hs6 & Hargs).
  pose proof HFL as (H9 & Hq120 & Hq128 & Hq256 & Hq304 & Hq296).
  pose proof HFRAC as (AF & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9F & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  assert (EAF : AF = A).
  { apply w4b_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | exact HA |].
    unfold ACtlCut.rgv in Hr9F, H9. rewrite <- Hr9F, <- H9. reflexivity. }
  subst AF.
  unfold B.AsanRT.APPMEM_END, ACtlCutP.FRAME_BYTES in HSapp, HfrA.
  assert (Esp : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp) by exact HspZ.
  unfold ACtlCutP.flen in *.
  (* the world facts of the cut: the stack window above alloc_ceiling, the owned frame, phi's live block *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & HstkS & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold Reusable.YCfn.LLVMF_STK in HstkS.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4b_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (Hphi : In (phi, B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite Efr in Hf4096. rewrite Efr, HFB in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hfapp.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi) as (_ & Hp4096 & Hpceil & _).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx)
    HAR Hphi Hin6) as Hsep.
  rewrite Efr, HFB in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  pose proof (Reusable.YCbq.req_size_pos (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ltac:(lia)) as [_ Hrq].
  assert (Hfimg : forall x, fr <= x < fr + 4096 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 x HAR _)).
    right; left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr, HFB. exact Hx. }
  assert (Himglo : forall x, Reusable.YG0d.in_img segs x -> 0 <= x < 0x7fff8000).
  { intros x Hx. pose proof (w4b_segs_low x Hx) as H. unfold Reusable.YG0f.kLowMemEnd in H. exact H. }

  (* the reply was accepted: ir holds, 14 <= ir_s <= 23, the record sum closes *)
  assert (Hir : Prog.RcReply.ir (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (w4b11_G cx j) = true).
  { unfold Prog.RcReply.reply_ok in Hok. apply andb_prop in Hok. exact (proj2 Hok). }
  destruct (Prog.RcReply.ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & _ & Hrec).
  assert (Hglen : length (w4b11_G cx j) = 50%nat)
    by (unfold B.Prog.SlotModel.t_g; apply B.Prog.SlotModel.fr50_length).
  assert (Hbig : B.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true)
    by (unfold B.Prog.SlotModel.t_big; apply Z.leb_le; exact H50).
  rewrite Hbig in Hq312.
  pose proof HHB as (Hphinz & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _).
  unfold B.ACtlK.a_size, B.AsanRT.APPMEM_END in Hpe. rewrite Z.max_l in Hpe by lia.
  pose proof (B.AsanRTFacts.addressable_app _ _ _ HAd) as Hphiapp.
  unfold B.ACtlK.a_size in Hphiapp. rewrite Z.max_l in Hphiapp by lia.
  pose proof HRP as (RWa & RWp & RWn).
  pose proof HLK as (_ & _ & _ & HFLI).
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HSTKfr & (HADid & _ & _) & _ & _ & _).
  pose proof HREC as ((HIDB & HIDok) & (HFGB & HFGok)).
  unfold Reusable.YCfn.LLVMF_STK in Hpres.
  (* the two write sets: the callee windows [sp - 16, sp) / [sp - 32, sp) and the identity record *)
  assert (HOW2 : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                 lib.Lib.Frame.outside (w4b11_W2 sp fr) x).
  { intros x H1 H2. cbn. split; [lia | split; [lia | exact I]]. }
  assert (HOW1 : forall x, (x < sp - 16 \/ sp <= x) -> lib.Lib.Frame.outside [(sp - 16, sp)] x).
  { intros x H1. cbn. split; [lia | exact I]. }
  assert (HW21 : forall x, lib.Lib.Frame.outside (w4b11_W2 sp fr) x -> lib.Lib.Frame.outside [(sp - 16, sp)] x).
  { intros x (H1 & _). cbn. split; [lia | exact I]. }
  assert (OA : forall x, A <= x < ACtlCut.c_sp cx -> lib.Lib.Frame.outside (w4b11_W2 sp fr) x)
    by (intros x Hx; apply HOW2; lia).
  assert (OF : forall x, fr <= x < fr + 2688 \/ fr + 2688 + 38 <= x < fr + 4096 ->
               lib.Lib.Frame.outside (w4b11_W2 sp fr) x)
    by (intros x Hx; apply HOW2; lia).
  assert (OP : forall x, phi <= x < phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
               lib.Lib.Frame.outside (w4b11_W2 sp fr) x)
    by (intros x Hx; apply HOW2; lia).
  assert (OS : forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside (w4b11_W2 sp fr) x).
  { intros x Hx. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hx. apply HOW2; lia. }
  assert (OI : forall x, Reusable.YG0d.in_img segs x -> lib.Lib.Frame.outside (w4b11_W2 sp fr) x).
  { intros x Hx. pose proof (Himglo x Hx) as Hxl. apply HOW2; [lia|].
    destruct (Z_lt_ge_dec x (fr + 2688)) as [D|D]; [left; exact D|].
    destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [D'|D']; [|right; lia].
    exfalso. exact (Hfimg x ltac:(lia) Hx). }
  (* the footprint: every visible byte of the cut's world *)
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RW : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
               lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible; eapply w4b_win_vis; [exact HJ | exact H1 | exact H2]).
  assert (RF : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible;
        eapply w4b_frame_vis; [exact HAR | exact Hin6 | rewrite Efr; exact H1 | rewrite Efr, HFB; exact H2]).
  assert (RP : forall lo len, phi <= lo ->
               lo + len <= phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
               lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible;
        eapply w4b_heap_vis; [exact HAR | exact Hphi | exact H1 | exact H2]).
  (* the cut's configuration in the run's state form, the walk moved to the canonical map *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8226c_at [Z.of_nat j])) with 0x8226c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8226c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  change (Lib.Regs6ss.mkR_of regs3) with (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6) (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9) (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12) (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  (* ---- run 1: 0x8226c -> record_sum_closes (T23 not taken), the callee, return at 0x82288 ---- *)
  pose proof record_sum_closesF_on.record_sum_closes_holds_F_on as HRSC.
  unfold record_sum_closes_c_on.record_sum_closes_contract_F_on, record_sum_closes_c.RECORD_SUM_CLOSES,
    record_sum_closes_c.RECORD_SUM_CLOSES_FRAME in HRSC.
  assert (Ea0 : bv_unsigned (Z_to_bv 64 (phi + 34)) = phi + 34) by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (Ea1 : bv_unsigned (Z_to_bv 64 (w4b11_S cx j - 13 + 5)) = w4b11_S cx j - 13 + 5)
    by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (Hrec34 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 34) (Prog.RcReply.ir_rec (w4b11_G cx j))).
  { pose proof (w4b11_sub mem3 phi _ 34 (Z.to_nat (w4b11_S cx j - 8)) HG ltac:(rewrite Hglen; lia)) as H.
    change (Z.of_nat 34) with 34 in H. exact H. }
  assert (HST0 : lib.Lib.Frame.stk B.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) sp).
  { apply (w4b11_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md3 RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F11F.seg_F11_pre_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A phi (w4b11_S cx j - 13)).
      - exact H9.
      - exact H11.
      - exact Hr26.
      - lia.
      - lia.
      - exact Hq312.
      - apply RW; lia. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    eapply (HRSC RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ACtlCut.c_sp cx - 32768) (Prog.RcReply.ir_rec (w4b11_G cx j)));
      rewrite ?Ea0, ?Ea1, ?Esp.
    - unfold Prog.RcReply.ir_rec. rewrite length_firstn, length_skipn, Hglen. lia.
    - right. split; [lia|]. split; [lia|]. split; [exact Hrec34 | left; lia].
    - exact HST0.
    - lia.
    - intros _. exact (proj1 Hrt).
    - intros _. apply (B.AsanRTFacts.addressable_sub mem3 phi
        (B.ACtlK.a_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j))); [exact HAd | lia | lia | unfold B.ACtlK.a_size; lia].
    - intros _ x Hx. cbn. split; [|exact I].
      unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
        B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia.
    - apply RW; lia.
    - intros _. apply w4b11_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    - intros _. apply w4b11_img_rng; unfold B.AsanRT.CELL_K; lia.
    - intros _. apply RP; lia.
    - intros _. apply B.ProgBridge.rng_of_visible. apply (w4b11_heap_shr ly3 S3 W3 mem3 md3 phi _ _ _ HAR Hphi); lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 HP1 Hhid1 Hsbm1.
  destruct HP1 as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & m1 & Ems1 & MU1 & WM1 & _ & ST1).
  subst ms1.
  rewrite (lib.Lib.MState.ret_pc_even 0x82288) by (first [lia | reflexivity]).
  rewrite Esp in MU1, ST1.

  (* ---- the facts stretch 2 and the ingest read, carried to the post-call memory m1 (call 1 wrote [sp-16, sp)) ---- *)
  pose proof (w4b_ctl_rt_munch _ _ _ mem3 m1 Hrt MU1
    ltac:(intros x Hx; cbn; split; [unfold B.AsanRT.HIGHMEM_BEG in Hx; lia | exact I])) as Hrt1.
  assert (Q1 : forall a v, A <= a -> a + 8 <= A + 448 -> ACtlCutP.q64 mem3 a v -> ACtlCutP.q64 m1 a v).
  { intros a v H1 H2 Hq. apply (w4b11_qmv _ mem3 m1 _ _ Hq MU1). intros x Hx. apply HOW1. lia. }
  assert (B1 : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> a + Z.of_nat (length bs) <= sp - 16 ->
               lib.Lib.Mem.bytes_at B.Img0.rsegs m1 a bs).
  { intros a bs Hb Hl. apply (w4b11_bmv _ mem3 m1 _ _ Hb MU1). intros x Hx. apply HOW1. lia. }
  assert (S1 : forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; apply HW21, OS, Hx).
  assert (Hpa : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (fr + 256)
      (lib.Lib.Mem.le2 (Z_to_bv 64 (bv_unsigned (Prog.RcParse.cp_b (w4b11_G cx j) 37) +
                                    256 * bv_unsigned (Prog.RcParse.cp_b (w4b11_G cx j) 36))))).
  { rewrite <- w4b11_le2. exact (w4b11_cb_bytes _ _ _ _ RWa). }
  assert (Hb36 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 36) [Prog.RcParse.cp_b (w4b11_G cx j) 36]).
  { pose proof (w4b_bytes_at_nth mem3 phi _ 36 HG ltac:(rewrite Hglen; lia)) as H.
    change (Z.of_nat 36) with 36 in H. exact H. }
  assert (Hb37 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 37) [Prog.RcParse.cp_b (w4b11_G cx j) 37]).
  { pose proof (w4b_bytes_at_nth mem3 phi _ 37 HG ltac:(rewrite Hglen; lia)) as H.
    change (Z.of_nat 37) with 37 in H. exact H. }
  pose proof (w4b11_shc mem3 phi _ 36 HAd H50 ltac:(lia)) as Hsh36.
  pose proof (w4b11_shc mem3 phi _ 37 HAd H50 ltac:(lia)) as Hsh37.
  assert (SH1 : forall c, 0 <= c < 50 -> forall x,
                Z.shiftr (phi + c) 3 + B.AsanRT.ASAN_K <= x < Z.shiftr (phi + c) 3 + B.AsanRT.ASAN_K + Z.of_nat 1 ->
                lib.Lib.Frame.outside (w4b11_W2 sp fr) x).
  { intros c Hc x Hx. apply OS. replace x with (Z.shiftr (phi + c) 3 + B.AsanRT.ASAN_K) by lia.
    apply w4b11_sh_in. apply Hphiapp. lia. }
  assert (HBpb : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 38) (w4b11_PB cx j)).
  { pose proof (w4b11_sub mem3 phi _ 38 (Z.to_nat (w4b11_S cx j - 13)) HG ltac:(rewrite Hglen; lia)) as H.
    change (Z.of_nat 38) with 38 in H. exact H. }
  assert (HADpb : B.AsanRT.addressable mem3 (phi + 38) (w4b11_S cx j - 13))
    by (apply (B.AsanRTFacts.addressable_sub mem3 phi (B.ACtlK.a_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)));
        [exact HAd | lia | lia | unfold B.ACtlK.a_size; lia]).
  assert (Hidc1 : lib.Lib.Step.rw_cells B.Img0.rsegs m1 (fr + 2688)
                    [lib.Lib.Cells.CB 38 (B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j)]).
  { apply w4b11_cb_rw; [| exact (w4b11_ID_len _ j) |].
    - apply B1; [exact HIDB|]. rewrite w4b11_ID_len. lia.
    - apply (w4b11_wr_of_stk mem3 m1 fr (fr + ACtlCutP.FRAME_BYTES) (fr + 2688) 38 HSTKfr WM1);
        unfold ACtlCutP.FRAME_BYTES; lia. }
  assert (Hidev : (fr + 2688) mod 2 = 0) by (Z.div_mod_to_equations; lia).
  assert (Href : reac_identity_ingest_c.ingest_refused (fr + 2688) (phi + 38) (w4b11_S cx j - 13) = false).
  { unfold reac_identity_ingest_c.ingest_refused. apply Bool.orb_false_intro.
    - apply Z.eqb_neq. lia.
    - apply Bool.andb_false_intro2. apply Z.eqb_neq. lia. }
  assert (Rids : lib.Lib.ExecF.rng RNG ((fr + 2688) / 8 + B.AsanRT.ASAN_K) ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1)).
  { pose proof (w4b11_frame_shr ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) 336 5 HAR Hin6 ltac:(lia) ltac:(lia)
      ltac:(rewrite HFB; change (4096 / 8) with 512; lia)) as V.
    rewrite Efr in V. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in V.
    replace ((fr + 2688) / 8 + B.AsanRT.ASAN_K) with (0x7fff8000 + fr / 8 + 336)
      by (unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia).
    replace ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1) with 5 by (Z.div_mod_to_equations; lia).
    exact (B.ProgBridge.rng_of_visible _ _ _ V). }
  (* ---- run 2: 0x82288 -> reac_identity_ingest (the sum-closes sink, T24 / T25, the reply-address compare not taken),
     the callee, return at the cut 0x82304 ---- *)
  pose proof reac_identity_ingestF.reac_identity_ingest_F_holds_on as HING.
  unfold reac_identity_ingest_c.reac_identity_ingest_contract_F_on, reac_identity_ingest_c.reac_identity_ingest_W,
    reac_identity_ingest_c.REAC_IDENTITY_INGEST, reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in HING.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md1 RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F11F.seg_F11_pre2_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A phi (w4b11_S cx j - 13) fr (w4b11_AD cx j)
                (Prog.RcParse.cp_b (w4b11_G cx j) 36) (Prog.RcParse.cp_b (w4b11_G cx j) 37)).
      - reflexivity.
      - reflexivity.
      - rewrite Hrec. reflexivity.
      - lia.
      - lia.
      - unfold Prog.RcParse.cp_v. lia.
      - apply (Q1 (A + 312) (phi + 18)); [lia | lia | exact Hq312].
      - apply (Q1 (A + 288) (fr + 256)); [lia | lia | exact Hq288].
      - apply (Q1 (A + 304) (fr + 272)); [lia | lia | exact Hq304].
      - apply (Q1 (A + 296) (fr + 304)); [lia | lia | exact Hq296].
      - apply (Q1 (A + 176) (fr + 2688)); [lia | lia | exact Hq176].
      - apply B1; [exact Hpa | rewrite lib.Lib.Mem.length_le2; lia].
      - apply B1; [exact (w4b_lrw8 _ _ _ RWp) | rewrite lib.Lib.Mem.length_le8; lia].
      - apply B1; [exact (w4b_lrw8 _ _ _ RWn) | rewrite lib.Lib.Mem.length_le8; lia].
      - apply B1; [exact Hb36 | cbn [length]; lia].
      - apply B1; [exact Hb37 | cbn [length]; lia].
      - apply (w4b11_bmv _ mem3 m1 _ _ Hsh36 MU1). intros x Hx. apply HW21. exact (SH1 36 ltac:(lia) x Hx).
      - apply (w4b11_bmv _ mem3 m1 _ _ Hsh37 MU1). intros x Hx. apply HW21. exact (SH1 37 ltac:(lia) x Hx).
      - apply RW; lia.
      - apply RW; lia.
      - apply RW; lia.
      - apply RW; lia.
      - apply RW; lia.
      - apply RF; lia.
      - apply RF; lia.
      - apply RF; lia.
      - apply RP; lia.
      - apply RP; lia.
      - apply B.ProgBridge.rng_of_visible. eapply w4b_heap_sh1; [exact HAR | exact Hphi | lia].
      - apply B.ProgBridge.rng_of_visible. eapply w4b_heap_sh1; [exact HAR | exact Hphi | lia]. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    (* the one application of the ingest contract (named bindings: independent of its binder order) *)
    eapply HING with (RNG := RNG) (lo := ACtlCut.c_sp cx - 32768) (id := fr + 2688) (ad := w4b11_AD cx j)
      (p := phi + 38) (len := w4b11_S cx j - 13) (idb := B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j)
      (pb := w4b11_PB cx j); rewrite ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - unfold Prog.RcParse.cp_v. pose proof (w4b11_ubv (Prog.RcParse.cp_b (w4b11_G cx j) 36)).
      pose proof (w4b11_ubv (Prog.RcParse.cp_b (w4b11_G cx j) 37)). lia.
    - lia.
    - lia.
    - intros _. split; [exact Hidev | exact Hidc1].
    - unfold lib.Prog.RcFrag.bsl. rewrite length_firstn, length_skipn, Hglen. lia.
    - intros _ _. apply B1; [exact HBpb|]. unfold lib.Prog.RcFrag.bsl. rewrite length_firstn, length_skipn, Hglen. lia.
    - intros _ _ _. lia.
    - exact ST1.
    - lia.
    - intros _. lia.
    - intros _ _. lia.
    - exact (proj1 Hrt1).
    - intros _. exact (w4b11_amv _ mem3 m1 _ _ HADid MU1 S1).
    - intros _ _. exact (w4b11_amv _ mem3 m1 _ _ HADpb MU1 S1).
    - intros x Hx. destruct Hx as [Hx | [Hx | Hx]].
      + apply OI. apply w4b11_in_img. unfold B.AsanRT.GOT_CELL_K in Hx. lia.
      + apply OI. apply w4b11_in_img. unfold B.AsanRT.CELL_K in Hx. lia.
      + apply OS. exact Hx.
    - apply RW; lia.
    - apply w4b11_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    - apply w4b11_img_rng; unfold B.AsanRT.CELL_K; lia.
    - intros _. split; [apply RF; lia | exact Rids].
    - intros _ _. split; [apply RP; lia|].
      apply B.ProgBridge.rng_of_visible. apply (w4b11_heap_shr ly3 S3 W3 mem3 md3 phi _ _ _ HAR Hphi); lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms2 md2 HP2 Hhid2 Hsbm2.
  unfold reac_identity_ingest_c.reac_identity_ingest_post in HP2.
  destruct HP2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MU2 & WM2 & _ &
    ST2 & _ & HRW).
  subst ms2.
  rewrite (lib.Lib.MState.ret_pc_even 0x82304) by (first [lia | reflexivity]).
  unfold reac_identity_ingest_c.reac_identity_ingest_W, reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in MU2.
  rewrite Esp in MU2, ST2.
  pose proof (HRW Href) as HRW'.

  (* ---- the exit cut B82304_at: the memory after both calls, the journal, the body ---- *)
  assert (MUW : lib.Lib.Frame.munch (w4b11_W2 sp fr) mem3 m2).
  { intros x Hx. rewrite (MU2 x Hx). apply MU1. apply HW21. exact Hx. }
  pose proof (lib.Lib.Frame.wmono_trans B.Img0.rsegs mem3 m1 m2 WM1 WM2) as WMW.
  assert (EIDr : B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j =
                 snd (lib.Prog.RcIdentModel.ING (B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j) (w4b11_AD cx j)
                        (w4b11_PB cx j))).
  { unfold B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.rp_id. rewrite Hir. reflexivity. }
  assert (HIDok' : lib.Prog.RcIdentModel.id_ok (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j)).
  { rewrite EIDr. exact (lib.Prog.RcIdentLib.ING_id_ok _ _ _ (w4b11_ID_len _ j) HIDok). }
  assert (Hv0b : 0 <= reac_identity_ingest_c.ingest_ret (fr + 2688) (w4b11_AD cx j) (phi + 38) (w4b11_S cx j - 13)
                   (B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j) (w4b11_PB cx j) < 2 ^ 63).
  { unfold reac_identity_ingest_c.ingest_ret. rewrite Href.
    destruct (lib.Prog.RcIdentModel.ING_ret (B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j) (w4b11_AD cx j)
                (w4b11_PB cx j)) as [E|E]; rewrite E; lia. }
  pose proof (lib.Lib.Frame.stk_of_rw_cells B.Img0.rsegs m2 _ _ HRW') as STid.
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in STid.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R2 := R) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82304_at [Z.of_nat j])) R2 m2 md2)
            (POST cx)).
  apply (H04 cx [Z.of_nat j] fr k ly3 S3 W3 R2 m2 md2 HB).
  - eapply w4b11_aj2 with (lo := sp - 32) (hi := sp) (flo := fr + 2688) (fhi := fr + 2688 + 38); [exact HJ | | | | | | |].
    + unfold Reusable.YCfn.LLVMF_STK. lia.
    + lia.
    + intros a Ha. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
      rewrite Efr, HFB. hnf. cbn [fst snd]. lia.
    + exact MUW.
    + intros x [Hx | Hx].
      * apply (w4b11_some m2 (ACtlCut.c_sp cx - 32768) sp x ST2); [lia|]. intros Hi. pose proof (Himglo _ Hi). lia.
      * apply (w4b11_some m2 _ _ x STid); [lia | apply Hfimg; lia].
    + intros x Hx. pose proof (Hhid2 x Hx) as E2. pose proof (Hhid1 x Hx) as E1.
      unfold lib.Lib.MState.MS in E1, E2. cbn [ms_mem] in E1, E2. rewrite E2. exact E1.
    + exact (Reusable.YK04.same_but_materialized_trans md3 md1 md2 Hsbm1 Hsbm2).
  - exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82304_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    assert (HR9 : ACtlCut.rgv R2 9 A) by reflexivity.
    assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R2 m2 off v).
    { intros off v Hoff Hsv. apply (w4b11_spmv (w4b11_W2 sp fr) regs3 R2 mem3 m2 off v A Hsv H9);
        try assumption; try lia.
      intros x Hx. apply OA. lia. }
    split.
    { apply (w4b11_frac_mv (w4b11_W2 sp fr) cx fr fr regs3 R2 mem3 m2 A HFRAC H9 HA);
        [reflexivity | reflexivity | reflexivity | reflexivity | exact (eq_sym H9) | reflexivity | exact (eq_sym Hr26)
        | exact MUW | intros x Hx; apply OA; lia | intros x Hx; apply OF; lia | ].
      intros x Hx. apply OS. apply (w4b11_sfr_shadow fr x); [lia | lia | exact Hx]. }
    unfold ACtlCutP.fcutp_body. exists phi. cbv beta.
    split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|].
    split; [split; [exact Hphinz | exact (w4b11_amv _ mem3 m2 _ _ HAd MUW OS)]|].
    split; [exact Hs2|]. split; [exact Hs4|].
    split.
    { destruct HFT as (T224 & T232 & Tphi & Tlen). split; [exact (SP 224 _ ltac:(lia) T224)|].
      split; [exact (SP 232 _ ltac:(lia) T232)|]. split; [|exact Tlen].
      apply (w4b11_bmv _ mem3 m2 _ _ Tphi MUW). intros x Hx. apply OP. lia. }
    split.
    { apply (w4b11_LK_mv (w4b11_W2 sp fr) cx fr j regs3 R2 mem3 m2 HLK SP);
        [reflexivity | exact MUW | exact OS | exact OI | intros x Hx; apply OF; lia | ].
      apply (w4b11_stk_tr _ mem3 m2 fr (fr + ACtlCutP.FRAME_BYTES) HSTKfr MUW WMW).
      intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
      destruct (Z_lt_ge_dec x (fr + 2688)) as [D|D]; [left; apply OF; lia|].
      destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [D'|D']; [|left; apply OF; lia].
      right. apply (w4b11_present m2 (fr + 2688) _ x (w4b11_cb_bytes _ _ _ _ HRW')).
      rewrite (lib.Prog.RcIdentModel.ING_length _ _ _ (w4b11_ID_len _ j)).
      change (Z.of_nat lib.Prog.RcIdentModel.ID_SIZE) with 38. lia. }
    split.
    { split; [exact (SP 184 _ ltac:(lia) Hs184)|]. split; [exact Hs8|]. split; [exact Hs6|].
      split; [exact Hs9|]. rewrite Hbig. exists A. split; [exact HR9|].
      apply (w4b11_qmv _ mem3 m2 _ _ Hq312 MUW). intros x Hx. apply OA. lia. }
    split.
    { destruct HFS as (Hhave & Hnb & Hbody & Had40 & HFI).
      split; [apply (w4b11_bmv _ mem3 m2 _ _ Hhave MUW); rewrite lib.Lib.Mem.length_le4; intros x Hx; apply OF; lia|].
      split; [apply (w4b11_bmv _ mem3 m2 _ _ Hnb MUW); cbn [length]; intros x Hx; apply OF; lia|].
      split; [apply (w4b11_bmv _ mem3 m2 _ _ Hbody MUW); pose proof (w4b11_body_len (ACtlCut.c_in cx) j);
              intros x Hx; apply OF; lia|].
      split; [exact (w4b11_amv _ mem3 m2 _ _ Had40 MUW OS) | exact HFI]. }
    split.
    { split; split.
      - unfold ACtlCutP.IDBe. rewrite EIDr. exact (w4b11_cb_bytes _ _ _ _ HRW').
      - exact HIDok'.
      - unfold ACtlCutP.FGBe in *. apply (w4b11_bmv _ mem3 m2 _ _ HFGB MUW). rewrite w4b11_FG_len.
        intros x Hx. apply OF. lia.
      - exact HFGok. }
    split; [intros _; apply (w4b11_bmv _ mem3 m2 _ _ HG MUW); rewrite Hglen; intros x Hx; apply OP; lia|].
    split.
    { destruct HFPS as (HpB & HaB). split; [|exact (w4b11_amv _ mem3 m2 _ _ HaB MUW OS)].
      unfold ACtlCutP.pBb in *. apply (w4b11_bmv _ mem3 m2 _ _ HpB MUW).
      unfold B.Prog.SlotModel.t_B. rewrite lib.Prog.RcParse.ctrlparse_length. intros x Hx. apply OF. lia. }
    split; [exact (SP 272 _ ltac:(lia) H272)|].
    split.
    { destruct HRCA as (Ra & Rp & Rn).
      split; [exact (w4b11_amv _ mem3 m2 _ _ Ra MUW OS)|].
      split; [exact (w4b11_amv _ mem3 m2 _ _ Rp MUW OS) | exact (w4b11_amv _ mem3 m2 _ _ Rn MUW OS)]. }
    split.
    { exists (reac_identity_ingest_c.ingest_ret (fr + 2688) (w4b11_AD cx j) (phi + 38) (w4b11_S cx j - 13)
                (B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) j) (w4b11_PB cx j)).
      split; [reflexivity | exact Hv0b]. }
    exists A. split; [exact HR9|].
    apply (w4b11_qmv _ mem3 m2 _ _ Hq248 MUW). intros x Hx. apply OA. lia.
  - exact (w4b11_rt_mv _ _ _ mem3 m2 Hrt MUW
             (fun x Hx => match Hx with or_introl H => OI x H | or_intror H => OS x H end)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Helpers of seg_F12 / seg_F12_298 (prefix w4b12_).  No Section hypothesis is added. *)

(* -- the pure model: the record buffer is 72 bytes, the identity record 38, the FIRST body at most 23 (local copies
   of Seg/F12.v t_FG_length, SlotInv.v t_ID_length and Tac_ro.v tr_body_length, over the qualified names) -- *)
Lemma w4b12_t_g_length : forall inp j, length (B.Prog.SlotModel.t_g inp j) = 50%nat.
Proof. intros inp j. unfold B.Prog.SlotModel.t_g. apply B.Prog.SlotModel.fr50_length. Qed.

Lemma w4b12_fr_fg_n : forall len g, ACtlCutP.RFR.fg_fr len g = true -> 1 <= ACtlCutP.RFR.fg_n g <= 22.
Proof.
  intros len g H. unfold ACtlCutP.RFR.fg_fr in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma w4b12_keep_T : forall st g, ACtlCutP.RFR.fg_keep st g = true -> ACtlCutP.RFR.fg_T st g <= 64.
Proof.
  intros st g H. unfold ACtlCutP.RFR.fg_keep in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. exact H.
Qed.

Lemma w4b12_first_length : forall st g, length st = 72%nat -> length g = 50%nat ->
  1 <= ACtlCutP.RFR.fg_n g <= 22 -> length (ACtlCutP.RFR.fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold ACtlCutP.RFR.fg_first, ACtlCutP.RFR.fg_body.
  rewrite !length_app, length_skipn, (Prog.RcFragLib.rf_bsl_length g 6 6),
    (Prog.RcFragLib.rf_bsl_length g 27 (ACtlCutP.RFR.fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma w4b12_fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (B.Prog.SlotModel.fg_next st g (ACtlCutP.RFR.fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold ACtlCutP.RFR.fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0));
    [cbn [B.Prog.SlotModel.fg_next]; exact HL|].
  destruct (ACtlCutP.RFR.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [B.Prog.SlotModel.fg_next]; exact HL].
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - cbn [B.Prog.SlotModel.fg_next]. apply w4b12_first_length; [exact HL | exact HG | exact (w4b12_fr_fg_n len g FR)].
  - destruct (ACtlCutP.RFR.fg_keep st g) eqn:KEEP; cbn [negb];
      [|cbn [B.Prog.SlotModel.fg_next]; apply Prog.RcFragLib.rf_clear_length; exact HL].
    destruct (ACtlCutP.RFR.fg_close st g); cbn [negb B.Prog.SlotModel.fg_next];
      apply Prog.RcFragLib.rf_clear_length, Prog.RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | exact (w4b12_fr_fg_n len g FR) | exact (w4b12_keep_T st g KEEP)].
Qed.

Lemma w4b12_t_FG_length : forall inp j, length (B.Prog.SlotModel.t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold B.Prog.SlotModel.t_FG in *. rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
    destruct (B.Prog.SlotModel.f_opens _ _); cbn [B.Prog.SlotModel.fs_fg];
      unfold B.Prog.SlotModel.fg_st, B.Prog.SlotModel.fcls;
      apply (w4b12_fg_next_length 1 1 1 1 1); solve [exact IH | apply w4b12_t_g_length].
Qed.

Lemma w4b12_rp_id_length : forall idb len gb, length idb = Prog.RcIdentModel.ID_SIZE ->
  length (B.Prog.SlotModel.rp_id idb len gb) = Prog.RcIdentModel.ID_SIZE.
Proof.
  intros idb len gb H. unfold B.Prog.SlotModel.rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply Prog.RcIdentModel.ING_length|]; exact H.
Qed.

Lemma w4b12_fg_id_length : forall idb len st gb, length idb = Prog.RcIdentModel.ID_SIZE ->
  length (B.Prog.SlotModel.fg_id idb len st gb) = Prog.RcIdentModel.ID_SIZE.
Proof.
  intros idb len st gb H. unfold B.Prog.SlotModel.fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply Prog.RcIdentModel.ING_length|]; exact H.
Qed.

Lemma w4b12_t_ID_length : forall inp j, length (B.Prog.SlotModel.t_ID inp j) = Prog.RcIdentModel.ID_SIZE.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_ID. induction j as [|j IH]; cbn [B.Prog.SlotModel.fst_at].
  - unfold B.Prog.SlotModel.fs0. cbn [B.Prog.SlotModel.fs_id]. unfold Prog.RcIdentModel.ID0. apply repeat_length.
  - unfold B.Prog.SlotModel.turn. cbv zeta.
    match goal with |- context [if ?c then _ else _] => destruct c end; cbn [B.Prog.SlotModel.fs_id];
      apply w4b12_fg_id_length, w4b12_rp_id_length, IH.
Qed.

Lemma w4b12_t_IDr_length : forall inp j, length (B.Prog.SlotModel.t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_IDr. rewrite w4b12_rp_id_length; [reflexivity|].
  apply w4b12_t_ID_length.
Qed.

Lemma w4b12_body_length : forall inp j,
  (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn. lia.
  - rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
    destruct (B.Prog.SlotModel.f_opens _ _); cbn [B.Prog.SlotModel.fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn, w4b12_t_g_length. lia.
Qed.

Lemma w4b12_memcmp_self : forall (bs : list byte) n, (n <= length bs)%nat ->
  ACtlCutP.SFA.memcmp_model bs bs n = Some 0.
Proof.
  intros bs n. revert bs. induction n as [|n IH]; intros [|b bs] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma w4b12_B_fields : forall (G : list byte), (16 <= length G)%nat ->
  firstn 6 (skipn 10 (Prog.RcParse.cp_struct G (Prog.RcParse.cp_kind G))) = firstn 6 G /\
  firstn 6 (skipn 4 (Prog.RcParse.cp_struct G (Prog.RcParse.cp_kind G))) = firstn 6 (skipn 6 G).
Proof.
  intros G HL. do 16 (destruct G as [|? G]; [cbn in HL; lia|]).
  split; reflexivity.
Qed.

(* -- byte readers -- *)
Lemma w4b12_nth_sub : forall (l : list byte) k n i, (i < n)%nat ->
  nth_error (firstn n (skipn k l)) i = nth_error l (k + i).
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l n i Hi.
  - cbn [skipn Nat.add]. revert n i Hi. induction l as [|x l IHl]; intros n i Hi.
    + rewrite firstn_nil. destruct i; reflexivity.
    + destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IHl. lia.
  - destruct l as [|x l].
    + rewrite skipn_nil, firstn_nil. destruct i; reflexivity.
    + cbn [skipn Nat.add nth_error]. apply IH. exact Hi.
Qed.

Lemma w4b12_sub : forall m a (bs : list byte) k n, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (k + n <= length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite w4b12_nth_sub by exact Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

Lemma w4b12_zb : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma w4b12_ubv : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma w4b12_b8_of : forall m a (bs : list byte) k, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> (k < length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) [Z_to_bv 8 (bv_unsigned (nth k bs Prog.RcParse.cp_z))].
Proof.
  intros m a bs k (H0 & H1 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. cbn [nth_error]. rewrite w4b12_zb.
  rewrite (H k Hk). apply nth_error_nth'. exact Hk.
Qed.

Lemma w4b12_b2_of : forall m a (bs : list byte) k, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (k + 2 <= length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) [nth k bs Prog.RcParse.cp_z; nth (S k) bs Prog.RcParse.cp_z].
Proof.
  intros m a bs k (H0 & H1 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  assert (Ei : i = 0%nat \/ i = 1%nat) by lia. destruct Ei as [-> | ->].
  - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. cbn [nth_error].
    rewrite (H k ltac:(lia)). apply nth_error_nth'. lia.
  - change (Z.of_nat 1) with 1. cbn [nth_error].
    replace (a + Z.of_nat k + 1) with (a + Z.of_nat (S k)) by lia.
    rewrite (H (S k) ltac:(lia)). apply nth_error_nth'. lia.
Qed.

Lemma w4b12_le2 : forall b0 b1 : byte,
  [b0; b1] = lib.Lib.Mem.le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)).
Proof.
  intros b0 b1. pose proof (w4b12_ubv b0) as R0. pose proof (w4b12_ubv b1) as R1.
  unfold lib.Lib.Mem.le2. rewrite lib.Lib.MState.unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b0 + 256 * bv_unsigned b1) / 256) with (bv_unsigned b1)
    by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    change (2 ^ 8) with 256.
  - rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The shadow byte of phi + c (7 <= c <= 42) is 0 when the block (phi, L) with 50 <= L is addressable (w4b_sh26). *)
Lemma w4b12_sh : forall m phi L c, B.AsanRT.addressable m phi (B.ACtlK.a_size L) -> 50 <= L -> 7 <= c <= 42 ->
  ACtlCutP.b8 m (Z.shiftr (phi + c) 3 + B.ACtlK.ASAN_K) 0.
Proof.
  intros m phi L c HA HL Hc.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + c) 8 ltac:(lia)) as Hr.
  assert (H8 : B.AsanRT.addressable m (phi + (c - (phi + c) mod 8)) 8)
    by (apply (B.AsanRTFacts.addressable_sub m phi (B.ACtlK.a_size L));
        [exact HA | lia | lia | unfold B.ACtlK.a_size; lia]).
  destruct (B.AsanRTFacts.meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (c - (phi + c) mod 8)) 3 = Z.shiftr (phi + c) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + c) 8 ltac:(lia)) as D.
    replace (phi + (c - (phi + c) mod 8)) with ((phi + c) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* Build a list from a function defined on [0, n) (Seg/F12.v f12_ex_list). *)
Lemma w4b12_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
  exists l, length l = n /\ forall i, (i < n)%nat -> f i = nth_error l i.
Proof.
  intros f n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - assert (H' : forall i, (i < n)%nat -> f i <> None) by (intros i Hi; apply H; lia).
    destruct (IH H') as (l & Hl & Hf).
    destruct (f n) as [b|] eqn:Eb; [|exfalso; exact (H n ltac:(lia) Eb)].
    exists (l ++ [b]). split; [rewrite length_app, Hl; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia. exact (Hf i Hlt).
    + assert (Ei : i = n) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. exact Eb.
Qed.

(* -- memory transports -- *)
(* A byte above the image (no segment holds it) reads as the raw byte, and is not read-only. *)
Lemma w4b12_mrd_high : forall m a, 0x5fe000 <= a < 2 ^ 64 ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a).
Proof.
  intros m a Ha. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  unfold lib.Lib.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment B.Img0.rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [s|] eqn:E; [|reflexivity].
  apply w4b_find_segment_low in E. rewrite lib.Lib.MState.unsigned_lit in E by lia. lia.
Qed.

Lemma w4b12_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false.
Proof.
  intros a Ha. unfold lib.Lib.Mem.ro_addr, lib.Lib.Mem.wa.
  destruct (find_segment B.Img0.rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [s|] eqn:E; [|reflexivity].
  apply w4b_find_segment_low in E. rewrite lib.Lib.MState.unsigned_lit in E by lia. lia.
Qed.

(* The spill base of a spill is register 9's value (the cell lies in [0, 2^64)). *)
Lemma w4b12_spill_base : forall regs A A' m off v,
  ACtlCut.rgv regs 9 A -> ACtlCut.rgv regs 9 A' -> 0 <= A < 2 ^ 63 -> 0 <= off <= 440 ->
  ACtlCutP.q64 m (A' + off) v -> A' = A.
Proof.
  intros regs A A' m off v HA HA' HAb Hoff Hq. unfold ACtlCut.rgv in *.
  pose proof (eq_trans (eq_sym HA') HA) as E.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in E.
  unfold ACtlCutP.q64, lib.Lib.Mem.bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  change (2 ^ 63) with 9223372036854775808 in HAb. change (2 ^ 64) with 18446744073709551616 in Hq1.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4b12_spill_q : forall regs A m off v, ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off <= 440 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs A m off v HA HAb Hoff (A' & HA' & Hq).
  pose proof (w4b12_spill_base regs A A' m off v HA HA' HAb Hoff Hq) as E. subst A'. exact Hq.
Qed.

Lemma w4b12_ba_keep : forall m m' a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (a + i)) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + i))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). apply HK. lia.
Qed.

Lemma w4b12_spill_keep : forall regs regs' m m' A off v, ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off <= 440 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v HA HAb Hoff E9 HK Hs.
  pose proof (w4b12_spill_q regs A m off v HA HAb Hoff Hs) as Hq.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  unfold ACtlCutP.q64 in *. apply (w4b12_ba_keep m m' (A + off) _ Hq).
  rewrite lib.Lib.Mem.length_le8. intros i Hi. apply HK. lia.
Qed.

Lemma w4b12_addr_keep : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) HK. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  rewrite HK by exact Hi. exact Hb.
Qed.

Lemma w4b12_stk_keep : forall m m' lo hi, lib.Lib.Frame.stk B.Img0.rsegs m lo hi ->
  (forall a, lo <= a < hi -> wview B.Img0.rsegs m (lib.Lib.Mem.wa a) <> None ->
     wview B.Img0.rsegs m' (lib.Lib.Mem.wa a) <> None) ->
  (forall a, lo <= a < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a) \/
     exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa a) = Some b) ->
  lib.Lib.Frame.stk B.Img0.rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) HW HR. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split; [exact (HW a Ha Hv)|].
  destruct (HR a Ha) as [E | Hs]; [exists b; rewrite E; exact Hb | exact Hs].
Qed.

(* A frame sub-range of a byte-backed stk range holds a writable CB cell (Seg/F12.v f12_stk_cb). *)
Lemma w4b12_stk_cb : forall m lo hi a n, lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs].
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn.
  destruct (w4b12_ex_list (fun i => lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat i))) n) as (bs & Hl & Hf).
  { intros i Hi. destruct (H (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb). rewrite Hb. discriminate. }
  exists bs. split; [exact Hl|]. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r.
    split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hf. lia.
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. rewrite Nat.add_0_r.
    split; [lia|]. split; [lia|]. intros i Hi. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* The CB cell's bytes. *)
Lemma w4b12_cb_bytes : forall m a n bs,
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros m a n bs ((_ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
  rewrite app_nil_r in Hb. exact Hb.
Qed.

(* The view at a visible address is the raw read. *)
Lemma w4b12_aview_vis : forall (W : Reusable.YA0n.world segs) mem a, Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Hh. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
  rewrite Hh. reflexivity.
Qed.

(* The ASan runtime cells (in the image) survive any change that keeps the image bytes. *)
Lemma w4b12_cells_keep : forall m m', B.AsanRT.asan_cells m ->
  (forall x, 0x10000 <= x < 0x5fe000 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  B.AsanRT.asan_cells m'.
Proof.
  intros m m' Hc HK.
  assert (Hb : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> 0x10000 <= a ->
                 a + Z.of_nat (length bs) <= 0x5fe000 -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H Ha Hl. apply (w4b12_ba_keep m m' a bs H). intros i Hi. apply HK. lia. }
  unfold B.AsanRT.asan_cells in *.
  destruct Hc as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
  refine (conj (Hb _ _ C1 _ _) (conj (Hb _ _ C2 _ _) (conj (Hb _ _ C3 _ _) (conj (Hb _ _ C4 _ _) (conj (Hb _ _ C5 _ _)
    (conj (Hb _ _ C6 _ _) (conj (Hb _ _ C7 _ _) (conj (Hb _ _ C8 _ _) (conj (Hb _ _ C9 _ _) (conj (Hb _ _ C10 _ _)
    (conj (Hb _ _ C11 _ _) (conj (Hb _ _ C12 _ _) (conj (Hb _ _ C13 _ _) (conj (Hb _ _ C14 _ _) (conj (Hb _ _ C15 _ _)
    (conj (Hb _ _ C16 _ _) (Hb _ _ C17 _ _)))))))))))))))));
    cbn [length]; rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4;
    unfold B.AsanRT.CELL_K, B.AsanRT.GOT_CELL_K, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.GOT_REPLACE,
      B.AsanRT.UAR, B.AsanRT.GOT_UAR, B.AsanRT.CANPOISON, B.AsanRT.HIEND, B.AsanRT.GOT_HIEND, B.AsanRT.MIDBEG,
      B.AsanRT.GOT_MIDBEG, B.AsanRT.MIDEND, B.AsanRT.GOT_MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
      B.AsanRT.GOT_REAL_MEMSET; cbn; lia.
Qed.

(* The fake frame of class 6 lies above the image: the fake stack is application memory (layout_ok) and a live
   frame's position is non-negative (wf_fs). *)
Lemma w4b12_frame_high : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  0x60a000 <= Reusable.YG0f.frame_addr ly 6 pos.
Proof.
  intros ly S W mem md pos HAR Hin.
  destruct HAR as (HARm & _).
  destruct HARm as [Hwf _ _ Hlay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct Hlay as [_ _ _ _ _ _ _ _ _ _ _ Happ _ _ _ _ _ _ _ _ _].
  pose proof (proj1 (Forall_forall _ _) Happ (Reusable.YG0f.ly_F ly, Reusable.YG0f.kFakeStackSize)
                ltac:(unfold Reusable.YG0f.owned_extents; right; right; right; left; reflexivity)) as HF.
  cbn [fst snd] in HF. unfold Reusable.YG0f.in_app in HF.
  destruct Hwf as [_ _ _ _ _ _ _ _ _ _ _ _ Hfs _ _ _ _ _ _ _].
  destruct Hfs as [_ _ Hl].
  pose proof (proj1 (Forall_forall _ _) Hl (6, pos) Hin) as Hp. cbn [fst snd] in Hp.
  unfold Reusable.YG0f.frame_addr, Reusable.YG0f.fs_frame_off, Reusable.YG0f.kFakeFramesOff.
  change (6 * Z.shiftl 1 Reusable.YG00.kStackSizeLog) with 6291456.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.


(* -- arithmetic of shadow indexes (Seg/F12.v f12_sh_back and the hull of a frame range) -- *)
Lemma w4b12_div8 : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof. intros x c H. Z.div_mod_to_equations. lia. Qed.

Lemma w4b12_mod8 : forall x c, x mod 8 = 0 -> (x + 8 * c) mod 8 = 0.
Proof. intros x c H. Z.div_mod_to_equations. lia. Qed.

Lemma w4b12_shidx : forall x t, x mod 8 = 0 -> (x + t) / 8 = x / 8 + t / 8.
Proof. intros x t H. Z.div_mod_to_equations. lia. Qed.

Lemma w4b12_sh_back : forall fr x, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  ACtlCutP.Sfr fr + 42 <= B.AsanRT.shadow_addr x < ACtlCutP.Sfr fr + 51 -> fr + 336 <= x < fr + 408.
Proof.
  intros fr x H8 Hfr Hx0 Hx. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4b12_hull : forall fr a n s, fr mod 8 = 0 -> 0 <= fr -> fr + 64 <= a -> 0 < n -> a + n + 64 <= fr + 4096 ->
  Reusable.YG0f.shadow_addr a / 8 * 8 <= s < Reusable.YG0f.shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  ACtlCutP.Sfr fr <= s < ACtlCutP.Sfr fr + 512.
Proof.
  intros fr a n s H8 Hfr Ha Hn Han Hs.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4b12_shadow_band : forall x, (4096 <= x < 0x7fff7000 \/ 0x10007fff8000 <= x < 0x800000000000) ->
  (0x7fff8000 <= B.AsanRT.shadow_addr x < 0x8fff7000 \/ 0x2008fff7000 <= B.AsanRT.shadow_addr x < 0x10007fff8000).
Proof. intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* ctrl's signed shadow check is the core's unsigned one. *)
Lemma w4b12_sok : forall x (b : byte), B.AsanRT.shadow_ok x (bv_signed b) -> Reusable.YG0v.saddr_ok x (bv_unsigned b).
Proof.
  intros x b H. pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (Hs : bv_signed b = bv_unsigned b \/ bv_signed b = bv_unsigned b - 256).
  { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. cbn [Z.of_N] in *.
    change (2 ^ 8) with 256 in *. Z.div_mod_to_equations. lia. }
  unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. change (2 ^ 8) with 256 in Hr.
  unfold B.AsanRT.shadow_ok in H. unfold Reusable.YG0v.saddr_ok. lia.
Qed.

(* A carried byte list reads Some at each of its bytes (Seg/F12.v ba_rd). *)
Lemma w4b12_ba_some : forall m a bs x, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m a bs x (HA & HL & H) Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (a + (x - a)) with x in HH by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* range_addressable over the view from ctrl's addressable, when the shadow bytes are visible (plan 2.4 T5). *)
Lemma w4b12_ra : forall (W : Reusable.YA0n.world segs) m p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n (H0 & Hn & He & HA) HV x Hx.
  destruct (HA (x - p) ltac:(lia)) as (_ & b & Hb & Hok). replace (p + (x - p)) with x in Hb, Hok by lia.
  exists (bv_unsigned b). split; [|exact (w4b12_sok x b Hok)].
  assert (E : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite E, w4b12_aview_vis.
  - unfold lib.Lib.Mem.wa in Hb. rewrite Hb. reflexivity.
  - specialize (HV (x - p) ltac:(lia)). replace (p + (x - p)) with x in HV by lia. exact HV.
Qed.

(* A state related to an MS state by MemNorm.ms_rel is that state with its own memory (Seg/F12.v f12_ms_rel_MS). *)
Lemma w4b12_ms_rel_MS : forall s R F pc fc rv m0 ro,
  B.MemNorm.ms_rel B.Img0.rsegs s (lib.Lib.MState.MS R F pc fc rv m0 ro) ->
  s = lib.Lib.MState.MS R F pc fc rv (ms_mem s) ro /\ B.MemNorm.mem_rel B.Img0.rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem lib.Lib.MState.MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* FRAC across a change that keeps its spill cells, frame words and saved registers, with a new frame-shadow list. *)
Lemma w4b12_frac_keep : forall (cx : ACtlCut.ctlcx) fr sel (regs regs' : bvmap 5 word) (m m' : word -> option byte) A,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, (A + 40 <= x < A + 56 \/ A + 336 <= x < A + 344 \/ fr <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096 \/
              ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  (exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' A HF HA HAb E2 E3 E4 E8 E9 E19 E26 HK Hsh'.
  destruct HF as (A0 & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA448 & HS4096 & HSapp & Hq336 & Hq48 & Hq40 & Hhd0 & Hhd16 & _ & Hsaved & Htrail).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as [Hb0 _]. exact Hb0. }
  assert (EA : A0 = A).
  { apply w4b_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | lia |].
    unfold ACtlCut.rgv in Hr9, HA. rewrite <- Hr9, <- HA. reflexivity. }
  subst A0.
  assert (KB : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
                 (forall i, 0 <= i < Z.of_nat (length bs) ->
                    (A + 40 <= a + i < A + 56 \/ A + 336 <= a + i < A + 344 \/ fr <= a + i < fr + 24 \/
                     fr + 4088 <= a + i < fr + 4096 \/ ACtlCut.c_sp cx - 104 <= a + i < ACtlCut.c_sp cx)) ->
                 lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs)
    by (intros a bs H Hp; apply (w4b12_ba_keep m m' a bs H); intros i Hi; apply HK; apply Hp; exact Hi).
  unfold ACtlCutP.q64 in *.
  exists A, sp. unfold ACtlCut.rgv in *.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ|].
  split; [rewrite E4; exact Hr4|]. split; [rewrite E8; exact Hr8|]. split; [rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|]. split; [rewrite E19; exact Hr19|]. split; [rewrite E26; exact Hr26|].
  do 8 (split; [assumption|]).
  split; [apply (KB _ _ Hq336); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia|].
  split; [apply (KB _ _ Hq48); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia|].
  split; [apply (KB _ _ Hq40); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia|].
  split; [apply (KB _ _ Hhd0); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia|].
  split; [apply (KB _ _ Hhd16); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia|].
  split; [exact Hsh'|].
  split; [apply (KB _ _ Hsaved); unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8;
          intros i Hi; cbn in Hi; lia|].
  apply (KB _ _ Htrail); rewrite lib.Lib.Mem.length_le8; intros i Hi; lia.
Qed.

(* The exit's record bundle FRB from facts on one memory (Seg/F12.v :1755-1899). *)
Lemma w4b12_frb : forall (cx : ACtlCut.ctlcx) (j : nat) fr phi A (regs : bvmap 5 word) (m : word -> option byte),
  (forall a, fr <= a < fr + 4096 -> B.AsanRT.app_mem a) -> 0 <= fr -> 4096 <= phi ->
  0 <= ACtlCutP.flen cx j ->
  (forall a, phi <= a < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) -> B.AsanRT.app_mem a) ->
  (phi + B.ACtlK.a_size (ACtlCutP.flen cx j) <= fr \/ fr + 4096 <= phi) ->
  fr + 4096 + 4672 <= Reusable.YG0d.spZ regs ->
  phi + B.ACtlK.a_size (ACtlCutP.flen cx j) + 4672 <= Reusable.YG0d.spZ regs ->
  Reusable.YG0d.spZ regs < 2 ^ 64 ->
  ACtlCutP.q64 m (A + 272) (B.Prog.SlotModel.b2z (B.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j)) ->
  ACtlCutP.q64 m (A + 312) (if B.Prog.SlotModel.t_big (ACtlCut.c_in cx) j then phi + 18 else 0) ->
  ACtlCutP.q64 m (A + 248) (1 - B.Prog.SlotModel.b2z (B.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j)) ->
  ACtlCutP.q64 m (A + 112) (fr + 186) -> ACtlCutP.q64 m (A + 96) (fr + 180) ->
  (50 <= ACtlCutP.flen cx j -> lib.Lib.Mem.bytes_at B.Img0.rsegs m phi (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (fr + 176) (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j) ->
  B.AsanRT.addressable m (fr + 176) 36 ->
  B.AsanRT.addressable m phi (B.ACtlK.a_size (ACtlCutP.flen cx j)) ->
  ACtlCutP.FRB cx j fr phi A (fr + 176) regs m.
Proof.
  intros cx j fr phi A regs m Hfapp Hfr0 Hp4096 Hfl0 Hpapp Hdj HspF HspP Hsp64 Q272 Q312 Q248 Q112 Q96 HGb HpB HaB HAd.
  assert (HBW : ACtlCutP.BWA.BCMP_WRAP_K = 4560) by reflexivity.
  assert (Hasz : ACtlCutP.flen cx j <= B.ACtlK.a_size (ACtlCutP.flen cx j)) by (unfold B.ACtlK.a_size; lia).
  unfold ACtlCutP.FRB. rewrite HBW.
  split; [intros a Ha; apply Hfapp; lia|].
  split.
  { exists (B.Prog.SlotModel.b2z (B.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j)).
    split; [exact Q272|].
    unfold B.Prog.SlotModel.b2z. destruct (B.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j).
    - split; [lia|]. split; [intros _; lia | intros E; discriminate].
    - split; [lia|]. split; [intros E; discriminate | intros _; reflexivity]. }
  split; [left; lia|]. split; [left; lia|]. split; [left; lia|].
  split; [intros H50; split; [destruct Hdj as [Hd|Hd]; [left|right]; lia | left; lia]|].
  intros H8819.
  assert (Hbig : B.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true).
  { unfold B.Prog.SlotModel.t_8819 in H8819. apply andb_prop in H8819. destruct H8819 as (H1 & _).
    apply andb_prop in H1. exact (proj1 H1). }
  assert (Hflen : 50 <= ACtlCutP.flen cx j) by (unfold ACtlCutP.flen; apply Z.leb_le; exact Hbig).
  rewrite Hbig in Q312.
  assert (Hhdr : Prog.RcParse.cp_hdr (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
                   (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = true) by exact H8819.
  pose proof (w4b12_t_g_length (ACtlCut.c_in cx) j) as HGL.
  assert (HBlen : length (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j) = 36%nat) by apply Prog.RcParse.ctrlparse_length.
  assert (Hknz : fst (Prog.RcParse.ctrlparse (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
                        (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) <> 0).
  { unfold Prog.RcParse.ctrlparse. rewrite Hhdr. cbn [fst].
    pose proof (Prog.RcParse.cp_kind_range (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)). lia. }
  pose proof (Prog.RcParse.ctrlparse_fields _ _ Hknz) as HBf. cbv zeta in HBf.
  destruct HBf as (_ & _ & _ & E20 & E21 & _).
  assert (EB : B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j =
               Prog.RcParse.cp_struct (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)
                 (Prog.RcParse.cp_kind (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))
    by (unfold B.Prog.SlotModel.t_B, Prog.RcParse.ctrlparse; rewrite Hhdr; reflexivity).
  destruct (w4b12_B_fields (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) ltac:(rewrite HGL; lia)) as (E6a & E6b).
  pose proof (HGb Hflen) as HGphi.
  split.
  { (* rec_inv *)
    unfold ACtlCutP.rec_inv.
    split; [lia|]. split; [unfold B.ACtlK.a_size in *; lia|]. split; [exact Hflen|].
    split; [pose proof (Prog.RcParse.ctrlparse_kind_range (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
                          (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)); unfold B.Prog.SlotModel.t_k; lia|].
    split; [intros a Ha; apply Hpapp; lia|].
    split; [exact Q312|].
    split.
    { unfold B.Prog.SlotModel.t_blk, ACtlCutP.RFR.bsl. replace (phi + 18) with (phi + Z.of_nat 18) by (cbn; lia).
      apply w4b12_sub; [exact HGphi | rewrite HGL; lia]. }
    split.
    { unfold ACtlCutP.RFR.bsl. replace (phi + 34) with (phi + Z.of_nat 34) by (cbn; lia).
      apply w4b12_sub; [exact HGphi | rewrite HGL; lia]. }
    exists (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 14 +
            256 * Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 15),
           (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 14),
           (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 15),
           (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 16),
           (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 17).
    split; [exact Q248|].
    split.
    { unfold ACtlCutP.u16. replace (fr + 176 + 20) with (fr + 176 + Z.of_nat 20) by (cbn; lia).
      pose proof (w4b12_b2_of m (fr + 176) _ 20 HpB ltac:(rewrite HBlen; lia)) as HU.
      unfold B.Prog.SlotModel.t_B in HU. rewrite E20, E21 in HU.
      unfold Prog.RcParse.cp_v. rewrite <- w4b12_le2. exact HU. }
    split; [lia|]. split; [lia|].
    split; [replace (phi + 14) with (phi + Z.of_nat 14) by (cbn; lia);
            exact (w4b12_b8_of m phi _ 14 HGphi ltac:(rewrite HGL; lia))|].
    split; [replace (phi + 15) with (phi + Z.of_nat 15) by (cbn; lia);
            exact (w4b12_b8_of m phi _ 15 HGphi ltac:(rewrite HGL; lia))|].
    split; [replace (phi + 16) with (phi + Z.of_nat 16) by (cbn; lia);
            exact (w4b12_b8_of m phi _ 16 HGphi ltac:(rewrite HGL; lia))|].
    split; [replace (phi + 17) with (phi + Z.of_nat 17) by (cbn; lia);
            exact (w4b12_b8_of m phi _ 17 HGphi ltac:(rewrite HGL; lia))|].
    split; [unfold Prog.RcParse.cp_v; apply w4b12_ubv|].
    split; [unfold Prog.RcParse.cp_v; apply w4b12_ubv|].
    split; [unfold Prog.RcParse.cp_v; apply w4b12_ubv|].
    split; [unfold Prog.RcParse.cp_v; apply w4b12_ubv|].
    split; [exact (w4b12_sh m phi (ACtlCutP.flen cx j) 14 HAd Hflen ltac:(lia))|].
    split; [exact (w4b12_sh m phi (ACtlCutP.flen cx j) 15 HAd Hflen ltac:(lia))|].
    split; [exact (w4b12_sh m phi (ACtlCutP.flen cx j) 16 HAd Hflen ltac:(lia))|].
    split; [exact (w4b12_sh m phi (ACtlCutP.flen cx j) 17 HAd Hflen ltac:(lia))|].
    split; [reflexivity|].
    assert (Hk1 : B.Prog.SlotModel.t_k (ACtlCut.c_in cx) j = 1 <->
                  (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 16 = 0 /\
                   Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 17 = 0)).
    { unfold B.Prog.SlotModel.t_k. rewrite Prog.RcParse.ctrlparse_filler. split.
      - intros (_ & A1 & A2). split; assumption.
      - intros (A1 & A2). split; [exact Hhdr | split; assumption]. }
    destruct (Z.eqb_spec (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 16) 0) as [E16|E16].
    - destruct (Z.eqb_spec (Prog.RcParse.cp_v (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 17) 0) as [E17|E17].
      + rewrite (proj2 (Z.eqb_eq (B.Prog.SlotModel.t_k (ACtlCut.c_in cx) j) 1) (proj2 Hk1 (conj E16 E17))).
        reflexivity.
      + replace (B.Prog.SlotModel.t_k (ACtlCut.c_in cx) j =? 1) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. intros HKk. exact (E17 (proj2 (proj1 Hk1 HKk))).
    - replace (B.Prog.SlotModel.t_k (ACtlCut.c_in cx) j =? 1) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. intros HKk. exact (E16 (proj1 (proj1 Hk1 HKk))). }
  split.
  { exists (fr + 186), (firstn 6 (skipn 10 (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j))),
           (firstn 6 (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
    split; [exact Q112|].
    split; [replace (fr + 186) with (fr + 176 + Z.of_nat 10) by (cbn; lia);
            apply w4b12_sub; [exact HpB | rewrite HBlen; lia]|].
    split; [rewrite length_firstn, length_skipn, HBlen; reflexivity|].
    split; [pose proof (w4b12_sub m phi _ 0 6 HGphi ltac:(rewrite HGL; lia)) as HS;
            change (Z.of_nat 0) with 0 in HS; rewrite Z.add_0_r in HS; exact HS|].
    split; [rewrite length_firstn, HGL; reflexivity|].
    split; [rewrite EB, E6a; apply w4b12_memcmp_self; rewrite length_firstn, HGL; lia|].
    split; [replace (fr + 186) with (fr + 176 + 10) by lia;
            apply (B.AsanRTFacts.addressable_sub m (fr + 176) 36); [exact HaB | lia | lia | lia]|].
    split; [apply Hfapp; lia|]. split; [apply Hfapp; lia|].
    split; [left; lia|]. split; [left; lia|]. left; lia. }
  exists (fr + 180), (firstn 6 (skipn 4 (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j))),
         (firstn 6 (skipn 6 (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))).
  split; [exact Q96|].
  split; [replace (fr + 180) with (fr + 176 + Z.of_nat 4) by (cbn; lia);
          apply w4b12_sub; [exact HpB | rewrite HBlen; lia]|].
  split; [rewrite length_firstn, length_skipn, HBlen; reflexivity|].
  split; [pose proof (w4b12_sub m phi _ 6 6 HGphi ltac:(rewrite HGL; lia)) as HS;
          change (Z.of_nat 6) with 6 in HS; exact HS|].
  split; [rewrite length_firstn, length_skipn, HGL; reflexivity|].
  split; [rewrite EB, E6b; apply w4b12_memcmp_self; rewrite length_firstn, length_skipn, HGL; lia|].
  split; [replace (fr + 180) with (fr + 176 + 4) by lia;
          apply (B.AsanRTFacts.addressable_sub m (fr + 176) 36); [exact HaB | lia | lia | lia]|].
  split; [apply Hfapp; lia|]. split; [apply Hfapp; lia|].
  split; [left; lia|]. split; [left; lia|]. left; lia.
Qed.


(* The shadow byte of a frame byte fr + t is S(fr) + t / 8; it is one of the nine (42 .. 50) iff t is in [336, 408). *)
Lemma w4b12_fsh : forall fr t, fr mod 8 = 0 -> 0 <= fr -> 0 <= t < 4096 ->
  B.AsanRT.shadow_addr (fr + t) = ACtlCutP.Sfr fr + t / 8 /\ 0 <= t / 8 < 512 /\ (42 <= t / 8 < 51 <-> 336 <= t < 408).
Proof.
  intros fr t H8 Hfr Ht. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. rewrite (w4b12_shidx fr t H8).
  split; [lia|]. Z.div_mod_to_equations. lia.
Qed.


(* The shared stage of seg_F12 and seg_F12_298 (Seg/F12.v f12_at): from either entry pc (0x82304 with the ingest
   result in a0, or 0x82308), F12F.f12_pre_F_on to __asan_memcpy's entry (on the normalized memory: its mem_inv
   premise, B.MemNormF.evtF_normalize_ro back to the cut memory under ctl_rt's ro_agree), the copy through
   YCbq.aj_intrin_at with AMEMCPY, the raw facts by ctl_post_memcpy, then C_B82340_at. *)
Lemma w4b12_at : forall POST (j : nat) (cx : ACtlCut.ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3 phi (pc r : Z),
  ctl_from POST (ix_cut C_B82340_at [Z.of_nat j]) ->
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 14 + 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat j]) + 1 ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  ACtlCut.c_n cx < 2 ^ 26 -> (j <= 255)%nat ->
  ACtlCutP.HB mem3 phi (ACtlCutP.flen cx j) ->
  ACtlCut.rgv regs3 18 phi -> ACtlCut.rgv regs3 20 (ACtlCutP.flen cx j) ->
  ACtlCutP.FTURN cx j phi regs3 mem3 ->
  ACtlCutP.LK cx fr j regs3 mem3 -> ACtlCutP.FM cx j phi fr regs3 mem3 -> ACtlCutP.FSj cx fr j regs3 mem3 ->
  ACtlCutP.RECR cx fr j mem3 ->
  (50 <= ACtlCutP.flen cx j -> lib.Lib.Mem.bytes_at segs mem3 phi (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) ->
  ACtlCutP.FPS cx fr j mem3 -> ACtlCutP.F272 cx j regs3 mem3 -> ACtlCutP.RCA fr mem3 ->
  ACtlCutP.FS9 cx j regs3 mem3 ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  (pc = 0x82308 \/ (pc = 0x82304 /\ ACtlCut.rgv regs3 10 r /\ 0 <= r < 2 ^ 63)) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs pc regs3 mem3 md3) (POST cx).
Proof.
  intros POST j cx fr k ly3 S3 W3 regs3 mem3 md3 phi pc r H40 HB HJ HF HL Hk HFRAC HP Hn Hj HHB H18 H20 HFT HLK
    HFM HFS HREC HGb HFPS H272 HRCA HS9 Hrt Hpc.
  (* ---- the cut's facts ---- *)
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  unfold B.AsanRT.APPMEM_END in HSapp.
  assert (HA63 : 0 <= A < 2 ^ 63) by lia.
  pose proof HB as ((Hafn & _) & _).
  pose proof Hafn as (_ & _ & _ & Hgp & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _).
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in Hpres, Hslo.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [HCE _]. unfold Reusable.YG0f.ASAN_CEIL in HCE.
  (* the owned class-6 frame: visible, application memory above the image, below the stack *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4b_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  pose proof (w4b12_frame_high ly3 S3 W3 mem3 md3 _ HAR Hin6) as Hfhi. rewrite Efr in Hfhi.
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 _ HAR Hin6) as (_ & Hfceil & Hfapp).
  rewrite Efr in Hfceil, Hfapp. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 _ HAR Hin6) as (_ & _ & Hfby & Hfsh).
  rewrite Efr in Hfby, Hfsh. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfby.
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512 in Hfsh.
  assert (ESh : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (unfold Reusable.YG0f.shadow_addr, ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K,
          Reusable.YG0f.SHADOW_OFF; lia).
  rewrite ESh in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HK3v : ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (Eq8 : fr = 8 * (fr / 8)) by (Z.div_mod_to_equations; lia).
  assert (Hfr_app : forall a, fr <= a < fr + 4096 -> B.AsanRT.app_mem a)
    by (intros a Ha; unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  assert (V_fr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfby a Ha)))).
  assert (V_sh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hfsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as [[Hv _] _].
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hv by lia. exact Hv. }
  assert (P_sh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> mem3 (Z_to_bv 64 a) <> None).
  { intros a Ha. destruct (Hfsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as [[_ (b & Hb)] _].
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hb by lia. rewrite Hb. discriminate. }
  assert (V_st : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hpres a Ha))).
  (* the turn's live heap block *)
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hphi)
    as (_ & Hp4096 & Hpceil & Hpapp & Hpby & _ & Hfl).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 _ HAR Hphi Hin6) as Hdj.
  rewrite Efr in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hdj.
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = B.ACtlK.a_size (ACtlCutP.flen cx j))
    by (unfold Reusable.YG00.req_size, B.ACtlK.a_size; destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia).
  rewrite Hreq in Hpceil, Hpapp, Hpby, Hdj.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hpapp.
  assert (Hasz : ACtlCutP.flen cx j <= B.ACtlK.a_size (ACtlCutP.flen cx j) /\ 1 <= B.ACtlK.a_size (ACtlCutP.flen cx j))
    by (unfold B.ACtlK.a_size; lia).
  assert (Hp_app : forall a, phi <= a < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) -> B.AsanRT.app_mem a)
    by (intros a Ha; unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  assert (V_hp : forall a, phi <= a < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hpby a Ha)))).
  assert (V_hs : forall a, phi <= a < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr a)) = false).
  { intros a Ha.
    pose proof (w4b_heap_sh1 ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) a HAR Hphi ltac:(rewrite Hreq; lia))
      as (_ & _ & Hv).
    specialize (Hv (Z.shiftr a 3 + B.AsanRT.ASAN_K) ltac:(lia)).
    rewrite Z.shiftr_div_pow2 in Hv by lia. exact Hv. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & V_img0).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in V_img0.
  pose proof (ctl_kind_name_shadow_vis ly3 S3 W3 mem3 md3 HAR) as (_ & _ & V_kn).
  (* the cut's spills and records *)
  pose proof HLK as (_ & P240 & HOUR & HFLI).
  pose proof HFLI as (H27 & P168 & P96 & P112 & P120 & P128 & P136 & P144 & P152 & P280 & P160 & P176 & P192 &
    P200 & P216 & P208 & P104 & P256 & P264 & P288 & P296 & P304 & HadOur & HstkF & HRAD & HKNT & P168b & P88).
  pose proof HRAD as (HRid & HRfg & HRfst).
  pose proof (w4b12_spill_q regs3 A mem3 200 _ Hr9 HA63 ltac:(lia) P200) as Q200.
  pose proof (w4b12_spill_q regs3 A mem3 208 _ Hr9 HA63 ltac:(lia) P208) as Q208.
  pose proof HREC as ((HIDb & HIDok) & (HFGb & HFGok)).
  pose proof (w4b12_t_FG_length (ACtlCut.c_in cx) j) as HFGL.
  (* ---- the normalized memory the run starts from ---- *)
  pose proof Hrt as (HAC3 & HSWc & _ & HRO3).
  (* route (C): the owned frame's shadow is the cut's own shadow (cut_shadow, frames disjunct) *)
  assert (HSWF : B.ShadowRwOn.shadow_rw_on (fun a => ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512) mem3).
  { refine (B.ShadowRwOn.shadow_rw_on_mono _ _ mem3 _ HSWc). intros a Ha. left.
    exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr, ESh.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. exact Ha. }
  assert (HRO : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact HRO3.
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 HRO) as HREL0.
  assert (MRD0 : forall x, lib.Lib.Mem.mrd B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) x =
                           lib.Lib.Mem.mrd B.Img0.rsegs mem3 x)
    by (intros x; symmetry; exact (B.MemNorm.mrd_rel B.Img0.rsegs mem3 _ x HREL0)).
  assert (WV0 : forall x, 0x5fe000 <= x < 2 ^ 64 ->
                  wview B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (lib.Lib.Mem.wa x) =
                  wview B.Img0.rsegs mem3 (lib.Lib.Mem.wa x))
    by (intros x Hx; exact (B.MemNorm.wview_rel_rw B.Img0.rsegs mem3 _ _ HREL0 (w4b12_ro_false x Hx))).
  assert (HstkN : lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (w4b12_stk_keep mem3 _ fr (fr + ACtlCutP.FRAME_BYTES) HstkF).
    - intros a Ha Hw. rewrite WV0 by lia. exact Hw.
    - intros a Ha. left. apply MRD0. }
  destruct (w4b12_stk_cb _ fr (fr + ACtlCutP.FRAME_BYTES) (fr + 336) 72 HstkN ltac:(lia) ltac:(rewrite HFBv; cbn; lia))
    as (jk & Hjkl & HRWD).
  (* ---- the run 0x82304 / 0x82308 -> __asan_memcpy (F12F.f12_pre_F_on, route (C)) ---- *)
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (R_sh : Lib.ExecF.rng RNG (ACtlCutP.Sfr fr + 42) 9).
  { apply B.ProgBridge.rng_of_visible. split; [rewrite HK3v; lia|]. split; [rewrite HK3v; lia|].
    intros a Ha. apply V_sh. lia. }
  assert (R200 : Lib.ExecF.rng RNG (A + 200) 8).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply V_st. lia. }
  assert (R208 : Lib.ExecF.rng RNG (A + 208) 8).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply V_st. lia. }
  evar (Pq : machine_state -> Prop).
  assert (HRUN : Lib.ExecF.evtF B.Img0.rsegs RNG Pq
                   (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
                      lib.Reusable.YK11.fp_csr None (B.MemNorm.normalize B.Img0.rsegs mem3)
                      (lib.Reusable.YK11.seg_rom segs))).
  { unfold Pq, Lib.Regs6ss.mkR_of.
    eapply F12F.f12_pre_F_on with (A := A) (r := r) (K3 := ACtlCutP.Sfr fr) (D := fr + 336) (S0 := ACtlCutP.fragb fr)
      (lo := sp - 2224) (src := B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (junk := jk).
    - exact Hr9.
    - exact Hr19.
    - destruct Hpc as [E|(E & H10 & Hrr)]; [left; exact E | right; exact (conj E (conj H10 Hrr))].
    - rewrite HK3v; lia.
    - rewrite HK3v; lia.
    - lia.
    - unfold ACtlCutP.fragb; lia.
    - unfold ACtlCutP.fragb; lia.
    - replace (fr + 336) with (fr + 8 * 42) by lia. exact (w4b12_mod8 fr 42 Hfr8).
    - replace (fr + 336) with (fr + 8 * 42) by lia. rewrite (w4b12_div8 fr 42 Hfr8). rewrite HK3v.
      unfold B.AsanRT.ASAN_K. lia.
    - unfold ACtlCutP.fragb. replace (fr + 2768) with (fr + 8 * 346) by lia. exact (w4b12_mod8 fr 346 Hfr8).
    - unfold ACtlCutP.fragb. replace (fr + 2768) with (fr + 8 * 346) by lia. rewrite (w4b12_div8 fr 346 Hfr8).
      rewrite HK3v. unfold B.AsanRT.ASAN_K. lia.
    - intros t Ht. apply Hfr_app. lia.
    - apply Hfr_app. unfold ACtlCutP.fragb. lia.
    - apply Hfr_app. unfold ACtlCutP.fragb. lia.
    - rewrite HK3v. lia.
    - rewrite HK3v. lia.
    - rewrite HK3v. lia.
    - unfold ACtlCutP.fragb. rewrite HK3v. lia.
    - apply (B.MemNorm.wr_at_norm B.Img0.rsegs mem3 _ _ _ HREL0).
      + split; [rewrite HK3v; lia|]. split; [rewrite HK3v; lia|]. intros i Hi.
        apply (proj1 (HSWF (ACtlCutP.Sfr fr + 42 + i) ltac:(lia) ltac:(unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG; rewrite HK3v; lia))).
      + intros i Hi. apply w4b12_ro_false. rewrite HK3v. lia.
    - intros mm MU WM HSH.
      apply (w4b12_cells_keep mem3 mm HAC3). intros x Hx.
      rewrite <- MRD0. unfold lib.Lib.Mem.mrd. rewrite (MU (lib.Lib.Mem.wa x)); [reflexivity|].
      rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside]. split; [rewrite HK3v; lia | exact I].
    - exact (B.MemNorm.bytes_at_normalize _ _ _ _ HRO Q200).
    - exact (B.MemNorm.bytes_at_normalize _ _ _ _ HRO Q208).
    - exact (B.MemNorm.bytes_at_normalize _ _ _ _ HRO HFGb).
    - exact HFGL.
    - exact HRWD.
    - apply (w4b12_addr_keep mem3 _ _ _ HRfg). intros i Hi. apply MRD0.
    - exact (B.MemNorm.mem_inv_normalize _ mem3).
    - match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (Reusable.YG0d.spZ regs3) end; rewrite HspZ. split; [lia|]. split; [lia|]. intros a Ha.
      destruct (Hpres a ltac:(lia)) as (_ & b & Hb). split.
      + rewrite WV0 by lia. unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
      + exists b. rewrite MRD0. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
    - match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (Reusable.YG0d.spZ regs3) end; rewrite HspZ. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K. lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (Reusable.YG0d.spZ regs3) end; rewrite HspZ. unfold B.AsanRT.APPMEM_END. lia.
    - unfold B.AsanRT.RT_HI. lia.
    - match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (Reusable.YG0d.spZ regs3) end; rewrite HspZ. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K. left. lia.
    - match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (Reusable.YG0d.spZ regs3) end; rewrite HspZ. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K, ACtlCutP.fragb. left. lia.
    - exact R_sh.
    - exact R200.
    - exact R208. }
  pose proof (B.MemNormF.evtF_normalize_ro RNG Pq _ _ _ _ _ mem3 _ HRO HRUN) as HRUN'.
  apply (Reusable.YA0nR.SRr_fevt_hid segs w4b_wx W3 _ md3 RNG _ (POST cx) (B.ProgBridge.fevt_of_evtF _ _ _ HRUN')
           (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' (s0 & HQ & Hrel & Hros) Hhid Hsbm.
  unfold Pq in HQ.
  destruct HQ as (m1N & Es0 & MU1 & WM1 & MI1 & ST1 & AC1 & SW1 & BS1 & RW1 & AD1 & AS1 & SH1).
  subst s0.
  destruct (w4b12_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as (Ems & HREL1).
  set (mem1 := ms_mem ms') in *.
  rewrite Ems.

  (* ---- the memory after the run (mem1): munch of the nine frame-shadow bytes ---- *)
  assert (MU1' : lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 42, ACtlCutP.Sfr fr + 51)] mem3 mem1)
    by exact (B.MemNorm.munch_rel B.Img0.rsegs _ mem3 _ mem1 m1N HREL0 HREL1 Hros MU1).
  assert (WM1' : lib.Lib.Frame.wmono B.Img0.rsegs mem3 mem1)
    by exact (B.MemNorm.wmono_rel B.Img0.rsegs mem3 _ mem1 m1N HREL0 HREL1 Hros WM1).
  assert (MRD1 : forall x, lib.Lib.Mem.mrd B.Img0.rsegs mem1 x = lib.Lib.Mem.mrd B.Img0.rsegs m1N x)
    by (intros x; exact (B.MemNorm.mrd_rel B.Img0.rsegs mem1 m1N x HREL1)).
  assert (BS1' : lib.Lib.Mem.bytes_at B.Img0.rsegs mem1 (ACtlCutP.fragb fr) (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j))
    by exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs mem1 m1N _ _ HREL1) BS1).
  assert (SH1' : forall kk, 0 <= kk < 9 ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem1 (ACtlCutP.Sfr fr + 42 + kk) [Z_to_bv 8 0])
    by (intros kk Hkk; exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs mem1 m1N _ _ HREL1) (SH1 kk Hkk))).
  assert (RW1b : lib.Lib.Mem.bytes_at B.Img0.rsegs mem1 (fr + 336) jk)
    by exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs mem1 m1N _ _ HREL1) (w4b12_cb_bytes _ _ _ _ RW1)).
  assert (AD1' : B.AsanRT.addressable mem1 (fr + 336) 72)
    by (apply (w4b12_addr_keep m1N mem1 _ _ AD1); intros i Hi; apply MRD1).
  assert (AS1' : B.AsanRT.addressable mem1 (ACtlCutP.fragb fr) 72)
    by (apply (w4b12_addr_keep m1N mem1 _ _ AS1); intros i Hi; apply MRD1).
  assert (HK01 : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 42 <= x < ACtlCutP.Sfr fr + 51) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem1 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hnw. unfold lib.Lib.Mem.mrd. rewrite (MU1' (lib.Lib.Mem.wa x)); [reflexivity|].
    rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside]. split; [exact Hnw | exact I]. }
  assert (Z9 : forall x, ACtlCutP.Sfr fr + 42 <= x < ACtlCutP.Sfr fr + 51 ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem1 (lib.Lib.Mem.wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (SH1' (x - (ACtlCutP.Sfr fr + 42)) ltac:(lia)) as (_ & _ & Hb).
    pose proof (Hb 0%nat ltac:(cbn; lia)) as Hb0. cbn [nth_error] in Hb0.
    replace (ACtlCutP.Sfr fr + 42 + (x - (ACtlCutP.Sfr fr + 42)) + Z.of_nat 0) with x in Hb0 by lia. exact Hb0. }
  assert (FSH1 : forall s, ACtlCutP.Sfr fr <= s < ACtlCutP.Sfr fr + 512 ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem1 (lib.Lib.Mem.wa s) <> None).
  { intros s Hs. destruct (Z_lt_le_dec s (ACtlCutP.Sfr fr + 42)) as [L1|L1];
      [|destruct (Z_lt_le_dec s (ACtlCutP.Sfr fr + 51)) as [L2|L2]].
    - rewrite HK01 by (rewrite HK3v in *; lia). rewrite w4b12_mrd_high by (rewrite HK3v in *; lia).
      exact (P_sh s Hs).
    - rewrite Z9 by lia. discriminate.
    - rewrite HK01 by (rewrite HK3v in *; lia). rewrite w4b12_mrd_high by (rewrite HK3v in *; lia).
      exact (P_sh s Hs). }
  (* the journal across the run: the nine bytes are the owned frame's shadow *)
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
      (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 W3 mem1 md' k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS w4b_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 md'
             (fun a => ACtlCutP.Sfr fr + 42 <= a < ACtlCutP.Sfr fr + 51) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1' x); [reflexivity|].
      cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hxr.
      destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 42) (bv_unsigned x)) as [H1|H1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 51)) as [H2|H2]|].
      + pose proof (Z9 (bv_unsigned x) ltac:(lia)) as Hz.
        rewrite w4b12_mrd_high in Hz by (rewrite HK3v in *; lia).
        unfold lib.Lib.Mem.wa in Hz. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hz. rewrite Hz. discriminate.
      + rewrite (MU1' x); [exact Hx | cbn; split; [lia | exact I]].
      + rewrite (MU1' x); [exact Hx | cbn; split; [lia | exact I]].
    - intros x Hx. exact (Hhid x Hx).
    - exact Hsbm.
    - intros a Ha. unfold Reusable.YCbq.awr_byte. right; right; right.
      unfold Reusable.YCbq.in_frames. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr, ESh.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia. }
  (* ---- the copy: __asan_memcpy (fr + 336, fragb fr, 72) through YCbq.aj_intrin_at with AMEMCPY ---- *)
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R) end.
  change (Reusable.YA0n.SRr segs W3 (mkCfg (lib.Reusable.YK11.mkst R1 (Z_to_bv 64 Reusable.YB1w.tfib_A_asan_memcpy)
            mem1 (lib.Reusable.YK11.seg_rom segs)) md') (POST cx)).
  assert (Esp1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_intrin_at segs B LAWS w4b_segs_low Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy
              AMEMCPY W3 R1 mem1 _ _ _ _ _ _ _ _ _ _ _ md' k (fr + 336) (ACtlCutP.fragb fr) 72
              (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82340) HJ1).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite Esp1. lia.
    - rewrite Zminus_mod, Hsp16, Hal16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK. rewrite HSTK. lia.
    - transitivity (lib.Reusable.YK11.getr regs3 3); [reflexivity|]. rewrite Hr3. exact Hgp.
    - transitivity (lib.Reusable.YK11.getr regs3 4); [reflexivity|]. exact Hr4.
    - reflexivity.
    - reflexivity.
    - intros a Ha. split.
      + unfold Reusable.YCbq.awr_byte. right; right; right.
        unfold Reusable.YCbq.in_frames. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + unfold Reusable.YG0d.ESTACK. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd.
      lia.
    - intros x Hx. exists 0. split; [|left; reflexivity].
      assert (E : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = ACtlCutP.Sfr fr + 42 + (x - (fr + 336)) / 8).
      { unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF. rewrite HK3v.
        replace x with (fr + 8 * 42 + (x - (fr + 336))) at 1 by lia.
        rewrite (w4b12_shidx (fr + 8 * 42) (x - (fr + 336))) by exact (w4b12_mod8 fr 42 Hfr8).
        rewrite (w4b12_div8 fr 42 Hfr8). lia. }
      rewrite E. pose proof (Z.div_pos (x - (fr + 336)) 8 ltac:(lia) ltac:(lia)) as Hq0.
      pose proof (Z.div_lt_upper_bound (x - (fr + 336)) 8 9 ltac:(lia) ltac:(lia)) as Hq1.
      rewrite w4b12_aview_vis by (apply V_sh; lia).
      unfold lib.Lib.Mem.wa in Z9. rewrite Z9 by lia. reflexivity.
    - intros _ s Hs. pose proof (w4b12_hull fr (fr + 336) 72 s Hfr8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hs'.
      rewrite w4b12_aview_vis by (apply V_sh; lia).
      pose proof (FSH1 s Hs') as Hn0. unfold lib.Lib.Mem.wa in Hn0.
      destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem1 (Z_to_bv 64 s)); [discriminate | exfalso; exact (Hn0 eq_refl)].
    - split; [unfold ACtlCutP.fragb; lia|]. split; [unfold ACtlCutP.fragb; lia|].
      split.
      { intros a Ha. split.
        - rewrite w4b12_aview_vis by (apply V_fr; unfold ACtlCutP.fragb in *; lia).
          destruct (w4b12_ba_some _ _ _ a BS1' ltac:(rewrite HFGL; lia)) as (b & Hb).
          unfold lib.Lib.Mem.wa in Hb. rewrite Hb. discriminate.
        - rewrite Esp1. unfold Reusable.YG0d.ESTACK, ACtlCutP.fragb in *. lia. }
      split; [unfold ACtlCutP.fragb; left; lia|].
      split; [unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
                Reusable.YG0f.kHighMemEnd, ACtlCutP.fragb; lia|].
      split.
      { apply (w4b12_ra W3 mem1 _ _ AS1'). intros i Hi. apply V_sh.
        unfold ACtlCutP.fragb, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
        replace (fr + 2768 + i) with (fr + 8 * 346 + i) by lia.
        rewrite (w4b12_shidx (fr + 8 * 346) i) by exact (w4b12_mod8 fr 346 Hfr8).
        rewrite (w4b12_div8 fr 346 Hfr8). rewrite HK3v.
        pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound i 8 9 ltac:(lia) ltac:(lia)).
        lia. }
      intros _ s Hs. unfold ACtlCutP.fragb in Hs.
      pose proof (w4b12_hull fr (fr + 2768) 72 s Hfr8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hs'.
      rewrite w4b12_aview_vis by (apply V_sh; lia).
      pose proof (FSH1 s Hs') as Hn0. unfold lib.Lib.Mem.wa in Hn0.
      destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem1 (Z_to_bv 64 s)); [discriminate | exfalso; exact (Hn0 eq_refl)]. }

  cbv beta. intros W' c' _ (EW & regs2 & mem2 & md2 & Ec & HJ2 & HPRS & H10' & Hcopy & Hfr2 & Hpres2).
  subst W' c'.
  (* registers across the run and the copy *)
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by exact (HPRS 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by exact (HPRS 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by exact (HPRS 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by exact (HPRS 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by exact (HPRS 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
    by exact (HPRS 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by exact (HPRS 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
    by exact (HPRS 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E21 : lib.Reusable.YK11.getr regs2 21 = Z_to_bv 64 (ACtlCutP.fragb fr))
    by exact (HPRS 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by exact (HPRS 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by exact (HPRS 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by exact (HPRS 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by exact (HPRS 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
    by exact (HPRS 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (Esp2 : Reusable.YG0d.spZ regs2 = sp) by (unfold Reusable.YG0d.spZ; rewrite E2; exact HspZ).
  (* the raw memory after the copy: ctl_post_memcpy *)
  assert (HPD : forall a, fr + 336 <= a < fr + 336 + 72 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem1 a).
  { intros a Ha. split; [apply V_fr; lia|].
    destruct (w4b12_ba_some _ _ _ a RW1b ltac:(rewrite Hjkl; lia)) as (b & Hb).
    rewrite w4b12_mrd_high in Hb by lia. exists b. exact Hb. }
  assert (HRPF : rt_post_frame W3 mem1 mem2 ((fr + 336, fr + 336 + 72) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil)).
  { split.
    - intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
      apply Hfr2; [exact Ha | exact Ho1 | lia].
    - exact Hpres2. }
  destruct (B.ProgWorld.ctl_post_memcpy W3 mem1 mem2 sp (fr + 336) (ACtlCutP.fragb fr) 72
              (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite HFGL; reflexivity) HPD BS1'
              (fun i Hi => V_fr (ACtlCutP.fragb fr + i) ltac:(unfold ACtlCutP.fragb; lia)) Hcopy HRPF)
    as (MV & WV & RW2).
  assert (HK12 : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
            ~ (fr + 336 <= x < fr + 408) -> ~ (sp - 4096 <= x < sp) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem1 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. apply MV; [exact Hv|]. rewrite lib.Lib.Mem.wa_unsigned by lia.
    cbn [lib.Lib.Frame.outside]. unfold Reusable.YG0d.ESTACK. split; [lia | split; [lia | exact I]]. }
  assert (HK : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
            ~ (ACtlCutP.Sfr fr + 42 <= x < ACtlCutP.Sfr fr + 51) -> ~ (fr + 336 <= x < fr + 408) ->
            ~ (sp - 4096 <= x < sp) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2 H3. rewrite HK12 by assumption. apply HK01; assumption. }
  assert (KST : forall x, sp <= x < ACtlCut.c_sp cx ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx. apply HK; [lia | apply V_st; lia | rewrite HK3v; lia | lia | lia]. }
  assert (KFR : forall x, fr <= x < fr + 4096 -> ~ (fr + 336 <= x < fr + 408) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hd. apply HK; [lia | apply V_fr; lia | rewrite HK3v; lia | exact Hd | lia]. }
  assert (KSH : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
            ~ (ACtlCutP.Sfr fr + 42 <= x < ACtlCutP.Sfr fr + 51) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hd. apply HK; [rewrite HK3v in *; lia | apply V_sh; lia | exact Hd | rewrite HK3v in *; lia
                              | rewrite HK3v in *; lia]. }
  assert (KHP : forall x, phi <= x < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx. apply HK; [lia | apply V_hp; lia | rewrite HK3v; lia | lia | lia]. }
  assert (KHS : forall x, phi <= x < phi + B.ACtlK.a_size (ACtlCutP.flen cx j) ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
            lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))).
  { intros x Hx. pose proof (w4b12_shadow_band x ltac:(lia)) as Hb.
    apply HK; [lia | apply V_hs; lia | | lia | lia].
    intros Hin. pose proof (w4b12_sh_back fr x Hfr8 ltac:(lia) ltac:(lia) Hin). lia. }
  assert (KIMG : forall x, 0x10000 <= x < 0x5fe000 ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx. apply HK; [lia | apply V_img0; lia | rewrite HK3v; lia | lia | lia]. }
  assert (EKN : B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME = 2147532464) by reflexivity.
  assert (KKN : forall i, 0 <= i < 14 ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME + i)) =
            lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME + i))).
  { intros i Hi. apply HK; [rewrite EKN; lia | apply V_kn; lia | rewrite EKN, HK3v; lia | rewrite EKN; lia
                           | rewrite EKN; lia]. }
  assert (HWm : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
            wview B.Img0.rsegs mem3 (lib.Lib.Mem.wa x) <> None -> wview B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) <> None)
    by (intros x Hx Hv Hw; exact (WV (lib.Lib.Mem.wa x) Hv (WM1' (lib.Lib.Mem.wa x) Hw))).
  assert (SKp : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v)
    by (intros off v Hoff Hs; exact (w4b12_spill_keep regs3 regs2 mem3 mem2 A off v Hr9 HA63 Hoff E9
                                       (fun x Hx => KST x ltac:(lia)) Hs)).
  assert (HADDR : forall a n, B.AsanRT.addressable mem3 a n -> fr <= a -> a + n <= fr + 4096 ->
            (forall i, 0 <= i < n -> ~ (fr + 336 <= a + i < fr + 408)) -> B.AsanRT.addressable mem2 a n).
  { intros a n HA Ha Han Hnd. apply (w4b12_addr_keep mem3 mem2 a n HA). intros i Hi.
    destruct (w4b12_fsh fr (a + i - fr) Hfr8 ltac:(lia) ltac:(lia)) as (Es & Hq & Hiff).
    replace (a + i) with (fr + (a + i - fr)) by lia. rewrite Es.
    apply KSH; [lia|]. intros Hin. apply (Hnd i Hi).
    assert (Hq' : 42 <= (a + i - fr) / 8 < 51) by lia. apply Hiff in Hq'. lia. }
  assert (HBK : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> fr <= a ->
            a + Z.of_nat (length bs) <= fr + 4096 ->
            (forall i, 0 <= i < Z.of_nat (length bs) -> ~ (fr + 336 <= a + i < fr + 408)) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
  { intros a bs H Ha Hl Hnd. apply (w4b12_ba_keep mem3 mem2 a bs H). intros i Hi.
    apply KFR; [lia | exact (Hnd i Hi)]. }
  (* ---- the exit cut C_B82340_at ---- *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82340_at [Z.of_nat j])) regs2 mem2 md2)
            (POST cx)).
  apply (H40 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HB).
  - exact HJ2.
  - exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82340_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    split.
    { apply (w4b12_frac_keep cx fr fr regs3 regs2 mem3 mem2 A HFRAC Hr9 HA63 E2 E3 E4 E8 E9 E19 E26).
      - intros x Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]];
          first [apply KST; lia | apply KFR; lia].
      - assert (HFS392 : Z.to_nat ACtlCutP.FRAME_SHADOW = 392%nat) by reflexivity. rewrite HFS392.
        destruct (w4b12_ex_list (fun i => lib.Lib.Mem.mrd B.Img0.rsegs mem2
                                          (lib.Lib.Mem.wa (ACtlCutP.Sfr fr + Z.of_nat i))) 392) as (l & Hl & Hf).
        { intros i Hi. rewrite HK12 by first [rewrite HK3v in *; lia | apply V_sh; lia]. apply FSH1. lia. }
        exists l. split; [|exact Hl]. split; [rewrite HK3v; lia|]. split; [rewrite Hl, HK3v; lia|].
        intros i Hi. rewrite Hl in Hi. apply Hf. exact Hi. }
    unfold ACtlCutP.fcutp_body. exists phi.
    pose proof HHB as (Hphinz & HAd).
    assert (HAd2 : B.AsanRT.addressable mem2 phi (B.ACtlK.a_size (ACtlCutP.flen cx j)))
      by (apply (w4b12_addr_keep mem3 mem2 _ _ HAd); intros i Hi; apply KHS; lia).
    split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|].
    split; [split; [exact Hphinz | exact HAd2]|].
    split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
    split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
    split.
    { pose proof HFT as (T224 & T232 & TPB & TPL).
      split; [apply SKp; [lia | exact T224]|]. split; [apply SKp; [lia | exact T232]|].
      split; [|exact TPL].
      apply (w4b12_ba_keep mem3 mem2 phi _ TPB). intros i Hi. apply KHP. unfold ACtlCutP.flen in *. lia. }
    assert (HD2 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 336) (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j))
      by exact (w4b12_cb_bytes _ _ _ _ RW2).
    split.
    { split.
      { (* LK *)
        split; [exact Hj|]. split; [apply SKp; [lia | exact P240]|].
        split.
        { unfold ACtlCutP.OURb in *. apply (HBK _ _ HOUR); rewrite ?B.Prog.SlotModel.OUR_length; intros; lia. }
        unfold ACtlCutP.FLI.
        split; [unfold ACtlCut.rgv in *; rewrite E27; exact H27|].
        do 21 (split; [apply SKp; [lia | assumption]|]).
        split; [apply (HADDR _ _ HadOur); intros; lia|].
        split.
        { apply (w4b12_stk_keep mem3 mem2 _ _ HstkF).
          - intros a Ha Hw. apply HWm; [lia | apply V_fr; lia | exact Hw].
          - intros a Ha. destruct (Z_lt_le_dec a (fr + 336)) as [L1|L1];
              [|destruct (Z_lt_le_dec a (fr + 408)) as [L2|L2]].
            + left. apply KFR; lia.
            + right. apply (w4b12_ba_some _ _ _ a HD2). rewrite HFGL. lia.
            + left. apply KFR; lia. }
        split.
        { split; [apply (HADDR _ _ HRid); intros; lia|].
          split; [apply (HADDR _ _ HRfg); unfold ACtlCutP.fragb; intros; lia|].
          apply (HADDR _ _ HRfst); intros; lia. }
        split.
        { destruct HKNT as (HKb & HKa). split.
          - apply (w4b12_ba_keep mem3 mem2 _ _ HKb). intros i Hi.
            assert (HKL : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by reflexivity. rewrite HKL in Hi.
            apply KIMG. unfold ACtlCutP.KNA.KIND_NAME. lia.
          - apply (w4b12_addr_keep mem3 mem2 _ _ HKa). intros i Hi.
            assert (EKNv : ACtlCutP.KNA.KIND_NAME = 652672) by reflexivity.
            assert (Es : B.AsanRT.shadow_addr (ACtlCutP.KNA.KIND_NAME + i) =
                         B.AsanRT.shadow_addr ACtlCutP.KNA.KIND_NAME + i / 8).
            { unfold B.AsanRT.shadow_addr. rewrite EKNv. rewrite (w4b12_shidx 652672 i) by reflexivity. lia. }
            rewrite Es. apply KKN.
            pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound i 8 14 ltac:(lia) ltac:(lia)).
            lia. }
        split; apply SKp; [lia | assumption | lia | assumption]. }
      split; [exact HD2|].
      split.
      { pose proof HFM as (M184 & M24 & M22 & M25 & M312).
        split; [apply SKp; [lia | exact M184]|].
        split; [unfold ACtlCut.rgv in *; rewrite E24; exact M24|].
        split; [unfold ACtlCut.rgv in *; rewrite E22; exact M22|].
        split; [unfold ACtlCut.rgv in *; rewrite E25; exact M25 | apply SKp; [lia | exact M312]]. }
      { unfold ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.u32, ACtlCutP.b8 in *.
        destruct HFS as (Hh & Hnn & Hbd & Had & HFI).
        pose proof (w4b12_body_length (ACtlCut.c_in cx) j) as Hbl.
        split; [apply (HBK _ _ Hh); rewrite ?lib.Lib.Mem.length_le4; intros; lia|].
        split; [apply (HBK _ _ Hnn); cbn [length]; intros; lia|].
        split; [apply (HBK _ _ Hbd); intros; lia|].
        split; [apply (HADDR _ _ Had); intros; lia | exact HFI]. } }
    split; [unfold ACtlCut.rgv; exact E21|].
    split.
    { intros H50. split; [destruct Hdj as [Hd|Hd]; [left|right]; lia|].
      split; [left; rewrite Esp2; unfold ACtlCutP.FGA.REAC_CTRL_IDENTITY_FRAGMENT_K; lia|].
      split.
      { apply (w4b12_ba_keep mem3 mem2 phi _ (HGb H50)). intros i Hi. apply KHP.
        rewrite w4b12_t_g_length in Hi. lia. }
      apply (B.AsanRTFacts.addressable_prefix mem2 phi (B.ACtlK.a_size (ACtlCutP.flen cx j)) 50 HAd2). lia. }
    split; [apply (HBK _ _ HFGb); unfold ACtlCutP.fragb; rewrite ?HFGL; intros; lia|].
    split; [apply (HADDR _ _ HRfg); unfold ACtlCutP.fragb; intros; lia|].
    split.
    { apply (w4b12_addr_keep mem1 mem2 _ _ AD1'). intros i Hi.
      destruct (w4b12_fsh fr (336 + i) Hfr8 ltac:(lia) ltac:(lia)) as (Es & Hq & _).
      replace (fr + 336 + i) with (fr + (336 + i)) by lia. rewrite Es.
      pose proof (Z.div_le_lower_bound (336 + i) 8 42 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (336 + i) 8 51 ltac:(lia) ltac:(lia)).
      apply HK12; [rewrite HK3v in *; lia | apply V_sh; lia | rewrite HK3v in *; lia | rewrite HK3v in *; lia]. }
    pose proof HRCA as (Hra & Hrp & Hrn).
    split; [apply (HADDR _ _ Hra); intros; lia|].
    split; [apply (HADDR _ _ Hrp); intros; lia|].
    split; [apply (HADDR _ _ Hrn); intros; lia|].
    split.
    { unfold ACtlCutP.IDBe, ACtlCutP.FGBe in *. split; split.
      - apply (HBK _ _ HIDb); rewrite ?w4b12_t_IDr_length; intros; lia.
      - exact HIDok.
      - apply (HBK _ _ HFGb); rewrite ?HFGL; intros; lia.
      - exact HFGok. }
    split.
    { exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr9|]. split; [lia|].
      assert (Hr9' : ACtlCut.rgv regs2 9 A) by (unfold ACtlCut.rgv in *; rewrite E9; exact Hr9).
      pose proof HFM as (_ & _ & _ & _ & M312).
      pose proof HFPS as (HpB & HaB).
      unfold ACtlCutP.pBb in HpB.
      assert (HBlen : length (B.Prog.SlotModel.t_B (ACtlCut.c_in cx) j) = 36%nat)
        by apply Prog.RcParse.ctrlparse_length.
      apply (w4b12_frb cx j fr phi A regs2 mem2 Hfr_app ltac:(lia) Hp4096 (proj1 Hfl) Hp_app Hdj).
      - rewrite Esp2. lia.
      - rewrite Esp2. lia.
      - rewrite Esp2. lia.
      - exact (w4b12_spill_q regs2 A mem2 272 _ Hr9' HA63 ltac:(lia) (SKp 272 _ ltac:(lia) H272)).
      - exact (w4b12_spill_q regs2 A mem2 312 _ Hr9' HA63 ltac:(lia) (SKp 312 _ ltac:(lia) M312)).
      - exact (w4b12_spill_q regs2 A mem2 248 _ Hr9' HA63 ltac:(lia) (SKp 248 _ ltac:(lia) HS9)).
      - exact (w4b12_spill_q regs2 A mem2 112 _ Hr9' HA63 ltac:(lia) (SKp 112 _ ltac:(lia) P112)).
      - exact (w4b12_spill_q regs2 A mem2 96 _ Hr9' HA63 ltac:(lia) (SKp 96 _ ltac:(lia) P96)).
      - intros H50. apply (w4b12_ba_keep mem3 mem2 phi _ (HGb H50)). intros i Hi. apply KHP.
        rewrite w4b12_t_g_length in Hi. lia.
      - apply (HBK _ _ HpB); rewrite ?HBlen; intros; lia.
      - apply (HADDR _ _ HaB); intros; lia.
      - exact HAd2. }
    apply SKp; [lia | exact HS9].
  - (* route (C): ctl_rt_C at the exit from the post journal's AR (a Theorem Labs lane's ctl_rt_C_of_AR) *)
    exact (w4b_ctlrt_C cx _ _ _ _ _ _ _ HB HJ2).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   B82304_at j (0x82304) --S_F12--> B82340_at j.
   S_F12 (Seg/F12.v seg_F12 :1907): `bltz a0,0x82fa4`, nine shadow stores S(fr) + 42 .. 50 (the 72 bytes
   [fr + 336, fr + 408) usable), __asan_memcpy([A + 200] = fr + 336, [A + 208] = fragb fr, 72) @0x8233c, s5 := fragb fr,
   returning at 0x82340. *)
Lemma seg_F12 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82340_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82304_at [Z.of_nat j]).
Proof.
  (* Plan (kept): F12F.f12_pre_F from 0x82304 (the bltz not taken: a0 = r, 0 <= r < 2^63), then the copy and the
     exit, all in w4b12_at (helpers above). *)
  intros POST j H40 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82304_at ACtlCutP.fcutp_body ACtlCutP.ixn ACtlCutP.ixz nth]
    in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & H18 & H20 & HFT & HLK & HFM & HFS & HREC & HGb & HFPS & H272 &
    HRCA & (r & H10 & Hr) & HS9).
  exact (w4b12_at POST j cx fr k ly3 S3 W3 regs3 mem3 md3 phi 0x82304 r H40 HB HJ HF HL Hk HFRAC HP Hn Hj HHB H18
           H20 HFT HLK HFM HFS HREC HGb HFPS H272 HRCA HS9 Hrt (or_intror (conj eq_refl (conj H10 Hr)))).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82308_at j (0x82308) --S_F12_298--> B82340_at j.
   S_F12_298 (Seg/F12.v seg_F12_298 :1919): the same run as S_F12 from 0x82308 (no `bltz` on this entry). *)
Lemma seg_F12_298 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82340_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82308_at [Z.of_nat j]).
Proof.
  (* Plan (kept): the same run from 0x82308 (no sink on this entry); FM and FS9 are f10_K's spills [A + 312] /
     [A + 248] and registers; the exit's record bundle is RECR (the body's own). *)
  intros POST j H40 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82308_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & HK & HFS & HGb & Hir & HFT & HREC & HFPS & H272 & HRCA).
  pose proof HK as (Hn & Hj & HHB & HLK & (A & HFL & HA & Hq288 & Hq176 & Hq200 & Hq208 & Hq248 & Hq312) &
    H18 & H20 & Hs9 & Hs8 & Hs184 & Hs6 & Hargs).
  pose proof HFL as (H9 & _).
  assert (HFM : ACtlCutP.FM cx j phi fr regs3 mem3).
  { split; [exact Hs184|]. split; [exact Hs8|]. split; [exact Hs6|]. split; [exact Hs9|].
    exists A. split; [exact H9 | exact Hq312]. }
  assert (HS9 : ACtlCutP.FS9 cx j regs3 mem3) by (exists A; split; [exact H9 | exact Hq248]).
  exact (w4b12_at POST j cx fr k ly3 S3 W3 regs3 mem3 md3 phi 0x82308 0 H40 HB HJ HF HL Hk HFRAC HP Hn Hj HHB H18
           H20 HFT HLK HFM HFS HREC HGb HFPS H272 HRCA HS9 Hrt (or_introl eq_refl)).
Qed.

End W4b.

(* Stage lemmas of this file, all proved (Qed); [j] abbreviates [Z.of_nat j]:
     seg_F7  (B8215c_at) : forall POST j, ctl_from POST (ix_cut C_B82174_at [j]) -> ctl_from POST (ix_cut C_B8215c_at [j])
     seg_F8  (B82174_at) : forall POST j, ctl_from POST (ix_cut C_B82180_at [j]) -> ctl_from POST (ix_cut C_B82174_at [j])
     seg_F9  (B82180_at) : forall POST j, ctl_from POST (ix_cut C_B821ec_at [j]) -> ctl_from POST (ix_cut C_B82180_at [j])
     seg_F10 (B821ec_at) : forall POST j, ctl_from POST (ix_cut C_B8226c_at [j]) ->
                           ctl_from POST (ix_cut C_B82308_at [j]) -> ctl_from POST (ix_cut C_B821ec_at [j])
     seg_F11 (B8226c_at) : forall POST j, ctl_from POST (ix_cut C_B82304_at [j]) -> ctl_from POST (ix_cut C_B8226c_at [j])
     seg_F12 (B82304_at) : forall POST j, ctl_from POST (ix_cut C_B82340_at [j]) -> ctl_from POST (ix_cut C_B82304_at [j])
     seg_F12_298 (B82308_at) : forall POST j, ctl_from POST (ix_cut C_B82340_at [j]) ->
                           ctl_from POST (ix_cut C_B82308_at [j])
   Each seg_* is named and stated exactly as ACtl.v's Hypothesis of the same name, generic in SK and FP.
   Sink / trap obligations (branch -> target: the stage whose run steps it not taken):
     0x8215c, 0x82168 -> 0x82fa4 : seg_F7      0x82174 -> 0x82fa4 : seg_F8
     0x821b4 -> 0x82fa4 : seg_F9 (not reached: the first name byte is not '?')
     0x821ec, 0x821f4, 0x82200, 0x82208, 0x8221c, 0x8223c, 0x82268 -> 0x82fa4 : seg_F10
     0x82224 (T20), 0x82230 (T21), 0x8224c (T22) -> 0x82fa0 : seg_F10
     0x82274 (T23), 0x82294 (T24), 0x822a0 (T25) -> 0x82fa0 : seg_F11
     0x82288, 0x822e8 -> 0x82fa4 : seg_F11     0x82304 -> 0x82fa4 : seg_F12
   0x821f4 (reply_ok -> t_sum_ok) is discharged in seg_F10 from the reply model (RcReply.ir_bytes: the record's
   block sum is 0, so SlotModel.t_sum_ok holds). *)

(* The gate's named Print Assumptions, one per closed stage (a Theorem Labs lane 04:22Z). *)
Check seg_F7.
Print Assumptions seg_F7.
Check seg_F8.
Print Assumptions seg_F8.
Check seg_F9.
Print Assumptions seg_F9.
Check seg_F10.
Print Assumptions seg_F10.
Check seg_F11.
Print Assumptions seg_F11.
Check seg_F12.
Print Assumptions seg_F12.
Check seg_F12_298.
Print Assumptions seg_F12_298.
