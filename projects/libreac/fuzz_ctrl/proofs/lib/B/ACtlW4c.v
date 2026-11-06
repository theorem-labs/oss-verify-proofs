(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e2.v, with its module paths and module names changed; 4090 of its 4391 lines of code are new or changed and 2544 lines of the source are left out. *)
(* lib/B/ACtlW4c.v -- piece W4c (frame turn, part 3: S_F13 .. S_F17, with S_F15b) of fuzz_ctrl image B's (asan-ubsan)
   walk of LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane.
   rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one stage lemma per cut of W4c (cut-table rows 54-59; all own6,
   k <= 14+2j+1, live list entry ++ [(phi, flen cx j)]), POINTWISE in the frame-loop index j (ACtlCut.ix_cut, a Theorem Labs lane
   22:47Z).  No allocator site, no fake-stack call.
     B82340_at j --S_F13-->  B8235c_at j    reac_ctrl_identity_fragment @0x82358 (whole lift)
     B8235c_at j --S_F14-->  B8237c_at j    (sum_ok: `bnez s9,0x8237c`)
                          | B82378_at j    (not sum_ok: the bcmp trampoline @0x82374 on the two 72-byte records)
     B82378_at j --S_F15-->  B8237c_at j    (inline)
     B8237c_at j --S_F15b--> B823d8_at j    (fg_ret = 1: FgClose, the bound checks)
                          | B82468_at j    (fg_ret <> 1: `bne s7,s6,0x82468`)
     B823d8_at j --S_F16-->  B82464_at j    record_sum_closes @0x823dc, joined_byte @0x82414 / @0x82438,
                                           reac_identity_ingest @0x82460 (whole lifts)
     B82464_at j --S_F17-->  B82468_at j    (inline: `bltz a0,0x82fa4` not taken)
   B8237c_at is a re-anchored cut (v1.8 Inv_B82310_at; plan 6.1).

   ROUTE (C) (a Theorem Labs lane 09:20Z; a working branch shell a Theorem Labs lane 94da0a5cc85; brief w4C-brief.md (a working note, not in this delivery)): every cut carries
   B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (asan_cells, shadow_rw_on the cut's own shadow and the image's, ro_agree) instead
   of the full ctl_rt; the VIS0 / OWNED_RO Section hypotheses are gone from this file.  The inline stages
   (S_F15, S_F15b, S_F17, S_F14's sum_ok arm) pass the cut's ctl_rt_C on unchanged; S_F13 / S_F14 give it at their
   exits by B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w4c_ctlrt), S_F16 carries it across its callee windows
   (w4c16_ctl_rt_munch / w4c16_rt_mv).  A callee's shadow premise is its `_on` region, shown inside the cut's own
   shadow (w4c13_frag_R_in): reac_identity_ingest (a Theorem Labs lane ebcd94ed838), record_sum_closes (a Theorem Labs lane
   3ea30e6571b), joined_byte (a Theorem Labs lane b31890d9f11) and reac_ctrl_identity_fragment (a Theorem Labs lane 66bf4fc003b,
   closed corollary reac_ctrl_identity_fragment_holds_F_closed_on) are landed and cited by name.

   ROUTE, BUILD STATE, SHELL GAPS (G1) / (G2), the shared Section hypotheses tfibsegs_rsegs / Hwx / RTP / rt_of_core
   and the PENDING KIT / BRIDGE FACTS: exactly as lib/B/ACtlW0.v's header.  FEVT, img_vis_W and ctl_post_bcmp are
   CITATIONS (RTPOST-SHARED-B.txt 15:40Z swap): B.ProgBridge.fevt_of_evtF (ProgBridge.v:30), B.ProgBridge.img_vis_W
   (:121), B.ProgWorld.ctl_post_bcmp (ProgWorld.v:660).

   SECTION HYPOTHESES OF THIS FILE (sources):
   - H_bcmp (with Variable B_bcmp_tramp_entry): `__interceptor_trampoline_bcmp` @0x82374 (callee 0x42aac), owned by
     a Theorem Labs lane (porter a Theorem Labs lane 23:17Z): "shared SRr-form contract = trampoline composed onto cgif's interceptor
     body contract (bcmp via YG0d's abcmp rule)"; names come with a Theorem Labs lane's stated sha; the ENTRY is
     `Variable B_bcmp_tramp_entry : Z` (intended = the core's `bcmp_tramp` in lib/Reusable/YTramp.v (not in this delivery), 0x42aac), never the
     literal.  Taken here in that shape: Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry (donor YG0d.v:352-371),
     through Reusable.YCbq.aj_bcmp_at (YCbq.v:2062).  TEXT PENDING (a Theorem Labs lane's sha).
   - ctl_post_bcmp : CITED, B.ProgWorld.ctl_post_bcmp : ctl_post_bcmp_stmt = ctl_post_window_stmt (2 * ESTACK)
     (lib/B/ProgWorld.v:653, :660; PROVED): H_bcmp's world-form post as visible-address facts.  a0 is the core post's
     own register fact, nothing to convert.  Used at 0x82374 (seg_F14 step 2).
   - img_vis_W : CITED, B.ProgBridge.img_vis_W (lib/B/ProgBridge.v:121; PROVED): the image range [IMG_LO, IMG_HI) =
     [0x10000, 0x5fe000) is visible in every world.  Used for the image premises of identity_fragment and
     identity_ingest, and in seg_F14's frame-byte carriage.
   PENDING CALLEE CONTRACTS (texts not yet published):
   - reac_ctrl_identity_fragment_SRr_at (a Theorem Labs lane ProgLift; B by a Theorem Labs lane), site 0x82358: a0 = s5 = fragb fr,
     a1 = phi, a2 = len, a3 = [A + 288] = pa = fr + 256, a4 = [A + 304] = pp = fr + 272, a5 = [A + 296] = pn = fr + 304;
     caller obligations = reac_ctrl_identity_fragment_contract_F premises (reac_ctrl_identity_fragment_c.v (at head lib/B/Prog/reac_ctrl_identity_fragment_c.v:95); its
     bcmp_wrap / memcpy `_F` premises are a Theorem Labs lane's; rng_bytes RNG premise, a working branch 083d3ab15d4);
     post: a0 = fg_ret of the fragment class (0 or 1 here), the record / cells per fg_mem; write set
     fg_fp K f pa pp pn sp c (the cells plus the callee window).
   - record_sum_closes, site 0x823dc: ACCEPTED and final (a Theorem Labs lane, 00:18Z via another Theorem Labs lane): `record_sum_closes_holds_F :
     record_sum_closes_contract_F` (lib/B/Prog/record_sum_closesF.v; the statement in lib/B/Prog/record_sum_closes_c.v:47-77)
     on a working branch eae8a0725f2 (799ea3ce98f superseded).  No Section hypothesis, no rng_bytes; Print
     Assumptions shows kernel primitives only.  CITED BY REQUIRING ITS MODULES, qualified, NOT as a Section hypothesis.
     It is a footprint run on ExecF.evtF from the entry RECORD_SUM_CLOSES = 0x83614 to ret_pc ra, composed like an
     `_F` (B.ProgBridge.fevt_of_evtF + SRr_fevt).  a0 = [A + 120] = fragb fr + 15, a1 = pll + 5 (6 <= a1 <= 56:
     FgClose's 14 <= fg_T <= 64);
     premise map in seg_F16 step 1; post: a0 = 1 (recsum bs = 0), munch [(sp - 16, sp)] m m', wmono, mem_inv and stk
     kept, ra / sp / gp / tp / t1 / t2 / s0-s11 / t3-t6 kept.
   - joined_byte, sites 0x82414 (i = 9) and 0x82438 (i = 10): ACCEPTED and final (a Theorem Labs lane, 00:22Z via another Theorem Labs lane):
     `joined_byte_holds_F : joined_byte_contract_F` (lib/B/Prog/joined_byteF.v; statement lib/B/Prog/joined_byte_c.v:70-104;
     corollary joined_byte_contract_of_F) on a working branch da405a385b2.  No callees, no Section
     hypothesis, no rng_bytes.  Both files are taken BY PATH from da405a385b2 into this branch (our joined_byte_c.v was
     a Theorem Labs lane's 3803efccea0 blob 19339d3c0b7, without the footprint section) and CITED BY REQUIRING THEIR MODULES, qualified.
     Entry JOINED_BYTE = 0x836ac, frame JOINED_BYTE_FRAME = 16; a0 = fr + 2880 (`first`, FSj), a1 = phi + 18 = blk (FM's
     [A + 312], long frame), a2 = i.  Its five UBSan checks T1-T5 (trap `unimp` 0x8373c) are INSIDE the callee and are
     discharged by the contract's premises S1.2-S1.6; premise map in seg_F16 step 2.
     OPEN-1 (plan F.4.4, value only): FI constrains fs_n / fs_body only when bat st 6 = 1; if the reassembly state does
     not hold a FIRST, nb (the byte at fr + 2884) is unconstrained against length (fs_body s), so on the i < nb arm the
     byte at fr + 2885 + i (S1.5's bytes_at) is supplied as the byte the memory holds there (readable: FSb's
     `addressable (fr + 2880) 40` and app_mem), not from FSj's body list.  No trap verdict changes.
     Post: a0 = zxb b, b the byte at jb_addr (fr + 2880) (phi + 18) nb i; munch [(sp - 16, sp)] m m'; wmono; mem_inv and
     stk kept; ra / sp / gp / tp / t0-t2 / a7 / s0-s11 / t3-t6 kept.
   - reac_identity_ingest_SRr_at, site 0x82460: a0 = [A + 176] = fr + 2688, a1 = the u16 at fr + 256 (fg_addr),
     a2 = [fr + 272] = fragb fr + 19, a3 = [fr + 304] = pll (FLV); post a0 >= 0, the 38 bytes at fr + 2688 = t_IDr j;
     write set [sp - 32, sp) and [fr + 2688, fr + 2726).
   `_F` HYPOTHESES (a Theorem Labs lane; module ..lib.B.Prog.Seg.<File>F; RNG-first; split at EVERY call).  PUBLISHED texts
   are cited by Requiring their module, qualified (a Theorem Labs lane 23:38Z / 23:4xZ); statuses as of
   bF-statements/ (a working note, not in this delivery) at 23:40Z (others: expected names, NOT YET PUBLISHED):
   - F13F.f13_pre_F (a Theorem Labs lane; F13.v f13_evt_n :1109 / f13_evt :1178, 0x82340 -> the fragment's entry 0x859e4,
          ra = 0x8235c; the callee's return pc 0x8235c IS the exit cut, so there is no `_post_F`)   PUBLISHED, proved
   - F14F.f14_evt_10_F (the sum_ok arm 0x8235c -> 0x8237c) and F14F.f14_evt_0c_pre_F (0x8235c -> the bcmp trampoline
          BCMP_WRAP 0x42aac, ra = 0x82378 = the exit cut, so no `_post_F`) (a working branch
          adb0b6e4f3e)                                                                         PUBLISHED
   - F15F.seg_F15_F (F15.v (not in this delivery) seg_F15, inline 0x82378 -> 0x8237c) and F15F.seg_F15b_F (seg_F15b, not in this delivery either,
          inline 0x8237c -> 0x823d8 / 0x82468)                                                PUBLISHED, in progress
   - F16F.seg_F16_pre_F / seg_F16_pre2_F / seg_F16_pre3_F / seg_F16_pre4_F (F16.v seg_F16 :1138; calls record_sum_closes
          0x823dc, joined_byte 0x82414 / 0x82438, reac_identity_ingest 0x82460; stretch k+1 starts at the return of call
          k, and call 4 returns at the exit cut 0x82464, so no `_post_F`) (a Theorem Labs lane, adb0b6e4f3e)   PUBLISHED
   - F17F.seg_F17_F (a Theorem Labs lane, a working branch 007c7fd6c63; F17.v (not in this delivery) seg_F17, inline 0x82464 -> 0x82468; no rng
          premise, one not-taken bltz; + seg_F17_run)                                          PUBLISHED, proved
   PROVENANCE: cut table rows 54-59; plan 2.3 rows 54-59, 6.2 rows S_F15b / S_F16, F.4.1 rows 25-26, F.4.2, F.4.4;
   runs at 3803efccea0 (F13-F17); objdump L85020-L85094.

   ABORT-SINK / TRAP OBLIGATIONS ON W4c (all branches into 0x82fa4 / 0x82fa0 in 0x82340-0x82468): 0x8235c, 0x82378,
   0x8238c, 0x8239c, 0x823b4, 0x823c8, 0x823e0, 0x823ec, 0x82440, 0x82464 (-> 0x82fa4) and 0x823c0 / 0x823d0 (T26 /
   T27, -> 0x82fa0).  joined_byte's own T1-T5 (-> 0x8373c) are the callee's (above). *)

From Coq Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn Reusable.YImgTop.
(* lib/Lib's raw-memory vocabulary of the call-post fact below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's published `_F` modules (Required qualified, never Imported, a Theorem Labs lane 23:38Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F13F F14F F15F F16F F17F.
(* The route (C) footprint contracts and proofs of the two plain callees of S_F16, Required qualified:
   record_sum_closes (a Theorem Labs lane 3ea30e6571b, build of record f9973b8f603: the accepted contract_F of eae8a0725f2 with
   the shadow premise dropped) and joined_byte (a Theorem Labs lane b31890d9f11: the shadow premise dropped, the post's last
   conjunct `forall P, shadow_rw_on P m -> shadow_rw_on P m'`). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c record_sum_closes_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closesF_on joined_byte_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require joined_byte_c_on joined_byteF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes PropExec.
(* The glue's kit and bridge (Required qualified, never Imported): the world-walk lift (YA0nR, above), the register-map
   move (Regs6ss), lib/Lib's state form, the image-B bridge (ProgBridge: cfg_at_MS, RNG_W, rng_of_visible), the core's
   state vocabulary and mem_grows (YK1b). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge B.AsanRT.
(* The pure models the S_F15 / S_F15b arithmetic reads (Required only, qualified): the fragment model and its lemmas,
   the record sum, the image-B slot model, memcmp's model, the runtime's addressable_sub; lib/Lib's cells. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcFragLib Prog.RcRec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel B.Spec.StrFun B.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Step Cells.
(* seg_F13: the fragment contract, the MemNorm route of its lift, the shadow-word cover, the image bounds,
   the runtime-cell names of its T11 premise (Required only, qualified). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_fragment_c rng_asan ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c memcmp_c.
(* route (C): the fragment's R through its callees' leaves (a Theorem Labs lane 0cf5e518128), Required qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memcpy_c_on bcmp_wrap_c_on sh_word_on.
(* route (C): the fragment's closed route (C) corollary (a working branch 66bf4fc003b),
   Required qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_fragment_F_closed.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormF.
(* seg_F16: reac_identity_ingest's footprint contract and its closed proof (cited by name), the identity
   model's ING_ret / ING_id_ok, image B's segment lookup (kb_find_segment) and the turn's frame bytes
   (SlotInv.t_g_of_phi, as lib/B/ACtlW4a.v cites it); all Required qualified, never Imported. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_ingest_c reac_identity_ingestF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcIdentModel Prog.RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.KindBGlue B.Prog.SlotInv.
(* ---- extra Requires for seg_F14: lia, the core's ret_ok, the shadow vocabulary ---- *)
From Coq Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.bcmp_wrap_c.
(* Route (C) (a Theorem Labs lane 09:20Z): every cut carries B.ACtlRtC.ctl_rt_C; the exits give it by a Theorem Labs lane's proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR, fed with the journal's kept read-only view (Reusable.APostBase.arodata_ok_journalP,
   B.ProgWorld.arodata_okP_of_S); B.ShadowRwOn / B.ShadowRwOnT carry the narrowed shadow (Required qualified, never
   Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE01 Reusable.APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC ShadowRwOn ShadowRwOnT.
Import ListNotations.
Local Open Scope Z_scope.

Section W4c.

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
Local Notation C_B82340_at := (ACtlCutP.C_B82340_at B).
Local Notation C_B8235c_at := (ACtlCutP.C_B8235c_at B).
Local Notation C_B82378_at := (ACtlCutP.C_B82378_at B).
Local Notation C_B8237c_at := (ACtlCutP.C_B8237c_at B).
Local Notation C_B823d8_at := (ACtlCutP.C_B823d8_at B).
Local Notation C_B82464_at := (ACtlCutP.C_B82464_at B).
Local Notation C_B82468_at := (ACtlCutP.C_B82468_at B).

(* ---- Section hypotheses (sources in the header and in ACtlW0.v's) ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* rt_of_core, placeholder form (a Theorem Labs lane 22:44Z; no APIf, a Theorem Labs lane 23:05Z).  TODO: B's bridge statement verbatim. *)
Variable RTP : (word -> option byte) -> Prop.
Hypothesis rt_of_core : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> RTP mem.

(* __interceptor_trampoline_bcmp @0x82374: a Theorem Labs lane's trampoline contract in the porter's shape (23:17Z).
   TEXT PENDING (a Theorem Labs lane's sha). *)
Variable B_bcmp_tramp_entry : Z.
Hypothesis H_bcmp : Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry.

(* LAWS / segs_low: the core's AR laws for B and the image's place below kLowMemEnd (the sibling W4e1's text, token for
   token, as lib/B/ACtlW4a.v carries it; obligation: the core's api_of_core (aa_laws) and B's segment table; owner: the
   core (a Theorem Labs lane)).  The journal step of every stage (YCbq.ajournal_exec) reads them. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* =========================================================================================================
   STAGE KIT (local to this file; none touches the allocator).  The pure fragment-model facts are copies of
   lib/B/Prog/Seg/F15.v's (read for the arithmetic, never cited); the visibility / register-move lemmas are the
   image-B twins of lib/B/ACtlW4b.v's w4b_win_vis / w4b_frame_vis / w4b_fr_ly3 / w4b_frac_move.
   ========================================================================================================= *)
Lemma w4c_memcmp_self_eq : forall (l : list byte) (n : nat) (v : Z),
  B.Spec.StrFun.memcmp_model l l n = Some v -> v = 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|b l] v H; cbn in H; try discriminate.
  - injection H as <-. reflexivity.
  - injection H as <-. reflexivity.
  - rewrite Z.eqb_refl in H. exact (IH l v H).
Qed.

Lemma w4c_sum_ok_false_fr : forall inp j, B.Prog.SlotModel.t_sum_ok inp j = false ->
  Prog.RcFrag.fg_fr (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j) = false.
Proof.
  intros inp j H. unfold B.Prog.SlotModel.t_sum_ok, B.Prog.SlotModel.t_big in H. rewrite Bool.andb_false_iff in H.
  unfold Prog.RcFrag.fg_fr. destruct H as [H|H]; rewrite H; [reflexivity | apply Bool.andb_false_r].
Qed.

Lemma w4c_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !lib.Lib.MState.unsigned_lit in E by lia. exact E.
Qed.

Lemma w4c_fg_ret_range : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  0 <= Prog.RcFrag.fg_ret (Prog.RcFrag.fg_class f fr pa pp pn len st g) <= 1.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. rewrite Prog.RcFragLib.rf_class_nn by assumption.
  destruct (Prog.RcFrag.fg_fr len g); cbn [negb].
  - destruct (Prog.RcFrag.bat g 19 =? 1); cbn [Prog.RcFrag.fg_ret].
    + lia.
    + destruct (Prog.RcFrag.fg_keep st g); cbn [negb].
      * destruct (Prog.RcFrag.fg_close st g); cbn [negb Prog.RcFrag.fg_ret]; lia.
      * cbn [Prog.RcFrag.fg_ret]; lia.
  - cbn [Prog.RcFrag.fg_ret]; lia.
Qed.

Lemma w4c_ret1_close : forall c, Prog.RcFrag.fg_ret c = 1 -> c = Prog.RcFrag.FgClose.
Proof. intros c H. destruct c; cbn [Prog.RcFrag.fg_ret] in H; try discriminate; reflexivity. Qed.

Lemma w4c_frcl_fcls : forall cx j fr phi, ACtlCutP.fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  ACtlCutP.frcl cx j fr phi =
  B.Prog.SlotModel.fcls (ACtlCutP.flen cx j) (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
    (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j).
Proof.
  intros cx j fr phi H1 H2 H3 H4 H5. unfold ACtlCutP.frcl, B.Prog.SlotModel.fcls.
  rewrite (Prog.RcFragLib.rf_class_nn (ACtlCutP.fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite (Prog.RcFragLib.rf_class_nn 1 1 1 1 1) by lia. reflexivity.
Qed.

Lemma w4c_trf_of_frcl : forall cx j fr phi, ACtlCutP.fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  B.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi).
Proof.
  intros cx j fr phi H1 H2 H3 H4 H5. unfold B.Prog.SlotModel.t_rf, B.Prog.SlotModel.fg_rf.
  rewrite (w4c_frcl_fcls cx j fr phi) by assumption. unfold ACtlCutP.flen. reflexivity.
Qed.

Lemma w4c_keep_T : forall st g, Prog.RcFrag.fg_keep st g = true -> Prog.RcFrag.fg_T st g <= 64.
Proof.
  intros st g H. unfold Prog.RcFrag.fg_keep in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma w4c_fr_fg_n : forall len g, Prog.RcFrag.fg_fr len g = true -> 1 <= Prog.RcFrag.fg_n g <= 22.
Proof.
  intros len g H. unfold Prog.RcFrag.fg_fr in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma w4c_rf_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= Prog.RcFrag.fg_n g <= 22 ->
  length (Prog.RcFrag.fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold Prog.RcFrag.fg_first, Prog.RcFrag.fg_body.
  rewrite !length_app, length_skipn, (Prog.RcFragLib.rf_bsl_length g 6 6),
    (Prog.RcFragLib.rf_bsl_length g 27 (Prog.RcFrag.fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma w4c_fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (B.Prog.SlotModel.fg_next st g (Prog.RcFrag.fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold Prog.RcFrag.fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0))%bool;
    [cbn [B.Prog.SlotModel.fg_next]; exact HL|].
  destruct (Prog.RcFrag.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [B.Prog.SlotModel.fg_next]; exact HL].
  destruct (Prog.RcFrag.bat g 19 =? 1).
  - cbn [B.Prog.SlotModel.fg_next]. apply w4c_rf_first_length; [exact HL | exact HG | apply (w4c_fr_fg_n len); exact FR].
  - destruct (Prog.RcFrag.fg_keep st g) eqn:Hkeep0; cbn [negb];
      [|cbn [B.Prog.SlotModel.fg_next]; apply Prog.RcFragLib.rf_clear_length; exact HL].
    destruct (Prog.RcFrag.fg_close st g); cbn [negb B.Prog.SlotModel.fg_next];
      apply Prog.RcFragLib.rf_clear_length, Prog.RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | apply (w4c_fr_fg_n len); exact FR | apply w4c_keep_T; exact Hkeep0].
Qed.

Lemma w4c_t_g_length : forall inp j, length (B.Prog.SlotModel.t_g inp j) = 50%nat.
Proof. intros inp j. unfold B.Prog.SlotModel.t_g. apply B.Prog.SlotModel.fr50_length. Qed.

Lemma w4c_t_FG_length : forall inp j, length (B.Prog.SlotModel.t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold B.Prog.SlotModel.t_FG in *. rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn.
    destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j));
      cbn [B.Prog.SlotModel.fs_fg]; unfold B.Prog.SlotModel.fg_st, B.Prog.SlotModel.fcls;
      apply (w4c_fg_next_length 1 1 1 1 1); solve [exact IH | apply w4c_t_g_length].
Qed.

Lemma w4c_t_FGf_length : forall inp j, length (B.Prog.SlotModel.t_FGf inp j) = 72%nat.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_FGf, B.Prog.SlotModel.fg_st, B.Prog.SlotModel.fcls.
  apply (w4c_fg_next_length 1 1 1 1 1); [apply w4c_t_FG_length | apply w4c_t_g_length].
Qed.

Lemma w4c_close_T : forall f fr pa pp pn len st g, Prog.RcFrag.fg_class f fr pa pp pn len st g = Prog.RcFrag.FgClose ->
  14 <= Prog.RcFrag.fg_T st g <= 64.
Proof.
  intros f fr pa pp pn len st g H. unfold Prog.RcFrag.fg_class in H.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0))%bool; [discriminate|].
  destruct (negb (Prog.RcFrag.fg_fr len g)); [discriminate|].
  destruct (Prog.RcFrag.bat g 19 =? 1); [discriminate|].
  destruct (Prog.RcFrag.fg_keep st g) eqn:Hkeep0; cbn [negb] in H; [|discriminate].
  destruct (Prog.RcFrag.fg_close st g) eqn:CLOSE; cbn [negb] in H; [|discriminate].
  split; [|apply w4c_keep_T; exact Hkeep0].
  unfold Prog.RcFrag.fg_close in CLOSE. rewrite !Bool.andb_true_iff in CLOSE.
  destruct CLOSE as (CL & _). repeat (destruct CL as (CL & _)). apply Z.leb_le in CL. lia.
Qed.

Lemma w4c_trf1_cls : forall inp j, B.Prog.SlotModel.t_rf inp j = 1 ->
  B.Prog.SlotModel.fcls (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j)
  = Prog.RcFrag.FgClose.
Proof. intros inp j H. unfold B.Prog.SlotModel.t_rf, B.Prog.SlotModel.fg_rf in H. apply w4c_ret1_close. exact H. Qed.

Lemma w4c_cls_close_inv : forall len st g,
  B.Prog.SlotModel.fcls len st g = Prog.RcFrag.FgClose ->
  Prog.RcFrag.fg_fr len g = true /\ Prog.RcFrag.fg_keep st g = true /\ Prog.RcFrag.fg_close st g = true /\
  Prog.RcFrag.bat g 19 <> 1.
Proof.
  intros len st g H. unfold B.Prog.SlotModel.fcls, Prog.RcFrag.fg_class in H.
  destruct (negb (Prog.RcFrag.fg_fr len g)) eqn:Efr; [cbn in H; discriminate|].
  destruct (Prog.RcFrag.bat g 19 =? 1) eqn:E19; [cbn in H; discriminate|].
  destruct (negb (Prog.RcFrag.fg_keep st g)) eqn:Ek; [cbn in H; discriminate|].
  destruct (negb (Prog.RcFrag.fg_close st g)) eqn:Ec; [cbn in H; discriminate|].
  apply Bool.negb_false_iff in Efr, Ek, Ec. apply Z.eqb_neq in E19. repeat split; assumption.
Qed.

Lemma w4c_fr_len50 : forall len g, Prog.RcFrag.fg_fr len g = true -> 50 <= len.
Proof.
  intros len g H. unfold Prog.RcFrag.fg_fr in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (((((((((((H & _) & _) & _) & _) & _) & _) & _) & _) & _) & _) & _).
  apply Z.leb_le. exact H.
Qed.

Lemma w4c_tFGf_close : forall inp j, B.Prog.SlotModel.t_rf inp j = 1 ->
  B.Prog.SlotModel.t_FGf inp j =
  Prog.RcFrag.fg_clear (Prog.RcFrag.fg_join (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j)).
Proof.
  intros inp j H. unfold B.Prog.SlotModel.t_FGf, B.Prog.SlotModel.fg_st. rewrite (w4c_trf1_cls inp j H). reflexivity.
Qed.

Lemma w4c_keep_hf : forall st g, Prog.RcFrag.fg_keep st g = true -> Prog.RcFrag.fg_hf st <> 0.
Proof.
  intros st g H. unfold Prog.RcFrag.fg_keep in H. rewrite !Bool.andb_true_iff in H. destruct H as ((H & _) & _).
  apply Bool.negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma w4c_nthfn : forall (i n : nat) (l : list byte), (i < n)%nat ->
  nth i (firstn n l) (Z_to_bv 8 0) = nth i l (Z_to_bv 8 0).
Proof.
  intros i n l. revert i l. induction n as [|n IH]; intros i l Hi; [lia|].
  destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma w4c_nth_sk : forall (m i : nat) (l : list byte), nth i (skipn m l) (Z_to_bv 8 0) = nth (m + i) l (Z_to_bv 8 0).
Proof.
  induction m as [|m IH]; intros i l.
  - reflexivity.
  - destruct l as [|a l].
    + cbn [skipn]. rewrite !nth_overflow by (cbn; lia). reflexivity.
    + cbn [skipn plus nth]. apply IH.
Qed.

Lemma w4c_nth_clear_hi : forall (j : nat) (st : list byte), (7 <= j)%nat -> (6 <= length st)%nat ->
  nth j (Prog.RcFrag.fg_clear st) (Z_to_bv 8 0) = nth j st (Z_to_bv 8 0).
Proof.
  intros j st Hj HL. unfold Prog.RcFrag.fg_clear.
  rewrite app_nth2; rewrite length_firstn; [|rewrite Nat.min_l by lia; lia].
  rewrite Nat.min_l by lia.
  rewrite app_nth2; cbn [length]; [|lia].
  rewrite w4c_nth_sk. f_equal. lia.
Qed.

Lemma w4c_skipn15_clear : forall st : list byte, (6 <= length st)%nat ->
  skipn 15 (Prog.RcFrag.fg_clear st) = skipn 15 st.
Proof.
  intros st HL. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_skipn. unfold Prog.RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn.
    cbn [length]. rewrite Nat.min_l by lia. lia.
  - intros i Hi. rewrite length_skipn in Hi. rewrite !w4c_nth_sk. apply w4c_nth_clear_hi; lia.
Qed.

Lemma w4c_bat_join_lo : forall st g i, 0 <= i -> i < 8 + Prog.RcFrag.fg_lf st -> (Z.to_nat i < length st)%nat ->
  Prog.RcFrag.bat (Prog.RcFrag.fg_join st g) i = Prog.RcFrag.bat st i.
Proof.
  intros st g i H0 Hlf HL. unfold Prog.RcFrag.bat, Prog.RcFrag.fg_join.
  assert (Hlen : (Z.to_nat i < length (firstn (Z.to_nat (8 + Prog.RcFrag.fg_lf st)) st))%nat).
  { rewrite length_firstn. apply Nat.min_glb_lt; [|exact HL]. apply Z2Nat.inj_lt; lia. }
  rewrite app_nth1 by exact Hlen. rewrite w4c_nthfn; [reflexivity| apply Z2Nat.inj_lt; lia].
Qed.

Lemma w4c_bat_join_mid : forall st g i, 8 + Prog.RcFrag.fg_lf st <= i -> i < 8 + Prog.RcFrag.fg_T st g ->
  0 <= Prog.RcFrag.fg_lf st -> (Z.to_nat (8 + Prog.RcFrag.fg_lf st) <= length st)%nat ->
  27 + Prog.RcFrag.fg_n g <= Z.of_nat (length g) ->
  Prog.RcFrag.bat (Prog.RcFrag.fg_join st g) i = Prog.RcFrag.bat g (27 + (i - 8 - Prog.RcFrag.fg_lf st)).
Proof.
  intros st g i H1 H2 H0 HL HG. unfold Prog.RcFrag.fg_T in H2.
  unfold Prog.RcFrag.bat, Prog.RcFrag.fg_join, Prog.RcFrag.fg_body, Prog.RcFrag.bsl. f_equal.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l by exact HL.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite w4c_nthfn by lia. rewrite w4c_nth_sk. f_equal. lia.
Qed.

Lemma w4c_bat_firstn_skipn : forall (l : list byte) n (k : nat) i, 0 <= i -> i < n ->
  Prog.RcFrag.bat (firstn (Z.to_nat n) (skipn k l)) i = Prog.RcFrag.bat l (Z.of_nat k + i).
Proof.
  intros l n k i H0 H1. unfold Prog.RcFrag.bat. f_equal. rewrite w4c_nthfn by lia. rewrite w4c_nth_sk. f_equal. lia.
Qed.

Lemma w4c_joined_close : forall st g s, length st = 72%nat -> length g = 50%nat -> B.Prog.SlotModel.frag_ok st ->
  B.Prog.SlotModel.FI st s ->
  Prog.RcFrag.bat st 6 = 1 -> 1 <= Prog.RcFrag.fg_n g <= 22 -> 14 <= Prog.RcFrag.fg_T st g ->
  Prog.RcFrag.bat (Prog.RcFrag.fg_join st g) 17 = B.Prog.SlotModel.joined_byte s g 9 /\
  Prog.RcFrag.bat (Prog.RcFrag.fg_join st g) 18 = B.Prog.SlotModel.joined_byte s g 10.
Proof.
  intros st g s HL HG (_ & Hok) HFI H6 Hn HT.
  destruct (HFI H6) as (_ & En & Eb). pose proof (Hok H6) as Hlf.
  assert (K : forall i, 9 <= i <= 10 ->
    Prog.RcFrag.bat (Prog.RcFrag.fg_join st g) (8 + i) = B.Prog.SlotModel.joined_byte s g i).
  { intros i Hi. unfold B.Prog.SlotModel.joined_byte. rewrite En, Eb.
    destruct (Z.ltb_spec i (Prog.RcFrag.bat st 7)) as [Hlt|Hge].
    - rewrite w4c_bat_join_lo by (unfold Prog.RcFrag.fg_lf; rewrite ?HL; lia).
      rewrite (w4c_bat_firstn_skipn st (Prog.RcFrag.bat st 7) 8 i) by lia. reflexivity.
    - rewrite w4c_bat_join_mid by (unfold Prog.RcFrag.fg_T, Prog.RcFrag.fg_lf in *; rewrite ?HL, ?HG; lia).
      unfold Prog.RcFrag.fg_lf. f_equal. lia. }
  split; [exact (K 9 ltac:(lia)) | exact (K 10 ltac:(lia))].
Qed.

Lemma w4c_fg_addr_joined : forall st g s, length st = 72%nat -> length g = 50%nat -> B.Prog.SlotModel.frag_ok st ->
  B.Prog.SlotModel.FI st s ->
  Prog.RcFrag.bat st 6 = 1 -> 1 <= Prog.RcFrag.fg_n g <= 22 -> 14 <= Prog.RcFrag.fg_T st g ->
  Prog.RcFrag.fg_addr st g = B.Prog.SlotModel.joined_addr s g.
Proof.
  intros st g s HL HG Hok HFI H6 Hn HT.
  destruct (w4c_joined_close st g s HL HG Hok HFI H6 Hn HT) as (E17 & E18).
  unfold Prog.RcFrag.fg_addr, B.Prog.SlotModel.joined_addr. rewrite E17, E18. reflexivity.
Qed.

Lemma w4c_close_recsum : forall st g, Prog.RcFrag.fg_close st g = true ->
  Prog.RcRec.recsum (Prog.RcFrag.bsl (Prog.RcFrag.fg_join st g) 15 (Prog.RcFrag.fg_T st g - 8)) = 0.
Proof.
  intros st g H. unfold Prog.RcFrag.fg_close in H. rewrite !Bool.andb_true_iff in H.
  destruct H as (_ & Hz). apply Z.eqb_eq. exact Hz.
Qed.

Lemma w4c_sum_closes : forall inp j, B.Prog.SlotModel.t_rf inp j = 1 ->
  Prog.RcRec.recsum (firstn (Z.to_nat (Prog.RcFrag.fg_T (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j) - 8))
                       (skipn 15 (B.Prog.SlotModel.t_FGf inp j))) = 0.
Proof.
  intros inp j Hrf.
  pose proof (w4c_trf1_cls inp j Hrf) as Hcls.
  destruct (w4c_cls_close_inv _ _ _ Hcls) as (Hfr & Hkeep & Hclose & _).
  pose proof (w4c_t_FG_length inp j) as HLst. pose proof (w4c_t_g_length inp j) as HLg.
  pose proof (w4c_fr_fg_n _ _ Hfr) as Hn. pose proof (w4c_keep_T _ _ Hkeep) as HT64.
  pose proof (Prog.RcFragLib.rf_fg_join_length _ _ HLst HLg Hn HT64) as HLX.
  rewrite (w4c_tFGf_close inp j Hrf). rewrite w4c_skipn15_clear by (rewrite HLX; lia).
  pose proof (w4c_close_recsum _ _ Hclose) as Hrec. unfold Prog.RcFrag.bsl in Hrec.
  change (Z.to_nat 15) with 15%nat in Hrec. exact Hrec.
Qed.

Lemma w4c_bat_clear6 : forall x, (6 <= length x)%nat -> Prog.RcFrag.bat (Prog.RcFrag.fg_clear x) 6 = 0.
Proof.
  intros x Hx. unfold Prog.RcFrag.bat, Prog.RcFrag.fg_clear. change (Z.to_nat 6) with 6%nat.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (6 - Init.Nat.min 6 (length x))%nat with 0%nat by lia.
  cbn [app nth]. reflexivity.
Qed.

Lemma w4c_fok_clear : forall x, (6 <= length x)%nat -> B.Prog.SlotModel.frag_ok (Prog.RcFrag.fg_clear x).
Proof.
  intros x Hx. split; [left; apply w4c_bat_clear6; exact Hx|].
  rewrite (w4c_bat_clear6 x Hx). intros H. discriminate H.
Qed.

Lemma w4c_fok_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= Prog.RcFrag.fg_n g <= 22 ->
  B.Prog.SlotModel.frag_ok (Prog.RcFrag.fg_first st g).
Proof.
  intros st g HL HG Hn.
  assert (HB : length (Prog.RcFrag.bsl g 6 6) = 6%nat) by (rewrite (Prog.RcFragLib.rf_bsl_length g 6 6) by lia; reflexivity).
  assert (E6 : Prog.RcFrag.bat (Prog.RcFrag.fg_first st g) 6 = 1).
  { unfold Prog.RcFrag.bat, Prog.RcFrag.fg_first. change (Z.to_nat 6) with 6%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (6 - 6)%nat with 0%nat by lia. cbn [app nth]. reflexivity. }
  assert (E7 : Prog.RcFrag.bat (Prog.RcFrag.fg_first st g) 7 = Prog.RcFrag.fg_n g).
  { unfold Prog.RcFrag.bat, Prog.RcFrag.fg_first, Prog.RcFrag.fg_n. change (Z.to_nat 7) with 7%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (7 - 6)%nat with 1%nat by lia. cbn [app nth]. change (Z.to_nat 26) with 26%nat. reflexivity. }
  split; [right; exact E6|]. rewrite E7. intros _. exact Hn.
Qed.

Lemma w4c_fok_next : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  B.Prog.SlotModel.frag_ok st ->
  B.Prog.SlotModel.frag_ok (B.Prog.SlotModel.fg_next st g (Prog.RcFrag.fg_class f fr pa pp pn len st g)).
Proof.
  intros f fr pa pp pn len st g HL HG Hok. unfold Prog.RcFrag.fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0))%bool;
    [cbn [B.Prog.SlotModel.fg_next]; exact Hok|].
  destruct (Prog.RcFrag.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [B.Prog.SlotModel.fg_next]; exact Hok].
  destruct (Prog.RcFrag.bat g 19 =? 1).
  - cbn [B.Prog.SlotModel.fg_next]. apply w4c_fok_first; [exact HL | exact HG | exact (w4c_fr_fg_n len g FR)].
  - destruct (Prog.RcFrag.fg_keep st g) eqn:Hkeep0; cbn [negb];
      [|cbn [B.Prog.SlotModel.fg_next]; apply w4c_fok_clear; lia].
    destruct (Prog.RcFrag.fg_close st g); cbn [negb B.Prog.SlotModel.fg_next]; apply w4c_fok_clear;
      rewrite (Prog.RcFragLib.rf_fg_join_length st g HL HG (w4c_fr_fg_n len g FR) (w4c_keep_T st g Hkeep0)); lia.
Qed.

Lemma w4c_t_FG_S : forall inp j, B.Prog.SlotModel.t_FG inp (S j) = B.Prog.SlotModel.t_FGf inp j.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_FG, B.Prog.SlotModel.t_FGf. rewrite B.Prog.SlotModel.fst_at_S.
  unfold B.Prog.SlotModel.turn. cbv zeta.
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j)); reflexivity.
Qed.

Lemma w4c_fok_FG : forall inp j, B.Prog.SlotModel.frag_ok (B.Prog.SlotModel.t_FG inp j).
Proof.
  intros inp j. induction j as [|j IH].
  - assert (E : Prog.RcFrag.bat (B.Prog.SlotModel.t_FG inp 0) 6 = 0) by reflexivity.
    split; [left; exact E|]. rewrite E. intros H. discriminate H.
  - rewrite w4c_t_FG_S. unfold B.Prog.SlotModel.t_FGf, B.Prog.SlotModel.fg_st, B.Prog.SlotModel.fcls.
    apply (w4c_fok_next 1 1 1 1 1); [apply w4c_t_FG_length | apply w4c_t_g_length | exact IH].
Qed.

Lemma w4c_t_ID_S_norf : forall inp j, B.Prog.SlotModel.t_rf inp j <> 1 ->
  B.Prog.SlotModel.t_ID inp (S j) = B.Prog.SlotModel.t_IDr inp j.
Proof.
  intros inp j H. unfold B.Prog.SlotModel.t_rf, B.Prog.SlotModel.t_FG in H.
  unfold B.Prog.SlotModel.t_ID, B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.t_FG.
  rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn, B.Prog.SlotModel.fg_id. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H).
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j)); reflexivity.
Qed.

Lemma w4c_ba_nth_err_firstn : forall (n i : nat) (l : list byte), (i < n)%nat ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  induction n as [|n IH]; intros [|i] [|a l] H; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma w4c_ba_firstn : forall m a bs n, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H2). split; [exact H0|].
  split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite w4c_ba_nth_err_firstn by lia. apply H2. lia.
Qed.

Lemma w4c_ba_skipn : forall m a bs (k : nat), (k <= length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k Hk HB. rewrite <- (firstn_skipn k bs) in HB.
  apply lib.Lib.Mem.bytes_at_app in HB. destruct HB as (_ & HB).
  rewrite length_firstn, Nat.min_l in HB by exact Hk. exact HB.
Qed.

Lemma w4c_lrw38 : forall m a bs,
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB 38 bs] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros m a bs [[_ H] _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

(* a spill read at the cut's own spill base A (register 9) *)
Lemma w4c_spill_q64 : forall regs m off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) Hr9 HA0 HA1 Hoff.
  assert (HA'eq : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    unfold ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'.
    apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
    clear - HA' Hq0 Hq1 HA0 HA1 Hoff. rewrite (Z.mod_small A) in HA' by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* the register moves of a run that writes registers 10 .. 14 only *)
Ltac w4c_move := unfold ACtlCutP.FRAC, ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.FM, ACtlCutP.FLV, ACtlCutP.FTURN,
  ACtlCutP.FRBA, ACtlCutP.FRB, ACtlCutP.FS9, ACtlCutP.spill, ACtlCut.rgv, Reusable.YG0d.spZ in *.

Lemma w4c_frac_move : forall cx fr sel (regs regs' : bvmap 5 word) (m : word -> option byte),
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
  intros cx fr sel regs regs' m H E2 E3 E4 E8 E9 E19 E26. w4c_move.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

Lemma w4c_lk_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.LK cx fr j regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  ACtlCutP.LK cx fr j regs' m.
Proof. intros cx fr j regs regs' m H E9 E27. w4c_move. rewrite E9, E27. exact H. Qed.

Lemma w4c_fm_move : forall cx j phi fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FM cx j phi fr regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  ACtlCutP.FM cx j phi fr regs' m.
Proof. intros cx j phi fr regs regs' m H E9 E22 E24 E25. w4c_move. rewrite E9, E22, E24, E25. exact H. Qed.

Lemma w4c_flv_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FLV cx fr j regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.FLV cx fr j regs' m.
Proof. intros cx fr j regs regs' m H E9. w4c_move. rewrite E9. exact H. Qed.

Lemma w4c_fturn_move : forall cx j phi (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FTURN cx j phi regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> ACtlCutP.FTURN cx j phi regs' m.
Proof. intros cx j phi regs regs' m H E9. w4c_move. rewrite E9. exact H. Qed.

Lemma w4c_frba_move : forall cx j fr phi (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FRBA cx j fr phi regs m ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.FRBA cx j fr phi regs' m.
Proof. intros cx j fr phi regs regs' m H E2 E9. w4c_move. rewrite E2, E9. exact H. Qed.

Lemma w4c_fs9_move : forall cx j (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FS9 cx j regs m ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> ACtlCutP.FS9 cx j regs' m.
Proof. intros cx j regs regs' m H E9. w4c_move. rewrite E9. exact H. Qed.

(* visibility of a run's reads: the journal's stack window, the owned class-6 frame *)
Lemma w4c_win_vis : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
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

Lemma w4c_frame_vis : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos lo len,
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

Lemma w4c_fr_ly3 : forall (cx : ACtlCut.ctlcx) ly3 fr,
  Reusable.YG0f.layout_le (length (Reusable.YG00.st_secs (ACtlCut.c_S cx))) (ACtlCut.c_ly cx) ly3 ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr.
Proof.
  intros cx ly3 fr Hly ->. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity.
Qed.

(* T11: the five runtime cells the bcmp wrapper reads, from AR (added 06:30Z; drafted by a Theorem Labs lane; same
   cells as a Theorem Labs lane's W3b ctl_bcmp_cells; owner a Theorem Labs lane, ctlrt_of_AR shape).  ctl_rt does not carry them:
   they are writable image data, so ro_agree does not give them and asan_cells has none.  Users: the
   reac_ctrl_identity_fragment and reply call sites (W3a, W3b, W4c). *)
Hypothesis ctl_bcmp_cells_of_AR : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.REAL_BCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.bcmp_wrap_c.BCMP)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.REAL_MEMCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.memcmp_c.MEMCMP)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.GOT_CF (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.bcmp_wrap_c.CF)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem (B.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1] /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem (B.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1].

(* ---------------------------------------------------------------------------------------------------------
   (b) NEW SECTION HYPOTHESES

   1. B_bcmp_tramp_at : B_bcmp_tramp_entry = B.Prog.bcmp_wrap_c.BCMP_WRAP.
      WHY: the file states the trampoline entry as the Variable B_bcmp_tramp_entry and the header forbids the
      literal, while the `_F` stretch F14F.f14_evt_0c_pre_F ends at bcmp_wrap_c.BCMP_WRAP; the stage needs the one
      equation that ties them.  OBLIGATION: the core's trampoline name (YTramp.bcmp_tramp) is 0x42aac =
      bcmp_wrap_c.BCMP_WRAP, so the TOP discharges it by eq_refl.  OWNER: a Theorem Labs lane (the file's TOP); name and text
      as a Theorem Labs lane gave them (06:15Z).

   2. ctl_kind_name_addressable : the walk's SHARED RtPost text, lib/B/RTPOST-SHARED-B.txt:154-155, token for token.
      WHY: FLI's KNT carries `addressable m KIND_NAME 112`; the image's SHADOW is allocator-owned, so no munch /
      visibility fact carries it across the bcmp call -- only AR does.  OBLIGATION / OWNER: a Theorem Labs lane's
      lib/B/ProgBridgeData.v (vm_compute over a Theorem Labs lane's regenerated tables), as the shared text states.

   3. ctl_rt_C at the post-call memory (route (C), a Theorem Labs lane 09:20Z): a Theorem Labs lane's proved
      B.ProgWorldCtlRtC.ctl_rt_C_of_AR through w4c_ctlrt below, with the shared texts TFIB_SYMS / RELRO_IMG / RO_OFL
      (RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; the TOP discharges all three).  No VIS0 (false at an AR state,
      a Theorem Labs lane's truth audit) and no OWNED_RO. *)

Hypothesis B_bcmp_tramp_at : B_bcmp_tramp_entry = B.Prog.bcmp_wrap_c.BCMP_WRAP.

Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* ctl_rt_C at an exit (route (C); W5's form, a Theorem Labs lane 68d9f362f0d): B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED;
   CtrlTSyms + AR_laws + AR + arodata_okP), whose premise TFIB_SYMS the next line carries, exact name and text; it
   supplies arodata_okP at the state from ctl_base's arodata_okS through Reusable.APostBase.arodata_ok_journalP (which
   finds RO_OFL as an instance).  The top discharges all three: TFIB_SYMS := Reusable.YD2l.CtrlB_syms, RELRO_IMG :=
   relro_img_CtrlB, RO_OFL by computation at SK := Reusable.YE2k.tfib_sink_head. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* ctl_rt_C at any journal state of the walk (copy, renamed, of lib/B/ACtlW5.v's w5_ctlrt at 68d9f362f0d): the proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR at this file's TFIB_SYMS / LAWS, its arodata_okP premise from ctl_base's
   arodata_okS through APostBase.arodata_ok_journalP and B.ProgWorld.arodata_okP_of_S. *)
Lemma w4c_arodata_cut : forall cx own ly3 S3 W3 mem3 md3 k, ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _) & _).
  exact (Reusable.APostBase.arodata_ok_journalP (RO := RO_OFL) segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           HJ HRO).
Qed.

Lemma w4c_ctlrt : forall cx own ly3 S3 W3 mem3 md3 k, ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HJ as (HAR & _).
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 HAR
           (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (w4c_arodata_cut cx own ly3 S3 W3 mem3 md3 k HB HJ)
              ltac:(lia) ltac:(lia))).
Qed.

(* ---- route (C): what lies in the cut's own shadow B.ACtlRtC.cut_shadow (its (F) owned-frame and (L) live-block
   disjuncts), for the inclusion of each callee's R in the region ctl_rt_C carries ---- *)
Lemma w4c_cs_frame : forall ly S cid pos a, In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly cid pos) <= a <
  Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly cid pos) + Reusable.YG00.fs_frame_bytes cid / 8 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof. intros ly S cid pos a Hin Ha. left. exists cid, pos. exact (conj Hin Ha). Qed.

Lemma w4c_cs_block : forall ly S p n a, In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= a <
  Reusable.YG0f.shadow_addr (p + Reusable.YG00.req_size n - 1) / 8 * 8 + 8 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof. intros ly S p n a Hin Ha. right. left. exists p, n. exact (conj Hin Ha). Qed.

(* The owned class-6 frame at fr (fr mod 8 = 0, 4096 bytes): its 512 shadow bytes. *)
Lemma w4c_cs_frame6 : forall ly S pos fr a, In (6, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 8 = 0 ->
  fr / 8 + B.AsanRT.ASAN_K <= a < fr / 8 + B.AsanRT.ASAN_K + 512 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S pos fr a Hin Efr H8 Ha. apply (w4c_cs_frame ly S 6 pos a Hin).
  rewrite Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. unfold B.AsanRT.ASAN_K in Ha. lia.
Qed.

(* The 8-aligned shadow-word cover of [lo, hi] inside that frame, 64 bytes away from either end. *)
Lemma w4c_cs_frame6_cover : forall ly S pos fr lo hi a, In (6, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 8 = 0 -> fr + 64 <= lo -> hi + 64 < fr + 4096 ->
  (lo / 8 + B.AsanRT.ASAN_K) / 8 * 8 <= a < (hi / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S pos fr lo hi a Hin Efr H8 H1 H2 Ha. apply (w4c_cs_frame6 ly S pos fr a Hin Efr H8).
  unfold B.AsanRT.ASAN_K in *. Z.div_mod_to_equations. lia.
Qed.

(* The 8-aligned shadow-word cover of [lo, hi] inside a live block (p, n). *)
Lemma w4c_cs_blk : forall ly S p n lo hi a, In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> hi <= p + Reusable.YG00.req_size n - 1 ->
  (lo / 8 + B.AsanRT.ASAN_K) / 8 * 8 <= a < (hi / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S p n lo hi a Hin H1 H2 Ha. apply (w4c_cs_block ly S p n a Hin).
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. unfold B.AsanRT.ASAN_K in Ha.
  Z.div_mod_to_equations. lia.
Qed.

(* seg_F13: a Theorem Labs lane's R at the fragment call (f := fragb fr, in the owned class-6 frame; the callee's fr := phi, the
   received record's live block) lies in the cut's own shadow: each memcpy / bcmp D-side range [f .., ..) of R in the
   frame's 512 shadow bytes (cut_shadow (F)), each S-side range [phi .., ..) in the block's shadow-word cover (L). *)
Lemma w4c13_frag_R_in : forall ly S pos fr phi len pa pp pn st g a,
  In (6, pos) (Reusable.YG01.frames S) -> Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 8 = 0 ->
  0 <= fr -> fr + 4096 <= 2 ^ 64 ->
  In (phi, len) (Reusable.YG0d.ablocks B ly S) -> 0 <= len -> 0 <= phi -> phi + 64 <= 2 ^ 64 ->
  B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R
    (ACtlCutP.fragb fr) phi len pa pp pn st g a ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S pos fr phi len pa pp pn st g a Hin Efr H8 Hf0 Hf1 Hphi Hl0 Hp0 Hp1 HR.
  unfold B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R,
    B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R, B.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R in HR.
  destruct HR as (_ & _ & _ & _ & _ & Hfr & HR).
  pose proof (w4c_fr_len50 _ _ Hfr) as H50. pose proof (w4c_fr_fg_n _ _ Hfr) as Hn.
  pose proof (proj2 (Reusable.YCbq.req_size_pos len Hl0)) as Hrs.
  assert (Hlf : 0 <= Prog.RcFrag.fg_lf st)
    by (unfold Prog.RcFrag.fg_lf, Prog.RcFrag.bat; exact (proj1 (bv_unsigned_in_range _ _))).
  assert (Hlf' : Prog.RcFrag.fg_lf st < 256)
    by (unfold Prog.RcFrag.fg_lf, Prog.RcFrag.bat; exact (proj2 (bv_unsigned_in_range _ _))).
  assert (U : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x)
    by (intros x Hx; apply lib.Lib.MState.unsigned_lit; exact Hx).
  assert (FR : forall p n, fr + 64 <= p -> p + n - 1 + 64 < fr + 4096 -> B.Prog.sh_word_on.sh_word_on p n a ->
               B.ACtlRtC.cut_shadow B ly S a).
  { intros p n H1 H2 (_ & Hw). unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr in Hw.
    exact (w4c_cs_frame6_cover ly S pos fr p (p + n - 1) a Hin Efr H8 H1 H2 Hw). }
  assert (BK : forall p n, phi <= p -> p + n - 1 <= phi + Reusable.YG00.req_size len - 1 ->
               B.Prog.sh_word_on.sh_word_on p n a -> B.ACtlRtC.cut_shadow B ly S a).
  { intros p n H1 H2 (_ & Hw). unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr in Hw.
    exact (w4c_cs_blk ly S phi len p (p + n - 1) a Hphi H1 H2 Hw). }
  unfold ACtlCutP.fragb in *.
  destruct HR as [(_ & [[H|H]|[H|H]]) | (_ & _ & [[H|H]|(Hk & [H|H])])];
    rewrite ?U in H by (unfold Prog.RcFrag.fg_lf in *; lia).
  - refine (BK _ _ _ _ H); lia.
  - refine (FR _ _ _ _ H); lia.
  - refine (BK _ _ _ _ H); lia.
  - refine (FR _ _ _ _ H); lia.
  - refine (FR _ _ _ _ H); lia.
  - refine (BK _ _ _ _ H); lia.
  - refine (BK _ _ _ _ H); lia.
  - pose proof (w4c_keep_T _ _ Hk) as HT. unfold Prog.RcFrag.fg_T in HT.
    refine (FR _ _ _ _ H); lia.
Qed.

(* =========================================================================================================
   KIT for seg_F13 (prefix w4c13_).  Copies, renamed, of the sibling W4a / W4b kits (lib/B/ACtlW4a.v,
   ACtlW4b.v), of image A's caller-side MemNorm transports (lib/A/MemNormTr.v, over image B's names) and of the pure
   fragment-model facts of Seg/F13.v; plus the frame-placement and frame-journal facts of this call site.
   ========================================================================================================= *)
Local Notation w4c13_AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation w4c13_AGR m m' x :=
  (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x)).

Lemma w4c13_wa_u : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. exact (lib.Lib.Mem.wa_unsigned x Hx). Qed.

Lemma w4c13_rgv_inj : forall regs (r : bv 5) a b, ACtlCut.rgv regs r a -> ACtlCut.rgv regs r b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ha' Hb'. unfold ACtlCut.rgv in *. rewrite Ha in Hb.
  apply (f_equal (@bv_unsigned 64)) in Hb. rewrite !w4c13_wa_u in Hb by lia. exact Hb.
Qed.

Lemma w4c13_rgv_move : forall regs regs' (r : bv 5) v, ACtlCut.rgv regs r v ->
  lib.Reusable.YK11.getr regs' r = lib.Reusable.YK11.getr regs r -> ACtlCut.rgv regs' r v.
Proof. intros regs regs' r v H E. unfold ACtlCut.rgv in *. rewrite E. exact H. Qed.

Lemma w4c13_mrd_munch : forall W m m' x, lib.Lib.Frame.munch W m m' -> 0 <= x < 2 ^ 64 ->
  lib.Lib.Frame.outside W x -> w4c13_AGR m m' x.
Proof.
  intros W m m' x MU Hx Ho. unfold lib.Lib.Mem.mrd. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite w4c13_wa_u by exact Hx. exact Ho.
Qed.

Lemma w4c13_ba_keep : forall m m' a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> w4c13_AGR m m' x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

Lemma w4c13_addr_keep : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> w4c13_AGR m m' (B.AsanRT.shadow_addr (p + i))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

Lemma w4c13_spill_keep : forall regs regs' m m' A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> w4c13_AGR m m' x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hr9 HA0 HA1 Hoff E9 HK (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    unfold ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'.
    apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
    clear - HA' Hq0 Hq1 HA0 HA1 Hoff. rewrite (Z.mod_small A) in HA' by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [exact (w4c13_rgv_move regs regs' 9 A Hr9 E9)|].
  unfold ACtlCutP.q64 in *. apply (w4c13_ba_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

Lemma w4c13_aj_bits : forall cx own ly3 S3 W3 mem3 md3 k, w4c13_AJ cx own ly3 S3 W3 mem3 md3 k ->
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 /\
  lib.Reusable.YM05.alloc_ceiling <= ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK /\ ACtlCut.c_sp cx <= 2 ^ 47 /\
  (forall a, ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < ACtlCut.c_sp cx ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists b, mem3 (Z_to_bv 64 a) = Some b).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
  split; [exact HAR|]. split; [lia|]. split; [lia|].
  exact Hpres.
Qed.

Lemma w4c13_spZ : forall regs, 0 <= Reusable.YG0d.spZ regs < 2 ^ 64.
Proof.
  intros regs. unfold Reusable.YG0d.spZ.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma w4c13_noseg : forall a, 0x5fe000 <= a -> find_segment B.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. apply (Reusable.YK04.find_segment1_none_above _ 0x5fe000); [vm_compute; reflexivity | exact Ha].
Qed.

Lemma w4c13_some_of_wmono : forall m m' a, 0 <= a < 2 ^ 64 -> find_segment B.Img0.rsegs a 1 = None ->
  (exists b, m (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> exists b, m' (Z_to_bv 64 a) = Some b.
Proof.
  intros m m' a Ha Hn (b & Hb) WM.
  assert (Hw : wview B.Img0.rsegs m (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hb; discriminate).
  pose proof (WM _ Hw) as Hw'. unfold wview in Hw'.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  rewrite w4c13_wa_u in Hw' by lia. rewrite Hn in Hw'. contradiction.
Qed.

Lemma w4c13_outside_dec : forall (WR : list (Z * Z)) x, lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & H'); exact (H H')].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* The journal across a run whose writes lie in the stack window or the owned frame (YCbq.ajournal_exec); W4a's
   w4a_aj_run with its `0x5fe000 <= a` (no segment byte) premise stated as `find_segment .. = None`, which the
   owned frame meets by AR's client-image law (w4c13_frame_noseg) wherever the frame lies. *)
Lemma w4c13_aj_run : forall cx own ly3 S3 W3 mem3 md3 k mem' md' (WR : list (Z * Z)),
  w4c13_AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Lib.Frame.munch WR mem3 mem' -> lib.Lib.Frame.wmono B.Img0.rsegs mem3 mem' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, ~ lib.Lib.Frame.outside WR a -> 0 <= a < 2 ^ 64 /\ find_segment B.Img0.rsegs a 1 = None /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\
      Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
        (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx))
        (Reusable.YG0d.ablocks B ly3 S3) ly3 own a) ->
  w4c13_AJ cx own ly3 S3 W3 mem' md' k.
Proof using LAWS segs_low.
  intros cx own ly3 S3 W3 mem3 md3 k mem' md' WR HJ MU WM Hhid Hsame HW.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md'
           (fun a => ~ lib.Lib.Frame.outside WR a) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (w4c13_outside_dec WR (bv_unsigned x)) as [H|H]; [exact H | contradiction].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x) eqn:EH; [exact Hx|].
    destruct (w4c13_outside_dec WR (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
    destruct (HW _ Ho) as (Hr & Hn & Hs & _).
    destruct (w4c13_some_of_wmono mem3 mem' (bv_unsigned x) Hr Hn Hs WM) as (b & Hb).
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
  - exact Hhid.
  - exact Hsame.
  - intros a Ha. exact (proj2 (proj2 (proj2 (HW a Ha)))).
Qed.

(* The owned class-6 frame: its address, its bytes and shadow (visible, present, owned by the journal); W4a's
   w4a_frame. *)
Lemma w4c13_frame : forall cx k ly3 S3 W3 mem3 md3 fr,
  w4c13_AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  fr mod 32 = 0 /\ 4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\ Reusable.YCbq.in_frames ly3 (ACtlCut.own6 cx) a) /\
  (forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
      Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\ Reusable.YCbq.in_frames ly3 (ACtlCut.own6 cx) a).
Proof using LAWS.
  intros cx k ly3 S3 W3 mem3 md3 fr HJ Hfrs Hfr.
  pose proof HJ as (HAR & Hly & _).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Hfr. unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF.
    reflexivity. }
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H32 & Happ & Hb & Hs).
  destruct (Reusable.YG0d.al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as (_ & Hbnd).
  rewrite Forall_forall in Hbnd. pose proof (Hbnd _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efa, E6 in *.
  assert (Esh : Reusable.YG0f.shadow_addr fr = B.AsanRT.shadow_addr fr)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|]. split.
  - intros a Ha. destruct (Hb a Ha) as ((Hv & Hp) & _). split; [exact Hv|]. split; [exact Hp|].
    exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa, E6. lia.
  - intros a Ha. change (4096 / 8) with 512 in Hs. rewrite Esh in Hs.
    destruct (Hs (a - B.AsanRT.shadow_addr fr) ltac:(lia)) as ((Hv & Hp) & _).
    replace (B.AsanRT.shadow_addr fr + (a - B.AsanRT.shadow_addr fr)) with a in Hv, Hp by lia.
    split; [exact Hv|]. split; [exact Hp|].
    exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa, E6, Esh. change (4096 / 8) with 512. lia.
Qed.

(* Image B's segments tile [0x10000, 0x5fe000) (ProgBridge.rsegs_spans), so every byte there is an image byte. *)
Lemma w4c13_in_img : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (H : exists b sz, In (b, sz) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s)))
                                           B.Img0.rsegs) /\ b <= a < b + sz).
  { rewrite B.ProgBridge.rsegs_spans.
    destruct (Z_lt_le_dec a 0x31000); [exists 0x10000, 0x21000; split; [left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 0x9f000); [exists 0x31000, 0x6e000; split; [right; left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 0xa2000); [exists 0x9f000, 0x3000; split; [right; right; left; reflexivity | lia]|].
    exists 0xa2000, 0x55c000. split; [right; right; right; left; reflexivity | lia]. }
  destruct H as (b & sz & Hin & Hb). apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
  exists s. split; [exact Hs | lia].
Qed.

(* A live frame lies wholly below or wholly above the image (AR's client-image law on its first and last bytes). *)
Lemma w4c13_frame_place : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (cid, pos) (Reusable.YG01.frames S) ->
  0 < Reusable.YG00.fs_frame_bytes cid <= 4096 ->
  Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid <= 0x10000 \/
  0x5fe000 <= Reusable.YG0f.frame_addr ly cid pos.
Proof using LAWS.
  intros ly S W mem md cid pos HAR Hin Hsz.
  set (F := Reusable.YG0f.frame_addr ly cid pos) in *.
  set (z := Reusable.YG00.fs_frame_bytes cid) in *.
  destruct (Z_le_gt_dec (F + z) 0x10000) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec 0x5fe000 F) as [H2|H2]; [right; exact H2|].
  exfalso.
  assert (Ha : F <= Z.max F 0x10000 < F + z) by lia.
  apply (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly S W mem md (Z.max F 0x10000) HAR
                  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha))))))).
  apply w4c13_in_img. lia.
Qed.

(* A byte of a live frame is in no segment (the client-image law: a frame byte is not an image byte). *)
Lemma w4c13_frame_noseg : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos a,
  Reusable.YG0n.AR segs B ly S W mem md -> In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly cid pos <= a < Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid ->
  find_segment B.Img0.rsegs a 1 = None.
Proof using LAWS.
  intros ly S W mem md cid pos a HAR Hin Ha.
  destruct (find_segment B.Img0.rsegs a 1) as [s|] eqn:E; [exfalso | reflexivity].
  destruct (Reusable.YK04.find_segment_some_spec _ _ _ _ E) as (Hs & H1 & H2).
  apply (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha))))))).
  exists s. split; [exact Hs | lia].
Qed.

Lemma w4c13_ro_false : forall a, find_segment B.Img0.rsegs (bv_unsigned a) 1 = None ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs a = false.
Proof. intros a H. unfold lib.Lib.Mem.ro_addr. rewrite H. reflexivity. Qed.

(* ---- image A's MemNormTr transports (lib/A/MemNormTr.v), over image B's names ---- *)
Lemma w4c13_asan_cells_normalize : forall m, B.MemNorm.ro_agree B.Img0.rsegs m -> B.AsanRT.asan_cells m ->
  B.AsanRT.asan_cells (B.MemNorm.normalize B.Img0.rsegs m).
Proof.
  intros m RO H. unfold B.AsanRT.asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end.
  all: apply (B.MemNorm.bytes_at_normalize B.Img0.rsegs m _ _ RO); assumption.
Qed.

Lemma w4c13_addressable_normalize : forall m p n, B.MemNorm.ro_agree B.Img0.rsegs m ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable (B.MemNorm.normalize B.Img0.rsegs m) p n.
Proof.
  intros m p n RO (H0 & H1 & H2 & H). pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m RO) as REL.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|].
  exists b. split; [|exact Hok]. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m (B.MemNorm.normalize B.Img0.rsegs m) _ REL).
  exact Hb.
Qed.

Lemma w4c13_stk_normalize : forall m lo hi, B.MemNorm.ro_agree B.Img0.rsegs m ->
  (forall a, lo <= a < hi -> lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false) ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) lo hi.
Proof.
  intros m lo hi RO Hro (H0 & H1 & H). pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m RO) as REL.
  split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (Hro a Ha) as E.
  split; [rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m (B.MemNorm.normalize B.Img0.rsegs m) _ REL E); exact Hv|].
  exists b. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m (B.MemNorm.normalize B.Img0.rsegs m) _ REL). exact Hb.
Qed.

Lemma w4c13_rw_cells_normalize : forall m p cs, B.MemNorm.ro_agree B.Img0.rsegs m ->
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) ->
     lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa (p + i)) = false) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m p cs ->
  lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) p cs.
Proof.
  intros m p cs RO Hn [[Hwf Hb] Hw]. pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m RO) as REL.
  split; [split; [exact Hwf | exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs m p _ RO Hb)]|].
  exact (B.MemNorm.wr_at_norm B.Img0.rsegs m (B.MemNorm.normalize B.Img0.rsegs m) p _ REL Hw Hn).
Qed.

Lemma w4c13_stk_of_rel : forall m m0 lo hi, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  lib.Lib.Frame.stk B.Img0.rsegs m0 lo hi -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (B.MemNorm.ro_false_of_wview B.Img0.rsegs m m0 _ REL Hv) as E.
  split; [rewrite <- (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ REL). exact Hb.
Qed.

Lemma w4c13_ms_rel_MS : forall s R F pc fc rv m0 ro,
  B.MemNorm.ms_rel B.Img0.rsegs s (lib.Lib.MState.MS R F pc fc rv m0 ro) ->
  s = lib.Lib.MState.MS R F pc fc rv (ms_mem s) ro /\ B.MemNorm.mem_rel B.Img0.rsegs (ms_mem s) m0.
Proof.
  intros s R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). split; [|exact E8].
  destruct s as [x1 x2 x3 x4 x5 x6 x7 x8]. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
Qed.

Lemma w4c13_fg_mem_of_rel : forall f pa pp pn st g c m m0, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.Prog.reac_ctrl_identity_fragment_c.fg_mem f pa pp pn st g c m0 ->
  B.Prog.reac_ctrl_identity_fragment_c.fg_mem f pa pp pn st g c m.
Proof.
  intros f pa pp pn st g c m m0 REL H.
  destruct c; cbv beta iota delta [B.Prog.reac_ctrl_identity_fragment_c.fg_mem] in H |- *; try exact I.
  - exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ _ _ REL) H).
  - exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ _ _ REL) H).
  - exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ _ _ REL) H).
  - destruct H as (H1 & H2 & H3 & H4).
    refine (conj _ (conj _ (conj _ _))); apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ _ _ REL)); assumption.
Qed.

(* ---- pure facts (Seg/F13.v's copies, renamed; the rest of the fragment model is the file's w4c_ kit) ---- *)
Lemma w4c13_inb_range : forall inp j, 0 <= ACtlCutP.SM.inb inp j < 256.
Proof.
  intros inp j. unfold ACtlCutP.SM.inb, ACtlCutP.RIM.bz.
  pose proof (bv_unsigned_in_range 8 (ACtlCutP.RIM.nthb inp (Z.to_nat j))) as H.
  unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma w4c13_flen_small : forall inp j, ACtlCutP.SM.t_len inp j <= 65535.
Proof.
  intros inp j. unfold ACtlCutP.SM.t_len, ACtlCutP.SM.f_len.
  pose proof (Z.le_min_l (ACtlCutP.SM.f_L inp (ACtlCutP.SM.fc inp j))
               (ACtlCutP.SM.f_left inp (ACtlCutP.SM.fc inp j) - ACtlCutP.SM.f_h inp (ACtlCutP.SM.fc inp j))) as Hm.
  assert (HL : ACtlCutP.SM.f_L inp (ACtlCutP.SM.fc inp j) <= 65535).
  { unfold ACtlCutP.SM.f_L. pose proof (w4c13_inb_range inp (ACtlCutP.SM.fc inp j)) as H1.
    pose proof (w4c13_inb_range inp (ACtlCutP.SM.fc inp j + 1)) as H2.
    destruct (2 <=? ACtlCutP.SM.f_left inp (ACtlCutP.SM.fc inp j)); lia. }
  lia.
Qed.

Lemma w4c13_t_ID_length : forall inp j, length (ACtlCutP.SM.t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold ACtlCutP.SM.t_ID in *. rewrite ACtlCutP.SM.fst_at_S. unfold ACtlCutP.SM.turn. cbv zeta.
  assert (Hr : length (ACtlCutP.SM.rp_id (ACtlCutP.SM.fs_id (ACtlCutP.SM.fst_at inp j)) (ACtlCutP.SM.t_len inp j)
                         (ACtlCutP.SM.t_g inp j)) = 38%nat).
  { unfold ACtlCutP.SM.rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply ACtlCutP.RIM.ING_length; exact IH | exact IH]. }
  assert (Hf : length (ACtlCutP.SM.fg_id (ACtlCutP.SM.rp_id (ACtlCutP.SM.fs_id (ACtlCutP.SM.fst_at inp j))
                          (ACtlCutP.SM.t_len inp j) (ACtlCutP.SM.t_g inp j)) (ACtlCutP.SM.t_len inp j)
                         (ACtlCutP.SM.fs_fg (ACtlCutP.SM.fst_at inp j)) (ACtlCutP.SM.t_g inp j)) = 38%nat).
  { unfold ACtlCutP.SM.fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply ACtlCutP.RIM.ING_length; exact Hr | exact Hr]. }
  destruct (ACtlCutP.SM.f_opens (ACtlCutP.SM.t_len inp j) (ACtlCutP.SM.t_g inp j)); cbn [ACtlCutP.SM.fs_id]; exact Hf.
Qed.

Lemma w4c13_t_IDr_length : forall inp j, length (ACtlCutP.SM.t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold ACtlCutP.SM.t_IDr, ACtlCutP.SM.rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply ACtlCutP.RIM.ING_length; apply w4c13_t_ID_length | apply w4c13_t_ID_length].
Qed.

Lemma w4c13_fst_body_len : forall inp j, (length (ACtlCutP.SM.fs_body (ACtlCutP.SM.fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite ACtlCutP.SM.fst_at_S. unfold ACtlCutP.SM.turn. cbv zeta.
  destruct (ACtlCutP.SM.f_opens (ACtlCutP.SM.t_len inp j) (ACtlCutP.SM.t_g inp j)); cbn [ACtlCutP.SM.fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, w4c_t_g_length. lia.
Qed.

Lemma w4c13_bat_nonneg : forall bs i, 0 <= Prog.RcFrag.bat bs i.
Proof. intros bs i. unfold Prog.RcFrag.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.

Lemma w4c13_bat_lt : forall bs i, Prog.RcFrag.bat bs i < 256.
Proof.
  intros bs i. unfold Prog.RcFrag.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma w4c13_fi_nb : forall st s, ACtlCutP.SM.FI st s -> Prog.RcFrag.bat st 6 = 1 ->
  ACtlCutP.SM.fs_have s = 1 /\ ACtlCutP.SM.fs_n s = Prog.RcFrag.bat st 7.
Proof. intros st s H H6. destruct (H H6) as (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Lemma w4c13_fst_bounds : forall inp j,
  (ACtlCutP.SM.fs_have (ACtlCutP.SM.fst_at inp j) = 0 \/ ACtlCutP.SM.fs_have (ACtlCutP.SM.fst_at inp j) = 1) /\
  0 <= ACtlCutP.SM.fs_n (ACtlCutP.SM.fst_at inp j) < 256.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [ACtlCutP.SM.fst_at]. unfold ACtlCutP.SM.fs0. cbn [ACtlCutP.SM.fs_have ACtlCutP.SM.fs_n]. lia.
  - rewrite ACtlCutP.SM.fst_at_S. unfold ACtlCutP.SM.turn. cbv zeta.
    destruct (ACtlCutP.SM.f_opens (ACtlCutP.SM.t_len inp j) (ACtlCutP.SM.t_g inp j));
      cbn [ACtlCutP.SM.fs_have ACtlCutP.SM.fs_n].
    + pose proof (w4c13_bat_nonneg (ACtlCutP.SM.t_g inp j) 26). pose proof (w4c13_bat_lt (ACtlCutP.SM.t_g inp j) 26). lia.
    + exact IH.
Qed.

Lemma w4c13_ba_det : forall m a bs cs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a cs -> length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & Hb) (_ & _ & Hc) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (Hb i Hi), <- (Hc i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None cs i) ltac:(lia)). reflexivity.
Qed.

Lemma w4c13_q64_det : forall m a v1 v2, ACtlCutP.q64 m a v1 -> ACtlCutP.q64 m a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Hb1 Hb2.
  assert (E : lib.Lib.Mem.le8 (Z_to_bv 64 v1) = lib.Lib.Mem.le8 (Z_to_bv 64 v2))
    by (apply (w4c13_ba_det m a); [exact H1 | exact H2 | rewrite !lib.Lib.Mem.length_le8; reflexivity]).
  apply (f_equal le_bytes_to_word) in E. rewrite !lib.Lib.Mem.le_bytes_to_word_le8 in E.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !lib.Lib.MState.unsigned_lit in E by lia. exact E.
Qed.

Lemma w4c13_rwc_of_q64 : forall m a v, ACtlCutP.q64 m a v -> lib.Lib.Mem.wr_at B.Img0.rsegs m a 8 ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hq Hw. split; [split|].
  - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; exact I.
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hq.
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. exact Hw.
Qed.

Lemma w4c13_bsl_len_le : forall bs k n, (length (Prog.RcFrag.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold Prog.RcFrag.bsl. rewrite length_firstn. apply Nat.le_min_l. Qed.

(* Every address the callee may write lies in one of the five FgClose intervals (Seg/F13.v fp_in / fp_outside_of). *)
Lemma w4c13_fp_in : forall K f pa pp pn S c x,
  ~ lib.Lib.Frame.outside (Prog.RcFrag.fg_fp K f pa pp pn S c) x ->
  (f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S).
Proof.
  intros K f pa pp pn S c x H.
  assert (D : forall lo hi, (lo <= x < hi) \/ ~ (lo <= x < hi)) by (intros lo hi; lia).
  destruct (D f (f + 72)) as [H1|H1]; [left; exact H1|].
  destruct (D pa (pa + 2)) as [H2|H2]; [right; left; exact H2|].
  destruct (D pp (pp + 8)) as [H3|H3]; [right; right; left; exact H3|].
  destruct (D pn (pn + 8)) as [H4|H4]; [right; right; right; left; exact H4|].
  destruct (D (S - K) S) as [H5|H5]; [right; right; right; right; exact H5|].
  exfalso. apply H. destruct c; cbn [Prog.RcFrag.fg_fp lib.Lib.Frame.outside]; tauto.
Qed.

Lemma w4c13_fp_outside_of : forall K f pa pp pn S c x,
  ((f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S) ->
     False) ->
  lib.Lib.Frame.outside (Prog.RcFrag.fg_fp K f pa pp pn S c) x.
Proof.
  intros K f pa pp pn S c x H.
  destruct (w4c13_outside_dec (Prog.RcFrag.fg_fp K f pa pp pn S c) x) as [Ho|Ho]; [exact Ho|].
  exfalso. exact (H (w4c13_fp_in K f pa pp pn S c x Ho)).
Qed.

(* ---- presence, visibility ---- *)
Lemma w4c13_stk_of_pres : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> exists b, m (Z_to_bv 64 a) = Some b) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as (b & Hb).
  unfold lib.Lib.Mem.wa. split; [unfold wview; rewrite Hb; discriminate|].
  exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma w4c13_wr_of_pres : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> exists b, m (Z_to_bv 64 x) = Some b) -> lib.Lib.Mem.wr_at B.Img0.rsegs m a n.
Proof.
  intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (H (a + i) ltac:(lia)) as (b & Hb). unfold lib.Lib.Mem.wa, wview. rewrite Hb. discriminate.
Qed.

Lemma w4c13_addr_keep_sh : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR m m' x) -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n HA K. pose proof HA as (H0 & H1 & H2 & _).
  apply (w4c13_addr_keep m m' p n HA). intros i Hi. apply K.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in *.
  pose proof (Z.div_pos (p + i) 8 ltac:(lia) ltac:(lia)).
  assert ((p + i) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma w4c13_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

Lemma w4c13_heap_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
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

(* The 8-aligned shadow-word cover of a sub-range [x, q] of a live block's hull (AR's shadow law). *)
Lemma w4c13_cover_hull : forall (W : Reusable.YA0n.world segs) mem x n q,
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n ->
  0 <= x -> x <= q -> q <= x + n - 1 -> x + n <= 2 ^ 47 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr x / 8 * 8)
    (B.AsanRT.shadow_addr q / 8 * 8 + 8 - B.AsanRT.shadow_addr x / 8 * 8).
Proof.
  intros W mem x n q Hh Hx Hxq Hq Hn.
  assert (M1 : B.AsanRT.shadow_addr q <= B.AsanRT.shadow_addr (x + n - 1))
    by (unfold B.AsanRT.shadow_addr; pose proof (Z.div_le_mono q (x + n - 1) 8 ltac:(lia) Hq); lia).
  assert (M2 : B.AsanRT.shadow_addr q / 8 <= B.AsanRT.shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (M3 : B.AsanRT.shadow_addr x <= B.AsanRT.shadow_addr q)
    by (unfold B.AsanRT.shadow_addr; pose proof (Z.div_le_mono x q 8 ltac:(lia) Hxq); lia).
  assert (M4 : B.AsanRT.shadow_addr x / 8 <= B.AsanRT.shadow_addr q / 8) by (apply Z.div_le_mono; lia).
  assert (B0 : 0 <= B.AsanRT.shadow_addr x / 8)
    by (apply Z.div_pos; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia | lia]).
  assert (B1 : B.AsanRT.shadow_addr (x + n - 1) < 2 ^ 45).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    assert ((x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (B2 : B.AsanRT.shadow_addr q / 8 * 8 <= B.AsanRT.shadow_addr q)
    by (pose proof (Z.mul_div_le (B.AsanRT.shadow_addr q) 8 ltac:(lia)); lia).
  split; [lia|]. split; [pose proof (Z.mul_div_le (B.AsanRT.shadow_addr q) 8 ltac:(lia)); lia|].
  intros s Hs. apply (w4c13_vis_of_aview W mem). apply Hh.
  assert (E1 : Reusable.YG0f.shadow_addr x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (E2 : Reusable.YG0f.shadow_addr (x + n - 1) = B.AsanRT.shadow_addr (x + n - 1))
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite E1, E2. lia.
Qed.

(* The 8-aligned shadow-word cover of a sub-range [p, q] of a 4096-byte frame, inside the frame's 512 shadow bytes. *)
Lemma w4c13_cover_in : forall (H : word -> bool) lo p q,
  (forall a, B.AsanRT.shadow_addr lo <= a < B.AsanRT.shadow_addr lo + 512 -> H (Z_to_bv 64 a) = false) ->
  0 <= lo -> lo + 64 <= p -> p <= q -> q + 64 < lo + 4096 -> lo + 4096 <= 2 ^ 47 ->
  B.ProgBridge.range_visible H (B.AsanRT.shadow_addr p / 8 * 8)
    (B.AsanRT.shadow_addr q / 8 * 8 + 8 - B.AsanRT.shadow_addr p / 8 * 8).
Proof.
  intros H lo p q Hv H0 H1 H2 H3 H4.
  unfold B.ProgBridge.range_visible. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  rewrite P64. rewrite P47 in H4.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply Hv. Z.div_mod_to_equations. lia.
Qed.

(* The stack range's zero-shadow entry (AR's zero-shadow law): the shadow-word cover of [p, p + n) is visible. *)
Lemma w4c13_win_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n,
  Reusable.YG0n.AR segs B ly S W mem md ->
  0 <= Reusable.YG0f.ly_stk_lo ly -> Reusable.YG0f.ly_stk_lo ly + 128 <= p ->
  p + n + 128 <= Reusable.YG0f.ly_stk_hi ly -> 1 <= n -> Reusable.YG0f.ly_stk_hi ly <= 2 ^ 47 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.Prog.rng_asan.sh_al8_lo p)
    (B.Prog.rng_asan.sh_al8_hi p n - B.Prog.rng_asan.sh_al8_lo p).
Proof.
  intros ly S W mem md p n HAR H0 H1 H2 H3 H4.
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md
                (Reusable.YG0f.ly_stk_lo ly, Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) HAR
                ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz. unfold Reusable.YG0v.zero_shadow, Reusable.YG0v.shadow_of_addr in Hz.
  set (lo := Reusable.YG0f.ly_stk_lo ly) in *. set (hi := Reusable.YG0f.ly_stk_hi ly) in *.
  unfold B.ProgBridge.range_visible, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi,
    B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  rewrite P64. rewrite P47 in H4.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply (w4c13_vis_of_aview W mem).
  assert (Hi : 0 <= a - (Reusable.YG0f.SHADOW_OFF + lo / 8) < (hi - lo) / 8)
    by (unfold Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Hz _ Hi) as Hs. replace (Reusable.YG0f.SHADOW_OFF + lo / 8 + (a - (Reusable.YG0f.SHADOW_OFF + lo / 8)))
    with a in Hs by lia.
  rewrite Hs. discriminate.
Qed.

Lemma w4c13_aj_stk : forall cx own ly3 S3 W3 mem3 md3 k, w4c13_AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YM05.alloc_ceiling <= Reusable.YG0f.ly_stk_lo ly3 /\
  Reusable.YG0f.ly_stk_lo ly3 + Reusable.YCfn.LLVMF_STK <= ACtlCut.c_sp cx /\
  ACtlCut.c_sp cx <= Reusable.YG0f.ly_stk_hi ly3 /\ Reusable.YG0f.ly_stk_hi ly3 <= 2 ^ 47.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Elo, Ehi. split; [exact Hceil|]. split; [exact Hlo|]. split; [exact Hhi | exact H47].
Qed.

Lemma w4c13_wr_win : forall cx own ly3 S3 W3 mem3 md3 k a n, w4c13_AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a -> a + n <= ACtlCut.c_sp cx -> 0 <= n ->
  lib.Lib.Mem.wr_at B.Img0.rsegs mem3 a n.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k a n HJ Ha Hn Hn0.
  destruct (w4c13_aj_bits _ _ _ _ _ _ _ _ HJ) as (_ & Hceil & H47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hc.
  apply w4c13_wr_of_pres; [lia | lia |]. intros x Hx. exact (proj2 (Hwin x ltac:(lia))).
Qed.

Lemma w4c13_saved_len : forall cx, Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104.
Proof. intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. Qed.

(* ---- cut predicates across a register change and a memory change that keeps the bytes they read ---- *)
Lemma w4c13_frac_mem : forall cx fr sel (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, A + 40 <= x < A + 56 \/ A + 336 <= x < A + 344 \/ fr <= x < fr + 24 \/
     ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW \/ ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx \/
     fr + 4088 <= x < fr + 4096 -> w4c13_AGR m m' x) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' A0 HF H9 HA0 E2 E3 E4 E8 E9 E19 E26 K.
  destruct HF as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & (sh & Hsh & Hshl) & Hsaved & Q4088).
  pose proof (w4c13_spZ (ACtlCut.c_regs cx)) as Hcs. pose proof (w4c13_spZ regs) as Hsp. unfold ACtlCut.c_sp in *.
  assert (EA : A = A0).
  { apply (w4c13_rgv_inj regs 9); [exact Hr9 | exact H9 | unfold B.AsanRT.APPMEM_END in HAPP; lia | exact HA0]. }
  subst A0.
  exists A, sp.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact Hr4|].
  split; [exact (w4c13_rgv_move _ _ _ _ Hr8 E8)|]. split; [exact (w4c13_rgv_move _ _ _ _ Hr9 E9)|].
  split; [rewrite E3; exact Hr3|].
  split; [exact (w4c13_rgv_move _ _ _ _ Hr19 E19)|]. split; [exact (w4c13_rgv_move _ _ _ _ Hr26 E26)|].
  do 8 (split; [assumption|]).
  unfold ACtlCutP.q64 in *.
  split; [apply (w4c13_ba_keep m m' _ _ Q336); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply K; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ Q48); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply K; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ Q40); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply K; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ Qh1); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply K; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ Qh2); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply K; lia|].
  split.
  { exists sh. split; [|exact Hshl]. apply (w4c13_ba_keep m m' _ _ Hsh). rewrite Hshl.
    intros x Hx. apply K. right; right; right; left.
    rewrite Z2Nat.id in Hx by (unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES; lia). lia. }
  split; [apply (w4c13_ba_keep m m' _ _ Hsaved); rewrite w4c13_saved_len; intros x Hx; apply K; lia|].
  apply (w4c13_ba_keep m m' _ _ Q4088). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
Qed.

Lemma w4c13_lk_mem : forall cx fr j (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  (forall x, A <= x < A + 448 -> w4c13_AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> w4c13_AGR m m' x) ->
  (forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR m m' x) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> w4c13_AGR m m' x) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS KI HSTK.
  assert (K : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. apply (w4c13_spill_keep regs regs' m m' A off v H9 HA0 HA1 Ho E9); [|exact Hs].
    intros x Hx. apply KA. lia. }
  destruct HFLI as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & HKNa) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  split; [exact Hj|]. split; [apply K; [lia | exact S240]|].
  split.
  { unfold ACtlCutP.OURb in *. apply (w4c13_ba_keep m m' _ _ HOUR). rewrite ACtlCutP.SM.OUR_length.
    intros x Hx. apply KF. cbn in Hx. lia. }
  unfold ACtlCutP.FLI.
  split; [exact (w4c13_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [lia | assumption]|]).
  split; [exact (w4c13_addr_keep_sh m m' _ _ HA2624 KS)|].
  split; [exact HSTK|].
  split.
  { split; [exact (w4c13_addr_keep_sh m m' _ _ HRAD1 KS)|].
    split; [exact (w4c13_addr_keep_sh m m' _ _ HRAD2 KS) | exact (w4c13_addr_keep_sh m m' _ _ HRAD3 KS)]. }
  split.
  { split; [|exact (w4c13_addr_keep_sh m m' _ _ HKNa KS)].
    apply (w4c13_ba_keep m m' _ _ HKNb).
    assert (HKL : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by reflexivity. rewrite HKL.
    intros x Hx. apply KI. lia. }
  split; (apply K; [lia | assumption]).
Qed.

Lemma w4c13_fm_mem : forall cx j phi fr (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FM cx j phi fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  (forall x, A <= x < A + 448 -> w4c13_AGR m m' x) ->
  ACtlCutP.FM cx j phi fr regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' A (S184 & H24 & H22 & H25 & S312) H9 HA0 HA1 E9 E22 E24 E25 KA.
  split; [apply (w4c13_spill_keep regs regs' m m' A 184 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S184];
          intros x Hx; apply KA; lia|].
  split; [exact (w4c13_rgv_move _ _ _ _ H24 E24)|].
  split; [exact (w4c13_rgv_move _ _ _ _ H22 E22)|].
  split; [exact (w4c13_rgv_move _ _ _ _ H25 E25)|].
  apply (w4c13_spill_keep regs regs' m m' A 312 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S312].
  intros x Hx. apply KA. lia.
Qed.

Lemma w4c13_fs9_mem : forall cx j (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FS9 cx j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> w4c13_AGR m m' x) ->
  ACtlCutP.FS9 cx j regs' m'.
Proof.
  intros cx j regs regs' m m' A S248 H9 HA0 HA1 E9 KA. unfold ACtlCutP.FS9 in *.
  apply (w4c13_spill_keep regs regs' m m' A 248 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S248].
  intros x Hx. apply KA. lia.
Qed.

Lemma w4c13_fturn_mem : forall cx j phi (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FTURN cx j phi regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> w4c13_AGR m m' x) ->
  (forall x, phi <= x < phi + ACtlCutP.flen cx j -> w4c13_AGR m m' x) ->
  ACtlCutP.FTURN cx j phi regs' m'.
Proof.
  intros cx j phi regs regs' m m' A (S224 & S232 & Hph & Hlen) H9 HA0 HA1 E9 KA KP.
  split; [apply (w4c13_spill_keep regs regs' m m' A 224 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S224];
          intros x Hx; apply KA; lia|].
  split; [apply (w4c13_spill_keep regs regs' m m' A 232 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S232];
          intros x Hx; apply KA; lia|].
  split; [|exact Hlen].
  apply (w4c13_ba_keep m m' _ _ Hph). intros x Hx. apply KP. unfold ACtlCutP.flen. lia.
Qed.

Lemma w4c13_fsj_mem : forall cx fr j (regs regs' : bvmap 5 word) m m',
  ACtlCutP.FSj cx fr j regs m ->
  (forall x, fr + 2880 <= x < fr + 2920 -> w4c13_AGR m m' x) ->
  (forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR m m' x) ->
  ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' (Hhave & Hn & Hbody & Had & HFI) KF KS.
  pose proof (w4c13_fst_body_len (ACtlCut.c_in cx) j) as HL.
  unfold ACtlCutP.FSj, ACtlCutP.FSb.
  split; [unfold ACtlCutP.u32 in *; apply (w4c13_ba_keep m m' _ _ Hhave); rewrite lib.Lib.Mem.length_le4;
          intros x Hx; apply KF; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hn); cbn [length]; intros x Hx; apply KF; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ Hbody); intros x Hx; apply KF; lia|].
  split; [exact (w4c13_addr_keep_sh m m' _ _ Had KS) | exact HFI].
Qed.

Lemma w4c13_rec_inv_mem : forall cx j phi A kp m m',
  ACtlCutP.rec_inv cx j phi A kp m ->
  (forall x, phi <= x < phi + 50 -> w4c13_AGR m m' x) ->
  (forall x, A + 248 <= x < A + 320 -> w4c13_AGR m m' x) ->
  (forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR m m' x) ->
  (forall x, kp + 20 <= x < kp + 22 -> w4c13_AGR m m' x) ->
  ACtlCutP.rec_inv cx j phi A kp m'.
Proof.
  intros cx j phi A kp m m' (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2) KP KA KS Kkp.
  assert (SH : forall t, 14 <= t <= 17 -> w4c13_AGR m m' (Z.shiftr (phi + t) 3 + B.ACtlK.ASAN_K)).
  { intros t Ht. apply KS. pose proof (Hpap (phi + t) ltac:(lia)) as Hap.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in Hap.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold B.ACtlK.ASAN_K, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG.
    pose proof (Z.div_pos (phi + t) 8 ltac:(lia) ltac:(lia)).
    assert ((phi + t) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  unfold ACtlCutP.rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold ACtlCutP.q64 in *; apply (w4c13_ba_keep m m' _ _ H312); rewrite lib.Lib.Mem.length_le8;
          intros x Hx; apply KA; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ H18); intros x Hx; apply KP; unfold ACtlCutP.SM.t_blk in Hx;
          pose proof (w4c13_bsl_len_le (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) 18 32) as BL;
          change (Z.to_nat 32) with 32%nat in BL; lia|].
  split; [apply (w4c13_ba_keep m m' _ _ H34); intros x Hx; apply KP;
          pose proof (w4c13_bsl_len_le (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) 34 6) as BL;
          change (Z.to_nat 6) with 6%nat in BL; lia|].
  exists field16, v14, v15, v16, v17.
  split; [unfold ACtlCutP.q64 in *; apply (w4c13_ba_keep m m' _ _ H248); rewrite lib.Lib.Mem.length_le8;
          intros x Hx; apply KA; lia|].
  split; [unfold ACtlCutP.u16 in *; apply (w4c13_ba_keep m m' _ _ Hf16); rewrite lib.Lib.Mem.length_le2;
          intros x Hx; apply Kkp; lia|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hb14); cbn [length]; intros x Hx; apply KP; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hb15); cbn [length]; intros x Hx; apply KP; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hb16); cbn [length]; intros x Hx; apply KP; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hb17); cbn [length]; intros x Hx; apply KP; lia|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hs14); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 14) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 14); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hs15); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 15) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 15); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hs16); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 16) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 16); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c13_ba_keep m m' _ _ Hs17); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 17) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 17); lia|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* FRB (kp = fr + 176) across a run that keeps the spill base and sp, with the two 6-byte operands at FLI's
   [A + 112] = fr + 186 and [A + 96] = fr + 180 (Seg/F13.v seg_F13's FRBA step). *)
Lemma w4c13_frb_mem : forall cx j fr phi A (regs regs' : bvmap 5 word) m m',
  ACtlCutP.FRB cx j fr phi A (fr + 176) regs m ->
  ACtlCutP.q64 m (A + 112) (fr + 186) -> ACtlCutP.q64 m (A + 96) (fr + 180) -> 0 <= fr -> fr + 4096 <= 2 ^ 47 ->
  Reusable.YG0d.spZ regs' = Reusable.YG0d.spZ regs ->
  (forall x, A + 96 <= x < A + 320 -> w4c13_AGR m m' x) ->
  (forall x, fr + 176 <= x < fr + 200 -> w4c13_AGR m m' x) ->
  (50 <= ACtlCutP.flen cx j -> forall x, phi <= x < phi + 50 -> w4c13_AGR m m' x) ->
  (forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR m m' x) ->
  ACtlCutP.FRB cx j fr phi A (fr + 176) regs' m'.
Proof.
  intros cx j fr phi A regs regs' m m' HFRB Q112 Q96 Hfr0 Hfr1 Esp KA KF KP KS.
  destruct HFRB as (Hw112 & (w272 & Hq272 & Hw272b & Hw272t & Hw272f) & Hkp112 & HkpBC & Hkp2688 &
    HphiG & H8819).
  unfold ACtlCutP.FRB. rewrite Esp.
  split; [exact Hw112|].
  split.
  { exists w272. split; [|exact (conj Hw272b (conj Hw272t Hw272f))].
    unfold ACtlCutP.q64 in *. apply (w4c13_ba_keep m m' _ _ Hq272). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply KA. lia. }
  split; [exact Hkp112|]. split; [exact HkpBC|]. split; [exact Hkp2688|]. split; [exact HphiG|].
  intros H8.
  destruct (H8819 H8) as (HRI &
    (L & ls & rs & QL & HBL1 & HLl & HBR1 & HLr & Hmm1 & HAL1 & Hap6 & Hap7 & HLBC & HLA & HL2688) &
    (L2 & ls2 & rs2 & QL2 & HBL2 & HLl2 & HBR2 & HLr2 & Hmm2 & HAL2 & Hap62 & Hap72 & HL2BC & HL2A & HL22688)).
  pose proof HRI as (_ & _ & H50 & _).
  assert (EL : L = fr + 186).
  { apply (w4c13_q64_det m (A + 112) L (fr + 186) QL Q112);
      [destruct HAL1 as (HL0 & _ & HLe & _); unfold B.AsanRT.APPMEM_END in *; lia | lia]. }
  assert (EL2 : L2 = fr + 180).
  { apply (w4c13_q64_det m (A + 96) L2 (fr + 180) QL2 Q96);
      [destruct HAL2 as (HL0 & _ & HLe & _); unfold B.AsanRT.APPMEM_END in *; lia | lia]. }
  subst L L2.
  split.
  { apply (w4c13_rec_inv_mem cx j phi A (fr + 176) m m' HRI).
    - exact (KP H50).
    - intros x Hx. apply KA. lia.
    - exact KS.
    - intros x Hx. apply KF. lia. }
  split.
  { exists (fr + 186), ls, rs.
    split; [unfold ACtlCutP.q64 in *; apply (w4c13_ba_keep m m' _ _ QL); rewrite lib.Lib.Mem.length_le8;
            intros x Hx; apply KA; lia|].
    split; [apply (w4c13_ba_keep m m' _ _ HBL1); rewrite HLl; intros x Hx; apply KF; lia|].
    split; [exact HLl|].
    split; [apply (w4c13_ba_keep m m' _ _ HBR1); rewrite HLr; intros x Hx; apply (KP H50); lia|].
    split; [exact HLr|]. split; [exact Hmm1|].
    split; [exact (w4c13_addr_keep_sh m m' _ _ HAL1 KS)|].
    split; [exact Hap6|]. split; [exact Hap7|]. split; [exact HLBC|]. split; [exact HLA | exact HL2688]. }
  { exists (fr + 180), ls2, rs2.
    split; [unfold ACtlCutP.q64 in *; apply (w4c13_ba_keep m m' _ _ QL2); rewrite lib.Lib.Mem.length_le8;
            intros x Hx; apply KA; lia|].
    split; [apply (w4c13_ba_keep m m' _ _ HBL2); rewrite HLl2; intros x Hx; apply KF; lia|].
    split; [exact HLl2|].
    split; [apply (w4c13_ba_keep m m' _ _ HBR2); rewrite HLr2; intros x Hx; apply (KP H50); lia|].
    split; [exact HLr2|]. split; [exact Hmm2|].
    split; [exact (w4c13_addr_keep_sh m m' _ _ HAL2 KS)|].
    split; [exact Hap62|]. split; [exact Hap72|]. split; [exact HL2BC|]. split; [exact HL2A | exact HL22688]. }
Qed.


(* the run's stack pointer `bv_unsigned (reg_get regs 2)` (from Regs6ss.mkR_of) as the cut's sp *)
Local Ltac w4c13_sp sp Hspz :=
  repeat match goal with |- context [bv_unsigned ?s] =>
    let E := fresh "Esp" in assert (E : bv_unsigned s = sp) by exact Hspz; rewrite E; clear E end.
Local Ltac w4c13_sp_in H sp Hspz :=
  repeat match type of H with context [bv_unsigned ?s] =>
    let E := fresh "Esp" in assert (E : bv_unsigned s = sp) by exact Hspz; rewrite E in H; clear E end.

(* ---------------------------------------------------------------------------------------------------------
   seg_F16 STAGE KIT (prefix w4c16_).  Copies, renamed, of the image-B glue kit of the sibling lane
   (lib/B/ACtlW4b.v w4b_* and w4b11_*: visibility of heap / frame / image ranges, memory transports across
   a munch, ctl_rt across a write that misses the image and the shadow, the journal across a stack-window range plus
   an owned-frame range), over this file's segs / LAWS / segs_low; then the S_F16-specific facts. *)

(* A byte the view reads is visible: a hidden byte lies in no segment (w_Hoff), so the view reads None there
   (lib/A/ProgWorldVisFrame.v vis_of_aview, over this file's segs). *)
Lemma w4c16_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

(* heap_vis (lib/A/ProgWorldVisHeap.v): a sub-range of a live heap block is visible. *)
Lemma w4c16_heap_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
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
Lemma w4c16_heap_sh1 : forall ly S (W : Reusable.YA0n.world segs) mem md p n x,
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
  apply (w4c16_vis_of_aview W mem). apply Hh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)) as M1.
  pose proof (Z.div_le_mono x (p + Reusable.YG00.req_size n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
  Z.div_mod_to_equations. lia.
Qed.

(* A carried byte list survives a munch that misses each of its bytes. *)
Lemma w4c16_bytes_at_munch : forall W m m' a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> lib.Lib.Frame.outside W (a + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) Hm Ho. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold lib.Lib.Mem.mrd. rewrite (Hm (lib.Lib.Mem.wa (a + Z.of_nat i))); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by lia. apply Ho. lia.
Qed.

(* The segment bytes of image B lie below 0x5fe000 (ProgBridge.rsegs_spans). *)
Lemma w4c16_find_segment_low : forall x seg, find_segment B.Img0.rsegs x 1 = Some seg -> x < 0x5fe000.
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

(* ctl_rt_C (route (C): the image cells, the cut's own and the image's shadow, the read-only image bytes) survives a
   munch that misses every address below HIGHMEM_BEG (a write inside the machine stack, above alloc_ceiling). *)
Lemma w4c16_ctl_rt_munch : forall ly S W m m',
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch W m m' ->
  (forall x, 0 <= x < B.AsanRT.HIGHMEM_BEG -> lib.Lib.Frame.outside W x) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S W m m' (Hc & Hs & Himg & Hr) Hm Ho.
  assert (Hb : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a + Z.of_nat (length bs) <= 0x5fe000 ->
                 lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H Hl. apply (w4c16_bytes_at_munch W m m' a bs H Hm). intros i Hi.
    pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ H) as Hbd.
    apply Ho. unfold B.AsanRT.HIGHMEM_BEG. lia. }
  assert (Hx : forall x : word, bv_unsigned x < B.AsanRT.HIGHMEM_BEG -> m' x = m x).
  { intros x Hx. apply Hm. apply Ho. pose proof (bv_unsigned_in_range 64 x) as [Hx0 _]. lia. }
  assert (SH : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').
  { unfold B.ShadowRwOn.shadow_rw_on. intros P H a Hp Ha.
    assert (Ea : m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)).
    { apply Hx. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
        B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Ha.
      rewrite lib.Lib.Mem.wa_unsigned by lia. unfold B.AsanRT.HIGHMEM_BEG. lia. }
    unfold wview, lib.Lib.Mem.mrd. rewrite Ea. exact (H a Hp Ha). }
  split; [|split; [exact (SH _ Hs)|split; [exact (SH _ Himg)|]]].
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
      pose proof (w4c16_find_segment_low _ _ Ef). unfold B.AsanRT.HIGHMEM_BEG. lia. }
    unfold lib.Lib.Mem.mrd. rewrite Ea. exact (Hr a Ha).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   memory transports across the callee write sets of S_F16 (the stack windows and the identity record), the record
   length of the turn model, the shadow facts, and the journal across the two written ranges. *)

(* A sub-list of a byte list (Seg/F11.v f11_nth_sub / f11_sub, over lib/Lib). *)
Lemma w4c16_nth_sub : forall (l : list byte) k n i, (i < n)%nat ->
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

Lemma w4c16_sub : forall m a (bs : list byte) k n, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (k + n <= length bs)%nat -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite w4c16_nth_sub by exact Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

(* The shadow byte of an application byte is a shadow address. *)
Lemma w4c16_sh_in : forall a, B.AsanRT.app_mem a -> B.AsanRT.in_shadow (Z.shiftr a 3 + B.AsanRT.ASAN_K).
Proof.
  intros a Ha. assert (Ha0 : 0 <= a)
    by (unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in Ha; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. exact (B.AsanRTFacts.shadow_of_app a Ha).
Qed.

(* Cells: the bytes of a CB cell; the cell of a writable byte range (Seg/F11.v f11_cb_bytes / f11_cb_rw /
   f11_wr_of_stk / f11_stk_tr / f11_present, over lib/Lib). *)
Lemma w4c16_cb_bytes : forall m a n bs,
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros m a n bs [[_ H] _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

Lemma w4c16_cb_rw : forall m a n bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> length bs = n ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m a (Z.of_nat n) -> lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes].
    rewrite app_nil_r. exact Hb.
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma w4c16_wr_of_stk : forall m m' lo hi a n, lib.Lib.Frame.stk B.Img0.rsegs m lo hi ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> lo <= a -> a + n <= hi -> 0 <= n -> lib.Lib.Mem.wr_at B.Img0.rsegs m' a n.
Proof.
  intros m m' lo hi a n (H0 & H1 & H) WM Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. apply WM. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

Lemma w4c16_stk_tr : forall W m m' lo hi,
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

Lemma w4c16_present : forall m a bs q, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
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
Lemma w4c16_in_img : forall x, 0x10000 <= x < 0x5fe000 -> Reusable.YG0d.in_img segs x.
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
Lemma w4c16_fseg_img : forall x seg, find_segment B.Img0.rsegs x 1 = Some seg -> Reusable.YG0d.in_img segs x.
Proof.
  intros x seg Hf.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.kb_find_segment B.Img0.rsegs x 1 seg Hf)
    as (Hin & Hb & He).
  exists seg. split; [exact Hin | lia].
Qed.

(* A byte list carried outside a munch's write set survives it (range form of w4c16_bytes_at_munch). *)
Lemma w4c16_bmv : forall W m m' a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Frame.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof. intros W m m' a bs H Hm Ho. apply (w4c16_bytes_at_munch W m m' a bs H Hm). intros i Hi. apply Ho. lia. Qed.

Lemma w4c16_qmv : forall W m m' a v, ACtlCutP.q64 m a v -> lib.Lib.Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> lib.Lib.Frame.outside W x) -> ACtlCutP.q64 m' a v.
Proof.
  intros W m m' a v H Hm Ho. unfold ACtlCutP.q64 in *. apply (w4c16_bmv W m m' a _ H Hm).
  rewrite lib.Lib.Mem.length_le8. exact Ho.
Qed.

(* A spill word sits at the spill base A that register 9 holds (A < 2^63, so the spill's own base is A). *)
Lemma w4c16_spill_q : forall (regs : bvmap 5 word) m off v A,
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
Lemma w4c16_spmv : forall W (regs R : bvmap 5 word) m m' off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 63 -> 0 <= off <= 440 ->
  ACtlCut.rgv R 9 A -> lib.Lib.Frame.munch W m m' ->
  (forall x, A <= x < A + 448 -> lib.Lib.Frame.outside W x) -> ACtlCutP.spill R m' off v.
Proof.
  intros W regs R m m' off v A Hs HA H0 H1 Hoff HR Hm Ho. exists A. split; [exact HR|].
  apply (w4c16_qmv W m m' _ _ (w4c16_spill_q regs m off v A Hs HA H0 H1 Hoff) Hm).
  intros x Hx. apply Ho. lia.
Qed.

(* The shadow bytes survive a munch that misses every shadow address; so does every addressable fact. *)
Lemma w4c16_meta : forall W m m', lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) -> B.AsanRTFacts.meta_kept m m'.
Proof.
  intros W m m' Hm Ho a Ha. unfold lib.Lib.Mem.mrd.
  destruct (B.AsanRTFacts.in_shadow_range a Ha) as [R0 R1].
  rewrite (Hm (lib.Lib.Mem.wa a)); [reflexivity|]. rewrite lib.Lib.Mem.wa_unsigned by lia. exact (Ho a Ha).
Qed.

Lemma w4c16_amv : forall W m m' p n, B.AsanRT.addressable m p n -> lib.Lib.Frame.munch W m m' ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) -> B.AsanRT.addressable m' p n.
Proof. intros W m m' p n H Hm Ho. exact (B.AsanRTFacts.addressable_kept m m' p n H (w4c16_meta W m m' Hm Ho)). Qed.

(* ctl_rt_C survives a munch that misses every image byte and every shadow byte (w4c16_ctl_rt_munch, with the image
   and the shadow in place of the whole range below HIGHMEM_BEG: S_F16 also writes an owned-frame range). *)
Lemma w4c16_rt_mv : forall ly S W m m',
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch W m m' ->
  (forall x, Reusable.YG0d.in_img segs x \/ B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S W m m' (Hc & Hs & Himg & Hr) Hm Ho.
  assert (Hb : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> 0x10000 <= a ->
                 a + Z.of_nat (length bs) <= 0x5fe000 -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H Hl0 Hl. apply (w4c16_bmv W m m' a bs H Hm). intros x Hx.
    apply Ho. left. apply w4c16_in_img. lia. }
  assert (Hx : forall x : word, Reusable.YG0d.in_img segs (bv_unsigned x) \/ B.AsanRT.in_shadow (bv_unsigned x) ->
                 m' x = m x).
  { intros x Hx. apply Hm. apply Ho. exact Hx. }
  assert (SH : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').
  { unfold B.ShadowRwOn.shadow_rw_on. intros P H a Hp Ha.
    assert (Ea : m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)).
    { apply Hx. right. destruct (B.AsanRTFacts.in_shadow_range a Ha) as [R0 R1].
      rewrite lib.Lib.Mem.wa_unsigned by lia. exact Ha. }
    unfold wview, lib.Lib.Mem.mrd. rewrite Ea. exact (H a Hp Ha). }
  split; [|split; [exact (SH _ Hs)|split; [exact (SH _ Himg)|]]].
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
      exact (w4c16_fseg_img _ _ Ef). }
    unfold lib.Lib.Mem.mrd. rewrite Ea. exact (Hr a Ha).
Qed.

Lemma w4c16_ID_len : forall inp j, length (B.Prog.SlotModel.t_ID inp j) = 38%nat.
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

(* Visibility: the shadow span of a sub-range of a live heap block (AR_shadow_law's shadow_hull_vis), a range of a
   live frame's shadow (AR_frames_law), and an image range (ProgBridge.img_vis_W). *)
Lemma w4c16_heap_shr : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
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
  apply (w4c16_vis_of_aview W mem). apply Hh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  pose proof (Z.div_le_mono p lo 8 ltac:(lia) ltac:(lia)) as M1.
  pose proof (Z.div_le_mono (lo + len - 1) (p + Reusable.YG00.req_size n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4c16_frame_shr : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos o len,
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

Lemma w4c16_img_rng : forall (W : Reusable.YA0n.world segs) lo len,
  0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 ->
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W lo len H0 H1 H2. apply B.ProgBridge.rng_of_visible.
  apply (B.ProgBridge.range_visible_sub _ B.Prog.ImgBounds.IMG_LO (B.Prog.ImgBounds.IMG_HI - B.Prog.ImgBounds.IMG_LO));
    [exact (B.ProgBridge.img_vis_W W) | | | ]; unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia.
Qed.

(* The journal across a raw-memory write confined to a sub-range [lo, hi) of its stack window and a range
   [flo, fhi) of an owned frame (YCbq.ajournal_exec with Wr = the two ranges; w4c16_aj_munch with a second range). *)
Lemma w4c16_aj2 : forall STK sp0 (FPj : list (Z * Z)) ly S (W : Reusable.YA0n.world segs) mem md own lyc Sc
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
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k
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
Lemma w4c16_raw : forall m (x : word) b, lib.Lib.Mem.mrd B.Img0.rsegs m x = Some b ->
  ~ Reusable.YG0d.in_img segs (bv_unsigned x) -> m x = Some b.
Proof.
  intros m x b H Hn. unfold lib.Lib.Mem.mrd in H. destruct (m x) as [b'|] eqn:E; [exact H|].
  exfalso. apply Hn. unfold lib.Lib.PropExec.seg_rom, memory_read in H.
  destruct (find_segment B.Img0.rsegs (bv_unsigned x) (Z.of_N 1)) as [seg|] eqn:Ef; [|discriminate H].
  exact (w4c16_fseg_img _ _ Ef).
Qed.

(* A byte-backed range outside the image is present in the raw memory. *)
Lemma w4c16_some : forall m lo hi (x : word), lib.Lib.Frame.stk B.Img0.rsegs m lo hi ->
  lo <= bv_unsigned x < hi -> ~ Reusable.YG0d.in_img segs (bv_unsigned x) -> m x <> None.
Proof.
  intros m lo hi x (_ & _ & H) Hx Hn. destruct (H _ Hx) as [_ (b & Hb)].
  unfold lib.Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
  rewrite (w4c16_raw m x b Hb Hn). discriminate.
Qed.

(* Present bytes are byte-backed (the journal's stack window gives stk). *)
Lemma w4c16_stk_pres : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Hp a Ha) as [_ (b & Hb)]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* The class-6 frame's shadow bytes are shadow addresses (the frame lies in low or high application memory). *)
Lemma w4c16_sfr_shadow : forall fr x, 4096 <= fr ->
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
Lemma w4c16_FLI_mv : forall W cx fr (regs R : bvmap 5 word) m m',
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
    (conj (SP 304 _ _ S304) (conj (w4c16_amv W m m' _ _ Had Hm HOS) (conj Hstk
    (conj (conj (w4c16_amv W m m' _ _ R1 Hm HOS) (conj (w4c16_amv W m m' _ _ R2 Hm HOS)
                                                    (w4c16_amv W m m' _ _ R3 Hm HOS)))
    (conj (conj _ (w4c16_amv W m m' _ _ K2 Hm HOS)) (conj (SP 168 _ _ S168b) (SP 88 _ _ S88)))))))))))))))))))))))))));
    try lia.
  apply (w4c16_bmv W m m' _ _ K1 Hm). intros x Hx. apply HOI. apply w4c16_in_img.
  change (Z.of_nat (length ACtlCutP.KNA.kind_name_bytes)) with 112 in Hx.
  unfold ACtlCutP.KNA.KIND_NAME in Hx. lia.
Qed.

Lemma w4c16_LK_mv : forall W cx fr j (regs R : bvmap 5 word) m m',
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
  - unfold ACtlCutP.OURb in *. apply (w4c16_bmv W m m' _ _ HOUR Hm).
    rewrite B.Prog.SlotModel.OUR_length. intros x Hx. apply HOO. lia.
  - exact (w4c16_FLI_mv W cx fr regs R m m' HFLI SP E27 Hm HOS HOI Hstk).
Qed.

(* FRAC across a munch that keeps its memory words: the spill words at [A, c_sp), the frame header / entry /
   trailer words, and the frame's shadow; registers 2 3 4 8 9 19 26 kept. *)
Lemma w4c16_frac_mv : forall W cx fr sel (regs R : bvmap 5 word) m m' A0,
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
  pose proof (w4c_frac_move cx fr sel regs R m H E2 E3 E4 E8 E9 E19 E26) as H'.
  destruct H' as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & (sh & Hsh & Hshl) & Hsv & Q4088).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr R 2)) as [Hb0 _]. exact Hb0. }
  assert (EA : A = A0).
  { apply w4c_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | exact HA0r |].
    unfold ACtlCut.rgv in Hr9, HA0. rewrite <- Hr9, <- HA0. exact E9. }
  subst A.
  exists A0, sp.
  repeat (split; [assumption|]).
  split; [apply (w4c16_qmv W m m' _ _ Q336 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4c16_qmv W m m' _ _ Q48 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4c16_qmv W m m' _ _ Q40 Hm); intros x Hx; apply HOA; lia|].
  split; [apply (w4c16_qmv W m m' _ _ Qhdr Hm); intros x Hx; apply HOF; lia|].
  split; [apply (w4c16_qmv W m m' _ _ Q16 Hm); intros x Hx; apply HOF; lia|].
  split; [exists sh; split; [apply (w4c16_bmv W m m' _ _ Hsh Hm); rewrite Hshl; intros x Hx; apply HOS;
          unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in *; lia | exact Hshl]|].
  split.
  - apply (w4c16_bmv W m m' _ _ Hsv Hm). intros x Hx. apply HOA.
    unfold ACtlCutP.saved_bytes in Hx. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hx. cbn in Hx. lia.
  - apply (w4c16_qmv W m m' _ _ Q4088 Hm); intros x Hx; apply HOF; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   seg_F16 kit (prefix w4c16_): the joined_byte model read (copies of lib/B/Prog/joined_byte.v jb_bytes_nth /
   jb_byte_lit / jb_lit8 / jb_model_range / joined_byte_model_rd, never cited), the byte / record facts of the ingest
   (copies of Seg/F16.v f16_zxb8 / ba_det / t_ID_S_rf / t_IDr_length), the place of joined_byte's address, and the
   record invariant / FSj across a munch. *)
Lemma w4c16_jb_nth : forall m a (bs : list byte) k, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  0 <= k < Z.of_nat (length bs) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + k) [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k (H0 & Hl & H) Hk. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
  replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
  rewrite H by lia. apply nth_error_nth'. lia.
Qed.

Lemma w4c16_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact (bv_unsigned_in_range 8 b).
Qed.

Lemma w4c16_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma w4c16_jb_range : forall s g i, 0 <= B.Prog.SlotModel.joined_byte s g i < 256.
Proof.
  intros s g i. unfold B.Prog.SlotModel.joined_byte, Prog.RcFrag.bat.
  destruct (i <? B.Prog.SlotModel.fs_n s);
    match goal with |- 0 <= bv_unsigned ?b < 256 =>
      pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; exact R end.
Qed.

Lemma w4c16_jb_rd : forall m fr phi (s : B.Prog.SlotModel.fstate) (g : list byte) i,
  (i = 9 \/ i = 10) -> 0 <= B.Prog.SlotModel.fs_n s ->
  Z.of_nat (length (B.Prog.SlotModel.fs_body s)) = B.Prog.SlotModel.fs_n s -> 50 <= Z.of_nat (length g) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (fr + 2885) (B.Prog.SlotModel.fs_body s) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m phi g ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (joined_byte_c.jb_addr (fr + 2880) (phi + 18) (B.Prog.SlotModel.fs_n s) i)
    [Z_to_bv 8 (B.Prog.SlotModel.joined_byte s g i)].
Proof.
  intros m fr phi s g i Hi Hn Hl Hg HBd HG.
  unfold joined_byte_c.jb_addr, B.Prog.SlotModel.joined_byte, Prog.RcFrag.bat.
  destruct (Z.ltb_spec i (B.Prog.SlotModel.fs_n s)) as [E|E].
  - rewrite w4c16_byte_lit. replace (fr + 2880 + 5 + i) with (fr + 2885 + i) by lia.
    apply w4c16_jb_nth; [exact HBd | lia].
  - rewrite w4c16_byte_lit.
    replace (phi + 18 + (9 + i - B.Prog.SlotModel.fs_n s)) with (phi + (27 + i - B.Prog.SlotModel.fs_n s)) by lia.
    apply w4c16_jb_nth; [exact HG | lia].
Qed.

(* joined_byte's address at the two calls: a byte of `first`'s body or of the block's bytes 27 .. 36. *)
Lemma w4c16_jb_place : forall fr phi n i, (i = 9 \/ i = 10) -> 1 <= n ->
  fr + 2885 <= joined_byte_c.jb_addr (fr + 2880) (phi + 18) n i < fr + 2896 \/
  phi + 27 <= joined_byte_c.jb_addr (fr + 2880) (phi + 18) n i < phi + 37.
Proof.
  intros fr phi n i Hi Hn. unfold joined_byte_c.jb_addr.
  destruct (Z.ltb_spec i n); [left | right]; lia.
Qed.

Lemma w4c16_zxb8 : forall v, 0 <= v < 256 -> lib.Lib.Mem.zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold lib.Lib.Mem.zxb. f_equal. apply w4c16_lit8. exact Hv. Qed.

Lemma w4c16_ba_det : forall m a bs cs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a cs -> length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & Hb) (_ & _ & Hc) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (Hb i Hi), <- (Hc i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None cs i) ltac:(lia)). reflexivity.
Qed.

Lemma w4c16_t_ID_S_rf : forall inp j, B.Prog.SlotModel.t_rf inp j = 1 ->
  B.Prog.SlotModel.t_ID inp (S j) =
  snd (Prog.RcIdentModel.ING (B.Prog.SlotModel.t_IDr inp j)
         (Prog.RcFrag.fg_addr (B.Prog.SlotModel.t_FG inp j) (B.Prog.SlotModel.t_g inp j))
         (B.Prog.SlotModel.f_pl (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_FG inp j)
            (B.Prog.SlotModel.t_g inp j))).
Proof.
  intros inp j H. unfold B.Prog.SlotModel.t_rf, B.Prog.SlotModel.t_FG in H.
  unfold B.Prog.SlotModel.t_ID, B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.t_FG.
  rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn, B.Prog.SlotModel.fg_id. cbv zeta.
  rewrite H, Z.eqb_refl.
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j)); reflexivity.
Qed.

Lemma w4c16_IDr_len : forall inp j, length (B.Prog.SlotModel.t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply Prog.RcIdentModel.ING_length; apply w4c16_ID_len | apply w4c16_ID_len].
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma w4c16_addr_at : forall m p n x n', B.AsanRT.addressable m p n -> p <= x -> 0 <= n' -> x + n' <= p + n ->
  B.AsanRT.addressable m x n'.
Proof.
  intros m p n x n' H H1 H2 H3. replace x with (p + (x - p)) by lia.
  apply (B.AsanRTFacts.addressable_sub m p n); [exact H | lia | lia | lia].
Qed.

(* The shadow span of a range of the owned class-6 frame, and the shadow byte of one frame byte / one byte of a live
   heap block, are visible (w4c16_frame_shr / w4c16_heap_shr at the run's own offsets). *)
Lemma w4c16_frame_shspan : forall ly S (W : Reusable.YA0n.world segs) mem md pos fr lo len,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 32 = 0 -> fr <= lo -> lo + len <= fr + 4096 -> 1 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (lo / 8 + B.AsanRT.ASAN_K) ((lo + len - 1) / 8 - lo / 8 + 1).
Proof.
  intros ly S W mem md pos fr lo len HAR Hin Efr Hfr Hlo Hhi Hlen.
  pose proof (Z.div_le_mono fr lo 8 ltac:(lia) ltac:(lia)) as M1.
  pose proof (Z.div_le_mono lo (lo + len - 1) 8 ltac:(lia) ltac:(lia)) as M2.
  pose proof (Z.div_le_mono (lo + len - 1) (fr + 4095) 8 ltac:(lia) ltac:(lia)) as M3.
  assert (E4095 : (fr + 4095) / 8 = fr / 8 + 511).
  { replace (fr + 4095) with (7 + (fr / 8 + 511) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. reflexivity. }
  pose proof (w4c16_frame_shr ly S W mem md 6 pos (lo / 8 - fr / 8) ((lo + len - 1) / 8 - lo / 8 + 1) HAR Hin
                ltac:(lia) ltac:(lia) ltac:(change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia)) as V.
  rewrite Efr in V. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in V.
  replace (lo / 8 + B.AsanRT.ASAN_K) with (0x7fff8000 + fr / 8 + (lo / 8 - fr / 8))
    by (unfold B.AsanRT.ASAN_K; lia).
  exact V.
Qed.

Lemma w4c16_frame_sa1 : forall ly S (W : Reusable.YA0n.world segs) mem md pos fr x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 32 = 0 -> fr <= x < fr + 4096 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr x) 1.
Proof.
  intros ly S W mem md pos fr x HAR Hin Efr Hfr Hx.
  pose proof (w4c16_frame_shspan ly S W mem md pos fr x 1 HAR Hin Efr Hfr ltac:(lia) ltac:(lia) ltac:(lia)) as V.
  replace ((x + 1 - 1) / 8 - x / 8 + 1) with 1 in V by (replace (x + 1 - 1) with x by lia; lia).
  exact V.
Qed.

Lemma w4c16_heap_sa1 : forall ly S (W : Reusable.YA0n.world segs) mem md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= x < p + Reusable.YG00.req_size n ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr x) 1.
Proof.
  intros ly S W mem md p n x HAR Hin Hx.
  pose proof (w4c16_heap_shr ly S W mem md p n x 1 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)) as V.
  replace ((x + 1 - 1) / 8 - x / 8 + 1) with 1 in V by (replace (x + 1 - 1) with x by lia; lia).
  exact V.
Qed.

(* The record invariant across a write set that misses Phi's first 50 bytes, the spill area, the record pointer's
   u16 and the shadow map (copy of Seg/F16.v f16_rec_inv_keep over this file's predicates). *)
Lemma w4c16_rec_inv_mv : forall cx j phi A kp m m' W,
  ACtlCutP.rec_inv cx j phi A kp m -> lib.Lib.Frame.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> lib.Lib.Frame.outside W x) ->
  (forall x, A + 248 <= x < A + 320 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  (forall x, kp + 20 <= x < kp + 22 -> lib.Lib.Frame.outside W x) ->
  ACtlCutP.rec_inv cx j phi A kp m'.
Proof.
  intros cx j phi A kp m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWsh OWkp.
  assert (SH : forall t, 14 <= t <= 17 -> lib.Lib.Frame.outside W (Z.shiftr (phi + t) 3 + B.ACtlK.ASAN_K)).
  { intros t Ht. apply OWsh. apply w4c16_sh_in. apply Hpap. lia. }
  assert (BL : forall (bs : list byte) k n, (length (Prog.RcFrag.bsl bs k n) <= Z.to_nat n)%nat).
  { intros bs k n. unfold Prog.RcFrag.bsl. rewrite length_firstn. apply Nat.le_min_l. }
  unfold ACtlCutP.rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [apply (w4c16_qmv W m m' _ _ H312 MU); intros x Hx; apply OWspill; lia|].
  split; [apply (w4c16_bmv W m m' _ _ H18 MU); intros x Hx; apply OWphi; unfold B.Prog.SlotModel.t_blk in Hx;
          pose proof (BL (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 18 32) as BL1;
          change (Z.to_nat 32) with 32%nat in BL1; lia|].
  split; [apply (w4c16_bmv W m m' _ _ H34 MU); intros x Hx; apply OWphi;
          pose proof (BL (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 34 6) as BL1;
          change (Z.to_nat 6) with 6%nat in BL1; lia|].
  exists field16, v14, v15, v16, v17.
  split; [apply (w4c16_qmv W m m' _ _ H248 MU); intros x Hx; apply OWspill; lia|].
  split; [unfold ACtlCutP.u16 in *; apply (w4c16_bmv W m m' _ _ Hf16 MU);
          rewrite lib.Lib.Mem.length_le2; intros x Hx; apply OWkp; lia|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hb14 MU); cbn [length]; intros x Hx; apply OWphi; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hb15 MU); cbn [length]; intros x Hx; apply OWphi; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hb16 MU); cbn [length]; intros x Hx; apply OWphi; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hb17 MU); cbn [length]; intros x Hx; apply OWphi; lia|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hs14 MU); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 14) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 14); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hs15 MU); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 15) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 15); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hs16 MU); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 16) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 16); lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hs17 MU); cbn [length]; intros x Hx;
          replace x with (Z.shiftr (phi + 17) 3 + B.ACtlK.ASAN_K) by lia; apply (SH 17); lia|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* FSj (the local `first` at fr + 2880, 40 bytes) across a munch that misses those bytes and the shadow. *)
Lemma w4c16_fsj_mv : forall cx fr j (regs R : bvmap 5 word) m m' W,
  ACtlCutP.FSj cx fr j regs m -> lib.Lib.Frame.munch W m m' ->
  (forall x, fr + 2880 <= x < fr + 2920 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) <= 35)%nat ->
  ACtlCutP.FSj cx fr j R m'.
Proof.
  intros cx fr j regs R m m' W (Hhave & Hn & Hbody & Had & HFI) MU OF OS HL.
  unfold ACtlCutP.FSj, ACtlCutP.FSb.
  split; [unfold ACtlCutP.u32 in *; apply (w4c16_bmv W m m' _ _ Hhave MU);
          rewrite lib.Lib.Mem.length_le4; intros x Hx; apply OF; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4c16_bmv W m m' _ _ Hn MU); cbn [length]; intros x Hx; apply OF; lia|].
  split; [apply (w4c16_bmv W m m' _ _ Hbody MU); intros x Hx; apply OF; lia|].
  split; [exact (w4c16_amv W m m' _ _ Had MU OS) | exact HFI].
Qed.

(* The configuration a callee returns to, in the cut's cfg_at form (lib/Lib's rom over B.Img0.rsegs is the core's over
   segs). *)
Lemma w4c16_cfg : forall (W : Reusable.YA0n.world segs) pc R m md Q,
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R m md) Q ->
  Reusable.YA0n.SRr segs W (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
                                     lib.Reusable.YK11.fp_csr None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md) Q.
Proof. intros W pc R m md Q H. rewrite B.ProgBridge.cfg_at_MS in H. exact H. Qed.

(* =============================================================================================================
   S_F14 KIT (prefix w4c14_).  Three groups: the pure model lengths the carried byte lists need (copies of
   lib/B/Prog/Seg/F15.v's t_ID_length / t_IDr_length / memcmp_self and of F1.v's f1_body_len, over this file's
   qualified names), the view / raw-memory bridge at a VISIBLE address (aview_vis_mrd's shape, PROVED here), and
   the transport of each carried bundle across the bcmp call's write window [sp - 2 * ESTACK, sp).
   ============================================================================================================= *)

Local Notation AGR m m' x :=
  (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x)).

(* ---- pure model facts ---- *)
Lemma w4c14_memcmp_self : forall (bs : list byte) (n : nat), (n <= length bs)%nat ->
  B.Spec.StrFun.memcmp_model bs bs n = Some 0.
Proof.
  intros bs n. revert bs. induction n as [|n IH]; intros [|b bs] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma w4c14_t_ID_length : forall inp j, length (B.Prog.SlotModel.t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold B.Prog.SlotModel.t_ID in *. rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
  assert (Hr : length (B.Prog.SlotModel.rp_id (B.Prog.SlotModel.fs_id (B.Prog.SlotModel.fst_at inp j))
                         (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j)) = 38%nat).
  { unfold B.Prog.SlotModel.rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply Prog.RcIdentModel.ING_length; exact IH | exact IH]. }
  assert (Hf : length (B.Prog.SlotModel.fg_id
                         (B.Prog.SlotModel.rp_id (B.Prog.SlotModel.fs_id (B.Prog.SlotModel.fst_at inp j))
                            (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j))
                         (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.fs_fg (B.Prog.SlotModel.fst_at inp j))
                         (B.Prog.SlotModel.t_g inp j)) = 38%nat).
  { unfold B.Prog.SlotModel.fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply Prog.RcIdentModel.ING_length; exact Hr | exact Hr]. }
  destruct (B.Prog.SlotModel.f_opens (B.Prog.SlotModel.t_len inp j) (B.Prog.SlotModel.t_g inp j));
    cbn [B.Prog.SlotModel.fs_id]; exact Hf.
Qed.

Lemma w4c14_t_IDr_length : forall inp j, length (B.Prog.SlotModel.t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold B.Prog.SlotModel.t_IDr, B.Prog.SlotModel.rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply Prog.RcIdentModel.ING_length; apply w4c14_t_ID_length | apply w4c14_t_ID_length].
Qed.

Lemma w4c14_body_len : forall inp j,
  (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite B.Prog.SlotModel.fst_at_S. unfold B.Prog.SlotModel.turn. cbv zeta.
  destruct (B.Prog.SlotModel.f_opens _ _); cbn [B.Prog.SlotModel.fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold B.Prog.SlotModel.t_g.
  rewrite B.Prog.SlotModel.fr50_length. lia.
Qed.

Lemma w4c14_kn_len : (length ACtlCutP.KNA.kind_name_bytes <= 112)%nat.
Proof. vm_compute. lia. Qed.

Lemma w4c14_frrec_length : forall cx j fr phi, length (ACtlCutP.frrec cx j fr phi) = 72%nat.
Proof.
  intros cx j fr phi. unfold ACtlCutP.frrec, ACtlCutP.frcl.
  apply w4c_fg_next_length; [apply w4c_t_FG_length | apply w4c_t_g_length].
Qed.

(* ---- the view / raw-memory bridge at a visible address (aview_vis_mrd's shape) ---- *)
Lemma w4c14_aview_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Hv.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd.
  rewrite Hv. reflexivity.
Qed.

Lemma w4c14_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

Lemma w4c14_aview_of_apresent : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None.
Proof.
  intros W mem a (Hv & b & Hb). rewrite (w4c14_aview_mrd W mem a Hv).
  unfold lib.Lib.Mem.mrd. rewrite Hb. discriminate.
Qed.

Lemma w4c14_byte_sgn : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* raw ASan addressability + visible shadow bytes give the core's range_addressable over aview *)
Lemma w4c14_ra_of_addr : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (p n : Z),
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem)
    Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W mem p n (Hp0 & Hn0 & Hpn & Hb) Hvis x Hx.
  destruct (Hb (x - p) ltac:(lia)) as (Happ & bb & Hbb & Hok).
  pose proof (Hvis (x - p) ltac:(lia)) as Hv.
  replace (p + (x - p)) with x in Hbb, Hok, Hv by lia.
  assert (Esh : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr,
          B.AsanRT.ASAN_K; lia).
  rewrite Esh.
  assert (Hs0 : 0 <= bv_signed bb).
  { unfold B.AsanRT.shadow_ok in Hok. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  exists (bv_unsigned bb). split.
  - rewrite (w4c14_aview_mrd W mem _ Hv). unfold lib.Lib.Mem.mrd in *. unfold lib.Lib.Mem.wa in Hbb.
    rewrite Hbb. reflexivity.
  - unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
    rewrite (w4c14_byte_sgn bb Hs0). destruct Hok as [H0 | (H1 & H2)]; [left; exact H0 | right; lia].
Qed.

(* the shadow hull of a 72-byte range inside the owned frame stays inside the frame's 512 shadow bytes *)
Lemma w4c14_hull_in : forall fr a n s,
  fr mod 8 = 0 -> 0 <= fr -> fr + 56 <= a -> a + n <= fr + 4000 -> 0 < n ->
  Reusable.YG0f.shadow_addr a / 8 * 8 <= s < Reusable.YG0f.shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  B.AsanRT.shadow_addr fr <= s < B.AsanRT.shadow_addr fr + 512.
Proof.
  intros fr a n s Hfm Hfr0 Hlo Hhi Hn Hs.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  set (uS := 2147450880 + a / 8) in *.
  set (wS := 2147450880 + (a + n - 1) / 8) in *.
  pose proof (Z.div_mod uS 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound uS 8 ltac:(lia)) as Mu.
  pose proof (Z.div_mod wS 8 ltac:(lia)) as Dw. pose proof (Z.mod_pos_bound wS 8 ltac:(lia)) as Mw.
  assert (Hau : fr / 8 + 7 <= a / 8).
  { pose proof (Z.div_le_mono (fr + 7 * 8) a 8 ltac:(lia) ltac:(lia)) as D.
    rewrite (Z.div_add fr 7 8 ltac:(lia)) in D. lia. }
  assert (Haw : (a + n - 1) / 8 <= fr / 8 + 500).
  { pose proof (Z.div_le_mono (a + n - 1) (fr + 500 * 8) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite (Z.div_add fr 500 8 ltac:(lia)) in D. lia. }
  subst uS wS. lia.
Qed.

Lemma w4c14_hull_of_pres : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (x n : Z),
  (forall s, Reusable.YG0f.shadow_addr x / 8 * 8 <= s < Reusable.YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem s) ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n.
Proof.
  intros W mem x n H s Hs. exact (w4c14_aview_of_apresent W mem s (H s Hs)).
Qed.

(* ---- raw-memory transport ---- *)
Lemma w4c14_ba_keep : forall m m' a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> AGR m m' x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold lib.Lib.Mem.wa. exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

Lemma w4c14_addr_keep : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> AGR m m' (B.AsanRT.shadow_addr (p + i))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. unfold lib.Lib.Mem.wa in *.
  rewrite (HK i Hi). exact Hb.
Qed.

Lemma w4c14_q64_keep : forall m m' a v, ACtlCutP.q64 m a v ->
  (forall x, a <= x < a + 8 -> AGR m m' x) -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.q64 in *. apply (w4c14_ba_keep m m' _ _ H).
  rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8. exact K.
Qed.

Lemma w4c14_u16_keep : forall m m' a v, ACtlCutP.u16 m a v ->
  (forall x, a <= x < a + 2 -> AGR m m' x) -> ACtlCutP.u16 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.u16 in *. apply (w4c14_ba_keep m m' _ _ H).
  rewrite lib.Lib.Mem.length_le2. change (Z.of_nat 2) with 2. exact K.
Qed.

Lemma w4c14_u32_keep : forall m m' a v, ACtlCutP.u32 m a v ->
  (forall x, a <= x < a + 4 -> AGR m m' x) -> ACtlCutP.u32 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.u32 in *. apply (w4c14_ba_keep m m' _ _ H).
  rewrite lib.Lib.Mem.length_le4. change (Z.of_nat 4) with 4. exact K.
Qed.

Lemma w4c14_b8_keep : forall m m' a v, ACtlCutP.b8 m a v ->
  (forall x, a <= x < a + 1 -> AGR m m' x) -> ACtlCutP.b8 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.b8 in *. apply (w4c14_ba_keep m m' _ _ H).
  cbn [length]. change (Z.of_nat 1) with 1. exact K.
Qed.

Lemma w4c14_spill_keep : forall (regs regs' : bvmap 5 word) m m' A off v,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> AGR m m' x) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hs Hr9 HA0 HA1 Hoff E9 HK.
  pose proof (w4c_spill_q64 regs m off v A Hs Hr9 HA0 HA1 Hoff) as Hq.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr9|].
  exact (w4c14_q64_keep m m' (A + off) v Hq HK).
Qed.

Lemma w4c14_q64_det : forall m a v1 v2, ACtlCutP.q64 m a v1 -> ACtlCutP.q64 m a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Hb1 Hb2.
  assert (E : lib.Lib.Mem.le8 (Z_to_bv 64 v1) = lib.Lib.Mem.le8 (Z_to_bv 64 v2)).
  { unfold ACtlCutP.q64 in H1, H2. destruct H1 as (_ & _ & Hb). destruct H2 as (_ & _ & Hc).
    apply nth_error_ext. intros i.
    destruct (Nat.lt_ge_cases i (length (lib.Lib.Mem.le8 (Z_to_bv 64 v1)))) as [Hi|Hi].
    - rewrite <- (Hb i Hi), <- (Hc i ltac:(rewrite !lib.Lib.Mem.length_le8 in *; lia)). reflexivity.
    - rewrite (proj2 (nth_error_None _ i) Hi),
        (proj2 (nth_error_None _ i) ltac:(rewrite !lib.Lib.Mem.length_le8 in *; lia)). reflexivity. }
  apply (f_equal le_bytes_to_word) in E.
  rewrite !lib.Lib.Mem.le_bytes_to_word_le8 in E.
  exact (w4c_lit_inj v1 v2 Hb1 Hb2 E).
Qed.

Lemma w4c14_stk_keep : forall m m' lo hi,
  lib.Lib.Frame.stk segs m lo hi ->
  (forall x, lo <= x < hi -> wview B.Img0.rsegs m (Z_to_bv 64 x) <> None ->
     wview B.Img0.rsegs m' (Z_to_bv 64 x) <> None) ->
  (forall x, lo <= x < hi -> AGR m m' x) ->
  lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi HS WM K. rewrite tfibsegs_rsegs in HS |- *.
  destruct HS as (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). unfold lib.Lib.Mem.wa in *.
  split; [exact (WM a Ha Hw)|]. exists b. rewrite (K a Ha). exact Hb.
Qed.

(* ---- the carried bundles across the call's window ---- *)
Lemma w4c14_saved_len : forall cx, Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104.
Proof.
  intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity.
Qed.

Lemma w4c14_frac_keep : forall cx fr sel (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= fr ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 -> AGR m m' x) ->
  (forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> AGR m m' x) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' A HF Hr9 HA0 HA1 Hfr0 E2 E3 E4 E8 E9 E19 E26 KA KF KS KV.
  destruct HF as (A' & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qh & Q16 & (shb & Hshb & Hshl) & Hsaved & Q4088).
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as [Hb0 _]. exact Hb0. }
  unfold B.AsanRT.APPMEM_END in HSapp.
  assert (EA : A' = A).
  { apply w4c_lit_inj; [lia | lia |]. unfold ACtlCut.rgv in Hr9, Hr9'. rewrite <- Hr9, <- Hr9'. reflexivity. }
  subst A'.
  exists A, sp.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold ACtlCut.rgv in *; rewrite E8; exact Hr8|].
  split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr9'|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold ACtlCut.rgv in *; rewrite E19; exact Hr19|].
  split; [unfold ACtlCut.rgv in *; rewrite E26; exact Hr26|].
  do 8 (split; [assumption|]).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  split; [apply (w4c14_q64_keep m m' _ _ Q336); intros x Hx; apply KA; lia|].
  split; [apply (w4c14_q64_keep m m' _ _ Q48); intros x Hx; apply KA; lia|].
  split; [apply (w4c14_q64_keep m m' _ _ Q40); intros x Hx; apply KA; lia|].
  split; [apply (w4c14_q64_keep m m' _ _ Qh); intros x Hx; apply KF; lia|].
  split; [apply (w4c14_q64_keep m m' _ _ Q16); intros x Hx; apply KF; lia|].
  split.
  - exists shb. split; [|exact Hshl]. apply (w4c14_ba_keep m m' _ _ Hshb). rewrite Hshl.
    intros x Hx. apply KS.
    unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hx. change (Z.to_nat (3136 / 8)) with 392%nat in Hx. lia.
  - split; [apply (w4c14_ba_keep m m' _ _ Hsaved); rewrite w4c14_saved_len; intros x Hx; apply KV; lia|].
    apply (w4c14_q64_keep m m' _ _ Q4088). intros x Hx. apply KF. lia.
Qed.

Lemma w4c14_our_keep : forall cx fr m m', ACtlCutP.OURb cx fr m ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) -> ACtlCutP.OURb cx fr m'.
Proof.
  intros cx fr m m' H KF. unfold ACtlCutP.OURb in *. apply (w4c14_ba_keep m m' _ _ H).
  rewrite B.Prog.SlotModel.OUR_length. change (Z.of_nat 6) with 6. intros x Hx. apply KF. lia.
Qed.

Lemma w4c14_fli_keep : forall cx fr (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= fr ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H Hr9 HA0 HA1 Hfr0 E9 E27 KA KF KS KI HKN HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & _) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Hoff Hs. apply (w4c14_spill_keep regs regs' m m' A off v Hs Hr9 HA0 HA1 Hoff E9).
    intros x Hx. apply KA. lia. }
  unfold ACtlCutP.FLI.
  split; [unfold ACtlCut.rgv in *; rewrite E27; exact H27|].
  do 21 (split; [apply K; [lia | assumption]|]).
  split; [apply (w4c14_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4c14_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4c14_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4c14_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split.
  { split; [|exact HKN].
    apply (w4c14_ba_keep m m' _ _ HKNb). pose proof w4c14_kn_len as HL. intros x Hx. apply KI. lia. }
  split; (apply K; [lia | assumption]).
Qed.

Lemma w4c14_lk_keep : forall cx fr j (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= fr ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 27 = lib.Reusable.YK11.getr regs 27 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) Hr9 HA0 HA1 Hfr0 E9 E27 KA KF KS KI HKN HSTK.
  split; [exact Hj|].
  split; [apply (w4c14_spill_keep regs regs' m m' A 240 _ S240 Hr9 HA0 HA1 ltac:(lia) E9);
          intros x Hx; apply KA; lia|].
  split; [apply (w4c14_our_keep cx fr m m' HOUR); intros x Hx; apply KF; lia|].
  exact (w4c14_fli_keep cx fr regs regs' m m' A HFLI Hr9 HA0 HA1 Hfr0 E9 E27 KA KF KS KI HKN HSTK).
Qed.

Lemma w4c14_flv_keep : forall cx fr j (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FLV cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= fr ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  ACtlCutP.FLV cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (S120 & S128 & S256 & S304 & S296 & Hc) Hr9 HA0 HA1 Hfr0 E9 KA KF.
  assert (K : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Hoff Hs. apply (w4c14_spill_keep regs regs' m m' A off v Hs Hr9 HA0 HA1 Hoff E9).
    intros x Hx. apply KA. lia. }
  split; [apply K; [lia | exact S120]|]. split; [apply K; [lia | exact S128]|].
  split; [apply K; [lia | exact S256]|]. split; [apply K; [lia | exact S304]|].
  split; [apply K; [lia | exact S296]|].
  intros Hrf. destruct (Hc Hrf) as (Hpp & Hpn).
  split; [apply (w4c14_q64_keep m m' _ _ Hpp); intros x Hx; apply KF; lia
         |apply (w4c14_q64_keep m m' _ _ Hpn); intros x Hx; apply KF; lia].
Qed.

Lemma w4c14_fm_keep : forall cx j phi fr (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FM cx j phi fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  ACtlCutP.FM cx j phi fr regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' A (S184 & H24 & H22 & H25 & S312) Hr9 HA0 HA1 E9 E22 E24 E25 KA.
  split; [apply (w4c14_spill_keep regs regs' m m' A 184 _ S184 Hr9 HA0 HA1 ltac:(lia) E9);
          intros x Hx; apply KA; lia|].
  split; [unfold ACtlCut.rgv in *; rewrite E24; exact H24|].
  split; [unfold ACtlCut.rgv in *; rewrite E22; exact H22|].
  split; [unfold ACtlCut.rgv in *; rewrite E25; exact H25|].
  apply (w4c14_spill_keep regs regs' m m' A 312 _ S312 Hr9 HA0 HA1 ltac:(lia) E9).
  intros x Hx. apply KA. lia.
Qed.

Lemma w4c14_fs9_keep : forall cx j (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FS9 cx j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  ACtlCutP.FS9 cx j regs' m'.
Proof.
  intros cx j regs regs' m m' A H Hr9 HA0 HA1 E9 KA.
  apply (w4c14_spill_keep regs regs' m m' A 248 _ H Hr9 HA0 HA1 ltac:(lia) E9).
  intros x Hx. apply KA. lia.
Qed.

Lemma w4c14_fturn_keep : forall cx j phi (regs regs' : bvmap 5 word) m m' A,
  ACtlCutP.FTURN cx j phi regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, phi <= x < phi + ACtlCutP.flen cx j -> AGR m m' x) ->
  ACtlCutP.FTURN cx j phi regs' m'.
Proof.
  intros cx j phi regs regs' m m' A (S224 & S232 & Hph & Hlen) Hr9 HA0 HA1 E9 KA KP.
  split; [apply (w4c14_spill_keep regs regs' m m' A 224 _ S224 Hr9 HA0 HA1 ltac:(lia) E9);
          intros x Hx; apply KA; lia|].
  split; [apply (w4c14_spill_keep regs regs' m m' A 232 _ S232 Hr9 HA0 HA1 ltac:(lia) E9);
          intros x Hx; apply KA; lia|].
  split; [|exact Hlen].
  apply (w4c14_ba_keep m m' _ _ Hph). intros x Hx. apply KP. unfold ACtlCutP.flen in *. lia.
Qed.

Lemma w4c14_hb_keep : forall m m' phi len, ACtlCutP.HB m phi len ->
  (forall i, 0 <= i < B.ACtlK.a_size len -> AGR m m' (B.AsanRT.shadow_addr (phi + i))) ->
  ACtlCutP.HB m' phi len.
Proof.
  intros m m' phi len (Hnz & HA) K. split; [exact Hnz|].
  exact (w4c14_addr_keep m m' _ _ HA K).
Qed.

Lemma w4c14_fsj_keep : forall cx fr j (regs regs' : bvmap 5 word) m m',
  ACtlCutP.FSj cx fr j regs m -> 0 <= fr ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' (Hhave & Hn & Hbody & Had & HFI) Hfr0 KF KS.
  pose proof (w4c14_body_len (ACtlCut.c_in cx) j) as HL.
  unfold ACtlCutP.FSj, ACtlCutP.FSb.
  split; [apply (w4c14_u32_keep m m' _ _ Hhave); intros x Hx; apply KF; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ Hn); intros x Hx; apply KF; lia|].
  split; [apply (w4c14_ba_keep m m' _ _ Hbody); intros x Hx; apply KF; lia|].
  split; [apply (w4c14_addr_keep m m' _ _ Had); intros i Hi; apply KS; lia|].
  exact HFI.
Qed.

Lemma w4c14_recf_keep : forall cx fr j m m',
  ACtlCutP.RECF cx fr j m -> 0 <= fr ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) -> ACtlCutP.RECF cx fr j m'.
Proof.
  intros cx fr j m m' ((Hid & Hidok) & (Hfg & Hfgok)) Hfr0 KF.
  split; split; [| exact Hidok | | exact Hfgok].
  - unfold ACtlCutP.IDBe in *. apply (w4c14_ba_keep m m' _ _ Hid).
    rewrite w4c14_t_IDr_length. change (Z.of_nat 38) with 38. intros x Hx. apply KF. lia.
  - unfold ACtlCutP.FGBe in *. apply (w4c14_ba_keep m m' _ _ Hfg).
    rewrite w4c_t_FG_length. change (Z.of_nat 72) with 72. intros x Hx. apply KF.
    unfold ACtlCutP.fragb in *. lia.
Qed.

Lemma w4c14_frx_keep : forall cx j fr phi m m',
  ACtlCutP.FRX cx j fr phi m -> 0 <= fr ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, 50 <= ACtlCutP.flen cx j -> phi <= x < phi + 50 -> AGR m m' x) ->
  (forall x, 50 <= ACtlCutP.flen cx j -> phi <= x < phi + 50 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, fr + 2688 <= x < fr + 2726 -> wview B.Img0.rsegs m (Z_to_bv 64 x) <> None ->
     wview B.Img0.rsegs m' (Z_to_bv 64 x) <> None) ->
  ACtlCutP.FRX cx j fr phi m'.
Proof.
  intros cx j fr phi m m' (Hlong & Hrec & Harec & (idb & Lid & Hidc) & Haid & Hrf) Hfr0 KF KS KP KPS WM.
  split.
  { intros Hl. destruct (Hlong Hl) as (Hg & Ha & Hp). split.
    - apply (w4c14_ba_keep m m' _ _ Hg). rewrite w4c_t_g_length. change (Z.of_nat 50) with 50.
      intros x Hx. apply KP; [exact Hl | lia].
    - split; [apply (w4c14_addr_keep m m' _ _ Ha); intros i Hi; apply KPS; [exact Hl | lia] | exact Hp]. }
  split.
  { apply (w4c14_ba_keep m m' _ _ Hrec). rewrite w4c14_frrec_length. change (Z.of_nat 72) with 72.
    intros x Hx. apply KF. unfold ACtlCutP.fragb in *. lia. }
  split; [apply (w4c14_addr_keep m m' _ _ Harec); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
  split.
  { exists idb. split; [exact Lid|].
    destruct Hidc as ((Hwf & Hb) & (Hw0 & Hw1 & Hw)).
    split; [split; [exact Hwf|]|].
    - apply (w4c14_ba_keep m m' _ _ Hb).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r, Lid.
      change (Z.of_nat 38) with 38. intros x Hx. apply KF. lia.
    - split; [exact Hw0|]. split; [exact Hw1|]. intros i Hi.
      apply (WM (fr + 2688 + i)); [cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; lia|].
      exact (Hw i Hi). }
  split; [apply (w4c14_addr_keep m m' _ _ Haid); intros i Hi; apply KS; lia|].
  intros H1. destruct (Hrf H1) as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & AD & HU & HADb & HAD).
  split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|]. split; [exact Hb4|]. split; [exact Hb5|].
  exists AD. split; [apply (w4c14_u16_keep m m' _ _ HU); intros x Hx; apply KF; lia|].
  split; [exact HADb | exact HAD].
Qed.

Lemma w4c14_shr3 : forall x, 0 <= x -> Z.shiftr x 3 + B.ACtlK.ASAN_K = B.AsanRT.shadow_addr x.
Proof.
  intros x Hx. unfold B.ACtlK.ASAN_K, B.AsanRT.shadow_addr. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma w4c14_sh_in_hull : forall p n x, 0 <= p -> p <= x -> x < p + n -> 0 < n ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= B.AsanRT.shadow_addr x <
  Reusable.YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8.
Proof.
  intros p n x Hp0 Hlo Hhi Hn.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  set (uS := 2147450880 + p / 8) in *. set (wS := 2147450880 + (p + n - 1) / 8) in *.
  pose proof (Z.div_mod uS 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound uS 8 ltac:(lia)) as Mu.
  pose proof (Z.div_mod wS 8 ltac:(lia)) as Dw. pose proof (Z.mod_pos_bound wS 8 ltac:(lia)) as Mw.
  pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)) as Hdv1.
  pose proof (Z.div_le_mono x (p + n - 1) 8 ltac:(lia) ltac:(lia)) as Hdv2.
  subst uS wS. lia.
Qed.

Lemma w4c14_rec_inv_keep : forall cx j phi A kp m m',
  ACtlCutP.rec_inv cx j phi A kp m ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, phi <= x < phi + 50 -> AGR m m' x) ->
  (forall x, phi <= x < phi + 50 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, kp + 20 <= x < kp + 22 -> AGR m m' x) ->
  ACtlCutP.rec_inv cx j phi A kp m'.
Proof.
  intros cx j phi A kp m m' (Hp0 & Hp64 & H50 & Hk64 & Happ & Q312 & Hblk & Hbsl &
    (f16 & v14 & v15 & v16 & v17 & Q248 & U16 & Hkp22 & Hkp0 & B14 & B15 & B16 & B17 &
     HRv14 & HRv15 & HRv16 & HRv17 & S14 & S15 & S16 & S17 & Ef & Ek)) KA KP KPS KK.
  assert (Lblk : Z.of_nat (length (B.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j)) = 32).
  { unfold B.Prog.SlotModel.t_blk. rewrite Prog.RcFragLib.rf_bsl_length;
      [reflexivity | lia | lia | rewrite w4c_t_g_length; cbn; lia]. }
  assert (Lbsl : Z.of_nat (length (Prog.RcFrag.bsl (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 34 6)) = 6).
  { rewrite Prog.RcFragLib.rf_bsl_length; [reflexivity | lia | lia | rewrite w4c_t_g_length; cbn; lia]. }
  split; [exact Hp0|]. split; [exact Hp64|]. split; [exact H50|]. split; [exact Hk64|]. split; [exact Happ|].
  split; [apply (w4c14_q64_keep m m' _ _ Q312); intros x Hx; apply KA; lia|].
  split; [apply (w4c14_ba_keep m m' _ _ Hblk); rewrite Lblk; intros x Hx; apply KP; lia|].
  split; [apply (w4c14_ba_keep m m' _ _ Hbsl); rewrite Lbsl; intros x Hx; apply KP; lia|].
  exists f16, v14, v15, v16, v17.
  split; [apply (w4c14_q64_keep m m' _ _ Q248); intros x Hx; apply KA; lia|].
  split; [apply (w4c14_u16_keep m m' _ _ U16); intros x Hx; apply KK; lia|].
  split; [exact Hkp22|]. split; [exact Hkp0|].
  split; [apply (w4c14_b8_keep m m' _ _ B14); intros x Hx; apply KP; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ B15); intros x Hx; apply KP; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ B16); intros x Hx; apply KP; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ B17); intros x Hx; apply KP; lia|].
  split; [exact HRv14|]. split; [exact HRv15|]. split; [exact HRv16|]. split; [exact HRv17|].
  split; [apply (w4c14_b8_keep m m' _ _ S14); intros x Hx; rewrite (w4c14_shr3 (phi + 14) ltac:(lia)) in Hx;
          replace x with (B.AsanRT.shadow_addr (phi + 14)) by lia; apply KPS; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ S15); intros x Hx; rewrite (w4c14_shr3 (phi + 15) ltac:(lia)) in Hx;
          replace x with (B.AsanRT.shadow_addr (phi + 15)) by lia; apply KPS; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ S16); intros x Hx; rewrite (w4c14_shr3 (phi + 16) ltac:(lia)) in Hx;
          replace x with (B.AsanRT.shadow_addr (phi + 16)) by lia; apply KPS; lia|].
  split; [apply (w4c14_b8_keep m m' _ _ S17); intros x Hx; rewrite (w4c14_shr3 (phi + 17) ltac:(lia)) in Hx;
          replace x with (B.AsanRT.shadow_addr (phi + 17)) by lia; apply KPS; lia|].
  split; [exact Ef | exact Ek].
Qed.

Lemma w4c14_frb_keep : forall cx j fr phi A (regs regs' : bvmap 5 word) m m',
  ACtlCutP.FRB cx j fr phi A (fr + 176) regs m ->
  Reusable.YG0d.spZ regs' = Reusable.YG0d.spZ regs ->
  0 <= fr -> fr + 4096 <= 2 ^ 64 ->
  ACtlCutP.q64 m (A + 112) (fr + 186) -> ACtlCutP.q64 m (A + 96) (fr + 180) ->
  (forall x, A <= x < A + 448 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' x) ->
  (forall x, fr <= x < fr + 4096 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, 50 <= ACtlCutP.flen cx j -> phi <= x < phi + 50 -> AGR m m' x) ->
  (forall x, 50 <= ACtlCutP.flen cx j -> phi <= x < phi + 50 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.FRB cx j fr phi A (fr + 176) regs' m'.
Proof.
  intros cx j fr phi A regs regs' m m'
    (Happ2880 & (w272 & Hq272 & Hw0 & Hwt & Hwf) & Hkp1 & Hkp2 & Hkp3 & HphiG & H8819)
    Easp Hfr0 Hfr64 QL112 QL96 KA KF KFS KP KPS.
  unfold ACtlCutP.FRB. rewrite Easp.
  split; [exact Happ2880|].
  split.
  { exists w272. split; [apply (w4c14_q64_keep m m' _ _ Hq272); intros x Hx; apply KA; lia|].
    split; [exact Hw0|]. split; [exact Hwt | exact Hwf]. }
  split; [exact Hkp1|]. split; [exact Hkp2|]. split; [exact Hkp3|]. split; [exact HphiG|].
  intros H8.
  destruct (H8819 H8) as (HRI &
    (L & ls & rs & QL & HBL & HLl & HBR & HLr & Hmm & HAL & Hap6 & Hap7 & HLBC & HLA & HL2688) &
    (L2 & ls2 & rs2 & QL2 & HBL2 & HLl2 & HBR2 & HLr2 & Hmm2 & HAL2 & Hap62 & Hap72 & HL2BC & HL2A & HL22688)).
  assert (H50 : 50 <= ACtlCutP.flen cx j) by exact (proj1 (proj2 (proj2 HRI))).
  assert (KP' : forall x, phi <= x < phi + 50 ->
                  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x))
    by (intros x Hx; apply KP; [exact H50 | exact Hx]).
  assert (KPS' : forall x, phi <= x < phi + 50 ->
                   lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr x)) =
                   lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr x)))
    by (intros x Hx; apply KPS; [exact H50 | exact Hx]).
  assert (HLb : 0 <= L /\ L + Z.of_nat (length ls) <= 2 ^ 64) by (destruct HBL as (HLb0 & HLb1 & _); split; [exact HLb0 | exact HLb1]).
  assert (HL2b : 0 <= L2 /\ L2 + Z.of_nat (length ls2) <= 2 ^ 64) by (destruct HBL2 as (HLb0 & HLb1 & _); split; [exact HLb0 | exact HLb1]).
  rewrite HLl in HLb. rewrite HLl2 in HL2b. cbn in HLb, HL2b.
  assert (EL : L = fr + 186) by (apply (w4c14_q64_det m (A + 112) L (fr + 186) QL QL112); lia).
  assert (EL2 : L2 = fr + 180) by (apply (w4c14_q64_det m (A + 96) L2 (fr + 180) QL2 QL96); lia).
  split.
  { apply (w4c14_rec_inv_keep cx j phi A (fr + 176) m m' HRI KA KP' KPS').
    intros x Hx. apply KF. lia. }
  split.
  { exists L, ls, rs.
    split; [apply (w4c14_q64_keep m m' _ _ QL); intros x Hx; apply KA; lia|].
    split; [apply (w4c14_ba_keep m m' _ _ HBL); rewrite HLl; cbn; intros x Hx; apply KF; lia|].
    split; [exact HLl|].
    split; [apply (w4c14_ba_keep m m' _ _ HBR); rewrite HLr; cbn; intros x Hx; apply KP'; lia|].
    split; [exact HLr|]. split; [exact Hmm|].
    split; [apply (w4c14_addr_keep m m' _ _ HAL); intros i Hi; apply KFS; lia|].
    split; [exact Hap6|]. split; [exact Hap7|].
    split; [exact HLBC|]. split; [exact HLA | exact HL2688]. }
  { exists L2, ls2, rs2.
    split; [apply (w4c14_q64_keep m m' _ _ QL2); intros x Hx; apply KA; lia|].
    split; [apply (w4c14_ba_keep m m' _ _ HBL2); rewrite HLl2; cbn; intros x Hx; apply KF; lia|].
    split; [exact HLl2|].
    split; [apply (w4c14_ba_keep m m' _ _ HBR2); rewrite HLr2; cbn; intros x Hx; apply KP'; lia|].
    split; [exact HLr2|]. split; [exact Hmm2|].
    split; [apply (w4c14_addr_keep m m' _ _ HAL2); intros i Hi; apply KFS; lia|].
    split; [exact Hap62|]. split; [exact Hap72|].
    split; [exact HL2BC|]. split; [exact HL2A | exact HL22688]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82340_at j (0x82340) --S_F13--> B8235c_at j.
   S_F13 (Seg/F13.v seg_F13 :1310): the six arguments and reac_ctrl_identity_fragment @0x82358, returning at
   0x8235c with a0 = the fragment result. *)
Lemma seg_F13 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8235c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82340_at [Z.of_nat j]).
Proof.
  intros POST j H5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk HBODY Hrt.
  unfold ix_cut, ACtlCutP.C_B82340_at in Hk, HBODY, HJ, HF, HL |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, HF, HL |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (HFRAC & phi & HP & Hn & Hj & HHB & H18 & H20 & HFT & (HLK & H336 & HFM & HFS) & H21 & H50 &
    Hfgb & Haf & Ha336 & Hapa & Happ & Hapn & HRECR & HFRBA & HFS9).
  (* ---- the cut's facts: the spill base, the journal, the owned frame, the turn block ---- *)
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & _).
  destruct (w4c13_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  destruct (w4c13_aj_stk _ _ _ _ _ _ _ _ HJ) as (Hstlo & Hstlo2 & Hsthi & Hsthi2).
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [[Hac1 Hac2] _]. unfold Reusable.YG0f.ASAN_CEIL in Hac1, Hac2.
  pose proof (w4c13_spZ regs3) as Hsp. pose proof (w4c13_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HKv : B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K = 4672) by reflexivity.
  rewrite HSTKv in Hceil, Hwin, Hstlo2. rewrite HFBv in Hfa.
  unfold B.AsanRT.APPMEM_END in HAPP.
  pose proof (w4c13_frame _ _ _ _ _ _ _ _ HJ HF (HL 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
    as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  pose proof HJ as (_ & Hly & _).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4c_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Hphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hpn).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hphi Hin6)
    as Hsep.
  unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efr in Hsep. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep.
  pose proof HFT as (_ & _ & _ & Hphilen).
  pose proof (w4c13_flen_small (ACtlCut.c_in cx) j) as Hfls.
  change (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) with (ACtlCutP.flen cx j) in Hphilen, Hfls.
  assert (Hfl0 : 0 <= ACtlCutP.flen cx j) by lia.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) Hfl0) as Hrs.
  pose proof (w4c13_frame_place _ _ _ _ _ 6 (ACtlCut.c_fpos cx) HAR Hin6
    ltac:(change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia)) as Hplace.
  rewrite Efr in Hplace. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hplace.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 _ HAR Hin6) as (_ & Happf & _).
  rewrite Efr in Happf. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happf.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happf.
  assert (NSfr : forall a, fr <= a < fr + 4096 -> find_segment B.Img0.rsegs a 1 = None).
  { intros a Ha. apply (w4c13_frame_noseg _ _ _ _ _ 6 (ACtlCut.c_fpos cx) a HAR Hin6).
    rewrite Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. exact Ha. }
  assert (NRfr : forall a, fr <= a < fr + 4096 -> lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false).
  { intros a Ha. apply w4c13_ro_false. rewrite lib.Lib.Mem.wa_unsigned by lia. exact (NSfr a Ha). }
  assert (HA0 : 0 <= A) by lia. assert (HA1 : A + 448 <= 2 ^ 64) by lia.
  pose proof HLK as (_ & _ & _ & HFLI).
  pose proof HFLI as (_ & _ & S96 & S112 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S288 & S296 & S304 & _).
  pose proof (w4c_spill_q64 _ _ _ _ _ S288 Hr9 HA0 HA1 ltac:(lia)) as Q288.
  pose proof (w4c_spill_q64 _ _ _ _ _ S296 Hr9 HA0 HA1 ltac:(lia)) as Q296.
  pose proof (w4c_spill_q64 _ _ _ _ _ S304 Hr9 HA0 HA1 ltac:(lia)) as Q304.
  pose proof (w4c_spill_q64 _ _ _ _ _ S112 Hr9 HA0 HA1 ltac:(lia)) as Q112.
  pose proof (w4c_spill_q64 _ _ _ _ _ S96 Hr9 HA0 HA1 ltac:(lia)) as Q96.
  (* route (C): the cut's ctl_rt_C -- asan_cells, the cut's own shadow, the image's shadow, ro_agree *)
  pose proof Hrt as (HAC & HSW & _ & Hro).
  change (B.MemNorm.ro_agree B.Img0.rsegs mem3) in Hro.
  destruct (ctl_bcmp_cells_of_AR _ _ _ _ _ HAR) as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct HRECR as ((HIDB & Hidok) & (HFGB & Hfok)).

  (* ---- the run: F13F.f13_pre_F, then the fragment's footprint contract on the normalized memory (MemNorm route,
     a Theorem Labs lane's B lift), lifted by SRr_fevt_hid at RNG := RNG_W (w_H W3) ---- *)
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82340) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Vwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
            B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2. apply (w4c_win_vis _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); rewrite ?HSTKv; lia. }
  assert (Vfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> 0 <= len ->
            B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hfrb a ltac:(lia))). }
  assert (Hfrsh' : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) by (intros a Ha; exact (proj1 (Hfrsh a Ha))).
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 RNG).
  - apply B.ProgBridge.fevt_of_evtF. eapply Lib.ExecF.evtF_cut.
    + unfold Lib.Regs6ss.mkR_of.
      eapply (F13F.f13_pre_F RNG) with (m := mem3) (A := A) (f := ACtlCutP.fragb fr) (frg := phi)
        (len := ACtlCutP.flen cx j) (pa := fr + 256) (pp := fr + 272) (pn := fr + 304).
      * exact Hr9.
      * exact H21.
      * exact H18.
      * exact H20.
      * lia.
      * unfold ACtlCutP.fragb; lia.
      * lia.
      * lia.
      * apply w4c13_rwc_of_q64; [exact Q288 | apply (w4c13_wr_win _ _ _ _ _ _ _ _ _ _ HJ); rewrite ?HSTKv; lia].
      * apply w4c13_rwc_of_q64; [exact Q296 | apply (w4c13_wr_win _ _ _ _ _ _ _ _ _ _ HJ); rewrite ?HSTKv; lia].
      * apply w4c13_rwc_of_q64; [exact Q304 | apply (w4c13_wr_win _ _ _ _ _ _ _ _ _ _ HJ); rewrite ?HSTKv; lia].
      * apply B.ProgBridge.rng_of_visible. apply Vwin; lia.
      * apply B.ProgBridge.rng_of_visible. apply Vwin; lia.
    + intros ms1 ->.
      eapply (B.MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ mem3 _ Hro).
      change (Z_to_bv 64 0x859e4) with (Z_to_bv 64 B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT).
      apply (B.Prog.reac_ctrl_identity_fragment_F_closed.reac_ctrl_identity_fragment_holds_F_closed_on RNG
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (B.MemNorm.normalize B.Img0.rsegs mem3) (ACtlCutP.fragb fr) phi (ACtlCutP.flen cx j)
               (fr + 256) (fr + 272) (fr + 304) (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j)
               (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j));
        w4c13_sp sp Hspz.

      * exact H21.
      * exact H18.
      * exact H20.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold ACtlCutP.fragb; lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Hsp16.
      * rewrite HKv. apply w4c13_stk_normalize; [exact Hro | |].
        -- intros a Ha. apply w4c13_ro_false. rewrite lib.Lib.Mem.wa_unsigned by lia. apply w4c13_noseg. lia.
        -- apply w4c13_stk_of_pres; [lia | lia |]. intros a Ha. exact (proj2 (Hwin a ltac:(lia))).
      * apply w4c_t_g_length.
      * apply w4c_t_FG_length.
      * intros _ _ _ _ _ Hl. apply B.MemNorm.bytes_at_normalize; [exact Hro | exact (proj1 (proj2 (proj2 (H50 Hl))))].
      * intros _ _ _ _ _.
        pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 Hro) as REL.
        assert (Wfr : forall a n, fr <= a -> a + n <= fr + 4096 -> 0 <= n ->
                  lib.Lib.Mem.wr_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) a n).
        { intros a n H1 H2 H3. apply (B.MemNorm.wr_at_norm B.Img0.rsegs mem3 _ a n REL).
          - apply w4c13_wr_of_pres; [lia | lia |]. intros x Hx. exact (proj1 (proj2 (Hfrb x ltac:(lia)))).
          - intros i Hi. apply NRfr. lia. }
        split.
        { apply w4c13_rw_cells_normalize; [exact Hro | |].
          - intros i Hi. cbn in Hi. apply NRfr. unfold ACtlCutP.fragb. lia.
          - split; [split|].
            + cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [apply w4c_t_FG_length | exact I].
            + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hfgb.
            + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. apply w4c13_wr_of_pres; [unfold ACtlCutP.fragb; lia | unfold ACtlCutP.fragb; lia |].
              intros x Hx. exact (proj1 (proj2 (Hfrb x ltac:(unfold ACtlCutP.fragb in *; lia)))). }
        split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
        split; [Z.div_mod_to_equations; lia|].
        split; [apply Wfr; lia|]. split; [apply Wfr; lia|]. split; [apply Wfr; lia|].
        rewrite HKv. cbn [Prog.RcFrag.all_dj Prog.RcFrag.dj_from]. unfold ACtlCutP.fragb. repeat split; lia.
      * apply B.MemNorm.mem_inv_normalize.
      * exact (w4c13_asan_cells_normalize mem3 Hro HAC).
      * (* route (C): the fragment's R lies in the cut's own shadow (w4c13_frag_R_in), carried to the normal form *)
        apply (B.ShadowRwOnT.shadow_rw_on_normalize _ mem3 Hro).
        apply (B.ShadowRwOn.shadow_rw_on_mono (B.ACtlRtC.cut_shadow B ly3 S3) _ mem3); [|exact HSW].
        intros a Ha.
        refine (w4c13_frag_R_in ly3 S3 (ACtlCut.c_fpos cx) fr phi (ACtlCutP.flen cx j)
                  (fr + 256) (fr + 272) (fr + 304) _ _ a Hin6 Efr _ _ _ Hphi Hfl0 _ _ Ha);
          [clear - Hfr32; Z.div_mod_to_equations; lia | lia ..].
      * rewrite HKv. unfold B.AsanRT.HIGHMEM_BEG. lia.
      * unfold B.AsanRT.APPMEM_END. lia.
      * intros _ _ _ _ _ Hl. exact (w4c13_addressable_normalize mem3 _ _ Hro (proj2 (proj2 (proj2 (H50 Hl))))).
      * intros _ _ _ _ _.
        split; [exact (w4c13_addressable_normalize mem3 _ _ Hro Haf)|].
        split; [exact (w4c13_addressable_normalize mem3 _ _ Hro Hapa)|].
        split; [exact (w4c13_addressable_normalize mem3 _ _ Hro Happ)|].
        split; [exact (w4c13_addressable_normalize mem3 _ _ Hro Hapn)|].
        split; [unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END, ACtlCutP.fragb; lia|].
        cbn [Prog.RcFrag.dj_from]. unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI, ACtlCutP.fragb. repeat split; lia.
      * apply B.MemNorm.bytes_at_normalize; [exact Hro | exact Hc1].
      * apply B.MemNorm.bytes_at_normalize; [exact Hro | exact Hc2].
      * apply B.MemNorm.bytes_at_normalize; [exact Hro | exact Hc3].
      * apply B.MemNorm.bytes_at_normalize; [exact Hro | exact Hc4].
      * apply B.MemNorm.bytes_at_normalize; [exact Hro | exact Hc5].
      * exact (B.ProgBridge.rng_bytes_RNG_W _).
      * exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
      * rewrite HKv. apply B.ProgBridge.rng_of_visible. apply Vwin; lia.
      * unfold B.Prog.rng_asan.sh_word_rng. right. rewrite HKv. apply B.ProgBridge.rng_of_visible.
        apply (w4c13_win_shadow_vis ly3 S3 W3 mem3 md3); [exact HAR | lia | lia | lia | lia | lia].
      * intros _ _ _ _ _ Hl. apply B.ProgBridge.rng_of_visible.
        apply (w4c13_heap_vis _ _ _ _ _ _ _ _ _ HAR Hphi); lia.
      * intros _ _ _ _ _ Hl. apply B.ProgBridge.rng_of_visible.
        apply (w4c13_cover_hull W3 mem3 phi (Reusable.YG00.req_size (ACtlCutP.flen cx j)));
          [exact (proj2 (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi)) | lia | lia | lia | lia].
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply Vfr; unfold ACtlCutP.fragb; lia.
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply (w4c13_cover_in _ fr); [exact Hfrsh' | unfold ACtlCutP.fragb; lia ..].
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply Vfr; lia.
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply (w4c13_cover_in _ fr); [exact Hfrsh' | lia ..].
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply Vfr; lia.
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply (w4c13_cover_in _ fr); [exact Hfrsh' | lia ..].
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply Vfr; lia.
      * intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. apply (w4c13_cover_in _ fr); [exact Hfrsh' | lia ..].
  - exact (B.ProgBridge.fp_avoids_RNG_W _).

  - intros ms' md' HPo Hhid Hsame.
    destruct HPo as (s0 & PO & HREL & HROS).
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU0 & WM0 & _ & ST0 & FG0 & AC0 & SW0).
    rewrite E0 in HREL. destruct (w4c13_ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
    pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 Hro) as REL.
    pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ mem3 _ (ms_mem ms') m0' REL HMR HROS MU0) as MU.
    pose proof (B.MemNorm.wmono_rel B.Img0.rsegs mem3 _ (ms_mem ms') m0' REL HMR HROS WM0) as WM.
    pose proof (w4c13_stk_of_rel _ _ _ _ HMR ST0) as ST'.
    pose proof (w4c13_fg_mem_of_rel _ _ _ _ _ _ _ _ _ HMR FG0) as FGM.
    w4c13_sp_in MU sp Hspz. w4c13_sp_in ST' sp Hspz.
    rewrite HKv in MU, ST'.
    rewrite Ems. clear E0 MU0 WM0 ST0 FG0 AC0 HREL.
    set (mem' := ms_mem ms') in *.
    assert (Hhid' : forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) by exact Hhid.
    rewrite (lib.Lib.MState.ret_pc_even 0x8235c) by lia.
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R' := R) end.
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x8235c R' mem' md') (POST cx)).
    assert (E2 : lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
    assert (E3 : lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
    assert (E4 : lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
    assert (E8 : lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
    assert (E9 : lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
    assert (E18 : lib.Reusable.YK11.getr R' 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
    assert (E19 : lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
    assert (E20 : lib.Reusable.YK11.getr R' 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
    assert (E22 : lib.Reusable.YK11.getr R' 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
    assert (E24 : lib.Reusable.YK11.getr R' 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
    assert (E25 : lib.Reusable.YK11.getr R' 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
    assert (E26 : lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
    assert (E27 : lib.Reusable.YK11.getr R' 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
    assert (E10 : lib.Reusable.YK11.getr R' 10 = Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)))
      by reflexivity.
    assert (ESP : Reusable.YG0d.spZ R' = Reusable.YG0d.spZ regs3) by (unfold Reusable.YG0d.spZ; rewrite E2; reflexivity).
    (* ---- the journal: the call wrote the owned frame's cells and its window [sp - K, sp) ---- *)
    assert (HJ' : w4c13_AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem' md' k).
    { apply (w4c13_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU WM Hhid' Hsame).
      intros a Ha. destruct (w4c13_fp_in _ _ _ _ _ _ _ a Ha) as [Hx|[Hx|[Hx|[Hx|Hx]]]];
        [unfold ACtlCutP.fragb in Hx .. |].
      1-4: destruct (Hfrb a ltac:(lia)) as (_ & Hpr & Hif);
           split; [lia|]; split; [apply NSfr; lia|]; split; [exact Hpr | right; right; right; exact Hif].
      destruct (Hwin a ltac:(lia)) as (_ & Hpr).
      split; [lia|]. split; [apply w4c13_noseg; lia|]. split; [exact Hpr | left; rewrite HSTKv; lia]. }
    pose proof (w4c13_frame _ _ _ _ _ _ _ _ HJ' HF (HL 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
      as (_ & _ & _ & Hfrb' & _).
    assert (HSTKfr : lib.Lib.Frame.stk segs mem' fr (fr + ACtlCutP.FRAME_BYTES)).
    { rewrite HFBv. apply w4c13_stk_of_pres; [lia | lia |]. intros a Ha. exact (proj1 (proj2 (Hfrb' a ltac:(lia)))). }
    (* route (C): ctl_rt_C at the successor cut from the post journal's AR (w4c_ctlrt, ctl_rt_C_of_AR) *)
    apply (H5c cx [Z.of_nat j] fr k ly3 S3 W3 R' mem' md' HB HJ' HF HL);
      [unfold ix_cut, ACtlCutP.C_B8235c_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk | |
       exact (w4c_ctlrt cx (ACtlCut.own6 cx) ly3 S3 W3 mem' md' k HB HJ')].

    (* ---- what the call kept: every byte outside its five write intervals ---- *)
    assert (AG : forall x, 0 <= x < 2 ^ 64 ->
      ~ (ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/ fr + 256 <= x < fr + 256 + 2 \/
         fr + 272 <= x < fr + 272 + 8 \/ fr + 304 <= x < fr + 304 + 8 \/ sp - 4672 <= x < sp) ->
      w4c13_AGR mem3 mem' x).
    { intros x Hx Hnot. apply (w4c13_mrd_munch _ _ _ x MU Hx). apply w4c13_fp_outside_of. exact Hnot. }
    assert (KF : forall x, fr <= x < fr + 256 \/ fr + 258 <= x < fr + 272 \/ fr + 280 <= x < fr + 304 \/
                            fr + 312 <= x < fr + 2768 \/ fr + 2840 <= x < fr + 4096 -> w4c13_AGR mem3 mem' x).
    { intros x Hx. apply AG; unfold ACtlCutP.fragb; lia. }
    assert (KA : forall x, A <= x < 2 ^ 64 -> w4c13_AGR mem3 mem' x).
    { intros x Hx. apply AG; unfold ACtlCutP.fragb; lia. }
    assert (KS : forall x, B.AsanRT.ASAN_K <= x < B.AsanRT.HIGHMEM_BEG -> w4c13_AGR mem3 mem' x).
    { intros x Hx. unfold B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG in Hx. apply AG; unfold ACtlCutP.fragb; lia. }
    assert (KH : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) -> w4c13_AGR mem3 mem' x).
    { intros x Hx. apply AG; unfold ACtlCutP.fragb; lia. }
    assert (KI : forall x, 0x10000 <= x < 0x5fe000 -> w4c13_AGR mem3 mem' x).
    { intros x Hx. apply AG; unfold ACtlCutP.fragb; lia. }
    (* ---- the record after the call, and as the model keeps it ---- *)
    assert (EFR : ACtlCutP.frrec cx j fr phi = ACtlCutP.SM.t_FG (ACtlCut.c_in cx) (S j)).
    { unfold ACtlCutP.frrec. rewrite w4c_t_FG_S. unfold ACtlCutP.SM.t_FGf, ACtlCutP.SM.fg_st. f_equal.
      rewrite (w4c_frcl_fcls cx j fr phi) by (unfold ACtlCutP.fragb; lia). unfold ACtlCutP.flen. reflexivity. }
    assert (Hrec : lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (ACtlCutP.fragb fr) (ACtlCutP.frrec cx j fr phi)).
    { pose proof FGM as FGM1. pose proof MU as MU1.
      unfold ACtlCutP.frrec, ACtlCutP.frcl.
      rewrite (Prog.RcFragLib.rf_class_nn (ACtlCutP.fragb fr) phi (fr + 256) (fr + 272) (fr + 304))
        in FGM1, MU1 |- * by (unfold ACtlCutP.fragb; lia).
      destruct (Prog.RcFrag.fg_fr (ACtlCutP.flen cx j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) eqn:FR;
        cbn [negb] in FGM1, MU1 |- *.
      - destruct (Prog.RcFrag.bat (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) 19 =? 1);
          cbn [B.Prog.reac_ctrl_identity_fragment_c.fg_mem ACtlCutP.SM.fg_next] in FGM1 |- *; [exact FGM1|].
        destruct (Prog.RcFrag.fg_keep (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j));
          cbn [negb] in FGM1 |- *;
          [|cbn [B.Prog.reac_ctrl_identity_fragment_c.fg_mem ACtlCutP.SM.fg_next] in FGM1 |- *; exact FGM1].
        destruct (Prog.RcFrag.fg_close (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j));
          cbn [negb B.Prog.reac_ctrl_identity_fragment_c.fg_mem ACtlCutP.SM.fg_next] in FGM1 |- *;
          [exact (proj1 FGM1) | exact FGM1].
      - cbn [ACtlCutP.SM.fg_next]. apply (w4c13_ba_keep mem3 mem' _ _ Hfgb). rewrite w4c_t_FG_length.
        intros x Hx. apply (w4c13_mrd_munch _ _ _ x MU1); [unfold ACtlCutP.fragb in *; lia|].
        cbn [Prog.RcFrag.fg_fp lib.Lib.Frame.outside]. split; [unfold ACtlCutP.fragb in *; lia | exact I]. }
    (* ---- C_B8235c_at's body at the post state ---- *)
    unfold ix_cut, ACtlCutP.C_B8235c_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. rewrite Ej.
    split.
    { apply (w4c13_frac_mem cx fr fr regs3 R' mem3 mem' A HFRAC Hr9 ltac:(lia) E2 E3 E4 E8 E9 E19 E26).
      intros x Hx. unfold ACtlCutP.Sfr in Hx. change ACtlCutP.FRAME_SHADOW with 392 in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]];
        [apply KA; lia | apply KA; lia | apply KF; lia | apply KS | apply KA; lia | apply KF; lia].
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG in *.
      pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)).
      assert (fr / 8 + 392 < 2 ^ 44) by (apply (Z.lt_le_trans _ ((fr + 3136) / 8 + 1)); [Z.div_mod_to_equations; lia|];
        assert ((fr + 3136) / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia); lia).
      lia. }
    unfold ACtlCutP.fcutp_body. exists phi.
    split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|].
    split; [destruct HHB as (Hpz & Had); split; [exact Hpz | exact (w4c13_addr_keep_sh _ _ _ _ Had KS)]|].
    split; [exact (w4c13_rgv_move _ _ _ _ H18 E18)|]. split; [exact (w4c13_rgv_move _ _ _ _ H20 E20)|].
    split.
    { apply (w4c13_fturn_mem cx j phi regs3 R' mem3 mem' A HFT Hr9 HA0 HA1 E9);
        [intros x Hx; apply KA; lia | intros x Hx; apply KH; lia]. }
    cbv beta.
    split.
    { split.
      { apply (w4c13_lk_mem cx fr j regs3 R' mem3 mem' A HLK Hr9 HA0 HA1 E9 E27);
          [intros x Hx; apply KA; lia | intros x Hx; apply KF; lia | exact KS
          | intros x Hx; apply KI; change ACtlCutP.KNA.KIND_NAME with 652672 in Hx; lia | exact HSTKfr]. }
      split.
      { apply (w4c13_fm_mem cx j phi fr regs3 R' mem3 mem' A HFM Hr9 HA0 HA1 E9 E22 E24 E25).
        intros x Hx; apply KA; lia. }
      apply (w4c13_fsj_mem cx fr j regs3 R' mem3 mem' HFS); [intros x Hx; apply KF; lia | exact KS]. }
    split; [exact E10|].
    split.
    { intros Hl. destruct (H50 Hl) as (H1 & H2 & H3 & H4).
      split; [exact H1|]. split; [rewrite ESP; exact H2|].
      split; [apply (w4c13_ba_keep mem3 mem' _ _ H3); rewrite w4c_t_g_length; intros x Hx; apply KH; lia|].
      exact (w4c13_addr_keep_sh _ _ _ _ H4 KS). }
    split; [apply (w4c13_ba_keep mem3 mem' _ _ H336); rewrite w4c_t_FG_length; intros x Hx; apply KF; lia|].
    split; [exact (w4c13_addr_keep_sh _ _ _ _ Ha336 KS)|].
    split; [exact Hrec|].
    split; [exact (w4c13_addr_keep_sh _ _ _ _ Haf KS)|].
    split; [exact FGM|].
    split.
    { split; split.
      - unfold ACtlCutP.IDBe in *. apply (w4c13_ba_keep mem3 mem' _ _ HIDB). rewrite w4c13_t_IDr_length.
        intros x Hx. apply KF. lia.
      - exact Hidok.
      - unfold ACtlCutP.FGBe. rewrite <- EFR. exact Hrec.
      - apply w4c_fok_FG. }
    split.
    { destruct HFRBA as (A0 & H9b & HA0b & HFRB).
      assert (EA0 : A0 = A) by (apply (w4c13_rgv_inj regs3 9); [exact H9b | exact Hr9 | exact HA0b | lia]).
      subst A0.
      exists A. split; [exact (w4c13_rgv_move _ _ _ _ Hr9 E9)|]. split; [exact HA0b|].
      apply (w4c13_frb_mem cx j fr phi A regs3 R' mem3 mem' HFRB Q112 Q96 ltac:(lia) ltac:(lia) ESP).
      - intros x Hx. apply KA. lia.
      - intros x Hx. apply KF. lia.
      - intros Hl x Hx. apply KH. lia.
      - exact KS. }
    split.
    { split.
      { intros Hl. destruct (H50 Hl) as (H1 & H2 & H3 & H4).
        split; [apply (w4c13_ba_keep mem3 mem' _ _ H3); rewrite w4c_t_g_length; intros x Hx; apply KH; lia|].
        split; [exact (w4c13_addr_keep_sh _ _ _ _ H4 KS) | exact H1]. }
      split; [exact Hrec|].
      split; [exact (w4c13_addr_keep_sh _ _ _ _ Haf KS)|].
      split.
      { exists (ACtlCutP.SM.t_IDr (ACtlCut.c_in cx) j). split; [apply w4c13_t_IDr_length|].
        split; [split|].
        - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [apply w4c13_t_IDr_length | exact I].
        - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r.
          unfold ACtlCutP.IDBe in HIDB. apply (w4c13_ba_keep mem3 mem' _ _ HIDB). rewrite w4c13_t_IDr_length.
          intros x Hx. apply KF. lia.
        - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. apply w4c13_wr_of_pres; [lia | lia |].
          intros x Hx. exact (proj1 (proj2 (Hfrb' x ltac:(lia)))). }
      split.
      { pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HRAD1 & _) & _). exact (w4c13_addr_keep_sh _ _ _ _ HRAD1 KS). }
      intros Hrf1.
      pose proof (w4c_trf1_cls (ACtlCut.c_in cx) j Hrf1) as Hcls.
      assert (HCfrcl : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgClose).
      { rewrite (w4c_frcl_fcls cx j fr phi) by (unfold ACtlCutP.fragb; lia). unfold ACtlCutP.flen. exact Hcls. }
      destruct (w4c_cls_close_inv _ _ _ Hcls) as (Hfr' & Hkeep & Hclose & _).
      pose proof (w4c_t_FG_length (ACtlCut.c_in cx) j) as HLst. pose proof (w4c_t_g_length (ACtlCut.c_in cx) j) as HLg.
      pose proof (w4c_fr_fg_n _ _ Hfr') as Hnn.
      destruct (w4c13_fst_bounds (ACtlCut.c_in cx) j) as (Hhave01 & Hnb).
      assert (Hbat6 : Prog.RcFrag.bat (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) 6 = 1).
      { pose proof (w4c_keep_hf _ _ Hkeep) as Hhf. unfold Prog.RcFrag.fg_hf in Hhf.
        destruct (w4c_fok_FG (ACtlCut.c_in cx) j) as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
      pose proof HFS as (_ & _ & _ & _ & HFI).
      destruct (w4c13_fi_nb _ _ HFI Hbat6) as (Hhave1 & Hnbeq).
      assert (HT14 : 14 <= Prog.RcFrag.fg_T (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)).
      { unfold Prog.RcFrag.fg_close in Hclose.
        repeat (apply andb_prop in Hclose; destruct Hclose as [Hclose _]).
        apply Z.leb_le. exact Hclose. }
      destruct (w4c_joined_close _ _ _ HLst HLg (w4c_fok_FG (ACtlCut.c_in cx) j) HFI Hbat6 Hnn HT14) as (E17 & E18').
      assert (HU : ACtlCutP.u16 mem' (fr + 256)
                     (Prog.RcFrag.fg_addr (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j))).
      { pose proof FGM as FGM'. change (ACtlCutP.FGA.fg_mem (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304)
          (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) (ACtlCutP.frcl cx j fr phi) mem')
          in FGM'.
        rewrite HCfrcl in FGM'. cbn [B.Prog.reac_ctrl_identity_fragment_c.fg_mem] in FGM'.
        destruct FGM' as (_ & Hpa & _ & _). unfold ACtlCutP.u16. exact Hpa. }
      set (stg := Prog.RcFrag.fg_join (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) in *.
      assert (HADb : 0 <= Prog.RcFrag.fg_addr (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) < 65536).
      { unfold Prog.RcFrag.fg_addr. fold stg.
        pose proof (w4c13_bat_nonneg stg 17). pose proof (w4c13_bat_lt stg 17).
        pose proof (w4c13_bat_nonneg stg 18). pose proof (w4c13_bat_lt stg 18). lia. }
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [rewrite <- E17; split; [apply w4c13_bat_nonneg | apply w4c13_bat_lt]|].
      split; [rewrite <- E18'; split; [apply w4c13_bat_nonneg | apply w4c13_bat_lt]|].
      exists (Prog.RcFrag.fg_addr (ACtlCutP.SM.t_FG (ACtlCut.c_in cx) j) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)).
      split; [exact HU|]. split; [exact HADb|].
      unfold Prog.RcFrag.fg_addr, ACtlCutP.SM.joined_addr. fold stg. rewrite E17, E18'. reflexivity. }
    apply (w4c13_fs9_mem cx j regs3 R' mem3 mem' A HFS9 Hr9 HA0 HA1 E9). intros x Hx. apply KA. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8235c_at j (0x8235c) --S_F14--> B8237c_at j | B82378_at j.
   S_F14 (Seg/F14.v seg_F14 :467): `bltz a0,0x82fa4`; s7 := a0; `bnez s9,0x8237c` (sum_ok); else a2 = 72,
   a0 = [A + 200] = fr + 336, a1 = [A + 208] = fragb fr and the bcmp trampoline @0x82374, returning at 0x82378. *)
Lemma seg_F14 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8237c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82378_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B8235c_at [Z.of_nat j]).
Proof.
  intros POST j H7c H78 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B8235c_at ACtlCutP.fcutp_body ACtlCutP.ixn ACtlCutP.ixz nth]
    in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & H18 & H20 & HFT &
    ((HLK & HFM & HFS) & Ha0 & Hlong & HbL & HaL & HbR & HaR & HFGM & HRECF & HFRBA & HFRX & HFS9)).
  (* ---- the cut's arithmetic: the spill base A, the frame fr, the turn block phi ---- *)
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qh & Q16 & Hshx & Hsaved & Q4088).
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hfr0 : 0 <= fr) by exact (proj1 Qh).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 448 <= 2 ^ 64) by lia.
  assert (Hphi0 : phi <> 0) by exact (proj1 HHB).
  assert (Hfnz : ACtlCutP.fragb fr <> 0) by (unfold ACtlCutP.fragb; lia).
  assert (H256nz : fr + 256 <> 0) by lia.
  assert (H272nz : fr + 272 <> 0) by lia.
  assert (H304nz : fr + 304 <> 0) by lia.
  assert (Hrr : 0 <= Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi) <= 1)
    by (unfold ACtlCutP.frcl; apply w4c_fg_ret_range; assumption).
  assert (Htrf : B.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
    by (apply w4c_trf_of_frcl; assumption).
  (* FLV is DERIVED: FLI's five pointer spills, and under t_rf j = 1 the class is FgClose, so the fragment's post
     memory fg_mem (the entry cut's own conjunct) gives [fr + 272] = fragb fr + 19 and [fr + 304] = f_pll. *)
  pose proof HLK as (Hj' & S240 & HOUR & HFLI).
  pose proof HFLI as (F27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 &
    S192 & S200 & S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & HSTK & HRAD & HKNT & S168b & S88).
  assert (HFLV : ACtlCutP.FLV cx fr j regs3 mem3).
  { split; [exact S120|]. split; [exact S128|]. split; [exact S256|]. split; [exact S304|]. split; [exact S296|].
    intros Hrf. rewrite Htrf in Hrf.
    pose proof HFGM as HG. rewrite (w4c_ret1_close _ Hrf) in HG. cbn [ACtlCutP.FGA.fg_mem] in HG.
    destruct HG as (_ & _ & Hpp & Hpn). split; [exact Hpp | exact Hpn]. }
  pose proof HFM as (S184 & H24 & H22 & H25 & S312).
  (* ---- the journal's world facts ---- *)
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & Hkp1 & Hkp2 & Hkp3 & Hkp4 & Hgone &
    Hwinpres & Hstkok & _).
  destruct Hstkok as (Hcsp16 & HSTK0 & Hcl & Hlolo & Hhihi & H47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hcv0 Hcv1] _].
  unfold Reusable.YCfn.LLVMF_STK in Hlolo, Hwinpres.
  assert (Hceil : lib.Reusable.YM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx) by lia.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4c_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfal & Hfapp & Hfby & Hfsh).
  rewrite Efr in Hfapp, Hfby, Hfsh.
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite E6 in Hfapp, Hfby, Hfsh.
  assert (Esha : Reusable.YG0f.shadow_addr fr = B.AsanRT.shadow_addr fr)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Esha in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (Hfrceil : fr + 4096 <= lib.Reusable.YM05.alloc_ceiling) by lia.
  assert (Hfr8 : fr mod 8 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfr32, Z.add_0_r in D.
    rewrite D. replace (32 * (fr / 32)) with (4 * (fr / 32) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Vfr : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (proj1 (Hfby x Hx)))).
  assert (Pfs : forall s, B.AsanRT.shadow_addr fr <= s < B.AsanRT.shadow_addr fr + 512 ->
            Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 s).
  { intros s Hs. change (4096 / 8) with 512 in Hfsh.
    pose proof (Hfsh (s - B.AsanRT.shadow_addr fr) ltac:(lia)) as HH.
    replace (B.AsanRT.shadow_addr fr + (s - B.AsanRT.shadow_addr fr)) with s in HH by lia.
    exact (proj1 HH). }
  assert (Hshrng : forall x, fr <= x < fr + 4096 ->
            B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr x < B.AsanRT.shadow_addr fr + 512).
  { intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    pose proof (Z.div_le_mono fr x 8 ltac:(lia) ltac:(lia)) as Hdv1.
    pose proof (Z.div_le_mono x (fr + 7 + 511 * 8) 8 ltac:(lia) ltac:(lia)) as Hdv2.
    rewrite (Z.div_add (fr + 7) 511 8 ltac:(lia)) in Hdv2.
    assert (E7 : (fr + 7) / 8 = fr / 8) by (Z.div_mod_to_equations; lia).
    lia. }
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hpn0).
  destruct (Reusable.YG0d.al_shadow segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (Hbsh & Hbhull).
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as (Hrq1 & Hrq2).
  destruct (B.ProgBridge.img_vis_W W3) as (Himg0 & Himg1 & Himgv).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg0, Himg1, Himgv.
  (* ---- the two arms of `bnez s9,0x8237c` ---- *)
  destruct (B.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j) eqn:Esum.
  - (* ================= sum_ok: the branch is taken, no memory access ================= *)
    rewrite ?Esum in H25. change (B.Prog.SlotModel.b2z true) with 1 in H25.
    change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8235c_at [Z.of_nat j])) with 0x8235c.
    rewrite B.ProgBridge.cfg_at_MS.
    apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
             (Z_to_bv 64 0x8235c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
      [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
    (* SINK 0x8235c (`bltz a0,0x82fa4`) not taken: a0 = fg_ret in {0, 1} (the body). *)
    eapply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 (fun _ _ => False)).
    + apply B.ProgBridge.fevt_of_evtF. unfold lib.Lib.Regs6ss.mkR_of.
      apply (F14F.f14_evt_10_F (fun _ _ => False)) with
        (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)) (v := 1);
        [exact Ha0 | exact Hrr | exact H25 | lia | lia].
    + intros a nn Hr. destruct Hr.
    + intros ms' md' Hms Hsbm. cbv beta in Hms. subst ms'.
      match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R' := R) end.
      assert (E2 : lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
      assert (E3 : lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
      assert (E4 : lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
      assert (E8 : lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
      assert (E9 : lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
      assert (E18 : lib.Reusable.YK11.getr R' 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
      assert (E19 : lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
      assert (E20 : lib.Reusable.YK11.getr R' 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
      assert (E22 : lib.Reusable.YK11.getr R' 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
      assert (E24 : lib.Reusable.YK11.getr R' 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
      assert (E25 : lib.Reusable.YK11.getr R' 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
      assert (E26 : lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
      assert (E27 : lib.Reusable.YK11.getr R' 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
      assert (E23 : lib.Reusable.YK11.getr R' 23 = Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)))
        by reflexivity.
      assert (HJ' : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                      (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                      (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
      { eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
          [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
          | exact Hsbm | intros a Ha; destruct Ha]. }
      change (Reusable.YA0n.SRr segs W3
                (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8237c_at [Z.of_nat j])) R' mem3 md')
                (POST cx)).
      apply (H7c cx [Z.of_nat j] fr k ly3 S3 W3 R' mem3 md' HB HJ' HF HL Hk); [| exact Hrt].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B8237c_at ACtlCutP.fcutp_body
        ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact (w4c_frac_move cx fr fr regs3 R' mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
      split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
      split; [exact (w4c_fturn_move cx j phi regs3 R' mem3 HFT E9)|].
      split; [exact (w4c_lk_move cx fr j regs3 R' mem3 HLK E9 E27)|].
      split; [exact (w4c_flv_move cx fr j regs3 R' mem3 HFLV E9)|].
      split; [exact (w4c_fm_move cx j phi fr regs3 R' mem3 HFM E9 E22 E24 E25)|].
      split; [exact HFS|].
      split; [exact E23|].
      split; [exact HRECF|].
      split; [exact (w4c_frba_move cx j fr phi regs3 R' mem3 HFRBA E2 E9)|].
      split; [exact HFRX | exact (w4c_fs9_move cx j regs3 R' mem3 HFS9 E9)].
  - (* ============== not sum_ok: the bcmp trampoline on the two 72-byte records ============== *)
    rewrite ?Esum in H25. change (B.Prog.SlotModel.b2z false) with 0 in H25.
    pose proof (w4c_spill_q64 regs3 mem3 200 _ A S200 Hr9 HA0 HA1 ltac:(lia)) as Q200.
    pose proof (w4c_spill_q64 regs3 mem3 208 _ A S208 Hr9 HA0 HA1 ltac:(lia)) as Q208.
    pose proof (w4c_spill_q64 regs3 mem3 112 _ A S112 Hr9 HA0 HA1 ltac:(lia)) as Q112.
    pose proof (w4c_spill_q64 regs3 mem3 96 _ A S96 Hr9 HA0 HA1 ltac:(lia)) as Q96.
    (* the fragment class of the turn is FgNone, so the record is the one the copy at fr + 336 holds *)
    assert (HC : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgNone).
    { unfold ACtlCutP.frcl. rewrite Prog.RcFragLib.rf_class_nn by (unfold ACtlCutP.fragb; lia).
      unfold ACtlCutP.flen. rewrite (w4c_sum_ok_false_fr _ _ Esum). reflexivity. }
    assert (Hfrrec : ACtlCutP.frrec cx j fr phi = B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j).
    { unfold ACtlCutP.frrec. rewrite HC. reflexivity. }
    set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
    assert (Gwin : forall off, 0 <= off <= 440 -> lib.Lib.ExecF.rng RNG (A + off) 8).
    { intros off Hoff. apply B.ProgBridge.rng_of_visible.
      eapply w4c_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]. }
    change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8235c_at [Z.of_nat j])) with 0x8235c.
    rewrite B.ProgBridge.cfg_at_MS.
    apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
             (Z_to_bv 64 0x8235c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
      [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
    (* the pre-call stretch 0x8235c -> BCMP_WRAP: the two spill loads only *)
    eapply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 RNG).
    + apply B.ProgBridge.fevt_of_evtF. unfold lib.Lib.Regs6ss.mkR_of.
      apply (F14F.f14_evt_0c_pre_F RNG) with (A := A) (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
        (L := fr + 336) (R := ACtlCutP.fragb fr).
      * exact Hr9.
      * exact Ha0.
      * exact Hrr.
      * lia.
      * unfold ACtlCutP.fragb; lia.
      * exact H25.
      * exact Q200.
      * exact Q208.
      * exact (Gwin 200 ltac:(lia)).
      * exact (Gwin 208 ltac:(lia)).
    + exact (B.ProgBridge.fp_avoids_RNG_W _).
    + intros ms' md' Hms Hsbm. cbv beta in Hms. subst ms'.
      match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R) end.
      assert (E2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
      assert (E3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
      assert (E4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
      assert (E8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
      assert (E9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
      assert (E18 : lib.Reusable.YK11.getr R1 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
      assert (E19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
      assert (E20 : lib.Reusable.YK11.getr R1 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
      assert (E22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
      assert (E24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
      assert (E25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
      assert (E26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
      assert (E27 : lib.Reusable.YK11.getr R1 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
      assert (E23 : lib.Reusable.YK11.getr R1 23 = Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)))
        by reflexivity.
      assert (EspZ : Reusable.YG0d.spZ R1 = sp) by (unfold Reusable.YG0d.spZ; rewrite E2; exact HspZ).
      assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                      (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                      (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
      { eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
          [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
          | exact Hsbm | intros a Ha; destruct Ha]. }
      pose proof HB as ((HAFN & _) & _).
      pose proof HAFN as (_ & _ & _ & Hgp & _).
      rewrite <- B_bcmp_tramp_at.
      change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs B_bcmp_tramp_entry R1 mem3 md') (POST cx)).
      eapply Reusable.YA0n.SRr_bind.
      { eapply (Reusable.YCbq.aj_bcmp_at segs B LAWS segs_low B_bcmp_tramp_entry H_bcmp W3 R1 mem3
                  Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
                  (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md' k
                  (fr + 336) (ACtlCutP.fragb fr) 72 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82378) HJ1).
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - lia.
        - lia.
        - lia.
        - unfold ACtlCutP.fragb; lia.
        - unfold ACtlCutP.fragb; lia.
        - rewrite EspZ; lia.
        - rewrite Zminus_mod, Hsp16, Hcsp16. reflexivity.
        - lia.
        - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
        - rewrite E3, Hr3. exact Hgp.
        - rewrite E4. exact Hr4.
        - reflexivity.
        - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
        - intros a Ha. split;
            [exact (w4c14_aview_of_apresent W3 mem3 a (proj1 (Hfby a ltac:(lia))))
            | rewrite EspZ; unfold Reusable.YG0d.ESTACK; lia].
        - intros a Ha. unfold ACtlCutP.fragb in Ha. split;
            [exact (w4c14_aview_of_apresent W3 mem3 a (proj1 (Hfby a ltac:(lia))))
            | rewrite EspZ; unfold Reusable.YG0d.ESTACK; lia].
        - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
        - intros a Ha. unfold ACtlCutP.fragb in Ha. unfold Reusable.YG0d.ESTACK. lia.
        - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
            Reusable.YG0f.kHighMemEnd. destruct Hfapp as (Hf1 & [Hf2 | (Hf2 & Hf3)]); [left | right]; lia.
        - unfold ACtlCutP.fragb, Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
            Reusable.YG0f.kHighMemEnd. destruct Hfapp as (Hf1 & [Hf2 | (Hf2 & Hf3)]); [left | right]; lia.
        - apply (w4c14_ra_of_addr W3 mem3 (fr + 336) 72 HaL). intros i Hi.
          apply (w4c14_vis_of_aview W3 mem3). apply w4c14_aview_of_apresent. apply Pfs. apply Hshrng. lia.
        - intros _. apply (w4c14_hull_of_pres W3 mem3). intros s Hs. apply Pfs.
          exact (w4c14_hull_in fr (fr + 336) 72 s Hfr8 Hfr0 ltac:(lia) ltac:(lia) ltac:(lia) Hs).
        - apply (w4c14_ra_of_addr W3 mem3 (ACtlCutP.fragb fr) 72 HaR). intros i Hi.
          apply (w4c14_vis_of_aview W3 mem3). apply w4c14_aview_of_apresent. apply Pfs. apply Hshrng.
          unfold ACtlCutP.fragb. lia.
        - intros _. apply (w4c14_hull_of_pres W3 mem3). intros s Hs. apply Pfs.
          exact (w4c14_hull_in fr (ACtlCutP.fragb fr) 72 s Hfr8 Hfr0 ltac:(unfold ACtlCutP.fragb; lia)
                   ltac:(unfold ACtlCutP.fragb; lia) ltac:(lia) Hs). }
      cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & mdP & v & -> & HJ2 & HPres2 & Ha02 & Hiff & Hfrpost &
        Hprespost).
      (* the compare result is 0: the copy at fr + 336 and the record at fragb fr hold the same 72 bytes *)
      assert (Hv0 : v = Reusable.YG0d.w64 0).
      { apply Hiff. intros i Hi.
        pose proof HbL as HbL0. destruct HbL0 as (_ & _ & HbL').
        pose proof HbR as HbR0. rewrite Hfrrec in HbR0. destruct HbR0 as (_ & _ & HbR').
        pose proof (HbL' (Z.to_nat i) ltac:(rewrite w4c_t_FG_length; lia)) as EL.
        pose proof (HbR' (Z.to_nat i) ltac:(rewrite w4c_t_FG_length; lia)) as ER.
        rewrite Z2Nat.id in EL, ER by lia.
        rewrite (w4c14_aview_mrd W3 mem3 (fr + 336 + i) (Vfr (fr + 336 + i) ltac:(lia))).
        rewrite (w4c14_aview_mrd W3 mem3 (ACtlCutP.fragb fr + i)
                  (Vfr (ACtlCutP.fragb fr + i) ltac:(unfold ACtlCutP.fragb; lia))).
        f_equal.
        transitivity (nth_error (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (Z.to_nat i));
          [exact EL | symmetry; exact ER]. }
      (* the callee-saved registers *)
      assert (Kg2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
        by exact (eq_trans (HPres2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E2).
      assert (Kg3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
        by exact (eq_trans (HPres2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E3).
      assert (Kg4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
        by exact (eq_trans (HPres2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E4).
      assert (Kg8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
        by exact (eq_trans (HPres2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E8).
      assert (Kg9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
        by exact (eq_trans (HPres2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E9).
      assert (Kg18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
        by exact (eq_trans (HPres2 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E18).
      assert (Kg19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
        by exact (eq_trans (HPres2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E19).
      assert (Kg20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
        by exact (eq_trans (HPres2 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E20).
      assert (Kg22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
        by exact (eq_trans (HPres2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E22).
      assert (Kg24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
        by exact (eq_trans (HPres2 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E24).
      assert (Kg25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
        by exact (eq_trans (HPres2 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E25).
      assert (Kg26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
        by exact (eq_trans (HPres2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E26).
      assert (Kg27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
        by exact (eq_trans (HPres2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E27).
      assert (Kg23 : lib.Reusable.YK11.getr regs2 23 =
                    Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)))
        by exact (eq_trans (HPres2 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) E23).
      assert (EspZ2 : Reusable.YG0d.spZ regs2 = Reusable.YG0d.spZ regs3)
        by (unfold Reusable.YG0d.spZ; rewrite Kg2; reflexivity).
      (* B.ProgWorld.ctl_post_bcmp turns the call's world post into raw-memory facts at visible addresses *)
      assert (RTP' : (forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside [(sp - 2 * Reusable.YG0d.ESTACK, sp)] a ->
                        Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a =
                        Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a) /\
                     (forall a, Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a ->
                        Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem2 a)).
      { split; [|exact Hprespost].
        intros a Ha Ho. apply Hfrpost; [exact Ha|].
        cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho & _). lia. }
      destruct (B.ProgWorld.ctl_post_bcmp W3 mem3 mem2 sp RTP') as (MV & WV).
      unfold B.ProgWorld.munch_vis, B.ProgWorld.wmono_vis in MV, WV.
      assert (AGRv : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
                       (x < sp - 2 * Reusable.YG0d.ESTACK \/ sp <= x) ->
                       lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                       lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx Hv Ho. apply (MV (Z_to_bv 64 x) Hv).
        rewrite lib.Lib.MState.unsigned_lit by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
      assert (Hest : Reusable.YG0d.ESTACK = 4096) by reflexivity.
      assert (Edc : 140737479966720 / 8 = 17592184995840) by reflexivity.
      assert (Hfd8 : fr / 8 <= 17592184995840).
      { pose proof (Z.div_le_mono fr 140737479966720 8 ltac:(lia) ltac:(lia)) as Dfr. lia. }
      assert (Hpd8 : phi / 8 <= 17592184995840).
      { pose proof (Z.div_le_mono phi 140737479966720 8 ltac:(lia) ltac:(lia)) as Dphi. lia. }
      assert (KA : forall x, A <= x < A + 448 -> lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. apply AGRv; [lia | exact (proj1 (Hwinpres x ltac:(lia))) | right; lia]. }
      assert (KV : forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx ->
                     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. apply AGRv; [lia | exact (proj1 (Hwinpres x ltac:(lia))) | right; lia]. }
      assert (KF : forall x, fr <= x < fr + 4096 -> lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. apply AGRv; [lia | exact (Vfr x Hx) | left; lia]. }
      assert (KS : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 ->
                     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx.
        apply AGRv; [lia | exact (w4c14_vis_of_aview W3 mem3 _ (w4c14_aview_of_apresent W3 mem3 _
            (Pfs x ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)))) | left; lia]. }
      assert (KFS : forall x, fr <= x < fr + 4096 ->
                      lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 (B.AsanRT.shadow_addr x)) =
                      lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr x)))
        by (intros x Hx; apply KS; exact (Hshrng x Hx)).
      assert (KP : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
                     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. apply AGRv; [lia | exact (proj1 (proj1 (Hppres x Hx))) | left; lia]. }
      assert (KPS : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
                      lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 (B.AsanRT.shadow_addr x)) =
                      lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr x))).
      { intros x Hx.
        assert (Hsx : B.AsanRT.shadow_addr x <= 17592184995840 + 2147450880).
        { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
          pose proof (Z.div_le_mono phi x 8 ltac:(lia) ltac:(lia)).
          pose proof (Z.div_le_upper_bound x 8 17592184995840 ltac:(lia) ltac:(lia)). lia. }
        apply AGRv.
        - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
          pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
        - apply (w4c14_vis_of_aview W3 mem3). apply Hbhull. apply w4c14_sh_in_hull; lia.
        - left. lia. }
      assert (KI : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 ->
                     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) =
                     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
      { intros x Hx. change ACtlCutP.KNA.KIND_NAME with 652672 in Hx. apply AGRv.
        - lia.
        - apply Himgv. lia.
        - left. lia. }
      assert (WMfr : forall x, fr <= x < fr + 4096 -> wview B.Img0.rsegs mem3 (Z_to_bv 64 x) <> None ->
                       wview B.Img0.rsegs mem2 (Z_to_bv 64 x) <> None)
        by (intros x Hx Hw; exact (WV (Z_to_bv 64 x) (Vfr x Hx) Hw)).
      assert (HKN2 : B.AsanRT.addressable mem2 ACtlCutP.KNA.KIND_NAME 112)
        by exact (ctl_kind_name_addressable ly3 S3 W3 mem2 mdP (proj1 HJ2)).
      assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
      { apply (w4c14_stk_keep mem3 mem2 fr (fr + ACtlCutP.FRAME_BYTES) HSTK).
        - intros x Hx Hw. apply WMfr; [unfold ACtlCutP.FRAME_BYTES in Hx; lia | exact Hw].
        - intros x Hx. apply KF. unfold ACtlCutP.FRAME_BYTES in Hx. lia. }
      (* the FRBA spill base is the FRAC spill base *)
      destruct HFRBA as (A0 & H9b & HA0b & HFRB).
      assert (EA0 : A0 = A).
      { apply w4c_lit_inj; [exact HA0b | lia |].
        unfold ACtlCut.rgv in Hr9, H9b. rewrite <- Hr9, <- H9b. reflexivity. }
      subst A0.
      (* the successor cut 0x82378 *)
      apply (H78 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 mdP HB HJ2 HF HL Hk);
        [| exact (w4c_ctlrt cx (ACtlCut.own6 cx) ly3 S3 W3 mem2 mdP k HB HJ2)].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82378_at ACtlCutP.fcutp_body
        ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split.
      { apply (w4c14_frac_keep cx fr fr regs3 regs2 mem3 mem2 A HFRAC Hr9 HA0 HA1 Hfr0
                 Kg2 Kg3 Kg4 Kg8 Kg9 Kg19 Kg26 KA KF KS KV). }
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|].
      split.
      { apply (w4c14_hb_keep mem3 mem2 phi (ACtlCutP.flen cx j) HHB).
        intros i Hi. apply KPS. unfold B.ACtlK.a_size in Hi. lia. }
      split; [unfold ACtlCut.rgv in *; rewrite Kg18; exact H18|].
      split; [unfold ACtlCut.rgv in *; rewrite Kg20; exact H20|].
      split.
      { apply (w4c14_fturn_keep cx j phi regs3 regs2 mem3 mem2 A HFT Hr9 HA0 HA1 Kg9).
        - intros x Hx. apply KA. lia.
        - intros x Hx. apply KP. unfold ACtlCutP.flen in *. lia. }
      split.
      { exact (w4c14_lk_keep cx fr j regs3 regs2 mem3 mem2 A HLK Hr9 HA0 HA1 Hfr0 Kg9 Kg27 KA KF KFS KI HKN2 HSTK2). }
      split.
      { exact (w4c14_flv_keep cx fr j regs3 regs2 mem3 mem2 A HFLV Hr9 HA0 HA1 Hfr0 Kg9 KA KF). }
      split.
      { exact (w4c14_fm_keep cx j phi fr regs3 regs2 mem3 mem2 A HFM Hr9 HA0 HA1 Kg9 Kg22 Kg24 Kg25 KA). }
      split.
      { exact (w4c14_fsj_keep cx fr j regs3 regs2 mem3 mem2 HFS Hfr0 KF KFS). }
      split; [exact Kg23|].
      split; [exact Esum|].
      split.
      { exists 0. split.
        - rewrite Hfrrec. apply w4c14_memcmp_self. rewrite w4c_t_FG_length. lia.
        - unfold ACtlCut.rgv. rewrite Ha02, Hv0. reflexivity. }
      split; [exact (w4c14_recf_keep cx fr j mem3 mem2 HRECF Hfr0 KF)|].
      split.
      { exists A. split; [unfold ACtlCut.rgv in *; rewrite Kg9; exact H9b|]. split; [exact HA0b|].
        apply (w4c14_frb_keep cx j fr phi A regs3 regs2 mem3 mem2 HFRB EspZ2 Hfr0 ltac:(lia) Q112 Q96 KA KF KFS).
        - intros x H50 Hx. apply KP. lia.
        - intros x H50 Hx. apply KPS. lia. }
      split.
      { apply (w4c14_frx_keep cx j fr phi mem3 mem2 HFRX Hfr0 KF KFS).
        - intros x H50 Hx. apply KP. lia.
        - intros x H50 Hx. apply KPS. lia.
        - intros x Hx Hw. apply WMfr; [lia | exact Hw]. }
      { exact (w4c14_fs9_keep cx j regs3 regs2 mem3 mem2 A HFS9 Hr9 HA0 HA1 Kg9 KA). }
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82378_at j (0x82378) --S_F15--> B8237c_at j.
   S_F15 (Seg/F15.v seg_F15 :687): `bnez a0,0x82fa4` not taken, fall through to 0x8237c. *)
Lemma seg_F15 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8237c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82378_at [Z.of_nat j]).
Proof.
  (* Plan (kept):
     intros POST j H7c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk (-> & HBODY) HRT.
     1. SINK 0x82378 (`bnez a0,0x82fa4`): not taken: the cut carries t_sum_ok j = false, which makes fg_fr false, so
        the fragment class of the turn is FgNone: the fragment call left the record as it was and the 72-byte compare
        of the copy against the record gives 0 (F15.v's header).  Step of F15F.seg_F15_F (0x82378 -> 0x8237c; no write).
     2. Apply H7c at cx, [Z.of_nat j], fr, k: C_B8237c_at's body is C_B82378_at's minus the compare facts. *)
  intros POST j H7c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82378_at ACtlCutP.fcutp_body ACtlCutP.ixn ACtlCutP.ixz nth]
    in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & H18 & H20 & HFT & HLK & HFLV & HFM & HFS & H23 & Hsum &
    (vcmp & Hmm & Ha0) & HRECF & HFRBA & HFRX & HFS9).
  (* the fragment class of the turn is FgNone (t_sum_ok j = false makes fg_fr false), so the record is the one the
     copy at fr + 336 holds and the 72-byte compare gives 0 *)
  assert (Hfr0 : 0 <= fr).
  { destruct HFRAC as (A & sp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      (Hq0 & _) & _). exact Hq0. }
  assert (Hphi0 : phi <> 0) by exact (proj1 HHB).
  assert (HC : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgNone).
  { unfold ACtlCutP.frcl. rewrite Prog.RcFragLib.rf_class_nn by (unfold ACtlCutP.fragb; lia).
    unfold ACtlCutP.flen. rewrite (w4c_sum_ok_false_fr _ _ Hsum). reflexivity. }
  unfold ACtlCutP.frrec in Hmm. rewrite HC in Hmm. cbn [B.Prog.SlotModel.fg_next] in Hmm.
  apply w4c_memcmp_self_eq in Hmm. subst vcmp.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82378_at [Z.of_nat j])) with 0x82378.
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82378) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* SINK 0x82378 (`bnez a0,0x82fa4`) not taken: a0 = 0.  No memory access: empty footprint. *)
  eapply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 (fun _ _ => False)).
  - apply B.ProgBridge.fevt_of_evtF. unfold lib.Lib.Regs6ss.mkR_of. eapply F15F.seg_F15_F. exact Ha0.
  - intros a n Hr. destruct Hr.
  - intros ms' md' Hms Hsbm. cbv beta in Hms. subst ms'.
    eapply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3); [| exact (lib.Lib.Regs6ss.mkR_of_eqv regs3)].
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8237c_at [Z.of_nat j])) regs3 mem3 md')
              (POST cx)).
    apply (H7c cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B8237c_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact HFRAC|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact H18|]. split; [exact H20|]. split; [exact HFT|].
      split; [exact HLK|]. split; [exact HFLV|]. split; [exact HFM|]. split; [exact HFS|].
      split; [exact H23|]. split; [exact HRECF|]. split; [exact HFRBA|]. split; [exact HFRX | exact HFS9].
    + exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8237c_at j (0x8237c) --S_F15b--> B823d8_at j | B82468_at j.
   S_F15b (Seg/F15.v seg_F15b :766): `bne s7,s6,0x82468` (s6 = 1); on fg_ret = 1 (FgClose) the bound checks of the
   closed record (0x82380-0x823d0) and a1 = pll + 5, falling into 0x823d8. *)
Lemma seg_F15b : forall POST (j : nat),
  ctl_from POST (ix_cut C_B823d8_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82468_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B8237c_at [Z.of_nat j]).
Proof.
  (* Plan (kept):
     intros POST j Hd8 H68 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk (-> & HBODY) HRT.
     1. Run F15F.seg_F15b_F (no call, no store; registers a0 .. a4 only).  RNG: the spills [A + 304], [A + 256],
        [A + 296], [A + 128], and the cells [fr + 272, +8), [fr + 304, +8).  fp_avoids: stack window, owned frame.
        fg_ret <> 1: `bne s7,s6` taken -> apply H68 at cx, [Z.of_nat j], fr, k (C_B82468_at's body from the entry's
          FCUTP / FM / FS9 / FSj / rec_inv / RECS: the record not closed this turn).
        fg_ret = 1 (FgClose, t_rf j = 1; FLV's conditional part gives [fr + 272] = fragb fr + 19 = pl and
          [fr + 304] = f_pll = fg_T - 13):
        SINK 0x8238c (`bltu pl, fragb fr + 8`): pl = (fragb fr + 8) + 11.
        SINK 0x8239c (`bltu 64, 11`): false.
        SINK 0x823b4 (`bltu 53, f_pll + 2`): FgClose gives 14 <= fg_T <= 64, so 1 <= f_pll <= 51, f_pll + 2 <= 53.
        TRAP 0x823c0 (T26, F.4.1 row 25) -> 0x82fa0: [A + 256] = fragb fr + 8 = fr + 2776 and FRB gives
          fr + 2840 <= 2^47, so [A + 256] + 11 does not wrap.
        SINK 0x823c8 (`bne [fr + 272], [A + 128]`): both are fragb fr + 19 (FLV, FLI's spill 128).
        TRAP 0x823d0 (T27, row 26): s11 = 2^64 - 8 (FLI's rgv 27 (-8) via LK) and [A + 256] <= 2^47 - 64, so the
          buffer + 7 (the record_sum_closes argument) does not wrap.
        Fall through to 0x823d8 with a1 = pll + 5: apply Hd8 at cx, [Z.of_nat j], fr, k: C_B823d8_at's body (FLV, FM,
        FS9, FSj, FTURN, HB, LK, rec_inv, RECF, a1 = pll + 5, the joined_byte caller facts A0V / A1V). *)
  intros POST j Hd8 H68 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B8237c_at ACtlCutP.fcutp_body ACtlCutP.ixn ACtlCutP.ixz nth]
    in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & H18 & H20 & HFT & HLK & HFLV & HFM & HFS & H23 & HRECF &
    HFRBA & HFRX & HFS9).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qh & Q16 & Hsh & Hsaved & Q4088).
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hfr0 : 0 <= fr) by exact (proj1 Qh).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 448 <= 2 ^ 64) by (rewrite P64; lia).
  assert (Hphi0 : phi <> 0) by exact (proj1 HHB).
  assert (Hnz : ACtlCutP.fragb fr <> 0 /\ fr + 256 <> 0 /\ fr + 272 <> 0 /\ fr + 304 <> 0)
    by (unfold ACtlCutP.fragb; lia).
  destruct Hnz as (Hfnz & H256nz & H272nz & H304nz).
  assert (Hrr : 0 <= Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi) <= 1)
    by (unfold ACtlCutP.frcl; apply w4c_fg_ret_range; assumption).
  assert (Htrf : B.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
    by (apply w4c_trf_of_frcl; assumption).
  (* the registers and spill cells the run reads *)
  pose proof HLK as (Hj' & H240 & HOUR & HFLI).
  pose proof HFLI as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 &
    S200 & S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & _).
  pose proof HFM as (H184 & H24 & H22 & H25 & H312).
  pose proof HFLV as (F120 & F128 & F256 & F304 & F296 & Fcond).
  pose proof (w4c_spill_q64 regs3 mem3 128 _ A F128 Hr9 HA0 HA1 ltac:(lia)) as Q128.
  pose proof (w4c_spill_q64 regs3 mem3 256 _ A F256 Hr9 HA0 HA1 ltac:(lia)) as Q256.
  pose proof (w4c_spill_q64 regs3 mem3 304 _ A F304 Hr9 HA0 HA1 ltac:(lia)) as Q304.
  pose proof (w4c_spill_q64 regs3 mem3 296 _ A F296 Hr9 HA0 HA1 ltac:(lia)) as Q296.
  (* the world facts: the reads are visible (the stack window and the owned class-6 frame) *)
  pose proof HJ as (HAR & Hly & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4c_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Gwin : forall off, 0 <= off <= 440 -> lib.Lib.ExecF.rng RNG (A + off) 8).
  { intros off Hoff. apply B.ProgBridge.rng_of_visible.
    eapply w4c_win_vis; [exact HJ | unfold Reusable.YCfn.LLVMF_STK; lia | lia]. }
  assert (Gfr : forall off, 0 <= off <= 4088 -> lib.Lib.ExecF.rng RNG (fr + off) 8).
  { intros off Hoff. apply B.ProgBridge.rng_of_visible.
    eapply w4c_frame_vis; [exact HAR | exact Hin6 | rewrite Efr; lia | rewrite Efr, HFB; lia]. }
  (* the cut's configuration in the run's state form *)
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B8237c_at [Z.of_nat j])) with 0x8237c.
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8237c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* S_F15b: `bne s7,s6` and, on a closing turn, the four record checks (SINK 0x8238c, 0x8239c, 0x823b4, 0x823c8)
     and the two arithmetic checks (TRAP T26 0x823c0, T27 0x823d0), all not taken inside the run *)
  eapply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 RNG).
  - apply B.ProgBridge.fevt_of_evtF. unfold lib.Lib.Regs6ss.mkR_of.
    apply (F15F.seg_F15b_F RNG) with (A := A) (q := ACtlCutP.fragb fr + 8) (pl := ACtlCutP.fragb fr + 19)
      (pp := fr + 272) (pn := fr + 304)
      (pll := B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))
      (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)).
    + exact Hr9.
    + exact H22.
    + exact H23.
    + exact H27.
    + exact Hrr.
    + exact HA0.
    + lia.
    + unfold ACtlCutP.fragb; lia.
    + unfold ACtlCutP.fragb; lia.
    + lia.
    + exact Q128.
    + exact Q256.
    + exact Q304.
    + exact Q296.
    + intros Hc. rewrite <- Htrf in Hc. destruct (Fcond Hc) as (Hpp & _).
      split; [lia|]. split; [lia | exact Hpp].
    + intros Hc. rewrite <- Htrf in Hc. destruct (Fcond Hc) as (_ & Hpn).
      split; [lia|]. split; [lia | exact Hpn].
    + intros Hc. apply w4c_ret1_close in Hc. unfold ACtlCutP.frcl in Hc.
      pose proof (w4c_close_T _ _ _ _ _ _ _ _ Hc) as HT. unfold B.Prog.SlotModel.f_pll. lia.
    + exact (Gwin 128 ltac:(lia)).
    + exact (Gwin 256 ltac:(lia)).
    + exact (Gwin 296 ltac:(lia)).
    + exact (Gwin 304 ltac:(lia)).
    + intros _. exact (Gfr 272 ltac:(lia)).
    + intros _. exact (Gfr 304 ltac:(lia)).
  - exact (B.ProgBridge.fp_avoids_RNG_W _).
  - intros ms' md' Hms Hsbm. cbv beta in Hms.
    destruct Hms as (a0' & a1' & a2' & a3' & a4' & pc' & -> & Hcase).
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R' := R) end.
    assert (E2 : lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
    assert (E3 : lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
    assert (E4 : lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
    assert (E8 : lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
    assert (E9 : lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
    assert (E18 : lib.Reusable.YK11.getr R' 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
    assert (E19 : lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
    assert (E20 : lib.Reusable.YK11.getr R' 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
    assert (E22 : lib.Reusable.YK11.getr R' 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
    assert (E24 : lib.Reusable.YK11.getr R' 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
    assert (E25 : lib.Reusable.YK11.getr R' 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
    assert (E26 : lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
    assert (E27 : lib.Reusable.YK11.getr R' 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
    assert (E11 : lib.Reusable.YK11.getr R' 11 = a1') by reflexivity.
    assert (Easp : Reusable.YG0d.spZ R' = Reusable.YG0d.spZ regs3) by (unfold Reusable.YG0d.spZ; rewrite E2; reflexivity).
    assert (HJ' : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
    { eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha]. }
    (* the FRBA spill base is the FRAC spill base *)
    destruct HFRBA as (A0 & H9b & HA0b & HFRB).
    assert (EA0 : A0 = A).
    { apply w4c_lit_inj; [exact HA0b | lia |]. unfold ACtlCut.rgv in Hr9, H9b. rewrite <- Hr9, <- H9b. reflexivity. }
    subst A0.
    destruct HFRB as (Hwin & Hw272 & Hkp2880 & HkpBC & Hkp2688 & HphiG & H8819).
    pose proof (w4c_spill_q64 regs3 mem3 280 _ A S280 Hr9 HA0 HA1 ltac:(lia)) as C280.
    destruct Hcase as [(Hpc & Hc & E11') | (Hpc & Hnc)]; subst pc'.
    + (* ---- the turn closes a record: F16's entry 0x823d8 ---- *)
      change (Reusable.YA0n.SRr segs W3
                (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B823d8_at [Z.of_nat j])) R' mem3 md')
                (POST cx)).
      assert (HC : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgClose) by (apply w4c_ret1_close; exact Hc).
      assert (Htrf1 : B.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = 1) by (rewrite Htrf; exact Hc).
      pose proof (w4c_trf1_cls _ _ Htrf1) as Hcls.
      destruct (w4c_cls_close_inv _ _ _ Hcls) as (Hfr' & Hkeep & Hclose & _).
      assert (Hl50 : 50 <= ACtlCutP.flen cx j) by (unfold ACtlCutP.flen; exact (w4c_fr_len50 _ _ Hfr')).
      assert (HT : 14 <= Prog.RcFrag.fg_T (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                          (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) <= 64).
      { pose proof HC as HC'. unfold ACtlCutP.frcl in HC'. exact (w4c_close_T _ _ _ _ _ _ _ _ HC'). }
      set (pll := B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                    (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
      assert (HLr : 1 <= pll <= 51) by (unfold pll, B.Prog.SlotModel.f_pll; lia).
      pose proof (w4c_t_FG_length (ACtlCut.c_in cx) j) as HLst.
      pose proof (w4c_t_g_length (ACtlCut.c_in cx) j) as HLg.
      pose proof (w4c_fr_fg_n _ _ Hfr') as Hnn.
      assert (Efrrec : ACtlCutP.frrec cx j fr phi = B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j).
      { unfold ACtlCutP.frrec, B.Prog.SlotModel.t_FGf, B.Prog.SlotModel.fg_st. f_equal.
        rewrite (w4c_frcl_fcls cx j fr phi) by assumption. unfold ACtlCutP.flen. reflexivity. }
      destruct HFRX as (Hlong & Hrecb & Harec & (idb & Hidbl & Hidc) & HADid & Hrfx).
      destruct (Hlong Hl50) as (Hphib & Haphi & Hphifr).
      rewrite Efrrec in Hrecb.
      destruct (Hrfx Htrf1) as (Hhaveb & Hhavenz & Hnbb & Hj9b & Hj10b & (AD & HADu & HADb & HADj)).
      destruct (Fcond Htrf1) as (Hpp & Hpn).
      destruct (HphiG Hl50) as (HphiA & HphiBC).
      pose proof (w4c_spill_q64 regs3 mem3 120 _ A F120 Hr9 HA0 HA1 ltac:(lia)) as C120.
      pose proof (w4c_spill_q64 regs3 mem3 168 _ A S168 Hr9 HA0 HA1 ltac:(lia)) as C168.
      pose proof (w4c_spill_q64 regs3 mem3 176 _ A S176 Hr9 HA0 HA1 ltac:(lia)) as C176.
      pose proof (w4c_spill_q64 regs3 mem3 288 _ A S288 Hr9 HA0 HA1 ltac:(lia)) as C288.
      assert (Hbig : B.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true)
        by (unfold B.Prog.SlotModel.t_big; apply Z.leb_le; unfold ACtlCutP.flen in Hl50; exact Hl50).
      assert (C312 : ACtlCutP.q64 mem3 (A + 312) (phi + 18)).
      { pose proof H312 as S312. rewrite Hbig in S312.
        exact (w4c_spill_q64 regs3 mem3 312 _ A S312 Hr9 HA0 HA1 ltac:(lia)). }
      pose proof HFS as (Hhave & Hnb8 & Hbody & Haddr40 & HFI).
      assert (Hbat6 : Prog.RcFrag.bat (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) 6 = 1).
      { pose proof (w4c_keep_hf _ _ Hkeep) as Hhf. unfold Prog.RcFrag.fg_hf in Hhf.
        destruct (w4c_fok_FG (ACtlCut.c_in cx) j) as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
      assert (EAD : AD = Prog.RcFrag.fg_addr (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                           (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
      { rewrite HADj. symmetry.
        apply (w4c_fg_addr_joined _ _ _ HLst HLg (w4c_fok_FG (ACtlCut.c_in cx) j) HFI Hbat6 Hnn); lia. }
      apply (Hd8 cx [Z.of_nat j] fr k ly3 S3 W3 R' mem3 md' HB HJ' HF HL Hk); [| exact Hrt].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B823d8_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split; [exact (w4c_frac_move cx fr fr regs3 R' mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4c_lk_move cx fr j regs3 R' mem3 HLK E9 E27)|].
      split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
      split; [exact (proj1 (w4c_fturn_move cx j phi regs3 R' mem3 HFT E9))|].
      split; [exact (w4c_fm_move cx j phi fr regs3 R' mem3 HFM E9 E22 E24 E25)|].
      split; [exact HFS|].
      split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
      split; [unfold ACtlCut.rgv in *; rewrite E27; exact H27|].
      split; [exact Haphi|].
      split.
      { exists (firstn 38 (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)). split; [exact (w4c_ba_firstn mem3 phi _ 38 Hphib)|].
        rewrite length_firstn, HLg. reflexivity. }
      split.
      { exists A, (fr + 176).
        split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr9|].
        split; [exact C280|].
        split; [unfold ACtlCut.rgv in *; rewrite E24; exact H24|].
        split; [lia|]. split; [rewrite Easp, HspZ; lia|]. split; [unfold ACtlCutP.FRAME_BYTES; lia|].
        split; [exact Hwin|]. split; [exact Hw272|].
        split; [exact HphiA|]. split; [exact Hkp2880|].
        split; [rewrite Easp; exact HphiBC|]. split; [rewrite Easp; exact HkpBC|].
        split; [destruct Hphifr as [Hd|Hd]; [left|right]; unfold ACtlCutP.FRAME_BYTES in *; lia|].
        split; [exact Hkp2688|].
        split.
        { intros H8. destruct (H8819 H8) as (HRI & HL1 & HL2). rewrite Easp.
          split; [exact HRI|]. split; [exact HL1 | exact HL2]. }
        split.
        { exists (pll + 5), (firstn (Z.to_nat (pll + 5)) (skipn 15 (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j))).
          split; [unfold ACtlCut.rgv; rewrite E11; exact E11'|].
          split; [exact C120|].
          split; [lia|].
          split; [unfold ACtlCutP.fragb, ACtlCutP.FRAME_BYTES; lia|].
          split.
          { pose proof (w4c_ba_skipn mem3 (ACtlCutP.fragb fr) (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 15
                          ltac:(rewrite w4c_t_FGf_length; lia) Hrecb) as HS.
            change (Z.of_nat 15) with 15 in HS. exact (w4c_ba_firstn mem3 _ _ _ HS). }
          split; [rewrite length_firstn, length_skipn, w4c_t_FGf_length; lia|].
          split.
          { replace (pll + 5) with (Prog.RcFrag.fg_T (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                                      (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) - 8)
              by (unfold pll, B.Prog.SlotModel.f_pll; lia).
            exact (w4c_sum_closes (ACtlCut.c_in cx) j Htrf1). }
          apply (B.AsanRTFacts.addressable_sub mem3 (ACtlCutP.fragb fr) 72 15 _ Harec); lia. }
        split.
        { exists (B.Prog.SlotModel.fs_have (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)),
                 (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)), AD, (fr + 2880), (phi + 18).
          split; [exact Hhave|]. split; [exact Hhavenz|]. split; [exact Hhaveb|].
          split; [exact Hnb8|]. split; [lia|].
          split; [exact C168|]. split; [reflexivity|].
          split; [exact C312|]. split; [reflexivity|].
          split; [exact C288|]. split; [exact HADu|]. split; [exact HADb | exact HADj]. }
        exists pll, idb, (firstn (Z.to_nat pll) (skipn 19 (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j))).
        split; [exact Q304|]. split; [exact Hpp|]. split; [exact Q296|]. split; [exact Hpn|].
        split; [exact C176|]. split; [lia|]. split; [unfold ACtlCutP.fragb, ACtlCutP.FRAME_BYTES; lia|].
        split; [rewrite length_firstn, length_skipn, w4c_t_FGf_length; lia|].
        split.
        { pose proof (w4c_ba_skipn mem3 (ACtlCutP.fragb fr) (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19
                        ltac:(rewrite w4c_t_FGf_length; lia) Hrecb) as HS.
          change (Z.of_nat 19) with 19 in HS. exact (w4c_ba_firstn mem3 _ _ _ HS). }
        split; [apply (B.AsanRTFacts.addressable_sub mem3 (ACtlCutP.fragb fr) 72 19 _ Harec); lia|].
        split; [exact Hidbl|]. split; [exact Hidc | exact HADid]. }
      split; [exact (w4c_flv_move cx fr j regs3 R' mem3 HFLV E9)|].
      split; [exact Htrf1|].
      split; [unfold ACtlCut.rgv; rewrite E11; exact E11'|].
      split; [exact Hrecb|]. split; [exact Harec|].
      split; [apply w4c_fok_FG|].
      split; [rewrite <- EAD; exact HADu|].
      split; [exists idb; split; [exact (w4c_lrw38 mem3 _ _ Hidc) | exact Hidbl]|].
      split; [exact (w4c_fturn_move cx j phi regs3 R' mem3 HFT E9)|].
      split; [exact HRECF | exact (w4c_fs9_move cx j regs3 R' mem3 HFS9 E9)].
    + (* ---- the turn closes no record: the F17 split cut 0x82468 ---- *)
      change (Reusable.YA0n.SRr segs W3
                (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82468_at [Z.of_nat j])) R' mem3 md')
                (POST cx)).
      apply (H68 cx [Z.of_nat j] fr k ly3 S3 W3 R' mem3 md' HB HJ' HF HL Hk); [| exact Hrt].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82468_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact (w4c_frac_move cx fr fr regs3 R' mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
      split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
      split; [exact (w4c_fturn_move cx j phi regs3 R' mem3 HFT E9)|].
      split; [exact (w4c_lk_move cx fr j regs3 R' mem3 HLK E9 E27)|].
      split; [exact (w4c_fm_move cx j phi fr regs3 R' mem3 HFM E9 E22 E24 E25)|].
      split; [exact HFS|].
      split.
      { intros Hl. destruct HFRX as (Hlong & _). destruct (Hlong Hl) as (Hg & Ha & _).
        split; [exact Ha|].
        exists (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j). split; [exact Hg | rewrite w4c_t_g_length; lia]. }
      split; [unfold ACtlCut.rgv in *; rewrite E27; exact H27|].
      split.
      { exists A, (fr + 176).
        split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr9|].
        split; [exact C280|]. split; [exact Hwin|]. split; [exact Hw272|].
        split; [unfold ACtlCut.rgv in *; rewrite E24; exact H24|].
        split; [exact Hkp2880|]. split; [rewrite Easp; exact HkpBC|].
        split.
        { intros Hl. destruct (HphiG Hl) as (HpA & HpBC). split; [exact HpA | rewrite Easp; exact HpBC]. }
        intros H8. destruct (H8819 H8) as (HRI &
            (L & ls & rs & QL & HBL1 & HLl & HBR1 & HLr & Hmm1 & HAL1 & Hap6 & Hap7 & HLBC & HLA & _) &
            (L2 & ls2 & rs2 & QL2 & HBL2 & HLl2 & HBR2 & HLr2 & Hmm2 & HAL2 & Hap62 & Hap72 & HL2BC & HL2A & _)).
        split; [exact HRI|]. split.
        - exists L, ls, rs.
          split; [exact QL|]. split; [exact HBL1|]. split; [lia|]. split; [exact HBR1|]. split; [lia|].
          split; [exact Hmm1|]. split; [exact HAL1|]. split; [exact Hap6|]. split; [exact Hap7|].
          split; [rewrite Easp; exact HLBC | exact HLA].
        - exists L2, ls2, rs2.
          split; [exact QL2|]. split; [exact HBL2|]. split; [lia|]. split; [exact HBR2|]. split; [lia|].
          split; [exact Hmm2|]. split; [exact HAL2|]. split; [exact Hap62|]. split; [exact Hap72|].
          split; [rewrite Easp; exact HL2BC | exact HL2A]. }
      split.
      { assert (Hnrf : B.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j <> 1) by (rewrite Htrf; exact Hnc).
        unfold ACtlCutP.RECS, ACtlCutP.RECF in *. rewrite (w4c_t_ID_S_norf _ _ Hnrf). exact HRECF. }
      exact (w4c_fs9_move cx j regs3 R' mem3 HFS9 E9).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B823d8_at j (0x823d8) --S_F16--> B82464_at j.
   S_F16 (Seg/F16.v seg_F16 :1138): record_sum_closes @0x823dc, first->have check, joined_byte @0x82414 and @0x82438,
   the joined-address check, reac_identity_ingest @0x82460, returning at 0x82464. *)
Lemma seg_F16 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82464_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B823d8_at [Z.of_nat j]).
Proof.
  intros POST j H64 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B823d8_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn26 & Hj & HHB & HLK & H20 & H224 & HFM & HFS & H18 & H27 & Had50 &
    (rb & Hrb & Hrbl) & HAblk & HFLV & Hrf & H11 & HFGf & Had72 & Hfok & HU256 & _ & HFT & HRECF & HFS9).
  destruct HAblk as (A & kp & H9 & Hkp & H24 & HAb & HspA' & HfrA' & Happ2880 & Hw272 & Hd1 & Hd2 & Hd3 & Hd4 &
    Hd5 & Hd6 & H8819 & HNblk & HFSTblk & HPLLblk).
  destruct HNblk as (N & bsN & H11N & Q120 & HN1 & HNfr & HbsN & HbsNl & HrecN & HadN).
  destruct HFSTblk as (HAVE & NB & AD & A0V & A1V & _ & _ & _ & _ & _ & Q168 & EA0V & Q312 & EA1V & Q288 &
    HU256' & HADb & EAD).
  destruct HPLLblk as (PLL & idbP & pbP & Q304 & Qpp & Q296 & _ & Q176 & _ & _ & _ & _ & _ & _ & _ & HadId).
  subst A0V A1V.
  unfold ACtlCutP.flen in *.
  (* the frame's spill base, the cut's sp *)
  pose proof HFRAC as (AF & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9F & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA448 & HS4096 & HSapp & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)) as [Hb0 _]. exact Hb0. }
  assert (EAF : AF = A).
  { apply w4c_lit_inj; [unfold B.AsanRT.APPMEM_END in HSapp; lia | exact HAb |].
    unfold ACtlCut.rgv in Hr9F, H9. rewrite <- Hr9F, <- H9. reflexivity. }
  subst AF.
  unfold B.AsanRT.APPMEM_END, ACtlCutP.FRAME_BYTES in HSapp, HfrA, HNfr.
  assert (Esp : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp) by exact HspZ.
  (* the world: the stack window above alloc_ceiling, the owned frame, phi's live block *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & HstkS & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold Reusable.YCfn.LLVMF_STK in Hpres, HstkS.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (apply w4c_fr_ly3; [exact Hly | apply HL; left; reflexivity]).
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite Efr in Hf4096. rewrite Efr, HFB in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (Hphi : In (phi, B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi) as (_ & Hp4096 & Hpceil & _).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx)
    HAR Hphi Hin6) as Hsep.
  rewrite Efr, HFB in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  assert (Hfimg : forall x, fr <= x < fr + 4096 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 x HAR _)).
    right; left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr, HFB. exact Hx. }
  assert (Himglo : forall x, Reusable.YG0d.in_img segs x -> 0 <= x < 0x7fff8000).
  { intros x Hx. pose proof (segs_low x Hx) as H. unfold Reusable.YG0f.kLowMemEnd in H. exact H. }
  (* the model: the turn closes a record (t_rf = 1), so the record is kept and joined; FI pins `first` *)
  pose proof (w4c_trf1_cls _ _ Hrf) as Hcls.
  destruct (w4c_cls_close_inv _ _ _ Hcls) as (Hfrr & Hkeep & Hclose & _).
  pose proof (w4c_close_T 1 1 1 1 1 _ _ _ Hcls) as HT.
  pose proof (w4c_fr_len50 _ _ Hfrr) as Hlen50.
  pose proof (w4c_fr_fg_n _ _ Hfrr) as Hfgn.
  pose proof (w4c_t_FG_length (ACtlCut.c_in cx) j) as HLst.
  pose proof (w4c_t_g_length (ACtlCut.c_in cx) j) as HLg.
  pose proof (w4c_t_FGf_length (ACtlCut.c_in cx) j) as HLf.
  pose proof (Reusable.YCbq.req_size_pos (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ltac:(lia)) as [_ Hrq].
  assert (Hbat6 : Prog.RcFrag.bat (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) 6 = 1).
  { pose proof (w4c_keep_hf _ _ Hkeep) as Hhf. unfold Prog.RcFrag.fg_hf in Hhf.
    destruct Hfok as ([H0|H1] & _); [exfalso; exact (Hhf H0) | exact H1]. }
  pose proof (proj2 Hfok Hbat6) as Hb7.
  pose proof HFS as (HFhave & HFn & HFbody & HFad40 & HFI).
  destruct (HFI Hbat6) as (Ehave & En & Ebody).
  rewrite Ehave in HFhave.
  assert (Hbl : Z.of_nat (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))) = (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))).
  { rewrite Ebody, En, length_firstn, length_skipn, HLst. lia. }
  assert (Hbl35 : (length (B.Prog.SlotModel.fs_body (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) <= 35)%nat) by lia.
  assert (Hpll : 1 <= (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) <= 51) by (unfold B.Prog.SlotModel.f_pll; lia).
  pose proof (B.Prog.SlotInv.t_g_of_phi mem3 phi _ j (proj1 (proj2 (proj2 HFT))) Hlen50) as HGb.
  pose proof (w4c16_jb_range (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9) as Rj9.
  pose proof (w4c16_jb_range (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 10) as Rj10.
  assert (EAD' : AD = (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 10) + 256 * (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9))
    by (rewrite EAD; unfold B.Prog.SlotModel.joined_addr; lia).
  assert (EADf : AD = Prog.RcFrag.fg_addr (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
  { rewrite EAD. symmetry. apply (w4c_fg_addr_joined _ _ _ HLst HLg Hfok HFI Hbat6 Hfgn). lia. }
  pose proof HLK as (_ & _ & _ & HFLI).
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HSTKfr & _).
  pose proof HFLV as (_ & _ & _ & _ & _ & HFLVrf).
  destruct (HFLVrf Hrf) as (Qpp' & Qpn').
  assert (Hal2880 : (fr + 2880) mod 4 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfr32 in D.
    replace (fr + 2880) with ((8 * (fr / 32) + 720) * 4) by lia. apply Z.mod_mul. lia. }
  assert (Hidev : (fr + 2688) mod 2 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfr32 in D.
    replace (fr + 2688) with ((16 * (fr / 32) + 1344) * 2) by lia. apply Z.mod_mul. lia. }
  (* the footprint: every visible byte of the cut's world *)
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RW : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
               lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible; eapply w4c_win_vis; [exact HJ | exact H1 | exact H2]).
  assert (RF : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible;
        eapply w4c_frame_vis; [exact HAR | exact Hin6 | rewrite Efr; exact H1 | rewrite Efr, HFB; exact H2]).
  assert (RP : forall lo len, phi <= lo ->
               lo + len <= phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
               lib.Lib.ExecF.rng RNG lo len)
    by (intros lo len H1 H2; apply B.ProgBridge.rng_of_visible;
        eapply w4c16_heap_vis; [exact HAR | exact Hphi | exact H1 | exact H2]).
  assert (RFS : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> 1 <= len ->
               lib.Lib.ExecF.rng RNG (lo / 8 + B.AsanRT.ASAN_K) ((lo + len - 1) / 8 - lo / 8 + 1))
    by (intros lo len H1 H2 H3; apply B.ProgBridge.rng_of_visible;
        exact (w4c16_frame_shspan ly3 S3 W3 mem3 md3 _ fr lo len HAR Hin6 Efr Hfr32 H1 H2 H3)).
  assert (RF1 : forall x, fr <= x < fr + 4096 -> lib.Lib.ExecF.rng RNG (B.AsanRT.shadow_addr x) 1)
    by (intros x Hx; apply B.ProgBridge.rng_of_visible;
        exact (w4c16_frame_sa1 ly3 S3 W3 mem3 md3 _ fr x HAR Hin6 Efr Hfr32 Hx)).
  assert (RP1 : forall x, phi <= x < phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
               lib.Lib.ExecF.rng RNG (B.AsanRT.shadow_addr x) 1)
    by (intros x Hx; apply B.ProgBridge.rng_of_visible; exact (w4c16_heap_sa1 ly3 S3 W3 mem3 md3 _ _ x HAR Hphi Hx)).
  (* what the three 16-byte callee windows [sp - 16, sp) keep *)
  assert (OW1 : forall x, (x < sp - 16 \/ sp <= x) -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn; split; [lia | exact I]).
  assert (OS1 : forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside [(sp - 16, sp)] x).
  { intros x Hx. apply OW1. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
      B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia. }
  assert (TB : forall m', lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m' -> forall a bs,
               lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs ->
               (a + Z.of_nat (length bs) <= sp - 16 \/ sp <= a) -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros m' MU a bs Hb Hd. apply (w4c16_bmv _ mem3 m' _ _ Hb MU). intros x Hx. apply OW1. lia. }
  assert (TQ : forall m', lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m' -> forall a v,
               ACtlCutP.q64 mem3 a v -> (a + 8 <= sp - 16 \/ sp <= a) -> ACtlCutP.q64 m' a v).
  { intros m' MU a v Hq Hd. apply (w4c16_qmv _ mem3 m' _ _ Hq MU). intros x Hx. apply OW1. lia. }
  assert (TA : forall m', lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m' -> forall p n,
               B.AsanRT.addressable mem3 p n -> B.AsanRT.addressable m' p n)
    by (intros m' MU p n H; exact (w4c16_amv _ mem3 m' p n H MU OS1)).
  (* route (C): the cut's ctl_rt_C across the three 16-byte callee windows *)
  assert (TR : forall m', lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m' -> B.ACtlRtC.ctl_rt_C B ly3 S3 m').
  { intros m' MU. apply (w4c16_ctl_rt_munch ly3 S3 _ mem3 m' Hrt MU). intros x Hx. apply OW1.
    unfold B.AsanRT.HIGHMEM_BEG in Hx. lia. }
  assert (HST0 : lib.Lib.Frame.stk B.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) sp).
  { apply (w4c16_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  (* the cut's configuration in the run's state form, the walk moved to the canonical map *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B823d8_at [Z.of_nat j])) with 0x823d8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x823d8) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  change (lib.Lib.Regs6ss.mkR_of regs3) with (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6) (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9) (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12) (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).

  (* ---- run 1: 0x823d8 -> record_sum_closes (a0 = [A + 120] = fragb fr + 15, a1 = N), the callee, return at
     0x823e0 with a0 = 1 (the record's 15-offset window sums to 0) ---- *)
  pose proof record_sum_closesF_on.record_sum_closes_holds_F_on as HRSC.
  unfold record_sum_closes_c_on.record_sum_closes_contract_F_on, record_sum_closes_c.RECORD_SUM_CLOSES,
    record_sum_closes_c.RECORD_SUM_CLOSES_FRAME in HRSC.
  assert (Ea0 : bv_unsigned (Z_to_bv 64 (ACtlCutP.fragb fr + 15)) = ACtlCutP.fragb fr + 15)
    by (apply lib.Lib.MState.unsigned_lit; unfold ACtlCutP.fragb; lia).
  assert (Ea1 : bv_unsigned (lib.Reusable.YK11.getr regs3 11) = N).
  { unfold ACtlCut.rgv in H11N. rewrite H11N. apply lib.Lib.MState.unsigned_lit. unfold ACtlCutP.fragb in HNfr. lia. }
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F16F.seg_F16_pre_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (ACtlCutP.fragb fr + 15)).
      - exact H9.
      - lia.
      - lia.
      - unfold ACtlCutP.fragb; lia.
      - exact Q120.
      - apply RW; lia. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    eapply (HRSC RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ACtlCut.c_sp cx - 32768) bsN); rewrite ?Ea0, ?Ea1, ?Esp.
    - exact HbsNl.
    - right. unfold ACtlCutP.fragb in *. split; [lia|]. split; [lia|]. split; [exact HbsN | left; lia].
    - exact HST0.
    - lia.
    - intros _. exact (proj1 Hrt).
    - intros _. exact HadN.
    - intros _ x Hx. cbn. split; [|exact I]. unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia.
    - apply RW; lia.
    - intros _. apply w4c16_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    - intros _. apply w4c16_img_rng; unfold B.AsanRT.CELL_K; lia.
    - intros _. apply RF; unfold ACtlCutP.fragb in *; lia.
    - intros _. apply RFS; unfold ACtlCutP.fragb in *; lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 HP1 Hhid1 Hsbm1.
  destruct HP1 as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & m1 & Ems1 & MU1 & WM1 & _ & ST1).
  subst ms1.
  rewrite (lib.Lib.MState.ret_pc_even 0x823e0) by (first [lia | reflexivity]).
  replace (if Prog.RcRec.recsum bsN =? 0 then 1 else 0) with 1 by (rewrite HrecN; reflexivity).
  rewrite Esp in MU1, ST1.
  pose proof (TR m1 MU1) as Hrt1.

  (* ---- run 2: 0x823e0 (`beqz a0` not taken: a0 = 1; `beqz [fr + 2880]` not taken: first->have = 1) -> joined_byte
     (first = fr + 2880, blk = phi + 18, 9), the callee, return at 0x82418 with a0 = joined_byte 9 ---- *)
  pose proof joined_byteF_on.joined_byte_holds_F_on as HJB.
  unfold joined_byte_c_on.joined_byte_contract_F_on, joined_byte_c.JOINED_BYTE, joined_byte_c.JOINED_BYTE_FRAME in HJB.
  assert (E2880 : bv_unsigned (Z_to_bv 64 (fr + 2880)) = fr + 2880) by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (E18q : bv_unsigned (Z_to_bv 64 (phi + 18)) = phi + 18) by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (Enb : bv_unsigned (Z_to_bv 8 (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))) = (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))) by (apply w4c16_lit8; lia).
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md1 RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F16F.seg_F16_pre2_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (fr + 2880) (fr + 256) AD (phi + 18)).
      - exact H9.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HADb.
      - apply (TQ m1 MU1); [exact Q168 | right; lia].
      - apply (TB m1 MU1); [exact HFhave | rewrite lib.Lib.Mem.length_le4; left; lia].
      - apply (TQ m1 MU1); [exact Q288 | right; lia].
      - apply (TB m1 MU1); [exact HU256' | rewrite lib.Lib.Mem.length_le2; left; lia].
      - apply (TQ m1 MU1); [exact Q312 | right; lia].
      - apply RW; lia.
      - apply RF; lia.
      - apply RW; lia.
      - apply RF; lia.
      - apply RW; lia. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    eapply (HJB RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ACtlCut.c_sp cx - 32768) 9 (Z_to_bv 8 (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))) (Z_to_bv 8 (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9))).
    all: rewrite ?E2880, ?E18q, ?Enb, ?Esp.
    + left; reflexivity.
    + reflexivity.
    + exact Hal2880.
    + replace (fr + 2880 + 4) with (fr + 2884) by lia. apply (TB m1 MU1); [exact HFn | cbn [length]; left; lia].
    + intros _. lia.
    + apply (w4c16_jb_rd m1 fr phi (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9 ltac:(lia) ltac:(lia) Hbl ltac:(rewrite HLg; lia)).
      * apply (TB m1 MU1); [exact HFbody | left; lia].
      * apply (TB m1 MU1); [exact HGb | rewrite HLg; left; lia].
    + exact ST1.
    + lia.
    + left. lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 9 ltac:(lia) ltac:(lia)) as [Hq|Hq]; left; lia.
    + exact (proj1 Hrt1).
    + apply (TA m1 MU1). apply (w4c16_addr_at mem3 (fr + 2880) 40); [exact HFad40 | lia | lia | lia].
    + apply (TA m1 MU1).
      destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 9 ltac:(lia) ltac:(lia)) as [Hq|Hq].
      * apply (w4c16_addr_at mem3 (fr + 2880) 40); [exact HFad40 | lia | lia | lia].
      * apply (w4c16_addr_at mem3 phi 50); [exact Had50 | lia | lia | lia].
    + intros x Hx. cbn. split; [|exact I]. unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia.
    + apply RW; lia.
    + apply w4c16_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    + apply w4c16_img_rng; unfold B.AsanRT.CELL_K; lia.
    + apply RF; lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 9 ltac:(lia) ltac:(lia)) as [Hq|Hq]; [apply RF | apply RP]; lia.
    + apply RF1; lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 9 ltac:(lia) ltac:(lia)) as [Hq|Hq]; [apply RF1 | apply RP1]; lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms2 md2 HP2 Hhid2 Hsbm2.
  destruct HP2 as (d1 & d2 & d3 & d4 & d5 & d6 & m2 & Ems2 & MU2 & WM2 & _ & ST2 & _).
  subst ms2.
  rewrite (lib.Lib.MState.ret_pc_even 0x82418) by (first [lia | reflexivity]).
  rewrite (w4c16_zxb8 _ Rj9).
  rewrite Esp in MU2, ST2.
  assert (MU12 : lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m2) by (intros x Hx; rewrite (MU2 x Hx); exact (MU1 x Hx)).
  pose proof (TR m2 MU12) as Hrt2.

  (* ---- run 3: 0x82418 -> joined_byte (first, blk, 10), the callee, return at 0x8243c ---- *)
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md2 RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F16F.seg_F16_pre3_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9)). exact Rj9. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    eapply (HJB RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ACtlCut.c_sp cx - 32768) 10 (Z_to_bv 8 (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j))) (Z_to_bv 8 (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 10))).
    all: rewrite ?E2880, ?E18q, ?Enb, ?Esp.
    + right; reflexivity.
    + reflexivity.
    + exact Hal2880.
    + replace (fr + 2880 + 4) with (fr + 2884) by lia. apply (TB m2 MU12); [exact HFn | cbn [length]; left; lia].
    + intros _. lia.
    + apply (w4c16_jb_rd m2 fr phi (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 10 ltac:(lia) ltac:(lia) Hbl ltac:(rewrite HLg; lia)).
      * apply (TB m2 MU12); [exact HFbody | left; lia].
      * apply (TB m2 MU12); [exact HGb | rewrite HLg; left; lia].
    + exact ST2.
    + lia.
    + left. lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 10 ltac:(lia) ltac:(lia)) as [Hq|Hq]; left; lia.
    + exact (proj1 Hrt2).
    + apply (TA m2 MU12). apply (w4c16_addr_at mem3 (fr + 2880) 40); [exact HFad40 | lia | lia | lia].
    + apply (TA m2 MU12).
      destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 10 ltac:(lia) ltac:(lia)) as [Hq|Hq].
      * apply (w4c16_addr_at mem3 (fr + 2880) 40); [exact HFad40 | lia | lia | lia].
      * apply (w4c16_addr_at mem3 phi 50); [exact Had50 | lia | lia | lia].
    + intros x Hx. cbn. split; [|exact I]. unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia.
    + apply RW; lia.
    + apply w4c16_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    + apply w4c16_img_rng; unfold B.AsanRT.CELL_K; lia.
    + apply RF; lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 10 ltac:(lia) ltac:(lia)) as [Hq|Hq]; [apply RF | apply RP]; lia.
    + apply RF1; lia.
    + destruct (w4c16_jb_place fr phi (B.Prog.SlotModel.fs_n (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)) 10 ltac:(lia) ltac:(lia)) as [Hq|Hq]; [apply RF1 | apply RP1]; lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms3 md3' HP3 Hhid3 Hsbm3.
  destruct HP3 as (e1 & e2 & e3 & e4 & e5 & e6 & m3 & Ems3 & MU3 & WM3 & _ & ST3 & _).
  subst ms3.
  rewrite (lib.Lib.MState.ret_pc_even 0x8243c) by (first [lia | reflexivity]).
  rewrite (w4c16_zxb8 _ Rj10).
  rewrite Esp in MU3, ST3.
  assert (MU13 : lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m3) by (intros x Hx; rewrite (MU3 x Hx); exact (MU12 x Hx)).
  assert (WM13 : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m3) by (intros x Hx; apply WM3, WM2, WM1, Hx).
  pose proof (TR m3 MU13) as Hrt3.

  (* ---- run 4: 0x8243c (`bne a0,s5` not taken: (jb 9 << 8) | jb 10 = the address cell's u16 AD = joined_addr) ->
     reac_identity_ingest (fr + 2688, AD, fragb fr + 19, pll), the callee, return at the exit cut 0x82464 ---- *)
  pose proof reac_identity_ingestF.reac_identity_ingest_F_holds_on as HING.
  unfold reac_identity_ingest_c.reac_identity_ingest_contract_F_on, reac_identity_ingest_c.reac_identity_ingest_W,
    reac_identity_ingest_c.REAC_IDENTITY_INGEST, reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in HING.
  assert (HPB : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (ACtlCutP.fragb fr + 19) (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))).
  { exact (w4c16_sub mem3 (ACtlCutP.fragb fr) _ 19 (Z.to_nat (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))) HFGf ltac:(rewrite HLf; lia)). }
  assert (HPBl : length (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))) = Z.to_nat (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))).
  { unfold Prog.RcFrag.bsl. rewrite length_firstn, length_skipn, HLf. lia. }
  assert (OIMG : forall x, Reusable.YG0d.in_img segs x -> x < fr \/ fr + 4096 <= x).
  { intros x Hx. destruct (Z_lt_ge_dec x fr) as [D|D]; [left; exact D|].
    destruct (Z_lt_ge_dec x (fr + 4096)) as [D'|D']; [exfalso; exact (Hfimg x ltac:(lia) Hx) | right; lia]. }
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3' RNG _ (POST cx)).
  { apply B.ProgBridge.fevt_of_evtF. eapply lib.Lib.ExecF.evtF_cut.
    { eapply (F16F.seg_F16_pre4_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (fr + 256) AD (fr + 272) (fr + 304) (fr + 2688) (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 9) (B.Prog.SlotModel.joined_byte (B.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 10)
                (ACtlCutP.fragb fr + 19) (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))).
      - exact H9.
      - lia.
      - lia.
      - exact Rj9.
      - exact Rj10.
      - exact HADb.
      - exact EAD'.
      - lia.
      - lia.
      - lia.
      - lia.
      - unfold ACtlCutP.fragb; lia.
      - lia.
      - apply (TQ m3 MU13); [exact Q288 | right; lia].
      - apply (TB m3 MU13); [exact HU256' | rewrite lib.Lib.Mem.length_le2; left; lia].
      - apply (TQ m3 MU13); [exact Q304 | right; lia].
      - apply (TQ m3 MU13); [exact Qpp' | left; lia].
      - apply (TQ m3 MU13); [exact Q296 | right; lia].
      - apply (TQ m3 MU13); [exact Qpn' | left; lia].
      - apply (TQ m3 MU13); [exact Q176 | right; lia].
      - apply RW; lia.
      - apply RF; lia.
      - apply RW; lia.
      - apply RF; lia.
      - apply RW; lia.
      - apply RF; lia.
      - apply RW; lia. }
    intros ms' Ems'. cbv beta in Ems'. subst ms'.
    eapply (HING RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ACtlCut.c_sp cx - 32768) (fr + 2688) AD (ACtlCutP.fragb fr + 19) (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))); rewrite ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact HADb.
    - unfold ACtlCutP.fragb; lia.
    - lia.
    - intros _. split; [exact Hidev|].
      apply w4c16_cb_rw; [| apply w4c16_IDr_len |].
      + apply (TB m3 MU13); [exact (proj1 (proj1 HRECF)) | rewrite w4c16_IDr_len; left; lia].
      + change (Z.of_nat 38) with 38.
        apply (w4c16_wr_of_stk mem3 m3 fr (fr + ACtlCutP.FRAME_BYTES) (fr + 2688) 38 HSTKfr WM13);
          unfold ACtlCutP.FRAME_BYTES; lia.
    - exact HPBl.
    - intros _ _. apply (TB m3 MU13); [exact HPB | rewrite HPBl; left; unfold ACtlCutP.fragb; lia].
    - intros _ _ _. right. unfold ACtlCutP.fragb; lia.
    - exact ST3.
    - lia.
    - intros _. left. lia.
    - intros _ _. left. unfold ACtlCutP.fragb; lia.
    - exact (proj1 Hrt3).
    - intros _. apply (TA m3 MU13). exact HadId.
    - intros _ _. apply (TA m3 MU13). apply (w4c16_addr_at mem3 (ACtlCutP.fragb fr) 72); [exact Had72 | lia | lia | lia].
    - intros x Hx. cbn. split; [unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx; lia|]. split; [|exact I].
      destruct Hx as [Hx|[Hx|Hx]].
      + pose proof (OIMG x ltac:(apply w4c16_in_img; unfold B.AsanRT.GOT_CELL_K in Hx; lia)). lia.
      + pose proof (OIMG x ltac:(apply w4c16_in_img; unfold B.AsanRT.CELL_K in Hx; lia)). lia.
      + unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
          B.AsanRT.HIGHMEM_BEG in Hx. lia.
    - apply RW; lia.
    - apply w4c16_img_rng; unfold B.AsanRT.GOT_CELL_K; lia.
    - apply w4c16_img_rng; unfold B.AsanRT.CELL_K; lia.
    - intros _. split; [apply RF; lia|].
      replace (fr + 2688 + 37) with (fr + 2688 + 38 - 1) by lia. apply RFS; lia.
    - intros _ _. split; [apply RF; unfold ACtlCutP.fragb; lia | apply RFS; unfold ACtlCutP.fragb; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms4 md4 HP4 Hhid4 Hsbm4.
  unfold reac_identity_ingest_c.reac_identity_ingest_post in HP4.
  destruct HP4 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & Ems4 & MU4 & WM4 & _ &
    ST4 & _ & HRW).
  subst ms4.
  rewrite (lib.Lib.MState.ret_pc_even 0x82464) by (first [lia | reflexivity]).
  unfold reac_identity_ingest_c.reac_identity_ingest_W, reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in MU4.
  rewrite Esp in MU4, ST4.
  assert (Href : reac_identity_ingest_c.ingest_refused (fr + 2688) (ACtlCutP.fragb fr + 19) (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) = false).
  { unfold reac_identity_ingest_c.ingest_refused. apply Bool.orb_false_intro.
    - apply Z.eqb_neq. lia.
    - apply Bool.andb_false_intro2. apply Z.eqb_neq. unfold ACtlCutP.fragb; lia. }
  pose proof (HRW Href) as HRW'.

  (* ---- the exit cut 0x82464: the run wrote the callee windows [sp - 32, sp) and the identity record ---- *)
  set (W4 := [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  assert (OW4 : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                lib.Lib.Frame.outside W4 x)
    by (intros x H1 H2; subst W4; cbn; split; [lia | split; [lia | exact I]]).
  assert (MU4' : lib.Lib.Frame.munch W4 mem3 m4).
  { subst W4. intros x Hx. rewrite (MU4 x Hx). apply MU13. cbn in Hx |- *. destruct Hx as (Hx1 & _).
    split; [lia | exact I]. }
  assert (WM4' : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m4) by (intros x Hx; apply WM4, WM13, Hx).
  assert (HID : forall x : word, Reusable.YA0n.w_H W3 x = true -> m4 x = mem3 x).
  { intros x Hx. etransitivity; [exact (Hhid4 x Hx)|]. etransitivity; [exact (Hhid3 x Hx)|].
    etransitivity; [exact (Hhid2 x Hx)|]. exact (Hhid1 x Hx). }
  assert (HSBM : Reusable.YK04.same_but_materialized md3 md4).
  { eapply Reusable.YK04.same_but_materialized_trans; [exact Hsbm1|].
    eapply Reusable.YK04.same_but_materialized_trans; [exact Hsbm2|].
    eapply Reusable.YK04.same_but_materialized_trans; [exact Hsbm3 | exact Hsbm4]. }
  assert (OS4 : forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W4 x).
  { intros x Hx. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hx. apply OW4; lia. }
  assert (OI4 : forall x, Reusable.YG0d.in_img segs x -> lib.Lib.Frame.outside W4 x).
  { intros x Hx. pose proof (Himglo x Hx). pose proof (OIMG x Hx). apply OW4; lia. }
  assert (OA4 : forall x, A <= x < A + 448 -> lib.Lib.Frame.outside W4 x) by (intros x Hx; apply OW4; lia).
  assert (OP4 : forall x, phi <= x < phi + Reusable.YG00.req_size (B.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) ->
                lib.Lib.Frame.outside W4 x) by (intros x Hx; apply OW4; lia).
  assert (TB4 : forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs ->
                (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W4 x) ->
                lib.Lib.Mem.bytes_at B.Img0.rsegs m4 a bs)
    by (intros a bs Hb Ho; exact (w4c16_bmv W4 mem3 m4 a bs Hb MU4' Ho)).
  assert (TQ4 : forall a v, ACtlCutP.q64 mem3 a v -> (forall x, a <= x < a + 8 -> lib.Lib.Frame.outside W4 x) ->
                ACtlCutP.q64 m4 a v)
    by (intros a v Hq Ho; exact (w4c16_qmv W4 mem3 m4 a v Hq MU4' Ho)).
  assert (TA4 : forall p n, B.AsanRT.addressable mem3 p n -> B.AsanRT.addressable m4 p n)
    by (intros p n H; exact (w4c16_amv W4 mem3 m4 p n H MU4' OS4)).
  assert (Hrt4 : B.ACtlRtC.ctl_rt_C B ly3 S3 m4).
  { apply (w4c16_rt_mv ly3 S3 W4 mem3 m4 Hrt MU4'). intros x [Hx|Hx]; [exact (OI4 x Hx) | exact (OS4 x Hx)]. }
  assert (HJ4 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m4 md4 k).
  { apply (w4c16_aj2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 md4 (sp - 32) sp (fr + 2688) (fr + 2688 + 38) HJ).
    - unfold Reusable.YCfn.LLVMF_STK. lia.
    - lia.
    - intros a Ha. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr, HFB. lia.
    - exact MU4'.
    - intros x [Hx|Hx].
      + apply (w4c16_some m4 (ACtlCut.c_sp cx - 32768) sp x ST4); [lia|]. intros Hi. pose proof (Himglo _ Hi). lia.
      + assert (HL38 : Z.of_nat (length (snd (Prog.RcIdentModel.ING (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) AD (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))))) = 38)
          by (rewrite Prog.RcIdentModel.ING_length; [reflexivity | apply w4c16_IDr_len]).
        destruct (w4c16_present m4 (fr + 2688) _ (bv_unsigned x) (w4c16_cb_bytes _ _ _ _ HRW') ltac:(lia))
          as (b & Hb).
        unfold lib.Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
        rewrite (w4c16_raw m4 x b Hb (Hfimg (bv_unsigned x) ltac:(lia))). discriminate.
    - exact HID.
    - exact HSBM. }
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R4 := R) end.
  assert (E2 : lib.Reusable.YK11.getr R4 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : lib.Reusable.YK11.getr R4 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : lib.Reusable.YK11.getr R4 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : lib.Reusable.YK11.getr R4 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : lib.Reusable.YK11.getr R4 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : lib.Reusable.YK11.getr R4 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : lib.Reusable.YK11.getr R4 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E20 : lib.Reusable.YK11.getr R4 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
  assert (E24 : lib.Reusable.YK11.getr R4 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E25 : lib.Reusable.YK11.getr R4 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (E26 : lib.Reusable.YK11.getr R4 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (E22 : ACtlCut.rgv R4 22 1) by reflexivity.
  assert (E27 : ACtlCut.rgv R4 27 (-8)) by reflexivity.
  assert (E27' : lib.Reusable.YK11.getr R4 27 = lib.Reusable.YK11.getr regs3 27)
    by (unfold ACtlCut.rgv in E27, H27; rewrite E27, H27; reflexivity).
  assert (E10 : ACtlCut.rgv R4 10 (reac_identity_ingest_c.ingest_ret (fr + 2688) AD (ACtlCutP.fragb fr + 19) (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))
                                     (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))))) by reflexivity.
  assert (HR9 : ACtlCut.rgv R4 9 A) by (unfold ACtlCut.rgv in *; rewrite E9; exact H9).
  assert (EspZ : Reusable.YG0d.spZ R4 = Reusable.YG0d.spZ regs3) by (unfold Reusable.YG0d.spZ; rewrite E2; reflexivity).
  assert (SP4 : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R4 m4 off v)
    by (intros off v Hoff Hs; exact (w4c16_spmv W4 regs3 R4 mem3 m4 off v A Hs H9 ltac:(lia) ltac:(lia) Hoff HR9 MU4' OA4)).
  assert (EIDS : B.Prog.SlotModel.t_ID (ACtlCut.c_in cx) (S j) = snd (Prog.RcIdentModel.ING (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) AD (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))))).
  { rewrite (w4c16_t_ID_S_rf _ _ Hrf), <- EADf. reflexivity. }
  apply (w4c16_cfg W3 0x82464 R4 m4 md4 (POST cx)).
  apply (H64 cx [Z.of_nat j] fr k ly3 S3 W3 R4 m4 md4 HB HJ4 HF HL Hk); [| exact Hrt4].
  (* C_B82464_at's body *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82464_at ACtlCutP.ixn ACtlCutP.ixz nth].
  split; [reflexivity|]. rewrite Nat2Z.id.
  exists phi.
  split; [exact HP|].
  split.
  { apply (w4c16_frac_mv W4 cx fr fr regs3 R4 mem3 m4 A HFRAC H9 HAb E2 E3 E4 E8 E9 E19 E26 MU4').
    - intros x Hx. apply OW4; lia.
    - intros x Hx. apply OW4; lia.
    - intros x Hx. apply OS4. apply (w4c16_sfr_shadow fr x Hf4096); [lia | exact Hx]. }
  split; [exact Hn26|]. split; [exact Hj|].
  split; [destruct HHB as (Hphinz & HAd); split; [exact Hphinz | exact (TA4 _ _ HAd)]|].
  split.
  { apply (w4c16_LK_mv W4 cx fr j regs3 R4 mem3 m4 HLK SP4 E27' MU4' OS4 OI4).
    - intros x Hx. apply OW4; lia.
    - apply (w4c16_stk_tr W4 mem3 m4 fr _ HSTKfr MU4' WM4'). intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
      destruct (Z_lt_ge_dec x (fr + 2688)) as [D|D]; [left; apply OW4; lia|].
      destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [D'|D']; [right | left; apply OW4; lia].
      apply (w4c16_present m4 (fr + 2688) _ x (w4c16_cb_bytes _ _ _ _ HRW')).
      rewrite Prog.RcIdentModel.ING_length by apply w4c16_IDr_len. unfold Prog.RcIdentModel.ID_SIZE. lia. }
  split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
  split; [exact (SP4 224 _ ltac:(lia) H224)|].
  split.
  { destruct HFM as (S184 & R24 & R22 & R25 & S312).
    split; [exact (SP4 184 _ ltac:(lia) S184)|].
    split; [unfold ACtlCut.rgv in *; rewrite E24; exact R24|].
    split; [exact E22|].
    split; [unfold ACtlCut.rgv in *; rewrite E25; exact R25|].
    exact (SP4 312 _ ltac:(lia) S312). }
  split; [apply (w4c16_fsj_mv cx fr j regs3 R4 mem3 m4 W4 HFS MU4'); [intros x Hx; apply OW4; lia | exact OS4 | exact Hbl35]|].
  split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
  split; [exact (TA4 _ _ Had50)|].
  split; [exists rb; split; [apply TB4; [exact Hrb | rewrite Hrbl; intros x Hx; apply OP4; lia] | lia]|].
  split.
  { exists (reac_identity_ingest_c.ingest_ret (fr + 2688) AD (ACtlCutP.fragb fr + 19) (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))).
    split; [exact E10|]. unfold reac_identity_ingest_c.ingest_ret. rewrite Href. cbv iota.
    destruct (Prog.RcIdentModel.ING_ret (B.Prog.SlotModel.t_IDr (ACtlCut.c_in cx) j) AD (Prog.RcFrag.bsl (B.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j) 19 (B.Prog.SlotModel.f_pll (B.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (B.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)))) as [E|E]; rewrite E; lia. }
  split; [exact E27|].
  split.
  { exists A, kp.
    split; [exact HR9|].
    split; [apply TQ4; [exact Hkp | intros x Hx; apply OA4; lia]|].
    split; [exact Happ2880|].
    split; [destruct Hw272 as (w272 & Q272 & Hw1 & Hw2 & Hw3); exists w272;
            split; [apply TQ4; [exact Q272 | intros x Hx; apply OA4; lia] | split; [exact Hw1 | split; [exact Hw2 | exact Hw3]]]|].
    split; [unfold ACtlCut.rgv in *; rewrite E24; exact H24|].
    split; [exact Hd1|]. split; [exact Hd2|].
    split; [rewrite EspZ; exact Hd3|]. split; [rewrite EspZ; exact Hd4|].
    intros H8. destruct (H8819 H8) as (HRI &
      (L & ls & rs & QL & HBL & HLls & HBR & HLrs & Hmm & HADL & HapL6 & HapL7 & HLBC & HLA & HL2688) &
      (L2 & ls2 & rs2 & QL2 & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HapL26 & HapL27 & HL2BC & HL2A & HL22688)).
    rewrite HspZ in Hd4, HLBC, HL2BC. unfold ACtlCutP.BWA.BCMP_WRAP_K in Hd4, HLBC, HL2BC.
    split.
    { apply (w4c16_rec_inv_mv cx j phi A kp mem3 m4 W4 HRI MU4').
      - intros x Hx. apply OP4. lia.
      - intros x Hx. apply OA4. lia.
      - exact OS4.
      - intros x Hx. apply OW4; lia. }
    split.
    { exists L, ls, rs.
      split; [apply TQ4; [exact QL | intros x Hx; apply OA4; lia]|].
      split; [apply TB4; [exact HBL | rewrite HLls; intros x Hx; apply OW4; lia]|].
      split; [lia|].
      split; [apply TB4; [exact HBR | rewrite HLrs; intros x Hx; apply OP4; lia]|].
      split; [lia|]. split; [exact Hmm|]. split; [exact (TA4 _ _ HADL)|].
      split; [exact HapL6|]. split; [exact HapL7|].
      split; [rewrite EspZ, HspZ; unfold ACtlCutP.BWA.BCMP_WRAP_K; exact HLBC | exact HLA]. }
    { exists L2, ls2, rs2.
      split; [apply TQ4; [exact QL2 | intros x Hx; apply OA4; lia]|].
      split; [apply TB4; [exact HBL2 | rewrite HLls2; intros x Hx; apply OW4; lia]|].
      split; [lia|].
      split; [apply TB4; [exact HBR2 | rewrite HLrs2; intros x Hx; apply OP4; lia]|].
      split; [lia|]. split; [exact Hmm2|]. split; [exact (TA4 _ _ HADL2)|].
      split; [exact HapL26|]. split; [exact HapL27|].
      split; [rewrite EspZ, HspZ; unfold ACtlCutP.BWA.BCMP_WRAP_K; exact HL2BC | exact HL2A]. } }
  split.
  { destruct HFT as (T224 & T232 & Tphi & Tlen).
    split; [exact (SP4 224 _ ltac:(lia) T224)|].
    split; [exact (SP4 232 _ ltac:(lia) T232)|].
    split; [apply TB4; [exact Tphi | intros x Hx; apply OP4; lia] | exact Tlen]. }
  split.
  { pose proof HRECF as ((_ & HIDok) & (HFGB & HFGok)).
    unfold ACtlCutP.RECS, ACtlCutP.FREC, ACtlCutP.IDb, ACtlCutP.FGb, ACtlCutP.IDBe, ACtlCutP.FGBe in *.
    split; split.
    - rewrite EIDS. exact (w4c16_cb_bytes _ _ _ _ HRW').
    - rewrite EIDS. apply Prog.RcIdentLib.ING_id_ok; [apply w4c16_IDr_len | exact HIDok].
    - apply TB4; [exact HFGB|]. rewrite w4c_t_FG_length. intros x Hx. apply OW4; lia.
    - exact HFGok. }
  exact (SP4 248 _ ltac:(lia) HFS9).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82464_at j (0x82464) --S_F17--> B82468_at j.
   S_F17 (Seg/F17.v seg_F17 :91): `bltz a0,0x82fa4` not taken, to the split cut 0x82468. *)
Lemma seg_F17 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82468_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82464_at [Z.of_nat j]).
Proof.
  (* 1. SINK 0x82464 (`bltz a0,0x82fa4`): not taken: a0 = the ingest result, nonnegative (body).  Step of
        F17F.seg_F17_F (0x82464 -> 0x82468; no write).
     2. Apply H68 at cx, [Z.of_nat j], fr, k: C_B82468_at's body = FCUTP .. (FM, FS9, FSj, LK, rec_inv, RECS), the
        entry's facts unchanged. *)
  intros POST j H68 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82464_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HLK & H20 & H224 & HFM & HFS & H18 & Had & Hrb &
    (v0 & Ha0 & Hv0) & H27 & HA & HFT & HRECS & HFS9).
  (* the cut's configuration in the run's state form, the walk moved to the canonical map mkR_of regs3 *)
  change (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82464_at [Z.of_nat j])) with 0x82464.
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82464) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* SINK 0x82464 (`bltz a0,0x82fa4`) not taken: a0 = v0 with 0 <= v0 < 2^63 (the body).  The run reads no memory,
     so its footprint is empty and fp_avoids is vacuous. *)
  eapply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 (fun _ _ => False)).
  - apply B.ProgBridge.fevt_of_evtF. unfold Lib.Regs6ss.mkR_of. eapply F17F.seg_F17_F; [exact Ha0 | exact Hv0].
  - intros a n Hr. destruct Hr.
  - intros ms' md' Hms Hsbm. cbv beta in Hms. subst ms'.
    eapply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3); [| exact (Lib.Regs6ss.mkR_of_eqv regs3)].
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ACtlCut.ix_cut C_B82468_at [Z.of_nat j])) regs3 mem3 md')
              (POST cx)).
    apply (H68 cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
    + (* no write: the journal moves by the model's materialization only *)
      eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* C_B82468_at's body: the entry's facts, registers and memory unchanged *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82468_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact HFRAC|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact H18|]. split; [exact H20|]. split; [exact HFT|].
      split; [exact HLK|]. split; [exact HFM|]. split; [exact HFS|].
      split; [intros _; exact (conj Had Hrb)|].
      split; [exact H27|].
      split; [|exact (conj HRECS HFS9)].
      destruct HA as (A & kp & H9 & Hkp & Happ & Hw272 & H24 & Hphi2880 & Hkp2880 & Hphisp & Hkpsp & H8819).
      exists A, kp.
      split; [exact H9|]. split; [exact Hkp|]. split; [exact Happ|]. split; [exact Hw272|].
      split; [exact H24|]. split; [exact Hkp2880|]. split; [exact Hkpsp|].
      split; [intros _; exact (conj Hphi2880 Hphisp)|].
      exact H8819.
    + exact Hrt.
Qed.

End W4c.

(* Stage lemmas of this file (all Abort until the shell, the core, the callee / trampoline contracts and the `_F`
   land); [j] abbreviates [Z.of_nat j]:
     seg_F13  (B82340_at) : forall POST j, ctl_from POST (ix_cut C_B8235c_at [j]) -> ctl_from POST (ix_cut C_B82340_at [j])
     seg_F14  (B8235c_at) : forall POST j, ctl_from POST (ix_cut C_B8237c_at [j]) ->
                            ctl_from POST (ix_cut C_B82378_at [j]) -> ctl_from POST (ix_cut C_B8235c_at [j])
     seg_F15  (B82378_at) : forall POST j, ctl_from POST (ix_cut C_B8237c_at [j]) -> ctl_from POST (ix_cut C_B82378_at [j])
     seg_F15b (B8237c_at) : forall POST j, ctl_from POST (ix_cut C_B823d8_at [j]) ->
                            ctl_from POST (ix_cut C_B82468_at [j]) -> ctl_from POST (ix_cut C_B8237c_at [j])
     seg_F16  (B823d8_at) : forall POST j, ctl_from POST (ix_cut C_B82464_at [j]) -> ctl_from POST (ix_cut C_B823d8_at [j])
     seg_F17  (B82464_at) : forall POST j, ctl_from POST (ix_cut C_B82468_at [j]) -> ctl_from POST (ix_cut C_B82464_at [j])
   Each seg_* is named and stated exactly as ACtl.v's Hypothesis of the same name (576147dfd46), generic in SK and FP.
   Sink / trap obligations (branch -> target: refuting lemma, step):
     0x8235c -> 0x82fa4 : seg_F14 step 1          0x82378 -> 0x82fa4 : seg_F15 step 1
     0x8238c, 0x8239c, 0x823b4, 0x823c8 -> 0x82fa4 : seg_F15b step 1
     0x823c0 (T26), 0x823d0 (T27) -> 0x82fa0 : seg_F15b step 1
     0x823e0, 0x823ec -> 0x82fa4 : seg_F16 step 2  0x82440 -> 0x82fa4 : seg_F16 step 4
     0x82464 -> 0x82fa4 : seg_F17 step 1
     joined_byte's T1-T5 (0x836b8, 0x836ec, 0x83704, 0x83714, 0x83718 -> 0x8373c): inside the callee, by its
     contract's premises S1.2-S1.6 (OPEN-1 noted in the header). *)

(* The gate's named audit (a Theorem Labs lane's checklist item 4 (a working note, not in this delivery)): one Check and one Print Assumptions per closed stage. *)
Check seg_F17.
Print Assumptions seg_F17.
Check seg_F15.
Print Assumptions seg_F15.
Check seg_F15b.
Print Assumptions seg_F15b.
Check seg_F13.
Print Assumptions seg_F13.
Check seg_F16.
Print Assumptions seg_F16.
Check seg_F14.
Print Assumptions seg_F14.
