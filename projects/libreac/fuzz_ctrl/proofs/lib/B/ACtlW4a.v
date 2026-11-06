(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 3670 of its 3875 lines of code are new or changed and 2907 lines of the source are left out. *)
(* lib/B/ACtlW4a.v -- piece W4a (frame turn, part 1: S_F1 .. S_F6) of fuzz_ctrl image B's (asan-ubsan) walk of
   LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane.
   rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one stage lemma per cut of W4a (cut-table rows 41-46; all own6), POINTWISE
   in the frame-loop index j (a Theorem Labs lane 22:47Z: every cut of a loop turn is stated at a fixed index through
   ACtlCut.ix_cut, so the top can run the donor's rt_G_allX induction over 256 - j; ACtlCut.ctl_from_ix recovers the
   all-index form), plus the ONE local lemma of the allocator site 0x81f4c.
     B81ec4_at j (k <= 14+2j)   --S_F1--> B81f50_at j | B82eac   malloc @0x81f4c (ctl_W4a_malloc_81f4c); the B82eac
                                                         exit is dead (an unused premise, as ACtl.v's seg_F1 carries it)
     B81f50_at j (k <= 14+2j+1) --S_F2--> B81f78_at j        len > 0: __asan_memcpy @0x81f74
                                        | B82048_at j        len = 0: reac_ctrl_parse @0x82044
     B81f78_at j                --S_F3--> B81fbc_at j        len >= 50: reac_ctrl_parse @0x81fb8
                                        | B82048_at j        len < 50: reac_ctrl_parse @0x82044
     B81fbc_at j                --S_F4--> B82098_at j        (inline stretch, no call)
     B82048_at j                --S_F5--> B8215c_at j        reac_ctrl_parse @0x82158
     B82098_at j                --S_F6--> B8215c_at j        the 32-turn byte sum (run-level loop), reac_ctrl_parse @0x82158
   From B81f50_at on the live list is entry ++ [(phi, flen cx j)] (fcutp_body / the record's own Permutation).

   ROUTE, BUILD STATE, SHELL GAPS (G1) / (G2), the shared Section hypotheses tfibsegs_rsegs / Hwx / RTP / rt_of_core
   (FEVT is CITED: B.ProgBridge.fevt_of_evtF) and
   the PENDING KIT / BRIDGE FACTS: exactly as lib/B/ACtlW0.v's header.  The frame-pointer chain and call trace at the
   allocator call are the shell's `ACtlCut.ctl_chain` / `ACtlCut.ctl_trace_in`; their source is the Section hypothesis
   CHAIN_OF_CUT (the shell's former ctl_chain_of_cut, which lib/B/ACtl.v now carries as its own Section hypothesis
   CHAIN_OF_CUT; same name and text here, copied from the sibling W2a, so the top discharges this one with its own).
   The site lemma takes chain_pre and the trace as premises, as the sibling W2a's site lemmas do.

   SECTION HYPOTHESES OF THIS FILE (sources):
   - AMALLOC4 : Reusable.YC5d.amalloc04_rule segs B MT (donor YC5d.v:56-74; the core's allocator rule for B, a Theorem Labs lane's
     core slice, plan M13), named ONLY in ctl_W4a_malloc_81f4c.  HMOK: the trivial meter (donor A/AD2o.v:49, MT_FREE).
     HPCM: B's malloc wrapper entry by the core's catalogue name (the sibling W2a's text).
   - AMEMCPY : __asan_memcpy @0x81f74, the core's rule `aintrin_realizes segs B OCpy <pc>` (donor YG0d.v:317-335) at the
     catalogue NAME Reusable.YB1w.tfib_A_asan_memcpy (porter 23:00Z), through Reusable.YCbq.aj_intrin_at (YCbq.v:1953).
   - CITED, not Section hypotheses (the 15:40Z swap of RTPOST-SHARED-B.txt (a working note, not in this delivery; the swap written on a working branch 3131914eb3ca): lib/B/ProgWorld.v
     and lib/B/ProgBridge.v are in the tree):
     B.ProgWorld.ctl_post_memcpy (ProgWorld.v:765): AMEMCPY's world-form post as visible-address facts; WR = the
       written range plus the callee window [sp - ESTACK, sp).  Used at 0x81f74 (seg_F2 step 1).
     B.ProgWorld.ctl_post_acall_kept (ProgWorld.v:681): from acall_kept, where amalloc04_rule ends, the mrd read is
       kept at a visible address of a kept class (B.ProgWorld.kept_class; the local notation kept_class is its text).
       Used at 0x81f4c (seg_F1 step 3): E = the new block [res, res + req_size (flen cx j)), [slo, shi) =
       [A - ASTACK, A); and at the reac_ctrl_parse calls.
     B.ProgBridge.img_vis_W (ProgBridge.v:121): the image range [IMG_LO, IMG_HI) is visible in every world.  Used for
       PARSE's image premise and the KIND_NAME bytes.
     B.ProgBridge.fevt_of_evtF (ProgBridge.v:30): the lift w4_lift.
     The last two are the former Section texts UP TO CONVERSION: Reusable.YB1v.tfibsegs = B.Img0.rsegs
     (B.ProgBridge.tfibsegs_rsegs, reflexivity); range_visible and B.Prog.ImgBounds.IMG_LO / IMG_HI unfold to the
     former written-out bounds 0x10000 / 0x5fe000 (Reusable.YImgTop.IMG_LO / IMG_TOP).
   - LAWS / segs_low : the core's AR laws for B and the image's place below kLowMemEnd, the sibling
     lib/B/ACtlW4e1.v:236-237 text token for token.  Used by the stage kit only (heap / frame visibility, the journal
     step YCbq.ajournal_exec).  Obligation: the core's api_of_core (aa_laws) and B's segment table; owner the core
     (a Theorem Labs lane).
   - ROUTE (C) (a working branch shell 78699c46fe7): the cut's runtime premise is B.ACtlRtC.ctl_rt_C B ly3 S3 mem3; the stages
     never read it (they consume no shadow_rw) and SUPPLY it at each successor cut by w4a_ctlrt, which cites the proved
     B.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws + AR + arodata_okP; no stage-level runtime hypothesis).
   STAGE KIT (local lemmas w4a_*, after the Section hypotheses): the lift w4_lift (cfg_at -> the `_F` run's MS state,
   Reusable.YA0nR.SRr_fevt_hid over B.ProgBridge.RNG_W), the journal step w4a_aj_run (YCbq.ajournal_exec for a run
   whose writes lie in the stack window or the owned frame), heap / frame visibility from LAWS, and one move lemma per
   cut predicate (it survives a change of registers and memory that keeps the bytes it reads).
   PENDING CALLEE CONTRACTS:
   - reac_ctrl_parse (cut callee; it takes its own class-1 fake frame at its __asan_stack_malloc_1 0x83e74, so the stage
     CUTS at each call and composes the callee's cgif-form contract between `_pre_F` and `_post_F`): owner lane
     a Theorem Labs lane (route table a Theorem Labs lane 22:31Z); name pending, written below as `PARSE` in the plans.  Caller obligations
     = reac_ctrl_parse_contract_F premises (a6 reac_ctrl_parse_c.v:305; `_x_F` :179): a0 = Phi (the turn block, live,
     HB), a1 = len, a2 = [A + 280] = fr + 176 (FLI) at 0x81fb8 / 0x82044 and a2 = 0 at 0x82158; the 36 record bytes
     [fr + 176, fr + 212) addressable (the five record-shadow stores just before the call); the callee window
     [sp - 8800, sp) present (8800 <= LLVMF_STK - 479); post: a0 = t_k j (fst (ctrlparse len (t_g j))), the record
     bytes = the parse struct (pBb), write set = the callee window, its class-1 fake frame and their shadow.
   `_F` HYPOTHESES (a Theorem Labs lane; module ..lib.B.Prog.Seg.<File>F; RNG-first; split at EVERY call, a Theorem Labs lane 23:15Z).
   PUBLISHED texts are cited by Requiring their module, qualified (a Theorem Labs lane 23:38Z / 23:4xZ); statuses as of
   bF-statements/ at 00:25Z; all of W4a on a Theorem Labs lane,
   a working branch a1dafb91d7d (F4F on a Theorem Labs lane):
   - F1F: f1_body_F (F1.v:149), f1_tail2_F (:207), f1_tail1_F (:240) (sub-runs, no call) and f1_evt_F (:294, 0x81ec4 ->
          the malloc wrapper entry 0x534b8, ra = 0x81f50 = the cut, so no post) (a Theorem Labs lane; + the `_of_F` compares)
                                                                                               PUBLISHED, proved
   - F2F: f2_head0_F (:80, 0x81f50 -> 0x82020), f2_head1_F (:109, 0x81f50 -> 0x81f68), f2_st_F (:142, the
          record-shadow stores), f2_pcall_pre_F (:286, to reac_ctrl_parse's entry 0x83e04 = PCF.REAC_CTRL_PARSE,
          ra = 0x82048 or 0x81fbc), f2_mcpy_pre_F (:346, to __asan_memcpy 0x52164, ra = 0x81f78 = the cut, no post)
          (a Theorem Labs lane; f2_parse_at :174 is the callee step itself: NOT re-run, the glue composes PARSE there)
                                                                                               PUBLISHED, proved
   - F3F.f3_head_F (a Theorem Labs lane; F3.v:26-75, 0x81f78 -> 0x81f94 / 0x82020; + f3_head_of_F)   PUBLISHED, proved (build
          in progress); with F2F.f2_st_F and F2F.f2_pcall_pre_F at the two parse blocks
   - F4F.seg_F4_eq88_F / F4F.seg_F4_ne88_F (a Theorem Labs lane, a working branch 007c7fd6c63; seg_F4 :183 cut at the branch
          0x81fe8 on record byte 12 = 0x88; no call; + the `_run` compares)                   PUBLISHED, proved
   - F5F.c_pre_F (F5.v:855; c_evt is the parse-call block 0x8214c -> 0x8215c: four instructions to the call 0x82158;
          ra = 0x8215c = the cut, so no post; no rng premise) (a Theorem Labs lane)                       PUBLISHED, proved
   - F5F.seg_F5_F (+ seg_F5_run_of_F): the inline stretch 0x82048 -> 0x8214c of seg_F5 (the short-frame arm), cut from
          seg_F5_run's own steps (F5.v:1874-1899); premises rg regs 10 0 (a0 = t_k j = 0, so `bnez a0,0x82fa4` falls
          through), rg regs 9 A, 0 <= A, A + 320 <= 2^64 and the four save-area word writes' rng; no call, no shadow
          check                                                                               PUBLISHED, proved
   - F6F: f6_loop_F (F6.v:210, the 32-turn byte sum, a run-level loop) and f6_run_evt_F (:301, 0x82098 -> 0x8214c;
          neither calls), then F5F.c_pre_F (a Theorem Labs lane)                                PUBLISHED, proved (build running)
   PROVENANCE: cut table rows 41-46; plan 2.3 rows 41-46, 2.5 (row 0x81f4c), 3 (frame loop), 6.2 rows S_F1 / S_F3 /
   S_F4 / S_F6, F.4.1 rows 9-18; runs at 3803efccea0 (F1-F6); objdump L84725-L84900.

   ABORT-SINK / TRAP OBLIGATIONS ON W4a (all branches into 0x82fa4 / 0x82fa0 in 0x81ec4-0x82158, one awk over the
   listing): 0x81ed4 / 0x81f04 / 0x81f3c (T10-T12, -> 0x82fa0), 0x81f5c (`j 0x82fa4`), 0x81f84 / 0x81f90 (T13-T14),
   0x81fc8 / 0x81ff4 (T15-T16), 0x82048 (`bnez a0,0x82fa4`), 0x8209c / 0x820e0 / 0x8210c (T17-T19), 0x82138
   (`bne a0,a2,0x82fa4`).  Each is refuted in the stage that contains it (closing summary).  The inline ASan checks
   (input bytes 0x81ed8 / 0x81f08, record bytes 0x81fcc / 0x81ff8, the byte sum 0x820a0, bytes 16 / 17 0x820e4 /
   0x82108) are not-taken steps of the same runs (their report calls are never reached). *)

From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn Reusable.YImgTop.
(* The core's read-only-data predicate (YE01.arodata_okS, ctl_base's conjunct) and the generic cgif-form pieces
   APostBase (afobj, ro_below_ofl, arodata_ok_journalP), for PARSE and its arodata premise. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE01 Reusable.APostBase.
(* Route (C)'s runtime fact at a cut (B.ACtlRtC.ctl_rt_C, from the core's AR by a Theorem Labs lane's proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR, with the read-only predicate it takes, B.Prog.CtrlBase.arodata_okP, from
   ctl_base's arodata_okS by B.ProgWorld.arodata_okP_of_S) and a Theorem Labs lane's image-B parse spec. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m B.ProgWorld B.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_parse.
(* lib/Lib/Mem.v, Required only (never Imported), for the saved-register bytes in CHAIN_OF_CUT's premise. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
(* lib/Lib's raw-memory vocabulary of the call-post fact below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step.
(* The kit's bridge (lib/B/ProgBridge.v: RNG_W, rng_RNG_W, fp_avoids_RNG_W, cfg_at_MS), lib/Lib's register
   transport, and the pure facts the stages cite from the `_F` files' own closure, qualified (never Imported, never
   their runs): SlotInv.t_g_of_phi, Seg.F1.f1_ID_len / f1_FG_len / f1_body_len / f1_kn_len, Seg.F2.f2_tB_len,
   Seg.F4.f4_sh_at, Seg.F5.c_tg_len / c_byte_range. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss B.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F1 F2 F4 F5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's published `_F` modules (Required qualified, never Imported, a Theorem Labs lane 23:38Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F1F F2F F3F F4F F5F F6F.
Import ListNotations.
Local Open Scope Z_scope.

Section W4a.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING (see ACtlW0.v): the only lines that name ACtlCut's / ACtlCutP's argument lists. ---- *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ctl_base := (ACtlCut.ctl_base B MT XM_LIB RLO RHI).
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation own6 := ACtlCut.own6.
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation ENTRYBL cx := (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)).
Local Notation flen := ACtlCutP.flen.
Local Notation C_B81ec4_at := (ACtlCutP.C_B81ec4_at B).
Local Notation C_B81f50_at := (ACtlCutP.C_B81f50_at B).
Local Notation C_B81f78_at := (ACtlCutP.C_B81f78_at B).
Local Notation C_B81fbc_at := (ACtlCutP.C_B81fbc_at B).
Local Notation C_B82048_at := (ACtlCutP.C_B82048_at B).
Local Notation C_B82098_at := (ACtlCutP.C_B82098_at B).
Local Notation C_B8215c_at := (ACtlCutP.C_B8215c_at B).
Local Notation C_B82eac := (ACtlCutP.C_B82eac B).

(* ---- Section hypotheses (sources in the header and in ACtlW0.v's) ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* rt_of_core, placeholder form (a Theorem Labs lane 22:44Z; no APIf, a Theorem Labs lane 23:05Z).  TODO: B's bridge statement verbatim. *)
Variable RTP : (word -> option byte) -> Prop.
Hypothesis rt_of_core : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> RTP mem.

(* The core's allocator rule (named only in ctl_W4a_malloc_81f4c), the trivial meter, B's malloc wrapper entry. *)
Hypothesis AMALLOC4 : Reusable.YC5d.amalloc04_rule segs B MT.
Hypothesis HMOK : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis HPCM : Reusable.YG0f.pc_wrap_malloc (Reusable.YG0f.as_code B) = Reusable.YB1w.tfib_A_malloc.

(* __asan_memcpy @0x81f74: the core's memcpy rule at B's catalogue name. *)
Hypothesis AMEMCPY :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy.

(* munch_vis / wmono_vis / rt_post_frame / kept_class: the local notations of B.ProgWorld's Definitions of the same
   names (the walk's shared RtPost text); the posts themselves are CITED: B.ProgWorld.ctl_post_memcpy and
   B.ProgWorld.ctl_post_acall_kept. *)
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
Local Notation kept_class B lyc Sc slo shi E a :=
  ((lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 /\ ~ (slo <= a < shi)) \/
   (exists b m i, In (b, m) (Reusable.YG0d.ablocks B lyc Sc) /\ 0 <= i < Reusable.YG00.req_size m /\
      a = b + i /\ ~ E (b + i)) \/
   (Reusable.YG0d.in_img segs a /\ ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
      ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4)) \/
   (exists cid pos, In (cid, pos) (Reusable.YG01.frames Sc) /\
      (Reusable.YG0n.in_zr a (Reusable.YCbq.frame_rng lyc (cid, pos)) \/
       Reusable.YG0n.in_zr a (Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr lyc cid pos),
                              Reusable.YG00.fs_frame_bytes cid / 8)) /\ ~ E a)).

(* Two image-B data facts, pasted TOKEN FOR TOKEN from the shared RTPOST-SHARED-B.txt (not in this delivery; owner a Theorem Labs lane,
   proved there in lib/B/ProgBridgeData.v): the stages carry FLI's KNT across the allocator call (seg_F1) and the
   reac_ctrl_parse calls (seg_F2 / F3 / F5 / F6). *)
(* V6 twin for the KIND_NAME table (added 04:35Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as V6): FLI's KNT (ACtlCutP.v, `addressable m KNA.KIND_NAME 112`, carried by every LK cut) crosses a runtime
   call only through AR, since the image's shadow is allocator-owned. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* T10 twin for the KIND_NAME table (added 05:24Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as T10): KNT's 112 bytes at KIND_NAME (RELRO) are neither a static owned extent nor the errno cell, so
   ctl_post_acall_kept's image arm keeps them across an allocator call or a reac_ctrl_parse call. *)
Hypothesis ctl_kind_name_not_owned : forall a : Z,
  B.ACtlCutP.KNA.KIND_NAME <= a < B.ACtlCutP.KNA.KIND_NAME + 112 ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

(* The runtime fact at a cut, ROUTE (C) (a Theorem Labs lane 09:20Z / 11:03Z; a working branch shell a Theorem Labs lane 78699c46fe7): a stage supplies
   B.ACtlRtC.ctl_rt_C at a successor cut by B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w4a_ctlrt) and carries these lines of the
   shared lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) token for token, MINUS its two route-(A) lines (the vis0-shadow and owned-ro
   premises), which route (C) deletes (a Theorem Labs lane's w4C brief item 3 (a working note, not in this delivery)).  arodata_okP at the state comes from ctl_base's
   arodata_okS through Reusable.APostBase.arodata_ok_journalP (which finds RO_OFL as an instance).  The top discharges
   all three: TFIB_SYMS := Reusable.YD2l.CtrlB_syms, RELRO_IMG := relro_img_CtrlB, RO_OFL by computation at
   SK := Reusable.YE2k.tfib_sink_head. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* The frame-pointer chain and the call trace at an allocator call: lib/B/ACtl.v's Section hypothesis CHAIN_OF_CUT,
   same name and text (the sibling W2a's, lib/B/ACtlW2a.v:199-217). *)
Hypothesis CHAIN_OF_CUT : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word) (pc0 ra : Z),
  ctl_base cx ->
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     lib.Lib.Mem.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 448 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81764);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81aa0);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81f50);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82d1c)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* LAWS / segs_low: the core's AR laws for B and the image's place below kLowMemEnd (the sibling W4e1's text, token for
   token; obligation: the core's api_of_core (aa_laws) and B's segment table; owner: the core (a Theorem Labs lane)). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* ---------------------------------------------------------------------------------------------------------
   PARSE: the cut callee reac_ctrl_parse in the cgif caller-journal form, cited as a Theorem Labs lane's IMAGE-B statement of
   record: lib/B/Prog/C_reac_ctrl_parse.v (a working branch ea59dbb03aa, taken by path; blob
   16774c751f5), `treac_ctrl_parse_spec (SK := SK) SEGS B RLO RHI` at SEGS := this walk's segs.  Image B's own entry
   0x83e04 and window 8800 (lib/B/Prog/reac_ctrl_parse_c.v:10, :13).  ONE named Section hypothesis, used by seg_F2
   (len = 0 arm), seg_F3, seg_F5, seg_F6 through w4a_parse.  OBLIGATION: a Theorem Labs lane proves it for image B
   (pb_reac_ctrl_parse); the TOP discharges it. *)
Hypothesis PARSE : B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) segs B RLO RHI.

(* The same contract in continuation form (the stages' shape): PARSE's post, bound by SRr_bind. *)
Lemma w4a_parse : forall STK sp0 FPc ly S W0 mem0 md0 own lyc Sc (W : Reusable.YA0n.world segs) memc mdc k
    (regs : bvmap 5 word) (f n o : Z) (fr50 : list byte)
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPc ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) memc) ->
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= Reusable.YG0d.raZ regs ->
  lib.Reusable.YK11.getr regs 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 f -> lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 n ->
  lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 o -> 0 <= n < 2 ^ 64 ->
  Reusable.YG0d.spZ regs mod 16 = 0 ->
  sp0 - STK <= Reusable.YG0d.spZ regs - ACtlCutP.RCP.REAC_CTRL_PARSE_K -> Reusable.YG0d.spZ regs <= sp0 ->
  Reusable.YG01.count_cid 1 (Reusable.YG01.frames Sc) < Reusable.YG00.fs_frames 1 ->
  (50 <= n -> exists Lf, In (f, Lf) (Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= Reusable.YG00.req_size Lf) ->
  (o <> 0 -> Reusable.APostBase.afobj segs B lyc Sc W memc o 36) ->
  (o <> 0 -> forall a, o <= a < o + 36 ->
     Reusable.YCbq.awr_byte STK sp0 FPc (Reusable.YG0d.ablocks B ly S) (Reusable.YG0d.ablocks B lyc Sc) lyc own a) ->
  length fr50 = 50%nat ->
  (50 <= n -> forall i, (i < 50)%nat ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) memc (f + Z.of_nat i) = Some (ACtlCutP.RPA.cp_v fr50 i)) ->
  (forall (W2 : Reusable.YA0n.world segs) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     Reusable.YA0n.wle W W2 ->
     Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPc ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
     Reusable.YG0d.aregs_preserved regs regs2 ->
     Reusable.YG01.frames S2 = Reusable.YG01.frames Sc ->
     Reusable.YG0d.ablocks B ly2 S2 = Reusable.YG0d.ablocks B lyc Sc ->
     (exists ff, S2 = Reusable.YG00.set_fs ff Sc) ->
     lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 (fst (ACtlCutP.RPA.ctrlparse n fr50)) ->
     (o <> 0 -> forall i, (i < 36)%nat ->
        Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 (o + Z.of_nat i) =
        Some (bv_unsigned (nth i (snd (ACtlCutP.RPA.ctrlparse n fr50)) ACtlCutP.RPA.cp_z))) ->
     Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2
       (Reusable.YG0d.spZ regs - ACtlCutP.RCP.REAC_CTRL_PARSE_K) (Reusable.YG0d.spZ regs)
       (fun a => o <= a < o + 36) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs (Reusable.YG0d.raZ regs) regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs ACtlCutP.RCP.REAC_CTRL_PARSE regs memc mdc) Q.
Proof using PARSE.
  intros STK sp0 FPc ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr50 Q
    HJ HRO Hret Hra Hgp Htp Ha0 Ha1 Ha2 Hn Hsp16 Hwin Hsp Hcid Hblk Hfo Haw Hlen Hrd HK.
  eapply Reusable.YA0n.SRr_bind.
  { exact (PARSE STK sp0 FPc ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr50
             HJ HRO Hret Hra Hgp Htp Ha0 Ha1 Ha2 Hn Hsp16 Hwin Hsp Hcid Hblk Hfo Haw Hlen Hrd). }
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hab2 & Hfs2 & Ha02 & Hrec2 & HK2).
  replace (lib.Reusable.YK11.getr regs 1) with (Reusable.YG0d.w64 (Reusable.YG0d.raZ regs)).
  - exact (HK W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2 Hfr2 Hab2 Hfs2 Ha02 Hrec2 HK2).
  - unfold Reusable.YG0d.w64, Reusable.YG0d.raZ. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
Qed.


(* The five record-shadow stores S(fr) + 22 .. 26 (0x82020-0x82034 and 0x81f94-0x81fa8) are a Theorem Labs lane's
   B.Prog.Seg.F2F.f2_st_noinv_F (lib/B/Prog/Seg/F2F.v, a working branch 11d4060c0f0, commit
   ade8bed0efa): f2_st_F without the `mem_inv rsegs m` premise and post conjunct, which the cgif-form cut does not
   carry (ACtlCut.v section 4).  Written by a Theorem Labs lane at this lane's request (via a Theorem Labs lane, 05:4xZ-06:1xZ); cited by
   name, never copied.  Its one memory premise is `rw_cells rsegs m (bv_unsigned s3 + 22) [CB 5 junk]`, which the
   stage builds from the owned frame's shadow by w4a_rw5 below. *)


Lemma w4a_arodata_cut : forall cx own ly3 S3 W3 mem3 md3 k, ctl_base cx ->
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof using RELRO_IMG RO_OFL.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _) & _).
  exact (Reusable.APostBase.arodata_ok_journalP (RO := RO_OFL) segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           HJ HRO).
Qed.

(* =========================================================================================================
   STAGE KIT: local lemmas the six stages share (none touches the allocator).  Every proof below names the Section
   hypotheses it uses (Default Proof Using "Type" plus a `Proof using` line), so a stage's closed statement carries
   exactly the hypotheses its proof needs.
   ========================================================================================================= *)
#[local] Set Default Proof Using "Type".

Lemma w4a_wa_u : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. exact (lib.Lib.Mem.wa_unsigned x Hx). Qed.

Lemma w4a_rgv_inj : forall regs (r : bv 5) a b, ACtlCut.rgv regs r a -> ACtlCut.rgv regs r b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ha' Hb'. unfold ACtlCut.rgv in *. rewrite Ha in Hb.
  apply (f_equal (@bv_unsigned 64)) in Hb. rewrite !w4a_wa_u in Hb by lia. exact Hb.
Qed.

Lemma w4a_rgv_move : forall regs regs' (r : bv 5) v, ACtlCut.rgv regs r v ->
  lib.Reusable.YK11.getr regs' r = lib.Reusable.YK11.getr regs r -> ACtlCut.rgv regs' r v.
Proof. intros regs regs' r v H E. unfold ACtlCut.rgv in *. rewrite E. exact H. Qed.

Lemma w4a_mrd_munch : forall W m m' x, lib.Lib.Frame.munch W m m' -> 0 <= x < 2 ^ 64 -> lib.Lib.Frame.outside W x ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x).
Proof.
  intros W m m' x MU Hx Ho. unfold lib.Lib.Mem.mrd. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite w4a_wa_u by exact Hx. exact Ho.
Qed.

Lemma w4a_ba_keep : forall m m' a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

Lemma w4a_addr_keep : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

Lemma w4a_spill_keep : forall regs regs' m m' A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x)) ->
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
  subst A'. exists A. split; [exact (w4a_rgv_move regs regs' 9 A Hr9 E9)|].
  unfold ACtlCutP.q64 in *. apply (w4a_ba_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

Lemma w4a_aj_bits : forall cx own ly3 S3 W3 mem3 md3 k, AJ cx own ly3 S3 W3 mem3 md3 k ->
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

(* Route (C)'s runtime fact at any cut state of the walk: a Theorem Labs lane's PROVED B.ProgWorldCtlRtC.ctl_rt_C_of_AR at this
   file's TFIB_SYMS / LAWS, with its arodata_okP premise from ctl_base's arodata_okS through
   B.ProgWorld.arodata_okP_of_S.  The cut state's own ly3 / S3 are the ones ctl_rt_C names. *)
Lemma w4a_ctlrt : forall cx own ly3 S3 W3 mem3 md3 k, ctl_base cx ->
  AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof using LAWS RELRO_IMG RO_OFL TFIB_SYMS.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ)) as HAR.
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 HAR
           (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (w4a_arodata_cut cx own ly3 S3 W3 mem3 md3 k HB HJ)
              ltac:(lia) ltac:(lia))).
Qed.

Lemma w4a_rng : forall (W : Reusable.YA0n.world segs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof. intros W lo len H0 H1 H2. exact (B.ProgBridge.rng_RNG_W _ lo len H0 H1 H2). Qed.

Lemma w4a_aview_vis : forall (W : Reusable.YA0n.world segs) mem s,
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem s <> None -> Reusable.YA0n.w_H W (Z_to_bv 64 s) = false.
Proof.
  intros W mem s Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 s)) eqn:EH; [exfalso|reflexivity].
  apply Hv. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite EH.
  unfold lib.Reusable.YK11.seg_rom.
  rewrite (lib.Reusable.YK04.memory_read1_hidden _ _ (Reusable.YA0n.w_Hoff W) _ EH). reflexivity.
Qed.

Lemma w4a_blk : forall ly S (W : Reusable.YA0n.world segs) mem md p n,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + Reusable.YG00.req_size n <= lib.Reusable.YM05.alloc_ceiling /\
  0 <= n /\ n <= Reusable.YG00.req_size n /\
  (forall a, p <= a < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) /\
  (forall x, p <= x < p + Reusable.YG00.req_size n ->
     Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr x)) = false).
Proof using LAWS.
  intros ly S W mem md p n HAR Hin.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin)
    as (H16 & H4096 & Hceil & _ & Hpres & _ & Hn).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [_ Hh].
  pose proof (Reusable.YCbq.req_size_pos n ltac:(lia)) as Hrs.
  split; [exact H16|]. split; [exact H4096|]. split; [exact Hceil|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (proj1 (proj1 (Hpres a Ha)))|].
  intros x Hx. apply (w4a_aview_vis W mem). apply Hh.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  assert (D1 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : x / 8 <= (p + Reusable.YG00.req_size n - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.mul_div_le (2147450880 + p / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (2147450880 + (p + Reusable.YG00.req_size n - 1) / 8) 8 ltac:(lia)) as M2.
  pose proof (Z.mod_pos_bound (2147450880 + (p + Reusable.YG00.req_size n - 1) / 8) 8 ltac:(lia)) as M3.
  lia.
Qed.

Lemma w4_lift : forall (W : Reusable.YA0n.world segs) (pc : Z) (regs : bvmap 5 word) mem md
    (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
       (lib.Reusable.YK11.seg_rom B.Img0.rsegs)) ->
  (forall ms' md', P ms' -> (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof using tfibsegs_rsegs Hwx.
  intros W pc regs mem md P Q HE HK.
  rewrite B.ProgBridge.cfg_at_MS.
  eapply Reusable.YA0nR.SRr_xregs_eqv; [| apply Lib.Regs6ss.xregs_eqv_sym, Lib.Regs6ss.mkR_of_eqv].
  replace (lib.Reusable.YK11.seg_rom segs) with (lib.Reusable.YK11.seg_rom B.Img0.rsegs)
    by (rewrite tfibsegs_rsegs; reflexivity).
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W _ md (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P Q).
  - exact (B.ProgBridge.fevt_of_evtF _ _ _ HE).
  - exact (B.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W)).
  - intros ms' md' HP Hh Hs. exact (HK ms' md' HP Hh Hs).
Qed.

(* ---- address facts the stages share ---- *)
Lemma w4a_spZ : forall regs, 0 <= Reusable.YG0d.spZ regs < 2 ^ 64.
Proof.
  intros regs. unfold Reusable.YG0d.spZ.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma w4a_noseg : forall a, 0x5fe000 <= a -> find_segment B.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. apply (lib.Reusable.YK04.find_segment1_none_above _ 0x5fe000); [vm_compute; reflexivity | exact Ha].
Qed.

Lemma w4a_some_of_wmono : forall m m' a, 0x5fe000 <= a < 2 ^ 64 -> (exists b, m (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> exists b, m' (Z_to_bv 64 a) = Some b.
Proof.
  intros m m' a Ha (b & Hb) WM.
  assert (Hw : wview B.Img0.rsegs m (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hb; discriminate).
  pose proof (WM _ Hw) as Hw'. unfold wview in Hw'.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  rewrite w4a_wa_u in Hw' by lia. rewrite (w4a_noseg a ltac:(lia)) in Hw'. contradiction.
Qed.

Lemma w4a_outside_dec : forall (WR : list (Z * Z)) x, lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & H'); exact (H H')].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* A run of the stage (a footprint run whose post is munch WR / wmono) keeps the journal when each written byte is
   in the journal's stack window or the owned frame / frame shadow (YCbq.ajournal_exec, the window / in_frames cases
   of awr_byte). *)
Lemma w4a_aj_run : forall cx own ly3 S3 W3 mem3 md3 k mem' md' (WR : list (Z * Z)),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Lib.Frame.munch WR mem3 mem' -> lib.Lib.Frame.wmono B.Img0.rsegs mem3 mem' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, ~ lib.Lib.Frame.outside WR a -> 0x5fe000 <= a < 2 ^ 64 /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\
      Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ENTRYBL cx)
        (Reusable.YG0d.ablocks B ly3 S3) ly3 own a) ->
  AJ cx own ly3 S3 W3 mem' md' k.
Proof using LAWS segs_low.
  intros cx own ly3 S3 W3 mem3 md3 k mem' md' WR HJ MU WM Hhid Hsame HW.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md'
           (fun a => ~ lib.Lib.Frame.outside WR a) HJ).
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (w4a_outside_dec WR (bv_unsigned x)) as [H|H]; [exact H | contradiction].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x) eqn:EH; [exact Hx|].
    destruct (w4a_outside_dec WR (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
    destruct (HW _ Ho) as (Hr & Hs & _).
    destruct (w4a_some_of_wmono mem3 mem' (bv_unsigned x) Hr Hs WM) as (b & Hb).
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
  - exact Hhid.
  - exact Hsame.
  - intros a Ha. exact (proj2 (proj2 (HW a Ha))).
Qed.

(* The owned class-6 frame: its address, its bytes and shadow (visible, present, owned by the journal). *)
Lemma w4a_frame : forall cx k ly3 S3 W3 mem3 md3 fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  fr mod 32 = 0 /\ 4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\ Reusable.YCbq.in_frames ly3 (own6 cx) a) /\
  (forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
      Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\ Reusable.YCbq.in_frames ly3 (own6 cx) a).
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

Lemma w4a_saved_len : forall cx, Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104.
Proof. intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. Qed.

(* ---- moves: a cut predicate survives a change of registers and memory that keeps what it reads ---- *)
Local Notation AGR m m' x := (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 x)).
Local Notation getr := lib.Reusable.YK11.getr.

Lemma w4a_frac_move : forall cx fr sel regs regs' m m',
  ACtlCutP.FRAC B cx fr sel regs m ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  (forall A x, ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
     A + 40 <= x < A + 56 \/ A + 336 <= x < A + 344 \/ fr <= x < fr + 24 \/
     ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW \/ ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx \/
     fr + 4088 <= x < fr + 4096 ->
     AGR m m' x) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' HF E2 E3 E4 E8 E9 E19 E26 K.
  destruct HF as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & (sh & Hsh & Hshl) & Hsaved & Qtr).
  pose proof (w4a_spZ regs) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  unfold ACtlCut.c_sp in *.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  exists A, sp.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact Hr4|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr8 E8)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|].
  split; [rewrite E3; exact Hr3|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr19 E19)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr26 E26)|].
  do 8 (split; [assumption|]).
  unfold ACtlCutP.q64 in *.
  split; [apply (w4a_ba_keep m m' _ _ Q336); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q48); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q40); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh1); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh2); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split.
  - exists sh. split; [|exact Hshl]. apply (w4a_ba_keep m m' _ _ Hsh). rewrite Hshl.
    intros x Hx. apply (K A x Hr9 HA). right; right; right; left. rewrite Z2Nat.id in Hx by (unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES; lia). lia.
  - split; [apply (w4a_ba_keep m m' _ _ Hsaved); rewrite w4a_saved_len; intros x Hx; apply (K A x Hr9 HA); lia|].
    apply (w4a_ba_keep m m' _ _ Qtr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply (K A x Hr9 HA). lia.
Qed.

Lemma w4a_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x /\ AGR m m' (B.AsanRT.shadow_addr x)) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS KI HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & HKNa) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split.
  { split.
    - apply (w4a_ba_keep m m' _ _ HKNb). pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
      intros x Hx. apply KI. lia.
    - apply (w4a_addr_keep m m' _ _ HKNa). intros i Hi. apply KI. lia. }
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.

Lemma w4a_our_move : forall cx fr m m', ACtlCutP.OURb cx fr m ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) -> ACtlCutP.OURb cx fr m'.
Proof.
  intros cx fr m m' H KF. unfold ACtlCutP.OURb in *. apply (w4a_ba_keep m m' _ _ H).
  rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply KF. cbn in Hx. lia.
Qed.

Lemma w4a_lk_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off (240 :: [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304]) -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x /\ AGR m m' (B.AsanRT.shadow_addr x)) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS KI HSTK.
  split; [exact Hj|].
  split; [apply (w4a_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply (KA 240 x); [left; reflexivity | exact Hx]|].
  split; [exact (w4a_our_move cx fr m m' HOUR KF)|].
  apply (w4a_fli_move cx fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27); [|exact KS | exact KI | exact HSTK].
  intros off x Hoff Hx. apply (KA off x); [right; exact Hoff | exact Hx].
Qed.

Lemma w4a_fsj_move : forall cx fr j regs regs' m m',
  ACtlCutP.FSj cx fr j regs m ->
  (forall x, fr + 2880 <= x < fr + 2920 -> AGR m m' x) ->
  (forall x, fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' (Hhave & Hn & Hbody & Had & HFI) KF KS.
  pose proof (B.Prog.Seg.F1.f1_body_len (ACtlCut.c_in cx) j) as HL.
  unfold ACtlCutP.FSj, ACtlCutP.FSb.
  split; [unfold ACtlCutP.u32 in *; apply (w4a_ba_keep m m' _ _ Hhave); rewrite lib.Lib.Mem.length_le4;
          intros x Hx; apply KF; lia|].
  split; [unfold ACtlCutP.b8 in *; apply (w4a_ba_keep m m' _ _ Hn); cbn [length]; intros x Hx; apply KF; lia|].
  split; [apply (w4a_ba_keep m m' _ _ Hbody); intros x Hx; apply KF; lia|].
  split; [apply (w4a_addr_keep m m' _ _ Had); intros i Hi; apply KS; lia|].
  exact HFI.
Qed.

Lemma w4a_rec0_move : forall cx fr j m m',
  ACtlCutP.REC0 cx fr j m -> (forall x, fr + 2688 <= x < fr + 2840 -> AGR m m' x) ->
  ACtlCutP.REC0 cx fr j m'.
Proof.
  intros cx fr j m m' ((HID & Hok) & (HFG & Hfok)) KF.
  split; split; [| exact Hok | | exact Hfok].
  - unfold ACtlCutP.IDBe in *. apply (w4a_ba_keep m m' _ _ HID). rewrite B.Prog.Seg.F1.f1_ID_len.
    intros x Hx. apply KF. lia.
  - unfold ACtlCutP.FGBe in *. apply (w4a_ba_keep m m' _ _ HFG). rewrite B.Prog.Seg.F1.f1_FG_len.
    intros x Hx. apply KF. lia.
Qed.

Lemma w4a_fps_move : forall cx fr j m m',
  ACtlCutP.FPS cx fr j m -> (forall x, fr + 176 <= x < fr + 212 -> AGR m m' x /\ AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.FPS cx fr j m'.
Proof.
  intros cx fr j m m' (HB & HA) K. split.
  - unfold ACtlCutP.pBb in *. apply (w4a_ba_keep m m' _ _ HB). rewrite B.Prog.Seg.F2.f2_tB_len.
    intros x Hx. apply K. lia.
  - apply (w4a_addr_keep m m' _ _ HA). intros i Hi. apply K. lia.
Qed.

Lemma w4a_hb_move : forall m m' phi len, ACtlCutP.HB m phi len ->
  (forall x, phi <= x < phi + B.ACtlK.a_size len -> AGR m m' (B.AsanRT.shadow_addr x)) -> ACtlCutP.HB m' phi len.
Proof.
  intros m m' phi len (Hnz & HA) K. split; [exact Hnz|].
  apply (w4a_addr_keep m m' _ _ HA). intros i Hi. apply K. lia.
Qed.

Lemma w4a_fturn_move : forall cx j phi regs regs' m m' A,
  ACtlCutP.FTURN cx j phi regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 ->
  (forall x, A + 224 <= x < A + 240 -> AGR m m' x) ->
  (forall x, phi <= x < phi + ACtlCutP.flen cx j -> AGR m m' x) ->
  ACtlCutP.FTURN cx j phi regs' m'.
Proof.
  intros cx j phi regs regs' m m' A (S224 & S232 & Hph & Hlen) H9 HA0 HA1 E9 KA KP.
  split; [apply (w4a_spill_keep regs regs' m m' A 224 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S224];
          intros x Hx; apply KA; lia|].
  split; [apply (w4a_spill_keep regs regs' m m' A 232 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S232];
          intros x Hx; apply KA; lia|].
  split; [|exact Hlen].
  apply (w4a_ba_keep m m' _ _ Hph). intros x Hx. apply KP. unfold ACtlCutP.flen. lia.
Qed.

Lemma w4a_fc_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.FC cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  (forall x, A + 232 <= x < A + 240 -> AGR m m' x) ->
  ACtlCutP.FC cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (S232 & H21 & H20) H9 HA0 HA1 E9 E20 E21 KA.
  split; [apply (w4a_spill_keep regs regs' m m' A 232 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S232];
          intros x Hx; apply KA; lia|].
  split; [exact (w4a_rgv_move _ _ _ _ H21 E21) | exact (w4a_rgv_move _ _ _ _ H20 E20)].
Qed.

Lemma w4a_in_move : forall cx m m', ACtlCutP.f1_IN cx m ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> AGR m m' x /\ AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.f1_IN cx m'.
Proof.
  intros cx m m' (Had & Hb) Hlen K. split.
  - apply (w4a_addr_keep m m' _ _ Had). intros i Hi. exact (proj2 (K (ACtlCut.c_p cx + i) ltac:(lia))).
  - apply (w4a_ba_keep m m' _ _ Hb). intros x Hx. exact (proj1 (K x ltac:(lia))).
Qed.

Lemma w4a_ba_nth : forall m a (bs : list byte) (k : nat) d, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (k < length bs)%nat -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) [nth k bs d].
Proof.
  intros m a bs k d (H0 & H1 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i. cbn [nth_error].
  rewrite Z.add_0_r. rewrite (H k Hk). apply nth_error_nth'. exact Hk.
Qed.

Lemma w4a_stk_keep : forall m m' lo hi, lib.Lib.Frame.stk segs m lo hi -> lib.Lib.Frame.wmono segs m m' ->
  (forall x, lo <= x < hi -> AGR m m' x) -> lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM K. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  exists b. rewrite <- Hb. exact (K a Ha).
Qed.

Lemma w4a_fli_stk : forall cx fr regs m, ACtlCutP.FLI cx fr regs m -> lib.Lib.Frame.stk segs m fr (fr + ACtlCutP.FRAME_BYTES).
Proof.
  intros cx fr regs m H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _).
  exact HS.
Qed.

Lemma w4a_sh_lt : forall x y, 0 <= x <= y -> 2 ^ 34 <= y -> 0 <= B.AsanRT.shadow_addr x < y.
Proof.
  intros x y Hx Hy. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.mul_div_le y 8 ltac:(lia)) as D2. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D3. lia.
Qed.

Lemma w4a_shr3 : forall x, 0 <= x -> Z.shiftr x 3 + B.AsanRT.ASAN_K = B.AsanRT.shadow_addr x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma w4a_wr_win : forall cx own ly3 S3 W3 mem3 md3 k a n, AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a -> a + n <= ACtlCut.c_sp cx -> 0 <= n ->
  lib.Lib.Mem.wr_at B.Img0.rsegs mem3 a n.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k a n HJ Ha Hn Hn0.
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (_ & Hceil & H47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hc.
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Hwin (a + i) ltac:(lia)) as (_ & b & Hb). unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
Qed.

Lemma w4a_not_out1 : forall lo hi a, ~ lib.Lib.Frame.outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_lt_le_dec a lo) as [H1|H1]; [exfalso; apply H; split; [lia | exact I]|].
  destruct (Z_lt_le_dec a hi) as [H2|H2]; [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

(* The bridge the call sites need: at a VISIBLE address the core's aview IS lib/Lib's mrd read (the shared text's
   aview_vis_mrd, proved here from the definitions: mrestrict keeps the byte, and seg_rom is the same fallback). *)
Lemma w4a_aview_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof using tfibsegs_rsegs.
  intros W mem a Hv. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict,
    lib.Lib.Mem.mrd. rewrite Hv. rewrite tfibsegs_rsegs. reflexivity.
Qed.

(* A byte list read at visible addresses, as the callee contracts want it (aview values). *)
Lemma w4a_ba_aview : forall (W : Reusable.YA0n.world segs) mem a (bs : list byte) (i : nat),
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem a bs -> (i < length bs)%nat ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem (a + Z.of_nat i) =
  Some (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof using tfibsegs_rsegs.
  intros W mem a bs i Hb Hi Hv. rewrite (w4a_aview_mrd W mem _ Hv).
  pose proof Hb as (_ & _ & H). unfold lib.Lib.Mem.wa in H. rewrite (H i Hi). rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). reflexivity.
Qed.

(* The reverse bridge: a byte the view has is a byte mrd has (used to rebuild bytes_at from a callee's post). *)
Lemma w4a_ba_of_aview : forall (W : Reusable.YA0n.world segs) mem a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> Reusable.YA0n.w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  (forall i, (i < length bs)%nat ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem (a + Z.of_nat i) =
     Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem a bs.
Proof using tfibsegs_rsegs.
  intros W mem a bs Ha0 Ha1 Hv Hval. split; [exact Ha0|]. split; [exact Ha1|].
  intros i Hi. pose proof (Hval i Hi) as E. rewrite (w4a_aview_mrd W mem _ (Hv i Hi)) in E.
  unfold lib.Lib.Mem.wa.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi).
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:Em; cbn [option_map] in E;
    [|discriminate].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A live heap block's bytes are ADDRESSABLE at the core's memory (AR's shadow law through YG0v's
   block_shadow_range, then the view / mrd bridge; ART.addressable's shadow_ok reads bv_signed, and a shadow
   value below 8 has bv_signed = bv_unsigned). *)
Lemma w4a_sbyte : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
  rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia. lia.
Qed.

Lemma w4a_blk_addr : forall ly S (W : Reusable.YA0n.world segs) mem md p n lo len,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> 0 <= len -> lo + len <= p + Reusable.YG00.req_size n ->
  B.AsanRT.addressable mem lo len.
Proof using LAWS tfibsegs_rsegs.
  intros ly S W mem md p n lo len HAR Hin Hlo Hlen Hhi.
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & Hceil & Hn0 & Hreq & Hvis & Hshvis).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  split; [lia|]. split; [exact Hlen|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
  intros i Hi.
  destruct (Reusable.YG0v.block_shadow_range (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem)
              Reusable.YG0f.SHADOW_OFF p (Reusable.YG00.req_size n) (lo + i) 1 Hbs ltac:(lia) ltac:(lia)
              (lo + i) ltac:(lia)) as (s & Hs & Hok).
  assert (Esh : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (lo + i) = B.AsanRT.shadow_addr (lo + i))
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Esh in Hs.
  assert (Hsvis : Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (lo + i))) = false)
    by (apply Hshvis; lia).
  rewrite (w4a_aview_mrd W mem _ Hsvis) in Hs.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (B.AsanRT.shadow_addr (lo + i)))) as [b|] eqn:Em;
    cbn [option_map] in Hs; [|discriminate].
  injection Hs as Hs.
  split.
  - pose proof (Reusable.YG0f.in_app_addr p (Reusable.YG00.req_size n) (lo + i) Happ ltac:(lia)) as Ha.
    unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Ha.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
  - exists b. split; [exact Em|].
    unfold B.AsanRT.shadow_ok. unfold Reusable.YG0v.saddr_ok in Hok.
    pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr.
    change (2 ^ Z.of_N 8) with 256 in Hbr.
    rewrite w4a_sbyte by lia. lia.
Qed.

(* rw_cells of five readable, writable bytes (a Theorem Labs lane's f2_st_noinv_F premise), from the journal's frame facts. *)
Lemma w4a_rw5 : forall m a, 0 <= a -> a + 5 <= 2 ^ 64 ->
  (forall i, 0 <= i < 5 -> (exists b, m (Z_to_bv 64 (a + i)) = Some b) /\
     wview B.Img0.rsegs m (Z_to_bv 64 (a + i)) <> None) ->
  exists junk, lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB 5 junk].
Proof.
  intros m a Ha0 Ha1 HK.
  destruct (HK 0 ltac:(lia)) as ((b0 & E0) & V0). destruct (HK 1 ltac:(lia)) as ((b1 & E1) & V1).
  destruct (HK 2 ltac:(lia)) as ((b2 & E2) & V2). destruct (HK 3 ltac:(lia)) as ((b3 & E3) & V3).
  destruct (HK 4 ltac:(lia)) as ((b4 & E4) & V4).
  exists [b0; b1; b2; b3; b4]. split.
  - split; [cbn; split; [reflexivity | exact I]|].
    cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app].
    split; [exact Ha0|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
    destruct i as [|[|[|[|[|i]]]]]; cbn [nth_error]; try lia;
      [ replace (a + Z.of_nat 0) with (a + 0) by lia; rewrite E0
      | replace (a + Z.of_nat 1) with (a + 1) by lia; rewrite E1
      | replace (a + Z.of_nat 2) with (a + 2) by lia; rewrite E2
      | replace (a + Z.of_nat 3) with (a + 3) by lia; rewrite E3
      | replace (a + Z.of_nat 4) with (a + 4) by lia; rewrite E4 ]; reflexivity.
  - split; [exact Ha0|]. split; [cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]; lia|].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add] in Hi.
    unfold lib.Lib.Mem.wa.
    destruct (Z.eq_dec i 0) as [->|?]; [exact V0|].
    destruct (Z.eq_dec i 1) as [->|?]; [exact V1|].
    destruct (Z.eq_dec i 2) as [->|?]; [exact V2|].
    destruct (Z.eq_dec i 3) as [->|?]; [exact V3|].
    destruct (Z.eq_dec i 4) as [->|?]; [exact V4 | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The allocator site 0x81f4c (S_F1): the core's rule at this site's constants, its continuation folded into the
   caller's; nothing else in the walk applies AMALLOC4 here.  Same shape as the sibling W2a's w2_malloc_81760.
   a0 = n = flen cx j (0 <= len <= 65535, F1.v:1597 / flen_small F13.v:111), ra = 0x81f50, frames own6, live list =
   the entry blocks, k <= 14 + 2j with j <= 255 (so k <= 524), trace [0x53754; 0x81f50] (P5-universe.v.txt:59-60). *)
Lemma ctl_W4a_malloc_81f4c : forall (cx : ctlcx) (j : nat) ly3 S3 W3 (regsT : bvmap 5 word) memT md3 k (o : Z) ch
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  ctl_base cx ->
  AJ cx (own6 cx) ly3 S3 W3 memT md3 k ->
  k <= 14 + 2 * Z.of_nat j -> (j <= 255)%nat ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx) ->
  lib.Reusable.YK11.getr regsT 10 = Z_to_bv 64 (flen cx j) -> 0 <= flen cx j <= 65535 ->
  Reusable.YG0d.spZ regsT = ACtlCut.c_sp cx + o -> o mod 16 = 0 -> -4096 < o <= -448 ->
  lib.Reusable.YK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 0x81f50 ->
  ACtlCut.ctl_chain ly3 W3 memT regsT ch ->
  ACtlCut.ctl_trace_in B (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B)) regsT ch ->
  (forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2 (res : Z),
     Reusable.YA0n.wle W3 W2 ->
     AJ cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) ->
     Reusable.YG0d.aregs_preserved regsT regs2 ->
     lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 res ->
     Reusable.YG01.frames S2 = own6 cx ->
     4096 <= res ->
     Permutation (Reusable.YG0d.ablocks B ly2 S2) (ENTRYBL cx ++ [(res, flen cx j)]) ->
     Reusable.YCbq.acall_kept segs B ly3 S3 W3 memT W2 mem2
       (ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (ACtlCut.c_sp cx + o)
       (fun a => res <= a < res + Reusable.YG00.req_size (flen cx j)) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x81f50 regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_malloc regsT memT md3) Q.
Proof using AMALLOC4 HMOK HPCM.
  (* The sibling W2a's w2_malloc_81760 (the donor's A/ACf2.v:116-141) at this site's constants. *)
  intros cx j ly3 S3 W3 regsT memT md3 k o ch Q HB HJ Hk Hj Hperm Ha0 Hn Hsp Ho16 Ho Hgp Htp Hra Hch Htr HK.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & Hlive0 & _) & _).   (* tfib_lib_pre_x, YCfn.v:32-45 *)
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).                      (* ajournal, YCbq.v:350-372 *)
  assert (Hj' : Z.of_nat j <= 255) by lia.
  assert (Hbb : Reusable.YCbq.bsum (Reusable.YG0d.ablocks B ly3 S3) = Reusable.YCbq.bsum (ENTRYBL cx))
    by exact (Reusable.YCbq.bsum_perm _ _ Hperm).
  rewrite <- (Reusable.YCbq.blocks_bytes_bsum B ly3 S3),
          <- (Reusable.YCbq.blocks_bytes_bsum B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) in Hbb.
  unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64. rewrite <- HPCM.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (AMALLOC4 W3 regsT memT Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
              (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
              (own6 cx) ly3 S3 md3 k (flen cx j) o (Z_to_bv 64 0x81f50) ch HJ).
    - exact Ha0.
    - unfold Reusable.YG00.MALLOC_MAX; lia.
    - (* blocks_bytes S3 = blocks_bytes (c_S cx) (Hbb) and blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX (the pre);
         flen <= 65535 <= LIVE_LIB = 2^33 *)
      unfold Reusable.YCfn.LIVE_LIB in Hlive0; lia.
    - exact Hsp.
    - exact Ho16.
    - lia.
    - unfold Reusable.YG0d.ASTACK, Reusable.YCfn.LLVMF_STK; lia.       (* 16384 + 4096 <= 32768 *)
    - exact Hgp.
    - exact Htp.
    - exact Hra.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - unfold Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *; lia.    (* st_nev S3 <= st_nev S + 524 *)
    - exact Hch.
    - exact Htr.
    - apply HMOK. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & H4096 & Eab2 & HK2 & _).
  apply (HK W2 ly2 S2 regs2 mem2 md2 res Hwle HJ2 HP2 Ha02).
  - rewrite Hfrs2, Hfrs, Hfr0, app_nil_r. reflexivity.
  - exact H4096.
  - rewrite Eab2. apply Permutation_app_tail. exact Hperm.
  - exact HK2.
Qed.

(* ---- local facts of S_F1, prefix w4a1_ ---- *)

(* The canonical register map, in THIS file's getr (F1's f1_mkR_of is stated in lib/B/Reusable's). *)
Lemma w4a1_mkR_of : forall regs : bvmap 5 word,
  Lib.Regs6ss.mkR_of regs =
  lib.Lib.Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
    (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
    (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
    (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
    (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* KNT's 112 bytes at KIND_NAME lie in B's image (a computation on the segment table), so they are of
   ctl_post_acall_kept's image class. *)
Lemma w4a1_kn_img : forall a, ACtlCutP.KNA.KIND_NAME <= a < ACtlCutP.KNA.KIND_NAME + 112 ->
  Reusable.YG0d.in_img segs a.
Proof using tfibsegs_rsegs.
  intros a Ha.
  assert (Hc : existsb (fun s : Segment =>
                  (Z.of_N (seg_base s) <=? ACtlCutP.KNA.KIND_NAME) &&
                  (ACtlCutP.KNA.KIND_NAME + 112 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
                  B.Img0.rsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hc. destruct Hc as (s & Hin & Hb).
  apply andb_true_iff in Hb. destruct Hb as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold Reusable.YG0d.in_img. exists s. rewrite tfibsegs_rsegs. split; [exact Hin | lia].
Qed.

(* w4a_fli_move / w4a_lk_move with KNT taken as a premise: across an allocator call KIND_NAME's SHADOW is not of
   a kept class (the image's shadow is allocator-owned), so KNT comes from the post-call AR instead. *)
Lemma w4a1_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.KNT m' ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS HKNT HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & _ & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split; [exact HKNT|].
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.
(* ---------------------------------------------------------------------------------------------------------
   B81ec4_at j (0x81ec4, own6, k <= 14+2j) --S_F1--> B81f50_at j.
   S_F1 (Seg/F1.v seg_F1 :1530): the length header of record j (one or two input bytes), len = min(L, left - h), the
   spills [A+232] = left - h and [A+240] = j, then malloc(len) @0x81f4c returning at 0x81f50.  The exit to B82eac
   (`j 0x82eac` at 0x81ec8) is dead: LI's 1 <= t_left j makes `bnez s9` at 0x81ec4 taken (F1.v:1528-1534). *)
Lemma seg_F1 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B81f50_at [Z.of_nat j]) ->
  ctl_from POST C_B82eac ->
  ctl_from POST (ix_cut C_B81ec4_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL AMALLOC4 HMOK HPCM CHAIN_OF_CUT
  ctl_kind_name_addressable ctl_kind_name_not_owned.
  intros POST j H50 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B81ec4_at in Hk, HBODY, HJ, Hfr, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfr, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (Hperm & HFRAC & Hn26 & HLI & HIN & H280 & H22).
  destruct HLI as (Hj & H13 & HOUR & (Hc0 & H23 & H25) & Hleft & HIFS & HFLI).
  destruct HIFS as (HIDj & HFGj & HFSj).
  assert (HREC : ACtlCutP.REC0 cx fr j mem3) by (split; [exact HIDj | exact HFGj]).
  pose proof HIN as (HINad & HINby).
  (* ---- the journal, the frame, the spill base, the entry pre ---- *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & Hshw & Hsaved & Qtr).
  pose proof (w4a_spZ regs3) as HspR. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HASv : Reusable.YG0d.ASTACK = 16384) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (HKv : B.AsanRT.ASAN_K = 2147450880) by reflexivity.
  destruct (w4a_frame _ _ _ _ _ _ _ _ HJ Hfr (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
    as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  pose proof HB as ((Hpre & _ & _ & _ & Hent & Hlen_in & _) & _).
  pose proof Hpre as (_ & _ & _ & Hgp & Htp & Hstk0 & _).
  pose proof Hstk0 as (Hsp0m16 & _).
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hsp0m16.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAbig : 140735332483072 <= A) by lia.
  assert (Hd2 : 0 <= fr / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : fr / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  assert (Efr8 : 8 * (fr / 8) = fr) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  (* ---- the model: left, h, len ---- *)
  assert (EL : ACtlCutP.SM.t_left (ACtlCut.c_in cx) j = ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)
    by (unfold ACtlCutP.SM.t_left, ACtlCutP.SM.f_left, ACtlCutP.SM.nlen; rewrite <- Hlen_in; reflexivity).
  rewrite EL in Hleft.
  assert (Eh : ACtlCutP.SM.t_h (ACtlCut.c_in cx) j =
               Z.min 2 (ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)) by (rewrite <- EL; reflexivity).
  assert (Elen : ACtlCutP.flen cx j =
    Z.min (bv_unsigned (ACtlCutP.RIM.nthb (ACtlCut.c_in cx) (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j))) +
           (if 2 <=? ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j
            then 256 * bv_unsigned (ACtlCutP.RIM.nthb (ACtlCut.c_in cx)
                                      (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1)))
            else 0))
          (ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j - ACtlCutP.SM.t_h (ACtlCut.c_in cx) j))
    by (rewrite <- EL; reflexivity).
  assert (Hb0r : 0 <= bv_unsigned (ACtlCutP.RIM.nthb (ACtlCut.c_in cx)
                    (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j))) < 256).
  { pose proof (bv_unsigned_in_range 8 (ACtlCutP.RIM.nthb (ACtlCut.c_in cx)
                  (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)))) as Hr.
    unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. lia. }
  assert (Hb1r : 0 <= bv_unsigned (ACtlCutP.RIM.nthb (ACtlCut.c_in cx)
                    (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1))) < 256).
  { pose proof (bv_unsigned_in_range 8 (ACtlCutP.RIM.nthb (ACtlCut.c_in cx)
                  (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1)))) as Hr.
    unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. lia. }
  assert (Hflen : 0 <= ACtlCutP.flen cx j <= 65535)
    by (rewrite Elen, Eh; destruct (2 <=? ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j); lia).
  (* ---- the input block ---- *)
  assert (HinE : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (ENTRYBL cx))
    by (destruct Hent as [(H0 & _)|(_ & Hin)]; [lia | exact Hin]).
  assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); exact HinE).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin3) as (Hp16 & Hp4096 & Hpceil & Hn0' & Hreq & Hpvis & Hpshvis).
  assert (Ereq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
    by (unfold Reusable.YG00.req_size; destruct (ACtlCut.c_n cx =? 0) eqn:E0;
        [apply Z.eqb_eq in E0; lia | reflexivity]).
  rewrite Ereq in Hpceil, Hpvis, Hpshvis.
  (* ---- the run's byte / shadow / window premises ---- *)
  assert (HWR : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (A + 232) 16)
    by (apply (w4a_wr_win _ _ _ _ _ _ _ _ _ _ HJ); lia).
  assert (HB0 : ov_read_bytes B.Img0.rsegs mem3
                  (lib.Lib.Mem.wa (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)) 1 =
                Some [ACtlCutP.RIM.nthb (ACtlCut.c_in cx) (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j))])
    by (apply (B.Prog.Seg.F1.f1_byte1 mem3 (ACtlCut.c_p cx) _ (ACtlCut.c_in cx) HINby);
        [lia | rewrite <- Hlen_in; lia]).
  destruct (B.Prog.Seg.F1.f1_shadow1 mem3 (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)
      (B.AsanRTFacts.addressable_sub mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
         (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) 1 HINad ltac:(lia) ltac:(lia) ltac:(lia))) as (k0 & HK0 & Hk0).
  assert (H2 : exists k1 : byte, 2 <= ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j ->
     ov_read_bytes B.Img0.rsegs mem3
       (lib.Lib.Mem.wa (Z.shiftr (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) 3 + B.AsanRT.ASAN_K)) 1
       = Some [k1] /\
     B.AsanRT.shadow_ok (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) (bv_signed k1) /\
     ov_read_bytes B.Img0.rsegs mem3
       (lib.Lib.Mem.wa (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1)) 1 =
       Some [ACtlCutP.RIM.nthb (ACtlCut.c_in cx) (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1))]).
  { destruct (Z_lt_le_dec (ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) 2) as [Hlt|Hge].
    - exists k0. intros Hc2. exfalso. lia.
    - pose proof (B.AsanRTFacts.addressable_sub mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
        (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) 1 HINad ltac:(lia) ltac:(lia) ltac:(lia)) as Had1.
      rewrite Z.add_assoc in Had1.
      destruct (B.Prog.Seg.F1.f1_shadow1 mem3 _ Had1) as (k1 & HK1 & Hk1).
      exists k1. intros _. split; [exact HK1|]. split; [exact Hk1|].
      rewrite <- Z.add_assoc.
      exact (B.Prog.Seg.F1.f1_byte1 mem3 (ACtlCut.c_p cx) (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1)
               (ACtlCut.c_in cx) HINby ltac:(lia) ltac:(rewrite <- Hlen_in; lia)). }
  destruct H2 as (k1 & H2).
  assert (Rq : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                 (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) 1)
    by (apply w4a_rng; [lia | lia | intros a Ha; apply Hpvis; lia]).
  assert (Rsh0 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
     (Z.shiftr (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) 3 + B.AsanRT.ASAN_K) 1).
  { rewrite w4a_shr3 by lia.
    pose proof (Hpshvis (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) ltac:(lia)) as Hv.
    pose proof (w4a_sh_lt (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) (2 ^ 47)
                  ltac:(lia) ltac:(lia)) as Hbd.
    apply w4a_rng; [lia | lia|].
    intros a Ha.
    replace a with (B.AsanRT.shadow_addr (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)) by lia.
    exact Hv. }
  assert (Rq1 : 2 <= ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
       (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) 1)
    by (intros H2l; apply w4a_rng; [lia | lia | intros a Ha; apply Hpvis; lia]).
  assert (Rsh1 : 2 <= ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
       (Z.shiftr (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) 3 + B.AsanRT.ASAN_K) 1).
  { intros H2l. rewrite w4a_shr3 by lia.
    pose proof (Hpshvis (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) ltac:(lia)) as Hv.
    pose proof (w4a_sh_lt (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1) (2 ^ 47)
                  ltac:(lia) ltac:(lia)) as Hbd.
    apply w4a_rng; [lia | lia|].
    intros a Ha.
    replace a with (B.AsanRT.shadow_addr (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1)) by lia.
    exact Hv. }
  assert (Rsp : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 232) 16)
    by (apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]).
  (* ---- 1. the run 0x81ec4 -> the allocator entry ---- *)
  change B.ACtlK.ASAN_K with B.AsanRT.ASAN_K in Hr26.
  eapply (w4_lift W3 0x81ec4 regs3 mem3 md3 _ (POST cx)).
  { rewrite w4a1_mkR_of.
    unfold ACtlCut.rgv in Hr9, H13, H22, H23, H25, Hr26.
    rewrite Hr9, H13, H22, H23, H25, Hr26.
    apply (B.Prog.Seg.F1F.f1_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (getr regs3 1) (getr regs3 2) (getr regs3 3) (getr regs3 4) (getr regs3 5) (getr regs3 6) (getr regs3 7)
      (getr regs3 8) (getr regs3 10) (getr regs3 11) (getr regs3 12) (getr regs3 14) (getr regs3 15)
      (getr regs3 16) (getr regs3 17) (getr regs3 18) (getr regs3 19) (getr regs3 20) (getr regs3 21)
      (getr regs3 24) (getr regs3 27) (getr regs3 28) (getr regs3 29) (getr regs3 30) (getr regs3 31)
      lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
      A (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)
      (ACtlCut.c_n cx - ACtlCutP.SM.t_c (ACtlCut.c_in cx) j) (Z.of_nat j)
      (ACtlCutP.SM.t_h (ACtlCut.c_in cx) j) (ACtlCutP.flen cx j)
      (ACtlCutP.RIM.nthb (ACtlCut.c_in cx) (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j)))
      (ACtlCutP.RIM.nthb (ACtlCut.c_in cx) (Z.to_nat (ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + 1))) k0 k1);
      [ lia | lia | lia | lia | lia | lia
      | exact HB0 | exact HK0 | exact Hk0
      | intros Hl2; exact (proj2 (proj2 (H2 Hl2)))
      | intros Hl2; exact (proj1 (H2 Hl2))
      | intros Hl2; exact (proj1 (proj2 (H2 Hl2)))
      | exact HWR | exact Eh | exact Elen
      | exact Rq | exact Rsh0 | exact Rq1 | exact Rsh1 | exact Rsp ]. }
  intros ms' md' (a1' & a2' & m' & -> & MU & WM & HB232 & HB240) Hhid Hsame.
  match goal with
  | |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (RT := R)
  end.
  assert (HspT : Reusable.YG0d.spZ RT = sp) by exact Hspz.
  assert (AG1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 232 <= x < A + 248) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx Hn. apply (w4a_mrd_munch _ _ _ x MU Hx).
    cbn [lib.Lib.Frame.outside]. split; [exact Hn | exact I]. }
  assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU WM Hhid Hsame).
    intros a Ha. apply w4a_not_out1 in Ha.
    split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia. }
  assert (Hsv : lib.Lib.Mem.bytes_at segs m' (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
  { apply (w4a_ba_keep mem3 m' _ _ Hsaved). rewrite w4a_saved_len.
    intros x Hx. exact (AG1 x ltac:(lia) ltac:(lia)). }
  destruct (CHAIN_OF_CUT cx (own6 cx) ly3 S3 W3 m' md' k RT
              (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B)) 0x81f50
              HB HJ' ltac:(exact Hr8) ltac:(reflexivity) Hsv ltac:(lia) ltac:(lia)
              ltac:(exact (in_cons _ _ _ (in_cons _ _ _ (in_eq _ _))))) as (ch & Hch & Htr).
  (* ---- 2. the allocator site ---- *)
  apply (ctl_W4a_malloc_81f4c cx j ly3 S3 W3 RT m' md' k (sp - ACtlCut.c_sp cx) ch (POST cx)
           HB HJ' Hk Hj Hperm ltac:(reflexivity) Hflen ltac:(rewrite HspT; lia)
           ltac:(rewrite Zminus_mod, Hsp16, Hsp0m16; reflexivity) ltac:(lia)
           ltac:(transitivity (getr (ACtlCut.c_regs cx) 3); [exact Hr3 | exact Hgp])
           ltac:(exact Hr4) ltac:(reflexivity) Hch Htr).
  clear Hch Htr.
  intros W2 ly2 S2 regs2 mem2 md2 res Hwle HJ2 HP2 Ha02 Hfrs2 Hres4096 Hperm2 HKEPT.
  (* ---- 3. the post-call facts ---- *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & Hwin2).
  destruct (w4a_frame cx (k + 1) ly2 S2 W2 mem2 md2 fr HJ2 Hfrs2
              (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl))) as (_ & _ & _ & Hfrb2 & _).
  assert (HinRes2 : In (res, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm2)); apply in_or_app; right; left; reflexivity).
  assert (Hinp2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm2)); apply in_or_app; left; exact HinE).
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof HJ2 as (_ & Hly2 & _).
  assert (Efa2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
    unfold Reusable.YG0f.frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res (ACtlCutP.flen cx j) 6
                (ACtlCut.c_fpos cx) HAR2 HinRes2 Hin62) as Hdj.
  unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Efa2 in Hdj.
  assert (E6b : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite E6b in Hdj.
  assert (Hperm3 : exists l, Permutation (Reusable.YG0d.ablocks B ly2 S2)
     ((ACtlCut.c_p cx, ACtlCut.c_n cx) :: (res, ACtlCutP.flen cx j) :: l)).
  { destruct (in_split _ _ HinE) as (l1 & l2 & E1).
    exists (l1 ++ l2).
    eapply Permutation_trans; [exact Hperm2|].
    rewrite E1, <- app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
    apply perm_skip. rewrite app_assoc. apply Permutation_sym, Permutation_cons_append. }
  destruct Hperm3 as (lrest & Hperm3).
  pose proof (Reusable.YCbq.sep_blocks_perm segs B LAWS ly2 S2 W2 mem2 md2
                (ACtlCut.c_p cx, ACtlCut.c_n cx) (res, ACtlCutP.flen cx j) lrest HAR2 Hperm3) as Hdb.
  unfold Reusable.YCbq.block_rng, Reusable.YG0f.zdisjoint in Hdb. cbn [fst snd] in Hdb.
  rewrite Ereq in Hdb.
  assert (Hshfr : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 ->
     ~ (res <= x < res + Reusable.YG00.req_size (ACtlCutP.flen cx j))).
  { intros x Hx Hres.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (ACtlCutP.flen cx j) HAR2 HinRes2)
      as (_ & _ & _ & Happ2 & _).
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happ2.
    unfold B.AsanRT.shadow_addr in Hx. destruct Happ2 as (Hq1 & [Hq2 | (Hq3 & Hq4)]); lia. }
  (* the four kept classes of the allocator call *)
  assert (KC1 : forall x, lib.Reusable.YM05.alloc_ceiling <= x < 2 ^ 64 ->
     ~ (sp - Reusable.YG0d.ASTACK <= x < sp) -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x)).
  { intros x Hx Hnw Hv.
    apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m' mem2 _ _ _ HKEPT Hwle (Z_to_bv 64 x) Hv).
    rewrite w4a_wa_u by lia. left. split; [lia|]. intros (Hw1 & Hw2). apply Hnw. lia. }
  assert (KC2 : forall b n x, In (b, n) (Reusable.YG0d.ablocks B ly3 S3) ->
     b <= x < b + Reusable.YG00.req_size n ->
     ~ (res <= x < res + Reusable.YG00.req_size (ACtlCutP.flen cx j)) ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x)).
  { intros b n x Hin Hx Hoff Hv.
    destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
    apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m' mem2 _ _ _ HKEPT Hwle (Z_to_bv 64 x) Hv).
    rewrite w4a_wa_u by lia. right. left. exists b, n, (x - b).
    split; [exact Hin|]. split; [lia|]. split; [lia|].
    replace (b + (x - b)) with x by lia. exact Hoff. }
  assert (KC3 : forall x, Reusable.YG0d.in_img segs x ->
     ~ Exists (Reusable.YG0n.in_zr x) (Reusable.YG0f.as_owned_static B) ->
     ~ (Reusable.YG0f.as_errno B <= x < Reusable.YG0f.as_errno B + 4) ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x)).
  { intros x Himg Hno Hne Hv.
    pose proof (segs_low x Himg) as Hlow. unfold Reusable.YG0f.kLowMemEnd in Hlow.
    apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m' mem2 _ _ _ HKEPT Hwle (Z_to_bv 64 x) Hv).
    rewrite w4a_wa_u by lia. right. right. left. split; [exact Himg|]. split; [exact Hno | exact Hne]. }
  assert (KC4 : forall x, Reusable.YCbq.in_frames ly3 (own6 cx) x -> 0 <= x < 2 ^ 64 ->
     ~ (res <= x < res + Reusable.YG00.req_size (ACtlCutP.flen cx j)) ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x)).
  { intros x Hinf Hx Hoff Hv.
    apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m' mem2 _ _ _ HKEPT Hwle (Z_to_bv 64 x) Hv).
    rewrite w4a_wa_u by lia. right. right. right.
    destruct Hinf as (cid & pos & Hin & Hzr). exists cid, pos.
    split; [rewrite Hfr; exact Hin|]. split; [exact Hzr | exact Hoff]. }
  (* the agreement facts the cut predicates need (mem3 -> mem2) *)
  assert (KS : forall x, A <= x < A + 448 -> ~ (A + 232 <= x < A + 248) -> AGR mem3 mem2 x).
  { intros x Hx Hn.
    rewrite (KC1 x ltac:(lia) ltac:(lia) ltac:(exact (proj1 (Hwin x ltac:(lia))))).
    exact (AG1 x ltac:(lia) Hn). }
  assert (KSV : forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> AGR mem3 mem2 x).
  { intros x Hx.
    rewrite (KC1 x ltac:(lia) ltac:(lia) ltac:(exact (proj1 (Hwin x ltac:(lia))))).
    exact (AG1 x ltac:(lia) ltac:(lia)). }
  assert (KFR : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 x).
  { intros x Hx. destruct (Hfrb x Hx) as (Hv & _ & Hinf).
    rewrite (KC4 x Hinf ltac:(lia) ltac:(lia) Hv). exact (AG1 x ltac:(lia) ltac:(lia)). }
  assert (KSH : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 -> AGR mem3 mem2 x).
  { intros x Hx. destruct (Hfrsh x Hx) as (Hv & _ & Hinf).
    rewrite (KC4 x Hinf ltac:(unfold B.AsanRT.shadow_addr in Hx; lia) ltac:(exact (Hshfr x Hx)) Hv).
    exact (AG1 x ltac:(unfold B.AsanRT.shadow_addr in Hx; lia)
                  ltac:(unfold B.AsanRT.shadow_addr in Hx; lia)). }
  assert (KFRS : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 (B.AsanRT.shadow_addr x)).
  { intros x Hx. apply KSH. unfold B.AsanRT.shadow_addr.
    assert (D1 : fr / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : x / 8 < fr / 8 + 512) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (Hinp_off : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
     ~ (res <= x < res + Reusable.YG00.req_size (ACtlCutP.flen cx j))) by (intros x Hx; lia).
  assert (KIN : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> AGR mem3 mem2 x).
  { intros x Hx.
    rewrite (KC2 (ACtlCut.c_p cx) (ACtlCut.c_n cx) x Hin3 ltac:(rewrite Ereq; lia)
               ltac:(exact (Hinp_off x Hx)) ltac:(apply Hpvis; lia)).
    exact (AG1 x ltac:(lia) ltac:(lia)). }
  assert (KKN : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
  { intros x Hx.
    assert (Hxv : 652672 <= x < 652784) by (change ACtlCutP.KNA.KIND_NAME with 652672 in Hx; lia).
    destruct (ctl_kind_name_not_owned x Hx) as (Hno & Hne).
    assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
      by (destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hvis);
          unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Hvis; apply Hvis; lia).
    rewrite (KC3 x (w4a1_kn_img x Hx) Hno Hne Hv). exact (AG1 x ltac:(lia) ltac:(lia)). }
  (* the registers kept by the call *)
  assert (E2' : getr regs2 2 = getr regs3 2)
    by exact (HP2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3' : getr regs2 3 = getr regs3 3)
    by exact (HP2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4' : getr regs2 4 = getr regs3 4)
    by exact (HP2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8' : getr regs2 8 = getr regs3 8)
    by exact (HP2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9' : getr regs2 9 = getr regs3 9).
  { transitivity (getr RT 9); [exact (HP2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    unfold ACtlCut.rgv in Hr9. rewrite Hr9. reflexivity. }
  assert (E19' : getr regs2 19 = getr regs3 19)
    by exact (HP2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26' : getr regs2 26 = getr regs3 26).
  { transitivity (getr RT 26); [exact (HP2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    unfold ACtlCut.rgv in Hr26. rewrite Hr26. reflexivity. }
  assert (E27' : getr regs2 27 = getr regs3 27)
    by exact (HP2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  (* KNT after the call: the bytes are kept image, the shadow comes from the post-call AR *)
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & (HKNb & _) & _ & _).
  assert (HKNT2 : ACtlCutP.KNT mem2).
  { split.
    - apply (w4a_ba_keep mem3 mem2 _ _ HKNb).
      pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
      intros x Hx. apply KKN. lia.
    - exact (ctl_kind_name_addressable ly2 S2 W2 mem2 md2 HAR2). }
  assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfrb2 a ltac:(lia)) as (_ & (b & Hbb) & _).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hbb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  (* ---- 4. the cut at 0x81f50 ---- *)
  apply (H50 cx [Z.of_nat j] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2 HFA);
    [ unfold ix_cut, ACtlCutP.C_B81f50_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; lia
    | | exact (w4a_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) HB HJ2) ].
  unfold ix_cut, ACtlCutP.C_B81f50_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
  exists res.
  split; [exact Hperm2|].
  split.
  { apply (w4a_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC E2' E3' E4' E8' E9' E19' E26').
    intros A0 x HA0 HA0r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA0 Hr9 HA0r ltac:(lia)) in Hx.
    destruct Hx as [H1|[H1|[H1|[H1|[H1|H1]]]]].
    - apply KS; lia.
    - apply KS; lia.
    - apply KFR; lia.
    - apply KSH; unfold ACtlCutP.Sfr in H1; lia.
    - apply KSV; lia.
    - apply KFR; lia. }
  split; [exact Hn26|]. split; [exact Hj|]. split; [exact Ha02|].
  split.
  { split; [lia|].
    apply (w4a_blk_addr ly2 S2 W2 mem2 md2 res (ACtlCutP.flen cx j) res
             (B.ACtlK.a_size (ACtlCutP.flen cx j)) HAR2 HinRes2 ltac:(lia)
             ltac:(unfold B.ACtlK.a_size; lia)
             ltac:(unfold B.ACtlK.a_size, Reusable.YG00.req_size;
                   destruct (ACtlCutP.flen cx j =? 0) eqn:E0;
                   [apply Z.eqb_eq in E0 | apply Z.eqb_neq in E0]; lia)). }
  split.
  { split; [exact Hj|].
    split.
    { exists A. split; [unfold ACtlCut.rgv; rewrite E9'; exact Hr9|].
      unfold ACtlCutP.q64.
      apply (w4a_ba_keep m' mem2 _ _ HB240). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KC1; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))]. }
    split.
    { apply (w4a_our_move cx fr mem3 mem2 HOUR). intros x Hx. apply KFR; lia. }
    apply (w4a1_fli_move cx fr regs3 regs2 mem3 mem2 A HFLI Hr9 ltac:(lia) ltac:(lia) E9' E27').
    - intros off x Hoff Hx. cbn [In] in Hoff. apply KS; lia.
    - intros x Hx. apply KFRS. unfold ACtlCutP.fragb in Hx. lia.
    - exact HKNT2.
    - exact HSTK2. }
  split.
  { split.
    { exists A. split.
      - unfold ACtlCut.rgv. rewrite E9'. exact Hr9.
      - unfold ACtlCutP.q64. rewrite EL.
        apply (w4a_ba_keep m' mem2 _ _ HB232). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply KC1; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))]. }
    split.
    - unfold ACtlCut.rgv.
      transitivity (getr RT 21); [exact (HP2 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j)
         with (ACtlCut.c_p cx + ACtlCutP.SM.t_c (ACtlCut.c_in cx) j + ACtlCutP.SM.t_h (ACtlCut.c_in cx) j)
         by (unfold ACtlCutP.SM.t_body, ACtlCutP.SM.f_body, ACtlCutP.SM.t_c, ACtlCutP.SM.t_h,
                    ACtlCutP.SM.f_h; lia).
      reflexivity.
    - unfold ACtlCut.rgv.
      transitivity (getr RT 20); [exact (HP2 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      reflexivity. }
  split.
  { split.
    - apply (w4a_blk_addr ly2 S2 W2 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_p cx)
               (ACtlCut.c_n cx) HAR2 Hinp2 ltac:(lia) ltac:(lia) ltac:(rewrite Ereq; lia)).
    - apply (w4a_ba_keep mem3 mem2 _ _ HINby). rewrite <- Hlen_in. intros x Hx. apply KIN; lia. }
  split.
  { apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj);
      intros x Hx; [apply KFR; lia | apply KFRS; lia]. }
  split.
  { apply (w4a_rec0_move cx fr j mem3 mem2 HREC). intros x Hx. apply KFR; lia. }
  unfold ACtlCut.rgv.
  transitivity (getr RT 22); [exact (HP2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  reflexivity.
Qed.

(* ---- local lemmas of seg_F2, prefix w4a2_ ---- *)
Lemma w4a2_perm2 : forall {X : Type} (l1 l2 : list X) x y, Permutation ((l1 ++ x :: l2) ++ [y]) (x :: y :: l1 ++ l2).
Proof.
  intros X l1 l2 x y. rewrite <- app_assoc. cbn [app]. symmetry. apply Permutation_cons_app.
  rewrite app_assoc. apply Permutation_cons_append.
Qed.

Lemma w4a2_out_app : forall W1 W2 x, lib.Lib.Frame.outside (W1 ++ W2) x ->
  lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app lib.Lib.Frame.outside] in *; [split; [exact I | exact H]|].
  destruct H as (H1 & H2). destruct (IH W2 x H2) as (H3 & H4). split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma w4a2_munch_tr : forall W1 W2 m m1 m2, lib.Lib.Frame.munch W1 m m1 -> lib.Lib.Frame.munch W2 m1 m2 ->
  lib.Lib.Frame.munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 M1 M2 x Hx. destruct (w4a2_out_app W1 W2 _ Hx) as (H1 & H2).
  rewrite (M2 x H2). exact (M1 x H1).
Qed.

Lemma w4a2_sbyte_inv : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  revert Hb. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
  intros Hb. Z.div_mod_to_equations. lia.
Qed.

(* An address of the shadow band [ASAN_K, kHighMemBeg) is not an application byte. *)
Lemma w4a2_shr_out : forall a lo len, B.AsanRT.ASAN_K <= a < Reusable.YG0f.kHighMemBeg ->
  Reusable.YG0f.in_app lo len -> ~ (lo <= a < lo + len).
Proof.
  intros a lo len Ha (H0 & H1). unfold B.AsanRT.ASAN_K, Reusable.YG0f.kHighMemBeg in Ha.
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H1. lia.
Qed.

Lemma w4a2_sh_in : forall fr x, fr mod 8 = 0 -> fr <= x < fr + 4096 ->
  B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr x < B.AsanRT.shadow_addr fr + 512.
Proof.
  intros fr x H8 Hx. unfold B.AsanRT.shadow_addr.
  assert (D1 : fr / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : x / 8 < fr / 8 + 512).
  { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod fr 8 ltac:(lia)). lia. }
  lia.
Qed.

(* KIND_NAME's 112 bytes lie in image B's third segment [0x9f000, 0xa2000). *)
Lemma w4a2_kn_img : forall a, ACtlCutP.KNA.KIND_NAME <= a < ACtlCutP.KNA.KIND_NAME + 112 ->
  Reusable.YG0d.in_img segs a.
Proof using tfibsegs_rsegs.
  intros a Ha. change ACtlCutP.KNA.KIND_NAME with 652672 in Ha.
  pose proof B.ProgBridge.rsegs_spans as E.
  assert (Hin : In (0x9f000, 0x3000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by (rewrite E; right; right; left; reflexivity).
  apply in_map_iff in Hin as (sg & Esg & Hsg). injection Esg as E1 E2.
  unfold Reusable.YG0d.in_img. rewrite tfibsegs_rsegs. exists sg. split; [exact Hsg | lia].
Qed.

(* The owned class-6 frame: its address in the journal's layout and its place in application memory. *)
Lemma w4a2_frame_app : forall cx k ly3 S3 W3 mem3 md3 fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr /\ Reusable.YG0f.in_app fr 4096.
Proof using LAWS.
  intros cx k ly3 S3 W3 mem3 md3 fr HJ Hfrs Hfr.
  pose proof HJ as (HAR & Hly & _).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Hfr. unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF.
    reflexivity. }
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Happ & _).
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efa, E6 in Happ. split; [exact Efa | exact Happ].
Qed.

(* The frame's bytes are present at any journal state that owns it (lib/Lib's stk form). *)
Lemma w4a2_frame_stk : forall cx k ly3 S3 W3 mem3 md3 fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  lib.Lib.Frame.stk segs mem3 fr (fr + ACtlCutP.FRAME_BYTES).
Proof using LAWS.
  intros cx k ly3 S3 W3 mem3 md3 fr HJ Hfrs Hfr.
  destruct (w4a_frame _ _ _ _ _ _ _ _ HJ Hfrs Hfr) as (_ & H4096 & Hceil & Hb & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Hb a ltac:(lia)) as (_ & (b & Hm) & _).
  split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Hm. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hm. reflexivity.
Qed.

(* ART.addressable at visible shadow bytes is the core's range_addressable over the view. *)
Lemma w4a2_ra_of_addr : forall (W : Reusable.YA0n.world segs) m p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof using tfibsegs_rsegs.
  intros W m p n (H0 & H1 & H2 & H) Hv x Hx.
  destruct (H (x - p) ltac:(lia)) as (_ & b & Hb & Hok). replace (p + (x - p)) with x in Hb, Hok by lia.
  assert (Esh : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Esh. pose proof (Hv (x - p) ltac:(lia)) as Hvx. replace (p + (x - p)) with x in Hvx by lia.
  rewrite (w4a_aview_mrd W m _ Hvx). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. cbn [option_map].
  exists (bv_unsigned b). split; [reflexivity|].
  unfold B.AsanRT.shadow_ok in Hok. unfold Reusable.YG0v.saddr_ok.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
  assert (Hs : 0 <= bv_signed b) by lia. rewrite (w4a2_sbyte_inv b Hs). lia.
Qed.

(* The five record-shadow bytes S(fr) + 22 .. 26 = 0, 0, 0, 0, 4 make [fr + 176, fr + 212) addressable. *)
Lemma w4a2_rec_addr : forall m fr (b0 b1 b2 b3 b4 : byte),
  fr mod 8 = 0 -> 0 <= fr -> fr + 212 <= B.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < 36 -> B.AsanRT.app_mem (fr + 176 + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4] ->
  bv_signed b0 = 0 -> bv_signed b1 = 0 -> bv_signed b2 = 0 -> bv_signed b3 = 0 -> bv_signed b4 = 4 ->
  B.AsanRT.addressable m (fr + 176) 36.
Proof.
  intros m fr b0 b1 b2 b3 b4 H8 Hfr0 Hfr1 Happ (_ & _ & Hb) E0 E1 E2 E3 E4.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  assert (Hq : forall q : nat, 8 * Z.of_nat q <= i < 8 * Z.of_nat q + 8 ->
     B.AsanRT.shadow_addr (fr + 176 + i) = ACtlCutP.Sfr fr + 22 + Z.of_nat q /\
     (fr + 176 + i) mod 8 = i - 8 * Z.of_nat q).
  { intros q Hqi. pose proof (Z.div_mod fr 8 ltac:(lia)) as Dfr. rewrite H8, Z.add_0_r in Dfr.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. split.
    - rewrite <- (Z.div_unique (fr + 176 + i) 8 (fr / 8 + 22 + Z.of_nat q) (i - 8 * Z.of_nat q)) by lia. lia.
    - rewrite <- (Z.mod_unique (fr + 176 + i) 8 (fr / 8 + 22 + Z.of_nat q) (i - 8 * Z.of_nat q)) by lia. reflexivity. }
  unfold B.AsanRT.shadow_ok.
  destruct (Z_lt_le_dec i 8) as [h0|h0].
  { destruct (Hq 0%nat ltac:(cbn; lia)) as (-> & _). exists b0. split; [exact (Hb 0%nat ltac:(cbn; lia)) | left; exact E0]. }
  destruct (Z_lt_le_dec i 16) as [h1|h1].
  { destruct (Hq 1%nat ltac:(cbn; lia)) as (-> & _). exists b1. split; [exact (Hb 1%nat ltac:(cbn; lia)) | left; exact E1]. }
  destruct (Z_lt_le_dec i 24) as [h2|h2].
  { destruct (Hq 2%nat ltac:(cbn; lia)) as (-> & _). exists b2. split; [exact (Hb 2%nat ltac:(cbn; lia)) | left; exact E2]. }
  destruct (Z_lt_le_dec i 32) as [h3|h3].
  { destruct (Hq 3%nat ltac:(cbn; lia)) as (-> & _). exists b3. split; [exact (Hb 3%nat ltac:(cbn; lia)) | left; exact E3]. }
  destruct (Hq 4%nat ltac:(cbn; lia)) as (-> & Hmod). exists b4. split; [exact (Hb 4%nat ltac:(cbn; lia))|].
  right. rewrite E4, Hmod. cbn. lia.
Qed.

(* w4a_fli_move / w4a_lk_move across a CALL: KIND_NAME's shadow is the allocator's (hidden), so KNT's addressable
   half comes from the post-call AR (ctl_kind_name_addressable), its bytes from the kept image. *)
Lemma w4a2_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS KI HKA HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & HKNa) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split.
  { split; [|exact HKA].
    apply (w4a_ba_keep m m' _ _ HKNb). pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
    intros x Hx. apply KI. lia. }
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.

Lemma w4a2_lk_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off (240 :: [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304]) -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS KI HKA HSTK.
  split; [exact Hj|].
  split; [apply (w4a_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply (KA 240 x); [left; reflexivity | exact Hx]|].
  split; [exact (w4a_our_move cx fr m m' HOUR KF)|].
  apply (w4a2_fli_move cx fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27); [|exact KS | exact KI | exact HKA | exact HSTK].
  intros off x Hoff Hx. apply (KA off x); [right; exact Hoff | exact Hx].
Qed.

(* The shadow byte of a frame address, as an offset from the frame's shadow base. *)
Lemma w4a2_sh_off : forall fr x, fr mod 8 = 0 -> fr <= x ->
  B.AsanRT.shadow_addr x = ACtlCutP.Sfr fr + (x - fr) / 8.
Proof.
  intros fr x H8 Hx. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Dfr. rewrite H8, Z.add_0_r in Dfr.
  replace x with ((x - fr) + (fr / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia.
Qed.

(* The owned frame's shadow bytes are present at any journal state that owns the frame: FRAC's shadow conjunct
   rebuilt (the record-shadow stores change five of its bytes). *)
Lemma w4a2_frame_sh : forall cx k ly3 S3 W3 mem3 md3 fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW.
Proof using LAWS.
  intros cx k ly3 S3 W3 mem3 md3 fr HJ Hfrs Hfr.
  destruct (w4a_frame _ _ _ _ _ _ _ _ HJ Hfrs Hfr) as (H32 & H4096 & Hceil & _ & Hsh).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  pose proof (w4a_sh_lt fr (2 ^ 47) ltac:(lia) ltac:(lia)) as Hb.
  assert (Hst : lib.Lib.Frame.stk B.Img0.rsegs mem3 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW)).
  { unfold ACtlCutP.Sfr. rewrite HFSv.
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hsh a ltac:(lia)) as (_ & (b & Hm) & _).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hm; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hm. reflexivity. }
  destruct (lib.Lib.Frame.stk_bytes B.Img0.rsegs mem3 _ _ Hst ltac:(rewrite HFSv; lia)) as (bs & Hl & Hbs).
  exists bs. split; [exact Hbs|]. rewrite Hl. f_equal. lia.
Qed.

(* w4a_frac_move with FRAC's frame-shadow conjunct supplied afresh instead of kept. *)
Lemma w4a2_frac_move : forall cx fr sel regs regs' m m',
  ACtlCutP.FRAC B cx fr sel regs m ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  (forall A x, ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
     A + 40 <= x < A + 56 \/ A + 336 <= x < A + 344 \/ fr <= x < fr + 24 \/
     ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx \/ fr + 4088 <= x < fr + 4096 ->
     AGR m m' x) ->
  (exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' HF E2 E3 E4 E8 E9 E19 E26 K Hsh'.
  destruct HF as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & _ & Hsaved & Qtr).
  pose proof (w4a_spZ regs) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  unfold ACtlCut.c_sp in *.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  exists A, sp.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact Hr4|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr8 E8)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|].
  split; [rewrite E3; exact Hr3|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr19 E19)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr26 E26)|].
  do 8 (split; [assumption|]).
  unfold ACtlCutP.q64 in *.
  split; [apply (w4a_ba_keep m m' _ _ Q336); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q48); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q40); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh1); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh2); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [exact Hsh'|].
  split; [apply (w4a_ba_keep m m' _ _ Hsaved); rewrite w4a_saved_len; intros x Hx; apply (K A x Hr9 HA); lia|].
  apply (w4a_ba_keep m m' _ _ Qtr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply (K A x Hr9 HA). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81f50_at j (0x81f50, own6, k <= 14+2j+1) --S_F2--> B81f78_at j | B82048_at j.
   S_F2 (Seg/F2.v seg_F2 :2580): s2 = Phi; len > 0: Phi <> 0 (the abort edge 0x81f5c not taken), [A + 224] = p + body,
   __asan_memcpy(Phi, p + body, len) @0x81f74 returning at 0x81f78; len = 0: [A + 224] := p + body, the five
   record-shadow stores S(fr) + 22 .. 26 (0x82020-0x82034) and reac_ctrl_parse(Phi, 0, fr + 176) @0x82044 returning at
   0x82048. *)
Lemma seg_F2 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B81f78_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B81f50_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx LAWS segs_low AMEMCPY PARSE
  TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable ctl_kind_name_not_owned.
  intros POST j H78 H48 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B81f50_at in Hk, HBODY, HJ, Hfr, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfr, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hn26 & Hj & Ha0 & HHB & HLK & HFC & HIN & HFSj & HREC & H22).
  (* the journal's facts, the frame, the spill base, the turn block *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & _).
  pose proof (w4a_spZ regs3) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (HESv : Reusable.YG0d.ESTACK = 4096) by reflexivity.
  assert (HA34 : 2 ^ 34 <= A) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0_16 & _) & _).
  assert (Hin : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hn0 & Hreq & Hpvis & Hpshvis).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & Hpapp & _).
  assert (HFA6 : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by exact (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
  pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ Hfr HFA6) as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  destruct (w4a2_frame_app _ _ _ _ _ _ _ _ HJ Hfr HFA6) as (Efa & Hfrapp).
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _ & _ & _ & Hpn & Hnlen & _) & _).
  pose proof HFC as (S232 & H21 & H20).
  assert (G9 : Sem.reg_get regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (G10 : Sem.reg_get regs3 10 = Z_to_bv 64 phi) by exact Ha0.
  assert (G19 : Sem.reg_get regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact Hr19.
  assert (G20 : Sem.reg_get regs3 20 = Z_to_bv 64 (flen cx j)) by exact H20.
  assert (G21 : Sem.reg_get regs3 21 = Z_to_bv 64 (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j))
    by exact H21.
  assert (HW224 : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (A + 224) 8)
    by (apply (w4a_wr_win _ _ _ _ _ _ _ _ _ _ HJ); lia).
  assert (R224 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 224) 8).
  { apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]. }
  assert (Hsfr : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 4096 <= A).
  { unfold ACtlCutP.Sfr. pose proof (w4a_sh_lt fr (A - 4096) ltac:(lia) ltac:(lia)). lia. }
  assert (Hsfr2 : B.AsanRT.ASAN_K <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 8192 <= sp /\
                  ACtlCutP.Sfr fr + 512 <= Reusable.YG0f.kHighMemBeg).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.kHighMemBeg.
    pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)) as D1.
    assert (D2 : fr / 8 + 512 <= 2 ^ 44) by (clear - Hfrceil Hcv Hfr4096; Z.div_mod_to_equations; lia).
    lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Esfr : ACtlCutP.Sfr fr = B.AsanRT.shadow_addr fr) by reflexivity.
  assert (Eflen : flen cx j = ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) by reflexivity.
  assert (HIL : Reusable.YImgTop.IMG_LO = 65536) by (vm_compute; reflexivity).
  assert (HIT : Reusable.YImgTop.IMG_TOP = 6283264) by (vm_compute; reflexivity).
  destruct (Z.eq_dec (flen cx j) 0) as [E0|Hnz].
  { (* ---- len = 0: f2_head0_F, the five record-shadow stores (F2F.f2_st_noinv_F), f2_pcall_pre_F,
       reac_ctrl_parse (PARSE) at o = fr + 176, a1 = 0, then B82048_at ---- *)
    assert (Et0 : ACtlCutP.SM.t_len (ACtlCut.c_in cx) j = 0) by (rewrite <- Eflen; exact E0).
    set (S1 := bv_unsigned (Z_to_bv 64 (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j))).
    assert (HS1 : 0 <= S1 < 2 ^ 64).
    { pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j))) as H.
      unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. exact H. }
    assert (ES1 : Z_to_bv 64 S1 = Z_to_bv 64 (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j))
      by (unfold S1; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
    assert (G21' : Sem.reg_get regs3 21 = Z_to_bv 64 S1) by (rewrite ES1; exact G21).
    assert (G20' : Sem.reg_get regs3 20 = Z_to_bv 64 0) by (rewrite G20, E0; reflexivity).
    assert (G19u : bv_unsigned (Z_to_bv 64 (ACtlCutP.Sfr fr)) = ACtlCutP.Sfr fr) by (apply w4a_wa_u; lia).
    assert (HKv : B.AsanRT.ASAN_K = 2147450880) by reflexivity.
    assert (HPKv : ACtlCutP.RCP.REAC_CTRL_PARSE_K = 8800) by reflexivity.
    pose proof HLK as (_ & _ & _ & HFLI).
    pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S280 & _).
    destruct S280 as (A' & HA' & Q280).
    assert (HA'eq : A' = A).
    { pose proof Q280 as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
      unfold ACtlCut.rgv in HA'. rewrite Hr9 in HA'.
      apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
      change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
      clear - HA' Hq0 Hq1 HA34 Hsp47 HAS. rewrite (Z.mod_small A) in HA' by lia.
      assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *. Z.div_mod_to_equations. lia. }
    subst A'.
    assert (R280 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 280) 8).
    { apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]. }
    assert (Rst : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 22) 5).
    { apply w4a_rng; [lia | lia |]. intros a Ha. apply (proj1 (Hfrsh a ltac:(unfold ACtlCutP.Sfr in Ha; lia))). }
    apply (w4_lift W3 0x81f50 regs3 mem3 md3
      (fun ms => exists m1 m2 (b0 b1 b2 b3 b4 : byte), ms = lib.Lib.MState.MS
          (lib.Lib.Frame.mkR (Z_to_bv 64 0x82048) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
             (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8) (Z_to_bv 64 A)
             (Z_to_bv 64 phi) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 176)) (Sem.reg_get regs3 13) (Sem.reg_get regs3 14)
             (Sem.reg_get regs3 15) (Sem.reg_get regs3 16) (Sem.reg_get regs3 17) (Z_to_bv 64 phi)
             (Z_to_bv 64 (ACtlCutP.Sfr fr)) (Z_to_bv 64 0) (Z_to_bv 64 S1) (Sem.reg_get regs3 22)
             (Sem.reg_get regs3 23) (Sem.reg_get regs3 24) (Sem.reg_get regs3 25) (Sem.reg_get regs3 26)
             (Sem.reg_get regs3 27) (Sem.reg_get regs3 28) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30)
             (Sem.reg_get regs3 31))
          lib.Reusable.YK11.fp_regs (Z_to_bv 64 ACtlCutP.RCP.REAC_CTRL_PARSE) lib.Reusable.YK11.fp_csr None m2
          (lib.Reusable.YK11.seg_rom B.Img0.rsegs) /\
        lib.Lib.Frame.munch [(A + 224, A + 232)] mem3 m1 /\ lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 /\
        lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (A + 224) (lib.Lib.Mem.le8 (Z_to_bv 64 S1)) /\
        lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 22, ACtlCutP.Sfr fr + 27)] m1 m2 /\
        lib.Lib.Frame.wmono B.Img0.rsegs m1 m2 /\
        lib.Lib.Mem.bytes_at B.Img0.rsegs m2 (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4] /\
        bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (POST cx)).
    { unfold Lib.Regs6ss.mkR_of. rewrite G9, G10, G19, G20', G21'.
      eapply Lib.ExecF.evtF_cut.
      - apply (B.Prog.Seg.F2F.f2_head0_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))); [lia | lia | lia | exact HW224 | exact R224].
      - intros ms1 (m1 & -> & MU1 & WM1 & BA1).
        assert (HRW : exists junk, lib.Lib.Step.rw_cells B.Img0.rsegs m1 (ACtlCutP.Sfr fr + 22) [lib.Lib.Cells.CB 5 junk]).
        { apply w4a_rw5; [lia | lia |]. intros i Hi.
          destruct (Hfrsh (ACtlCutP.Sfr fr + 22 + i) ltac:(unfold ACtlCutP.Sfr; lia)) as (_ & (b & Hb) & _).
          assert (Hm1 : m1 (Z_to_bv 64 (ACtlCutP.Sfr fr + 22 + i)) = Some b).
          { rewrite (MU1 (Z_to_bv 64 (ACtlCutP.Sfr fr + 22 + i))); [exact Hb|]. rewrite w4a_wa_u by lia.
            cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
          split; [exists b; exact Hm1|]. unfold wview. rewrite Hm1. discriminate. }
        destruct HRW as (junk & HRW).
        eapply Lib.ExecF.evtF_cut.
        + apply (B.Prog.Seg.F2F.f2_st_noinv_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (junk := junk)
            (pc0 := 0x82020) (pc1 := 0x82038); [left; split; reflexivity | rewrite G19u; exact HRW | rewrite G19u; exact Rst].
        + intros ms2 (a0' & m2 & b0 & b1 & b2 & b3 & b4 & -> & MU2 & WM2 & BA2 & Es0 & Es1 & Es2 & Es3 & Es4).
          rewrite G19u in MU2, BA2.
          assert (Q2 : lib.Lib.Mem.bytes_at B.Img0.rsegs m2 (A + 280) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))).
          { apply (w4a_ba_keep mem3 m2 _ _ Q280). rewrite lib.Lib.Mem.length_le8. intros x Hx.
            rewrite (w4a_mrd_munch _ _ _ x MU2 ltac:(lia)) by (cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
            apply (w4a_mrd_munch _ _ _ x MU1 ltac:(lia)). cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
          pose proof (lib.Lib.Mem.bytes_at_ov_read B.Img0.rsegs m2 (A + 280) _ 0 8 Q2
                        ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as HRD.
          replace (A + 280 + Z.of_nat 0) with (A + 280) in HRD by lia.
          change (skipn 0 (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))) with (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))) in HRD.
          rewrite (firstn_all2 (n := 8)) in HRD by (rewrite lib.Lib.Mem.length_le8; lia).
          eapply Lib.ExecF.evtF_mono.
          * apply (B.Prog.Seg.F2F.f2_pcall_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (o := fr + 176)
              (pcm := 0x82038) (pcr := 0x82048) (A := A); [left; split; reflexivity | reflexivity | lia | lia | exact HRD | exact R280].
          * intros ms3 ->. exists m1, m2, b0, b1, b2, b3, b4. split; [reflexivity|].
            split; [exact MU1|]. split; [exact WM1|]. split; [exact BA1|]. split; [exact MU2|]. split; [exact WM2|].
            split; [exact BA2|]. split; [exact Es0|]. split; [exact Es1|]. split; [exact Es2|]. split; [exact Es3 | exact Es4]. }
    intros ms' md' (m1 & m2 & b0 & b1 & b2 & b3 & b4 & -> & MU1 & WM1 & BA1 & MU2 & WM2 & BA2 & Es0 & Es1 & Es2 & Es3 & Es4)
      Hhid Hsame.
    assert (MU12 : lib.Lib.Frame.munch ([(A + 224, A + 232)] ++ [(ACtlCutP.Sfr fr + 22, ACtlCutP.Sfr fr + 27)]) mem3 m2)
      by exact (w4a2_munch_tr _ _ _ _ _ MU1 MU2).
    assert (WM12 : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m2) by (intros x Hx; exact (WM2 x (WM1 x Hx))).
    assert (HJ2 : AJ cx (own6 cx) ly3 S3 W3 m2 md' k).
    { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU12 WM12 Hhid Hsame).
      intros a Ha. cbn [app lib.Lib.Frame.outside] in Ha.
      assert (Hor : (A + 224 <= a < A + 232) \/ (ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 27)) by lia.
      destruct Hor as [Hw|Hs].
      - split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia.
      - destruct (Hfrsh a ltac:(unfold ACtlCutP.Sfr in Hs; lia)) as (_ & Hp & Hif).
        split; [lia|]. split; [exact Hp|]. right. right. right. exact Hif. }
    pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ2)) as HAR2.
    assert (AG12 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 224 <= x < A + 232) ->
                     ~ (ACtlCutP.Sfr fr + 22 <= x < ACtlCutP.Sfr fr + 27) -> AGR mem3 m2 x).
    { intros x Hx H1 H2. apply (w4a_mrd_munch _ _ _ x MU12 Hx). cbn [app lib.Lib.Frame.outside].
      split; [exact H1|]. split; [exact H2 | exact I]. }
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (RT := R) end.
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs ACtlCutP.RCP.REAC_CTRL_PARSE RT m2 md') (POST cx)).
    assert (HspRT : Reusable.YG0d.spZ RT = sp)
      by (change (Reusable.YG0d.spZ RT) with (Reusable.YG0d.spZ regs3); exact Hspz).
    assert (Happ36 : forall i, 0 <= i < 36 -> B.AsanRT.app_mem (fr + 176 + i)).
    { intros i Hi. destruct Hfrapp as (H0 & H1). pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as HC.
      unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
      unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H1. lia. }
    assert (Hrsv : forall i, 0 <= i < 36 ->
               ACtlCutP.Sfr fr + 22 <= B.AsanRT.shadow_addr (fr + 176 + i) < ACtlCutP.Sfr fr + 27).
    { intros i Hi. rewrite (w4a2_sh_off fr (fr + 176 + i) Hfr8 ltac:(lia)).
      replace (fr + 176 + i - fr) with (176 + i) by lia.
      assert (D1 : 22 <= (176 + i) / 8) by (apply Z.div_le_lower_bound; lia).
      assert (D2 : (176 + i) / 8 < 27) by (apply Z.div_lt_upper_bound; lia). lia. }
    apply (w4a_parse Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 m2 md' k RT phi 0 (fr + 176)
             (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) (POST cx) HJ2).
    - exact (w4a_arodata_cut _ _ _ _ _ _ _ _ HB HJ2).
    - change (getr RT 1) with (Z_to_bv 64 0x82048). apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - unfold Reusable.YG0d.raZ. change (getr RT 1) with (Z_to_bv 64 0x82048). rewrite w4a_wa_u by lia. lia.
    - change (getr RT 3) with (getr regs3 3). rewrite Hr3. exact Hgp0.
    - change (getr RT 4) with (getr regs3 4). exact Hr4.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - rewrite HspRT. exact Hsp16.
    - rewrite HspRT, HPKv. lia.
    - rewrite HspRT. lia.
    - rewrite Hfr. unfold ACtlCut.own6. vm_compute. reflexivity.
    - intros H50. lia.
    - intros _. split; [|split].
      + exists 6, (ACtlCut.c_fpos cx). split; [rewrite Hfr; left; reflexivity|]. rewrite Efa.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. split; [lia|]. split; [exact Hfr8 | lia].
      + clear - Hfr8. Z.div_mod_to_equations. lia.
      + apply w4a2_ra_of_addr.
        * exact (w4a2_rec_addr m2 fr b0 b1 b2 b3 b4 Hfr8 ltac:(lia) ltac:(unfold B.AsanRT.APPMEM_END; lia) Happ36 BA2
                   Es0 Es1 Es2 Es3 Es4).
        * intros i Hi. pose proof (Hrsv i Hi) as Hr.
          exact (proj1 (Hfrsh (B.AsanRT.shadow_addr (fr + 176 + i)) ltac:(unfold ACtlCutP.Sfr in Hr; lia))).
    - intros _ a Ha. right. right. right. exact (proj2 (proj2 (Hfrb a ltac:(lia)))).
    - exact (B.Prog.Seg.F5.c_tg_len _ _).
    - intros H50. lia.
    - intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ3 HP2 Hfrs2 Hab2 _ Ha02 Hrec2 Hkept.
      pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ3)) as HAR3.
      assert (Hfr2 : Reusable.YG01.frames S2 = own6 cx) by (rewrite Hfrs2; exact Hfr).
      assert (Hvis2 : forall x, Reusable.YA0n.w_H W3 x = false -> Reusable.YA0n.w_H W2 x = false).
      { intros x Hx. destruct (Reusable.YA0n.w_H W2 x) eqn:E; [|reflexivity]. rewrite (Hwle x E) in Hx. discriminate. }
      assert (KP : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
          kept_class B ly3 S3 (Reusable.YG0d.spZ RT - ACtlCutP.RCP.REAC_CTRL_PARSE_K) (Reusable.YG0d.spZ RT)
            (fun a => fr + 176 <= a < fr + 176 + 36) x -> AGR m2 mem2 x).
      { intros x Hx Hv Hc.
        apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m2 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x) Hv).
        rewrite w4a_wa_u by exact Hx. exact Hc. }
      rewrite HspRT, HPKv in KP.
      (* kept classes: high memory off the callee window (1), the frame's bytes / shadow off the record (4),
         the image off the owned extents and errno (3) *)
      assert (KW : forall x, A <= x < ACtlCut.c_sp cx -> AGR m2 mem2 x).
      { intros x Hx. apply KP; [lia | exact (proj1 (Hwin x ltac:(lia))) |]. left. split; lia. }
      assert (KF : forall x, fr <= x < fr + 4096 -> ~ (fr + 176 <= x < fr + 212) -> AGR m2 mem2 x).
      { intros x Hx Hn. apply KP; [lia | exact (proj1 (Hfrb x Hx)) |].
        right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [rewrite Hfr; left; reflexivity|].
        split; [left; unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng; cbn [fst snd]; rewrite Efa;
                change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia | cbv beta; lia]. }
      assert (KSH : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> AGR m2 mem2 a).
      { intros a Ha. pose proof (w4a2_shr_out a fr 4096 ltac:(lia) Hfrapp) as Ho.
        apply KP; [lia | exact (proj1 (Hfrsh a ltac:(unfold ACtlCutP.Sfr in Ha; lia))) |].
        right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [rewrite Hfr; left; reflexivity|].
        split; [right; unfold Reusable.YG0n.in_zr; cbn [fst snd]; rewrite Efa;
                unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF;
                change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512;
                unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr in Ha; lia
               | cbv beta; lia]. }
      assert (KK : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m2 mem2 x).
      { intros x Hx. pose proof (w4a2_kn_img x Hx) as Himg. destruct (ctl_kind_name_not_owned x Hx) as (Hno & Hne).
        destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hiv).
        unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Hiv.
        change ACtlCutP.KNA.KIND_NAME with 652672 in Hx.
        apply KP; [lia | apply Hiv; rewrite ?HIL, ?HIT; lia |].
        right. right. left. split; [exact Himg|]. split; [exact Hno | exact Hne]. }
      assert (AGW : forall x, A <= x < ACtlCut.c_sp cx -> ~ (A + 224 <= x < A + 232) -> AGR mem3 mem2 x).
      { intros x Hx Hn. rewrite (KW x Hx). apply AG12; lia. }
      assert (AGF : forall x, fr <= x < fr + 4096 -> ~ (fr + 176 <= x < fr + 212) -> AGR mem3 mem2 x).
      { intros x Hx Hn. rewrite (KF x Hx Hn). apply AG12; [lia | lia |].
        intros Hs. apply (w4a2_shr_out x fr 4096 ltac:(lia) Hfrapp). lia. }
      assert (AGSH : forall x, fr <= x < fr + 4096 -> ~ (fr + 176 <= x < fr + 216) ->
                       AGR mem3 mem2 (B.AsanRT.shadow_addr x)).
      { intros x Hx Hn. pose proof (w4a2_sh_in fr x Hfr8 Hx) as Hs.
        rewrite (KSH _ Hs). apply AG12; [lia | lia |].
        rewrite (w4a2_sh_off fr x Hfr8 ltac:(lia)). intros Hs'.
        destruct (Z_lt_le_dec x (fr + 176)) as [h|h].
        - assert ((x - fr) / 8 < 22) by (apply Z.div_lt_upper_bound; lia). lia.
        - assert (27 <= (x - fr) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert (AGK : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
      { intros x Hx. rewrite (KK x Hx). change ACtlCutP.KNA.KIND_NAME with 652672 in Hx. apply AG12; lia. }
      assert (BA3 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4]).
      { apply (w4a_ba_keep m2 mem2 _ _ BA2). cbn [length]. intros x Hx. apply KSH. lia. }
      (* the callee-saved pins *)
      assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E9 : getr regs2 9 = getr regs3 9).
      { transitivity (getr RT 9); [exact (HP2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact Hr9]. }
      assert (E18 : getr regs2 18 = Z_to_bv 64 phi) by exact (HP2 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E19 : getr regs2 19 = getr regs3 19).
      { transitivity (getr RT 19); [exact (HP2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact Hr19]. }
      assert (E20 : getr regs2 20 = Z_to_bv 64 0) by exact (HP2 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E22 : getr regs2 22 = getr regs3 22) by exact (HP2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
      assert (Hin3 : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hab2; exact Hin).
      (* the cut B82048_at *)
      change (Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x82048 regs2 mem2 md2) (POST cx)).
      apply (H48 cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ3 Hfr2 HFA);
        [unfold ix_cut, ACtlCutP.C_B82048_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk | |
         exact (w4a_ctlrt _ _ _ _ _ _ _ _ HB HJ3)].
      unfold ix_cut, ACtlCutP.C_B82048_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
      split.
      { apply (w4a2_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
        - intros A9 x HA9 HA9r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA9 Hr9 HA9r ltac:(lia)) in Hx.
          destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
          + apply AGW; lia.
          + apply AGW; lia.
          + apply AGF; lia.
          + apply AGW; lia.
          + apply AGF; lia.
        - exact (w4a2_frame_sh _ _ _ _ _ _ _ _ HJ3 Hfr2 HFA6). }
      exists phi.
      split; [rewrite Hab2; exact Hperm|]. split; [exact Hn26|]. split; [exact Hj|].
      split.
      { split; [lia|].
        pose proof (Reusable.YCbq.req_size_pos (flen cx j) ltac:(lia)) as Hrs.
        apply (w4a_blk_addr _ _ _ _ _ _ _ _ _ HAR3 Hin3); unfold B.ACtlK.a_size; lia. }
      split; [exact E18|]. split; [unfold ACtlCut.rgv; rewrite E0; exact E20|].
      split.
      { split.
        - exists A. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|]. unfold ACtlCutP.q64. rewrite <- ES1.
          apply (w4a_ba_keep m1 mem2 _ _ BA1). rewrite lib.Lib.Mem.length_le8. intros x Hx.
          rewrite (KW x ltac:(lia)).
          apply (w4a_mrd_munch _ _ _ x MU2 ltac:(lia)). cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
        - split.
          + apply (w4a_spill_keep regs3 regs2 mem3 mem2 A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9); [|exact S232].
            intros x Hx. apply AGW; lia.
          + assert (Enil : ACtlCutP.SM.t_phi (ACtlCut.c_in cx) j = []).
            { apply length_zero_iff_nil. rewrite B.Prog.SlotInv.t_phi_length, Et0. reflexivity. }
            rewrite Enil. split; [|cbn [length]; lia].
            split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
      split.
      { apply (w4a2_lk_move cx fr j regs3 regs2 mem3 mem2 A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
        - intros off x Hoff Hx. cbn [In] in Hoff. apply AGW; lia.
        - intros x Hx. apply AGF; lia.
        - intros x Hx. apply AGSH; unfold ACtlCutP.fragb in Hx; lia.
        - exact AGK.
        - exact (ctl_kind_name_addressable _ _ _ _ _ HAR3).
        - exact (w4a2_frame_stk _ _ _ _ _ _ _ _ HJ3 Hfr2 HFA6). }
      split; [exact (w4a_rgv_move _ _ _ _ H22 E22)|].
      split; [apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj); intros x Hx; [apply AGF; lia | apply AGSH; lia]|].
      split; [apply (w4a_rec0_move cx fr j mem3 mem2 HREC); intros x Hx; apply AGF; lia|].
      split.
      { split.
        - unfold ACtlCutP.pBb.
          assert (EtB : ACtlCutP.SM.t_B (ACtlCut.c_in cx) j =
                        snd (ACtlCutP.RPA.ctrlparse 0 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)))
            by (unfold ACtlCutP.SM.t_B; rewrite Et0; reflexivity).
          pose proof (B.Prog.Seg.F2.f2_tB_len (ACtlCut.c_in cx) j) as HtBl. rewrite EtB in HtBl |- *.
          apply (w4a_ba_of_aview W2 mem2); [lia | rewrite HtBl; lia | |].
          + intros i Hi. rewrite HtBl in Hi. apply Hvis2. exact (proj1 (Hfrb (fr + 176 + Z.of_nat i) ltac:(lia))).
          + intros i Hi. rewrite HtBl in Hi. exact (Hrec2 ltac:(lia) i Hi).
        - exact (w4a2_rec_addr mem2 fr b0 b1 b2 b3 b4 Hfr8 ltac:(lia) ltac:(unfold B.AsanRT.APPMEM_END; lia) Happ36 BA3
                   Es0 Es1 Es2 Es3 Es4). }
      split; [unfold ACtlCut.a0v, ACtlCut.rgv, ACtlCutP.SM.t_k; rewrite Et0; exact Ha02|].
      lia. }
  (* ---- len > 0: f2_head1_F, f2_mcpy_pre_F, __asan_memcpy (aj_intrin_at), then B81f78_at ---- *)
  assert (HN : 0 < flen cx j) by lia.
  pose proof (B.Prog.SlotInv.fc_range (ACtlCut.c_in cx) j) as Rc.
  assert (Hbl : 0 <= ACtlCutP.SM.t_body (ACtlCut.c_in cx) j /\
                ACtlCutP.SM.t_body (ACtlCut.c_in cx) j + flen cx j <= ACtlCut.c_n cx).
  { rewrite Hnlen. clear - Rc HN.
    unfold ACtlCutP.flen, ACtlCutP.SM.t_body, ACtlCutP.SM.t_len, ACtlCutP.SM.f_body,
      ACtlCutP.SM.f_len, ACtlCutP.SM.f_h, ACtlCutP.SM.f_left, ACtlCutP.SM.nlen in *. lia. }
  set (S0 := ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j) in *.
  assert (HinE : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (ENTRYBL cx)) by (destruct Hpn as [[H _] | [_ H]]; [lia | exact H]).
  assert (Hin2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact HinE).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin2) as (Hq16 & Hq4096 & Hqceil & Hqn0 & Hqreq & Hqvis & Hqshvis).
  assert (Hdisj : phi + flen cx j <= S0 \/ S0 + flen cx j <= phi).
  { destruct (in_split _ _ HinE) as (l1 & l2 & EE).
    pose proof (Reusable.YCbq.sep_blocks_perm segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx, ACtlCut.c_n cx)
                  (phi, flen cx j) (l1 ++ l2) HAR
                  ltac:(eapply Permutation_trans; [exact Hperm|]; rewrite EE; apply w4a2_perm2)) as Hd.
    unfold Reusable.YCbq.block_rng, Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. subst S0. lia. }
  assert (Hnot : ~ In (phi, flen cx j) (ENTRYBL cx)).
  { intros Hx. destruct (in_split _ _ Hx) as (m1 & m2 & EM).
    pose proof (Reusable.YCbq.sep_blocks_perm segs B LAWS ly3 S3 W3 mem3 md3 (phi, flen cx j) (phi, flen cx j)
                  (m1 ++ m2) HAR ltac:(eapply Permutation_trans; [exact Hperm|]; rewrite EM; apply w4a2_perm2)) as Hd.
    pose proof (Reusable.YCbq.req_size_pos (flen cx j) ltac:(lia)) as Hrs.
    unfold Reusable.YCbq.block_rng, Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  pose proof HIN as (HINa & HINb).
  assert (HSRC : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 S0 (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) j)).
  { pose proof (B.Prog.Seg.F2.f2_ba_sub mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx)
                  (Z.to_nat (ACtlCutP.SM.t_body (ACtlCut.c_in cx) j)) (Z.to_nat (flen cx j)) HINb
                  ltac:(lia)) as H.
    rewrite Z2Nat.id in H by lia. exact H. }
  pose proof (B.Prog.SlotInv.t_phi_length (ACtlCut.c_in cx) j) as HPHIl.
  apply (w4_lift W3 0x81f50 regs3 mem3 md3
    (fun ms => exists m1, ms = lib.Lib.MState.MS
        (lib.Lib.Frame.mkR (Z_to_bv 64 0x81f78) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
           (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8) (Z_to_bv 64 A)
           (Z_to_bv 64 phi) (Z_to_bv 64 S0) (Z_to_bv 64 (flen cx j)) (Sem.reg_get regs3 13) (Sem.reg_get regs3 14)
           (Sem.reg_get regs3 15) (Sem.reg_get regs3 16) (Sem.reg_get regs3 17) (Z_to_bv 64 phi)
           (Sem.reg_get regs3 19) (Z_to_bv 64 (flen cx j)) (Z_to_bv 64 S0) (Sem.reg_get regs3 22)
           (Sem.reg_get regs3 23) (Sem.reg_get regs3 24) (Sem.reg_get regs3 25) (Sem.reg_get regs3 26)
           (Sem.reg_get regs3 27) (Sem.reg_get regs3 28) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30)
           (Sem.reg_get regs3 31))
        lib.Reusable.YK11.fp_regs (Z_to_bv 64 B.Prog.Seg.F2F.MCCF.ASAN_MEMCPY) lib.Reusable.YK11.fp_csr None m1
        (lib.Reusable.YK11.seg_rom B.Img0.rsegs) /\
      lib.Lib.Frame.munch [(A + 224, A + 232)] mem3 m1 /\ lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 /\
      lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (A + 224) (lib.Lib.Mem.le8 (Z_to_bv 64 S0)))
    (POST cx)).
  { unfold Lib.Regs6ss.mkR_of. rewrite G9, G10, G20, G21.
    eapply Lib.ExecF.evtF_cut.
    - apply (B.Prog.Seg.F2F.f2_head1_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))); [lia | lia | lia | lia | lia | exact HW224 | exact R224].
    - intros ms1 (m1 & -> & MU1 & WM1 & BA1).
      eapply Lib.ExecF.evtF_mono; [apply B.Prog.Seg.F2F.f2_mcpy_pre_F|].
      intros ms2 ->. exists m1. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1 | exact BA1]. }
  intros ms' md' (m1 & -> & MU1 & WM1 & BA1) Hhid Hsame.
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 m1 md' k).
  { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU1 WM1 Hhid Hsame).
    intros a Ha. apply w4a_not_out1 in Ha.
    split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia. }
  pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ1)) as HAR1.
  assert (AG1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 224 <= x < A + 232) -> AGR mem3 m1 x).
  { intros x Hx Hn. apply (w4a_mrd_munch _ _ _ x MU1 Hx). cbn [lib.Lib.Frame.outside]. split; [exact Hn | exact I]. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin) as (_ & _ & _ & _ & Hppres1 & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin2) as (_ & _ & _ & _ & Hqpres1 & _).
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (RT := R) end.
  change (Reusable.YA0n.SRr segs W3 (mkCfg (lib.Reusable.YK11.mkst RT (Z_to_bv 64 Reusable.YB1w.tfib_A_asan_memcpy) m1
           (lib.Reusable.YK11.seg_rom segs)) md') (POST cx)).
  assert (HspRT : Reusable.YG0d.spZ RT = sp)
    by (change (Reusable.YG0d.spZ RT) with (Reusable.YG0d.spZ regs3); exact Hspz).
  eapply Reusable.YA0n.SRr_bind.
  { apply (Reusable.YCbq.aj_intrin_at segs B LAWS segs_low Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy AMEMCPY
            W3 RT m1 Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
            (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (own6 cx) ly3 S3 md' k phi S0 (flen cx j) (sp - ACtlCut.c_sp cx)
            (Z_to_bv 64 0x81f78) HJ1).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspRT. lia.
    - rewrite Zminus_mod, Hsp16, Hsp0_16. reflexivity.
    - lia.
    - lia.
    - change (getr RT 3) with (getr regs3 3). rewrite Hr3. exact Hgp0.
    - change (getr RT 4) with (getr regs3 4). exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [|lia]. right. right. left. exists phi, (flen cx j).
      split; [exact Hin|]. split; [exact Hnot | lia].
    - apply (Reusable.YCbq.amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin); lia.
    - apply (Reusable.YCbq.range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin); lia.
    - intros Hn'. apply (Reusable.YCbq.shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin); lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split; [apply (Reusable.YCbq.aview_some_of_apresent segs); exact (proj1 (Hqpres1 a ltac:(lia)))|].
        rewrite HspRT. lia.
      + split; [lia|].
        split; [apply (Reusable.YCbq.amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin2); lia|].
        split; [apply (Reusable.YCbq.range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin2); lia|].
        intros Hn'. apply (Reusable.YCbq.shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hin2); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hcopy & Hframe & Hpres2).
  destruct (B.ProgWorld.ctl_post_memcpy W3 m1 mem2 sp phi S0 (flen cx j) (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) j))
    as (MUV & WMV & RWC).
  { lia. } { lia. } { lia. }
  { rewrite HPHIl. lia. }
  { intros a Ha. exact (proj1 (Hppres1 a ltac:(lia))). }
  { apply (w4a_ba_keep mem3 m1 _ _ HSRC). rewrite HPHIl. intros x Hx. apply AG1; lia. }
  { intros i Hi. apply Hqvis. lia. }
  { intros i Hi. exact (Hcopy i Hi). }
  { split; [|exact Hpres2]. intros a Ha Hout. destruct Hout as (Ho1 & Ho2 & _). apply Hframe; [exact Ha | exact Ho1 | lia]. }
  pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ2)) as HAR2.
  (* memory kept at visible addresses off the copy, the callee window and the head's spill *)
  assert (AGV : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
      ~ (phi <= x < phi + flen cx j) -> ~ (sp - 4096 <= x < sp) -> AGR m1 mem2 x).
  { intros x Hx Hv H2 H3. apply MUV; [exact Hv|]. rewrite w4a_wa_u by exact Hx.
    cbn [lib.Lib.Frame.outside]. rewrite HESv. split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (AG : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
      ~ (A + 224 <= x < A + 232) -> ~ (phi <= x < phi + flen cx j) -> ~ (sp - 4096 <= x < sp) -> AGR mem3 mem2 x).
  { intros x Hx Hv H1 H2 H3. rewrite (AGV x Hx Hv H2 H3). exact (AG1 x Hx H1). }
  assert (AGW : forall x, A <= x < ACtlCut.c_sp cx -> ~ (A + 224 <= x < A + 232) -> AGR mem3 mem2 x).
  { intros x Hx Hn. apply AG; [lia | exact (proj1 (Hwin x ltac:(lia))) | exact Hn | lia | lia]. }
  assert (AGF : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 x).
  { intros x Hx.
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (flen cx j) 6 (ACtlCut.c_fpos cx) HAR Hin
                  ltac:(rewrite Hfr; left; reflexivity)) as Hd.
    rewrite Efa in Hd. unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd.
    apply AG; [lia | exact (proj1 (Hfrb x Hx)) | lia | lia | lia]. }
  assert (AGSR : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> AGR mem3 mem2 a).
  { intros a Ha. pose proof (w4a2_shr_out a phi _ ltac:(lia) Hpapp) as Ho.
    apply AG; [lia | exact (proj1 (Hfrsh a Ha)) | lia | lia | lia]. }
  assert (AGSH : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 (B.AsanRT.shadow_addr x)).
  { intros x Hx. apply AGSR. exact (w4a2_sh_in fr x Hfr8 Hx). }
  assert (AGK : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
  { intros x Hx. pose proof (w4a2_kn_img x Hx) as Himg.
    assert (Hnb : ~ (phi <= x < phi + flen cx j)).
    { intros Hb.
      assert (Hcl : exists p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) /\ p <= x < p + Reusable.YG00.req_size n)
        by (exists phi, (flen cx j); split; [exact Hin | lia]).
      destruct (Reusable.YG0d.al_client_img _ _ LAWS _ _ _ _ _ x HAR (or_introl Hcl)) as (_ & Hni). exact (Hni Himg). }
    destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hiv).
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Hiv.
    change ACtlCutP.KNA.KIND_NAME with 652672 in Hx.
    apply AG; [lia | apply Hiv; rewrite ?HIL, ?HIT; lia | lia | exact Hnb | lia]. }
  (* the callee-saved pins *)
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9).
  { transitivity (getr RT 9); [exact (HP2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact Hr9]. }
  assert (E18 : getr regs2 18 = Z_to_bv 64 phi) by exact (HP2 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (HP2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20).
  { transitivity (getr RT 20); [exact (HP2 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact H20]. }
  assert (E21 : getr regs2 21 = getr regs3 21).
  { transitivity (getr RT 21); [exact (HP2 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact H21]. }
  assert (E22 : getr regs2 22 = getr regs3 22) by exact (HP2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  (* the cut B81f78_at *)
  apply (H78 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfr HFA);
    [unfold ix_cut, ACtlCutP.C_B81f78_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk | |
     exact (w4a_ctlrt _ _ _ _ _ _ _ _ HB HJ2)].
  unfold ix_cut, ACtlCutP.C_B81f78_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
  split.
  { apply (w4a_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
    intros A' x HA' HA'r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA' Hr9 HA'r ltac:(lia)) in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
    - apply AGW; lia.
    - apply AGW; lia.
    - apply AGF; lia.
    - apply AGSR. rewrite HFSv in Hx. lia.
    - apply AGW; lia.
    - apply AGF; lia. }
  exists phi.
  split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj|].
  split.
  { split; [lia|].
    pose proof (Reusable.YCbq.req_size_pos (flen cx j) ltac:(lia)) as Hrs.
    apply (w4a_blk_addr _ _ _ _ _ _ _ _ _ HAR2 Hin); unfold B.ACtlK.a_size; lia. }
  split; [exact E18|]. split; [exact (w4a_rgv_move _ _ _ _ H20 E20)|].
  split.
  { split.
    - exists A. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|]. unfold ACtlCutP.q64.
      apply (w4a_ba_keep m1 mem2 _ _ BA1). rewrite lib.Lib.Mem.length_le8. intros x Hx.
      apply AGV; [lia | exact (proj1 (Hwin x ltac:(lia))) | lia | lia].
    - split.
      + apply (w4a_spill_keep regs3 regs2 mem3 mem2 A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9); [|exact S232].
        intros x Hx. apply AGW; lia.
      + split; [|rewrite HPHIl; lia].
        destruct RWC as ((_ & Hb) & _). cbn [lib.Lib.Cells.cbytes lib.Lib.Cells.cells_bytes] in Hb.
        rewrite app_nil_r in Hb. exact Hb. }
  split.
  { apply (w4a2_lk_move cx fr j regs3 regs2 mem3 mem2 A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
    - intros off x Hoff Hx. cbn [In] in Hoff. apply AGW; lia.
    - intros x Hx. apply AGF; lia.
    - intros x Hx. apply AGSH. unfold ACtlCutP.fragb in Hx. lia.
    - exact AGK.
    - exact (ctl_kind_name_addressable _ _ _ _ _ HAR2).
    - exact (w4a2_frame_stk _ _ _ _ _ _ _ _ HJ2 Hfr HFA6). }
  split; [exact (w4a_fc_move cx fr j regs3 regs2 mem3 mem2 A HFC Hr9 ltac:(lia) ltac:(lia) E9 E20 E21
                   ltac:(intros x Hx; apply AGW; lia))|].
  split; [exact (w4a_rgv_move _ _ _ _ H22 E22)|].
  split; [apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj); intros x Hx; [apply AGF; lia | apply AGSH; lia]|].
  apply (w4a_rec0_move cx fr j mem3 mem2 HREC); intros x Hx; apply AGF; lia.
Qed.

(* =========================================================================================================
   LOCAL LEMMAS OF seg_F3 (prefix w4a3_).  They are the pieces the parse call needs that the shared kit does not
   carry: the small shadow-byte arithmetic of the five record-shadow stores, the frame's app-memory place (so a
   frame shadow byte is never a block byte or a record byte), the image place of the KIND_NAME table, and the
   three move lemmas whose kit twins read a byte this stage rewrites (FRAC's frame shadow) or a byte no class
   keeps (KNT's shadow, which comes from the post-call AR instead).
   ========================================================================================================= *)

(* A byte whose signed value is a small non-negative number has that value unsigned (the converse of w4a_sbyte). *)
Lemma w4a3_usgn : forall (b : byte) (v : Z), 0 <= v < 128 -> bv_signed b = v -> bv_unsigned b = v.
Proof.
  intros b v Hv Hs. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  destruct (Z_lt_le_dec (bv_unsigned b) 128) as [Hlt|Hge];
    [rewrite (w4a_sbyte b ltac:(lia)) in Hs; exact Hs|].
  exfalso. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hs.
  change (2 ^ Z.of_N 8) with 256 in Hs. change (256 `div` 2) with 128 in Hs.
  assert (E : (bv_unsigned b + 128) mod 256 = bv_unsigned b - 128).
  { replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E in Hs. lia.
Qed.

(* The granule index of a byte of an 8-aligned object. *)
Lemma w4a3_div8 : forall p x q, p mod 8 = 0 -> 0 <= p -> p + 8 * q <= x < p + 8 * q + 8 -> x / 8 = p / 8 + q.
Proof.
  intros p x q Hm Hp Hx. symmetry.
  apply (Z.div_unique_pos x 8 (p / 8 + q) (x - (p + 8 * q))); [lia|].
  pose proof (Z.div_mod p 8 ltac:(lia)) as D. lia.
Qed.

(* A frame's shadow bytes are not application memory, so they are no byte of a live block and no byte of the
   frame itself (the parse call's E = the 36 record bytes). *)
Lemma w4a3_sh_out : forall f p n a,
  Reusable.YG0f.in_app f 4096 -> Reusable.YG0f.in_app p n -> p <= a < p + n ->
  ~ (B.AsanRT.shadow_addr f <= a < B.AsanRT.shadow_addr f + 512).
Proof.
  intros f p n a Hf Hp Hin Ha.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof (Reusable.YG0f.in_app_addr p n a Hp Hin) as Happ.
  unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hf.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  pose proof (Z.div_mod f 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound f 8 ltac:(lia)) as Dm.
  lia.
Qed.

(* The journal's layout keeps the frame's address (w4a_frame's own first step, named for the stage). *)
Lemma w4a3_frame_addr : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ Hfr.
  pose proof HJ as (_ & Hly & _).
  rewrite Hfr. unfold Reusable.YG0f.frame_addr.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

(* The owned frame is application memory (AR's frame law). *)
Lemma w4a3_frame_app : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  Reusable.YG0f.in_app fr 4096.
Proof using LAWS.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ Hfrs Hfr.
  pose proof HJ as (HAR & _).
  pose proof (w4a3_frame_addr cx ly3 S3 W3 mem3 md3 k fr HJ Hfr) as Efa.
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Happ & _).
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efa, E6 in Happ. exact Happ.
Qed.

(* The KIND_NAME table is image memory (class 3 of kept_class). *)
Lemma w4a3_kn_img : forall a, ACtlCutP.KNA.KIND_NAME <= a < ACtlCutP.KNA.KIND_NAME + 112 ->
  Reusable.YG0d.in_img segs a.
Proof using tfibsegs_rsegs.
  intros a Ha. change ACtlCutP.KNA.KIND_NAME with 652672 in Ha.
  unfold Reusable.YG0d.in_img. rewrite tfibsegs_rsegs.
  destruct (find_segment B.Img0.rsegs 652672 112) as [sg|] eqn:E.
  - destruct (lib.Reusable.YK04.find_segment_some_spec _ _ _ _ E) as (Hin & H1 & H2).
    exists sg. split; [exact Hin | lia].
  - exfalso.
    assert (Hb : match find_segment B.Img0.rsegs 652672 112 with Some _ => true | None => false end = true)
      by (vm_compute; reflexivity).
    rewrite E in Hb. discriminate.
Qed.

(* A present range has SOME byte list (FRAC's frame-shadow conjunct after the five record-shadow stores). *)
Lemma w4a3_bytes_of_present : forall (m : word -> option byte) lo n,
  0 <= lo -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall a, lo <= a < lo + n -> exists b, m (Z_to_bv 64 a) = Some b) ->
  exists bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m lo bs /\ length bs = Z.to_nat n.
Proof.
  intros m lo n Hlo Hn Hhi HP.
  exists (map (fun i : nat => match m (Z_to_bv 64 (lo + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
            (seq 0 (Z.to_nat n))).
  assert (HL : length (map (fun i : nat => match m (Z_to_bv 64 (lo + Z.of_nat i)) with
                                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n)))
               = Z.to_nat n) by (rewrite length_map, length_seq; reflexivity).
  split; [|exact HL].
  split; [exact Hlo|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi.
  assert (Hs : nth_error (seq 0 (Z.to_nat n)) i = Some i).
  { rewrite (nth_error_nth' (seq 0 (Z.to_nat n)) 0%nat) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. reflexivity. }
  rewrite (map_nth_error _ i _ Hs).
  destruct (HP (lo + Z.of_nat i) ltac:(lia)) as (b & Hb).
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

(* AsanRT's addressable, read through the core's view at visible shadow bytes (PARSE's afobj premise). *)
Lemma w4a3_ra_of_addr : forall (W : Reusable.YA0n.world segs) m p n,
  B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof using tfibsegs_rsegs.
  intros W m p n (H0 & H1 & H2 & HA) HV x Hx.
  destruct (HA (x - p) ltac:(lia)) as (Happ & b & Hb & Hok).
  assert (Ex : p + (x - p) = x) by lia. rewrite Ex in Hb, Hok.
  pose proof (HV (x - p) ltac:(lia)) as Hv. rewrite Ex in Hv.
  assert (Esh : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Esh. rewrite (w4a_aview_mrd W m _ Hv). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. cbn [option_map].
  exists (bv_unsigned b). split; [reflexivity|].
  unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm8.
  destruct Hok as [Hz|(Hlt & Hle)].
  - left. exact (w4a3_usgn b 0 ltac:(lia) Hz).
  - right. rewrite (w4a3_usgn b (bv_signed b) ltac:(lia) eq_refl). lia.
Qed.

(* The five record-shadow stores make the 36 record bytes addressable (0 0 0 0 4 over [fr + 176, fr + 216)). *)
Lemma w4a3_fps_addr : forall (m : word -> option byte) fr b0 b1 b2 b3 b4,
  Reusable.YG0f.in_app fr 4096 -> fr mod 32 = 0 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4] ->
  bv_signed b0 = 0 -> bv_signed b1 = 0 -> bv_signed b2 = 0 -> bv_signed b3 = 0 -> bv_signed b4 = 4 ->
  B.AsanRT.addressable m (fr + 176) 36.
Proof.
  intros m fr b0 b1 b2 b3 b4 Happ Hfr32 HB5 E0 E1 E2 E3 E4.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof Happ as Happ'. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg,
    Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ'.
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof HB5 as (HBa & HBb & HBc).
  split; [lia|]. split; [lia|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
  intros i Hi.
  assert (Happm : B.AsanRT.app_mem (fr + 176 + i)).
  { pose proof (Reusable.YG0f.in_app_addr fr 4096 (fr + 176 + i) Happ ltac:(lia)) as Ha.
    unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Ha.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia. }
  assert (Hsh : forall q, 0 <= q -> fr + 176 + 8 * q <= fr + 176 + i < fr + 176 + 8 * q + 8 ->
            B.AsanRT.shadow_addr (fr + 176 + i) = ACtlCutP.Sfr fr + 22 + q).
  { intros q Hq0 Hq. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    rewrite (w4a3_div8 fr (fr + 176 + i) (22 + q) Hfr8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hcase : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3 \/ i / 8 = 4)
    by (Z.div_mod_to_equations; lia).
  assert (Hd : 8 * (i / 8) <= i < 8 * (i / 8) + 8)
    by (pose proof (Z.div_mod i 8 ltac:(lia)); pose proof (Z.mod_pos_bound i 8 ltac:(lia)); lia).
  split; [exact Happm|].
  destruct Hcase as [Hc|[Hc|[Hc|[Hc|Hc]]]]; rewrite Hc in Hd.
  - rewrite (Hsh 0 ltac:(lia) ltac:(lia)).
    pose proof (HBc 0%nat ltac:(cbn [length]; lia)) as Hn. cbn [nth_error] in Hn.
    change (Z.of_nat 0) with 0 in Hn.
    exists b0. split; [exact Hn | left; exact E0].
  - rewrite (Hsh 1 ltac:(lia) ltac:(lia)).
    pose proof (HBc 1%nat ltac:(cbn [length]; lia)) as Hn. cbn [nth_error] in Hn.
    change (Z.of_nat 1) with 1 in Hn.
    exists b1. split; [exact Hn | left; exact E1].
  - rewrite (Hsh 2 ltac:(lia) ltac:(lia)).
    pose proof (HBc 2%nat ltac:(cbn [length]; lia)) as Hn. cbn [nth_error] in Hn.
    change (Z.of_nat 2) with 2 in Hn.
    exists b2. split; [exact Hn | left; exact E2].
  - rewrite (Hsh 3 ltac:(lia) ltac:(lia)).
    pose proof (HBc 3%nat ltac:(cbn [length]; lia)) as Hn. cbn [nth_error] in Hn.
    change (Z.of_nat 3) with 3 in Hn.
    exists b3. split; [exact Hn | left; exact E3].
  - rewrite (Hsh 4 ltac:(lia) ltac:(lia)).
    pose proof (HBc 4%nat ltac:(cbn [length]; lia)) as Hn. cbn [nth_error] in Hn.
    change (Z.of_nat 4) with 4 in Hn.
    exists b4. split; [exact Hn|]. right. rewrite E4. split; [|lia].
    assert (Hm : (fr + 176 + i) mod 8 = i - 32) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* aregs_preserved at the register numbers the cut bodies read. *)
Lemma w4a3_ap : forall regs regs', Reusable.YG0d.aregs_preserved regs regs' ->
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs regs' H. unfold Reusable.YG0d.aregs_preserved in H.
  split; [exact (H 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (H 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
  exact (H 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
Qed.

(* FRAC's move with the frame shadow supplied (the five stores rewrite five of its bytes). *)
Lemma w4a3_frac_move : forall cx fr sel regs regs' m m',
  ACtlCutP.FRAC B cx fr sel regs m ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  (exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs m' (ACtlCutP.Sfr fr) sh /\
     length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  (forall A x, ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
     A + 40 <= x < A + 56 \/ A + 336 <= x < A + 344 \/ fr <= x < fr + 24 \/
     ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx \/ fr + 4088 <= x < fr + 4096 ->
     AGR m m' x) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' HF E2 E3 E4 E8 E9 E19 E26 HSH K.
  destruct HF as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & (sh & Hsh & Hshl) & Hsaved & Qtr).
  pose proof (w4a_spZ regs) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  unfold ACtlCut.c_sp in *.
  assert (HA : 0 <= A < 2 ^ 64) by lia.
  exists A, sp.
  split; [rewrite E2; exact Hr2|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact Hr4|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr8 E8)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|].
  split; [rewrite E3; exact Hr3|].
  split; [exact (w4a_rgv_move _ _ _ _ Hr19 E19)|]. split; [exact (w4a_rgv_move _ _ _ _ Hr26 E26)|].
  do 8 (split; [assumption|]).
  unfold ACtlCutP.q64 in *.
  split; [apply (w4a_ba_keep m m' _ _ Q336); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q48); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Q40); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh1); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [apply (w4a_ba_keep m m' _ _ Qh2); rewrite lib.Lib.Mem.length_le8; intros x Hx; apply (K A x Hr9 HA); lia|].
  split; [exact HSH|].
  split; [apply (w4a_ba_keep m m' _ _ Hsaved); rewrite w4a_saved_len; intros x Hx; apply (K A x Hr9 HA); lia|].
  apply (w4a_ba_keep m m' _ _ Qtr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply (K A x Hr9 HA). lia.
Qed.

(* FLI's move with KNT's addressable supplied (the KIND_NAME shadow is allocator-owned: it comes from the
   post-call AR by ctl_kind_name_addressable, never from a kept class). *)
Lemma w4a3_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS KI HKNa' HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & HKNa) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split.
  { split.
    - apply (w4a_ba_keep m m' _ _ HKNb). pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
      intros x Hx. apply KI. lia.
    - exact HKNa'. }
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.

Lemma w4a3_lk_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off (240 :: [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304]) -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR m m' x) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS KI HKNa' HSTK.
  split; [exact Hj|].
  split; [apply (w4a_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply (KA 240 x); [left; reflexivity | exact Hx]|].
  split; [exact (w4a_our_move cx fr m m' HOUR KF)|].
  apply (w4a3_fli_move cx fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27);
    [|exact KS | exact KI | exact HKNa' | exact HSTK].
  intros off x Hoff Hx. apply (KA off x); [right; exact Hoff | exact Hx].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81f78_at j (0x81f78, own6, k <= 14+2j+1) --S_F3--> B81fbc_at j | B82048_at j.
   S_F3 (Seg/F3.v seg_F3 :108): len < 50 -> the short parse block 0x82020 (as S_F2's len = 0 arm) -> 0x82048;
   len >= 50 -> T13 / T14, the long-frame record-shadow stores 0x81f94 .. and reac_ctrl_parse(Phi, len, fr + 176)
   @0x81fb8 returning at 0x81fbc. *)
Lemma seg_F3 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B81fbc_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B81f78_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx LAWS segs_low
  ctl_kind_name_addressable ctl_kind_name_not_owned PARSE TFIB_SYMS RELRO_IMG RO_OFL.
  intros POST j Hbc H48 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B81f78_at in Hk, HBODY, HJ, Hfrs, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfrs, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (HFRAC & phi & Hperm & Hn26 & Hj & HHB & H18 & H20 & HFT & HLK & HFC & H22 & HFSj & HREC).
  (* ---- the journal's bits, the frame, the spill base, the turn block ---- *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HPK : ACtlCutP.RCP.REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  rewrite HSTKv in Hceil, Hwin.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & (sh0 & Hsh0 & Hshl0) & Hsaved & Qtr).
  pose proof (w4a_spZ regs3) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  unfold ACtlCut.rgv in Hr9, Hr19, H18, H20.
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hn0 & Hreq & Hpvis & Hpshvis).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hin)
    as (_ & _ & _ & Happb & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ Hfrs (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
    as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  pose proof (w4a3_frame_addr cx ly3 S3 W3 mem3 md3 k fr HJ (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl))) as Efa.
  pose proof (w4a3_frame_app cx ly3 S3 W3 mem3 md3 k fr HJ Hfrs
                (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl))) as Happf.
  assert (Happ176 : Reusable.YG0f.in_app (fr + 176) 36)
    by (apply (Reusable.YG0f.in_app_sub fr 4096); [exact Happf | lia | lia | lia]).
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (ESfr : ACtlCutP.Sfr fr = B.AsanRT.shadow_addr fr) by reflexivity.
  assert (Esh6 : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, B.AsanRT.shadow_addr,
        B.AsanRT.ASAN_K; lia).
  assert (HA34 : 2 ^ 34 <= A) by lia.
  assert (Hsfr : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 4096 <= A).
  { unfold ACtlCutP.Sfr. pose proof (w4a_sh_lt fr (A - 4096) ltac:(lia) ltac:(lia)). lia. }
  assert (HSfrlo : 2147450880 <= ACtlCutP.Sfr fr).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hgp : lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B)).
  { pose proof HB as ((Hpre & _) & _). destruct Hpre as (_ & _ & _ & Hg & _). exact Hg. }
  assert (HSHfr : forall d, B.AsanRT.shadow_addr (fr + d) = ACtlCutP.Sfr fr + d / 8 /\
                            8 * (d / 8) <= d < 8 * (d / 8) + 8).
  { intros d.
    assert (Hdd : 8 * (d / 8) <= d < 8 * (d / 8) + 8)
      by (pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
    split; [|exact Hdd].
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    rewrite (w4a3_div8 fr (fr + d) (d / 8) Hfr8 ltac:(lia) ltac:(lia)). lia. }

  (* =======================================================================================================
     THE SHARED CONTINUATION: at the reac_ctrl_parse entry, with the five record-shadow stores done and the
     call registers set.  Both arms of `bltu s4,50` reach it; pcr is the arm's return pc (the cut).
     ======================================================================================================= *)
  assert (HKc : forall (pcr : Z) (R : bvmap 5 word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte) md',
    (pcr = 0x81fbc /\ 50 <= ACtlCutP.flen cx j) \/ (pcr = 0x82048 /\ ACtlCutP.flen cx j < 50) ->
    getr R 1 = Z_to_bv 64 pcr ->
    getr R 2 = getr regs3 2 -> getr R 3 = getr regs3 3 -> getr R 4 = getr regs3 4 ->
    getr R 8 = getr regs3 8 -> getr R 9 = getr regs3 9 ->
    getr R 10 = Z_to_bv 64 phi -> getr R 11 = Z_to_bv 64 (ACtlCutP.flen cx j) ->
    getr R 12 = Z_to_bv 64 (fr + 176) ->
    getr R 18 = getr regs3 18 -> getr R 19 = getr regs3 19 -> getr R 20 = getr regs3 20 ->
    getr R 21 = getr regs3 21 -> getr R 22 = getr regs3 22 -> getr R 26 = getr regs3 26 ->
    getr R 27 = getr regs3 27 ->
    lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 22, ACtlCutP.Sfr fr + 27)] mem3 m1 ->
    lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 ->
    lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4] ->
    bv_signed b0 = 0 -> bv_signed b1 = 0 -> bv_signed b2 = 0 -> bv_signed b3 = 0 -> bv_signed b4 = 4 ->
    (forall x : word, Reusable.YA0n.w_H W3 x = true -> m1 x = mem3 x) ->
    Reusable.YK04.same_but_materialized md3 md' ->
    Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs ACtlCutP.RCP.REAC_CTRL_PARSE R m1 md') (POST cx)).
  { intros pcr R m1 b0 b1 b2 b3 b4 md' Harm E1 E2 E3 E4 E8 E9 E10 E11 E12 E18 E19 E20 E21 E22 E26 E27
      MU1 WM1 HB5 Eb0 Eb1 Eb2 Eb3 Eb4 Hhid Hsame.
    assert (ESP : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz).
    assert (Hpcr : pcr = 0x81fbc \/ pcr = 0x82048)
      by (destruct Harm as [(-> & _)|(-> & _)]; [left|right]; reflexivity).
    assert (AG31 : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 22 <= x < ACtlCutP.Sfr fr + 27) ->
      AGR mem3 m1 x).
    { intros x Hx Hn. apply (w4a_mrd_munch _ _ _ x MU1 Hx). cbn [lib.Lib.Frame.outside].
      split; [exact Hn | exact I]. }
    assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 m1 md' k).
    { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU1 WM1 Hhid Hsame).
      intros a Ha. apply w4a_not_out1 in Ha.
      destruct (Hfrsh a ltac:(rewrite <- ESfr; lia)) as (Hv & Hp & Hinf).
      split; [lia|]. split; [exact Hp|]. right; right; right. exact Hinf. }
    assert (HADDR1 : B.AsanRT.addressable m1 (fr + 176) 36)
      by exact (w4a3_fps_addr m1 fr b0 b1 b2 b3 b4 Happf Hfr32 HB5 Eb0 Eb1 Eb2 Eb3 Eb4).
    assert (HSHrec : forall i, 0 <= i < 36 ->
      B.AsanRT.shadow_addr (fr + 176 + i) = ACtlCutP.Sfr fr + 22 + i / 8 /\ 0 <= i / 8 <= 4).
    { intros i Hi.
      assert (Hd : 8 * (i / 8) <= i < 8 * (i / 8) + 8)
        by (pose proof (Z.div_mod i 8 ltac:(lia)); pose proof (Z.mod_pos_bound i 8 ltac:(lia)); lia).
      assert (Hq : 0 <= i / 8 <= 4) by (Z.div_mod_to_equations; lia).
      split; [|exact Hq].
      unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      rewrite (w4a3_div8 fr (fr + 176 + i) (22 + i / 8) Hfr8 ltac:(lia) ltac:(lia)). lia. }
    apply (w4a_parse Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
             (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 m1 md' k R
             phi (ACtlCutP.flen cx j) (fr + 176) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) (POST cx) HJ1).
    - exact (w4a_arodata_cut cx (own6 cx) ly3 S3 W3 m1 md' k HB HJ1).
    - rewrite E1. destruct Hpcr as [ -> | -> ]; apply lib.Reusable.YK0s.ret_ok_even; vm_compute; reflexivity.
    - unfold Reusable.YG0d.raZ. rewrite E1.
      destruct Hpcr as [ -> | -> ]; rewrite w4a_wa_u by lia; lia.
    - rewrite E3, Hr3. exact Hgp.
    - rewrite E4. exact Hr4.
    - exact E10.
    - exact E11.
    - exact E12.
    - lia.
    - rewrite ESP. exact Hsp16.
    - rewrite ESP. lia.
    - rewrite ESP. lia.
    - assert (Hcc : Reusable.YG01.count_cid 1 (Reusable.YG01.frames S3) = 0).
      { rewrite Hfrs. unfold ACtlCut.own6. cbn [Reusable.YG01.count_cid]. reflexivity. }
      rewrite Hcc. assert (Hf1 : 0 < Reusable.YG00.fs_frames 1) by (vm_compute; reflexivity). lia.
    - intros H50. exists (ACtlCutP.flen cx j). split; [exact Hin | lia].
    - intros _. split.
      + exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [lia|].
        rewrite Efa. split; [exact Hfr8|]. split; [lia|].
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + split; [Z.div_mod_to_equations; lia|].
        apply (w4a3_ra_of_addr W3 m1 (fr + 176) 36 HADDR1).
        intros i Hi. destruct (HSHrec i Hi) as (Es & Hq). rewrite Es.
        exact (proj1 (Hfrsh (ACtlCutP.Sfr fr + 22 + i / 8) ltac:(rewrite <- ESfr; lia))).
    - intros _ a Ha. right; right; right. exact (proj2 (proj2 (Hfrb a ltac:(lia)))).
    - exact (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j).
    - intros H50 i Hi.
      assert (HGb : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 phi (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j))
        by exact (B.Prog.SlotInv.t_g_of_phi mem3 phi (ACtlCut.c_in cx) j (proj1 (proj2 (proj2 HFT))) H50).
      assert (HGb1 : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 phi (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)).
      { apply (w4a_ba_keep mem3 m1 _ _ HGb). rewrite (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j).
        intros x Hx. apply AG31; [lia|]. intros Hc.
        exact (w4a3_sh_out fr phi (Reusable.YG00.req_size (ACtlCutP.flen cx j)) x Happf Happb
                 ltac:(lia) ltac:(rewrite <- ESfr; lia)). }
      pose proof (w4a_ba_aview W3 m1 phi (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) i HGb1
                    ltac:(rewrite (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j); lia)
                    ltac:(apply Hpvis; lia)) as HV.
      unfold ACtlCutP.RPA.cp_v, ACtlCutP.RPA.cp_b, ACtlCutP.RPA.cp_z. exact HV.
    - (* ---- the callee's post: rebuild the cut at the return pc ---- *)
      intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2 Hfrs2 Eab2 Hff Ha02 Hrec Hkept.
      assert (Hfrs2' : Reusable.YG01.frames S2 = own6 cx) by (rewrite Hfrs2; exact Hfrs).
      destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & Hwin2).
      pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ2 Hfrs2' (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
        as (_ & _ & _ & Hfrb2 & Hfrsh2).
      assert (Hin2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2))
        by (rewrite Eab2; exact Hin).
      destruct (w4a3_ap R regs2 HP2) as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G26 & G27).
      assert (R2 : getr regs2 2 = getr regs3 2) by (rewrite G2; exact E2).
      assert (R3 : getr regs2 3 = getr regs3 3) by (rewrite G3; exact E3).
      assert (R4 : getr regs2 4 = getr regs3 4) by (rewrite G4; exact E4).
      assert (R8 : getr regs2 8 = getr regs3 8) by (rewrite G8; exact E8).
      assert (R9 : getr regs2 9 = getr regs3 9) by (rewrite G9; exact E9).
      assert (R18 : getr regs2 18 = getr regs3 18) by (rewrite G18; exact E18).
      assert (R19 : getr regs2 19 = getr regs3 19) by (rewrite G19; exact E19).
      assert (R20 : getr regs2 20 = getr regs3 20) by (rewrite G20; exact E20).
      assert (R21 : getr regs2 21 = getr regs3 21) by (rewrite G21; exact E21).
      assert (R22 : getr regs2 22 = getr regs3 22) by (rewrite G22; exact E22).
      assert (R26 : getr regs2 26 = getr regs3 26) by (rewrite G26; exact E26).
      assert (R27 : getr regs2 27 = getr regs3 27) by (rewrite G27; exact E27).
      (* the kept transport, class by class *)
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
        kept_class B ly3 S3 (Reusable.YG0d.spZ R - ACtlCutP.RCP.REAC_CTRL_PARSE_K) (Reusable.YG0d.spZ R)
          (fun z : Z => fr + 176 <= z < fr + 176 + 36) a -> AGR m1 mem2 a).
      { intros a Ha Hv Hc.
        pose proof (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m1 mem2
                      (Reusable.YG0d.spZ R - ACtlCutP.RCP.REAC_CTRL_PARSE_K) (Reusable.YG0d.spZ R)
                      (fun z : Z => fr + 176 <= z < fr + 176 + 36) Hkept Hwle (Z_to_bv 64 a) Hv) as HH.
        rewrite w4a_wa_u in HH by lia. exact (HH Hc). }
      assert (AGH : forall x, A <= x -> x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
        AGR mem3 mem2 x).
      { intros x Hx1 Hx2 Hv.
        assert (G1 : AGR mem3 m1 x) by (apply AG31; lia).
        assert (GG : AGR m1 mem2 x)
          by (apply KEEP; [lia | exact Hv | left; split; [lia | rewrite ESP; lia]]).
        rewrite GG. exact G1. }
      assert (AGF : forall x, fr <= x < fr + 4096 -> ~ (fr + 176 <= x < fr + 212) -> AGR mem3 mem2 x).
      { intros x Hx Hn.
        assert (G1 : AGR mem3 m1 x).
        { apply AG31; [lia|]. intros Hc.
          exact (w4a3_sh_out fr fr 4096 x Happf Happf Hx ltac:(rewrite <- ESfr; lia)). }
        assert (GG : AGR m1 mem2 x).
        { apply KEEP; [lia | exact (proj1 (Hfrb x Hx))|].
          right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
          split; [left; unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng; cbn [fst snd]; rewrite Efa;
                  change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia|]. lia. }
        rewrite GG. exact G1. }
      assert (AGS : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
        ~ (ACtlCutP.Sfr fr + 22 <= x < ACtlCutP.Sfr fr + 27) -> AGR mem3 mem2 x).
      { intros x Hx Hn.
        assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
          by exact (proj1 (Hfrsh x ltac:(rewrite <- ESfr; lia))).
        assert (G1 : AGR mem3 m1 x) by (apply AG31; [lia | exact Hn]).
        assert (GG : AGR m1 mem2 x).
        { apply KEEP; [lia | exact Hv|].
          right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
          split; [right; unfold Reusable.YG0n.in_zr; cbn [fst snd]; rewrite Efa, Esh6;
                  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia|].
          intros Hc.
          exact (w4a3_sh_out fr (fr + 176) 36 x Happf Happ176 ltac:(lia) ltac:(rewrite <- ESfr; lia)). }
        rewrite GG. exact G1. }
      assert (AGB : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
        AGR mem3 mem2 x).
      { intros x Hx.
        assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false) by (apply Hpvis; lia).
        assert (G1 : AGR mem3 m1 x).
        { apply AG31; [lia|]. intros Hc.
          exact (w4a3_sh_out fr phi (Reusable.YG00.req_size (ACtlCutP.flen cx j)) x Happf Happb Hx
                   ltac:(rewrite <- ESfr; lia)). }
        assert (GG : AGR m1 mem2 x).
        { apply KEEP; [lia | exact Hv|].
          right; left. exists phi, (ACtlCutP.flen cx j), (x - phi). split; [exact Hin|].
          split; [lia|]. split; [lia|].
          pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi
                        (ACtlCutP.flen cx j) 6 (ACtlCut.c_fpos cx) HAR Hin Hin6) as Hsep.
          unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efa in Hsep.
          change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep. lia. }
        rewrite GG. exact G1. }
      assert (AGI : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
      { intros x Hx.
        pose proof Hx as Hx'. change ACtlCutP.KNA.KIND_NAME with 652672 in Hx'.
        assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
        { destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hvv).
          unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Hvv. apply Hvv. lia. }
        assert (G1 : AGR mem3 m1 x) by (apply AG31; lia).
        assert (GG : AGR m1 mem2 x).
        { apply KEEP; [lia | exact Hv|].
          right; right; left. split; [exact (w4a3_kn_img x Hx)|]. exact (ctl_kind_name_not_owned x Hx). }
        rewrite GG. exact G1. }
      (* the pieces of the cut body at mem2 *)
      assert (HB52 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4]).
      { apply (w4a_ba_keep m1 mem2 _ _ HB5). cbn [length]. intros x Hx.
        apply KEEP; [lia | exact (proj1 (Hfrsh x ltac:(rewrite <- ESfr; lia)))|].
        right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
        split; [right; unfold Reusable.YG0n.in_zr; cbn [fst snd]; rewrite Efa, Esh6;
                change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia|].
        intros Hc.
        exact (w4a3_sh_out fr (fr + 176) 36 x Happf Happ176 ltac:(lia) ltac:(rewrite <- ESfr; lia)). }
      assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
      { split; [lia|]. split; [rewrite HFBv; lia|].
        intros a Ha. rewrite HFBv in Ha.
        destruct (Hfrb2 a ltac:(lia)) as (_ & (bb & Hbb) & _).
        split.
        - unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate.
        - exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
      assert (HSH2 : exists shx, lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (ACtlCutP.Sfr fr) shx /\
                     length shx = Z.to_nat ACtlCutP.FRAME_SHADOW).
      { apply (w4a3_bytes_of_present mem2 (ACtlCutP.Sfr fr) ACtlCutP.FRAME_SHADOW);
          [lia | rewrite HFSv; lia | rewrite HFSv; lia |].
        intros a Ha. rewrite HFSv in Ha.
        exact (proj1 (proj2 (Hfrsh2 a ltac:(rewrite <- ESfr; lia)))). }
      assert (BFRAC : ACtlCutP.FRAC B cx fr fr regs2 mem2).
      { apply (w4a3_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC R2 R3 R4 R8 R9 R19 R26 HSH2).
        intros A' x HA' HA'r Hx.
        rewrite (w4a_rgv_inj _ _ _ _ HA' Hr9
                   HA'r ltac:(lia)) in Hx.
        destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
        - apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))].
        - apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))].
        - apply AGF; lia.
        - apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))].
        - apply AGF; lia. }
      assert (BLK : ACtlCutP.LK cx fr j regs2 mem2).
      { apply (w4a3_lk_move cx fr j regs3 regs2 mem3 mem2 A HLK
                 Hr9 ltac:(lia) ltac:(lia) R9 R27).
        - intros off x Hoff Hx. cbn [In] in Hoff.
          apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))].
        - intros x Hx. apply AGF; lia.
        - intros x Hx. destruct (HSHfr (x - fr)) as (Es & Hdd).
          replace (fr + (x - fr)) with x in Es by lia. rewrite Es.
          apply AGS; unfold ACtlCutP.fragb in Hx; lia.
        - intros x Hx. apply AGI; exact Hx.
        - exact (ctl_kind_name_addressable ly2 S2 W2 mem2 md2 HAR2).
        - exact HSTK2. }
      assert (Hsz : B.ACtlK.a_size (ACtlCutP.flen cx j) <= Reusable.YG00.req_size (ACtlCutP.flen cx j)).
      { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
        destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0) as [->|Hne]; lia. }
      assert (BHB : ACtlCutP.HB mem2 phi (ACtlCutP.flen cx j)).
      { split; [exact (proj1 HHB)|].
        exact (w4a_blk_addr ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) phi
                 (B.ACtlK.a_size (ACtlCutP.flen cx j)) HAR2 Hin2 ltac:(lia)
                 ltac:(unfold B.ACtlK.a_size; lia) ltac:(lia)). }
      assert (BFT : ACtlCutP.FTURN cx j phi regs2 mem2).
      { apply (w4a_fturn_move cx j phi regs3 regs2 mem3 mem2 A HFT
                 Hr9 ltac:(lia) ltac:(lia) R9).
        - intros x Hx. apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))].
        - intros x Hx. apply AGB. lia. }
      assert (BFSj : ACtlCutP.FSj cx fr j regs2 mem2).
      { apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj).
        - intros x Hx. apply AGF; lia.
        - intros x Hx. destruct (HSHfr (x - fr)) as (Es & Hdd).
          replace (fr + (x - fr)) with x in Es by lia. rewrite Es. apply AGS; lia. }
      assert (BREC : ACtlCutP.REC0 cx fr j mem2)
        by (apply (w4a_rec0_move cx fr j mem3 mem2 HREC); intros x Hx; apply AGF; lia).
      assert (BFPS : ACtlCutP.FPS cx fr j mem2).
      { split.
        - unfold ACtlCutP.pBb.
          apply (w4a_ba_of_aview W2 mem2 (fr + 176) (ACtlCutP.SM.t_B (ACtlCut.c_in cx) j)).
          + lia.
          + rewrite (B.Prog.Seg.F2.f2_tB_len (ACtlCut.c_in cx) j). lia.
          + intros i Hi. rewrite (B.Prog.Seg.F2.f2_tB_len (ACtlCut.c_in cx) j) in Hi.
            exact (proj1 (Hfrb2 (fr + 176 + Z.of_nat i) ltac:(lia))).
          + intros i Hi. rewrite (B.Prog.Seg.F2.f2_tB_len (ACtlCut.c_in cx) j) in Hi.
            unfold ACtlCutP.SM.t_B. exact (Hrec ltac:(lia) i ltac:(lia)).
        - exact (w4a3_fps_addr mem2 fr b0 b1 b2 b3 b4 Happf Hfr32 HB52 Eb0 Eb1 Eb2 Eb3 Eb4). }
      assert (BFC : ACtlCutP.FC cx fr j regs2 mem2).
      { apply (w4a_fc_move cx fr j regs3 regs2 mem3 mem2 A HFC
                 Hr9 ltac:(lia) ltac:(lia) R9 R20 R21).
        intros x Hx. apply AGH; [lia | lia | exact (proj1 (Hwin x ltac:(lia)))]. }
      assert (Ba0 : ACtlCut.a0v regs2 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j))
        by (unfold ACtlCut.a0v, ACtlCut.rgv, ACtlCutP.SM.t_k; exact Ha02).
      assert (Bperm : Permutation (Reusable.YG0d.ablocks B ly2 S2)
                        (ENTRYBL cx ++ [(phi, ACtlCutP.flen cx j)])) by (rewrite Eab2; exact Hperm).
      destruct Harm as [(Epcr & H50) | (Epcr & Hlt50)].
      + (* 50 <= len: the cut B81fbc_at at 0x81fbc *)
        assert (Hra : Reusable.YG0d.raZ R = 0x81fbc)
          by (unfold Reusable.YG0d.raZ; rewrite E1, Epcr, w4a_wa_u by lia; reflexivity).
        rewrite Hra.
        apply (Hbc cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2' HFA);
          [ unfold ix_cut, ACtlCutP.C_B81fbc_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk
          | | exact (w4a_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 k HB HJ2) ].
        unfold ix_cut, ACtlCutP.C_B81fbc_at. cbn [ACtlCut.cut_body]. split; [reflexivity|].
        cbv zeta. rewrite Ej.
        split; [exact BFRAC|].
        exists phi. split; [exact Bperm|]. split; [exact Hn26|]. split; [exact Hj|].
        split; [exact BHB|].
        split; [unfold ACtlCut.rgv; rewrite R18; exact H18|].
        split; [unfold ACtlCut.rgv; rewrite R20; exact H20|].
        split; [exact BFT|]. split; [exact BLK|]. split; [exact BFC|].
        split; [exact (w4a_rgv_move _ _ _ _ H22 R22)|].
        split; [exact BFSj|]. split; [exact BREC|]. split; [exact BFPS|].
        split; [exact Ba0|]. exact H50.
      + (* len < 50: the cut B82048_at at 0x82048 *)
        assert (Hra : Reusable.YG0d.raZ R = 0x82048)
          by (unfold Reusable.YG0d.raZ; rewrite E1, Epcr, w4a_wa_u by lia; reflexivity).
        rewrite Hra.
        apply (H48 cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2' HFA);
          [ unfold ix_cut, ACtlCutP.C_B82048_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk
          | | exact (w4a_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 k HB HJ2) ].
        unfold ix_cut, ACtlCutP.C_B82048_at. cbn [ACtlCut.cut_body]. split; [reflexivity|].
        cbv zeta. rewrite Ej.
        split; [exact BFRAC|].
        exists phi. split; [exact Bperm|]. split; [exact Hn26|]. split; [exact Hj|].
        split; [exact BHB|].
        split; [unfold ACtlCut.rgv; rewrite R18; exact H18|].
        split; [unfold ACtlCut.rgv; rewrite R20; exact H20|].
        split; [exact BFT|]. split; [exact BLK|].
        split; [exact (w4a_rgv_move _ _ _ _ H22 R22)|].
        split; [exact BFSj|]. split; [exact BREC|]. split; [exact BFPS|].
        split; [exact Ba0|]. exact Hlt50. }

  (* =======================================================================================================
     THE RUN 0x81f78 -> the reac_ctrl_parse entry: f3_head_F (T13 / T14), the five record-shadow stores
     (f2_st_noinv_F) and the four instructions to the call (f2_pcall_pre_F), in both arms of `bltu s4,50`.
     ======================================================================================================= *)
  assert (ER : Lib.Regs6ss.mkR_of regs3 =
    lib.Lib.Frame.mkR (getr regs3 1) (getr regs3 2) (getr regs3 3) (getr regs3 4) (getr regs3 5)
      (getr regs3 6) (getr regs3 7) (getr regs3 8) (Z_to_bv 64 A) (getr regs3 10) (getr regs3 11)
      (getr regs3 12) (getr regs3 13) (getr regs3 14) (getr regs3 15) (getr regs3 16) (getr regs3 17)
      (Z_to_bv 64 phi) (Z_to_bv 64 (ACtlCutP.Sfr fr)) (Z_to_bv 64 (ACtlCutP.flen cx j)) (getr regs3 21)
      (getr regs3 22) (getr regs3 23) (getr regs3 24) (getr regs3 25) (getr regs3 26) (getr regs3 27)
      (getr regs3 28) (getr regs3 29) (getr regs3 30) (getr regs3 31)).
  { unfold Lib.Regs6ss.mkR_of. rewrite <- Hr9, <- H18, <- Hr19, <- H20. reflexivity. }
  apply (w4_lift W3 0x81f78 regs3 mem3 md3
    (fun ms' => exists (pcr : Z) (R : bvmap 5 word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
       ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs
               (Z_to_bv 64 ACtlCutP.RCP.REAC_CTRL_PARSE) lib.Reusable.YK11.fp_csr None m1
               (lib.Reusable.YK11.seg_rom B.Img0.rsegs) /\
       ((pcr = 0x81fbc /\ 50 <= ACtlCutP.flen cx j) \/ (pcr = 0x82048 /\ ACtlCutP.flen cx j < 50)) /\
       getr R 1 = Z_to_bv 64 pcr /\
       getr R 2 = getr regs3 2 /\ getr R 3 = getr regs3 3 /\ getr R 4 = getr regs3 4 /\
       getr R 8 = getr regs3 8 /\ getr R 9 = getr regs3 9 /\
       getr R 10 = Z_to_bv 64 phi /\ getr R 11 = Z_to_bv 64 (ACtlCutP.flen cx j) /\
       getr R 12 = Z_to_bv 64 (fr + 176) /\
       getr R 18 = getr regs3 18 /\ getr R 19 = getr regs3 19 /\ getr R 20 = getr regs3 20 /\
       getr R 21 = getr regs3 21 /\ getr R 22 = getr regs3 22 /\ getr R 26 = getr regs3 26 /\
       getr R 27 = getr regs3 27 /\
       lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 22, ACtlCutP.Sfr fr + 27)] mem3 m1 /\
       lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (ACtlCutP.Sfr fr + 22) [b0; b1; b2; b3; b4] /\
       bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
    (POST cx)).
  - (* the footprint run *)
    rewrite ER.
    eapply Lib.ExecF.evtF_cut; [apply B.Prog.Seg.F3F.f3_head_F; [lia | lia | lia]|].
    intros ms1 (a0' & ->).
    assert (HRW : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
      (exists b, mem3 (Z_to_bv 64 a) = Some b) /\ wview B.Img0.rsegs mem3 (Z_to_bv 64 a) <> None).
    { intros a Ha. destruct (Hfrsh a ltac:(rewrite <- ESfr; lia)) as (_ & (bb & Hbb) & _).
      split; [exists bb; exact Hbb | unfold wview; rewrite Hbb; discriminate]. }
    assert (HRNG5 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 22) 5).
    { apply w4a_rng; [lia | lia|].
      intros a Ha. exact (proj1 (Hfrsh a ltac:(rewrite <- ESfr; lia))). }
    assert (HRNG280 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 280) 8).
    { apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]. }
    assert (Hsp280 : ACtlCutP.spill regs3 mem3 280 (fr + 176)).
    { pose proof HLK as (_ & _ & _ & HFLI).
      destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S280 & _). exact S280. }
    destruct Hsp280 as (A' & HA' & Hq280).
    pose proof Hq280 as (Hq280a & Hq280b & _). rewrite lib.Lib.Mem.length_le8 in Hq280b.
    change (Z.of_nat 8) with 8 in Hq280b.
    assert (HA'eq : A' = A).
    { assert (HAb : 0 <= A <= 2 ^ 47) by lia.
      unfold ACtlCut.rgv in HA'. rewrite Hr9 in HA'.
      apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'.
      unfold bv_wrap, bv_modulus in HA'. change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
      clear - HA' Hq280a Hq280b HAb. rewrite (Z.mod_small A) in HA' by lia.
      assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in HA', Hq280b.
      Z.div_mod_to_equations. lia. }
    subst A'.
    destruct (w4a_rw5 mem3 (ACtlCutP.Sfr fr + 22) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; apply HRW; lia)) as (junk & Hjunk).
    destruct (Z.ltb_spec (ACtlCutP.flen cx j) 50) as [Hlt|Hge]; cbv iota.
    + (* len < 50: the short record-shadow block 0x82020, ra = 0x82048 *)
      eapply Lib.ExecF.evtF_cut;
        [eapply B.Prog.Seg.F2F.f2_st_noinv_F with (junk := junk); [left; split; reflexivity | | ]|].
      * rewrite w4a_wa_u by lia. exact Hjunk.
      * rewrite w4a_wa_u by lia. exact HRNG5.
      * intros ms2 (a1' & m1 & bb0 & bb1 & bb2 & bb3 & bb4 & -> & MU1 & WM1 & HB5 & Eb0 & Eb1 & Eb2 & Eb3 & Eb4).
        rewrite (w4a_wa_u (ACtlCutP.Sfr fr) ltac:(lia)) in MU1, HB5.
        assert (Hq280' : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (A + 280)
                           (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))).
        { apply (w4a_ba_keep mem3 m1 _ _ Hq280). rewrite lib.Lib.Mem.length_le8.
          intros x Hx. apply (w4a_mrd_munch _ _ _ x MU1 ltac:(lia)).
          cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
        eapply Lib.ExecF.evtF_mono;
          [eapply B.Prog.Seg.F2F.f2_pcall_pre_F; [left; split; reflexivity | reflexivity | lia | lia | | ]|].
        -- pose proof (lib.Lib.Mem.bytes_at_ov_read B.Img0.rsegs m1 (A + 280)
                         (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))) 0 8 Hq280'
                         ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as HOV.
           assert (E8 : firstn 8 (skipn 0 (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))) =
                        lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))).
           { change (skipn 0 (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))))
               with (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))).
             apply firstn_all2. rewrite lib.Lib.Mem.length_le8. lia. }
           rewrite E8 in HOV. change (Z.of_nat 0) with 0 in HOV. rewrite Z.add_0_r in HOV. exact HOV.
        -- exact HRNG280.
        -- intros ms3 ->.
           exists 0x82048. eexists. exists m1, bb0, bb1, bb2, bb3, bb4.
           split; [reflexivity|].
           split; [right; split; [reflexivity | exact Hlt]|].
           split; [reflexivity|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [reflexivity|]. split; [symmetry; exact Hr9|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [symmetry; exact H18|]. split; [symmetry; exact Hr19|]. split; [symmetry; exact H20|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [exact MU1|]. split; [exact WM1|]. split; [exact HB5|].
           split; [exact Eb0|]. split; [exact Eb1|]. split; [exact Eb2|]. split; [exact Eb3|]. exact Eb4.
    + (* 50 <= len: T13 / T14 passed, the long record-shadow block 0x81f94, ra = 0x81fbc *)
      eapply Lib.ExecF.evtF_cut;
        [eapply B.Prog.Seg.F2F.f2_st_noinv_F with (junk := junk); [right; split; reflexivity | | ]|].
      * rewrite w4a_wa_u by lia. exact Hjunk.
      * rewrite w4a_wa_u by lia. exact HRNG5.
      * intros ms2 (a1' & m1 & bb0 & bb1 & bb2 & bb3 & bb4 & -> & MU1 & WM1 & HB5 & Eb0 & Eb1 & Eb2 & Eb3 & Eb4).
        rewrite (w4a_wa_u (ACtlCutP.Sfr fr) ltac:(lia)) in MU1, HB5.
        assert (Hq280' : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (A + 280)
                           (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))).
        { apply (w4a_ba_keep mem3 m1 _ _ Hq280). rewrite lib.Lib.Mem.length_le8.
          intros x Hx. apply (w4a_mrd_munch _ _ _ x MU1 ltac:(lia)).
          cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
        eapply Lib.ExecF.evtF_mono;
          [eapply B.Prog.Seg.F2F.f2_pcall_pre_F; [right; split; reflexivity | reflexivity | lia | lia | | ]|].
        -- pose proof (lib.Lib.Mem.bytes_at_ov_read B.Img0.rsegs m1 (A + 280)
                         (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))) 0 8 Hq280'
                         ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as HOV.
           assert (E8 : firstn 8 (skipn 0 (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176)))) =
                        lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))).
           { change (skipn 0 (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))))
               with (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 176))).
             apply firstn_all2. rewrite lib.Lib.Mem.length_le8. lia. }
           rewrite E8 in HOV. change (Z.of_nat 0) with 0 in HOV. rewrite Z.add_0_r in HOV. exact HOV.
        -- exact HRNG280.
        -- intros ms3 ->.
           exists 0x81fbc. eexists. exists m1, bb0, bb1, bb2, bb3, bb4.
           split; [reflexivity|].
           split; [left; split; [reflexivity | exact Hge]|].
           split; [reflexivity|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [reflexivity|]. split; [symmetry; exact Hr9|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [symmetry; exact H18|]. split; [symmetry; exact Hr19|]. split; [symmetry; exact H20|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [exact MU1|]. split; [exact WM1|]. split; [exact HB5|].
           split; [exact Eb0|]. split; [exact Eb1|]. split; [exact Eb2|]. split; [exact Eb3|]. exact Eb4.
  - (* the lift's continuation: the shared parse call *)
    intros ms' md' (pcr & R & m1 & b0 & b1 & b2 & b3 & b4 & -> & Harm & E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 &
      E12 & E18 & E19 & E20 & E21 & E22 & E26 & E27 & MU1 & WM1 & HB5 & Eb0 & Eb1 & Eb2 & Eb3 & Eb4) Hhid Hsame.
    exact (HKc pcr R m1 b0 b1 b2 b3 b4 md' Harm E1 E2 E3 E4 E8 E9 E10 E11 E12 E18 E19 E20 E21 E22 E26 E27
             MU1 WM1 HB5 Eb0 Eb1 Eb2 Eb3 Eb4 Hhid Hsame).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81fbc_at j (0x81fbc, own6, k <= 14+2j+1) --S_F4--> B82098_at j.
   S_F4 (Seg/F4.v seg_F4 :183, an inline stretch): s8 = t_k j; T15 and the checked read of Phi[12]; byte 12 = 0x88:
   T16 and Phi[13], [A + 272] := (Phi[13] = 0x19); else [A + 272] := 0; then the block-sum loop registers. *)
Lemma seg_F4 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82098_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B81fbc_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL.
  intros POST j H98 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B81fbc_at in Hk, HBODY, HJ, Hfr, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfr, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (HFRAC & phi & Hperm & Hn26 & Hj & HHB & H18 & H20 & HFT & HLK & HFC & H22 & HFSj & HREC & HFPS &
    Ha0 & H50).
  (* the journal's facts, the frame, the spill base *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & _).
  pose proof (w4a_spZ regs3) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  (* the turn block *)
  assert (Hin : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hn0 & Hreq & Hpvis & Hpshvis).
  (* the record bytes 12 / 13 and their shadow *)
  pose proof (B.Prog.SlotInv.t_g_of_phi mem3 phi (ACtlCut.c_in cx) j (proj1 (proj2 (proj2 HFT))) H50) as HGb.
  pose proof (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j) as Hglen.
  pose proof (w4a_ba_nth mem3 phi _ 12 ACtlCutP.RPA.cp_z HGb ltac:(rewrite Hglen; lia)) as Hb12.
  pose proof (w4a_ba_nth mem3 phi _ 13 ACtlCutP.RPA.cp_z HGb ltac:(rewrite Hglen; lia)) as Hb13.
  change (Z.of_nat 12) with 12 in Hb12. change (Z.of_nat 13) with 13 in Hb13.
  pose proof (B.Prog.Seg.F4.f4_sh_at mem3 phi (flen cx j) 12 (proj2 HHB) H50 ltac:(lia)) as Hsh12.
  pose proof (B.Prog.Seg.F4.f4_sh_at mem3 phi (flen cx j) 13 (proj2 HHB) H50 ltac:(lia)) as Hsh13.
  assert (Hphib : 0 < phi /\ phi + 64 <= 2 ^ 64) by lia.
  assert (HW272 : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (A + 272) 8)
    by (apply (w4a_wr_win _ _ _ _ _ _ _ _ _ _ HJ); lia).
  pose proof (lib.Lib.Mem.wr_at_store_ok _ _ _ _ 0 8 HW272 ltac:(lia) ltac:(lia)) as HS272.
  rewrite Z.add_0_r in HS272.
  assert (Rsh : forall x, phi <= x < phi + Reusable.YG00.req_size (flen cx j) ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Z.shiftr x 3 + B.AsanRT.ASAN_K) 1).
  { intros x Hx. rewrite w4a_shr3 by lia. pose proof (Hpshvis x Hx) as Hv.
    pose proof (w4a_sh_lt x (2 ^ 47) ltac:(lia) ltac:(lia)) as Hb.
    apply w4a_rng; [lia | lia | intros a Ha; replace a with (B.AsanRT.shadow_addr x) by lia; exact Hv]. }
  assert (Rby : forall x, phi <= x < phi + Reusable.YG00.req_size (flen cx j) ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) x 1).
  { intros x Hx. apply w4a_rng; [lia | lia | intros a Ha; apply Hpvis; lia]. }
  assert (R272 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 272) 8).
  { apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]. }
  pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ Hfr (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
    as (Hfr32' & Hfr4096 & Hfrceil & _ & _).
  assert (HA34 : 2 ^ 34 <= A) by lia.
  assert (Hsfr : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 4096 <= A).
  { unfold ACtlCutP.Sfr. pose proof (w4a_sh_lt fr (A - 4096) ltac:(lia) ltac:(lia)). lia. }
  (* the continuation at 0x82098, shared by both arms *)
  assert (HKc : forall (v : Z) (R : bvmap 5 word) md',
    v = ACtlCutP.SM.b2z (ACtlCutP.SM.t_8819 (ACtlCut.c_in cx) j) ->
    getr R 2 = getr regs3 2 -> getr R 3 = getr regs3 3 -> getr R 4 = getr regs3 4 ->
    getr R 8 = getr regs3 8 -> getr R 9 = getr regs3 9 -> getr R 18 = getr regs3 18 ->
    getr R 19 = getr regs3 19 -> getr R 20 = getr regs3 20 -> getr R 22 = getr regs3 22 ->
    getr R 26 = getr regs3 26 -> getr R 27 = getr regs3 27 ->
    getr R 24 = Z_to_bv 64 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j) -> getr R 10 = Z_to_bv 64 (phi + 18) ->
    getr R 11 = Z_to_bv 64 0 -> getr R 12 = Z_to_bv 64 (phi + 18) ->
    getr R 13 = Z_to_bv 64 (- (phi + 18)) -> getr R 14 = Z_to_bv 64 32 ->
    getr R 17 = Z_to_bv 64 32 -> getr R 5 = Z_to_bv 64 (phi + 18) ->
    (forall x : word, Reusable.YA0n.w_H W3 x = true ->
       write_to_mem mem3 (lib.Lib.Mem.wa (A + 272)) (lib.Lib.Mem.le8 (Z_to_bv 64 v)) x = mem3 x) ->
    Reusable.YK04.same_but_materialized md3 md' ->
    Reusable.YA0n.SRr segs W3
      (Reusable.YG0d.cfg_at segs 0x82098 R
         (write_to_mem mem3 (lib.Lib.Mem.wa (A + 272)) (lib.Lib.Mem.le8 (Z_to_bv 64 v))) md') (POST cx)).
  { intros v R md' Ev E2 E3 E4 E8 E9 E18 E19 E20 E22 E26 E27 E24 E10 E11 E12 E13 E14 E17 E5 Hhid Hsame.
    set (mem' := write_to_mem mem3 (lib.Lib.Mem.wa (A + 272)) (lib.Lib.Mem.le8 (Z_to_bv 64 v))) in *.
    assert (MU : lib.Lib.Frame.munch [(A + 272, A + 280)] mem3 mem').
    { subst mem'. apply lib.Lib.Frame.munch_write; [apply lib.Lib.Frame.munch_refl | lia | rewrite lib.Lib.Mem.length_le8; lia
        | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]. }
    assert (WM : lib.Lib.Frame.wmono B.Img0.rsegs mem3 mem')
      by (subst mem'; apply lib.Lib.Frame.wmono_write; apply lib.Lib.Frame.wmono_refl).
    assert (AG : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 272 <= x < A + 280) -> AGR mem3 mem' x).
    { intros x Hx Hn. apply (w4a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside]. split; [exact Hn | exact I]. }
    assert (AGS : forall x, 0 <= x <= A -> AGR mem3 mem' (B.AsanRT.shadow_addr x)).
    { intros x Hx. pose proof (w4a_sh_lt x A Hx HA34). apply AG; lia. }
    assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 mem' md' k).
    { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU WM Hhid Hsame).
      intros a Ha. apply w4a_not_out1 in Ha.
      split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia. }
    pose proof (proj1 (w4a_aj_bits _ _ _ _ _ _ _ _ HJ')) as HAR'.
    apply (H98 cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB HJ' Hfr HFA);
      [unfold ix_cut, ACtlCutP.C_B82098_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk | |
       exact (w4a_ctlrt _ _ _ _ _ _ _ _ HB HJ')].
    unfold ix_cut, ACtlCutP.C_B82098_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
    split.
    { apply (w4a_frac_move cx fr fr regs3 R mem3 mem' HFRAC E2 E3 E4 E8 E9 E19 E26).
      intros A' x HA' HA'r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA' Hr9 HA'r ltac:(lia)) in Hx.
      apply AG; lia. }
    exists phi.
    split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj|].
    split; [apply (w4a_hb_move mem3 mem' phi _ HHB); intros x Hx; apply AGS; unfold B.ACtlK.a_size in Hx; lia|].
    split; [exact (w4a_rgv_move _ _ _ _ H18 E18)|]. split; [exact (w4a_rgv_move _ _ _ _ H20 E20)|].
    split.
    { apply (w4a_fturn_move cx j phi regs3 R mem3 mem' A HFT Hr9 ltac:(lia) ltac:(lia) E9);
        intros x Hx; apply AG; unfold ACtlCutP.flen in *; lia. }
    split.
    { pose proof HLK as (_ & _ & _ & HFLI).
      apply (w4a_lk_move cx fr j regs3 R mem3 mem' A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
      - intros off x Hoff Hx. cbn [In] in Hoff. apply AG; lia.
      - intros x Hx. apply AG; lia.
      - intros x Hx. apply AGS. unfold ACtlCutP.fragb in Hx. lia.
      - intros x Hx. change ACtlCutP.KNA.KIND_NAME with 652672 in Hx. split; [apply AG; lia | apply AGS; lia].
      - apply (w4a_stk_keep mem3 mem' _ _ (w4a_fli_stk _ _ _ _ HFLI) WM). intros x Hx. apply AG; lia. }
    split; [exact (w4a_rgv_move _ _ _ _ H22 E22)|].
    split; [apply (w4a_fsj_move cx fr j regs3 R mem3 mem' HFSj); intros x Hx; [apply AG; lia | apply AGS; lia]|].
    split; [apply (w4a_rec0_move cx fr j mem3 mem' HREC); intros x Hx; apply AG; lia|].
    split; [apply (w4a_fps_move cx fr j mem3 mem' HFPS); intros x Hx; split; [apply AG; lia | apply AGS; lia]|].
    split.
    { exists A. split; [exact (w4a_rgv_move _ _ _ _ Hr9 E9)|]. unfold ACtlCutP.q64. rewrite <- Ev. subst mem'.
      apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
    split; [exact H50|].
    split; [exact E24|]. split; [exact E10|]. split; [exact E11|]. split; [exact E12|].
    split; [exact E13|]. split; [exact E14|]. split; [exact E17|]. exact E5. }

  set (tg := ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) in *.
  pose proof (B.Prog.Seg.F5.c_byte_range (nth 12 tg ACtlCutP.RPA.cp_z)) as Hv12.
  pose proof (B.Prog.Seg.F5.c_byte_range (nth 13 tg ACtlCutP.RPA.cp_z)) as Hv13.
  assert (Hbig : ACtlCutP.SM.t_big (ACtlCut.c_in cx) j = true)
    by (unfold ACtlCutP.SM.t_big; apply Z.leb_le; exact H50).
  destruct (Z.eq_dec (ACtlCutP.RPA.cp_v tg 12) 136) as [H12eq|H12ne].
  - (* record byte 12 = 0x88 *)
    apply (w4_lift W3 0x81fbc regs3 mem3 md3 _ (POST cx)
      (B.Prog.Seg.F4F.seg_F4_eq88_F lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
         (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3 mem3 A phi (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j)
         (nth 12 tg ACtlCutP.RPA.cp_z) (nth 13 tg ACtlCutP.RPA.cp_z) Ha0 H18 Hr9 Hr26 Hphib Hsh12 Hb12 H12eq
         Hsh13 Hb13 Hv13 HS272 (Rsh (phi + 12) ltac:(lia)) (Rby (phi + 12) ltac:(lia))
         (Rsh (phi + 13) ltac:(lia)) (Rby (phi + 13) ltac:(lia)) R272)).
    intros ms' md' (R & pc' & mem' & -> & (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E26 & E27 &
      E24 & E10 & E11 & E12 & E13 & E14 & E17 & E5)) Hhid Hsame.
    apply (HKc (if bv_unsigned (nth 13 tg ACtlCutP.RPA.cp_z) =? 25 then 1 else 0) R md'); try assumption.
    unfold ACtlCutP.SM.b2z, ACtlCutP.SM.t_8819. rewrite Hbig. fold tg.
    replace (ACtlCutP.RPA.cp_v tg 12 =? 0x88) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
    reflexivity.
  - (* record byte 12 <> 0x88 *)
    apply (w4_lift W3 0x81fbc regs3 mem3 md3 _ (POST cx)
      (B.Prog.Seg.F4F.seg_F4_ne88_F lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
         (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3 mem3 A phi (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j)
         (nth 12 tg ACtlCutP.RPA.cp_z) Ha0 H18 Hr9 Hr26 Hphib Hsh12 Hb12 H12ne Hv12 HS272
         (Rsh (phi + 12) ltac:(lia)) (Rby (phi + 12) ltac:(lia)) R272)).
    intros ms' md' (R & pc' & mem' & -> & (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E26 & E27 &
      E24 & E10 & E11 & E12 & E13 & E14 & E17 & E5)) Hhid Hsame.
    apply (HKc 0 R md'); try assumption.
    unfold ACtlCutP.SM.b2z, ACtlCutP.SM.t_8819. fold tg.
    replace (ACtlCutP.RPA.cp_v tg 12 =? 0x88) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
    rewrite andb_false_r, andb_false_l. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Local lemmas of seg_F5 (prefix w4a5_). *)

(* The image segment that holds the KIND_NAME table (lib/B/ACtl.v's relro_img_CtrlB text, at this range). *)
Lemma w4a5_img : forall a, 0x9f000 <= a < 0x9f000 + 0x3000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold Reusable.YG0d.in_img.
  assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs) 2 =
               Some (0x9f000, 0x3000)) by (vm_compute; reflexivity).
  rewrite nth_error_map in Hb. destruct (nth_error segs 2) as [sg|] eqn:E; [|discriminate Hb].
  cbn in Hb. injection Hb as H1 H2.
  exists sg. split; [exact (nth_error_In _ 2 E) | rewrite H1, H2; lia].
Qed.

(* mkR_of with the three registers c_pre_F pins (sp, s2, s4) in the shape its start state wants. *)
Lemma w4a5_mkR_at : forall (R : bvmap 5 word) (s2 s18 s20 : Z),
  getr R 2 = Z_to_bv 64 s2 -> getr R 18 = Z_to_bv 64 s18 -> getr R 20 = Z_to_bv 64 s20 ->
  Lib.Regs6ss.mkR_of R =
  lib.Lib.Frame.mkR (getr R 1) (Z_to_bv 64 s2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7)
    (getr R 8) (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15)
    (getr R 16) (getr R 17) (Z_to_bv 64 s18) (getr R 19) (Z_to_bv 64 s20) (getr R 21) (getr R 22)
    (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
    (getr R 31).
Proof. intros R s2 s18 s20 E2 E18 E20. rewrite <- E2, <- E18, <- E20. reflexivity. Qed.

Lemma w4a5_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) (z : Z),
  Reusable.YG0d.aregs_preserved regs regs' -> r = Z_to_bv 5 z -> Reusable.YG0d.acallee_saved z ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r z H -> Hc. exact (H z Hc). Qed.

Lemma w4a5_shadow_add : forall p d, p mod 8 = 0 -> 0 <= d ->
  B.AsanRT.shadow_addr (p + d) = B.AsanRT.shadow_addr p + d / 8.
Proof.
  intros p d Hm Hd. unfold B.AsanRT.shadow_addr.
  assert (E : (p + d) / 8 = p / 8 + d / 8) by (Z.div_mod_to_equations; lia).
  lia.
Qed.

Lemma w4a5_out4 : forall l1 h1 l2 h2 l3 h3 l4 h4 a,
  ~ (l1 <= a < h1) -> ~ (l2 <= a < h2) -> ~ (l3 <= a < h3) -> ~ (l4 <= a < h4) ->
  lib.Lib.Frame.outside [(l1, h1); (l2, h2); (l3, h3); (l4, h4)] a.
Proof.
  intros l1 h1 l2 h2 l3 h3 l4 h4 a H1 H2 H3 H4. cbn [lib.Lib.Frame.outside].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact I].
Qed.

(* The frame's bytes are present, so the frame window is `stk` (FLI's conjunct) at the post-call memory. *)
Lemma w4a5_stk_of_pres : forall (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> exists b, m (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.stk segs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (b & Hb). unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma w4a5_q64_of_spill : forall regs m off v A,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A Hr9 HA0 HA1 Hoff (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    unfold ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'.
    apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
    clear - HA' Hq0 Hq1 HA0 HA1 Hoff. rewrite (Z.mod_small A) in HA' by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

Lemma w4a5_spill_of_q64 : forall regs m off v A,
  ACtlCut.rgv regs 9 A -> ACtlCutP.q64 m (A + off) v -> ACtlCutP.spill regs m off v.
Proof. intros regs m off v A H9 Hq. exists A. split; [exact H9 | exact Hq]. Qed.

(* The parse struct of a short frame is 36 zero bytes, so its kind word is 0. *)
Lemma w4a5_u32_of_rep : forall m a,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (repeat ACtlCutP.RPA.cp_z 36) -> ACtlCutP.u32 m a 0.
Proof.
  intros m a (H0 & H1 & H). unfold ACtlCutP.u32, ACtlCutP.MEM.bytes_at.
  rewrite repeat_length in H1. rewrite lib.Lib.Mem.length_le4.
  split; [exact H0|]. split; [cbn [Z.of_nat] in H1 |- *; lia|].
  intros i Hi. transitivity (nth_error (repeat ACtlCutP.RPA.cp_z 36) i).
  - exact (H i ltac:(rewrite repeat_length; lia)).
  - do 4 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(* w4a_fli_move / w4a_lk_move with KNT supplied at the post memory (the KIND_NAME shadow is not kept by a
   call's write-set argument: its `addressable` comes from ctl_kind_name_addressable on the post-call AR). *)
Lemma w4a5_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.KNT m' ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS HKNT HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & _ & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split; [exact HKNT|].
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.

Lemma w4a5_lk_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off (240 :: [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304]) -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.KNT m' ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS HKNT HSTK.
  split; [exact Hj|].
  split; [apply (w4a_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply (KA 240 x); [left; reflexivity | exact Hx]|].
  split; [exact (w4a_our_move cx fr m m' HOUR KF)|].
  apply (w4a5_fli_move cx fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27); [|exact KS | exact HKNT | exact HSTK].
  intros off x Hoff Hx. apply (KA off x); [right; exact Hoff | exact Hx].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82048_at j (0x82048, own6, k <= 14+2j+1) --S_F5--> B8215c_at j.
   S_F5 (Seg/F5.v seg_F5 :2020): `bnez a0,0x82fa4` (not taken), the short-frame spills [A+184] = [A+272] = [A+312] = 0,
   s8 = s9 = 0, [A + 248] = 1, then the shared parse block 0x8214c: reac_ctrl_parse(Phi, len, 0) @0x82158 returning at
   0x8215c. *)
Lemma seg_F5 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8215c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82048_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx ctl_kind_name_addressable
            ctl_kind_name_not_owned LAWS segs_low TFIB_SYMS RELRO_IMG RO_OFL PARSE.
  intros POST j H5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B82048_at in Hk, HBODY, HJ, Hfr, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfr, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (HFRAC & phi & Hperm & Hn26 & Hj & HHB & H18 & H20 & HFT & HLK & H22 & HFSj & HREC & HFPS &
    Ha0 & H50).
  (* ---- the journal's facts, the frame, the spill base ---- *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & Hfa & HA448 & HS4 & HAPP & Q336 & Q48 & Q40 & Qh1 & Qh2 & (shb & Hshb & Hshl) & Hsaved & Qtr).
  pose proof (w4a_spZ regs3) as Hsp. pose proof (w4a_spZ (ACtlCut.c_regs cx)) as Hcs.
  change (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) with (ACtlCut.c_sp cx) in Hcs.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (Hfreq : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by exact (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
  destruct (w4a_frame _ _ _ _ _ _ _ _ HJ Hfr Hfreq) as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  assert (HA34 : 2 ^ 34 <= A) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { pose proof HJ as (_ & Hly & _). rewrite Hfreq. unfold Reusable.YG0f.frame_addr.
    destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Esh : Reusable.YG0f.shadow_addr fr = B.AsanRT.shadow_addr fr)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (Hsfr : 0 <= B.AsanRT.shadow_addr fr /\ B.AsanRT.shadow_addr fr + 4096 <= A).
  { pose proof (w4a_sh_lt fr (A - 4096) ltac:(lia) ltac:(lia)). lia. }
  assert (HSfrlo : 2147450880 <= B.AsanRT.shadow_addr fr).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    assert (Hd : 0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  (* ---- the turn block ---- *)
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hn0 & Hreq & Hpvis & Hpshvis).
  destruct (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as (Hrq1 & Hrq2).
  (* ---- the model's values on the short-frame arm ---- *)
  assert (Hlen50 : ACtlCutP.SM.t_len (ACtlCut.c_in cx) j < 50) by exact H50.
  assert (Hlen0 : 0 <= ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) by exact Hn0.
  assert (Hbig : ACtlCutP.SM.t_big (ACtlCut.c_in cx) j = false)
    by (unfold ACtlCutP.SM.t_big; apply Z.leb_gt; lia).
  assert (Htk : ACtlCutP.SM.t_k (ACtlCut.c_in cx) j = 0).
  { unfold ACtlCutP.SM.t_k. apply (proj2 (ACtlCutP.RPA.ctrlparse_none _ _)).
    intros (HH & _). lia. }
  assert (Hsum : ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) j = false)
    by (unfold ACtlCutP.SM.t_sum_ok; rewrite Hbig; reflexivity).
  assert (Htf : ACtlCutP.SM.t_tfill (ACtlCut.c_in cx) j = false)
    by (unfold ACtlCutP.SM.t_tfill; rewrite Hbig; reflexivity).
  assert (H8819 : ACtlCutP.SM.t_8819 (ACtlCut.c_in cx) j = false)
    by (unfold ACtlCutP.SM.t_8819; rewrite Hbig; reflexivity).
  assert (EB : ACtlCutP.SM.t_B (ACtlCut.c_in cx) j = repeat ACtlCutP.RPA.cp_z 36).
  { unfold ACtlCutP.SM.t_B. apply ACtlCutP.RPA.ctrlparse_bytes_none. unfold ACtlCutP.RPA.cp_hdr.
    replace (50 <=? ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) with false
      by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  (* ---- run 1: 0x82048 -> 0x8214c (the four short-frame spills) ---- *)
  assert (Ha00 : ACtlCut.rgv regs3 10 0) by (unfold ACtlCut.a0v in Ha0; rewrite Htk in Ha0; exact Ha0).
  assert (HW184 : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (A + 184) 136)
    by (apply (w4a_wr_win _ _ _ _ _ _ _ _ _ _ HJ); lia).
  assert (Rsp : forall off, 184 <= off -> off + 8 <= 320 ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + off) 8).
  { intros off Ho1 Ho2. apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]. }
  apply (w4_lift W3 0x82048 regs3 mem3 md3 _ (POST cx)
    (B.Prog.Seg.F5F.seg_F5_F lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
       (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3 mem3 A Ha00 Hr9 ltac:(lia) ltac:(lia) HW184
       (Rsp 184 ltac:(lia) ltac:(lia)) (Rsp 272 ltac:(lia) ltac:(lia))
       (Rsp 312 ltac:(lia) ltac:(lia)) (Rsp 248 ltac:(lia) ltac:(lia)))).
  intros ms' md' (R & pc' & mem1 & -> & -> & Hm1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E26 & E27 &
    E24 & E25) Hhid Hsame.
  (* the run's frame: one munch for the journal, one for the four words *)
  assert (MU1 : lib.Lib.Frame.munch [(A + 184, A + 320)] mem3 mem1).
  { rewrite Hm1.
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_refl. }
  assert (MU4 : lib.Lib.Frame.munch
            [(A + 184, A + 192); (A + 272, A + 280); (A + 312, A + 320); (A + 248, A + 256)] mem3 mem1).
  { rewrite Hm1.
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_write; [|lia|rewrite lib.Lib.Mem.length_le8; lia|cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Frame.munch_refl. }
  assert (WM : lib.Lib.Frame.wmono B.Img0.rsegs mem3 mem1).
  { rewrite Hm1. repeat apply lib.Lib.Frame.wmono_write. apply lib.Lib.Frame.wmono_refl. }
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem1 md' k).
  { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU1 WM Hhid Hsame).
    intros a Ha. apply w4a_not_out1 in Ha.
    split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia. }
  assert (AG1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 184 <= x < A + 192) -> ~ (A + 272 <= x < A + 280) ->
     ~ (A + 312 <= x < A + 320) -> ~ (A + 248 <= x < A + 256) -> AGR mem3 mem1 x).
  { intros x Hx N1 N2 N3 N4. apply (w4a_mrd_munch _ _ _ x MU4 Hx). apply w4a5_out4; assumption. }
  (* the four written words at mem1 *)
  assert (Q184 : ACtlCutP.q64 mem1 (A + 184) 0).
  { unfold ACtlCutP.q64. rewrite Hm1.
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (Q272 : ACtlCutP.q64 mem1 (A + 272) 0).
  { unfold ACtlCutP.q64. rewrite Hm1.
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (Q312 : ACtlCutP.q64 mem1 (A + 312) 0).
  { unfold ACtlCutP.q64. rewrite Hm1.
    apply lib.Lib.Mem.bytes_at_write_other; [|lia|rewrite lib.Lib.Mem.length_le8; lia|rewrite !lib.Lib.Mem.length_le8; lia].
    apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (Q248 : ACtlCutP.q64 mem1 (A + 248) 1).
  { unfold ACtlCutP.q64. rewrite Hm1.
    apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  (* ---- run 2: 0x8214c -> reac_ctrl_parse's entry ---- *)
  assert (R2 : getr R 2 = Z_to_bv 64 sp) by (etransitivity; [exact E2 | exact Hr2]).
  assert (R18 : getr R 18 = Z_to_bv 64 phi) by (etransitivity; [exact E18 | exact H18]).
  assert (R20 : getr R 20 = Z_to_bv 64 (ACtlCutP.flen cx j)) by (etransitivity; [exact E20 | exact H20]).
  eapply (w4_lift W3 0x8214c R mem1 md' _ (POST cx)).
  { rewrite (w4a5_mkR_at R sp phi (ACtlCutP.flen cx j) R2 R18 R20). apply B.Prog.Seg.F5F.c_pre_F. }
  intros ms'' md'' -> Hhid2 Hsame2.
  match goal with
  | |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?RR _ _ _ _ _ _) _) _ => set (regs1 := RR)
  end.
  assert (HJ2 : AJ cx (own6 cx) ly3 S3 W3 mem1 md'' k).
  { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ [] HJ1 (lib.Lib.Frame.munch_refl _ _)
            (lib.Lib.Frame.wmono_refl _ _) (fun x _ => eq_refl) Hsame2).
    intros a Ha. exfalso. exact (Ha I). }
  assert (Esp1 : Reusable.YG0d.spZ regs1 = sp).
  { unfold Reusable.YG0d.spZ. replace (getr regs1 2) with (Z_to_bv 64 sp) by reflexivity.
    apply w4a_wa_u. lia. }
  assert (Era1 : Reusable.YG0d.raZ regs1 = 0x8215c).
  { unfold Reusable.YG0d.raZ. replace (getr regs1 1) with (Z_to_bv 64 0x8215c) by reflexivity.
    apply w4a_wa_u. lia. }
  assert (HK8800 : ACtlCutP.RCP.REAC_CTRL_PARSE_K = 8800) by reflexivity.
  pose proof (proj1 (proj1 HB)) as HAFN.
  destruct HAFN as (_ & _ & _ & Hgp & Htp & _).
  (* ---- the cut callee ---- *)
  apply (w4a_parse Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
    (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 mem1 md'' k regs1
    phi (ACtlCutP.flen cx j) 0 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) (POST cx)).
  - exact HJ2.
  - exact (w4a_arodata_cut cx (own6 cx) ly3 S3 W3 mem1 md'' k HB HJ2).
  - replace (getr regs1 1) with (Z_to_bv 64 0x8215c) by reflexivity.
    apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
  - rewrite Era1. lia.
  - replace (getr regs1 3) with (getr R 3) by reflexivity.
    etransitivity; [exact E3|]. etransitivity; [exact Hr3 | exact Hgp].
  - replace (getr regs1 4) with (getr R 4) by reflexivity.
    etransitivity; [exact E4 | exact Hr4].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite Esp1. exact Hsp16.
  - rewrite Esp1, HK8800. lia.
  - rewrite Esp1. lia.
  - rewrite Hfr. unfold ACtlCut.own6.
    replace (Reusable.YG01.count_cid 1 [(6, ACtlCut.c_fpos cx)]) with 0 by reflexivity.
    assert (HFS1 : Reusable.YG00.fs_frames 1 = 8192) by (vm_compute; reflexivity). lia.
  - intros HH. exfalso. lia.
  - intros HH. exfalso. exact (HH eq_refl).
  - intros HH. exfalso. exact (HH eq_refl).
  - exact (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j).
  - intros HH. exfalso. lia.
  - (* ---- the call's continuation: the cut at 0x8215c ---- *)
    intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ3 HPRES Hfrs2 Hab2 Hff Ha02 Hrec Hkept.
    rewrite Esp1, HK8800 in Hkept.
    destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ3) as (HAR2 & _ & _ & Hwin2).
    assert (Hfrs2' : Reusable.YG01.frames S2 = own6 cx) by (rewrite Hfrs2; exact Hfr).
    assert (Hin2 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hab2; exact Hin).
    destruct (w4a_frame _ _ _ _ _ _ _ _ HJ3 Hfrs2' Hfreq) as (_ & _ & _ & Hfrb2 & _).
    (* the kept classes of this call *)
    assert (KHI : forall x, sp <= x -> x < ACtlCut.c_sp cx -> AGR mem1 mem2 x).
    { intros x Hx1 Hx2.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x));
        [exact (proj1 (Hwin x ltac:(lia)))|].
      left. rewrite w4a_wa_u by lia. lia. }
    assert (KFR : forall x, fr <= x < fr + 4096 -> AGR mem1 mem2 x).
    { intros x Hx.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x));
        [exact (proj1 (Hfrb x Hx))|].
      right. right. right. rewrite w4a_wa_u by lia.
      exists 6, (ACtlCut.c_fpos cx). split; [rewrite Hfr; left; reflexivity|].
      split; [left; unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng; cbn [fst snd]; rewrite Efa, E6; lia|].
      cbv beta. lia. }
    assert (KFS : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 -> AGR mem1 mem2 x).
    { intros x Hx.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x));
        [exact (proj1 (Hfrsh x Hx))|].
      right. right. right. rewrite w4a_wa_u by lia.
      exists 6, (ACtlCut.c_fpos cx). split; [rewrite Hfr; left; reflexivity|].
      split; [right; unfold Reusable.YG0n.in_zr; cbn [fst snd]; rewrite Efa, E6, Esh;
              change (4096 / 8) with 512; lia|].
      cbv beta. lia. }
    assert (KBLK : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) -> AGR mem1 mem2 x).
    { intros x Hx.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x));
        [exact (Hpvis x Hx)|].
      right. left. rewrite w4a_wa_u by lia.
      exists phi, (ACtlCutP.flen cx j), (x - phi).
      split; [exact Hin|]. split; [lia|]. split; [lia|]. cbv beta. lia. }
    assert (KIMG : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem1 mem2 x).
    { intros x Hx. change ACtlCutP.KNA.KIND_NAME with 652672 in Hx.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ Hkept Hwle (Z_to_bv 64 x));
        [exact (proj2 (proj2 (B.ProgBridge.img_vis_W W3)) x
                  ltac:(unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia))|].
      right. right. left. rewrite w4a_wa_u by lia.
      destruct (ctl_kind_name_not_owned x ltac:(change ACtlCutP.KNA.KIND_NAME with 652672; lia)) as (Hno & Hne).
      split; [apply w4a5_img; lia|]. split; [exact Hno | exact Hne]. }
    (* composed with the run's frame *)
    assert (AGH : forall x, sp <= x -> x < ACtlCut.c_sp cx ->
       ~ (A + 184 <= x < A + 192) -> ~ (A + 272 <= x < A + 280) -> ~ (A + 312 <= x < A + 320) ->
       ~ (A + 248 <= x < A + 256) -> AGR mem3 mem2 x).
    { intros x H1 H2 N1 N2 N3 N4. exact (eq_trans (KHI x H1 H2) (AG1 x ltac:(lia) N1 N2 N3 N4)). }
    assert (AGF : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 x).
    { intros x Hx.
      exact (eq_trans (KFR x Hx) (AG1 x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
    assert (AGS : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 -> AGR mem3 mem2 x).
    { intros x Hx.
      exact (eq_trans (KFS x Hx) (AG1 x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
    assert (AGFS : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 (B.AsanRT.shadow_addr x)).
    { intros x Hx. apply AGS.
      replace x with (fr + (x - fr)) by lia. rewrite w4a5_shadow_add by lia.
      pose proof (Z.div_pos (x - fr) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (x - fr) 4095 8 ltac:(lia) ltac:(lia)).
      assert (E4095 : 4095 / 8 = 511) by reflexivity. lia. }
    assert (AGB : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) -> AGR mem3 mem2 x).
    { intros x Hx.
      exact (eq_trans (KBLK x Hx) (AG1 x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
    assert (AGK : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
    { intros x Hx. change ACtlCutP.KNA.KIND_NAME with 652672 in Hx.
      exact (eq_trans (KIMG x ltac:(change ACtlCutP.KNA.KIND_NAME with 652672; lia))
                      (AG1 x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
    assert (AGW : forall x, A + 184 <= x < A + 320 -> AGR mem1 mem2 x) by (intros x Hx; apply KHI; lia).
    (* the registers the cut reads *)
    assert (G2 : getr regs2 2 = getr regs3 2).
    { etransitivity; [exact (w4a5_pres regs1 regs2 2 2 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 2) with (Z_to_bv 64 sp) by reflexivity. symmetry. exact Hr2. }
    assert (G3 : getr regs2 3 = getr regs3 3).
    { etransitivity; [exact (w4a5_pres regs1 regs2 3 3 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 3) with (getr R 3) by reflexivity. exact E3. }
    assert (G4 : getr regs2 4 = getr regs3 4).
    { etransitivity; [exact (w4a5_pres regs1 regs2 4 4 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 4) with (getr R 4) by reflexivity. exact E4. }
    assert (G8 : getr regs2 8 = getr regs3 8).
    { etransitivity; [exact (w4a5_pres regs1 regs2 8 8 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 8) with (getr R 8) by reflexivity. exact E8. }
    assert (G9 : getr regs2 9 = getr regs3 9).
    { etransitivity; [exact (w4a5_pres regs1 regs2 9 9 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 9) with (getr R 9) by reflexivity. exact E9. }
    assert (G18 : getr regs2 18 = getr regs3 18).
    { etransitivity; [exact (w4a5_pres regs1 regs2 18 18 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 18) with (Z_to_bv 64 phi) by reflexivity. symmetry. exact H18. }
    assert (G19 : getr regs2 19 = getr regs3 19).
    { etransitivity; [exact (w4a5_pres regs1 regs2 19 19 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 19) with (getr R 19) by reflexivity. exact E19. }
    assert (G20 : getr regs2 20 = getr regs3 20).
    { etransitivity; [exact (w4a5_pres regs1 regs2 20 20 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 20) with (Z_to_bv 64 (ACtlCutP.flen cx j)) by reflexivity. symmetry. exact H20. }
    assert (G22 : getr regs2 22 = getr regs3 22).
    { etransitivity; [exact (w4a5_pres regs1 regs2 22 22 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 22) with (getr R 22) by reflexivity. exact E22. }
    assert (G26 : getr regs2 26 = getr regs3 26).
    { etransitivity; [exact (w4a5_pres regs1 regs2 26 26 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 26) with (getr R 26) by reflexivity. exact E26. }
    assert (G27 : getr regs2 27 = getr regs3 27).
    { etransitivity; [exact (w4a5_pres regs1 regs2 27 27 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 27) with (getr R 27) by reflexivity. exact E27. }
    assert (G24 : getr regs2 24 = Z_to_bv 64 0).
    { etransitivity; [exact (w4a5_pres regs1 regs2 24 24 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 24) with (getr R 24) by reflexivity. exact E24. }
    assert (G25 : getr regs2 25 = Z_to_bv 64 0).
    { etransitivity; [exact (w4a5_pres regs1 regs2 25 25 HPRES ltac:(apply bv_eq; reflexivity)
                               ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
      replace (getr regs1 25) with (getr R 25) by reflexivity. exact E25. }
    assert (H9b : ACtlCut.rgv regs2 9 A) by exact (w4a_rgv_move _ _ _ _ Hr9 G9).
    (* the cut's predicates at the post-call memory *)
    pose proof HLK as (_ & _ & _ & HFLI3).
    destruct HFLI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & HKNT3 & _ & _).
    assert (HKNT2 : ACtlCutP.KNT mem2).
    { split.
      - apply (w4a_ba_keep mem3 mem2 _ _ (proj1 HKNT3)).
        pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
        intros x Hx. apply AGK. lia.
      - exact (ctl_kind_name_addressable ly2 S2 W2 mem2 md2 HAR2). }
    assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
    { apply (w4a5_stk_of_pres mem2 fr (fr + ACtlCutP.FRAME_BYTES) ltac:(lia) ltac:(lia)).
      intros a Ha. exact (proj1 (proj2 (Hfrb2 a ltac:(lia)))). }
    assert (HLK2 : ACtlCutP.LK cx fr j regs2 mem2).
    { apply (w4a5_lk_move cx fr j regs3 regs2 mem3 mem2 A HLK Hr9 ltac:(lia) ltac:(lia) G9 G27).
      - intros off x Hoff Hx. cbn [In] in Hoff. apply AGH; lia.
      - intros x Hx. apply AGF; lia.
      - intros x Hx. apply AGFS. unfold ACtlCutP.fragb in Hx. lia.
      - exact HKNT2.
      - exact HSTK2. }
    pose proof HLK2 as (_ & _ & _ & HFLI2).
    destruct HFLI2 as (_ & _ & _ & _ & S120 & S128 & _ & _ & _ & S280 & _ & _ & _ & _ & _ & _ & _ & S256 & _ &
      _ & S296 & S304 & _ & _ & _ & _ & _ & _).
    assert (HFSj2 : ACtlCutP.FSj cx fr j regs2 mem2).
    { apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj);
        intros x Hx; [apply AGF; lia | apply AGFS; lia]. }
    assert (HREC2 : ACtlCutP.REC0 cx fr j mem2)
      by (apply (w4a_rec0_move cx fr j mem3 mem2 HREC); intros x Hx; apply AGF; lia).
    assert (HFPS2 : ACtlCutP.FPS cx fr j mem2).
    { apply (w4a_fps_move cx fr j mem3 mem2 HFPS).
      intros x Hx. split; [apply AGF; lia | apply AGFS; lia]. }
    assert (HFT2 : ACtlCutP.FTURN cx j phi regs2 mem2).
    { apply (w4a_fturn_move cx j phi regs3 regs2 mem3 mem2 A HFT Hr9 ltac:(lia) ltac:(lia) G9).
      - intros x Hx. apply AGH; lia.
      - intros x Hx. apply AGB. lia. }
    assert (QW : forall off v, 184 <= off -> off + 8 <= 320 -> ACtlCutP.q64 mem1 (A + off) v ->
       ACtlCutP.q64 mem2 (A + off) v).
    { intros off v Ho1 Ho2 Hq. unfold ACtlCutP.q64 in *.
      apply (w4a_ba_keep mem1 mem2 _ _ Hq). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply AGW. change (Z.of_nat 8) with 8 in Hx. lia. }
    (* ---- the cut at 0x8215c ---- *)
    rewrite Era1.
    apply (H5c cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ3 Hfrs2' HFA);
      [ unfold ix_cut, ACtlCutP.C_B8215c_at; cbn [ACtlCut.cut_kmax]; rewrite Ej; exact Hk
      | | exact (w4a_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 k HB HJ3) ].
    unfold ix_cut, ACtlCutP.C_B8215c_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
    exists phi.
    split; [rewrite Hab2; exact Hperm|].
    split.
    { apply (w4a_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC G2 G3 G4 G8 G9 G19 G26).
      intros A' x HA' HA'r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA' Hr9 HA'r ltac:(lia)) in Hx.
      destruct Hx as [H1|[H1|[H1|[H1|[H1|H1]]]]].
      - apply AGH; lia.
      - apply AGH; lia.
      - apply AGF; lia.
      - apply AGS. unfold ACtlCutP.Sfr in H1. lia.
      - apply AGH; lia.
      - apply AGF; lia. }
    split; [exact Hn26|]. split; [exact Hj|].
    split.
    { split; [exact (proj1 HHB)|].
      exact (w4a_blk_addr ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) phi
               (B.ACtlK.a_size (ACtlCutP.flen cx j)) HAR2 Hin2 ltac:(lia)
               ltac:(unfold B.ACtlK.a_size; lia) ltac:(unfold B.ACtlK.a_size; lia)). }
    split; [exact HLK2|].
    split; [exact (w4a_rgv_move _ _ _ _ H18 G18)|].
    split; [exact (w4a_rgv_move _ _ _ _ H20 G20)|].
    split.
    { (* FM *)
      split.
      { rewrite Htf. cbn [ACtlCutP.SM.b2z].
        exact (w4a5_spill_of_q64 regs2 mem2 184 0 A H9b (QW 184 0 ltac:(lia) ltac:(lia) Q184)). }
      split; [unfold ACtlCut.rgv; rewrite Htk; exact G24|].
      split; [exact (w4a_rgv_move _ _ _ _ H22 G22)|].
      split; [unfold ACtlCut.rgv; rewrite Hsum; cbn [ACtlCutP.SM.b2z]; exact G25|].
      rewrite Hbig.
      exact (w4a5_spill_of_q64 regs2 mem2 312 0 A H9b (QW 312 0 ltac:(lia) ltac:(lia) Q312)). }
    split; [exact HFSj2|].
    split; [exact (proj1 HKNT2)|].
    split; [exact (proj2 HKNT2)|].
    split.
    { rewrite Hsum. cbn [ACtlCutP.SM.b2z].
      replace (1 - 0) with 1 by lia.
      exact (w4a5_spill_of_q64 regs2 mem2 248 1 A H9b (QW 248 1 ltac:(lia) ltac:(lia) Q248)). }
    split; [intros HH; exfalso; lia|].
    split; [exact HFT2|].
    split; [exact HREC2|].
    split; [exact HFPS2|].
    split.
    { unfold ACtlCutP.F272. rewrite H8819. cbn [ACtlCutP.SM.b2z].
      exact (w4a5_spill_of_q64 regs2 mem2 272 0 A H9b (QW 272 0 ltac:(lia) ltac:(lia) Q272)). }
    exists A, 0.
    split.
    { unfold ACtlCutP.FLVsp.
      split; [exact H9b|].
      split; [exact (w4a5_q64_of_spill regs2 mem2 120 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S120)|].
      split; [exact (w4a5_q64_of_spill regs2 mem2 128 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S128)|].
      split; [exact (w4a5_q64_of_spill regs2 mem2 256 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S256)|].
      split; [exact (w4a5_q64_of_spill regs2 mem2 304 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S304)|].
      exact (w4a5_q64_of_spill regs2 mem2 296 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S296). }
    split.
    { unfold ACtlCut.rgv. rewrite Ha02. f_equal. exact Htk. }
    split; [exact G24|].
    split; [lia|].
    split; [exact (w4a5_q64_of_spill regs2 mem2 280 _ A H9b ltac:(lia) ltac:(lia) ltac:(lia) S280)|].
    apply w4a5_u32_of_rep. rewrite <- EB. exact (proj1 HFPS2).
Qed.

(* ---- seg_F6's local lemmas (prefix w4a6_) ---- *)
(* A spill read at the known spill base A (w4a_spill_keep's base argument, without a move). *)
Lemma w4a6_spill_q64 : forall regs m A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  ACtlCutP.spill regs m off v -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (A + off) (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros regs m A off v Hr9 HA0 HA1 Hoff (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    unfold ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'.
    apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in HA'.
    clear - HA' Hq0 Hq1 HA0 HA1 Hoff. rewrite (Z.mod_small A) in HA' by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* The KIND_NAME table lies in segment 2 of tfibsegs = (0x9f000, 0x3000) (ACtl.v's relro_img_CtrlB argument). *)
Lemma w4a6_kn_img : forall a, 0x9f000 <= a < 0xa2000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold Reusable.YG0d.in_img.
  assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs) 2 =
               Some (0x9f000, 0x3000)) by (vm_compute; reflexivity).
  rewrite nth_error_map in Hb. destruct (nth_error segs 2) as [sg|] eqn:E; [|discriminate Hb].
  cbn in Hb. injection Hb as H1 H2.
  exists sg. split; [exact (nth_error_In _ 2 E) | rewrite H1, H2; lia].
Qed.

(* The shadow byte of a byte of an 8-aligned 4096-byte frame lies in the frame's 512 shadow bytes. *)
Lemma w4a6_sh_in : forall fr x, fr mod 8 = 0 -> fr <= x < fr + 4096 ->
  B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr x < B.AsanRT.shadow_addr fr + 512.
Proof.
  intros fr x H8 Hx. unfold B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D3. lia.
Qed.

(* A shadow address of the application range lies in [ASAN_K, ASAN_K + 2^44), far below the stack window. *)
Lemma w4a6_sh_bound : forall x, 0 <= x < 2 ^ 47 ->
  2147450880 <= B.AsanRT.shadow_addr x < 2147450880 + 2 ^ 44.
Proof.
  intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2. lia.
Qed.

(* The parse struct's first word is the kind (F5.v's c_u32_kind over the cut's pBb). *)
Lemma w4a6_u32_kind : forall cx fr j m, ACtlCutP.pBb cx fr j m ->
  ACtlCutP.u32 m (fr + 176) (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j).
Proof.
  intros cx fr j m H. unfold ACtlCutP.pBb, ACtlCutP.u32, ACtlCutP.SM.t_k, ACtlCutP.SM.t_B in *.
  pose proof (ACtlCutP.RPA.ctrlparse_kind_range (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j)
                (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) as R.
  rewrite (B.Prog.Seg.F5.c_le4_kind _ R). rewrite <- ACtlCutP.RPA.ctrlparse_kind_bytes.
  exact (B.Prog.Seg.F5.c_bytes_firstn m _ _ 4 H).
Qed.

(* FLI / LK across a CALL: w4a_fli_move / w4a_lk_move with the KIND_NAME table (KNT) given at the new memory (its
   shadow is allocator-owned, so a call keeps it only through AR: ctl_kind_name_addressable). *)
Lemma w4a6_fli_move : forall cx fr regs regs' m m' A,
  ACtlCutP.FLI cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.KNT m' ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS HKNT HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & _ & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, In off [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304] ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v H0 Hs. apply (w4a_spill_keep regs regs' m m' A off v H9 HA0 HA1); [| exact E9 | | exact Hs].
    - cbn [In] in H0. lia.
    - intros x Hx. exact (KA off x H0 Hx). }
  unfold ACtlCutP.FLI.
  split; [exact (w4a_rgv_move _ _ _ _ H27 E27)|].
  do 21 (split; [apply K; [cbn [In]; lia | assumption]|]).
  split; [apply (w4a_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (w4a_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (w4a_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold ACtlCutP.fragb in *; lia|].
    apply (w4a_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split; [exact HKNT|].
  split; (apply K; [cbn [In]; lia | assumption]).
Qed.

Lemma w4a6_lk_move : forall cx fr j regs regs' m m' A,
  ACtlCutP.LK cx fr j regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall off x, In off (240 :: [88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176; 192; 200; 208; 216; 256; 264; 280; 288; 296; 304]) -> A + off <= x < A + off + 8 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> AGR m m' x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ ACtlCutP.fragb fr <= x < ACtlCutP.fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 -> AGR m m' (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.KNT m' ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS HKNT HSTK.
  split; [exact Hj|].
  split; [apply (w4a_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply (KA 240 x); [left; reflexivity | exact Hx]|].
  split; [exact (w4a_our_move cx fr m m' HOUR KF)|].
  apply (w4a6_fli_move cx fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27); [|exact KS | exact HKNT | exact HSTK].
  intros off x Hoff Hx. apply (KA off x); [right; exact Hoff | exact Hx].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82098_at j (0x82098, own6, k <= 14+2j+1) --S_F6--> B8215c_at j.
   S_F6 (Seg/F6.v seg_F6 :729): the 32-turn block sum of Phi[18 .. 50) (back edge 0x820c4 inside the run),
   [A + 312] := Phi + 18, T18 / T19 and the checked reads of Phi[16] / Phi[17] ([A + 184] = b2z t_tfill), the abort
   compare 0x82138, s9 = b2z t_sum_ok, [A + 248], then the shared parse block @0x82158. *)
Lemma seg_F6 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B8215c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82098_at [Z.of_nat j]).
Proof using tfibsegs_rsegs Hwx ctl_kind_name_addressable ctl_kind_name_not_owned
  LAWS segs_low PARSE TFIB_SYMS RELRO_IMG RO_OFL.
  intros POST j H5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ix_cut, ACtlCutP.C_B82098_at in Hk, HBODY, HJ, Hfr, HFA |- *.
  cbn [ACtlCut.cut_pc ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body] in Hk, HBODY, HJ, Hfr, HFA |- *.
  destruct HBODY as (-> & HBODY).
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Ej in Hk, HBODY.
  destruct HBODY as (HFRAC & phi & Hperm & Hn26 & Hj & HHB & H18 & H20 & HFT & HLK & H22 & HFSj & HREC & HFPS &
    H272 & H50 & H24 & Ha0 & H11 & H12 & H13 & H14 & H17 & H5).
  (* ---- the journal, the spill base, the frame, the turn block ---- *)
  destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ) as (HAR & Hceil & Hsp47 & Hwin).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hcv.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
    Hfa & HA448 & HS4 & HAPP & _).
  pose proof (w4a_spZ regs3) as Hsp.
  assert (HSTKv : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  assert (HFBv : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (Hin : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (w4a_blk _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hn0 & Hreq & Hpvis & Hpshvis).
  pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ Hfr (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
    as (Hfr32' & Hfr4096 & Hfrceil & Hfrb & Hfrsh).
  assert (HA34 : 2 ^ 34 <= A) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  (* ---- the model facts: phi's 50 record bytes, the kind, the flags (F6.v) ---- *)
  pose proof (B.Prog.SlotInv.t_g_of_phi mem3 phi (ACtlCut.c_in cx) j (proj1 (proj2 (proj2 HFT))) H50) as HGb.
  pose proof (B.Prog.Seg.F5.c_tg_len (ACtlCut.c_in cx) j) as Hglen.
  assert (Htk : 0 <= ACtlCutP.SM.t_k (ACtlCut.c_in cx) j <= 13) by exact (ACtlCutP.RPA.ctrlparse_kind_range _ _).
  assert (Hbig : ACtlCutP.SM.t_big (ACtlCut.c_in cx) j = true)
    by (unfold ACtlCutP.SM.t_big; apply Z.leb_le; exact H50).
  (* SINK 0x82138 not taken: [A + 272] = b2z (t_8819 j) = (t_k j <> 0) (F6.v's f6_8819_eq) *)
  assert (He272 : ACtlCutP.SM.b2z (ACtlCutP.SM.t_8819 (ACtlCut.c_in cx) j) =
                  (if ACtlCutP.SM.t_k (ACtlCut.c_in cx) j =? 0 then 0 else 1)).
  { rewrite <- (B.Prog.Seg.F6.f6_8819_eq (ACtlCut.c_in cx) j). rewrite w4a_wa_u by lia. reflexivity. }
  assert (Hsum : ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) j) =
     (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32 mod 256 =? 0 then 1 else 0))
    by exact (B.Prog.Seg.F6.f6_sum _ _ Hbig).
  assert (Hsum' : 1 - ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) j) =
     (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32 mod 256 =? 0 then 0 else 1)).
  { rewrite Hsum. destruct (ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32 mod 256 =? 0);
      reflexivity. }
  (* ---- f6_run_evt_F's premises ---- *)
  pose proof (w4a6_spill_q64 regs3 mem3 A 272 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H272) as Hq272.
  pose proof (w4a_blk_addr _ _ _ _ _ _ _ phi 50 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)) as Haddr50.
  assert (Hstk : lib.Lib.Frame.stk B.Img0.rsegs mem3 (A + 184) (A + 320)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (Hwin a ltac:(lia)) as (_ & b & Hb).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  assert (Hshadow : forall x, phi <= x < phi + 50 -> B.AsanRT.shadow_addr x < A).
  { intros x Hx. pose proof (w4a_sh_lt x A ltac:(lia) HA34). lia. }
  assert (Rrec : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (phi + 16) 34)
    by (apply w4a_rng; [lia | lia | intros a Ha; apply Hpvis; lia]).
  assert (Rsh : forall x, phi + 16 <= x < phi + 50 ->
     Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Z.shiftr x 3 + B.AsanRT.ASAN_K) 1).
  { intros x Hx. rewrite w4a_shr3 by lia. pose proof (Hpshvis x ltac:(lia)) as Hv.
    pose proof (w4a_sh_lt x (2 ^ 47) ltac:(lia) ltac:(lia)) as Hb.
    apply w4a_rng; [lia | lia | intros a Ha; replace a with (B.AsanRT.shadow_addr x) by lia; exact Hv]. }
  assert (R184 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 184) 8)
    by (apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]).
  assert (R248 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 248) 8)
    by (apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]).
  assert (R272 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 272) 8)
    by (apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]).
  assert (R312 : Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 312) 8)
    by (apply w4a_rng; [lia | lia | intros a Ha; exact (proj1 (Hwin a ltac:(lia)))]).
  assert (G2 : B.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp) by exact Hr2.
  assert (G5 : B.Reusable.YK11.getr regs3 5 = Z_to_bv 64 (phi + 18)) by exact H5.
  assert (G9 : B.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (G10 : B.Reusable.YK11.getr regs3 10 = Z_to_bv 64 (phi + 18)) by exact Ha0.
  assert (G11 : B.Reusable.YK11.getr regs3 11 = Z_to_bv 64 0) by exact H11.
  assert (G12 : B.Reusable.YK11.getr regs3 12 = Z_to_bv 64 (phi + 18)) by exact H12.
  assert (G13 : B.Reusable.YK11.getr regs3 13 = Z_to_bv 64 (- (phi + 18))) by exact H13.
  assert (G14 : B.Reusable.YK11.getr regs3 14 = Z_to_bv 64 32) by exact H14.
  assert (G17 : B.Reusable.YK11.getr regs3 17 = Z_to_bv 64 32) by exact H17.
  assert (G18 : B.Reusable.YK11.getr regs3 18 = Z_to_bv 64 phi) by exact H18.
  assert (G20 : B.Reusable.YK11.getr regs3 20 = Z_to_bv 64 (flen cx j)) by exact H20.
  assert (G24 : B.Reusable.YK11.getr regs3 24 = Z_to_bv 64 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j)) by exact H24.
  assert (G26 : B.Reusable.YK11.getr regs3 26 = Z_to_bv 64 B.AsanRT.ASAN_K) by exact Hr26.
  (* ---- the run's memory: [A + 312] := phi + 18, [A + 184] := tfill, [A + 248] := 1 - sum_ok ---- *)
  pose (M1 := write_to_mem mem3 (lib.Lib.Mem.wa (A + 312)) (lib.Lib.Mem.le8 (Z_to_bv 64 (phi + 18)))).
  pose (M2 := write_to_mem M1 (lib.Lib.Mem.wa (A + 184))
                (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.Seg.F6.f6_tf (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j))))).
  pose (M3 := write_to_mem M2 (lib.Lib.Mem.wa (A + 248))
                (lib.Lib.Mem.le8 (Z_to_bv 64 (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32
                                                 mod 256 =? 0 then 0 else 1)))).
  (* ---- 1. the run 0x82098 -> 0x8214c (F6F.f6_run_evt_F) and the parse call block (F5F.c_pre_F) ---- *)
  apply (w4_lift W3 0x82098 regs3 mem3 md3
    (fun ms => exists R : bvmap 5 word,
       ms = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 ACtlCutP.RCP.REAC_CTRL_PARSE)
              lib.Reusable.YK11.fp_csr None M3 (lib.Reusable.YK11.seg_rom B.Img0.rsegs) /\
       getr R 1 = Z_to_bv 64 0x8215c /\ getr R 2 = getr regs3 2 /\ getr R 3 = getr regs3 3 /\
       getr R 4 = getr regs3 4 /\ getr R 8 = getr regs3 8 /\ getr R 9 = getr regs3 9 /\
       getr R 10 = Z_to_bv 64 phi /\ getr R 11 = Z_to_bv 64 (flen cx j) /\ getr R 12 = Z_to_bv 64 0 /\
       getr R 18 = getr regs3 18 /\ getr R 19 = getr regs3 19 /\ getr R 20 = getr regs3 20 /\
       getr R 22 = getr regs3 22 /\ getr R 24 = getr regs3 24 /\
       getr R 25 = Z_to_bv 64 (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32 mod 256 =? 0
                               then 1 else 0) /\
       getr R 26 = getr regs3 26 /\ getr R 27 = getr regs3 27)
    (POST cx)).
  { rewrite B.Prog.Seg.F5.c_mkR_expand.
    rewrite G2, G5, G9, G10, G11, G12, G13, G14, G17, G18, G20, G24, G26.
    eapply Lib.ExecF.evtF_cut.
    { exact (B.Prog.Seg.F6F.f6_run_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 phi A (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j)
               (ACtlCutP.SM.b2z (ACtlCutP.SM.t_8819 (ACtlCut.c_in cx) j)) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)
               ltac:(lia) ltac:(lia) Hglen HGb Haddr50 ltac:(lia) ltac:(lia) Hstk ltac:(lia) Hq272 He272 ltac:(lia)
               Hshadow Rrec Rsh R184 R248 R272 R312). }
    intros ms1 (b0 & b1 & b2 & b3 & b4 & b5 & b6 & ->).
    eapply Lib.ExecF.evtF_mono; [apply B.Prog.Seg.F5F.c_pre_F|].
    intros ms2 ->. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; first [reflexivity | symmetry; assumption]. }
  intros ms' md' (R & -> & E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E22 & E24 & E25 & E26 &
    E27) Hhid Hsame.
  (* ---- 2. the run's memory (munch of the three spill words), the journal at the call ---- *)
  assert (MU : lib.Lib.Frame.munch [(A + 312, A + 320); (A + 184, A + 192); (A + 248, A + 256)] mem3 M3).
  { subst M3 M2 M1.
    apply lib.Lib.Frame.munch_write;
      [apply lib.Lib.Frame.munch_write;
         [apply lib.Lib.Frame.munch_write;
            [apply lib.Lib.Frame.munch_refl | lia | rewrite lib.Lib.Mem.length_le8; lia
            | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]
         | lia | rewrite lib.Lib.Mem.length_le8; lia | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]
      | lia | rewrite lib.Lib.Mem.length_le8; lia | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (MU13 : lib.Lib.Frame.munch [(A + 184, A + 192); (A + 248, A + 256)] M1 M3).
  { subst M3 M2.
    apply lib.Lib.Frame.munch_write;
      [apply lib.Lib.Frame.munch_write;
         [apply lib.Lib.Frame.munch_refl | lia | rewrite lib.Lib.Mem.length_le8; lia
         | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]
      | lia | rewrite lib.Lib.Mem.length_le8; lia | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (MU23 : lib.Lib.Frame.munch [(A + 248, A + 256)] M2 M3).
  { subst M3.
    apply lib.Lib.Frame.munch_write;
      [apply lib.Lib.Frame.munch_refl | lia | rewrite lib.Lib.Mem.length_le8; lia
      | cbn [lib.Lib.Frame.inside]; rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (WM : lib.Lib.Frame.wmono B.Img0.rsegs mem3 M3)
    by (subst M3 M2 M1; apply lib.Lib.Frame.wmono_write; apply lib.Lib.Frame.wmono_write;
        apply lib.Lib.Frame.wmono_write; apply lib.Lib.Frame.wmono_refl).
  assert (AG1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 312 <= x < A + 320) -> ~ (A + 184 <= x < A + 192) ->
             ~ (A + 248 <= x < A + 256) -> AGR mem3 M3 x).
  { intros x Hx N1 N2 N3. apply (w4a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside].
    exact (conj N1 (conj N2 (conj N3 I))). }
  assert (Q312 : lib.Lib.Mem.bytes_at B.Img0.rsegs M3 (A + 312) (lib.Lib.Mem.le8 (Z_to_bv 64 (phi + 18)))).
  { apply (w4a_ba_keep M1 M3).
    - subst M1. apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia].
    - rewrite lib.Lib.Mem.length_le8. intros x Hx. apply (w4a_mrd_munch _ _ _ x MU13); [lia|].
      cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (Q184 : lib.Lib.Mem.bytes_at B.Img0.rsegs M3 (A + 184)
                   (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.Seg.F6.f6_tf (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j))))).
  { apply (w4a_ba_keep M2 M3).
    - subst M2. apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia].
    - rewrite lib.Lib.Mem.length_le8. intros x Hx. apply (w4a_mrd_munch _ _ _ x MU23); [lia|].
      cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (Q248 : lib.Lib.Mem.bytes_at B.Img0.rsegs M3 (A + 248)
                   (lib.Lib.Mem.le8 (Z_to_bv 64 (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32
                                                    mod 256 =? 0 then 0 else 1)))).
  { subst M3. apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (HGb3 : lib.Lib.Mem.bytes_at B.Img0.rsegs M3 phi (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)).
  { apply (w4a_ba_keep mem3 M3 _ _ HGb). rewrite Hglen. intros x Hx. apply AG1; lia. }
  assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 M3 md' k).
  { apply (w4a_aj_run _ _ _ _ _ _ _ _ _ _ _ HJ MU WM Hhid Hsame).
    intros a Ha.
    assert (Hai : A + 184 <= a < A + 320).
    { cbn [lib.Lib.Frame.outside] in Ha.
      destruct (Z_lt_le_dec a (A + 184)) as [Hl|Hl]; [exfalso; apply Ha; repeat split; lia|].
      destruct (Z_lt_le_dec a (A + 320)) as [Hh|Hh]; [lia | exfalso; apply Ha; repeat split; lia]. }
    split; [lia|]. split; [exact (proj2 (Hwin a ltac:(lia)))|]. left. lia. }
  assert (EspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite E2; exact Hspz).
  (* ---- 3. reac_ctrl_parse(phi, len, 0) @0x82158: PARSE (w4a_parse) at o = 0, returning to the cut 0x8215c ---- *)
  apply (w4a_parse Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
           (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 M3 md' k R phi (flen cx j) 0
           (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) (POST cx) HJ').
  - exact (w4a_arodata_cut cx (own6 cx) ly3 S3 W3 M3 md' k HB HJ').
  - rewrite E1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
  - unfold Reusable.YG0d.raZ. rewrite E1, w4a_wa_u by lia. lia.
  - pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _). rewrite E3, Hr3. exact Hgp0.
  - rewrite E4. exact Hr4.
  - exact E10.
  - exact E11.
  - exact E12.
  - lia.
  - rewrite EspR. exact Hsp16.
  - rewrite EspR. unfold ACtlCutP.RCP.REAC_CTRL_PARSE_K. lia.
  - rewrite EspR. lia.
  - rewrite Hfr. vm_compute. reflexivity.
  - intros _. exists (flen cx j). split; [exact Hin | lia].
  - intros Ho. exfalso. apply Ho. reflexivity.
  - intros Ho. exfalso. apply Ho. reflexivity.
  - exact Hglen.
  - intros _ i Hi.
    rewrite (w4a_ba_aview W3 M3 phi _ i HGb3 ltac:(lia) (Hpvis (phi + Z.of_nat i) ltac:(lia))).
    reflexivity.
  - intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2 Hfrs2 Hab2 _ Ha02 _ HKC.
    replace (Reusable.YG0d.raZ R) with 0x8215c
      by (unfold Reusable.YG0d.raZ; rewrite E1, w4a_wa_u by lia; reflexivity).
    destruct (w4a_aj_bits _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & _).
    assert (Hfrs2' : Reusable.YG01.frames S2 = own6 cx) by (rewrite Hfrs2; exact Hfr).
    pose proof (w4a_frame _ _ _ _ _ _ _ _ HJ2 Hfrs2' (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)))
      as (_ & _ & _ & Hfrb2 & _).
    assert (Hin2 : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hab2; exact Hin).
    (* the callee-saved registers (aregs_preserved) *)
    assert (P2 : getr regs2 2 = getr regs3 2)
      by (rewrite <- E2; exact (HP2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P3 : getr regs2 3 = getr regs3 3)
      by (rewrite <- E3; exact (HP2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P4 : getr regs2 4 = getr regs3 4)
      by (rewrite <- E4; exact (HP2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P8 : getr regs2 8 = getr regs3 8)
      by (rewrite <- E8; exact (HP2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P9 : getr regs2 9 = getr regs3 9)
      by (rewrite <- E9; exact (HP2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P18 : getr regs2 18 = getr regs3 18)
      by (rewrite <- E18; exact (HP2 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P19 : getr regs2 19 = getr regs3 19)
      by (rewrite <- E19; exact (HP2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P20 : getr regs2 20 = getr regs3 20)
      by (rewrite <- E20; exact (HP2 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P22 : getr regs2 22 = getr regs3 22)
      by (rewrite <- E22; exact (HP2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P24 : getr regs2 24 = getr regs3 24)
      by (rewrite <- E24; exact (HP2 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P25 : getr regs2 25 = Z_to_bv 64 (if ACtlCutP.RMO.psum (skipn 18 (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j)) 32
                                                 mod 256 =? 0 then 1 else 0))
      by (rewrite <- E25; exact (HP2 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P26 : getr regs2 26 = getr regs3 26)
      by (rewrite <- E26; exact (HP2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    assert (P27 : getr regs2 27 = getr regs3 27)
      by (rewrite <- E27; exact (HP2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
    (* the bytes the call keeps (ctl_post_acall_kept: high memory above the callee window, the owned frame and its
       shadow, the live turn block, the KIND_NAME image bytes), at visible addresses of W3 *)
    assert (AGC : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
              ((ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= x < ACtlCut.c_sp cx /\ sp <= x) \/
               (Reusable.YCbq.in_frames ly3 (own6 cx) x /\ 36 <= x) \/
               (phi <= x < phi + Reusable.YG00.req_size (flen cx j)) \/
               (ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112)) ->
              AGR M3 mem2 x).
    { intros x Hx Hv Hc.
      apply (B.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 M3 mem2 _ _ _ HKC Hwle (Z_to_bv 64 x) Hv).
      rewrite w4a_wa_u by exact Hx.
      destruct Hc as [Hc|[Hc|[Hc|Hc]]].
      - left. split; [lia|]. rewrite EspR. lia.
      - right; right; right. destruct Hc as ((cid & pos & Hcp & Hz) & H36). exists cid, pos.
        split; [rewrite Hfr; exact Hcp|]. split; [exact Hz|]. cbv beta. lia.
      - right; left. exists phi, (flen cx j), (x - phi).
        split; [exact Hin|]. split; [lia|]. split; [lia|]. cbv beta. lia.
      - right; right; left. split.
        + apply w4a6_kn_img. change ACtlCutP.KNA.KIND_NAME with 652672 in Hc. lia.
        + exact (ctl_kind_name_not_owned x Hc). }
    assert (AGW : forall x, sp <= x < ACtlCut.c_sp cx -> AGR M3 mem2 x).
    { intros x Hx. apply (AGC x ltac:(lia) (proj1 (Hwin x ltac:(lia)))). left. lia. }
    assert (AGS : forall x, sp <= x < ACtlCut.c_sp cx -> ~ (A + 312 <= x < A + 320) -> ~ (A + 184 <= x < A + 192) ->
               ~ (A + 248 <= x < A + 256) -> AGR mem3 mem2 x).
    { intros x Hx N1 N2 N3. rewrite (AGW x Hx). exact (AG1 x ltac:(lia) N1 N2 N3). }
    assert (AGF : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 x).
    { intros x Hx. destruct (Hfrb x Hx) as (Hv & _ & Hif).
      rewrite (AGC x ltac:(lia) Hv ltac:(right; left; split; [exact Hif | lia])). apply AG1; lia. }
    assert (AGSH : forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 512 -> AGR mem3 mem2 x).
    { intros x Hx. destruct (Hfrsh x Hx) as (Hv & _ & Hif).
      pose proof (w4a6_sh_bound fr ltac:(lia)) as Hsb.
      rewrite (AGC x ltac:(lia) Hv ltac:(right; left; split; [exact Hif | lia])). apply AG1; lia. }
    assert (AGFS : forall x, fr <= x < fr + 4096 -> AGR mem3 mem2 (B.AsanRT.shadow_addr x)).
    { intros x Hx. apply AGSH. exact (w4a6_sh_in fr x Hfr8 Hx). }
    assert (AGP : forall x, phi <= x < phi + Reusable.YG00.req_size (flen cx j) -> AGR mem3 mem2 x).
    { intros x Hx. rewrite (AGC x ltac:(lia) (Hpvis x Hx) ltac:(right; right; left; exact Hx)). apply AG1; lia. }
    assert (AGK : forall x, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 -> AGR mem3 mem2 x).
    { intros x Hx. destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
      unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
      assert (Hx' : 652672 <= x < 652672 + 112) by exact Hx.
      assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
      { apply Himg. lia. }
      rewrite (AGC x ltac:(lia) Hv ltac:(right; right; right; exact Hx)). apply AG1; lia. }
    (* FLI's KNT after the call: the table bytes kept (image, not owned), their shadow from the post-call AR *)
    assert (HKNT2 : ACtlCutP.KNT mem2).
    { pose proof HLK as (_ & _ & _ & HFLI).
      destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & (HKNb & _) & _).
      split.
      - apply (w4a_ba_keep mem3 mem2 _ _ HKNb). pose proof B.Prog.Seg.F1.f1_kn_len as HL. apply Nat.leb_le in HL.
        intros x Hx. apply AGK. lia.
      - exact (ctl_kind_name_addressable _ _ _ _ _ HAR2). }
    assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
    { split; [lia|]. split; [lia|]. intros a Ha. destruct (Hfrb2 a ltac:(lia)) as (_ & (b & Hb) & _).
      split; [unfold wview, lib.Lib.Mem.wa; rewrite Hb; discriminate|].
      exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
    assert (HLK2 : ACtlCutP.LK cx fr j regs2 mem2).
    { apply (w4a6_lk_move cx fr j regs3 regs2 mem3 mem2 A HLK Hr9 ltac:(lia) ltac:(lia) P9 P27).
      - intros off x Hoff Hx. cbn [In] in Hoff. apply AGS; lia.
      - intros x Hx. apply AGF; lia.
      - intros x Hx. apply AGFS. unfold ACtlCutP.fragb in Hx. lia.
      - exact HKNT2.
      - exact HSTK2. }
    assert (HFPS2 : ACtlCutP.FPS cx fr j mem2).
    { apply (w4a_fps_move cx fr j mem3 mem2 HFPS). intros x Hx. split; [apply AGF; lia | apply AGFS; lia]. }
    pose proof (w4a_rgv_move _ _ _ _ Hr9 P9) as Hr9'.
    (* ---- 4. the cut B8215c_at j ---- *)
    apply (H5c cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2).
    + exact Hfrs2'.
    + exact HFA.
    + unfold ix_cut, ACtlCutP.C_B8215c_at. cbn [ACtlCut.cut_kmax]. rewrite Ej. exact Hk.
    + unfold ix_cut, ACtlCutP.C_B8215c_at. cbn [ACtlCut.cut_body]. split; [reflexivity|]. cbv zeta. rewrite Ej.
      exists phi.
      split; [rewrite Hab2; exact Hperm|].
      split.
      { apply (w4a_frac_move cx fr fr regs3 regs2 mem3 mem2 HFRAC P2 P3 P4 P8 P9 P19 P26).
        intros A' x HA' HA'r Hx. rewrite (w4a_rgv_inj _ _ _ _ HA' Hr9 HA'r ltac:(lia)) in Hx.
        unfold ACtlCutP.Sfr in Hx.
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]];
          [apply AGS; lia | apply AGS; lia | apply AGF; lia | apply AGSH; lia | apply AGS; lia | apply AGF; lia]. }
      split; [exact Hn26|]. split; [exact Hj|].
      split.
      { split; [exact (proj1 HHB)|].
        pose proof (Reusable.YCbq.req_size_pos (flen cx j) Hn0) as Hrs.
        apply (w4a_blk_addr _ _ _ _ _ phi (flen cx j) phi _ HAR2 Hin2); unfold B.ACtlK.a_size; lia. }
      split; [exact HLK2|].
      split; [exact (w4a_rgv_move _ _ _ _ H18 P18)|].
      split; [exact (w4a_rgv_move _ _ _ _ H20 P20)|].
      split.
      { split.
        { exists A. split; [exact Hr9'|]. unfold ACtlCutP.q64.
          rewrite (B.Prog.Seg.F6.f6_tfill _ _ Hbig). apply (w4a_ba_keep M3 mem2 _ _ Q184).
          rewrite lib.Lib.Mem.length_le8. intros x Hx. apply AGW; lia. }
        split; [exact (w4a_rgv_move _ _ _ _ H24 P24)|].
        split; [exact (w4a_rgv_move _ _ _ _ H22 P22)|].
        split; [unfold ACtlCut.rgv; rewrite P25, Hsum; reflexivity|].
        rewrite Hbig. exists A. split; [exact Hr9'|]. unfold ACtlCutP.q64.
        apply (w4a_ba_keep M3 mem2 _ _ Q312). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply AGW; lia. }
      split; [apply (w4a_fsj_move cx fr j regs3 regs2 mem3 mem2 HFSj); intros x Hx; [apply AGF; lia | apply AGFS; lia]|].
      split; [exact (proj1 HKNT2)|]. split; [exact (proj2 HKNT2)|].
      split.
      { exists A. split; [exact Hr9'|]. unfold ACtlCutP.q64. rewrite Hsum'.
        apply (w4a_ba_keep M3 mem2 _ _ Q248). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply AGW; lia. }
      split.
      { intros _. apply (w4a_ba_keep mem3 mem2 _ _ HGb). rewrite Hglen. intros x Hx. apply AGP; lia. }
      split.
      { apply (w4a_fturn_move cx j phi regs3 regs2 mem3 mem2 A HFT Hr9 ltac:(lia) ltac:(lia) P9);
          intros x Hx; [apply AGS; lia | apply AGP; unfold ACtlCutP.flen in *; lia]. }
      split; [apply (w4a_rec0_move cx fr j mem3 mem2 HREC); intros x Hx; apply AGF; lia|].
      split; [exact HFPS2|].
      split.
      { exists A. split; [exact Hr9'|]. unfold ACtlCutP.q64.
        apply (w4a_ba_keep mem3 mem2 _ _ Hq272). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply AGS; lia. }
      exists A, (ACtlCutP.SM.t_k (ACtlCut.c_in cx) j).
      pose proof HLK2 as (_ & _ & _ & HFLI2).
      destruct HFLI2 as (_ & _ & _ & _ & S120 & S128 & _ & _ & _ & S280 & _ & _ & _ & _ & _ & _ & _ & S256 & _ & _ &
        S296 & S304 & _).
      split.
      { split; [exact Hr9'|].
        split; [exact (w4a6_spill_q64 regs2 mem2 A 120 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S120)|].
        split; [exact (w4a6_spill_q64 regs2 mem2 A 128 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S128)|].
        split; [exact (w4a6_spill_q64 regs2 mem2 A 256 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S256)|].
        split; [exact (w4a6_spill_q64 regs2 mem2 A 304 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S304)|].
        exact (w4a6_spill_q64 regs2 mem2 A 296 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S296). }
      split; [exact Ha02|].
      split; [exact (w4a_rgv_move _ _ _ _ H24 P24)|].
      split; [lia|].
      split; [exact (w4a6_spill_q64 regs2 mem2 A 280 _ Hr9' ltac:(lia) ltac:(lia) ltac:(lia) S280)|].
      exact (w4a6_u32_kind cx fr j mem2 (proj1 HFPS2)).
    + exact (w4a_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 k HB HJ2).
Qed.

End W4a.

(* Assumption audit of each closed stage (the gate's named Print Assumptions). *)
Check ctl_W4a_malloc_81f4c.
Print Assumptions ctl_W4a_malloc_81f4c.
Check seg_F1.
Print Assumptions seg_F1.
Check seg_F2.
Print Assumptions seg_F2.
Check seg_F3.
Print Assumptions seg_F3.
Check seg_F4.
Print Assumptions seg_F4.
Check seg_F5.
Print Assumptions seg_F5.
Check seg_F6.
Print Assumptions seg_F6.

(* Stage lemmas of this file, EVERY ONE ENDING IN Qed (each from the Section hypotheses its `Proof using` line names;
   the closed statements carry exactly those):
     ctl_W4a_malloc_81f4c : the allocator site (statement above)
     seg_F1 (B81ec4_at) : forall POST j, ctl_from POST (ix_cut C_B81f50_at [j]) -> ctl_from POST C_B82eac ->
                          ctl_from POST (ix_cut C_B81ec4_at [j])
     seg_F2 (B81f50_at) : forall POST j, ctl_from POST (ix_cut C_B81f78_at [j]) ->
                          ctl_from POST (ix_cut C_B82048_at [j]) -> ctl_from POST (ix_cut C_B81f50_at [j])
     seg_F3 (B81f78_at) : forall POST j, ctl_from POST (ix_cut C_B81fbc_at [j]) ->
                          ctl_from POST (ix_cut C_B82048_at [j]) -> ctl_from POST (ix_cut C_B81f78_at [j])
     seg_F4 (B81fbc_at) : forall POST j, ctl_from POST (ix_cut C_B82098_at [j]) -> ctl_from POST (ix_cut C_B81fbc_at [j])
     seg_F5 (B82048_at) : forall POST j, ctl_from POST (ix_cut C_B8215c_at [j]) -> ctl_from POST (ix_cut C_B82048_at [j])
     seg_F6 (B82098_at) : forall POST j, ctl_from POST (ix_cut C_B8215c_at [j]) -> ctl_from POST (ix_cut C_B82098_at [j])
   ([j] abbreviates [Z.of_nat j].)  Each seg_* is named and stated exactly as ACtl.v's Hypothesis of the same name
   (576147dfd46), generic in SK and FP.
   Sink / trap obligations (branch -> target: refuting lemma, step):
     0x81ed4 (T10) -> 0x82fa0 : seg_F1 step 1     0x81f04 (T11) -> 0x82fa0 : seg_F1 step 1
     0x81f3c (T12) -> 0x82fa0 : seg_F1 step 1     0x81f5c (j)   -> 0x82fa4 : seg_F2 step 1
     0x81f84 (T13) -> 0x82fa0 : seg_F3 step 1     0x81f90 (T14) -> 0x82fa0 : seg_F3 step 1
     0x81fc8 (T15) -> 0x82fa0 : seg_F4 step 1     0x81ff4 (T16) -> 0x82fa0 : seg_F4 step 1
     0x82048 (bnez)-> 0x82fa4 : seg_F5 step 1     0x8209c (T17) -> 0x82fa0 : seg_F6 step 1
     0x820e0 (T18) -> 0x82fa0 : seg_F6 step 1     0x8210c (T19) -> 0x82fa0 : seg_F6 step 1
     0x82138 (bne) -> 0x82fa4 : seg_F6 step 1
   Dead edge discharged: S_F1 -> B82eac (LI's 1 <= t_left j). *)
