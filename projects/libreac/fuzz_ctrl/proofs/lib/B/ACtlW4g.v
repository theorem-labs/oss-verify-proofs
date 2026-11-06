(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 943 of its 1013 lines of code are new or changed and 2396 lines of the source are left out. *)
(* lib/B/ACtlW4g.v -- piece W4g (frame turn, end: S_F37, S_F38) of fuzz_ctrl image B's (asan-ubsan) walk of
   LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane.
   rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): the stage lemmas of cut-table rows 84-85, POINTWISE in the frame-loop index
   j (ACtlCut.ix_cut, a Theorem Labs lane 22:47Z), plus the ONE local lemma of the allocator site 0x82d18:
     B82ca0_at j (0x82ca0, own6, k <= 14+2j+1, live list entry ++ [(phi, flen cx j)])
                 --S_F37--> B82d1c_at j                 free(Phi) @0x82d18 (ctl_W4g_free_82d18)
     B82d1c_at j (0x82d1c, own6, k <= 14+2j+2, live list = entry blocks)
                 --S_F38--> B81ec4_at (S j)              the frame-loop LATCH (j < 255, left_(j+1) >= 1)
                          | B82eac                       the loop exit (j = 255, or left_(j+1) = 0 through 0x81ec4)
   The latch keeps the k bound exactly: 14 + 2j + 2 = 14 + 2 (S j) (B81ec4_at's bound at S j); the exit's
   14 + 2j + 2 <= 14 + 2*255 + 2 = 526 = B.ACtlK.EV_LLVMF (j <= 255 from LK).  These two lemmas close the turn: with
   W4a .. W4f they give, for each j, ctl_from POST (ix_cut C_B81ec4_at [S j]) -> ctl_from POST C_B82eac ->
   ctl_from POST (ix_cut C_B81ec4_at [j]), the step of the top's rt_G_allX induction over 256 - j (plan 3, row 7).

   ROUTE, BUILD STATE, SHELL GAPS (G1) / (G2), the shared Section hypothesis Hwx and the PENDING KIT / BRIDGE FACTS:
   exactly as lib/B/ACtlW0.v's header.  The frame-pointer chain and call
   trace at the allocator call are the shell's `ACtlCut.ctl_chain` / `ACtlCut.ctl_trace_in`; their source is the
   Section hypothesis CHAIN_OF_CUT (the shell's former ctl_chain_of_cut, which lib/B/ACtl.v now carries as its own
   Section hypothesis CHAIN_OF_CUT; same name and text here, copied from the sibling W2a, so the top discharges this
   one with its own).  The site lemma takes chain_pre and the trace as premises, as the sibling W2a's site lemmas do.

   SECTION HYPOTHESES OF THIS FILE (sources):
   - AFREE4 : Reusable.YC5d.afree04_rule segs B MT (donor YC5d.v:75-96; the core's allocator rule for B, a Theorem Labs lane's core
     slice, plan M13), named ONLY in ctl_W4g_free_82d18.  HMOK: the trivial meter (donor A/AD2o.v:49).  HPCF: B's free
     wrapper entry by the core's catalogue name (the sibling W2a's text).  LAWS: the core's AR_laws (for the not-an-entry-
     block step, the sibling W2a's w2_phi_not_entry argument through al_sep).
   - ctl_post_acall_kept : a Theorem Labs lane's allocator conversion (item 23), the image-B TWIN of its published text,
     lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:646-663; written on a working branch c03ce1627b6) (kept_class at head lib/A/ProgWorld.v:646-656, the lemma
     at head lib/A/ProgWorld.v:658-663; PROVED there), changing only lib.Reusable -> Reusable, Lib.Mem -> lib.Lib.Mem and A.Img0 -> B.Img0.  The free rule ends in
     acall_kept (Reusable.YCbq.v:824-835), and from it the mrd read is kept at a VISIBLE address of a KEPT CLASS:
     high memory outside the call window, a live block off E, a non-owned non-errno image byte, a live frame's
     bytes or shadow off E.  kept_class takes YM05's RunCeil field alloc_ceiling, as acall_kept does
     (Reusable.YCbq.v:826), over Reusable.YG0f.alayout and Reusable.YG00.astate -- never YK06's alloc_ceiling
     (two Theorem Labs lanes, 02:2xZ).  At this file's one site E is the freed block (phi, flen cx j) and
     [slo, shi) is the ASTACK window [c_sp cx + o - ASTACK, c_sp cx + o).  munch_vis over ALL addresses is NOT
     derivable there (the allocator's own bytes change), so no plan here claims one.
   - (aview_vis_mrd, RTPOST-SHARED-B.txt's member and lib/B/ProgWorld.v:587's lemma, is not declared here: no lemma
     of this file takes it, measured by About / Arguments on the compiled lemmas.)
   - ctl_kind_name_addressable / ctl_kind_name_not_owned : the shared RtPost text's V6 / T10 twins for KIND_NAME
     (lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) at adc9b58a03c, owner a Theorem Labs lane), pasted token for token: FLI's KNT crosses the free
     through the post-call AR (addressability) and through ctl_post_acall_kept's image arm (the 112 bytes).
   - the runtime conjunct after the free (route (C), brief routeC-refit.md): the cut carries ctl_rt_C
     (B.ACtlRtC.ctl_rt_C B ly S m: asan cells, shadow_rw only on the cut's own shadow and the image's, ro_agree), and
     seg_F37's exit produces it at the post-free state by B.ProgWorldCtlRtC.ctl_rt_C_of_AR, cited by name.  Its
     premises are the named Section hypothesis TFIB_SYMS (lib/B/ACtl.v's text, which the top discharges), LAWS, the
     post-call AR, and arodata_okP at the post-free state, which w4g_arodata_post derives from ctl_base's arodata_okS
     (B.ProgWorld.arodata_okP_of_S) and the journal's image clause.  No AR_states_vis0_shadow, no AR_states_owned_ro.
     No stage of this file reads shadow_rw at a cut: seg_F38 passes the cut's ctl_rt_C on unchanged (same state).
   - FP_nil : FP = [] (the top's CF instantiates FP := [] and discharges it by eq_refl): seg_F38's loop-head body
     carries the entry input block's bytes (f1_IN), which the journal keeps only off FP.
   Used by the proofs and not by any statement: B.ProgBridge's PROVED fevt_of_evtF / RNG_W / fp_avoids_RNG_W /
   rng_of_visible / rsegs_spans / img_vis_W (a Theorem Labs lane, frozen), cited by name where a proof needs them.
   `_F` HYPOTHESES (a Theorem Labs lane; module ..lib.B.Prog.Seg.<File>F; RNG-first; split at EVERY call).  PUBLISHED texts
   are cited by Requiring their module, qualified (a Theorem Labs lane 23:38Z / 23:4xZ).  All image-B `_F` are now on ONE branch,
   a working branch 12a7ea50807, cited from there; statuses as of
   bF-statements/ at 00:45Z:
   - F37F.f37_evt_F (a working branch d511d09bbd7; F37.v:292; the PRE-CALL stretch
     0x82ca0 -> the free wrapper entry 0x534b4, ra = 0x82d1c
     = the cut, so no post; rng premises `rng RNG (A + 224) 24` (the three spills) and `rng RNG (Sf + 22) 45` (the 23
     out-of-scope shadow marks))                                                                   PUBLISHED, proved
     Its auditor compare lemma is now f37_evt_of_F_bounded (+ f37_evt_of_F_shape), which adds bound premises on the
     spill base; this glue applies f37_evt_F itself, not the compare lemma, so no bound obligation arises here.
   - F38F.seg_F38_F (F38.v (not in this delivery) seg_F38, the inline latch 0x82d1c -> 0x81ec4 / 0x82eac; + seg_F38_run)
                                                                                               PUBLISHED, in progress
     (a Theorem Labs lane 22:46Z: a Theorem Labs lane cuts the run out of the segment proof; only if that fails does this lane walk it in cgif
     form, on a Theorem Labs lane's word.)  The arm j < 255 with left_(j+1) = 0 also runs 0x81ec4 -> 0x81ec8 -> 0x82eac (F38.v's (not in this delivery)
     header); that stretch is part of seg_F38's proof, so it is inside seg_F38_F's exit to 0x82eac (to check against
     the published text's Q when its status is proved).
   PROVENANCE: cut table rows 84-85; plan 2.3 rows 83-84, 2.5 (row 0x82d18), 3 (frame loop), 6.2 (no trap on W4g);
   runs at 3803efccea0 (F37.v, F38.v); objdump L85620-L85660.

   ABORT-SINK / TRAP OBLIGATIONS ON W4g (all branches into 0x82fa4 / 0x82fa0 in 0x82ca0-0x82d28 and on the F38 path
   0x81ec4-0x81ec8): ONE, 0x82ca4 `bne a0,s7,0x82fa4` (L85622), in S_F37.  No UBSan branch (plan 6.2). *)

From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
(* lib/Lib/Mem.v, Required only (never Imported), for the saved-register bytes in CHAIN_OF_CUT's premise. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's published `_F` modules (Required qualified, never Imported, a Theorem Labs lane 23:38Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F37F F38F.
(* Proofs only (Required, never Imported): ProgBridge's proved glue (a Theorem Labs lane, frozen: fevt_of_evtF, rsegs_spans),
   lib/Lib's register and machine-state vocabulary of the runs' start / end states, the core's shadow reader
   (YG0v), the core's byte reader (YP09.mbyte), inFP / val_mem (YI04), mem_grows (YK1b). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge Lib.Regs6ss.
(* a Theorem Labs lane's image-B ProgWorld layer (arodata_okP_of_S), the route-(C) runtime conjunct from AR
   (lib/B/ProgWorldCtlRtC.v: ctl_rt_C_of_AR) and the PA layer's arodata_okP (lib/B/Prog/CtrlBase.v). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldCtlRtC B.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI04 YK1b YP09 YO0f.
(* the fragment model's length facts (pure; Required only) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFragLib.
Import ListNotations.
Local Open Scope Z_scope.
Module RFL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFragLib.

Section W4g.

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
Local Notation C_B82ca0_at := (ACtlCutP.C_B82ca0_at B).
Local Notation C_B82d1c_at := (ACtlCutP.C_B82d1c_at B).
Local Notation C_B81ec4_at := (ACtlCutP.C_B81ec4_at B).
Local Notation C_B82eac := (ACtlCutP.C_B82eac B).

(* ---- Section hypotheses (sources in the header and in ACtlW0.v's) ---- *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* The core's allocator rule (named only in ctl_W4g_free_82d18), the trivial meter, B's free wrapper entry, AR_laws. *)
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule segs B MT.
Hypothesis HMOK : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis HPCF : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code B) = Reusable.YB1w.tfib_A_free.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

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

(* ---- RtPost, image B: the shared text of record of this walk (RTPOST-SHARED-B.txt (a working note, not in this delivery), author a Theorem Labs lane for
   a Theorem Labs lane), pasted token for token; only the members this file's lemmas take are here.  SOURCE of
   ctl_post_acall_kept: a Theorem Labs lane's lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:646-663; written on a working branch c03ce1627b6), with
   lib.Reusable -> Reusable, Lib.Mem -> lib.Lib.Mem and A.Img0 -> B.Img0 and nothing else; a Theorem Labs lane's kept_class Definition is a Local Notation
   here and its PROVED lemma a named Section hypothesis, as RTPOST-SHARED-B.txt (a working note, not in this delivery) states it (lib/B/ProgWorld.v:681
   proves the same statement over its kept_class Definition).
   AT THIS FILE'S SITE (0x82d18, S_F37): E is the freed block (phi, flen cx j) and [slo, shi) is the ASTACK window
   [c_sp cx + o - ASTACK, c_sp cx + o) of ctl_W4g_free_82d18 below. ---- *)

(* kept_class / ctl_post_acall_kept: lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:646-663; written on a working branch c03ce1627b6) (PROVED on A).  The ceiling is YM05's RunCeil field
   alloc_ceiling, as acall_kept (Reusable/YCbq.v:826) uses it; lyc / Sc are Reusable.YG0f.alayout /
   Reusable.YG00.astate (a Theorem Labs lane's kept_class binders; untyped in a Theorem Labs lane's lemma, fixed there by acall_kept).  At an
   allocator site: E = the new block (malloc) or the freed block (free), [slo, shi) = the ASTACK window
   [sp - ASTACK, sp). *)
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
Hypothesis ctl_post_acall_kept : forall (B : Reusable.YG0f.asyms) lyc Sc (W W2 : Reusable.YA0n.world segs)
    (memc mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop),
  Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E ->
  Reusable.YA0n.wle W W2 ->
  forall x : word, Reusable.YA0n.w_H W x = false -> kept_class B lyc Sc slo shi E (bv_unsigned x) ->
    lib.Lib.Mem.mrd B.Img0.rsegs mem2 x = lib.Lib.Mem.mrd B.Img0.rsegs memc x.

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
(* ---- end of the pasted RtPost members ---- *)

(* ctl_rt_C after the free comes from B.ProgWorldCtlRtC.ctl_rt_C_of_AR (route (C)), whose statement takes CtrlTSyms
   (plus AR_laws = LAWS).  Text = lib/B/ACtl.v's Section hypothesis of the same name; the top supplies it (Reusable.YD2l.CtrlB_syms). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.

(* The live-list step of the free: removing the turn block from a list that is the entry blocks plus that block
   leaves a permutation of the entry blocks (the sibling W2a's w2_perm_free).  Stdlib only. *)
Lemma w4g_perm_free : forall (E l1 l2 : list (Z * Z)) (x : Z * Z),
  Permutation (l1 ++ x :: l2) (E ++ [x]) -> Permutation (l1 ++ l2) E.
Proof.
  intros E l1 l2 x H.
  apply (Permutation_cons_inv (a := x)).
  apply (Permutation_trans (Permutation_middle l1 l2 x)).
  apply (Permutation_trans H).
  apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Generic stage helpers.  The first group is the sibling W2a's section 3b (a working branch 7cca696f747f,
   names w2_x renamed w4g_x), with ProgBridge's PROVED fevt_of_evtF in place of the FEVT hypothesis; then the frame
   loop's model facts one turn needs, and the byte-level bridges between the core's view and lib/Lib's reads. *)
Local Notation GR := lib.Reusable.YK11.getr.

(* The freed-block list is the empty one: the top runs the walk with FP := [] (lib/B/ACtl.v's CF notation, section 1),
   so it discharges this by eq_refl.  Used for the entry input block's bytes at the loop head (f1_IN). *)
Hypothesis FP_nil : FP = [].

Lemma w4g_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Ha).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin) as Hm.
  change Reusable.YB1v.tfibsegs with B.Img0.rsegs in Hm. rewrite B.ProgBridge.rsegs_spans in Hm.
  unfold Reusable.YG0f.kLowMemEnd.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma w4g_lift : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md (pc : Z)
    (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs RNG P
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None
       mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc RNG P Q Hrun Hav K.
  change (Reusable.YG0d.cfg_at segs pc regs mem md) with
    (mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md).
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W (Lib.Regs6ss.mkR_of regs) regs).
  2: exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs)).
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W _ md RNG P Q (B.ProgBridge.fevt_of_evtF RNG P _ Hrun) Hav).
  intros ms' md' HP Hhid Hsbm. apply (K ms' md' HP); [| exact Hsbm].
  intros x Hx. rewrite (Hhid x Hx). reflexivity.
Qed.

(* The journal across a run that writes nothing: only the model is materialized (YCbq.ajournal_exec, empty write
   set). *)
Lemma w4g_journal_mat : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w4g_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 md'
           (fun _ => False) HJ).
  - intros x _. reflexivity.
  - intros x Hx. exact Hx.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* FRAC reads the registers 2, 3, 4, 8, 9, 19 and 26 only. *)
Lemma w4g_frac_regs : forall (cx : ctlcx) (fr sel : Z) (regs R : bvmap 5 word) (m : word -> option byte),
  GR R 2 = GR regs 2 -> GR R 3 = GR regs 3 -> GR R 4 = GR regs 4 -> GR R 8 = GR regs 8 ->
  GR R 9 = GR regs 9 -> GR R 19 = GR regs 19 -> GR R 26 = GR regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel R m.
Proof.
  intros cx fr sel regs R m E2 E3 E4 E8 E9 E19 E26 H.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

(* A spill reads the registers only through its base, register 9; FLI also reads register 27. *)
Lemma w4g_spill_regs : forall (R regs : bvmap 5 word) (m : word -> option byte) (off v : Z),
  GR R 9 = GR regs 9 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m off v.
Proof. intros R regs m off v E9 H. unfold ACtlCutP.spill, ACtlCut.rgv in *. rewrite E9. exact H. Qed.

Lemma w4g_fli_regs : forall (cx : ctlcx) (fr : Z) (R regs : bvmap 5 word) (m : word -> option byte),
  GR R 9 = GR regs 9 -> GR R 27 = GR regs 27 -> ACtlCutP.FLI cx fr regs m -> ACtlCutP.FLI cx fr R m.
Proof.
  intros cx fr R regs m E9 E27 H. unfold ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv in *. rewrite E9, E27. exact H.
Qed.

Lemma w4g_rgv_move : forall (R regs : bvmap 5 word) (r : bv 5) (v : Z),
  GR R r = GR regs r -> ACtlCut.rgv regs r v -> ACtlCut.rgv R r v.
Proof. intros R regs r v E H. unfold ACtlCut.rgv in *. rewrite E. exact H. Qed.

(* A pinned register's unsigned value is the pin, when the pin is in [0, 2^64). *)
Lemma w4g_rgv_unsigned : forall (regs : bvmap 5 word) (r : bv 5) (v : Z),
  ACtlCut.rgv regs r v -> 0 <= v < 2 ^ 64 -> bv_unsigned (GR regs r) = v.
Proof.
  intros regs r v H Hv. unfold ACtlCut.rgv in H. rewrite H, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

(* ---- the frame loop's model over one turn (SlotModel's f_* functions) ---- *)
Lemma w4g_inb_nonneg : forall inp x, 0 <= ACtlCutP.SM.inb inp x.
Proof.
  intros inp x. unfold ACtlCutP.SM.inb.
  match goal with |- 0 <= _ ?b => exact (proj1 (bv_unsigned_in_range _ b)) end.
Qed.

(* Every turn's cursor c_j lies in [0, n]. *)
Lemma w4g_fc_bounds : forall inp j, 0 <= ACtlCutP.SM.fc inp j <= ACtlCutP.SM.nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [ACtlCutP.SM.fc].
  - unfold ACtlCutP.SM.c0, ACtlCutP.SM.nlen. lia.
  - pose proof (w4g_inb_nonneg inp (ACtlCutP.SM.fc inp j)) as H0.
    pose proof (w4g_inb_nonneg inp (ACtlCutP.SM.fc inp j + 1)) as H1.
    unfold ACtlCutP.SM.f_next, ACtlCutP.SM.f_body, ACtlCutP.SM.f_len, ACtlCutP.SM.f_h, ACtlCutP.SM.f_L,
      ACtlCutP.SM.f_left.
    destruct (2 <=? ACtlCutP.SM.nlen inp - ACtlCutP.SM.fc inp j); lia.
Qed.

Lemma w4g_t_left_S : forall inp j,
  ACtlCutP.SM.t_left inp (S j) = ACtlCutP.SM.t_left inp j - ACtlCutP.SM.t_h inp j - ACtlCutP.SM.t_len inp j.
Proof.
  intros inp j. unfold ACtlCutP.SM.t_left, ACtlCutP.SM.t_h, ACtlCutP.SM.t_len. cbn [ACtlCutP.SM.fc].
  unfold ACtlCutP.SM.f_left, ACtlCutP.SM.f_next, ACtlCutP.SM.f_body. lia.
Qed.

Lemma w4g_t_c_S : forall inp j,
  ACtlCutP.SM.t_c inp (S j) = ACtlCutP.SM.t_body inp j + ACtlCutP.SM.t_len inp j.
Proof. intros inp j. reflexivity. Qed.

Lemma w4g_t_left_c : forall inp j, ACtlCutP.SM.t_left inp j = ACtlCutP.SM.nlen inp - ACtlCutP.SM.t_c inp j.
Proof. intros inp j. reflexivity. Qed.

(* The identity record keeps its 38 bytes through every turn (the twin of Seg/F15.v's t_ID_length). *)
Lemma w4g_tID_length : forall inp j, length (ACtlCutP.SM.t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold ACtlCutP.SM.t_ID in *. cbn [ACtlCutP.SM.fst_at]. unfold ACtlCutP.SM.turn. cbv zeta.
  assert (Hr : length (ACtlCutP.SM.rp_id (ACtlCutP.SM.fs_id (ACtlCutP.SM.fst_at inp j)) (ACtlCutP.SM.t_len inp j)
                         (ACtlCutP.SM.t_g inp j)) = 38%nat).
  { unfold ACtlCutP.SM.rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply ACtlCutP.RIM.ING_length; exact IH | exact IH]. }
  assert (Hf : length (ACtlCutP.SM.fg_id (ACtlCutP.SM.rp_id (ACtlCutP.SM.fs_id (ACtlCutP.SM.fst_at inp j))
                         (ACtlCutP.SM.t_len inp j) (ACtlCutP.SM.t_g inp j)) (ACtlCutP.SM.t_len inp j)
                         (ACtlCutP.SM.fs_fg (ACtlCutP.SM.fst_at inp j)) (ACtlCutP.SM.t_g inp j)) = 38%nat).
  { unfold ACtlCutP.SM.fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply ACtlCutP.RIM.ING_length; exact Hr | exact Hr]. }
  destruct (ACtlCutP.SM.f_opens _ _); cbn [ACtlCutP.SM.fs_id]; exact Hf.
Qed.

(* ---- lists and byte reads ---- *)
Lemma w4g_nth_firstn : forall {X : Type} (l : list X) (n i : nat) (d : X),
  (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros X l. induction l as [|x l IH]; intros n i d Hi; destruct n as [|n]; try lia.
  - cbn. destruct i; reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma w4g_nth_skipn : forall {X : Type} (l : list X) (k i : nat) (d : X), nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros X l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct i; reflexivity | apply IH].
Qed.

Lemma w4g_nth_error_firstn : forall {X : Type} (l : list X) (n i : nat),
  (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X l. induction l as [|x l IH]; intros n i Hi; destruct n as [|n]; try lia.
  - cbn. destruct i; reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma w4g_bytes_at_firstn : forall (m : word -> option byte) (a : Z) (bs : list byte) (n : nat),
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H2). split; [exact H0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite (w4g_nth_error_firstn bs n i) by lia. apply H2. lia.
Qed.

Lemma w4g_find_byte_some : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> bv_unsigned (nth i l d) = 0 -> ACtlCutP.SFA.find_byte 0 l <> None.
Proof.
  induction l as [|b l IH]; intros i d Hi Hz; [cbn in Hi; lia|].
  cbn [ACtlCutP.SFA.find_byte]. destruct (bv_unsigned b =? 0) eqn:E; [discriminate|].
  destruct i as [|i]; [cbn in Hz; apply Z.eqb_neq in E; contradiction|].
  cbn [length nth] in Hi, Hz. specialize (IH i d ltac:(lia) Hz).
  destruct (ACtlCutP.SFA.find_byte 0 l); [discriminate | exfalso; apply IH; reflexivity].
Qed.

Lemma w4g_addressable_sub : forall (m : word -> option byte) (p n p' n' : Z),
  B.AsanRT.addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> B.AsanRT.addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & H1 & H2 & H3) Hp Hn' Hle. unfold B.AsanRT.addressable.
  split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (p' + i) with (p + (p' - p + i)) by lia. apply H3. lia.
Qed.

Lemma w4g_le_byte1 : forall v, 0 <= v < 256 -> lib.Reusable.YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold lib.Reusable.YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma w4g_signed_small : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

(* The core's view of a present byte is the raw byte, and so is lib/Lib's read. *)
Lemma w4g_aview_present : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.apresent H mem a ->
  exists b, mem (Z_to_bv 64 a) = Some b /\
    Reusable.YG0n.aview segs H mem a = Some (bv_unsigned b) /\
    lib.Lib.Mem.mrd segs mem (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros H mem a [Hh [b Hb]]. exists b. split; [exact Hb|]. split.
  - unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh, Hb. reflexivity.
  - unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

(* Off the image, a byte the core's view reads is a byte lib/Lib reads (a hidden byte reads None there). *)
Lemma w4g_mrd_of_aview : forall (H : word -> bool) (mem : word -> option byte) (a v : Z),
  0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  Reusable.YG0n.aview segs H mem a = Some v ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem a v Ha Hni Hv.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv.
  rewrite (Reusable.YCbq.seg_rom_none segs a Ha Hni) in Hv.
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  destruct (H (Z_to_bv 64 a)); [cbn in Hv; discriminate|].
  destruct (mem (Z_to_bv 64 a)) as [b|]; cbn in Hv; [|discriminate].
  injection Hv as Hv. exists b. split; [reflexivity | exact Hv].
Qed.

(* The entry input block at a frame-loop cut: its bytes and its shadow (ACtlCutP.f1_IN), from the pre's input facts,
   the journal's kept view of a live entry block (FP = []), the core's block and shadow laws, and n > 0. *)
Lemma w4g_f1_IN : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k,
  ctl_base cx -> AJ cx own ly3 S3 W3 mem3 md3 k ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx) -> 0 < ACtlCut.c_n cx ->
  ACtlCutP.f1_IN cx mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ Hperm Hn.
  pose proof HB as ((_ & _ & _ & _ & Hdisj & Hlen & Hgarr & _) & _).
  destruct Hdisj as [[E0 _] | [_ Hin0]]; [lia |].
  assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
    by exact (Permutation_in _ (Permutation_sym Hperm) Hin0).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & HF2 & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hpres & _ & Hnmax).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (Hbsh & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hceil _]. unfold Reusable.YG0f.ASAN_CEIL in Hceil.
  assert (Hreq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
  { unfold Reusable.YG00.req_size. destruct (ACtlCut.c_n cx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
  rewrite Hreq in Hpceil, Hpapp, Hpres, Hbsh.
  split.
  - (* the shadow: the core's block_shadow, read through lib/Lib *)
    unfold B.AsanRT.addressable.
    split; [lia|]. split; [lia|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
    intros i Hi. unfold B.AsanRT.addr_byte. split.
    + unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL in Hpapp.
      lia.
    + destruct Hbsh as (Hp8 & _ & Hsh).
      specialize (Hsh (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])).
      unfold Reusable.YG0v.shadow_of_addr in Hsh.
      assert (Esh : B.AsanRT.shadow_addr (ACtlCut.c_p cx + i) =
                    Reusable.YG0f.SHADOW_OFF + ACtlCut.c_p cx / 8 + i / 8).
      { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF. lia. }
      assert (Hsr : 0 <= Reusable.YG0f.SHADOW_OFF + ACtlCut.c_p cx / 8 + i / 8 < 2 ^ 64)
        by (unfold Reusable.YG0f.SHADOW_OFF; lia).
      assert (Hsi : ~ Reusable.YG0d.in_img segs (Reusable.YG0f.SHADOW_OFF + ACtlCut.c_p cx / 8 + i / 8)).
      { intros Himg. pose proof (w4g_segs_low _ Himg) as Hl.
        unfold Reusable.YG0f.kLowMemEnd, Reusable.YG0f.SHADOW_OFF in Hl. lia. }
      destruct (w4g_mrd_of_aview _ _ _ _ Hsr Hsi Hsh) as (b & Hb & Hbv).
      exists b. rewrite Esh. split; [exact Hb|].
      unfold B.AsanRT.shadow_ok.
      destruct (i / 8 <? ACtlCut.c_n cx / 8) eqn:Eg.
      * left. rewrite w4g_signed_small by lia. exact Hbv.
      * apply Z.ltb_ge in Eg. right. rewrite w4g_signed_small by (rewrite Hbv; lia). rewrite Hbv. lia.
  - (* the bytes: the journal keeps the entry view of the live input block, which the pre's garr8 states *)
    unfold lib.Lib.Mem.bytes_at.
    split; [lia|]. split; [rewrite <- Hlen; lia|].
    intros i Hi.
    assert (Hi' : 0 <= Z.of_nat i < ACtlCut.c_n cx) by (rewrite Hlen; lia).
    destruct (Hpres (ACtlCut.c_p cx + Z.of_nat i) ltac:(lia)) as [Hpr _].
    destruct (w4g_aview_present _ _ _ Hpr) as (b & _ & Hav & Hmrd).
    rewrite Hmrd.
    rewrite (HF2 _ _ (Z.of_nat i) Hin0 Hin3 ltac:(rewrite Hreq; lia)) in Hav.
    2: { rewrite FP_nil. apply lib.Reusable.YI04.inFP_nil. }
    destruct (Hgarr i ltac:(rewrite length_map; exact Hi)) as [Hv Hr].
    specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
    unfold Reusable.YG0n.aview in Hav. rewrite Hv in Hav. cbn [option_map] in Hav. injection Hav as Hbv.
    rewrite (nth_error_nth' (ACtlCut.c_in cx) (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. rewrite <- Hbv.
    rewrite (nth_indep (map (fun b0 : byte => bv_unsigned b0) (ACtlCut.c_in cx)) 0
               (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; exact Hi).
    rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth i (ACtlCut.c_in cx) (Z_to_bv 8 0))) as Hbr.
    change (bv_modulus 8) with 256 in Hbr.
    cbv beta.
    rewrite (w4g_le_byte1 _ Hbr). rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* The read-only data fact at any journalled state, in the PA layer's form ctl_rt_C_of_AR reads.  It follows
   Reusable.APostBase.arodata_ok_journalP's proof at an EMPTY PA range (rlo = rhi = 0; ctl_rt_C_of_AR quantifies
   RLO RHI, and only the read-only segments matter): the entry's arodata_okS (ctl_base's pre, YCfn.v:40) gives the PA
   form at the entry (B.ProgWorld.arodata_okP_of_S); a read-only segment byte is an image byte, so the journal's image
   clause (FP = [], nothing spared) keeps its view. *)
Lemma w4g_arodata_post : forall (cx : ctlcx) own ly' S' W' mem' md' k,
  ctl_base cx -> AJ cx own ly' S' W' mem' md' k ->
  B.Prog.CtrlBase.arodata_okP segs 0 0 B (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') mem').
Proof.
  intros cx own ly' S' W' mem' md' k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _) & _).
  pose proof (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Haro ltac:(lia) ltac:(lia)) as HP0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF3 & _).
  intros a Ha Hown Herr.
  destruct Ha as [(s & Hs & Hw & Hr) | Hr]; [| lia].
  rewrite (HF3 a ltac:(exists s; split; [exact Hs | exact Hr]) Hown Herr).
  - apply HP0; [left; exists s; split; [exact Hs | split; [exact Hw | exact Hr]] | exact Hown | exact Herr].
  - intros Ho. rewrite FP_nil in Ho. exfalso. exact (Reusable.YCbq.sink_closed_nil Ho).
Qed.

(* ---- seg_F37's helpers: the turn block is not an entry block; byte facts carried across a memory change by
   per-address read equalities; the frame-loop model's record lengths. ---- *)

(* A list on which an irreflexive relation holds pairwise has no duplicate (the sibling W2a's w2_pairwise_nodup). *)
Lemma w4g_pairwise_nodup : forall (X : Type) (R : X -> X -> Prop) (l : list X),
  Reusable.YG0f.pairwise R l -> (forall x, In x l -> ~ R x x) -> List.NoDup l.
Proof.
  intros X R l. induction l as [|x l IH]; cbn; intros Hp Hirr.
  - apply List.NoDup_nil.
  - apply List.NoDup_cons.
    + destruct Hp as [Hf _]. intros Hx. apply (Hirr x (or_introl eq_refl)).
      exact (proj1 (Forall_forall _ _) Hf x Hx).
    + destruct Hp as [_ Hp]. apply IH; [exact Hp |]. intros y Hy. apply Hirr. right. exact Hy.
Qed.

(* The turn block is not an entry block (the sibling W2a's w2_phi_not_entry): the live blocks are pairwise disjoint
   with req_size >= 1 (al_blocks), so (phi, n) cannot occur twice in a permutation of entry ++ [(phi, n)]. *)
Lemma w4g_phi_not_entry : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (phi n : Z),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, n)]) ->
  ~ In (phi, n) (ENTRYBL cx).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k phi n HJ Hperm Hin.
  destruct HJ as (HAR & _).
  assert (Hin3 : In (phi, n) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi n HAR Hin3) as (_ & _ & _ & _ & _ & Hpw & _).
  assert (Hnd : List.NoDup (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (List.NoDup_map_inv (fun b0 : Z * Z => (fst b0, Reusable.YG00.req_size (snd b0)))).
    apply (w4g_pairwise_nodup _ Reusable.YG0f.zdisjoint _ Hpw).
    intros x Hx. apply in_map_iff in Hx as ([p m] & <- & Hpm).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p m HAR Hpm) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (Reusable.YCbq.req_size_pos m (proj1 Hm)) as Hr.
    unfold Reusable.YG0f.zdisjoint. cbn [fst snd]. lia. }
  pose proof (Permutation.Permutation_NoDup Hperm Hnd) as Hnd2.
  apply (List.NoDup_remove_2 (ENTRYBL cx) [] (phi, n) Hnd2).
  rewrite app_nil_r. exact Hin.
Qed.

(* Bytes carried to another memory that reads the same at each of their addresses. *)
Lemma w4g_bytes_eq : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (a + i)) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (a + i))) ->
  lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H2) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite HE by lia. apply H2. exact Hi.
Qed.

(* Addressability carried to another memory that reads the same shadow bytes. *)
Lemma w4g_addr_eq : forall (m m' : word -> option byte) (p n : Z),
  B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H3) HE. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [|exact Hok]. rewrite <- Hb. exact (HE i Hi).
Qed.

(* A run of readable bytes is some byte list. *)
Lemma w4g_bytes_build : forall (m : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, lib.Lib.Mem.bytes_at segs m a bs /\ length bs = n.
Proof.
  intros m a n H0 H1 Hr.
  exists (map (fun i => match lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (a + Z.of_nat i)) with
                       | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [|reflexivity].
  split; [exact H0|]. split; [rewrite length_map, length_seq; exact H1|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map. rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
  destruct (Hr i Hi) as (b & Hb). rewrite Hb. reflexivity.
Qed.

(* A spill at the spill base A, when A is the register-9 pin. *)
Lemma w4g_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  ACtlCut.rgv regs 9 A -> 0 <= off -> off < A < 2 ^ 63 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HA Hoff HAr (A' & HA' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
    unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
    apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
    change (bv_modulus 64) with 18446744073709551616 in HA'. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite (Z.mod_small A) in HA' by lia. lia. }
  subst A'. exact Hq.
Qed.

Lemma w4g_spill_cross : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (off v A : Z),
  ACtlCut.rgv regs 9 A -> GR regs' 9 = GR regs 9 -> 0 <= off -> off + 8 <= 448 -> 448 < A < 2 ^ 63 ->
  (forall a, A <= a < A + 448 ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' off v A HA E9 Hoff1 Hoff2 HAr HE Hs.
  pose proof (w4g_spill_at regs m off v A HA Hoff1 ltac:(lia) Hs) as Hq.
  exists A. split; [exact (w4g_rgv_move regs' regs 9 A E9 HA)|].
  unfold ACtlCutP.q64 in *. apply (w4g_bytes_eq m m' _ _ Hq).
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. apply HE. lia.
Qed.

Lemma w4g_q64_ov : forall (m : word -> option byte) (a v : Z),
  ACtlCutP.q64 m a v -> ov_read_bytes B.Img0.rsegs m (lib.Lib.Mem.wa a) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold ACtlCutP.q64 in H.
  pose proof (lib.Lib.Mem.bytes_at_ov_read segs m a _ 0 8 H ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as E.
  pose proof (lib.Lib.Mem.length_le8 (Z_to_bv 64 v)) as L8.
  cbn [Z.of_nat] in E. rewrite Z.add_0_r in E. change (skipn 0 ?l) with l in E.
  rewrite firstn_all2 in E by lia. exact E.
Qed.

(* FLI carried across a memory change that keeps the spill area [A, A + 448), the owned frame's addressability
   bytes for [fr + 2624, fr + 2920), and gives the frame's stk and KNT afresh. *)
Lemma w4g_fli_cross : forall (cx : ctlcx) (fr : Z) (regs regs' : bvmap 5 word) (m m' : word -> option byte) (A : Z),
  ACtlCut.rgv regs 9 A -> GR regs' 9 = GR regs 9 -> GR regs' 27 = GR regs 27 -> 448 < A < 2 ^ 63 ->
  (forall a, A <= a < A + 448 ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)) ->
  (forall p n, B.AsanRT.addressable m p n -> fr + 2624 <= p -> p + n <= fr + 2920 -> B.AsanRT.addressable m' p n) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) -> ACtlCutP.KNT m' ->
  ACtlCutP.FLI cx fr regs m -> ACtlCutP.FLI cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' A HA E9 E27 HAr HE Had Hstk' HKNT' H.
  unfold ACtlCutP.FLI in *.
  destruct H as (H27 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & s12 & s13 & s14 & s15 & s16 & s17 &
                 s18 & s19 & s20 & s21 & Had2624 & _ & (R1 & R2 & R3) & _ & s22 & s23).
  assert (SC : forall off v, 0 <= off -> off + 8 <= 448 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v)
    by (intros off v H1 H2 Hs; exact (w4g_spill_cross regs regs' m m' off v A HA E9 H1 H2 HAr HE Hs)).
  split; [exact (w4g_rgv_move regs' regs 27 (-8) E27 H27)|].
  split; [apply SC; [lia | lia | exact s1]|]. split; [apply SC; [lia | lia | exact s2]|].
  split; [apply SC; [lia | lia | exact s3]|]. split; [apply SC; [lia | lia | exact s4]|].
  split; [apply SC; [lia | lia | exact s5]|]. split; [apply SC; [lia | lia | exact s6]|].
  split; [apply SC; [lia | lia | exact s7]|]. split; [apply SC; [lia | lia | exact s8]|].
  split; [apply SC; [lia | lia | exact s9]|]. split; [apply SC; [lia | lia | exact s10]|].
  split; [apply SC; [lia | lia | exact s11]|]. split; [apply SC; [lia | lia | exact s12]|].
  split; [apply SC; [lia | lia | exact s13]|]. split; [apply SC; [lia | lia | exact s14]|].
  split; [apply SC; [lia | lia | exact s15]|]. split; [apply SC; [lia | lia | exact s16]|].
  split; [apply SC; [lia | lia | exact s17]|]. split; [apply SC; [lia | lia | exact s18]|].
  split; [apply SC; [lia | lia | exact s19]|]. split; [apply SC; [lia | lia | exact s20]|].
  split; [apply SC; [lia | lia | exact s21]|].
  split; [apply Had; [exact Had2624 | lia | lia]|].
  split; [exact Hstk'|].
  split.
  { unfold ACtlCutP.RAD in *. split; [apply Had; [exact R1 | lia | lia]|].
    split; [apply Had; [exact R2 | unfold ACtlCutP.fragb; lia | unfold ACtlCutP.fragb; lia]|].
    apply Had; [exact R3 | lia | lia]. }
  split; [exact HKNT'|].
  split; [apply SC; [lia | lia | exact s22] | apply SC; [lia | lia | exact s23]].
Qed.

(* The frame loop's record lengths: the fragment state has 72 bytes (the twin of Seg/F15.v's t_FG_length, on the
   pure RcFragLib facts), the first-fragment body at most 23. *)
Lemma w4g_fg_next_length : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (ACtlCutP.SM.fg_next st g (ACtlCutP.SM.fcls len st g)) = 72%nat.
Proof.
  intros len st g HL HG. unfold ACtlCutP.SM.fcls, ACtlCutP.RFR.fg_class. cbn [Z.eqb orb].
  destruct (ACtlCutP.RFR.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [ACtlCutP.SM.fg_next]; exact HL].
  assert (Hn : 1 <= ACtlCutP.RFR.fg_n g <= 22).
  { unfold ACtlCutP.RFR.fg_fr in FR. rewrite !Bool.andb_true_iff in FR.
    destruct FR as (FR & _). destruct FR as (FR & Hn2). destruct FR as (_ & Hn1).
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia. }
  destruct (ACtlCutP.RFR.bat g 19 =? 1).
  - cbn [ACtlCutP.SM.fg_next]. unfold ACtlCutP.RFR.fg_first, ACtlCutP.RFR.fg_body.
    rewrite !length_app, length_skipn, (RFL.rf_bsl_length g 6 6), (RFL.rf_bsl_length g 27 (ACtlCutP.RFR.fg_n g))
      by lia.
    cbn [length]. lia.
  - destruct (ACtlCutP.RFR.fg_keep st g) eqn:KEEP; cbn [negb];
      [|cbn [ACtlCutP.SM.fg_next]; apply RFL.rf_clear_length; exact HL].
    assert (HT : ACtlCutP.RFR.fg_T st g <= 64).
    { unfold ACtlCutP.RFR.fg_keep in KEEP. rewrite !Bool.andb_true_iff in KEEP.
      destruct KEEP as (_ & HT). apply Z.leb_le in HT. exact HT. }
    destruct (ACtlCutP.RFR.fg_close st g); cbn [negb ACtlCutP.SM.fg_next];
      apply RFL.rf_clear_length, RFL.rf_fg_join_length; assumption.
Qed.

Lemma w4g_tFG_length : forall inp j, length (ACtlCutP.SM.t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold ACtlCutP.SM.t_FG in *. cbn [ACtlCutP.SM.fst_at]. unfold ACtlCutP.SM.turn. cbv zeta.
  pose proof (ACtlCutP.SM.fr50_length (ACtlCutP.SM.t_phi inp j)) as HG.
  destruct (ACtlCutP.SM.f_opens _ _); cbn [ACtlCutP.SM.fs_fg]; unfold ACtlCutP.SM.fg_st;
    apply w4g_fg_next_length; [exact IH | exact HG | exact IH | exact HG].
Qed.

Lemma w4g_fsbody_length : forall inp j, (length (ACtlCutP.SM.fs_body (ACtlCutP.SM.fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  cbn [ACtlCutP.SM.fst_at]. unfold ACtlCutP.SM.turn. cbv zeta.
  pose proof (ACtlCutP.SM.fr50_length (ACtlCutP.SM.t_phi inp j)) as HG.
  destruct (ACtlCutP.SM.f_opens _ _); cbn [ACtlCutP.SM.fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold ACtlCutP.SM.t_g. lia.
Qed.

(* IFS carried across a memory change that keeps the owned frame's bytes [fr + 2688, fr + 2920) and their
   addressability bytes. *)
Lemma w4g_ifs_cross : forall (cx : ctlcx) (fr : Z) (j : nat) (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  (forall a, fr + 2688 <= a < fr + 2920 ->
     lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa a)) ->
  (forall p n, B.AsanRT.addressable m p n -> fr + 2624 <= p -> p + n <= fr + 2920 -> B.AsanRT.addressable m' p n) ->
  ACtlCutP.IFS cx fr j regs m -> ACtlCutP.IFS cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' HE Had ((HID & Hok) & (HFG & Hfok) & (H80 & H84 & H85 & Had80 & HFI)).
  pose proof (w4g_tID_length (ACtlCut.c_in cx) j) as L1. pose proof (w4g_tFG_length (ACtlCut.c_in cx) j) as L2.
  pose proof (w4g_fsbody_length (ACtlCut.c_in cx) j) as L3.
  split; [split; [|exact Hok]|split; [split; [|exact Hfok]|]].
  - unfold ACtlCutP.IDBe in *. apply (w4g_bytes_eq m m' _ _ HID). intros i Hi. apply HE. rewrite L1 in Hi. lia.
  - unfold ACtlCutP.FGBe in *. apply (w4g_bytes_eq m m' _ _ HFG). intros i Hi. apply HE. rewrite L2 in Hi. lia.
  - split; [|split; [|split; [|split; [|exact HFI]]]].
    + unfold ACtlCutP.u32 in *. apply (w4g_bytes_eq m m' _ _ H80). intros i Hi. apply HE.
      rewrite lib.Lib.Mem.length_le4 in Hi. lia.
    + unfold ACtlCutP.b8 in *. apply (w4g_bytes_eq m m' _ _ H84). intros i Hi. apply HE. cbn [length] in Hi. lia.
    + apply (w4g_bytes_eq m m' _ _ H85). intros i Hi. apply HE. lia.
    + apply Had; [exact Had80 | lia | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The allocator site 0x82d18 (S_F37): the core's free rule at this site's constants, its continuation folded into the
   caller's; nothing else in the walk applies AFREE4 here.  Same shape as the sibling W2a's w2_free_81a9c.
   a0 = s2 = phi, ra = 0x82d1c, frames own6, live list entry ++ [(phi, flen cx j)] with phi not an entry block,
   k <= 14 + 2j + 1 with j <= 255 (so k <= 525), trace [0x535f4; 0x82d1c] (P5-universe.v.txt:55-56). *)
Lemma ctl_W4g_free_82d18 : forall (cx : ctlcx) (j : nat) (phi : Z) ly3 S3 W3 (regsT : bvmap 5 word) memT md3 k
    (o : Z) ch (Q : Reusable.YA0n.world segs -> config -> Prop),
  ctl_base cx ->
  AJ cx (own6 cx) ly3 S3 W3 memT md3 k ->
  k <= 14 + 2 * Z.of_nat j + 1 -> (j <= 255)%nat ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, flen cx j)]) ->
  ~ In (phi, flen cx j) (ENTRYBL cx) ->
  lib.Reusable.YK11.getr regsT 10 = Z_to_bv 64 phi ->
  Reusable.YG0d.spZ regsT = ACtlCut.c_sp cx + o -> o mod 16 = 0 -> -4096 < o <= -448 ->
  lib.Reusable.YK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 0x82d1c ->
  ACtlCut.ctl_chain ly3 W3 memT regsT ch ->
  ACtlCut.ctl_trace_in B (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) regsT ch ->
  (forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     Reusable.YA0n.wle W3 W2 ->
     AJ cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) ->
     Reusable.YG0d.aregs_preserved regsT regs2 ->
     Reusable.YG01.frames S2 = own6 cx ->
     Permutation (Reusable.YG0d.ablocks B ly2 S2) (ENTRYBL cx) ->
     Reusable.YCbq.acall_kept segs B ly3 S3 W3 memT W2 mem2
       (ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (ACtlCut.c_sp cx + o)
       (fun a => phi <= a < phi + Reusable.YG00.req_size (flen cx j)) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x82d1c regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_free regsT memT md3) Q.
Proof.
  (* The sibling W2a's w2_free_81a9c (a working branch d0e10c707373; the donor's free pattern A/ACf3.v:97-110)
     at this site's constants. *)
  intros cx j phi ly3 S3 W3 regsT memT md3 k o ch Q HB HJ Hk Hj Hperm Hnin Ha0 Hsp Ho16 Ho Hgp Htp Hra Hch Htr HK.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & _) & _).   (* tfib_lib_pre_x, YCfn.v:32-45 *)
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).                (* ajournal, YCbq.v:350-372 *)
  assert (Hin : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64. rewrite <- HPCF.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (AFREE4 W3 regsT memT Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
              (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
              (own6 cx) ly3 S3 md3 k phi (flen cx j) o (Z_to_bv 64 0x82d1c) ch HJ Hin).
    - exact Ha0.
    - exact Hsp.
    - exact Ho16.
    - lia.
    - unfold Reusable.YG0d.ASTACK, Reusable.YCfn.LLVMF_STK; lia.
    - exact Hgp.
    - exact Htp.
    - exact Hra.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - unfold Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *; lia.    (* st_nev S3 <= st_nev S + 525 *)
    - exact Hch.
    - exact Htr.
    - intros Hent. exfalso. exact (Hnin Hent).
    - apply HMOK. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfrs2 & HK2 & _).
  apply (HK W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2).
  - rewrite Hfrs2, Hfrs, Hfr0, app_nil_r. reflexivity.
  - rewrite E2. apply (w4g_perm_free (ENTRYBL cx) l1 l2 (phi, flen cx j)). rewrite <- E1. exact Hperm.
  - exact HK2.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82ca0_at j (0x82ca0) --S_F37--> B82d1c_at j.
   S_F37 (Seg/F37.v seg_F37 :762): s5 = [A + 240] = j; `bne a0,s7,0x82fa4` (the catalogue_match result against the row
   found); s7 = p + body_j + len_j, s9 = left_j - h_j - len_j; 23 shadow stores of 0xf8 into S(fr) + 22 .. 66 (the
   locals go out of scope); a0 = phi and free(phi) @0x82d18 returning at 0x82d1c. *)
Lemma seg_F37 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B82d1c_at [Z.of_nat j]) ->
  ctl_from POST (ix_cut C_B82ca0_at [Z.of_nat j]).
Proof.
  (* The body's pins feed F37F.f37_evt_F (0x82ca0 -> the free wrapper entry, ra = 0x82d1c, a0 = phi; its 23 stores
     write only the owned frame's shadow [S(fr) + 22, S(fr) + 67)), lifted with RNG_W (the spills and that shadow are
     visible).  The journal survives the run (ajournal_exec, write set in the owned frame's shadow).  The call is
     ctl_W4g_free_82d18 (chain / trace from CHAIN_OF_CUT).  After it, B82d1c_at's body: registers by aregs_preserved;
     every byte read through ctl_post_acall_kept at a visible address of a kept class (spills and saved bytes: high
     memory above the callee window; frame words, records and their shadow: the live frame off the freed block;
     KNT's bytes: the image arm, ctl_kind_name_not_owned); the frame's stk and KNT's addressability from the post-call
     AR (al_frames, ctl_kind_name_addressable); ctl_rt_C by B.ProgWorldCtlRtC.ctl_rt_C_of_AR (arodata_okP from
     w4g_arodata_post).  The sink branch 0x82ca4 is refuted inside the run (a0 = s7 = t_want j = t_want_m j). *)
  intros POST j H1c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HP HRT.
  destruct HP as [-> HBODY].
  cbn [ACtlCut.cut_body ACtlCut.cut_kmax ACtlCut.cut_pc ACtlCut.ix_cut ACtlCutP.C_B82ca0_at] in HBODY, Hk |- *.
  unfold ACtlCutP.ixn in HBODY, Hk. cbn [nth] in HBODY, Hk. rewrite Nat2Z.id in HBODY, Hk.
  destruct HBODY as (HFRAC & phi & Hperm & Hn & Hj255 & HHB & H18 & H20 & HFTURN & HLK & H272 & _ & H10 & H23 &
                     _ & _ & H152 & H160 & Hphib & Hphil & Hstk & Hwant & HIFS & H22).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
                       HspA & HfrA & HA448 & Hsp4096 & HcspE & Hq336 & Hq48 & Hq40 & Hqhdr & Hq16 & Hsh0 & Hsaved &
                       Hq4088).
  pose proof HLK as (_ & H240 & HOUR & HFLI).
  pose proof HFLI as (H27 & _).
  pose proof HFTURN as (H224 & H232 & _).
  pose proof HB as ((Hafn & _ & _ & _ & _ & _ & _ & Hfr0 & _) & _).
  pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstatic & _).
  pose proof Hstatic as (Hcsp16 & _ & Hceil_lo & Hlo_stk & Hsp_hi & Hhi47 & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hceil _]. unfold Reusable.YG0f.ASAN_CEIL in Hceil.
  unfold Reusable.YCfn.LLVMF_STK in Hlo_stk.
  (* the owned frame (6, fpos) at fr, its 4096 bytes and 512 shadow bytes present (al_frames) *)
  assert (Hfrs3' : Reusable.YG01.frames S3 = own6 cx) by (rewrite Hfrs3, Hfr0, app_nil_r; reflexivity).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs3'; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HFA; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Hfapp & Hfpres & Hfspres).
  rewrite Efr3, E4096 in Hfapp, Hfpres, Hfspres.
  (* the turn block (phi, flen cx j): live, in app memory, off the frame *)
  assert (Hinb : In (phi, flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hinb) as (_ & _ & _ & Hbapp & _).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (flen cx j) 6 (ACtlCut.c_fpos cx)
                HAR3 Hinb Hin6) as Hsep.
  rewrite Efr3, E4096 in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  pose proof (w4g_phi_not_entry cx (own6 cx) ly3 S3 W3 mem3 md3 k phi (flen cx j) HJ Hperm) as Hnin.
  (* the address arithmetic: S(fr) = shadow_addr fr in the shadow, the stack above the ceiling *)
  assert (ESf' : ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    lia. }
  assert (ESf : ACtlCutP.Sfr fr = 0x7fff8000 + fr / 8).
  { rewrite ESf'. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
  unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg
    in Hfapp, Hbapp.
  assert (HSfb : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 < lib.Reusable.YM05.alloc_ceiling) by lia.
  assert (Hcsp_b : lib.Reusable.YM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx <= 2 ^ 47) by lia.
  assert (HAr : 448 < A < 2 ^ 63) by lia.
  (* ---- the run 0x82ca0 -> 0x534b4 ---- *)
  assert (E27 : GR regs3 27 = Z_to_bv 64 (-8)) by exact H27.
  assert (E23 : GR regs3 23 = Z_to_bv 64 (ACtlCutP.SM.t_want (ACtlCut.c_in cx) j)) by (rewrite Hwant; exact H23).
  pose proof (w4g_spill_at regs3 mem3 240 _ A Hr9 ltac:(lia) ltac:(lia) H240) as Q240.
  pose proof (w4g_spill_at regs3 mem3 224 _ A Hr9 ltac:(lia) ltac:(lia) H224) as Q224.
  pose proof (w4g_spill_at regs3 mem3 232 _ A Hr9 ltac:(lia) ltac:(lia) H232) as Q232.
  assert (Hvis_sh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. destruct (Hfspres (a - Reusable.YG0f.shadow_addr fr) ltac:(rewrite <- ESf'; lia)) as [Hp _].
    replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hp by lia. exact Hp. }
  assert (HWR : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 22) 45).
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Hvis_sh (ACtlCutP.Sfr fr + 22 + i) ltac:(lia)) as (_ & b & Hb).
    unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate. }
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (RA : Lib.ExecF.rng RNG (A + 224) 24).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres3 a ltac:(unfold Reusable.YCfn.LLVMF_STK; lia))). }
  assert (RSh : Lib.ExecF.rng RNG (ACtlCutP.Sfr fr + 22) 45).
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hvis_sh a ltac:(lia))). }
  apply (w4g_lift W3 regs3 mem3 md3 0x82ca0 RNG _ (POST cx)
           (F37F.f37_evt_F RNG regs3 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 A (ACtlCutP.Sfr fr)
              (ACtlCutP.SM.t_want (ACtlCut.c_in cx) j) (Z.of_nat j)
              (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j)
              (ACtlCutP.SM.t_left (ACtlCut.c_in cx) j - ACtlCutP.SM.t_h (ACtlCut.c_in cx) j)
              (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) phi
              Hr9 H10 E23 H18 Hr19 H20 E27 ltac:(lia)
              ltac:(match goal with |- _ + ?F <= _ => replace F with 392 by reflexivity end; lia)
              (w4g_q64_ov _ _ _ Q240) (w4g_q64_ov _ _ _ Q224) (w4g_q64_ov _ _ _ Q232) HWR RA RSh)).
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (RT & memT & Ems & HRa & HR10 & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR20 & HR26 & HR27 &
                  HR22 & HR23 & HR25 & HR21 & Hmunch & Hwmono & Hread) Hhid Hsbm.
  subst ms'.
  assert (ER1 : GR RT 1 = Z_to_bv 64 0x82d1c) by exact HRa.
  assert (ER10 : GR RT 10 = Z_to_bv 64 phi) by exact HR10.
  assert (ER2 : GR RT 2 = GR regs3 2) by exact HR2.
  assert (ER3 : GR RT 3 = GR regs3 3) by exact HR3.
  assert (ER4 : GR RT 4 = GR regs3 4) by exact HR4.
  assert (ER8 : GR RT 8 = GR regs3 8) by exact HR8.
  assert (ER9 : GR RT 9 = GR regs3 9) by exact HR9.
  assert (ER19 : GR RT 19 = GR regs3 19) by exact HR19.
  assert (ER26 : GR RT 26 = GR regs3 26) by exact HR26.
  assert (ER27 : GR RT 27 = GR regs3 27) by exact HR27.
  assert (ER22 : GR RT 22 = GR regs3 22) by exact HR22.
  assert (ER23 : GR RT 23 = Z_to_bv 64 (ACtlCut.c_p cx + ACtlCutP.SM.t_body (ACtlCut.c_in cx) j +
                                      ACtlCutP.SM.t_len (ACtlCut.c_in cx) j)) by exact HR23.
  assert (ER25 : GR RT 25 = Z_to_bv 64 (ACtlCutP.SM.t_left (ACtlCut.c_in cx) j - ACtlCutP.SM.t_h (ACtlCut.c_in cx) j -
                                      ACtlCutP.SM.t_len (ACtlCut.c_in cx) j)) by exact HR25.
  assert (ER21 : GR RT 21 = Z_to_bv 64 (Z.of_nat j)) by exact HR21.
  (* the run's memory: outside the written shadow it is the cut's *)
  assert (HmT : forall a, 0 <= a < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 67) ->
            lib.Lib.Mem.mrd segs memT (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha Hout. unfold lib.Lib.Mem.mrd. rewrite (Hmunch (lib.Lib.Mem.wa a)); [reflexivity|].
    rewrite (lib.Lib.Mem.wa_unsigned a Ha). cbn [lib.Lib.Frame.outside]. split; [exact Hout | exact I]. }
  (* the journal after the run *)
  assert (HJT : AJ cx (own6 cx) ly3 S3 W3 memT md' k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS w4g_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memT md'
             (fun a => ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 67) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (Hmunch x); [reflexivity|].
      cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x) eqn:Ehx; [exact Hx|].
      destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 22) (bv_unsigned x)) as [Hlo|Hlo];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 67)) as [Hhi|Hhi]|].
      + (* inside the written shadow: no segment there, so the writable view is the raw byte *)
        assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
        { intros Himg. pose proof (w4g_segs_low _ Himg) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl. lia. }
        pose proof (Reusable.YCbq.find_segment_none segs (bv_unsigned x) Hni) as Hfs.
        assert (Hw3 : wview B.Img0.rsegs mem3 x <> None).
        { unfold wview. destruct (mem3 x); [discriminate | contradiction]. }
        pose proof (Hwmono x Hw3) as HwT. unfold wview in HwT. change B.Img0.rsegs with segs in HwT.
        rewrite Hfs in HwT. destruct (memT x); [discriminate | exact HwT].
      + rewrite (Hmunch x); [exact Hx|]. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
      + rewrite (Hmunch x); [exact Hx|]. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    - intros x Hx. exact (Hhid x Hx).
    - exact Hsbm.
    - intros a Ha. cbv beta in Ha. right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096, <- ESf'. lia. }
  (* ---- the call: free(phi) @0x82d18 ---- *)
  set (o := sp - ACtlCut.c_sp cx).
  assert (HspT : Reusable.YG0d.spZ RT = ACtlCut.c_sp cx + o).
  { unfold Reusable.YG0d.spZ in *. rewrite ER2, HspZ. unfold o. lia. }
  assert (Ho16 : o mod 16 = 0) by (unfold o; lia).
  assert (Ho : -4096 < o <= -448) by (unfold o; lia).
  assert (ERgp : GR RT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B)) by (rewrite ER3, Hr3; exact Hgp0).
  assert (ERtp : GR RT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B)) by (rewrite ER4; exact Hr4).
  assert (ER8c : GR RT 8 = Z_to_bv 64 (ACtlCut.c_sp cx)) by (rewrite ER8; exact Hr8).
  assert (Lsv : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
  assert (HsavedT : lib.Lib.Mem.bytes_at segs memT (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
  { apply (w4g_bytes_eq mem3 memT _ _ Hsaved). intros i Hi. rewrite Lsv in Hi. apply HmT; lia. }
  destruct (CHAIN_OF_CUT cx (own6 cx) ly3 S3 W3 memT md' k RT
              (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) 0x82d1c HB HJT ER8c ER1 HsavedT
              ltac:(rewrite HspT; unfold o; lia) ltac:(rewrite HspT; unfold o; lia)
              ltac:(right; right; right; left; reflexivity)) as (ch & Hch & Htr).
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_free RT memT md') (POST cx)).
  apply (ctl_W4g_free_82d18 cx j phi ly3 S3 W3 RT memT md' k o ch (POST cx) HB HJT Hk Hj255 Hperm Hnin
           ER10 HspT Ho16 Ho ERgp ERtp ER1 Hch Htr).
  intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2 Hfrs2 Hperm2 Hkept.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  (* ---- after the call: the callee-saved registers ---- *)
  assert (Q2 : GR regs2 2 = GR regs3 2).
  { rewrite <- ER2. exact (HP2 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q3 : GR regs2 3 = GR regs3 3).
  { rewrite <- ER3. exact (HP2 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q4 : GR regs2 4 = GR regs3 4).
  { rewrite <- ER4. exact (HP2 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q8 : GR regs2 8 = GR regs3 8).
  { rewrite <- ER8. exact (HP2 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q9 : GR regs2 9 = GR regs3 9).
  { rewrite <- ER9. exact (HP2 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q19 : GR regs2 19 = GR regs3 19).
  { rewrite <- ER19. exact (HP2 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q26 : GR regs2 26 = GR regs3 26).
  { rewrite <- ER26. exact (HP2 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q27 : GR regs2 27 = GR regs3 27).
  { rewrite <- ER27. exact (HP2 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q22 : GR regs2 22 = GR regs3 22).
  { rewrite <- ER22. exact (HP2 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)). }
  assert (Q21 : GR regs2 21 = GR RT 21) by exact (HP2 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (Q23 : GR regs2 23 = GR RT 23) by exact (HP2 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (Q25 : GR regs2 25 = GR RT 25) by exact (HP2 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  (* ---- after the call: the kept bytes (ctl_post_acall_kept at E = the freed block, [sp - ASTACK, sp)) ---- *)
  assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            kept_class B ly3 S3 (ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (ACtlCut.c_sp cx + o)
              (fun a => phi <= a < phi + Reusable.YG00.req_size (flen cx j)) a ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs memT (lib.Lib.Mem.wa a)).
  { intros a Ha Hv Hkc.
    pose proof (ctl_post_acall_kept B ly3 S3 W3 W2 memT mem2 _ _ _ Hkept Hwle (lib.Lib.Mem.wa a) Hv) as H.
    rewrite (lib.Lib.Mem.wa_unsigned a Ha) in H. exact (H Hkc). }
  assert (HST : forall a, A <= a < ACtlCut.c_sp cx ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. rewrite <- (HmT a ltac:(lia) ltac:(lia)).
    apply Hk2; [lia | exact (proj1 (Hpres3 a ltac:(unfold Reusable.YCfn.LLVMF_STK; lia))) |].
    left. split; [lia | unfold o; lia]. }
  assert (HFM : forall a, fr <= a < fr + 4096 ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. destruct (Hfpres a Ha) as [[Hv _] _].
    rewrite <- (HmT a ltac:(lia) ltac:(lia)).
    apply Hk2; [lia | exact Hv |].
    right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
    - left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3, E4096. lia.
    - cbv beta. lia. }
  assert (HFS : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs memT (lib.Lib.Mem.wa a)).
  { intros a Ha. destruct (Hvis_sh a Ha) as [Hv _]. apply Hk2; [lia | exact Hv |].
    right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096, <- ESf'. lia.
    - cbv beta. lia. }
  assert (HSH : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            ~ (ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 67) ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha Hout. rewrite (HFS a Ha). exact (HmT a ltac:(lia) Hout). }
  assert (HKN : forall a, ACtlCutP.KNA.KIND_NAME <= a < ACtlCutP.KNA.KIND_NAME + 112 ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. pose proof Ha as Ha'. unfold ACtlCutP.KNA.KIND_NAME in Ha'.
    rewrite <- (HmT a ltac:(lia) ltac:(lia)).
    apply Hk2; [lia | |].
    - destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
      unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI. lia.
    - right. right. left. split; [| exact (ctl_kind_name_not_owned a Ha)].
      assert (Hseg : In (0x9f000, 0x3000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
        by (rewrite B.ProgBridge.rsegs_spans; right; right; left; reflexivity).
      apply in_map_iff in Hseg as (sg & Esg & Hsg). injection Esg as E1 E2.
      exists sg. split; [exact Hsg|]. rewrite E1, E2. lia. }
  assert (HAD : forall p n, B.AsanRT.addressable mem3 p n -> fr + 2624 <= p -> p + n <= fr + 2920 ->
                 B.AsanRT.addressable mem2 p n).
  { intros p n Had Hp Hpn. apply (w4g_addr_eq mem3 mem2 p n Had). intros i Hi.
    pose proof Had as (_ & Hn0 & _).
    assert (Esa : B.AsanRT.shadow_addr (p + i) = ACtlCutP.Sfr fr + (p + i - fr) / 8).
    { unfold B.AsanRT.shadow_addr. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. lia. }
    rewrite Esa. apply HSH; lia. }
  (* the frame's stk and KNT, from the post-call AR *)
  assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
  { assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfrs2; left; reflexivity).
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
      as (_ & _ & Hfp2 & _).
    assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr).
    { rewrite Efr. unfold Reusable.YG0f.frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF.
      reflexivity. }
    rewrite Efr2, E4096 in Hfp2.
    unfold ACtlCutP.FRAME_BYTES. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfp2 a ltac:(lia)) as [[_ [b Hb]] _].
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  assert (HKNT2 : ACtlCutP.KNT mem2).
  { pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                        _ & _ & (HKb & _) & _).
    assert (Lkn : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
    split.
    - apply (w4g_bytes_eq mem3 mem2 _ _ HKb). intros i Hi. rewrite Lkn in Hi. apply HKN. lia.
    - exact (ctl_kind_name_addressable ly2 S2 W2 mem2 md2 HAR2). }
  (* the frame shadow's 392 bytes are readable after the call *)
  assert (HSH2 : exists sh', lib.Lib.Mem.bytes_at segs mem2 (ACtlCutP.Sfr fr) sh' /\
                             length sh' = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { destruct Hsh0 as (sh & Hsh & Hshl).
    change ACtlCutP.FRAME_SHADOW with 392 in *.
    apply (w4g_bytes_build mem2 (ACtlCutP.Sfr fr) (Z.to_nat 392)); [lia | lia |].
    intros i Hi. rewrite (HFS (ACtlCutP.Sfr fr + Z.of_nat i) ltac:(lia)).
    destruct Hsh as (_ & _ & Hsh3).
    pose proof (Hsh3 i ltac:(rewrite Hshl; lia)) as Hi3.
    rewrite (nth_error_nth' sh (Z_to_bv 8 0)) in Hi3 by (rewrite Hshl; lia).
    destruct (Hread (ACtlCutP.Sfr fr + Z.of_nat i) ltac:(lia) (ex_intro _ _ Hi3)) as (b & Hb).
    exists b. exact Hb. }
  (* ---- B82d1c_at j at k + 1 ---- *)
  apply (H1c cx [Z.of_nat j] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2 HFA).
  - cbn [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_B82d1c_at]. unfold ACtlCutP.ixn. cbn [nth].
    rewrite Nat2Z.id. lia.
  - split; [reflexivity|].
    cbn [ACtlCut.cut_body ACtlCutP.C_B82d1c_at]. unfold ACtlCutP.ixn. cbn [nth]. rewrite Nat2Z.id.
    split; [exact Hperm2|].
    split.
    { (* FRAC *)
      exists A, sp.
      split; [rewrite Q2; exact Hr2|]. split; [exact Hsp16|].
      split; [unfold Reusable.YG0d.spZ in *; rewrite Q2; exact HspZ|].
      split; [rewrite Q4; exact Hr4|]. split; [exact (w4g_rgv_move regs2 regs3 8 _ Q8 Hr8)|].
      split; [exact (w4g_rgv_move regs2 regs3 9 _ Q9 Hr9)|]. split; [rewrite Q3; exact Hr3|].
      split; [exact (w4g_rgv_move regs2 regs3 19 _ Q19 Hr19)|].
      split; [exact (w4g_rgv_move regs2 regs3 26 _ Q26 Hr26)|].
      do 8 (split; [assumption|]).
      unfold ACtlCutP.q64 in *.
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hq336); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi;
              apply HST; lia|].
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hq48); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi;
              apply HST; lia|].
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hq40); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi;
              apply HST; lia|].
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hqhdr); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi;
              apply HFM; lia|].
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hq16); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi;
              apply HFM; lia|].
      split; [exact HSH2|].
      split; [apply (w4g_bytes_eq mem3 mem2 _ _ Hsaved); intros i Hi; rewrite Lsv in Hi; apply HST; lia|].
      apply (w4g_bytes_eq mem3 mem2 _ _ Hq4088); intros i Hi; rewrite lib.Lib.Mem.length_le8 in Hi.
      apply HFM; lia. }
    split; [exact Hn|].
    split.
    { (* LK *)
      split; [exact Hj255|].
      split; [exact (w4g_spill_cross regs3 regs2 mem3 mem2 240 _ A Hr9 Q9 ltac:(lia) ltac:(lia) HAr
                       (fun a Ha => HST a ltac:(lia)) H240)|].
      split.
      - unfold ACtlCutP.OURb in *. apply (w4g_bytes_eq mem3 mem2 _ _ HOUR). intros i Hi.
        unfold ACtlCutP.SM.OUR in Hi. rewrite length_map, length_seq in Hi. apply HFM. lia.
      - exact (w4g_fli_cross cx fr regs3 regs2 mem3 mem2 A Hr9 Q9 Q27 HAr (fun a Ha => HST a ltac:(lia)) HAD
                 HSTK2 HKNT2 HFLI). }
    split; [exact (w4g_spill_cross regs3 regs2 mem3 mem2 272 _ A Hr9 Q9 ltac:(lia) ltac:(lia) HAr
                     (fun a Ha => HST a ltac:(lia)) H272)|].
    split; [exact I|].
    split; [exact (w4g_spill_cross regs3 regs2 mem3 mem2 224 _ A Hr9 Q9 ltac:(lia) ltac:(lia) HAr
                     (fun a Ha => HST a ltac:(lia)) H224)|].
    split; [unfold ACtlCut.rgv; rewrite Q21; exact ER21|].
    split; [unfold ACtlCut.rgv; rewrite Q23; exact ER23|].
    split; [unfold ACtlCut.rgv; rewrite Q25; exact ER25|].
    split; [exact (w4g_ifs_cross cx fr (S j) regs3 regs2 mem3 mem2 (fun a Ha => HFM a ltac:(lia)) HAD HIFS)|].
    exact (w4g_rgv_move regs2 regs3 22 1 Q22 H22).
  - exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly2 S2 W2 mem2 md2
             HAR2 (w4g_arodata_post cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) HB HJ2)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82d1c_at j (0x82d1c) --S_F38--> B81ec4_at (S j) | B82eac.
   S_F38 (Seg/F38.v seg_F38 :153): a3 = j + 1; `bne a3,256,0x81ec4` (back edge when j <> 255) else `j 0x82eac`; at the
   head 0x81ec4 `bnez s9` (left_(j+1)) decides between the turn S j and `j 0x82eac` (0x81ec8).  No store, no call. *)
Lemma seg_F38 : forall POST (j : nat),
  ctl_from POST (ix_cut C_B81ec4_at [Z.of_nat (S j)]) ->
  ctl_from POST C_B82eac ->
  ctl_from POST (ix_cut C_B82d1c_at [Z.of_nat j]).
Proof.
  (* The body's pins feed F38F.seg_F38_F (registers a0 / a3 only, no memory access: the empty footprint); its post's
     two exits are the latch to B81ec4_at (S j) (j < 255, left_(j+1) <> 0) and the exit to B82eac (j = 255, or
     left_(j+1) = 0 through 0x81ec4 / 0x81ec8).  Memory, journal, frames and the cut's ctl_rt_C are unchanged. *)
  intros POST j Hhead Hexit cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HP HRT.
  destruct HP as [-> HBODY].
  cbn [ACtlCut.cut_body ACtlCut.cut_kmax ACtlCut.cut_pc ACtlCut.ix_cut ACtlCutP.C_B82d1c_at] in HBODY, Hk |- *.
  unfold ACtlCutP.ixn in HBODY, Hk. cbn [nth] in HBODY, Hk. rewrite Nat2Z.id in HBODY, Hk.
  destruct HBODY as (Hperm & HFRAC & Hn & HLK & H272 & _ & H224 & H21 & H23 & H25 & HIFS & H22).
  pose proof HLK as (Hj255 & H240 & HOUR & HFLI).
  pose proof HB as ((_ & _ & _ & _ & _ & Hlen & _) & _).
  (* the model: left_(j+1) = n - c_(j+1) lies in [0, n] *)
  pose proof (w4g_fc_bounds (ACtlCut.c_in cx) (S j)) as Hfc.
  assert (EnL : ACtlCut.c_n cx = ACtlCutP.SM.nlen (ACtlCut.c_in cx)) by (unfold ACtlCutP.SM.nlen; exact Hlen).
  set (Lz := ACtlCutP.SM.t_left (ACtlCut.c_in cx) j - ACtlCutP.SM.t_h (ACtlCut.c_in cx) j
             - ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) in H25.
  assert (ELz : Lz = ACtlCutP.SM.t_left (ACtlCut.c_in cx) (S j)) by (unfold Lz; rewrite w4g_t_left_S; reflexivity).
  assert (HLz : 0 <= Lz <= ACtlCut.c_n cx).
  { rewrite ELz, w4g_t_left_c. unfold ACtlCutP.SM.t_c. lia. }
  (* the run 0x82d1c -> 0x81ec4 | 0x82eac *)
  pose proof (F38F.seg_F38_F (fun _ _ => False)
    (GR regs3 1) (GR regs3 2) (GR regs3 3) (GR regs3 4) (GR regs3 5) (GR regs3 6) (GR regs3 7) (GR regs3 8)
    (GR regs3 9) (GR regs3 10) (GR regs3 11) (GR regs3 12) (GR regs3 13) (GR regs3 14) (GR regs3 15)
    (GR regs3 16) (GR regs3 17) (GR regs3 18) (GR regs3 19) (GR regs3 20) (GR regs3 21) (GR regs3 22)
    (GR regs3 23) (GR regs3 24) (GR regs3 25) (GR regs3 26) (GR regs3 27) (GR regs3 28) (GR regs3 29)
    (GR regs3 30) (GR regs3 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
    (Z.of_nat j) Lz H21 H25 ltac:(lia) ltac:(lia)) as Hrun.
  apply (w4g_lift W3 regs3 mem3 md3 0x82d1c (fun _ _ => False) _ (POST cx) Hrun).
  { intros a n []. }
  intros ms' md' (a0' & a3' & pc' & Ems & Hcase) _ Hsbm. subst ms'.
  match goal with |- context [lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (R' := R) end.
  pose proof (w4g_journal_mat cx (own6 cx) ly3 S3 W3 mem3 md3 md' k HJ Hsbm) as HJ'.
  assert (E2 : GR R' 2 = GR regs3 2) by reflexivity.
  assert (E3 : GR R' 3 = GR regs3 3) by reflexivity.
  assert (E4 : GR R' 4 = GR regs3 4) by reflexivity.
  assert (E8 : GR R' 8 = GR regs3 8) by reflexivity.
  assert (E9 : GR R' 9 = GR regs3 9) by reflexivity.
  assert (E19 : GR R' 19 = GR regs3 19) by reflexivity.
  assert (E22 : GR R' 22 = GR regs3 22) by reflexivity.
  assert (E23 : GR R' 23 = GR regs3 23) by reflexivity.
  assert (E25 : GR R' 25 = GR regs3 25) by reflexivity.
  assert (E26 : GR R' 26 = GR regs3 26) by reflexivity.
  assert (E27 : GR R' 27 = GR regs3 27) by reflexivity.
  assert (E13 : GR R' 13 = a3') by reflexivity.
  pose proof (w4g_frac_regs cx fr fr regs3 R' mem3 E2 E3 E4 E8 E9 E19 E26 HFRAC) as HFRAC'.
  pose proof (w4g_fli_regs cx fr R' regs3 mem3 E9 E27 HFLI) as HFLI'.
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hs280 & _ & Hs176 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & HRAD & _).
  destruct Hcase as [[Epc Hex] | (Epc & Hjne & HL0 & Ha3)]; subst pc'.
  - (* the exit to B82eac *)
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x82eac R' mem3 md') (POST cx)).
    apply (Hexit cx [] fr k ly3 S3 W3 R' mem3 md' HB HJ' Hfr HFA).
    + cbn [ACtlCut.cut_kmax ACtlCutP.C_B82eac]. unfold B.ACtlK.EV_LLVMF. lia.
    + cbn [ACtlCut.cut_body ACtlCutP.C_B82eac].
      split; [exact Hperm|]. split; [exact HFRAC'|]. split; [exact Hn|]. split; [exact HOUR|].
      split; [exact (w4g_spill_regs R' regs3 mem3 176 (fr + 2688) E9 Hs176)|].
      split.
      * (* the identity record's first 21 bytes, with the 0 byte at 19 (id_ok) among the 17 name bytes *)
        destruct HIFS as ((HIDb & HIDok) & _ & _).
        pose proof (w4g_tID_length (ACtlCut.c_in cx) (S j)) as HL38.
        set (idb := ACtlCutP.SM.t_ID (ACtlCut.c_in cx) (S j)) in HIDb, HIDok, HL38.
        exists (firstn 21 idb).
        split; [exact (w4g_bytes_at_firstn mem3 (fr + 2688) idb 21 HIDb)|].
        split; [rewrite length_firstn, HL38; reflexivity|].
        destruct HIDok as (_ & _ & _ & H19 & _).
        apply (w4g_find_byte_some _ 16 (Z_to_bv 8 0)).
        -- rewrite length_firstn, length_skipn, length_firstn, HL38. lia.
        -- rewrite w4g_nth_firstn by lia. rewrite w4g_nth_skipn. rewrite w4g_nth_firstn by lia. exact H19.
      * destruct HRAD as (H2688 & _ & _).
        exact (w4g_addressable_sub mem3 (fr + 2688) 38 (fr + 2691) 17 H2688 ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact HRT.
  - (* the latch to B81ec4_at (S j) *)
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81ec4 R' mem3 md') (POST cx)).
    apply (Hhead cx [Z.of_nat (S j)] fr k ly3 S3 W3 R' mem3 md' HB HJ' Hfr HFA).
    + cbn [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_B81ec4_at]. unfold ACtlCutP.ixn. cbn [nth].
      rewrite Nat2Z.id. lia.
    + split; [reflexivity|].
      cbn [ACtlCut.cut_body ACtlCutP.C_B81ec4_at]. unfold ACtlCutP.ixn. cbn [nth]. rewrite Nat2Z.id.
      split; [exact Hperm|]. split; [exact HFRAC'|]. split; [exact Hn|].
      split.
      * (* LI cx fr (S j) *)
        split; [lia|]. split.
        { unfold ACtlCut.rgv. rewrite E13, Ha3. f_equal. lia. }
        split; [exact HOUR|]. split.
        { unfold ACtlCutP.CUR. split; [unfold ACtlCutP.SM.t_c; lia|]. split.
          - apply (w4g_rgv_move R' regs3 23 _ E23). rewrite w4g_t_c_S. unfold ACtlCut.rgv in *. rewrite H23.
            f_equal. lia.
          - apply (w4g_rgv_move R' regs3 25 _ E25). unfold ACtlCut.rgv in *. rewrite H25.
            f_equal. rewrite ELz, w4g_t_left_c, EnL. reflexivity. }
        split; [rewrite <- ELz; lia|]. split; [exact HIFS | exact HFLI'].
      * split; [exact (w4g_f1_IN cx (own6 cx) ly3 S3 W3 mem3 md' k HB HJ' Hperm ltac:(lia))|].
        split; [exact (w4g_spill_regs R' regs3 mem3 280 (fr + 176) E9 Hs280)|].
        exact (w4g_rgv_move R' regs3 22 1 E22 H22).
    + exact HRT.
Qed.

End W4g.

(* Stage lemmas of this file, all closed by Qed (type-checked with the workspace stand-ins of u19build.sh);
   [j] abbreviates [Z.of_nat j]:
     ctl_W4g_free_82d18 : the allocator site (statement above)
     seg_F37 (B82ca0_at) : forall POST j, ctl_from POST (ix_cut C_B82d1c_at [j]) -> ctl_from POST (ix_cut C_B82ca0_at [j])
     seg_F38 (B82d1c_at) : forall POST j, ctl_from POST (ix_cut C_B81ec4_at [Z.of_nat (S j)]) -> ctl_from POST C_B82eac ->
                           ctl_from POST (ix_cut C_B82d1c_at [j])
   Each seg_* is named and stated exactly as ACtl.v's Hypothesis of the same name, generic in SK; FP enters only
   through the named Section hypothesis FP_nil (FP = [], the top's instance).
   Sink / trap obligations: 0x82ca4 (`bne a0,s7`) -> 0x82fa4, refuted inside F37F.f37_evt_F's run (a0 = s7 =
   t_want j = t_want_m j, the body's pins). *)
