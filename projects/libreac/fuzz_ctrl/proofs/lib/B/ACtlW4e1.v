(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* lib/B/ACtlW4e1.v -- piece W4e1 (S_F18 .. S_F23, cut-table-B.tsv rows 61-67: B82634_at j .. B82844_at j) of
   fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.
   One writer: a Theorem Labs lane's glue lane.  rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one stage lemma per cut of the piece, in the donor's continuation shape
   (rt_A2 A/ACf0.v:173, rt_B A/ACf1.v:499, rt_C A/ACf2.v:402, rt_D A/ACf3.v:311 at c8557374ad2e): "the successor
   cuts hold -> this cut holds", over lib/B/ACtlCut.v's ctl_from and lib/B/ACtlCutP.v's cut records.  Every cut
   here lies inside the frame loop (loop_frames, head B81ec4_at j), so every stage is stated POINTWISE in the turn
   j with ACtlCut.ix_cut X [Z.of_nat j] (a Theorem Labs lane 22:47Z; a Theorem Labs lane's form, ctl_from_ix proved in ACtlCut.v), which is
   what the frame-loop induction of W4g / the top consumes.  Each stage lemma carries the NAME of its stage hypothesis
   in lib/B/ACtl.v (seg_F18 .. seg_F23, ACtl.v:555-576 at 576147dfd46) and its statement is that hypothesis's once the
   top instantiates SK := Reusable.YE2k.tfib_sink_head and FP := [] (ACtl.v:171-177), so the top cites
   ACtlW4e1.seg_F18 .. directly.
     B82634_at j (0x82634) --S_F18-->  B8264c_at j (bcmp @0x82648)  |  B82abc_at j (t_8819 j = false, silent)
     B8264c_at j (0x8264c) --S_F19-->  B82668_at j (bcmp @0x82664)
     B82668_at j (0x82668) --S_F20-->  B82728_at j (reac_ctrl_checksum_verify @0x82724)
     B82728_at j (0x82728) --S_F21-->  B827f8_at j (silent)  |  B82844_at j (reac_ctrl_headamp_record_verify @0x82840)
     B827f8_at j (0x827f8) --S_F22-->  B8283c_at j (silent; the 6-turn record-sum loop inside the stretch)
     B8283c_at j (0x8283c) --S_F22t-> B82844_at j (reac_ctrl_headamp_record_verify @0x82840)
     B82844_at j (0x82844) --S_F23-->  B82878_at j (__asan_memcpy @0x82870, then `li s7,1`)
   No allocator site, no fake-stack call: k and the frame list are unchanged on every stage (kmax 14 + 2j + 1 on
   both sides).  The successor sets are the plan's (llvmf-B-walk-plan.md 2.3 rows 61-67) and the segment headers'
   (UB Seg/F18.v-F23.v :1-40).

   ROUTE (lead FINAL 22:18Z via a Theorem Labs lane 22:29Z, route (a); brief bwalk-piece.md (a working note, not in this delivery))
   Each stage is GLUE over a footprint form of ctrl's already-proved v1.9 segment run: (1) from the cut body derive
   the `_F` stretch's entry premises and its rng premises, (2) prove fp_avoids (w_H W) RNG from the world facts,
   (3) lift with a Theorem Labs lane's kit (Reusable.YA0nR.SRr_fsteps / SRr_fevt, bridge-stmt.md:77-89 (a working note, not in this delivery), proved at
   a working branch eea54967566) after ProgBridge's fevt_of_evtF, (4) at a call, the callee's contract
   (runtime: the CORE's SRr-form rule by the donor's name; program callee: its stated `_contract_F`), (5) in the
   continuation re-establish the successor's body, journal, frames, k and ctl_rt.  No `_F` steps a callee
   (a Theorem Labs lane's bF-brief.md:36-43 (a working note, not in this delivery), a Theorem Labs lane 22:28Z).  Not used, by rule: a top, W_cutfree_ok, a cut-free twin, an
   LSCPS join.

   BUILD STATE (route (C), a Theorem Labs lane DECISION 09:20Z; shell a working branch, where ctl_from carries
   B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 in place of ctl_rt mem3).  All seven stage lemmas (seg_F18, seg_F19, seg_F20,
   seg_F21, seg_F22, seg_F22t, seg_F23) close with Qed (u19build on a build machine and the cbrec build of record; each
   push's report names the build log and the Print Assumptions log; the named audit is lib/B/AuditW4e1.v (not in this delivery)).  The two
   program callees are cited by their route (C) `_contract_F_on` proofs (HCKV_F, HHRV_F), so no stage needs the
   whole shadow.  What a stage does not prove is a NAMED Section hypothesis with its OBLIGATION / OWNER comment;
   every helper is a proved lemma.  No Axiom, no Parameter, no Admitted, no Abort.  The ONE place that names the
   shell's argument lists is the SHELL BINDING block below.

   THE FRAME TIE (a Theorem Labs lane's G1, now a premise of ctl_from in the re-twinned shell, lib/B/ACtlCut.v:239 in the
   worktree): for every owned (cid, pos), fr = Reusable.YG0f.frame_addr (c_ly cx) cid pos.  The stages here use it
   wherever a stretch writes the frame or its shadow (S_F23: S(fr)+16 / +17 and [fr+128, fr+140)), to show the
   write is awr_byte's owned-frame case and its range is visible (fp_avoids); it is named HG1 in the plans.

   SECTION HYPOTHESES (source of each text):
   - tfibsegs_rsegs, Hwx: the one segment bridge `tfibsegs_rsegs : Reusable.YB1v.tfibsegs = Img0.rsegs`, by its
     lib/B/ProgBridge.v name (settled with two Theorem Labs lanes ~23:40Z; still a Section hypothesis (:267), though ProgBridge.v:146
     lands) and the kit's once-per-unit `wx_segs_nowrap segs` (bridge-stmt.md (a working note, not in this delivery)).
   - LAWS, segs_low: the core's AR laws and image placement, the Section hypotheses of the donor YCbq.v Section d0
     (:813-814) that aj_bcmp_at / aj_intrin_at / ajournal_exec take; the donor supplies them from TfibLib
     (A/ACf0.v:39-43); ctrl B's CtrlBB record (plan M11, ACtlK) will.
   - ctl_rt_C (route C): after a program callee whose post is a raw munch, by the proved transport w4k_ctlrt_run
     (B.ShadowRwOnT.shadow_rw_on_mem_mono on both shadow conjuncts); after a WORLD call (the bcmp of seg_F18 /
     seg_F19, the memcpy of seg_F23), by the PROVED B.ProgWorldCtlRtC.ctl_rt_C_of_AR through w4_ctlrt, with
     TFIB_SYMS, RELRO_IMG and RO_OFL (no AR_states_vis0_shadow, no AR_states_owned_ro).
   - B_bcmp_tramp_entry / H_bcmp: the bcmp TRAMPOLINE's shared SRr-form contract, owned by a Theorem Labs lane (porter
     a Theorem Labs lane 23:17Z via another Theorem Labs lane): the trampoline composed onto cgif's interceptor body contract, in the core's
     abcmp_realizes shape (donor YG0d.v:352-371; AsanAPI field aa_bcmp :542), at the entry B_bcmp_tramp_entry
     (intended: the core's `bcmp_tramp` in lib/Reusable/YTramp.v (not in this delivery), image B 0x42aac; never the literal here).  The
     stage consumes it through the core's journal-form rule aj_bcmp_at (YCbq.v:2060-2079).  Name and sha come with
     a Theorem Labs lane's statement; until then H_bcmp in that shape.
   - AMEMCPY: the CORE's memcpy rule by the donor's name, aintrin_realizes OCpy (YG0d.v:317-335; AsanAPI field
     aa_asan_memcpy :537), consumed through aj_intrin_at (YCbq.v:1953-1975) as the donor's rt_C does (A/ACf2.v:51,
     :250-252), at the donor catalogue's name Reusable.YB1w.tfib_A_asan_memcpy (donor root lib/YB1w.v:148 at
     c8557374ad2e; the B core relocates it to __asan_memcpy 0x52164, plan F.3 row 15 (a working note, not in this delivery); a Theorem Labs lane 23:2xZ: cite the name
     now, image B's planning core lands ~00:30Z).
   The `_F` stretches stop at the literal entries of ctrl's run text (0x42aac, 0x52164); they meet
   B_bcmp_tramp_entry / YB1w.tfib_A_asan_memcpy when those are the core's names (definitionally those values).
   - HCKV_F: reac_ctrl_checksum_verify's route (C) footprint contract, by name:
     B/Prog/reac_ctrl_checksum_verify_c.v:111 `reac_ctrl_checksum_verify_contract_F_on` (shadow_rw premise dropped),
     proved as reac_ctrl_checksum_verify_F_holds_on (reac_ctrl_checksum_verify_F.v:101; the three files by path from
     a working branch 0d7160552d5).
   - HHRV_F: reac_ctrl_headamp_record_verify's route (C) footprint contract, by name:
     B/Prog/reac_ctrl_headamp_record_verify_c_on.v:65 `reac_ctrl_headamp_record_verify_contract_F_on` (shadow_rw
     premise dropped), proved as reac_ctrl_headamp_record_verify_holds_F_on (reac_ctrl_headamp_record_verify_F_on.v:27;
     both by path from a Theorem Labs lane c19d457ab68).  It has no callee hypothesis and no rng_bytes premise, and it lifts
     WHOLE through ProgBridge.fevt_of_evtF + the kit (the callee makes no runtime or fake-stack call).  Used by
     seg_F21 (exit 2) and seg_F22t.
   `_F` RUNS (a Theorem Labs lane's bF-statements/<File>F.md (working notes, not in this delivery); module OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.<File>F;
   RNG-first binder; conclusion ExecF.evtF rsegs RNG Q (MState.MS ..)).  Names per bF-brief.md:36-43 (a working note, not in this delivery) and the run
   inventory bseg-runs.tsv rows 109-116 (a working note, not in this delivery).  By the GLUE CLOSURE RULE
   (porter 23:38Z) this file Requires a Theorem Labs lane's `_F` modules QUALIFIED and uses their lemmas directly: no
   `_F` text is copied here, and no statement of this file names a frame-route identifier.  AC.GT (porter 23:40Z):
   neither F18F lemma cited mentions AC.GT; a stage that applies an `_F` that does gets the one lemma
   `AC.GT = Reusable.YImgTop.IMG_TOP` and rewrites with it, so its statements say IMG_TOP only.
   CITED (proved, bF-statements/F18F.md 23:13Z):
   - B.Prog.Seg.F18F.f18_pre_F       (Seg/F18.v:342 f18_evt, 0x82634 -> 0x42aac with ra = 0x8264c)
   - B.Prog.Seg.F18F.f18_evt_skip_F  (Seg/F18.v:439, 0x82634 -> 0x82abc, no call)
   NOT USED: F18F.f18_post_F (the empty stretch at the return pc 0x8264c, which is the cut B8264c_at itself; its
   munch premise is ctrl's 4560-byte wrapper window, not what the core's bcmp post gives, so the continuation reads
   C_B8264c_at's body directly off aj_bcmp_at's post).
   CITED (proved, bF-statements/F19F.md, F20F.md, F21F.md, F22F.md, read ~23:50Z / ~00:10Z; none mentions AC.GT):
   - B.Prog.Seg.F19F.f19_pre_F       (Seg/F19.v:108 f19_evt, 0x8264c -> 0x42aac with ra = 0x82668)
   - B.Prog.Seg.F20F.seg_F20_pre_F   (seg_F20's inline stretch, Seg/F20.v:538-616; 0x82668 -> 0x83b94 with
                                      ra = 0x82728, no store)
   - B.Prog.Seg.F21F.seg_F21_F       (seg_F21's inline stretch, Seg/F21.v:662-766; 0x82728 -> 0x827f8 when the record
                                      bytes are 4 / 3, else -> 0x8283c, the head-amp call site; no store, no call)
   - B.Prog.Seg.F22F.seg_F22_F       (0x827f8 -> 0x8283c, the whole stretch; f22_loop_F inside)
   - B.Prog.Seg.F22F.seg_F22t_pre_F  (0x8283c -> 0x858e4 with ra = 0x82844; used by seg_F22t AND by seg_F21's
                                      second arm, which reaches 0x8283c inside its own stage)
   NOT USED, as f18_post_F: f19_post_F (the empty stretch at the cut 0x82668), seg_F20_post_F (at the cut 0x82728),
   seg_F22t_post_F (at the cut 0x82844).  F21F has no `_pre_F`: its call is F22F's (F21F.md:6-9).
   CITED (proved, bF-statements/F23F.md:12-56, :101-123 and route (C) :125-185):
   - B.Prog.Seg.F23F.f23_pre_F_on    (0x82844 -> 0x52164 = ASAN_MEMCPY with ra = 0x82874; shadow_rw premise
                                      DROPPED, HRTnew / post `forall P, shadow_rw_on P m -> shadow_rw_on P _`;
                                      it states `AC.GT <= D`, which w4e1_gt_img_top below rewrites)
   - B.Prog.Seg.F23F.f23_li_F        (F23F.md (a working note, not in this delivery); the one step `li s7,1` at the memcpy return pc,
                                      0x82874 -> 0x82878, s7 := 1 and every other register kept, the SAME memory
                                      on both sides, NO memory premise and no rng premise, so it is the step the
                                      world-form memcpy can be followed by)
   NOT USED: F23F.f23_post_F (F23F.md:65-96 (a working note, not in this delivery); unchanged by a Theorem Labs lane): its premise is a raw munch, which the world-form
   memcpy post cannot give (rule ~00:45Z (2)); f23_li_F runs its one instruction instead.
   Every image-B `_F` module cited here is proved on ONE branch, a working branch 12a7ea50807
   (lib/B/Prog/Seg/<File>F.v), now also in this tree (Required at :185-186).
   (The `_post_F` of a call whose return pc is the next cut is the empty stretch and is not used, as f18_post_F.)
   CLOSURE (rule (3)-(4)): the frame-route files reached through the `_F` modules must be the v1.9 blobs of record:
   lib/B/Prog/SlotModel.v de18d111c37, SlotInv.v dfc10b8f7a4 (23a791566db = UB 3803efccea0), AsanRT.v
   32e0f5191fd, Contract.v 65b05173b1a, and the Seg sources at UB 3803efccea0 (Seg/F18.v ca8603bbf01, F20.v
   9f1728fca25, F21.v 20a1f323863, F23.v 239425eb4a7 (F23F.md:3 (a working note, not in this delivery)); the blobs a Theorem Labs lane re-runs; Seg/F18.v-F23.v are
   not in 23a791566db or the union).
   No lib/AZ/AsanW, W6 or cut-free file.  The lib/AZ files the closure reaches (measured by a Require walk over this
   branch at d0225cddfc9) are exactly: lib/AZ/LibA/AcctCore.v (blob 0e06d81d553 (the blob this tree had at release c5e779efe8c)) through lib/Lib/ExecF.v:11
   38b86b5d83a (the blob this tree had at release c5e779efe8c), and lib/AZ/Spec/AsanCtrl.v 80ffbfc0a07, AsanCtrlProps.v b4f333a2672, STree.v 1293d54ecd2 through
   lib/B/Contract.v (65b05173b1a), which every Seg source Requires.  All four are allowed in the closure only
   (porter 00:24Z / 00:25Z); no statement or hypothesis here names any of them.
   PENDING KIT / BRIDGE FACTS (named so the build pass knows what each step consumes.  The
   ProgWorld members below ARE published (lib/B/ProgWorld.v) and none of the members below is stated above as a Section hypothesis; ProgBridge's ajournal_after_munch is published nowhere;
   lib/B/ProgWorld.v (owner a Theorem Labs lane) and ProgBridge.v are in the tree, Required :205 / :196):
   - ProgBridge.fevt_of_evtF (bridge-stmt.md:101-102): ExecF.evtF rsegs RNG P ms -> exists ms', fsteps .. /\ P ms';
   - the transports T5 / T7 / T10 / V1-V6 of plan (a working note, not in this delivery) (a Theorem Labs lane, M5): range_addressable / shadow_hull_vis from
     ctrl's `addressable`, apartness from the core's 2 * ESTACK window, visibility of the spill area, the frame, the
     turn's block and the image cells;
   - ProgBridge's ajournal_after_munch (plan M3) where a stretch writes; here the core's own ajournal_exec
     (YCbq.v:634) is used through w4_after_run below, which needs only the write set.
   - the posts of the two WORLD calls are the core rules' own posts (YCbq.aj_bcmp_at, YCbq.aj_intrin_at): the
     journal at the new memory, the view kept outside the written range and the callee window, presence kept, and
     (memcpy) the view of the destination equal to the view of the source.  No ProgWorld runtime-call hypothesis
     (ctl_post_bcmp / ctl_post_memcpy) is used: every carried byte is read back over a VISIBLE address through
     aview_vis_mrd (proved below), and the copied bytes through w4_copy_byte.
   - img_vis_W (image-B ProgBridge) is cited for the image bytes the stages read: KIND_NAME's 112 bytes and the
     memcpy source `__const.check_ports.ports` at 0x21180.

   PROVENANCE: cut table cut-table-B.tsv rows 61-67 (lines 62-68) (a working note, not in this delivery); cut
   records lib/B/ACtlCutP.v (6d691a975b6); plan llvmf-B-walk-plan.md 2.3 rows 61-67, 2.4, F.2 rows 32-33, F.3 rows 15 and 22-23, 6.2, F.4.1 rows 41-52 (a working note, not in this delivery);
   ctrl's runs at
   a working branch 3803efccea0 (Seg/F18.v-F23.v); objdump
   fuzz_ctrl.objdump.txt L85210-L85355 (a working note, not in this delivery).

   MODEL: the cut bodies are drafted against image B's v1.9 SlotModel (blob de18d111c37 by path from 23a791566db:
   SM.CAT = 0x9f620, fstate with fs_n / fs_body, joined_byte; porter ruling via a Theorem Labs lane ~23:30Z), which this branch
   carries since the shell re-twin (lib/B/Prog/SlotModel.v blob de18d111c37 at 576147dfd46). *)

From Coq Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* the register reader lib/Lib's mkR_of and the `_F` runs name (the core's getr is it on every register but x0) *)
From LinuxProcessSemantics.Riscv Require Sem.
(* The six modules that lib/B/Reusable shadows (YI04 YI16 YK11 YK1b YM05 YO09) are Required through the CORE
   path lib.Reusable, never through `lib Require Reusable.X`, which matches both copies (porter a Theorem Labs lane
   04:33Z amendment (b)); every use below writes them `lib.Reusable.X.n`. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG01 Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ACtlK B.ACtlCut B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState PropExec.
(* lib/Lib's raw-memory vocabulary of the call-post facts below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step Mem.
(* the register-map equivalence the kit's SRr_xregs_eqv moves a cut state through (Regs6ss is not doubled) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
(* w4_vis_high's core fact: no read-only image byte at or above the image top 0x5fe000 (YF0x.seg_rom_none_high).
   NOT YD1y.not_in_img_high: YD1y Requires YE22 -> YE2y, whose icpt_rodata_chk vm_compute fails on the walk line
   adc9b58a03c, so YD1y would pull a broken core file into this closure. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0x.
(* a Theorem Labs lane's `_F` modules, Required qualified (glue closure rule, porter 23:38Z); the files land with a Theorem Labs lane's batch *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F18F B.Prog.Seg.F19F B.Prog.Seg.F20F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F21F B.Prog.Seg.F22F B.Prog.Seg.F23F.
(* AC.GT = IMG_TOP (w4e1_gt_img_top) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Contract Reusable.YImgTop.
(* the callee contract file of HCKV_F AND its proof, route (C) form (reac_ctrl_checksum_verify_contract_F_on /
   reac_ctrl_checksum_verify_F_holds_on, by path from 0d7160552d5): HCKV_F is discharged by name, not a hypothesis *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_checksum_verify_F.
(* The footprint vocabulary of the `_F` runs, and image-B's ProgBridge (a Theorem Labs lane, merged at 6fe149485c2):
   fevt_of_evtF, RNG_W / fp_avoids_RNG_W / rng_RNG_W / range_visible, img_vis_W.  These are PROVED on this
   branch, so the walk cites them by name instead of hypothesising them (porter's glue closure rule). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF B.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.ImgBounds Prog.RcLeaf Prog.RcModel.
(* the bcmp trampoline's entry constant (owner ruling a Theorem Labs lane 06:15Z: B_bcmp_tramp_at names it, no literal), and
   the two modules the w4k_ toolkit reads (AsanRTFacts.in_shadow_range; YG0v's range_addressable / saddr_ok) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.bcmp_wrap_c B.AsanRTFacts B.Prog.Seg.Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0v.
(* ctl_rt_C after a world call: the PROVED B.ProgWorldCtlRtC.ctl_rt_C_of_AR (route C; no vis0 / owned_ro premise),
   the read-only view keep APostBase.arodata_ok_journalP, and TFIB_SYMS's type YF0m.CtrlTSyms; the cut form
   B.ACtlRtC (ctl_rt_C, cut_shadow, img_shadow) and its transports B.ShadowRwOn / B.ShadowRwOnT / B.Prog.MemMono *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ShadowRwOn B.ShadowRwOnT B.Prog.MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.YF0m.
(* the PROVED B.ProgWorld_Fs.ctl_frame_above_img (rule a Theorem Labs lane 13:12Z: cite a proved ProgWorld statement) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld_Fs.
(* the callee contract of HHRV_F in its route (C) form and its proof (a Theorem Labs lane c19d457ab68, taken by path) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_headamp_record_verify_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_headamp_record_verify_F_on.
(* seg_F23: the memcpy callee constant, image B's memory normalization (lib.B.MemNorm / lib.B.MemNormF, the copies
   the `_F` statements use; f23_pre_F needs mem_inv, which ctl_rt does not carry, so the run is taken at
   `normalize rsegs m` and carried back by MemNormF.evtF_normalize_ro), the model facts of UB Seg/F23 and SlotInv
   (both already in the closure through F23F), and rng_asan's 8-aligned shadow cover. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memcpy_c B.MemNorm B.MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F23 B.Prog.SlotInv B.Prog.rng_asan.
Import ListNotations.
Local Open Scope Z_scope.

(* F23F's f23_pre_F states `AC.GT <= D` (F23F.md:24).  Porter 23:40Z: ONE lemma AC.GT = IMG_TOP, rewritten inside the
   stage proof, so no statement or hypothesis of this file says AC.GT.  Both sides are the literal 0x5fe000
   (lib/B/Contract.v:73 `Definition GT : Z := 0x5fe000`; YImgTop IMG_TOP).  Proof-internal, Qed. *)
Lemma w4e1_gt_img_top : B.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof. reflexivity. Qed.

Section W4e1.

(* The shell's contexts and variables, in its order (lib/B/ACtlCut.v section CtlCut after the 22:47Z re-twin).
   SK is the core's sink head; the top instantiates it EXPLICITLY with Reusable.YE2k.tfib_sink_head (a Theorem Labs lane
   22:39Z / 22:45Z); nothing here relies on instance resolution. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists.  At the re-twin, fix the
   argument lists here and nowhere else. ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ctl_base := (ACtlCut.ctl_base B MT XM_LIB RLO RHI).
Local Notation ix := ACtlCut.ix_cut.
Local Notation C_B82634_at := (ACtlCutP.C_B82634_at B).
Local Notation C_B8264c_at := (ACtlCutP.C_B8264c_at B).
Local Notation C_B82668_at := (ACtlCutP.C_B82668_at B).
Local Notation C_B82728_at := (ACtlCutP.C_B82728_at B).
Local Notation C_B827f8_at := (ACtlCutP.C_B827f8_at B).
Local Notation C_B8283c_at := (ACtlCutP.C_B8283c_at B).
Local Notation C_B82844_at := (ACtlCutP.C_B82844_at B).
Local Notation C_B82878_at := (ACtlCutP.C_B82878_at B).
Local Notation C_B82abc_at := (ACtlCutP.C_B82abc_at B).
(* ctl_from's journal premise, verbatim (ACtlCut.v section 5), as one name for the helpers below. *)
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).

(* (No lib/Lib notation block: the `_F` lemmas are used by their qualified names, never pasted.) *)

(* ---- Section hypotheses (sources in the header) ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* ctl_rt_C after a WORLD call (the bcmp of seg_F18 / seg_F19, the memcpy of seg_F23), route (C) (a Theorem Labs lane DECISION
   09:20Z; shell a working branch).  The stages cite the PROVED B.ProgWorldCtlRtC.ctl_rt_C_of_AR
   (statement ctl_rt_C_of_AR_stmt B: CtrlTSyms + AR_laws + AR + arodata_okP) through w4_ctlrt below; its read-only
   premise arodata_okP at the cut / post state comes from ctl_base's arodata_okS by ProgWorld.arodata_okP_of_S and
   APostBase.arodata_ok_journalP.  The facts that route takes, with lib/B/ACtl.v's names and texts (owner of every
   discharge: the walk's top):
   - TFIB_SYMS (ACtl.v:157): ctl_rt_C_of_AR_stmt's CtrlTSyms premise;
   - RELRO_IMG (ACtl.v:152): arodata_ok_journalP's relro_img;
   - RO_OFL (a Theorem Labs lane 06:46Z, a Context so arodata_ok_journalP finds the instance): every read-only byte and [RLO, RHI)
     lies below the sink's ofl_head; the top proves it by computation at SK := Reusable.YE2k.tfib_sink_head
     (ofl_head 0x5fcd48).
   After a program callee whose post is a raw munch (seg_F20, seg_F21, seg_F22t) ctl_rt_C is kept by the proved
   transport w4k_ctlrt_run instead (accepted by the owner 06:46Z). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* The bcmp trampoline (a Theorem Labs lane's shared contract, abcmp_realizes shape; entry a Section variable until
   YTramp lands) and the core's memcpy rule at the donor catalogue's name.  B_bcmp_tramp_at: the entry is image
   B's bcmp wrapper constant B.Prog.bcmp_wrap_c.BCMP_WRAP (owner ruling a Theorem Labs lane 06:15Z, text exact; owner of
   the discharge: the walk's top). *)
Variable B_bcmp_tramp_entry : Z.
Hypothesis B_bcmp_tramp_at : B_bcmp_tramp_entry = B.Prog.bcmp_wrap_c.BCMP_WRAP.
Hypothesis H_bcmp : Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry.
Hypothesis AMEMCPY :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy.

(* aview_vis_mrd: lib/A/ProgWorld.v :556-559 (a version not in this delivery; at head lib/A/ProgWorld.v:564-567) (PROVED on A).  PROVED HERE as well, as image B's form of that statement (B.Img0.rsegs and image B's segs where A has A.Img0.rsegs and image A's segs): at a visible address
   mrestrict is the identity and the core's mbyte (YP09.v:18) and lib/Lib's mrd (Mem.v:52) have the same body,
   so the two readers agree definitionally once tfibsegs_rsegs reads segs as rsegs.  It is therefore NOT a
   Section hypothesis of this file; when lib/B/ProgWorld.v lands its aview_vis_mrd is the same statement. *)
Lemma aview_vis_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Ha.
  unfold Reusable.YG0n.aview, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte.
  rewrite Ha. rewrite tfibsegs_rsegs. reflexivity.
Qed.

(* HCKV_F -- reac_ctrl_checksum_verify @0x82724 (entry 0x83b94): its ROUTE (C) footprint contract
   `reac_ctrl_checksum_verify_contract_F_on` (lib/B/Prog/reac_ctrl_checksum_verify_c.v:111, the old `_contract_F`
   with its `shadow_rw m` premise DROPPED).  NOT a hypothesis: its proof `reac_ctrl_checksum_verify_F_holds_on`
   (reac_ctrl_checksum_verify_F.v:101) is on this branch (the three files by path from a Theorem Labs lane,
   a working branch 0d7160552d5, cbrec v6 VERDICT ok) and is cited by name.  The 04:29Z pattern
   rule: a callee's contract_F premise is discharged by the callee's proved theorem, never by a lift lemma. *)
Lemma HCKV_F : B.Prog.reac_ctrl_checksum_verify_c.reac_ctrl_checksum_verify_contract_F_on.
Proof. exact B.Prog.reac_ctrl_checksum_verify_F.reac_ctrl_checksum_verify_F_holds_on. Qed.

(* HHRV_F -- reac_ctrl_headamp_record_verify @0x82840 (entry 0x858e4): its ROUTE (C) footprint contract
   `reac_ctrl_headamp_record_verify_contract_F_on` (lib/B/Prog/reac_ctrl_headamp_record_verify_c_on.v:65, the old
   `_contract_F` of reac_ctrl_headamp_record_verify_c.v:43 with its `shadow_rw m` premise DROPPED).  NOT a
   hypothesis: its proof `reac_ctrl_headamp_record_verify_holds_F_on` (reac_ctrl_headamp_record_verify_F_on.v:27) is
   in this file's closure (both files taken by path from a working branch
   c19d457ab68, on its accepted 0d31eaafd82), so it is cited by name as HCKV_F is.  (Before route (C) this was a
   named Section hypothesis over the old `_contract_F` text, a Theorem Labs lane 11:04Z ruling (a); the `_F_on` text takes no
   shadow fact, so nothing in it needs the top.)  Used by seg_F22t, and by seg_F21 through seg_F22t. *)
Lemma HHRV_F : B.Prog.reac_ctrl_headamp_record_verify_c_on.reac_ctrl_headamp_record_verify_contract_F_on.
Proof. exact B.Prog.reac_ctrl_headamp_record_verify_F_on.reac_ctrl_headamp_record_verify_holds_F_on. Qed.

(* img_vis_W, the walk's image-visibility bridge, in the shared block's shape (lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) at
   a working branch 61ccf7a7f5f) but PROVED here, because its owner's lemma is already on
   this branch: B.ProgBridge.img_vis_W (a Theorem Labs lane's image-B ProgBridge, merged at 6fe149485c2), whose bounds
   B.Prog.ImgBounds.IMG_LO / IMG_HI are the same two numbers as the core's Reusable.YImgTop.IMG_LO / IMG_TOP.
   Used by seg_F23 for the twelve read-only source bytes at 0x21180. *)
Lemma img_vis_W : forall W : Reusable.YA0n.world segs,
  0 <= Reusable.YImgTop.IMG_LO /\
  Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) <= 2 ^ 64 /\
  forall a, Reusable.YImgTop.IMG_LO <= a <
              Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) ->
    Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W. unfold B.ProgBridge.range_visible in *.
  destruct (B.ProgBridge.img_vis_W W) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ctl_kind_name_addressable -- pasted token for token from the shared block lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) at
   a working branch 61ccf7a7f5f (added by the text's one writer a Theorem Labs lane, 04:35Z).
   OBLIGATION: FLI's KNT conjunct `B.AsanRT.addressable m B.ACtlCutP.KNA.KIND_NAME 112`, which every LK cut
   carries, crosses a runtime call only through AR: the image's shadow is allocator-owned (YG0f.v:298-299), so
   no kept class and no visible-munch argument reaches those shadow bytes.
   OWNER: a Theorem Labs lane (lib/B/ProgBridgeData.v, proved there at :768), over a Theorem Labs lane's regenerated tables.
   Used by seg_F18 / seg_F19 (bcmp) and seg_F23 (memcpy), which carry LK across the call. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* seg_F23's bridge facts.
   - ctl_frame_above_img (B.ProgWorld section 18): a live fake frame lies above the image top 0x5fe000.  NOT a
     hypothesis (rule a Theorem Labs lane 13:12Z): B.ProgWorld.ctl_frame_above_img_stmt B is PROVED on this branch as
     B.ProgWorld_Fs.ctl_frame_above_img (lib/B/ProgWorld_Fs.v (at head lib/B/ProgWorld_Fs.v:539), Section Fs; from a working branch a2ab7f5988a), cited by
     name below.  Used by seg_F23 for f23_pre_F_on's AC.GT <= fr + 128, ASAN_K + 0x4240 <= Sfr fr, RT_HI <= fr + 128.
   - ctl_ports_addressable / ctl_ports_shadow_vis (texts accepted token for token into lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) by
     its writer a Theorem Labs lane, relayed by a Theorem Labs lane 08:3xZ; the literal 0x21180 stays, there is no named constant): the
     memcpy source `__const.check_ports.ports` (0x21180, 12 bytes) is addressable and its 8-aligned shadow cover is
     visible, as AR states the global's zero shadow (the image's shadow is allocator-owned, so no kept class
     reaches it).  OBLIGATION: those two facts at every AR state.  OWNER: a Theorem Labs lane (same file and tables as
     ctl_cat_addressable / ctl_cat_shadow_vis).  Neither is a ProgWorld `_stmt`; no B proof of either text is on
     a working branch a2ab7f5988a. *)
Lemma ctl_frame_above_img : B.ProgWorld.ctl_frame_above_img_stmt B.
Proof. exact (B.ProgWorld_Fs.ctl_frame_above_img B). Qed.
Hypothesis ctl_ports_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md, Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem 0x21180 12.
Hypothesis ctl_ports_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md, Reusable.YG0n.AR segs B ly S W mem md -> B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.Prog.rng_asan.sh_al8_lo 0x21180) (B.Prog.rng_asan.sh_al8_hi 0x21180 12 - B.Prog.rng_asan.sh_al8_lo 0x21180).

(* The F18 stretches are a Theorem Labs lane's proved lemmas B.Prog.Seg.F18F.f18_pre_F / f18_evt_skip_F, used directly. *)

(* ---------------------------------------------------------------------------------------------------------
   Helpers shared by the W4e1 / W4e2 / W4f stages.  (If a Theorem Labs lane opens the shared generic translation file of
   plan section 5, these three move there unchanged.) *)

(* H1. The core's configuration at a pc is ctrl's MState.MS state under tfibsegs_rsegs: YK11.mkst and MState.MS build the
   same record (FP registers and fcsr from the Section's fx), and YK11.seg_rom / PropExec.seg_rom have the same
   body (the SHADOWED NAMES rule of ACtlCut.v: they are different constants, equal by conversion only). *)
Lemma w4_cfg_MS : forall (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  Reusable.YG0d.cfg_at segs pc regs mem md =
  mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
           (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md.
Proof. intros pc regs mem md. rewrite <- tfibsegs_rsegs. reflexivity. Qed.

(* H2. The kit lift, keeping what the stage's journal step needs: the run's post, the materialized model, and the
   hidden bytes unchanged (YK04R.fsteps_restrict's second conjunct). *)
Lemma w4_lift : forall (W : Reusable.YA0n.world segs) (ms : machine_state) (md : Model)
    (RNG : Z -> nat -> Prop) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  (exists ms', Reusable.YK04R.fsteps segs RNG ms ms' /\ P ms') ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md RNG P Q Hex Hav K.
  exact (Reusable.YA0nR.SRr_fevt_hid segs Hwx W ms md RNG P Q Hex Hav
           (fun ms' md' HP Hhid Hsbm => K ms' md' HP Hsbm Hhid)).
Qed.

(* H2b. The same lift for an `_F` run, which concludes Lib/ExecF's evtF: ProgBridge.fevt_of_evtF turns it into
   the kit's `exists ms', fsteps .. /\ P ms'`, and the footprint is the largest one the world admits,
   ProgBridge.RNG_W (w_H W), whose fp_avoids is ProgBridge.fp_avoids_RNG_W.  Each `rng RNG lo len` premise of
   the run is then one visibility fact (w4_rng_vis below). *)
Lemma w4_lift_F : forall (W : Reusable.YA0n.world segs) (ms : machine_state) (md : Model)
    (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P ms ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md P Q Hevt K.
  apply (w4_lift W ms md (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P Q);
    [| apply B.ProgBridge.fp_avoids_RNG_W | exact K].
  (* segs (= YB1v.tfibsegs) is convertible to B.Img0.rsegs, so fevt_of_evtF's rsegs result closes the goal. *)
  exact (B.ProgBridge.fevt_of_evtF (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P ms Hevt).
Qed.

(* The visibility fact a run's `rng RNG lo len` premise becomes under RNG_W. *)
Lemma w4_rng_vis : forall (W : Reusable.YA0n.world segs) (lo len : Z),
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W lo len H0 H1 H2.
  exact (B.ProgBridge.rng_RNG_W (Reusable.YA0n.w_H W) lo len H0 H1 H2).
Qed.

(* H3. The continuation after a stretch: the successor's ctl_from applies once the journal is moved across the
   stretch's writes Wr by the core's ajournal_exec (YCbq.v:634-660).  Frames and k do not move (no allocator, no
   fake-stack event on any stage of W4e / W4f). *)
Lemma w4_after_run : forall POST (X : ACtlCut.ctlcut) cx idx (fr k : Z) ly3 S3 (W3 : Reusable.YA0n.world segs)
    (mem3 : word -> option byte) md3 (regs' : bvmap 5 word) (mem' : word -> option byte) md' (Wr : Z -> Prop),
  ctl_from POST X ->
  ctl_base cx ->
  AJ cx (ACtlCut.cut_own X cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.cut_own X cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.cut_own X cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= ACtlCut.cut_kmax X cx idx ->
  (forall x : word, ~ Wr (bv_unsigned x) ->
     Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem' x = Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem3 x) ->
  lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem3)
    (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem') ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, Wr a ->
     Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
       (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
       (ACtlCut.cut_own X cx) a) ->
  ACtlCut.cut_body X cx idx (Reusable.YG0d.ablocks B ly3 S3) fr fr regs' mem' ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem' ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc X) regs' mem' md') (POST cx).
Proof.
  intros POST X cx idx fr k ly3 S3 W3 mem3 md3 regs' mem' md' Wr HX HB HJ Hfr HG1 Hk Hfrz Hgr Hhid Hsbm HW HBODY HRT.
  apply (HX cx idx fr k ly3 S3 W3 regs' mem' md' HB); [| exact Hfr | exact HG1 | exact Hk | exact HBODY | exact HRT].
  exact (Reusable.YCbq.ajournal_exec segs B LAWS segs_low
           Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
           (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
           (ACtlCut.cut_own X cx) ly3 S3 W3 mem3 md3 k mem' md' Wr HJ Hfrz Hgr Hhid Hsbm HW).
Qed.

(* H4. Seat an `_F` run at a cut.  The cut's configuration is cfg_at over the cut's actual register map regs;
   the `_F` statement starts at the canonical map R it names, which agrees with regs on every register but x0
   (Regs6ss.xregs_eqv).  The kit's SRr_xregs_eqv moves the walk across that equivalence, and w4_lift_F lifts the
   run.  The continuation sees the run's end state, the materialized model, and the start's hidden bytes. *)
Lemma w4_seat_F : forall (W : Reusable.YA0n.world segs) (regs R : bvmap 5 word) (pc : Z)
    (mem : word -> option byte) (md : Model) (P : machine_state -> Prop)
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.Regs6ss.xregs_eqv R regs ->
  Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P
    (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs R pc mem md P Q Hxe Hevt K.
  rewrite w4_cfg_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W R regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
           lib.Reusable.YK11.fp_csr None mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs) md Q); [|exact Hxe].
  apply (w4_lift_F W _ md P Q Hevt).
  intros ms' md' HP Hsbm Hhid. exact (K ms' md' HP Hsbm Hhid).
Qed.

(* H5. Visibility above the image.  At or above the image top 0x5fe000 there is no read-only image byte
   (Reusable.YF0x.seg_rom_none_high), so a byte the core's view reads there (aview <> None) can only come from
   memory the world does not hide.  This is how a block's SHADOW byte, which AR_shadow_law gives as
   shadow_hull_vis (aview <> None), becomes visible. *)
Lemma w4_vis_high : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  0x5fe000 <= a < 2 ^ 64 ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Ha Hv.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hv.
  unfold Reusable.YG0n.aview, Reusable.YK04.mrestrict,
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte.
  rewrite E.
  rewrite (Reusable.YF0x.seg_rom_none_high a Ha).
  reflexivity.
Qed.

(* H6. One byte of a byte run (an `_F` run states its per-turn reads one byte at a time). *)
Lemma w4_bytes_at_byte : forall (m : word -> option byte) (a : Z) (bs : list byte) (t : nat) (d : byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> (t < length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat t) [nth t bs d].
Proof.
  intros m a bs t d (Ha & Hlen & H) Ht.
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
  replace (a + Z.of_nat t + Z.of_nat 0) with (a + Z.of_nat t) by lia.
  rewrite (H t Ht). cbn [nth_error]. apply nth_error_nth'. exact Ht.
Qed.

(* H7. FRAC reads registers 2, 3, 4, 8, 9, 19 and 26 and memory only: equal values there carry it across a run
   that changes other registers.  (The fake-frame trailer word, FRAC's last conjunct since a218ac85be5, is a
   memory conjunct and moves with the rest.) *)
Lemma w4_FRAC_cong : forall cx fr sel (r r' : bvmap 5 word) (m : word -> option byte),
  lib.Reusable.YK11.getr r' 2 = lib.Reusable.YK11.getr r 2 ->
  lib.Reusable.YK11.getr r' 3 = lib.Reusable.YK11.getr r 3 ->
  lib.Reusable.YK11.getr r' 4 = lib.Reusable.YK11.getr r 4 ->
  lib.Reusable.YK11.getr r' 8 = lib.Reusable.YK11.getr r 8 ->
  lib.Reusable.YK11.getr r' 9 = lib.Reusable.YK11.getr r 9 ->
  lib.Reusable.YK11.getr r' 19 = lib.Reusable.YK11.getr r 19 ->
  lib.Reusable.YK11.getr r' 26 = lib.Reusable.YK11.getr r 26 ->
  ACtlCutP.FRAC B cx fr sel r m -> ACtlCutP.FRAC B cx fr sel r' m.
Proof.
  intros cx fr sel r r' m H2 H3 H4 H8 H9 H19 H26 HF.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in HF |- *.
  rewrite <- H2, <- H3, <- H4, <- H8, <- H9, <- H19, <- H26 in HF.
  exact HF.
Qed.

(* H8. The record-sum model fact of S_F22 (UB Seg/F22.v:17): on the record arm (Phi[18] / Phi[19] = 4 / 3) the
   loop's result `psum rec 6 mod 128 =? 0` IS the model's head-amp verdict t_want_v, because hv reduces to its
   rsum conjunct there and rsum rec = psum rec 6 mod 128 (Prog/RcLeaf.v:9-12). *)
Lemma w4_f22_want : forall (inp : list byte) (jn : nat),
  ACtlCutP.RPA.cp_v (ACtlCutP.SM.t_g inp jn) 18 = 4 ->
  ACtlCutP.RPA.cp_v (ACtlCutP.SM.t_g inp jn) 19 = 3 ->
  (if ACtlCutP.RMO.psum (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g inp jn) 34 6) 6 mod 128 =? 0 then 0 else -1)
    = ACtlCutP.SM.t_want_v inp jn.
Proof.
  intros inp jn H18 H19.
  unfold ACtlCutP.SM.t_want_v, Prog.RcLeaf.hv, Prog.RcLeaf.rsum.
  unfold ACtlCutP.RPA.cp_v in H18, H19.
  rewrite H18, H19. reflexivity.
Qed.

(* H9. A live block's bytes are visible (V3): AR_blocks_law states apresent on every byte of a block the
   current state lists, and apresent includes w_H = false.  As an `_F` run's one-byte rng premise under RNG_W. *)
Lemma w4_rng_block : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= x -> x < p + Reusable.YG00.req_size n -> 0 <= x -> x + 1 <= 2 ^ 64 ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) x 1.
Proof.
  intros W mem ly S md p n x HAR Hin Hx1 Hx2 Hx0 Hx3.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpres & _ & _).
  apply w4_rng_vis; [exact Hx0 | exact Hx3 |].
  intros a Ha. destruct (Hpres a ltac:(lia)) as (Hap & _). exact (proj1 Hap).
Qed.

(* H10. A live block's SHADOW bytes are visible (V4): AR_shadow_law gives the shadow hull as
   shadow_hull_vis (aview <> None); a shadow address lies above the image top, where w4_vis_high turns
   aview <> None into w_H = false.  The run states the shadow byte as Z.shiftr x 3 + ASAN_K, which is the core's
   shadow_addr x = SHADOW_OFF + x / 8 for x >= 0. *)
Lemma w4_block_shadow_vis : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= p -> p <= x -> x < p + Reusable.YG00.req_size n -> x < 2 ^ 64 ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (Z.shiftr x 3 + B.ACtlK.ASAN_K)) = false.
Proof.
  intros W mem ly S md p n x HAR Hin Hp Hx1 Hx2 Hx3.
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hhull).
  unfold Reusable.YG0d.shadow_hull_vis in Hhull.
  assert (Hsh : Z.shiftr x 3 + B.ACtlK.ASAN_K = Reusable.YG0f.shadow_addr x).
  { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.ACtlK.ASAN_K, B.AsanRT.ASAN_K.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
  rewrite Hsh.
  assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : x / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  apply (w4_vis_high W mem).
  - unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
  - apply Hhull.
    pose proof (Reusable.YCbq.shadow_mono p x Hx1) as M1.
    pose proof (Reusable.YCbq.shadow_mono x (p + Reusable.YG00.req_size n - 1) ltac:(lia)) as M2.
    pose proof (Z.mul_div_le (Reusable.YG0f.shadow_addr p) 8 ltac:(lia)) as A1.
    pose proof (Z.div_mod (Reusable.YG0f.shadow_addr (p + Reusable.YG00.req_size n - 1)) 8 ltac:(lia)) as A2.
    pose proof (Z.mod_pos_bound (Reusable.YG0f.shadow_addr (p + Reusable.YG00.req_size n - 1)) 8 ltac:(lia)) as A3.
    lia.
Qed.

(* H11. H10 as an `_F` run's one-byte rng premise under RNG_W. *)
Lemma w4_rng_block_shadow : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= p -> p <= x -> x < p + Reusable.YG00.req_size n -> x < 2 ^ 64 ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) (Z.shiftr x 3 + B.ACtlK.ASAN_K) 1.
Proof.
  intros W mem ly S md p n x HAR Hin Hp Hx1 Hx2 Hx3.
  pose proof (w4_block_shadow_vis W mem ly S md p n x HAR Hin Hp Hx1 Hx2 Hx3) as Hv.
  assert (Hd : Z.shiftr x 3 = x / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : x / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  unfold B.ACtlK.ASAN_K, B.AsanRT.ASAN_K in *.
  apply w4_rng_vis; [rewrite Hd; lia | rewrite Hd; lia |].
  intros a Ha. replace a with (Z.shiftr x 3 + 0x7fff8000) by lia. exact Hv.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   BODY-TRANSPORT TOOLKIT (the w4k_ lemmas).  Ported from a Theorem Labs lane's PROVED local helpers (lib/B/ACtlW3a.v,
   lines 273-879 at head; from a working branch 6365e5d6107; renamed w3a_ -> w4k_, `Proof using ..` relaxed to
   `Proof.` because aview_vis_mrd is a proved lemma here, and W3a's turn-0 / PRO-only lemmas left out).  Raw
   memory readers, the journal and ctl_rt after a silent run, the own6 cut context from the journal (w4k_cut6),
   and the transports of the carried bundles.  Each is proved from the core (YCbq, YG0d's AR laws, the journal),
   lib/Lib and B's ProgBridge; none is a hypothesis.  (If a Theorem Labs lane opens the shared translation file of plan
   section 5, these move there.) *)

Local Notation rsegs := B.Img0.rsegs.

Lemma w4k_P64 : 2 ^ 64 = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma w4k_outside_dec : forall W x, lib.Lib.Frame.outside W x \/ ~ lib.Lib.Frame.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
    + right. intros [H1 _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma w4k_not_outside1 : forall lo hi a, ~ lib.Lib.Frame.outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma w4k_raw_mrd : forall (m : word -> option byte) x b, m x = Some b -> lib.Lib.Mem.mrd rsegs m x = Some b.
Proof. intros m x b H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma w4k_raw_wview : forall (m : word -> option byte) x b, m x = Some b -> wview rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

Lemma w4k_not_img_high : forall a, Reusable.YG0f.kLowMemEnd <= a -> ~ Reusable.YG0d.in_img segs a.
Proof. intros a Ha Hi. pose proof (segs_low a Hi) as H. lia. Qed.

Lemma w4k_mrd_raw : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa a) = Some b -> m (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros m a b Ha Hn H. unfold lib.Lib.Mem.mrd in H. destruct (m (lib.Lib.Mem.wa a)) as [b'|] eqn:E; [exact H|].
  exfalso. pose proof (Reusable.YCbq.seg_rom_none segs a Ha Hn) as R.
  assert (H' : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) by exact H.
  rewrite R in H'. discriminate.
Qed.

(* The image hull [0x10000, 0x5fe000) is covered by the segments (ProgBridge.rsegs_spans). *)
Lemma w4k_img_hull : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. pose proof B.ProgBridge.rsegs_spans as E.
  assert (HIn : forall b sz, In (b, sz) [(65536, 135168); (200704, 450560); (651264, 12288); (663552, 5619712)] ->
                  b <= a < b + sz -> Reusable.YG0d.in_img segs a).
  { intros b sz Hin Hb. rewrite <- E in Hin. apply in_map_iff in Hin as (s & Es & Hs). injection Es as Eb Esz.
    exists s. split; [exact Hs | lia]. }
  destruct (Z_lt_le_dec a 200704); [apply (HIn 65536 135168); [left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 651264); [apply (HIn 200704 450560); [right; left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 663552); [apply (HIn 651264 12288); [right; right; left; reflexivity | lia]|].
  apply (HIn 663552 5619712); [right; right; right; left; reflexivity | lia].
Qed.

Lemma w4k_mrd_munch : forall W (m m' : word -> option byte) x, lib.Lib.Frame.munch W m m' -> 0 <= x < 2 ^ 64 ->
  lib.Lib.Frame.outside W x -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x).
Proof.
  intros W m m' x MU Hx Ho. unfold lib.Lib.Mem.mrd. rewrite (MU (lib.Lib.Mem.wa x)); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho.
Qed.

Lemma w4k_bytes_keep : forall (m m' : word -> option byte) a bs,
  lib.Lib.Mem.bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  lib.Lib.Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite K; [exact (H i Hi) | lia].
Qed.

Lemma w4k_addr_keep : forall (m m' : word -> option byte) p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) K. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b.
  split; [rewrite (K i Hi); exact Hb | exact Hk].
Qed.

Lemma w4k_stk_raw : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [b Hb].
  split; [exact (w4k_raw_wview m _ b Hb) | exists b; exact (w4k_raw_mrd m _ b Hb)].
Qed.

Lemma w4k_wr_raw : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Mem.wr_at rsegs m a n.
Proof.
  intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (H (a + i) ltac:(lia)) as [b Hb]. exact (w4k_raw_wview m _ b Hb).
Qed.

Lemma w4k_rw8 : forall m a v, lib.Lib.Mem.bytes_at rsegs m a (lib.Lib.Mem.le8 v) -> lib.Lib.Mem.wr_at rsegs m a 8 ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 v].
Proof.
  intros m a v H Hw. split; [split; [exact (conj I I) | cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]; rewrite app_nil_r; exact H]|].
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. exact Hw.
Qed.

Lemma w4k_rw1 : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> m (lib.Lib.Mem.wa a) = Some b ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C1 b].
Proof.
  intros m a b Ha Hb. split; [split; [exact (conj I I)|] |].
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
    exact (w4k_raw_mrd m _ b Hb).
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. apply w4k_wr_raw; [lia | lia|].
    intros x Hx. replace x with a by lia. exists b. exact Hb.
Qed.

Lemma w4k_cb_raw : forall (m : word -> option byte) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, m (lib.Lib.Mem.wa x) = Some b) ->
  exists junk, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n junk].
Proof.
  intros m a n H0 H1 H.
  destruct (lib.Lib.Frame.stk_carve rsegs m a (a + Z.of_nat n) n (w4k_stk_raw m a (a + Z.of_nat n) H0 H1 H) ltac:(lia))
    as (_ & junk & Hj).
  replace (a + Z.of_nat n - Z.of_nat n) with a in Hj by lia. exists junk. exact Hj.
Qed.

Lemma w4k_bytes_of_mrd : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x) = Some b) ->
  exists bs, length bs = n /\ lib.Lib.Mem.bytes_at rsegs m a bs.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H a ltac:(lia)) as [b Hb].
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) (fun x Hx => H x ltac:(lia))) as (bs & Hl & (_ & _ & Hbs)).
    exists (b :: bs). split; [cbn [length]; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply Hbs. cbn [length] in Hi. lia.
Qed.

(* A spill read at register 9's value. *)
Lemma w4k_spill_A : forall regs m off v A, B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 ->
  0 <= off <= 512 -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HA HA0 HA1 Hoff (A' & HA' & Hq).
  unfold B.ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
  apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
  change (bv_modulus 64) with (2 ^ 64) in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat Pos.of_succ_nat] in Hq1.
  pose proof w4k_P64 as P64. rewrite P64 in HA', HA1, Hq1.
  assert (E : A = A') by (Z.div_mod_to_equations; lia). subst A'. exact Hq.
Qed.

Lemma w4k_spill_keep : forall regs R (m m' : word -> option byte) off v A,
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 -> 0 <= off <= 512 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill R m' off v.
Proof.
  intros regs R m m' off v A HA HA0 HA1 Hoff E9 K Hs.
  pose proof (w4k_spill_A regs m off v A HA HA0 HA1 Hoff Hs) as Hq.
  exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact HA|].
  apply (w4k_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

(* ctl_rt_C (route C) after a silent run whose written bytes lie outside the image and are present afterwards: the
   cells and the read-only bytes are kept (outside the image's written set nothing moves), and both shadow conjuncts
   by the shared transport B.ShadowRwOnT.shadow_rw_on_mem_mono (every byte readable before is readable after:
   B.Prog.MemMono.rd_mono_munch). *)
Lemma w4k_ctlrt_run : forall ly S (m m' : word -> option byte) Wr,
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch Wr m m' -> lib.Lib.Frame.wmono rsegs m m' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a -> ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S m m' Wr (HAC & HSWC & HSWI & HRO) MU WM HW.
  assert (KI : forall x, 0 <= x < 2 ^ 64 -> ~ ~ Reusable.YG0d.in_img segs x ->
             lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)).
  { intros x Hx Hi. apply (w4k_mrd_munch Wr); [exact MU | exact Hx |].
    destruct (w4k_outside_dec Wr x) as [H|H]; [exact H|]. exfalso. exact (Hi (proj1 (HW x H))). }
  assert (RD : B.Prog.MemMono.rd_mono m m').
  { apply (B.Prog.MemMono.rd_mono_munch Wr m m' MU). intros x Hx.
    assert (E : lib.Lib.Mem.wa (bv_unsigned x) = x)
      by (unfold lib.Lib.Mem.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
    destruct (HW _ Hx) as (_ & b & Hb). rewrite E in Hb. exists b. exact (w4k_raw_mrd _ _ _ Hb). }
  pose proof w4k_P64 as P64.
  split; [|split; [|split]].
  - unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells in HAC |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; (eapply w4k_bytes_keep; [eassumption|]); intros x Hx;
      (apply KI; [| intros Hn; apply Hn; apply w4k_img_hull]);
      rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx;
      unfold B.AsanRT.CELL_K, B.AsanRT.UAR, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.CANPOISON,
        B.AsanRT.HIEND, B.AsanRT.MIDBEG, B.AsanRT.MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
        B.AsanRT.GOT_CELL_K, B.AsanRT.GOT_UAR, B.AsanRT.GOT_REPLACE, B.AsanRT.GOT_HIEND, B.AsanRT.GOT_MIDBEG,
        B.AsanRT.GOT_MIDEND, B.AsanRT.GOT_REAL_MEMSET in Hx; lia.
  - exact (B.ShadowRwOnT.shadow_rw_on_mem_mono _ m m' HSWC WM RD).
  - exact (B.ShadowRwOnT.shadow_rw_on_mem_mono _ m m' HSWI WM RD).
  - unfold B.ACtlK.ro_agree_at in HRO |- *. intros a Ha. rewrite <- (HRO a Ha).
    pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    assert (E : lib.Lib.Mem.wa (bv_unsigned a) = a)
      by (unfold lib.Lib.Mem.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
    rewrite <- E. apply KI; [lia|]. intros Hn. unfold lib.Lib.Mem.ro_addr in Ha.
    assert (Hn' : find_segment rsegs (bv_unsigned a) 1 = None) by exact (Reusable.YCbq.find_segment_none segs _ Hn).
    rewrite Hn' in Ha. discriminate.
Qed.

(* The journal after a silent run (YCbq.ajournal_exec) whose written bytes are journal-writable. *)
Lemma w4k_after_run : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k
    (m' : word -> option byte) md' (Wr : list (Z * Z)),
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  lib.Lib.Frame.munch Wr mem3 m' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a ->
     (exists b, m' (lib.Lib.Mem.wa a) = Some b) /\
     Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
       (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
       (B.ACtlCut.own6 cx) a) ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 m' md' k.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k m' md' Wr HJ MU Hhid Hsame HW.
  refine (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
            (fun a => ~ lib.Lib.Frame.outside Wr a) HJ _ _ Hhid Hsame _).
  - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (w4k_outside_dec Wr (bv_unsigned x)) as [H|H]; [exact H | exfalso; exact (Hx H)].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (w4k_outside_dec Wr (bv_unsigned x)) as [H|H]; [rewrite (MU x H); exact Hx|].
    destruct (HW _ H) as ((b & Hb) & _). unfold lib.Lib.Mem.wa in Hb.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
    rewrite Hb. discriminate.
  - intros a Ha. exact (proj2 (HW a Ha)).
Qed.

Lemma w4k_awr_fsh : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) ->
  B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + 512 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 (B.ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 fr STK sp0 bl0 blc a Efr Ha. right. right. right.
  exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity|]. right. rewrite <- Efr.
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
Qed.

Lemma w4k_awr_fr : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) -> fr <= a < fr + 4096 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 (B.ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 fr STK sp0 bl0 blc a Efr Ha. right. right. right.
  exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity|]. left. rewrite <- Efr.
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

Lemma w4k_awr_stk : forall ly3 own STK sp0 bl0 blc a, sp0 - STK <= a < sp0 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 own a.
Proof. intros ly3 own STK sp0 bl0 blc a Ha. left. exact Ha. Qed.

(* Step C0 for an own6 cut: the frame's placement and presence, the frame shadow's presence, the stack window's
   presence and placement, all from the journal (its AR, YG0d's AR_frames_law, astk_ok, the window clause) and
   the shell's frame law. *)
Lemma w4k_cut6 : forall (cx : B.ACtlCut.ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (B.ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) /\
  fr mod 32 = 0 /\ 4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/ Reusable.YG0f.kHighMemBeg <= fr) /\
  (fr + 4096 <= 0x10000 \/ 0x5fe000 <= fr) /\
  (forall a, fr <= a < fr + 4096 -> ~ Reusable.YG0d.in_img segs a) /\
  (forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) /\
  (forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) /\
  B.ACtlCut.c_sp cx mod 16 = 0 /\
  lib.Reusable.YM05.alloc_ceiling + Reusable.YCfn.LLVMF_STK <= B.ACtlCut.c_sp cx /\
  B.ACtlCut.c_sp cx <= 2 ^ 47 /\
  (forall a, B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < B.ACtlCut.c_sp cx ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
  assert (Hin : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx)).
  { rewrite (HFA 6 (B.ACtlCut.c_fpos cx) (or_introl eq_refl)). unfold Reusable.YG0f.frame_addr.
    destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin)
    as (H32 & Happ & Hfb & Hfsh).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hceil & _).
  pose proof (fun a => Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) a HAR Hin)
    as Himg.
  rewrite <- Efr in H32, Happ, Hfb, Hfsh, H4096, Hceil, Himg.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ, Hfb, Hfsh, Hceil, Himg.
  change (4096 / 8) with 512 in Hfsh.
  destruct Hstk as (H16 & _ & Hc & Hlo & Hhi & H47 & _ & _).
  destruct Happ as (_ & Happ). unfold Reusable.YG0f.ASAN_CEIL in Happ.
  split; [exact Efr|]. split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|].
  split; [destruct Happ as [H|[H _]]; [left | right]; exact H|].
  split.
  { destruct (Z_le_gt_dec (fr + 4096) 0x10000) as [H|H]; [left; exact H|].
    destruct (Z_lt_le_dec fr 0x5fe000) as [H'|H']; [|right; exact H'].
    exfalso. apply (Himg (Z.max fr 0x10000)); [lia | apply w4k_img_hull; lia]. }
  split; [exact Himg|]. split; [intros a Ha; exact (proj1 (Hfb a Ha))|].
  split.
  { intros a Ha. pose proof (proj1 (Hfsh (a - B.ACtlCutP.Sfr fr) ltac:(lia))) as H.
    replace (Reusable.YG0f.shadow_addr fr + (a - B.ACtlCutP.Sfr fr)) with a in H; [exact H|].
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.ACtlCutP.Sfr, B.AsanRT.shadow_addr,
      B.AsanRT.ASAN_K. lia. }
  split; [exact H16|]. split; [lia|]. split; [lia|]. exact Hpres.
Qed.

Lemma w4k_vis : forall (W : Reusable.YA0n.world segs) mem lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W mem lo len H0 H1 H. apply B.ProgBridge.rng_of_visible. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (proj1 (H a Ha)).
Qed.

Lemma w4k_sh_off : forall fr off i, fr mod 8 = 0 -> off mod 8 = 0 -> 0 <= i < 8 ->
  B.AsanRT.shadow_addr (fr + off + i) = B.ACtlCutP.Sfr fr + off / 8.
Proof.
  intros fr off i Hf Ho Hi. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. pose proof (Z.div_mod off 8 ltac:(lia)) as E2.
  rewrite Hf in E1. rewrite Ho in E2.
  replace (fr + off + i) with (i + (fr / 8 + off / 8) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small i 8) by lia. lia.
Qed.

Lemma w4k_kn_shadow : forall i, 0 <= i < 112 ->
  2147450880 + 81584 <= B.AsanRT.shadow_addr (B.ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597.
Proof.
  intros i Hi. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.KNA.KIND_NAME.
  split; Z.div_mod_to_equations; lia.
Qed.

(* The carried bundle FRAC across a memory step that keeps the registers it pins, the stack words above sp and the
   frame header, and leaves the 392 frame-shadow bytes readable. *)
Lemma w4k_FRAC_keep : forall (cx : B.ACtlCut.ctlcx) fr sel regs R (m m' : word -> option byte),
  B.ACtlCutP.FRAC B cx fr sel regs m ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, Reusable.YG0d.spZ regs <= x < B.ACtlCut.c_sp cx ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  (forall x, fr <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096 ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  (forall x, B.ACtlCutP.Sfr fr <= x < B.ACtlCutP.Sfr fr + 392 ->
     exists b, lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = Some b) ->
  B.ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel regs R m m' (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 &
    HAS & HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & (sh & Hsh & Hshl) & Hsaved &
    Htr)
    E2 E3 E4 E8 E9 E19 E26 KS KF KSh.
  pose proof w4k_P64 as P64.
  exists A, sp.
  refine (conj _ (conj Hsp16 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hfr32 (conj HA32
    (conj HAS (conj HspA (conj HfrA (conj HAS448 (conj HSsp (conj HSapp _))))))))))))))))).
  - rewrite E2. exact Hr2.
  - unfold Reusable.YG0d.spZ in HspZ |- *. rewrite E2. exact HspZ.
  - rewrite E4. exact Hr4.
  - unfold B.ACtlCut.rgv in Hr8 |- *. rewrite E8. exact Hr8.
  - unfold B.ACtlCut.rgv in Hr9 |- *. rewrite E9. exact Hr9.
  - rewrite E3. exact Hr3.
  - unfold B.ACtlCut.rgv in Hr19 |- *. rewrite E19. exact Hr19.
  - unfold B.ACtlCut.rgv in Hr26 |- *. rewrite E26. exact Hr26.
  - assert (HQ : forall a v, A <= a -> a + 8 <= B.ACtlCut.c_sp cx -> B.ACtlCutP.q64 m a v -> B.ACtlCutP.q64 m' a v).
    { intros a v H1 H2 Hq. apply (w4k_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KS. lia. }
    refine (conj (HQ _ _ _ _ Hq336) (conj (HQ _ _ _ _ Hq48) (conj (HQ _ _ _ _ Hq40)
      (conj _ (conj _ (conj _ (conj _ _)))))));
      try lia.
    + apply (w4k_bytes_keep m m' _ _ Hqh0). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + apply (w4k_bytes_keep m m' _ _ Hqh16). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + change (Z.to_nat B.ACtlCutP.FRAME_SHADOW) with 392%nat in Hshl |- *.
      destruct Hsh as (Hs0 & Hs1 & _). rewrite Hshl in Hs1.
      destruct (w4k_bytes_of_mrd m' 392 (B.ACtlCutP.Sfr fr) Hs0 Hs1 KSh) as (sh' & Hl & Hb).
      exists sh'. split; [exact Hb | exact Hl].
    + assert (Hlen : length (B.ACtlCutP.saved_bytes cx) = 104%nat).
      { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
      apply (w4k_bytes_keep m m' _ _ Hsaved). rewrite Hlen. intros x Hx. apply KS. lia.
    + apply (w4k_bytes_keep m m' _ _ Htr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
Qed.

Lemma w4k_bv_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma w4k_signed_nonneg : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of a frame address, by its offset from the 8-aligned frame base. *)
Lemma w4k_sh_frame : forall fr x, fr mod 8 = 0 -> fr <= x ->
  B.AsanRT.shadow_addr x = B.ACtlCutP.Sfr fr + (x - fr) / 8 /\
  8 * ((x - fr) / 8) <= x - fr < 8 * ((x - fr) / 8) + 8.
Proof.
  intros fr x Hf Hx. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. rewrite Hf in E1.
  pose proof (Z.div_mod (x - fr) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (x - fr) 8 ltac:(lia)) as E3.
  split; [|lia].
  assert (Ex : x = (x - fr) + (fr / 8) * 8) by lia. rewrite Ex at 1. rewrite Z.div_add by lia. lia.
Qed.

Lemma w4k_hull_in : forall x n s, 0 <= x -> 0 < n ->
  Reusable.YG0f.shadow_addr x / 8 * 8 <= s < Reusable.YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8.
Proof.
  intros x n s Hx Hn Hs.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* T5 at a call site: ctrl's addressable (mrd of the shadow bytes) gives the core's range_addressable over the view,
   where the shadow bytes are visible (aview_vis_mrd). *)
Lemma w4k_range_addr : forall (W : Reusable.YA0n.world segs) mem p n,
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W mem p n (H1 & H2 & H3 & H) HV x Hx.
  destruct (H (x - p) ltac:(lia)) as (Ha & b & Hb & Hk). pose proof (HV (x - p) ltac:(lia)) as Hv.
  replace (p + (x - p)) with x in Ha, Hb, Hk, Hv by lia.
  assert (E : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  exists (bv_unsigned b). rewrite E. split.
  - rewrite (aview_vis_mrd W mem _ Hv).
    change (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) with (Z_to_bv 64 (B.AsanRT.shadow_addr x)) in Hb.
    rewrite Hb. reflexivity.
  - unfold B.AsanRT.shadow_ok in Hk. unfold Reusable.YG0v.saddr_ok.
    destruct Hk as [Hk|Hk]; [left | right]; rewrite w4k_signed_nonneg by lia; lia.
Qed.

Lemma w4k_hull_vis : forall (W : Reusable.YA0n.world segs) mem x n, 0 <= x -> 0 < n ->
  (forall s, B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem s) ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n.
Proof.
  intros W mem x n Hx Hn H s Hs. apply (Reusable.YCbq.aview_some_of_apresent segs). apply H.
  exact (w4k_hull_in x n s Hx Hn Hs).
Qed.

Lemma w4k_q64_of_c8 : forall m a v, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 (Z_to_bv 64 v)] ->
  B.ACtlCutP.q64 m a v.
Proof.
  intros m a v ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

Lemma w4k_bytes_of_cb : forall m a n bs, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n bs] ->
  lib.Lib.Mem.bytes_at rsegs m a bs.
Proof.
  intros m a n bs ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

(* The entry's gp (the core's afn_pre inside the lib pre). *)
Lemma w4k_gp : forall cx, B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B).
Proof.
  intros cx ((HAF & _) & _). destruct HAF as (_ & _ & _ & Hgp & _). exact Hgp.
Qed.

Lemma w4k_amem_frame : forall fr d n, 4096 <= fr -> fr + 4096 <= lib.Reusable.YM05.alloc_ceiling ->
  (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/ Reusable.YG0f.kHighMemBeg <= fr) ->
  fr <= d -> d + n <= fr + 4096 -> Reusable.YG0d.amem_range d n.
Proof.
  intros fr d n H0 H1 H2 H3 H4. pose proof Reusable.YG0f.ASAN_CEIL_range as (HC & _).
  unfold Reusable.YG0f.ASAN_CEIL in HC. unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd,
    Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd, Reusable.YG0f.kLowShadowBeg in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   CALL-TRANSPORT TOOLKIT (the w4m_ lemmas).  Ported from a Theorem Labs lane's PROVED local helpers (lib/B/ACtlW4f.v,
   lines 324-518 and 889-1352 at head; from a working branch c8fda648d4e; renamed w4f_ -> w4m_, nothing else
   changed; aview_vis_mrd, a Section hypothesis on that working branch, is the proved lemma of this file).  Run seating
   (w4m_enter / w4m_run / w4m_exit), the register transports of the cut bundles (w4m_ ... _tr), and the
   transports of FRAC / HB / FTK / FTURN / IFS / LK across a call whose post keeps the raw bytes (MKEPT) of the
   regions they read (w4m_bcmp_ ...), with the frame / block / KIND_NAME keeps from a view kept outside a
   window.  Each is proved from the core (YCbq, YG0d's AR laws, the journal), lib/Lib and B's ProgBridge; none is
   a hypothesis. *)

Local Notation getr := lib.Reusable.YK11.getr.

(* A cut state as a footprint run's start state: lib/Lib's MS over the canonical register map (Regs6ss.mkR_of),
   which the walk does not tell apart from the cut's map (YA0nR.SRr_xregs_eqv). *)
Lemma w4m_enter : forall (W : Reusable.YA0n.world segs) pc regs mem md Q,
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS (lib.Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
              lib.Reusable.YK11.fp_csr None mem (lib.Reusable.YK11.seg_rom segs)) md) Q ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W pc regs mem md Q H. rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W (lib.Lib.Regs6ss.mkR_of regs) regs _ _ _ _ _ _ md Q H).
  apply lib.Lib.Regs6ss.xregs_eqv_sym, lib.Lib.Regs6ss.mkR_of_eqv.
Qed.

(* A footprint run (Lib/ExecF.evtF over Img0.rsegs) as a silent prefix of the walk (YA0nR.SRr_fevt_hid through
   ProgBridge.fevt_of_evtF); the continuation also gets the hidden bytes kept (ajournal_exec's premise). *)
Lemma w4m_run : forall (W : Reusable.YA0n.world segs) ms md RNG (P : machine_state -> Prop) Q,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG P ms ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md RNG P Q Hrun Hav K.
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W ms md RNG P Q (B.ProgBridge.fevt_of_evtF RNG P ms Hrun) Hav).
  intros ms' md' HP Hhid Hs. exact (K ms' md' HP Hs Hhid).
Qed.

(* The cut configuration of a run's end state. *)
Lemma w4m_exit : forall (W : Reusable.YA0n.world segs) pc R mem md Q,
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R mem md) Q ->
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Reusable.YK11.seg_rom segs)) md) Q.
Proof. intros W pc R mem md Q H. rewrite <- B.ProgBridge.cfg_at_MS. exact H. Qed.

(* The journal across a stretch that writes no memory (YCbq.ajournal_exec, empty write set). *)
Lemma w4m_aj_nowrite : forall cx own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ);
    [intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity | exact Hs |
     intros a Ha; destruct Ha].
Qed.

(* A stack range inside the journal's present window [c_sp cx - LLVMF_STK, c_sp cx) is visible. *)
Lemma w4m_vis_stack : forall cx own ly3 S3 W3 mem3 md3 k lo len,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> lo + len <= ACtlCut.c_sp cx -> 0 <= lo ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo len HJ H1 H2 H0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hsp.
  unfold ACtlCut.c_sp, Reusable.YG0d.spZ in *. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  split; [exact H0 |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* The owned class-6 frame of a cut is visible: its bytes are in_frames of the journal's own (awr_byte's fourth
   case), hence apresent (YCbq.awr_byte_present); the layout's frame base does not move (layout_le). *)
Lemma w4m_frame_at : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HG1.
  pose proof HJ as (_ & Hly & _).
  rewrite (HG1 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
  unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity.
Qed.

Lemma w4m_frame_bounds : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof HJ as (HAR & _).
  rewrite (w4m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (H1 & H2 & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2. lia.
Qed.

Lemma w4m_vis_frame : forall cx ly3 S3 W3 mem3 md3 k fr lo len,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr <= lo -> lo + len <= fr + 4096 -> 0 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo len HJ HF HG1 H1 H2 H3.
  pose proof (w4m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (B1 & B2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  pose proof (w4m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  split; [lia |]. split; [lia |].
  intros a Ha.
  refine (proj1 (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _))).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

(* A spill slot read at the spill base of FRAC. *)
Lemma w4m_spill : forall regs m off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HAb Hoff.
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). unfold ACtlCut.rgv in HA, HA'. rewrite HA' in HA.
    apply (f_equal bv_unsigned) in HA. rewrite !Z_to_bv_unsigned in HA. unfold bv_wrap in HA.
    change (bv_modulus 64) with (2 ^ 64) in HA. rewrite lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat] in Hq1.
    Z.div_mod_to_equations. nia. }
  subst A'. exact Hq.
Qed.

(* Register transport of the body predicates: each reads only the registers named in its premises. *)
Ltac w4m_rw_regs :=
  repeat match goal with
  | E : getr ?R ?r = getr ?R0 ?r |- context [getr ?R ?r] => rewrite E
  end.
Ltac w4m_tr := intros; w4m_rw_regs; assumption.

Lemma w4m_rgv_tr : forall R R0 r v, getr R r = getr R0 r -> ACtlCut.rgv R0 r v -> ACtlCut.rgv R r v.
Proof. unfold ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_spill_tr : forall R R0 m off v, getr R 9 = getr R0 9 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m off v.
Proof. unfold ACtlCutP.spill, ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_FRAC_tr : forall cx fr sel R R0 m,
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m.
Proof. unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ. w4m_tr. Qed.
Lemma w4m_FLI_tr : forall cx fr R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m.
Proof. unfold ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_LK_tr : forall cx fr j R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m.
Proof. unfold ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_FTK_tr : forall cx j fr R R0 m,
  getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 -> getr R 25 = getr R0 25 ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m.
Proof. unfold ACtlCutP.FTK, ACtlCutP.spill, ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_FTURN_tr : forall cx j phi R R0 m, getr R 9 = getr R0 9 ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m.
Proof. unfold ACtlCutP.FTURN, ACtlCutP.spill, ACtlCut.rgv. w4m_tr. Qed.
Lemma w4m_IFS_tr : forall cx fr j R R0 m, ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m.
Proof. unfold ACtlCutP.IFS, ACtlCutP.FSj, ACtlCutP.FSb. w4m_tr. Qed.

(* The raw bytes of [lo, hi) are the same in m and m'. *)
Local Notation MKEPT m m' lo hi :=
  (forall w4m_x : Z, lo <= w4m_x < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 w4m_x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 w4m_x)).

(* ---- the one step from a view-level post to a raw fact: a visible address whose view is kept keeps its byte ---- *)
Lemma w4m_bcmp_pt : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) a,
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a).
Proof.
  intros W m m' a Hv E.
  rewrite (aview_vis_mrd W m' a Hv), (aview_vis_mrd W m a Hv) in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a)) as [b'|],
    (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A byte whose view is not None at a non-image address is visible. *)
Lemma w4m_bcmp_vis_of_aview : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a -> Reusable.YG0n.aview segs H m a <> None ->
  H (Z_to_bv 64 a) = false.
Proof.
  intros H m a Ha Hn Hv.
  destruct (Reusable.YG0n.aview segs H m a) as [v|] eqn:Ev; [| exfalso; apply Hv; reflexivity].
  destruct (Reusable.YCbq.aview_byte segs H m a v Ev) as (b & _ & -> & _).
  refine (proj1 (Reusable.YCbq.apresent_transfer segs (fun _ => false) H (fun _ => Some b) m a Ha Hn _ _)).
  - rewrite Ev. reflexivity.
  - split; [reflexivity | exists b; reflexivity].
Qed.

(* ---- primitive raw-fact transfers ---- *)
Lemma w4m_bcmp_bytes : forall (m m' : word -> option byte) a bs,
  MKEPT m m' a (a + Z.of_nat (length bs)) ->
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H). split; [exact H0 |]. split; [exact H1 |].
  intros i Hi. exact (eq_trans (K (a + Z.of_nat i) ltac:(lia)) (H i Hi)).
Qed.

Lemma w4m_bcmp_q64 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 8) ->
  ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.q64 in *. apply (w4m_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

Lemma w4m_bcmp_u32 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 4) ->
  ACtlCutP.u32 m a v -> ACtlCutP.u32 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.u32 in *. apply (w4m_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le4. exact K.
Qed.

Lemma w4m_bcmp_b8 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 1) ->
  ACtlCutP.b8 m a v -> ACtlCutP.b8 m' a v.
Proof. intros m m' a v K H. unfold ACtlCutP.b8 in *. exact (w4m_bcmp_bytes m m' a [Z_to_bv 8 v] K H). Qed.

Lemma w4m_bcmp_sp : forall R R0 (m m' : word -> option byte) A csp off v,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> 0 <= off <= 440 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros R R0 m m' A csp off v HA E9 H0 H1 H2 K Hoff Hs.
  pose proof (w4m_spill R0 m off v A Hs HA ltac:(lia) ltac:(lia)) as Hq.
  exists A. split; [exact (w4m_rgv_tr R R0 9 A E9 HA) |].
  apply (w4m_bcmp_q64 m m' (A + off) v); [intros x Hx; apply K; lia | exact Hq].
Qed.

Lemma w4m_bcmp_addr : forall (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |].
  exists b. split; [| exact Hok]. exact (eq_trans (K i Hi) Hb).
Qed.

(* A raw-present range stays a stack range (wview / mrd of a present byte). *)
Lemma w4m_bcmp_stk : forall (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.stk segs m lo hi -> lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi Hp (H0 & H1 & _). split; [exact H0 |]. split; [exact H1 |].
  intros a Ha. destruct (Hp a Ha) as [b Hb]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* ---- the callee's view-level arguments from raw facts at visible addresses ---- *)
Lemma w4m_bcmp_signed : forall b : byte, 0 <= bv_signed b <= 7 -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4m_bcmp_range_addr : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) p n,
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  B.AsanRT.addressable m p n ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n Hv (_ & _ & _ & H) x Hx.
  destruct (H (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  pose proof (Hv (x - p) ltac:(lia)) as Hvx.
  replace (p + (x - p)) with x in Hb, Hok, Hvx by lia.
  exists (bv_unsigned b). split.
  - replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x) with (B.AsanRT.shadow_addr x)
      by (unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
    rewrite (aview_vis_mrd W m _ Hvx). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. reflexivity.
  - unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
    destruct Hok as [Hok | Hok].
    + left. rewrite (w4m_bcmp_signed b ltac:(lia)). exact Hok.
    + right. rewrite (w4m_bcmp_signed b ltac:(lia)). lia.
Qed.

(* The byte the view reads at a visible address of a bytes_at fact. *)
Lemma w4m_bcmp_aview_at : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) x l k,
  lib.Lib.Mem.bytes_at segs m x l -> (k < length l)%nat ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (x + Z.of_nat k)) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (x + Z.of_nat k) =
  option_map (fun b : byte => bv_unsigned b) (nth_error l k).
Proof.
  intros W m x l k (_ & _ & H) Hk Hv. rewrite (aview_vis_mrd W m _ Hv). f_equal. exact (H k Hk).
Qed.

Lemma w4m_bcmp_list_eq : forall (l r : list byte), length l = length r ->
  (forall k, (k < length l)%nat -> nth_error l k = nth_error r k) -> l = r.
Proof.
  induction l as [|a l IH]; intros [|b r] HL H; cbn in HL; try discriminate; [reflexivity |].
  f_equal.
  - specialize (H 0%nat ltac:(cbn; lia)). cbn in H. injection H as H. exact H.
  - apply IH; [lia | intros k Hk; exact (H (S k) ltac:(cbn; lia))].
Qed.

(* The bcmp result: the view equality of the n compared bytes is the equality of the two byte lists. *)
Lemma w4m_bcmp_cmp : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) x y (l r : list byte) n,
  length l = length r -> n = Z.of_nat (length l) ->
  lib.Lib.Mem.bytes_at segs m x l -> lib.Lib.Mem.bytes_at segs m y r ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (x + i)) = false) ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (y + i)) = false) ->
  ((forall i, 0 <= i < n ->
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (x + i) =
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (y + i)) <-> l = r).
Proof.
  intros W m x y l r n HL Hn Hx Hy Vx Vy. subst n. split.
  - intros H. apply (w4m_bcmp_list_eq l r HL).
    intros k Hk. pose proof (H (Z.of_nat k) ltac:(lia)) as E.
    rewrite (w4m_bcmp_aview_at W m x l k Hx Hk (Vx (Z.of_nat k) ltac:(lia))) in E.
    rewrite (w4m_bcmp_aview_at W m y r k Hy ltac:(lia) (Vy (Z.of_nat k) ltac:(lia))) in E.
    destruct (nth_error l k) as [b1|], (nth_error r k) as [b2|]; cbn in E; try discriminate; [|reflexivity].
    injection E as E. f_equal. apply bv_eq. exact E.
  - intros <- i Hi.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (w4m_bcmp_aview_at W m x l (Z.to_nat i) Hx ltac:(lia) (Vx (Z.of_nat (Z.to_nat i)) ltac:(lia))).
    rewrite (w4m_bcmp_aview_at W m y l (Z.to_nat i) Hy ltac:(lia) (Vy (Z.of_nat (Z.to_nat i)) ltac:(lia))).
    reflexivity.
Qed.

(* ---- visibility of the walk's owned frame, its shadow and the live blocks ---- *)
Lemma w4m_bcmp_frame_present : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  refine (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512. exact Ha.
Qed.

Lemma w4m_bcmp_block_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n i,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= i < Reusable.YG00.req_size n ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false.
Proof.
  intros ly S W mem md p n i HAR Hin Hi.
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  destruct (Reusable.YCbq.range_addressable_of_block segs B LAWS ly S W mem md p n p (Reusable.YG00.req_size n)
              HAR Hin ltac:(lia) ltac:(lia) (p + i) ltac:(lia)) as (s & Hs & _).
  replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (p + i)) with (B.AsanRT.shadow_addr (p + i)) in Hs
    by (unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
  apply (w4m_bcmp_vis_of_aview _ mem).
  - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
  - intros Him. apply segs_low in Him. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.kLowMemEnd in Him.
    Z.div_mod_to_equations. lia.
  - rewrite Hs. discriminate.
Qed.

(* ---- a view kept outside a window [wlo, whi) gives the raw bytes of the frame, its shadow, the spill area and
   KNT's image table (for the walk's cuts: everything the frame-loop bodies read except the live block) ---- *)
Lemma w4m_bcmp_frame_kept : forall cx ly3 S3 W3 mem3 md3 k fr (mem2 : word -> option byte) sp,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCut.c_sp cx - 4096 < sp -> sp <= ACtlCut.c_sp cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a) ->
  MKEPT mem3 mem2 sp (ACtlCut.c_sp cx) /\ MKEPT mem3 mem2 fr (fr + 4096) /\
  MKEPT mem3 mem2 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) /\
  MKEPT mem3 mem2 ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp1 Hsp2 Hk.
  pose proof (w4m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hcl & Hlsp & Hshi & Hshi47 & _). unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  assert (HS : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= lib.Reusable.YM05.alloc_ceiling).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  refine (conj _ (conj _ (conj _ _))).
  - intros a Ha. apply (w4m_bcmp_pt W3); [exact (proj1 (Hpres a ltac:(lia))) | apply Hk; lia].
  - intros a Ha. apply (w4m_bcmp_pt W3); [| apply Hk; lia].
    exact (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_introl Ha))).
  - intros a Ha. apply (w4m_bcmp_pt W3); [| apply Hk; lia].
    refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_intror _))).
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
      Reusable.YG0f.SHADOW_OFF in *. lia.
  - intros a Ha. unfold ACtlCutP.KNA.KIND_NAME in Ha.
    apply (w4m_bcmp_pt W3); [apply Himg; lia | apply Hk; lia].
Qed.

(* The same for a live block and its shadow (the block law gives the bytes present, the shadow law the shadow
   bytes' view, hence their visibility). *)
Lemma w4m_bcmp_block_kept : forall ly S (W : Reusable.YA0n.world segs) mem md (mem2 : word -> option byte)
    wlo whi p n,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  lib.Reusable.YM05.alloc_ceiling <= wlo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a) ->
  MKEPT mem mem2 p (p + Reusable.YG00.req_size n) /\
  (forall i, 0 <= i < Reusable.YG00.req_size n ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))).
Proof.
  intros ly S W mem md mem2 wlo whi p n HAR Hin Hw Hk.
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _ & Hpr & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  split.
  - intros a Ha. apply (w4m_bcmp_pt W); [exact (proj1 (proj1 (Hpr a Ha))) | apply Hk; lia].
  - intros i Hi. apply (w4m_bcmp_pt W).
    + exact (w4m_bcmp_block_shadow_vis ly S W mem md p n i HAR Hin Hi).
    + apply Hk; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- the cut-body predicates across a call that keeps the raw bytes of the regions they read ---- *)
Lemma w4m_bcmp_FRAC : forall cx fr sel R R0 (m m' : word -> option byte),
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  MKEPT m m' (Reusable.YG0d.spZ R0) (ACtlCut.c_sp cx) -> MKEPT m m' fr (fr + 4096) ->
  MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R R0 m m' E2 E3 E4 E8 E9 E19 E26 KS KF KSH
    (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA & HfrA & HA448 &
     Hsp4096 & HspEnd & Q336 & Q48 & Q40 & Qhdr & Q16 & (sh & Hsh & Lsh) & Hsav & Q4088).
  assert (Lsv : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  assert (Lsh' : Z.of_nat (length sh) = 392) by (rewrite Lsh; reflexivity).
  unfold ACtlCutP.FRAME_BYTES in *.
  exists A, sp.
  split; [rewrite E2; exact Hr2 |].
  split; [exact Hspm |].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ |].
  split; [rewrite E4; exact Hr4 |].
  split; [exact (w4m_rgv_tr R R0 8 _ E8 Hr8) |].
  split; [exact (w4m_rgv_tr R R0 9 _ E9 Hr9) |].
  split; [rewrite E3; exact Hr3 |].
  split; [exact (w4m_rgv_tr R R0 19 _ E19 Hr19) |].
  split; [exact (w4m_rgv_tr R R0 26 _ E26 Hr26) |].
  do 8 (split; [assumption |]).
  split; [apply (w4m_bcmp_q64 m m' (A + 336) fr); [intros x Hx; apply KS; lia | exact Q336] |].
  split; [apply (w4m_bcmp_q64 m m' (A + 48) sel); [intros x Hx; apply KS; lia | exact Q48] |].
  split; [apply (w4m_bcmp_q64 m m' (A + 40) fr); [intros x Hx; apply KS; lia | exact Q40] |].
  split; [apply (w4m_bcmp_q64 m m' fr _); [intros x Hx; apply KF; lia | exact Qhdr] |].
  split; [apply (w4m_bcmp_q64 m m' (fr + 16) _); [intros x Hx; apply KF; lia | exact Q16] |].
  split; [exists sh; split; [apply (w4m_bcmp_bytes m m' _ sh); [intros x Hx; apply KSH; lia | exact Hsh] |
    exact Lsh] |].
  split; [apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KS; rewrite Lsv in Hx; lia | exact Hsav] |].
  apply (w4m_bcmp_q64 m m' (fr + 4088) _); [intros x Hx; apply KF; lia | exact Q4088].
Qed.

Lemma w4m_bcmp_HB : forall (m m' : word -> option byte) phi len,
  (forall i, 0 <= i < B.ACtlK.a_size len ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof. intros m m' phi len K (H0 & H1). split; [exact H0 | exact (w4m_bcmp_addr m m' phi _ K H1)]. Qed.

Lemma w4m_bcmp_FTK : forall cx j fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 ->
  getr R 25 = getr R0 25 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m'.
Proof.
  intros cx j fr R R0 m m' A csp HA E9 E22 E24 E25 H0 H1 H2 KS (H184 & H22 & H24 & H272 & H25).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (w4m_bcmp_sp R R0 m m' A csp 184 _ HA E9 H0 H1 H2 KS ltac:(lia) H184).
  - exact (w4m_rgv_tr R R0 22 _ E22 H22).
  - exact (w4m_rgv_tr R R0 24 _ E24 H24).
  - exact (w4m_bcmp_sp R R0 m m' A csp 272 _ HA E9 H0 H1 H2 KS ltac:(lia) H272).
  - exact (w4m_rgv_tr R R0 25 _ E25 H25).
Qed.

Lemma w4m_bcmp_FTURN : forall cx j phi R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> MKEPT m m' phi (phi + ACtlCutP.flen cx j) ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m'.
Proof.
  intros cx j phi R R0 m m' A csp HA E9 H0 H1 H2 KS KB (H224 & H232 & Hphi & Hlen).
  unfold ACtlCutP.flen in KB.
  refine (conj _ (conj _ (conj _ Hlen))).
  - exact (w4m_bcmp_sp R R0 m m' A csp 224 _ HA E9 H0 H1 H2 KS ltac:(lia) H224).
  - exact (w4m_bcmp_sp R R0 m m' A csp 232 _ HA E9 H0 H1 H2 KS ltac:(lia) H232).
  - apply (w4m_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
Qed.

Lemma w4m_bcmp_IFS : forall cx fr j R R0 (m m' : word -> option byte),
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' KF KSH ((HID & Hidok) & (HFG & Hfgok) & (Hhave & Hnb & Hbody & Had & HFI)).
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LBD.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb in *.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj _ HFI)))))).
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HID].
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HFG].
  - apply (w4m_bcmp_u32 m m' _ _); [intros x Hx; apply KF; lia | exact Hhave].
  - apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KF; lia | exact Hnb].
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact Hbody].
  - apply (w4m_bcmp_addr m m' _ _); [| exact Had]. intros i Hi. apply KSH.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma w4m_bcmp_FLI : forall cx fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m'.
Proof.
  intros cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Hs; exact (w4m_bcmp_sp R R0 m m' A csp off v HA E9 H0 H1 H2 KS Ho Hs)).
  assert (AD : forall p n, fr <= p -> p + n <= fr + 4000 -> 0 <= n ->
                 B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n).
  { intros p n Hp1 Hp2 Hn Hp. apply (w4m_bcmp_addr m m' p n); [| exact Hp].
    intros i Hi. apply KSH. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (LKN : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  unfold ACtlCutP.FLI in *.
  destruct HFLI as (H27 & HFLI).
  split; [exact (w4m_rgv_tr R R0 27 _ E27 H27) |].
  do 21 (destruct HFLI as (Hsp & HFLI); split; [apply SP; [lia | exact Hsp] | clear Hsp]).
  destruct HFLI as (Had & Hstk & HRAD & HKNT & Hs168 & Hs88).
  split; [apply AD; [lia | lia | lia | exact Had] |].
  split; [exact (w4m_bcmp_stk m m' fr _ Hpr Hstk) |].
  split.
  { unfold ACtlCutP.RAD, ACtlCutP.fragb in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
    split; [apply AD; [lia | lia | lia | exact Ra1] |].
    split; [apply AD; [lia | lia | lia | exact Ra2] |].
    apply AD; [lia | lia | lia | exact Ra3]. }
  split.
  { unfold ACtlCutP.KNT in *. destruct HKNT as (Hkb & _). split; [| exact HKA].
    apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KK; rewrite LKN in Hx; lia | exact Hkb]. }
  split; [apply SP; [lia | exact Hs168] | apply SP; [lia | exact Hs88]].
Qed.

Lemma w4m_bcmp_LK : forall cx fr j R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr (Hj & S240 & HOUR & HFLI).
  refine (conj Hj (conj (w4m_bcmp_sp R R0 m m' A csp 240 _ HA E9 H0 H1 H2 KS ltac:(lia) S240) (conj _ _))).
  - unfold ACtlCutP.OURb in *. apply (w4m_bcmp_bytes m m' _ _); [| exact HOUR].
    rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply KF. lia.
  - exact (w4m_bcmp_FLI cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   CALL-STAGE HELPERS (proved here). *)

(* ctl_rt_C (route C) at a cut or post-call state whose journal starts at the walk's entry (owner ruling 06:46Z):
   ctl_base's read-only view (arodata_okS, YCfn.v:40) as ProgWorld's arodata_okP (arodata_okP_of_S), moved by the
   journal (APostBase.arodata_ok_journalP under RELRO_IMG and RO_OFL), then the PROVED
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR on the journal's AR (CtrlTSyms + AR_laws; no vis0 / owned_ro). *)
Lemma w4_ctlrt : forall cx own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  ctl_base cx -> AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _) & _).
  pose proof (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Haro ltac:(lia) ltac:(lia)) as Hp0.
  pose proof (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hp0) as Hp.
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 (proj1 HJ) Hp).
Qed.

(* ctl_rt_C's frame region (cut_shadow's first disjunct): the 512 shadow bytes of the owned class-6 frame. *)
Lemma w4_cut_fsh : forall (cx : ACtlCut.ctlcx) ly3 S3 fr a,
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) ->
  ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
  B.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros cx ly3 S3 fr a Hin Efr Ha. left. do 2 eexists. split; [exact Hin|].
  rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512.
  unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* ctl_rt_C's image region (img_shadow): a shadow byte of the image hull [IMG_LO, IMG_HI) = [0x10000, 0x5fe000),
   i.e. [SHADOW_OFF + 0x10000 / 8, SHADOW_OFF + 0x5fe000 / 8) = [0x7fffa000, 0x800b7c00). *)
Lemma w4_img_sh : forall s, 0x7fffa000 <= s < 0x800b7c00 -> B.ACtlRtC.img_shadow s.
Proof.
  intros s Hs. exists ((s - 0x7fff8000) * 8).
  unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  rewrite Z.div_mul by lia. split; lia.
Qed.

(* A cut register as the run's register word (the runs name lib/Lib's reg_get; the cut's rgv the core's getr). *)
Lemma w4_rgv_reg : forall (regs : bvmap 5 word) (r : bv 5) v,
  bv_eqb r 0 = false -> ACtlCut.rgv regs r v -> LinuxProcessSemantics.Riscv.Sem.reg_get regs r = Z_to_bv 64 v.
Proof. intros regs r v E H. unfold ACtlCut.rgv, lib.Reusable.YK11.getr in H. rewrite E in H. exact H. Qed.

(* The turn's 50-byte record. *)
Lemma w4_tg_len : forall inp jn, length (ACtlCutP.SM.t_g inp jn) = 50%nat.
Proof.
  intros inp jn. unfold ACtlCutP.SM.t_g, ACtlCutP.SM.fr50.
  rewrite length_firstn, length_app, repeat_length. lia.
Qed.

Lemma w4_skipn_cons : forall (l : list byte) (n : nat) (d : byte), (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  induction l as [|x l IH]; intros [|n] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

(* The two record bytes Phi[18], Phi[19] as the first two bytes of the turn block t_blk = bsl g 18 32. *)
Lemma w4_blk01 : forall (m : word -> option byte) (a : Z) (g : list byte), length g = 50%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (ACtlCutP.RFR.bsl g 18 32) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a [ACtlCutP.RPA.cp_b g 18; ACtlCutP.RPA.cp_b g 19].
Proof.
  intros m a g Hl (H0 & H1 & H).
  assert (L : length (ACtlCutP.RFR.bsl g 18 32) = 32%nat)
    by (unfold ACtlCutP.RFR.bsl; rewrite length_firstn, length_skipn, Hl; reflexivity).
  rewrite L in H1. rewrite L in H.
  unfold ACtlCutP.RFR.bsl in H. change (Z.to_nat 32) with 32%nat in H. change (Z.to_nat 18) with 18%nat in H.
  rewrite (w4_skipn_cons g 18 ACtlCutP.RPA.cp_z) in H by lia.
  rewrite (w4_skipn_cons g 19 ACtlCutP.RPA.cp_z) in H by lia.
  split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|i]]; [| |lia].
  - rewrite (H 0%nat ltac:(lia)). reflexivity.
  - rewrite (H 1%nat ltac:(lia)). reflexivity.
Qed.

(* A sub-range of an addressable range. *)
Lemma w4_addr_sub : forall (m : word -> option byte) p n q k,
  B.AsanRT.addressable m p n -> p <= q -> 0 <= k -> q + k <= p + n -> B.AsanRT.addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hqk.
  split; [lia|]. split; [exact Hk|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* Every shadow byte between the shadow bytes of x and y is the shadow byte of an address between them. *)
Lemma w4_sh_between : forall x y a, 0 <= x <= y ->
  B.AsanRT.shadow_addr x <= a <= B.AsanRT.shadow_addr y ->
  exists z, x <= z <= y /\ B.AsanRT.shadow_addr z = a.
Proof.
  intros x y a Hxy Ha. unfold B.AsanRT.shadow_addr in *.
  exists (Z.max x (8 * (a - B.AsanRT.ASAN_K))).
  split; [Z.div_mod_to_equations; lia|].
  destruct (Z.max_spec x (8 * (a - B.AsanRT.ASAN_K))) as [(Hm & E) | (Hm & E)]; rewrite E.
  - rewrite Z.mul_comm, Z.div_mul by lia. lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* A raw munch keeps the bytes of every range outside its write set. *)
Lemma w4_munch_kept : forall Wr (m m' : word -> option byte) lo hi,
  lib.Lib.Frame.munch Wr m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> lib.Lib.Frame.outside Wr x) -> MKEPT m m' lo hi.
Proof. intros Wr m m' lo hi MU H0 H1 Ho x Hx. exact (w4k_mrd_munch Wr m m' x MU ltac:(lia) (Ho x Hx)). Qed.

(* FM across a call that keeps the spill area. *)
Lemma w4_FM_keep : forall cx j phi fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 ->
  getr R 25 = getr R0 25 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  ACtlCutP.FM cx j phi fr R0 m -> ACtlCutP.FM cx j phi fr R m'.
Proof.
  intros cx j phi fr R R0 m m' A csp HA E9 E22 E24 E25 H0 H1 H2 KS (S184 & R24 & R22 & R25 & S312).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (w4m_bcmp_sp R R0 m m' A csp 184 _ HA E9 H0 H1 H2 KS ltac:(lia) S184).
  - exact (w4m_rgv_tr R R0 24 _ E24 R24).
  - exact (w4m_rgv_tr R R0 22 _ E22 R22).
  - exact (w4m_rgv_tr R R0 25 _ E25 R25).
  - exact (w4m_bcmp_sp R R0 m m' A csp 312 _ HA E9 H0 H1 H2 KS ltac:(lia) S312).
Qed.

(* A stretch whose post is itself a run (a `_pre_F` lemma with a continuation premise, then the callee's run). *)
Lemma w4_evtF_join : forall RNG (Q : machine_state -> Prop) ms,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG (lib.Lib.ExecF.evtF B.Img0.rsegs RNG Q) ms ->
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG Q ms.
Proof. intros RNG Q ms H. exact (lib.Lib.ExecF.evtF_cut _ _ _ _ _ H (fun _ h => h)). Qed.

(* Two 8-byte words read at one address are the same word. *)
Lemma w4_q64_det : forall (m : word -> option byte) a v1 v2,
  ACtlCutP.q64 m a v1 -> ACtlCutP.q64 m a v2 -> Z_to_bv 64 v1 = Z_to_bv 64 v2.
Proof.
  intros m a v1 v2 (_ & _ & H1) (_ & _ & H2).
  assert (E : lib.Lib.Mem.le8 (Z_to_bv 64 v1) = lib.Lib.Mem.le8 (Z_to_bv 64 v2)).
  { apply w4m_bcmp_list_eq; [rewrite !lib.Lib.Mem.length_le8; reflexivity|].
    intros k Hk. pose proof Hk as Hk2. rewrite lib.Lib.Mem.length_le8 in Hk2.
    rewrite <- (H1 k Hk), <- (H2 k ltac:(rewrite lib.Lib.Mem.length_le8; exact Hk2)). reflexivity. }
  pose proof (lib.Lib.Mem.le_bytes_to_word_le8 (Z_to_bv 64 v1)) as L1.
  pose proof (lib.Lib.Mem.le_bytes_to_word_le8 (Z_to_bv 64 v2)) as L2.
  rewrite E in L1. rewrite L1 in L2. exact L2.
Qed.

(* memcmp_model n = Some 0: the first n bytes agree. *)
Lemma w4_memcmp0 : forall n (l r : list byte), ACtlCutP.SFA.memcmp_model l r n = Some 0 -> firstn n l = firstn n r.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] H; cbn in H |- *; try discriminate; [reflexivity .. |].
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
  - f_equal; [apply bv_eq; exact E | exact (IH l r H)].
  - injection H as H. lia.
Qed.

Lemma w4_nth_error_firstn : forall (l : list byte) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros [|n] [|i] H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma w4_bytes_firstn : forall (m : word -> option byte) a (bs : list byte) n,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H). split; [exact H0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite (H i ltac:(lia)).
  symmetry. apply w4_nth_error_firstn. lia.
Qed.

(* The shadow hull of a range inside the owned frame (ported from W4f c8fda648d4e, w4f_bcmp_hull_frame). *)
Lemma w4m_bcmp_hull_frame : forall cx ly3 S3 W3 mem3 md3 k fr d n,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr + 56 <= d -> d + n + 64 <= fr + 4096 -> 0 < n ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3) d n.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr d n HJ HG1 H1 H2 H3 s Hs.
  apply (Reusable.YCbq.aview_some_of_apresent segs).
  apply (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr s HJ HG1). right.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* A zero shadow byte of x (as the runs state it, Z.shiftr x 3 + ASAN_K) keeps across a step that keeps that byte. *)
Lemma w4_sh_b8_keep : forall (m m' : word -> option byte) x, 0 <= x ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr x)) =
  lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr x)) ->
  ACtlCutP.b8 m (Z.shiftr x 3 + B.ACtlK.ASAN_K) 0 -> ACtlCutP.b8 m' (Z.shiftr x 3 + B.ACtlK.ASAN_K) 0.
Proof.
  intros m m' x Hx K H. apply (w4m_bcmp_b8 m m' _ 0); [|exact H].
  intros y Hy. assert (E : y = B.AsanRT.shadow_addr x).
  { unfold B.AsanRT.shadow_addr. unfold B.ACtlK.ASAN_K in Hy.
    rewrite Z.shiftr_div_pow2 in Hy by lia. change (2 ^ 3) with 8 in Hy. lia. }
  rewrite E. exact K.
Qed.

(* The hull of a sub-range of a live block is inside the block's hull, which AR_shadow_law states visible. *)
Lemma w4_block_hull_sub : forall ly S (W : Reusable.YA0n.world segs) mem md p n x len,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= p -> p <= x -> 0 < len -> x + len <= p + Reusable.YG00.req_size n ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x len.
Proof.
  intros ly S W mem md p n x len HAR Hin Hp Hx Hl Hxl s Hs.
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hhull).
  apply Hhull.
  pose proof (Reusable.YCbq.shadow_mono p x Hx) as M1.
  pose proof (Reusable.YCbq.shadow_mono (x + len - 1) (p + Reusable.YG00.req_size n - 1) ltac:(lia)) as M2.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* The record invariant across a step that keeps the bytes it reads: the spills [A + 248, A + 320), the record bytes
   [phi + 14, phi + 50), the halfword [kp + 20, kp + 22) and the shadow bytes of phi + 14 .. phi + 17. *)
Lemma w4_rec_inv_keep : forall cx j phi A kp (m m' : word -> option byte),
  ACtlCutP.rec_inv cx j phi A kp m ->
  MKEPT m m' (A + 248) (A + 320) -> MKEPT m m' (phi + 14) (phi + 50) -> MKEPT m m' (kp + 20) (kp + 22) ->
  (forall i, 14 <= i < 18 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))) ->
  ACtlCutP.rec_inv cx j phi A kp m'.
Proof.
  intros cx j phi A kp m m' (H0 & H50 & Hfl & Htk & Happ & Q312 & Hb18 & Hb34 &
    (f16 & v14 & v15 & v16 & v17 & Q248 & Hu16 & Hkp22 & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 & R14 & R15 & R16 & R17 &
     S14 & S15 & S16 & S17 & Hf & Hk)) KA KP KK KS.
  pose proof (B.Prog.Seg.F21.t_blk_len (ACtlCut.c_in cx) j) as Lb.
  assert (Ls : length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) j) 34 6) = 6%nat)
    by (unfold ACtlCutP.RFR.bsl; rewrite length_firstn, length_skipn, w4_tg_len; reflexivity).
  refine (conj H0 (conj H50 (conj Hfl (conj Htk (conj Happ (conj _ (conj _ (conj _ _)))))))).
  - apply (w4m_bcmp_q64 m m' _ _); [intros x Hx; apply KA; lia | exact Q312].
  - apply (w4m_bcmp_bytes m m' _ _); [rewrite Lb; intros x Hx; apply KP; lia | exact Hb18].
  - apply (w4m_bcmp_bytes m m' _ _); [rewrite Ls; intros x Hx; apply KP; lia | exact Hb34].
  - exists f16, v14, v15, v16, v17.
    refine (conj _ (conj _ (conj Hkp22 (conj Hkp0 (conj _ (conj _ (conj _ (conj _ (conj R14 (conj R15 (conj R16
      (conj R17 (conj _ (conj _ (conj _ (conj _ (conj Hf Hk))))))))))))))))).
    + apply (w4m_bcmp_q64 m m' _ _); [intros x Hx; apply KA; lia | exact Q248].
    + unfold ACtlCutP.u16 in *. apply (w4m_bcmp_bytes m m' _ _); [| exact Hu16].
      rewrite lib.Lib.Mem.length_le2. intros x Hx. apply KK. lia.
    + apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KP; lia | exact Hb14].
    + apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KP; lia | exact Hb15].
    + apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KP; lia | exact Hb16].
    + apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KP; lia | exact Hb17].
    + apply (w4_sh_b8_keep m m' (phi + 14)); [lia | apply KS; lia | exact S14].
    + apply (w4_sh_b8_keep m m' (phi + 15)); [lia | apply KS; lia | exact S15].
    + apply (w4_sh_b8_keep m m' (phi + 16)); [lia | apply KS; lia | exact S16].
    + apply (w4_sh_b8_keep m m' (phi + 17)); [lia | apply KS; lia | exact S17].
Qed.

(* ---- seg_F23's transports.  Across seg_F23 the bytes change at the spill [A + 272, A + 280) and the frame shadow
   bytes Sfr fr + 16 / + 17 (the stretch's two stores), and at the copy's destination [fr + 128, fr + 140) (the
   memcpy).  The body of 0x82878 reads none of them except through the new values, so each carried bundle is kept
   from the bytes it does read: the spills in [A + 40, A + 272) and [A + 280, c_sp), the frame header [fr, fr + 24),
   the frame tail [fr + 2624, fr + 4096) and its shadow [Sfr fr + 328, Sfr fr + 512), and the presence of the 392
   frame-shadow bytes FRAC quantifies over.  (Proofs as the w4m_bcmp_ ones, with the narrower kept ranges.) *)
Lemma w4_sp2 : forall R R0 (m m' : word -> option byte) A csp off v,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' (A + 40) (A + 272) -> MKEPT m m' (A + 280) csp ->
  (40 <= off /\ off + 8 <= 272 \/ 280 <= off <= 440) ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros R R0 m m' A csp off v HA E9 H0 H1 H2 K1 K2 Hoff Hs.
  pose proof (w4m_spill R0 m off v A Hs HA ltac:(lia) ltac:(lia)) as Hq.
  exists A. split; [exact (w4m_rgv_tr R R0 9 A E9 HA) |].
  apply (w4m_bcmp_q64 m m' (A + off) v); [| exact Hq].
  intros x Hx. destruct Hoff as [Hoff | Hoff]; [apply K1 | apply K2]; lia.
Qed.

Lemma w4_FLI2 : forall cx fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' (A + 40) (A + 272) -> MKEPT m m' (A + 280) csp ->
  MKEPT m m' (fr + 2624) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 328) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m'.
Proof.
  intros cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS1 KS2 KF KSH KK HKA Hpr HFLI.
  assert (SP : forall off v, 88 <= off <= 440 -> (off + 8 <= 272 \/ 280 <= off) ->
                 ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Ho' Hs; exact (w4_sp2 R R0 m m' A csp off v HA E9 H0 H1 H2 KS1 KS2 ltac:(lia) Hs)).
  assert (AD : forall p n, fr + 2624 <= p -> p + n <= fr + 4000 -> 0 <= n ->
                 B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n).
  { intros p n Hp1 Hp2 Hn Hp. apply (w4m_bcmp_addr m m' p n); [| exact Hp].
    intros i Hi. apply KSH. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (LKN : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  unfold ACtlCutP.FLI in *.
  destruct HFLI as (H27 & HFLI).
  split; [exact (w4m_rgv_tr R R0 27 _ E27 H27) |].
  do 21 (destruct HFLI as (Hsp & HFLI); split; [apply SP; [lia | lia | exact Hsp] | clear Hsp]).
  destruct HFLI as (Had & Hstk & HRAD & HKNT & Hs168 & Hs88).
  split; [apply AD; [lia | lia | lia | exact Had] |].
  split; [exact (w4m_bcmp_stk m m' fr _ Hpr Hstk) |].
  split.
  { unfold ACtlCutP.RAD, ACtlCutP.fragb in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
    split; [apply AD; [lia | lia | lia | exact Ra1] |].
    split; [apply AD; [lia | lia | lia | exact Ra2] |].
    apply AD; [lia | lia | lia | exact Ra3]. }
  split.
  { unfold ACtlCutP.KNT in *. destruct HKNT as (Hkb & _). split; [| exact HKA].
    apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KK; rewrite LKN in Hx; lia | exact Hkb]. }
  split; [apply SP; [lia | lia | exact Hs168] | apply SP; [lia | lia | exact Hs88]].
Qed.

Lemma w4_LK2 : forall cx fr j R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' (A + 40) (A + 272) -> MKEPT m m' (A + 280) csp ->
  MKEPT m m' (fr + 2624) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 328) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A csp HA E9 E27 H0 H1 H2 KS1 KS2 KF KSH KK HKA Hpr (Hj & S240 & HOUR & HFLI).
  refine (conj Hj (conj (w4_sp2 R R0 m m' A csp 240 _ HA E9 H0 H1 H2 KS1 KS2 ltac:(lia) S240) (conj _ _))).
  - unfold ACtlCutP.OURb in *. apply (w4m_bcmp_bytes m m' _ _); [| exact HOUR].
    rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply KF. lia.
  - exact (w4_FLI2 cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS1 KS2 KF KSH KK HKA Hpr HFLI).
Qed.

Lemma w4_IFS2 : forall cx fr j R R0 (m m' : word -> option byte),
  MKEPT m m' (fr + 2624) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 328) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' KF KSH ((HID & Hidok) & (HFG & Hfgok) & (Hhave & Hnb & Hbody & Had & HFI)).
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LBD.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb in *.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj _ HFI)))))).
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HID].
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HFG].
  - apply (w4m_bcmp_u32 m m' _ _); [intros x Hx; apply KF; lia | exact Hhave].
  - apply (w4m_bcmp_b8 m m' _ _); [intros x Hx; apply KF; lia | exact Hnb].
  - apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact Hbody].
  - apply (w4m_bcmp_addr m m' _ _); [| exact Had]. intros i Hi. apply KSH.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma w4_FRAC2 : forall cx fr sel R R0 (m m' : word -> option byte),
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  (forall A, ACtlCut.rgv R0 9 A -> 0 <= A -> A + 448 <= ACtlCut.c_sp cx ->
     MKEPT m m' (A + 40) (A + 272) /\ MKEPT m m' (A + 280) (ACtlCut.c_sp cx)) ->
  MKEPT m m' fr (fr + 24) -> MKEPT m m' (fr + 2624) (fr + 4096) ->
  (forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
     exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = Some b) ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R R0 m m' E2 E3 E4 E8 E9 E19 E26 KS KF1 KF2 KSh
    (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA & HfrA & HA448 &
     Hsp4096 & HspEnd & Q336 & Q48 & Q40 & Qhdr & Q16 & (sh & Hsh & Lsh) & Hsav & Q4088).
  assert (HA0 : 0 <= A).
  { pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr R0 2)) as Hr. unfold Reusable.YG0d.spZ in HspZ. lia. }
  destruct (KS A Hr9 HA0 HA448) as (KS1 & KS2).
  assert (Lsv : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  unfold ACtlCutP.FRAME_BYTES in *.
  exists A, sp.
  split; [rewrite E2; exact Hr2 |].
  split; [exact Hspm |].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ |].
  split; [rewrite E4; exact Hr4 |].
  split; [exact (w4m_rgv_tr R R0 8 _ E8 Hr8) |].
  split; [exact (w4m_rgv_tr R R0 9 _ E9 Hr9) |].
  split; [rewrite E3; exact Hr3 |].
  split; [exact (w4m_rgv_tr R R0 19 _ E19 Hr19) |].
  split; [exact (w4m_rgv_tr R R0 26 _ E26 Hr26) |].
  do 8 (split; [assumption |]).
  split; [apply (w4m_bcmp_q64 m m' (A + 336) fr); [intros x Hx; apply KS2; lia | exact Q336] |].
  split; [apply (w4m_bcmp_q64 m m' (A + 48) sel); [intros x Hx; apply KS1; lia | exact Q48] |].
  split; [apply (w4m_bcmp_q64 m m' (A + 40) fr); [intros x Hx; apply KS1; lia | exact Q40] |].
  split; [apply (w4m_bcmp_q64 m m' fr _); [intros x Hx; apply KF1; lia | exact Qhdr] |].
  split; [apply (w4m_bcmp_q64 m m' (fr + 16) _); [intros x Hx; apply KF1; lia | exact Q16] |].
  split.
  { change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Lsh |- *.
    destruct Hsh as (Hs0 & Hs1 & _). rewrite Lsh in Hs1.
    destruct (w4k_bytes_of_mrd m' 392 (ACtlCutP.Sfr fr) Hs0 Hs1 KSh) as (sh' & Hl & Hb).
    exists sh'. split; [exact Hb | exact Hl]. }
  split; [apply (w4m_bcmp_bytes m m' _ _); [intros x Hx; apply KS2; rewrite Lsv in Hx; lia | exact Hsav] |].
  apply (w4m_bcmp_q64 m m' (fr + 4088) _); [intros x Hx; apply KF2; lia | exact Q4088].
Qed.

(* One byte of a range, present. *)
Lemma w4_ba_rd : forall (m : word -> option byte) a (bs : list byte) x,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

(* A byte the copy wrote: the view at the destination equals the view at the source, both visible. *)
Lemma w4_copy_byte : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) a s (ob : option byte),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false -> Reusable.YA0n.w_H W (Z_to_bv 64 s) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m s ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 s) = ob -> ob <> None ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = ob.
Proof.
  intros W m m' a s ob Ha Hs E Hb Hn. destruct ob as [b|]; [|congruence].
  rewrite (aview_vis_mrd W m' a Ha), (aview_vis_mrd W m s Hs), Hb in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a)) as [b'|]; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma w4_FTURN2 : forall cx j phi R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' (A + 40) (A + 272) -> MKEPT m m' (A + 280) csp -> MKEPT m m' phi (phi + ACtlCutP.flen cx j) ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m'.
Proof.
  intros cx j phi R R0 m m' A csp HA E9 H0 H1 H2 KS1 KS2 KB (H224 & H232 & Hphi & Hlen).
  unfold ACtlCutP.flen in KB.
  refine (conj _ (conj _ (conj _ Hlen))).
  - exact (w4_sp2 R R0 m m' A csp 224 _ HA E9 H0 H1 H2 KS1 KS2 ltac:(lia) H224).
  - exact (w4_sp2 R R0 m m' A csp 232 _ HA E9 H0 H1 H2 KS1 KS2 ltac:(lia) H232).
  - apply (w4m_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82634_at j (0x82634) --S_F18--> B8264c_at j | B82abc_at j.
   0x82634 ld a0,272(s1); beqz a0,82abc; li a2,6; ld a0,112(s1); mv a1,s2; jal 0x42aac (ra 0x8264c).
   The word [A+272] is b2z (t_8819 j) (the body's w272 with its two t_8819 implications): t_8819 j = false takes
   the beqz to 0x82abc with no memory change; t_8819 j = true runs to the bcmp trampoline.
   SINK BRANCHES on the stretch: none (no branch to 0x82fa4 / 0x82fa0 in [0x82634, 0x8264c), objdump L85210-L85215). *)
Lemma seg_F18 : forall POST (j : nat),
  ctl_from POST (ix C_B8264c_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82abc_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82634_at [Z.of_nat j]).
Proof.
  intros POST j H64c Habc cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell), by the case on t_8819 j that the word [A + 272] and the beqz at 0x82638 decide.
     ARM false: f18_evt_skip_F (0x82634 -> 0x82abc, a0 = 0, memory unchanged), one lift; C_B82abc_at from the
     carried body, FTK's spill 272 = t_k j from [A + 272] = 0 = t_k j (F18.f18_tk0).
     ARM true: f18_pre_F (0x82634 -> the bcmp trampoline 0x42aac, ra = 0x8264c), one lift; the trampoline by
     YCbq.aj_bcmp_at (x := L = fr + 186, FLI's spill 112; y := phi; n := 6); v = 0 from memcmp_model ls rs 6 =
     Some 0; C_B8264c_at from the L2 group (its first six bytes) and rec_inv (w4_rec_inv_keep), every byte kept over
     visible addresses; ctl_rt by w4_ctlrt. *)
  unfold ACtlCutP.C_B82634_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM &
    (A' & kp & w272 & Hr9' & HA' & HspA' & H18 & H24 & Q280 & Q272 & Hw272 & Hfalse & Htrue) & HFT & HIFS).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1) as (_ & _ & Bfr1 & Bfr2 & HfrApp & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  assert (EA : A' = A).
  { apply w4k_bv_inj; [lia | lia |]. unfold ACtlCut.rgv in Hr9', Hr9. rewrite <- Hr9'. exact Hr9. }
  subst A'.
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _).
  pose proof HFM as (S184 & H24' & H22 & H25 & S312).
  destruct (ACtlCutP.SM.t_8819 (ACtlCut.c_in cx) jj) eqn:E8819.
  2: {
    (* ARM false: 0x82634 -> 0x82abc *)
    pose proof (Hfalse eq_refl) as Ew. subst w272.
    pose proof (B.Prog.Seg.F18.f18_tk0 (ACtlCut.c_in cx) jj E8819) as Htk0.
    apply w4m_enter.
    eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
    { unfold lib.Lib.Regs6ss.mkR_of.
      eapply (B.Prog.Seg.F18F.f18_evt_skip_F) with (A := A) (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
      - exact (w4_rgv_reg _ 9 _ eq_refl Hr9).
      - exact Q272.
      - apply B.ProgBridge.rng_of_visible.
        apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
    intros ms' md' -> Hs _.
    apply (w4m_exit W3 0x82abc).
    match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
    assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
    assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
    assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
    assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
    assert (E9 : getr R1 9 = getr regs3 9) by (transitivity (Z_to_bv 64 A); [reflexivity | symmetry; exact Hr9]).
    assert (E18 : getr R1 18 = getr regs3 18) by reflexivity.
    assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
    assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
    assert (E22 : getr R1 22 = getr regs3 22) by reflexivity.
    assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
    assert (E25 : getr R1 25 = getr regs3 25) by reflexivity.
    assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
    assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
    apply (Habc cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem3 md' HB (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) HF HG1 Hk);
      [| exact HRT].
    unfold ACtlCutP.C_B82abc_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
    split; [reflexivity|].
    split; [exact (w4m_FRAC_tr cx fr fr R1 regs3 mem3 E2 E3 E4 E8 E9 E19 E26 HFRAC)|].
    exists phi.
    split; [exact Hperm|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (w4m_rgv_tr R1 regs3 18 _ E18 H18)|].
    split; [exact (w4m_rgv_tr R1 regs3 20 _ E20 H20)|].
    split; [exact (w4m_FTURN_tr cx jj phi R1 regs3 mem3 E9 HFT)|].
    split; [exact (w4m_LK_tr cx fr jj R1 regs3 mem3 E9 E27 HLK)|].
    split.
    { refine (conj (w4m_spill_tr R1 regs3 mem3 _ _ E9 S184) (conj (w4m_rgv_tr R1 regs3 22 _ E22 H22)
        (conj (w4m_rgv_tr R1 regs3 24 _ E24 H24) (conj _ (w4m_rgv_tr R1 regs3 25 _ E25 H25))))).
      exists A. split; [unfold ACtlCut.rgv; reflexivity|]. rewrite Htk0. exact Q272. }
    split; [exact (w4m_IFS_tr cx fr (S jj) R1 regs3 mem3 HIFS)|].
    exact (w4m_spill_tr R1 regs3 mem3 _ _ E9 S312). }
  (* ARM true: 0x82634 -> 0x42aac -> 0x8264c *)
  destruct (Htrue eq_refl) as (Hw272nz & HREC & L & L2 & ls & rs & ls2 & rs2 & Q112 & HL & Hls & Hlenls & Hrs &
    Hlenrs & Hmc & HadL & HadP & HapL6 & HapL7 & HapP6 & HapP7 & HwL & HwP & HwP50 & Hwkp & Q96 & HL2 & Hls2 &
    Hlen2 & Hrs2 & Hrlen2 & Hmc2 & HadL2 & HadP6 & HapL26 & HapL27 & HapP12 & HapP13 & HwL2 & HwP6).
  pose proof HREC as (Hphi0 & Hphi50 & Hflen & Htk & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Hkp22 & Hkp0 & _)).
  (* L = fr + 186, L2 = fr + 180, kp = fr + 176 (FLI's spills 112 / 96 / 280) *)
  pose proof HLK as (_ & _ & _ & (_ & _ & S96 & S112 & _ & _ & _ & _ & _ & S280 & _)).
  pose proof (w4m_spill regs3 mem3 112 (fr + 186) A S112 Hr9 ltac:(lia) ltac:(lia)) as Q112'.
  pose proof (w4m_spill regs3 mem3 96 (fr + 180) A S96 Hr9 ltac:(lia) ltac:(lia)) as Q96'.
  pose proof (w4m_spill regs3 mem3 280 (fr + 176) A S280 Hr9 ltac:(lia) ltac:(lia)) as Q280'.
  assert (EL : L = fr + 186) by (apply w4k_bv_inj; [lia | lia | exact (w4_q64_det _ _ _ _ Q112 Q112')]).
  assert (EL2 : L2 = fr + 180) by (apply w4k_bv_inj; [lia | lia | exact (w4_q64_det _ _ _ _ Q96 Q96')]).
  assert (Ekp : kp = fr + 176) by (apply w4k_bv_inj; [lia | lia | exact (w4_q64_det _ _ _ _ Q280 Q280')]).
  subst L L2 kp.
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (Hp16 & Hp4096 & Hpc & Happp & Hbpr & _).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  apply w4m_enter.
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply (B.Prog.Seg.F18F.f18_pre_F) with (A := A) (L := fr + 186) (R := phi) (w272 := w272)
      (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
    - exact (w4_rgv_reg _ 9 _ eq_refl Hr9).
    - exact (w4_rgv_reg _ 18 _ eq_refl H18).
    - exact Q272.
    - exact Hw272nz.
    - exact Hw272.
    - exact Q112.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
  intros ms' md' -> Hs _.
  apply (w4m_exit W3 0x42aac).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  change 0x42aac with B.Prog.bcmp_wrap_c.BCMP_WRAP. rewrite <- B_bcmp_tramp_at.
  pose proof (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) as HJ'.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  (* the bcmp trampoline, x = fr + 186, y = phi, n = 6 *)
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_bcmp_at segs B LAWS segs_low _ H_bcmp W3 R1 mem3 Reusable.YCfn.LLVMF_STK
      (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 md' k (fr + 186) phi 6 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x8264c) HJ').
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspR1. lia.
    - rewrite Zminus_mod, Hspm, Hsp16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - transitivity (getr regs3 3); [reflexivity | rewrite Hr3; exact Hgp0].
    - exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs).
        apply (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). left. lia.
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs). exact (proj1 (Hbpr a ltac:(lia))).
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - apply (w4k_amem_frame fr); [exact Bfr1 | exact Bfr2 | exact HfrApp | lia | lia].
    - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL in Happp.
      unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - apply (w4m_bcmp_range_addr W3 mem3 (fr + 186) 6); [| exact HadL].
      intros i Hi. refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4m_bcmp_hull_frame cx ly3 S3 W3 mem3 md3 k fr); [exact HJ | exact HG1 | lia | lia | lia].
    - apply (w4m_bcmp_range_addr W3 mem3 phi 6); [| exact HadP].
      intros i Hi. apply (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ i HAR Hin). lia.
    - intros _. apply (w4_block_hull_sub ly3 S3 W3 mem3 md3 phi _ phi 6 HAR Hin); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr2 & Hpres2).
  assert (Hv0 : v = Reusable.YG0d.w64 0).
  { assert (Vx : forall i, 0 <= i < 6 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (fr + 186 + i)) = false).
    { intros i Hi.
      assert (Ha' : fr <= fr + 186 + i < fr + 4096 \/
                    Reusable.YG0f.shadow_addr fr <= fr + 186 + i < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
      exact (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 Ha')). }
    assert (Vy : forall i, 0 <= i < 6 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (phi + i)) = false)
      by (intros i Hi; exact (proj1 (proj1 (Hbpr (phi + i) ltac:(lia))))).
    apply Hcmp.
    apply (proj2 (w4m_bcmp_cmp W3 mem3 (fr + 186) phi (firstn 6 ls) (firstn 6 rs) 6
                    ltac:(rewrite !length_firstn; lia) ltac:(rewrite length_firstn; lia)
                    (w4_bytes_firstn _ _ _ _ Hls) (w4_bytes_firstn _ _ _ _ Hrs) Vx Vy)).
    exact (w4_memcmp0 6 ls rs Hmc). }
  assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
    Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha Hna. apply Hfr2; [exact Ha | unfold Reusable.YG0d.ESTACK; lia]. }
  destruct (w4m_bcmp_frame_kept cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp4096 ltac:(lia) Hwin)
    as (KS & KF & KSH & KK).
  destruct (w4m_bcmp_block_kept ly3 S3 W3 mem3 md3 mem2 (sp - 8192) sp phi _ HAR Hin ltac:(lia) Hwin) as (KB & KBS).
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, mem2 (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    exact (proj2 (Hpres2 a (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha'))). }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) as HKA.
  assert (KSA : forall x, A <= x < ACtlCut.c_sp cx ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KS; lia).
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9)
    by exact (eq_trans (HP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym Hr9)).
  assert (E18 : getr regs2 18 = getr regs3 18)
    by exact (eq_trans (HP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym H18)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (HP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20) by exact (HP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs2 22 = getr regs3 22) by exact (HP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : getr regs2 24 = getr regs3 24) by exact (HP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : getr regs2 25 = getr regs3 25) by exact (HP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (Hsp2 : Reusable.YG0d.spZ regs2 = sp) by (unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ).
  rewrite HspZ in HwL, HwP, HwP50, Hwkp, HwL2, HwP6.
  apply (H64c cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 HF HG1 Hk);
    [| exact (w4_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2)].
  unfold ACtlCutP.C_B8264c_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
  split; [reflexivity|].
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4m_bcmp_FRAC cx fr fr regs2 regs3 mem3 mem2 E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. rewrite HspZ in Hx. lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [apply (w4m_bcmp_HB mem3 mem2 phi _); [intros i Hi; apply KBS; lia | exact HHB]|].
  split; [exact (w4m_bcmp_LK cx fr jj regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                   ltac:(lia) KSA KF KSH KK HKA Hpr HLK)|].
  split; [exact (w4m_rgv_tr regs2 regs3 20 _ E20 H20)|].
  split; [exact (w4_FM_keep cx jj phi fr regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                   ltac:(lia) ltac:(lia) KSA HFM)|].
  split.
  { exists A, (fr + 176), (fr + 180), (firstn 6 ls2), (firstn 6 rs2).
    split; [exact (w4m_rgv_tr regs2 regs3 9 _ E9 Hr9)|].
    split; [lia|]. split; [rewrite Hsp2; lia|].
    split; [exact (w4m_rgv_tr regs2 regs3 18 _ E18 H18)|].
    split; [exact (w4m_rgv_tr regs2 regs3 24 _ E24 H24)|].
    split; [apply (w4m_bcmp_q64 mem3 mem2 _ _); [intros x Hx; apply KSA; lia | exact Q280]|].
    split; [unfold ACtlCut.rgv; rewrite Hv; exact Hv0|].
    split.
    { apply (w4_rec_inv_keep cx jj phi A (fr + 176) mem3 mem2 HREC).
      - intros x Hx. apply KSA. lia.
      - intros x Hx. apply KB. lia.
      - intros x Hx. apply KF. lia.
      - intros i Hi. apply KBS. lia. }
    split; [apply (w4m_bcmp_q64 mem3 mem2 _ _); [intros x Hx; apply KSA; lia | exact Q96]|].
    split; [lia|].
    split; [apply (w4m_bcmp_bytes mem3 mem2 _ _); [rewrite length_firstn; intros x Hx; apply KF; lia
                                                  | exact (w4_bytes_firstn _ _ _ _ Hls2)]|].
    split; [rewrite length_firstn; lia|].
    split; [apply (w4m_bcmp_bytes mem3 mem2 _ _); [rewrite length_firstn; intros x Hx; apply KB; lia
                                                  | exact (w4_bytes_firstn _ _ _ _ Hrs2)]|].
    split; [rewrite length_firstn; lia|].
    split; [rewrite (B.Prog.Seg.F18.memcmp_firstn 6 ls2 rs2); exact Hmc2|].
    split.
    { apply (w4m_bcmp_addr mem3 mem2 (fr + 180) 6); [| exact HadL2].
      intros i Hi. apply KSH. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
    split.
    { apply (w4m_bcmp_addr mem3 mem2 (phi + 6) 6); [| exact HadP6].
      intros i Hi. replace (phi + 6 + i) with (phi + (6 + i)) by lia. apply KBS. lia. }
    split; [exact HapL26|]. split; [exact HapL27|]. split; [exact HapP12|]. split; [exact HapP13|].
    rewrite Hsp2.
    split; [exact HwL2|]. split; [exact HwP6|]. split; [exact HwP50 | exact Hwkp]. }
  split.
  { apply (w4m_bcmp_FTURN cx jj phi regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFT].
    intros x Hx. apply KB. lia. }
  exact (w4m_bcmp_IFS cx fr (S jj) regs2 regs3 mem3 mem2 KF KSH HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8264c_at j (0x8264c) --S_F19--> B82668_at j.
   0x8264c bnez a0,82fa4 (not taken: a0 = 0 by the body); addi a1,s2,6; li a0,7; bltu a1,a0,82fa0 (TRAP row 41,
   T43); li a2,6; ld a0,96(s1); jal 0x42aac (ra 0x82668).
   SINK BRANCHES (objdump L85216-L85222):
   - 0x8264c `bnez a0,82fa4` (ASan abort sink): not taken, a0 = 0 (C_B8264c_at body `rgv regs 10 0`: the F18 bcmp
     returned 0).
   - 0x82658 `bltu a1,a0,82fa0` (UBSan trap, plan F.4.1 row 41, T43): not taken, Phi + 6 >= 7 and no wrap from
     rec_inv's 0 < phi /\ phi + 50 <= 2^64 (C_B8264c_at body, ACtlCutP rec_inv).
   Both are discharged INSIDE f19_pre_F, whose premises carry those conjuncts. *)
Lemma seg_F19 : forall POST (j : nat),
  ctl_from POST (ix C_B82668_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B8264c_at [Z.of_nat j]).
Proof.
  intros POST j H668 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell): f19_pre_F (0x8264c -> the bcmp trampoline 0x42aac, ra = 0x82668, memory
     unchanged), one lift at RNG_W; then the trampoline by the core's journal rule aj_bcmp_at (H_bcmp,
     B_bcmp_tramp_at), x := L2 = fr + 180 (FLI's spill 96), y := phi + 6, n := 6; v = 0 because the six bytes agree
     (memcmp_model ls2 rs2 6 = Some 0); the successor body keeps its bytes over visible addresses (aj_bcmp_at's
     view post, W4f's frame / block keeps), ctl_rt by w4_ctlrt (B.ProgWorldCtlRt.ctlrt_of_AR). *)
  unfold ACtlCutP.C_B8264c_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM &
    (A' & kp & L2 & ls2 & rs2 & Hr9' & HA' & HspA' & H18 & H24 & Q280 & H10 & HREC & Q96 & HL2 & Hls2 & Hlen2 &
     Hrs2 & Hrlen2 & Hmc & HadL & HadP & HapL6 & HapL7 & HapP12 & HapP13 & HwL & HwP & HwPhi & Hwkp) & HFT & HIFS).
  pose proof HREC as (Hphi0 & Hphi50 & Hflen & Htk & Happ50 & Q312 & Hblk & Hbsl &
    (f16 & v14 & v15 & v16 & v17 & Q248 & Hu16 & Hkp22 & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 & Rv14 & Rv15 & Rv16 & Rv17 &
     Hs14 & Hs15 & Hs16 & Hs17 & Hf16 & Hkeq)).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1) as (_ & _ & Bfr1 & Bfr2 & HfrApp & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _).
  (* the two spill bases agree; L2 = fr + 180 and kp = fr + 176 (FLI's spills 96 / 280) *)
  assert (EA : A' = A).
  { apply w4k_bv_inj; [lia | lia |]. unfold ACtlCut.rgv in Hr9', Hr9. rewrite <- Hr9'. exact Hr9. }
  subst A'.
  pose proof HLK as (_ & _ & _ & (_ & _ & S96 & _ & _ & _ & _ & _ & _ & S280 & _)).
  pose proof (w4m_spill regs3 mem3 96 (fr + 180) A S96 Hr9 ltac:(lia) ltac:(lia)) as Q96'.
  pose proof (w4m_spill regs3 mem3 280 (fr + 176) A S280 Hr9 ltac:(lia) ltac:(lia)) as Q280'.
  assert (EL2 : L2 = fr + 180) by (apply w4k_bv_inj; [lia | lia | exact (w4_q64_det _ _ _ _ Q96 Q96')]).
  assert (Ekp : kp = fr + 176) by (apply w4k_bv_inj; [lia | lia | exact (w4_q64_det _ _ _ _ Q280 Q280')]).
  subst L2 kp.
  (* the turn block phi *)
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (Hp16 & Hp4096 & Hpc & Happp & Hbpr & _).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  pose proof (w4_tg_len (ACtlCut.c_in cx) jj) as Htg.
  assert (Hreclen : length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 34 6) = 6%nat)
    by (unfold ACtlCutP.RFR.bsl; rewrite length_firstn, length_skipn, Htg; reflexivity).
  assert (Lblk : length (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj) = 32%nat).
  { change (length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 18 32) = 32%nat).
    unfold ACtlCutP.RFR.bsl. rewrite length_firstn, length_skipn, Htg. reflexivity. }
  (* 0x8264c -> 0x42aac: the stretch, memory unchanged *)
  apply w4m_enter.
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply (B.Prog.Seg.F19F.f19_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
      (A := A) (L := fr + 180) (R := phi).
    - exact (w4_rgv_reg _ 9 _ eq_refl Hr9).
    - exact (w4_rgv_reg _ 18 _ eq_refl H18).
    - exact (w4_rgv_reg _ 10 _ eq_refl H10).
    - lia.
    - exact Hphi0.
    - exact Hphi50.
    - exact Q96.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
  intros ms' md' -> Hs _.
  apply (w4m_exit W3 0x42aac).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  change 0x42aac with B.Prog.bcmp_wrap_c.BCMP_WRAP. rewrite <- B_bcmp_tramp_at.
  pose proof (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) as HJ'.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  (* the bcmp trampoline, x = fr + 180, y = phi + 6, n = 6 *)
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_bcmp_at segs B LAWS segs_low _ H_bcmp W3 R1 mem3 Reusable.YCfn.LLVMF_STK
      (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 md' k (fr + 180) (phi + 6) 6 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82668) HJ').
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspR1. lia.
    - rewrite Zminus_mod, Hspm, Hsp16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - transitivity (getr regs3 3); [reflexivity | rewrite Hr3; exact Hgp0].
    - exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs).
        apply (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). left. lia.
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs). exact (proj1 (Hbpr a ltac:(lia))).
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - apply (w4k_amem_frame fr); [exact Bfr1 | exact Bfr2 | exact HfrApp | lia | lia].
    - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL in Happp.
      unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - apply (w4m_bcmp_range_addr W3 mem3 (fr + 180) 6); [| exact HadL].
      intros i Hi. refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4m_bcmp_hull_frame cx ly3 S3 W3 mem3 md3 k fr); [exact HJ | exact HG1 | lia | lia | lia].
    - apply (w4m_bcmp_range_addr W3 mem3 (phi + 6) 6); [| exact HadP].
      intros i Hi. replace (phi + 6 + i) with (phi + (6 + i)) by lia.
      apply (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (6 + i) HAR Hin). lia.
    - intros _. apply (w4_block_hull_sub ly3 S3 W3 mem3 md3 phi _ (phi + 6) 6 HAR Hin); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr2 & Hpres2).
  (* v = 0: the six bytes agree *)
  assert (Hv0 : v = Reusable.YG0d.w64 0).
  { assert (Vx : forall i, 0 <= i < 6 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (fr + 180 + i)) = false).
    { intros i Hi.
      assert (Ha' : fr <= fr + 180 + i < fr + 4096 \/
                    Reusable.YG0f.shadow_addr fr <= fr + 180 + i < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
      exact (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 Ha')). }
    assert (Vy : forall i, 0 <= i < 6 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (phi + 6 + i)) = false)
      by (intros i Hi; exact (proj1 (proj1 (Hbpr (phi + 6 + i) ltac:(lia))))).
    apply Hcmp.
    apply (proj2 (w4m_bcmp_cmp W3 mem3 (fr + 180) (phi + 6) (firstn 6 ls2) (firstn 6 rs2) 6
                    ltac:(rewrite !length_firstn; lia) ltac:(rewrite length_firstn; lia)
                    (w4_bytes_firstn _ _ _ _ Hls2) (w4_bytes_firstn _ _ _ _ Hrs2) Vx Vy)).
    exact (w4_memcmp0 6 ls2 rs2 Hmc). }
  (* the raw bytes the successor body reads, over their visible regions *)
  assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
    Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha Hna. apply Hfr2; [exact Ha | unfold Reusable.YG0d.ESTACK; lia]. }
  destruct (w4m_bcmp_frame_kept cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp4096 ltac:(lia) Hwin)
    as (KS & KF & KSH & KK).
  destruct (w4m_bcmp_block_kept ly3 S3 W3 mem3 md3 mem2 (sp - 8192) sp phi _ HAR Hin ltac:(lia) Hwin) as (KB & KBS).
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, mem2 (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    exact (proj2 (Hpres2 a (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha'))). }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) as HKA.
  assert (KSA : forall x, A <= x < ACtlCut.c_sp cx ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KS; lia).
  (* the callee-saved registers *)
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9)
    by exact (eq_trans (HP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym Hr9)).
  assert (E18 : getr regs2 18 = getr regs3 18)
    by exact (eq_trans (HP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym H18)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (HP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20) by exact (HP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs2 22 = getr regs3 22) by exact (HP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : getr regs2 24 = getr regs3 24) by exact (HP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : getr regs2 25 = getr regs3 25) by exact (HP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  pose proof HFM as (_ & _ & _ & H25 & _).
  apply (H668 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 HF HG1 Hk);
    [| exact (w4_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2)].
  unfold ACtlCutP.C_B82668_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
  split; [reflexivity|].
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4m_bcmp_FRAC cx fr fr regs2 regs3 mem3 mem2 E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. rewrite HspZ in Hx. lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [apply (w4m_bcmp_HB mem3 mem2 phi _); [intros i Hi; apply KBS; lia | exact HHB]|].
  split; [exact (w4m_bcmp_LK cx fr jj regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                   ltac:(lia) KSA KF KSH KK HKA Hpr HLK)|].
  split; [exact (w4m_rgv_tr regs2 regs3 20 _ E20 H20)|].
  split; [exact (w4_FM_keep cx jj phi fr regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                   ltac:(lia) ltac:(lia) KSA HFM)|].
  split; [exact (w4m_rgv_tr regs2 regs3 18 _ E18 H18)|].
  split; [exact (w4m_rgv_tr regs2 regs3 24 _ E24 H24)|].
  split; [unfold ACtlCut.rgv; rewrite Hv; exact Hv0|].
  split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
  split; [apply (w4m_bcmp_bytes mem3 mem2 (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; lia | exact Hblk]|].
  split; [apply (w4m_bcmp_bytes mem3 mem2 (phi + 34) _); [intros x Hx; apply KB; rewrite Hreclen in Hx; lia
                                                           | exact Hbsl]|].
  split; [exact (w4m_rgv_tr regs2 regs3 25 _ E25 H25)|].
  split; [left; unfold Reusable.YG0d.spZ in *; rewrite E2; lia|].
  split.
  { apply (w4m_bcmp_FTURN cx jj phi regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFT].
    intros x Hx. apply KB. lia. }
  split; [exact (w4m_bcmp_IFS cx fr (S jj) regs2 regs3 mem3 mem2 KF KSH HIFS)|].
  exists v14, v15, v16, v17, f16.
  split.
  { unfold ACtlCutP.u16 in *. replace (fr + 196) with (fr + 176 + 20) by lia.
    apply (w4m_bcmp_bytes mem3 mem2 _ _); [| exact Hu16].
    rewrite lib.Lib.Mem.length_le2. intros x Hx. apply KF. lia. }
  split; [apply (w4m_bcmp_b8 mem3 mem2 _ _); [intros x Hx; apply KB; lia | exact Hb14]|].
  split; [apply (w4m_bcmp_b8 mem3 mem2 _ _); [intros x Hx; apply KB; lia | exact Hb15]|].
  split; [apply (w4m_bcmp_b8 mem3 mem2 _ _); [intros x Hx; apply KB; lia | exact Hb16]|].
  split; [apply (w4m_bcmp_b8 mem3 mem2 _ _); [intros x Hx; apply KB; lia | exact Hb17]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [apply (w4_sh_b8_keep mem3 mem2 (phi + 14)); [lia | apply (KBS 14); lia | exact Hs14]|].
  split; [apply (w4_sh_b8_keep mem3 mem2 (phi + 15)); [lia | apply (KBS 15); lia | exact Hs15]|].
  split; [apply (w4_sh_b8_keep mem3 mem2 (phi + 16)); [lia | apply (KBS 16); lia | exact Hs16]|].
  split; [apply (w4_sh_b8_keep mem3 mem2 (phi + 17)); [lia | apply (KBS 17); lia | exact Hs17]|].
  split; [exact Hf16 | exact Hkeq].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82668_at j (0x82668) --S_F20--> B82728_at j.
   Four one-byte instrumented checks on Phi + 14 .. Phi + 17 (zero shadow bytes carried by the body), the
   compares at 0x826c0 (u16 at fr + 196 against (v15 << 8) | v14) and 0x8271c (v16 / v17 against k = 1), both
   not taken by the body's field equations; `mv a0,s2` 0x82720; `jal reac_ctrl_checksum_verify` 0x82724
   (entry 0x83b94, ra 0x82728).
   SINK BRANCHES (objdump L85223-L85268):
   - 0x82668 `bnez a0,82fa4`: not taken, a0 = 0 (C_B82668_at body `rgv regs 10 0`).
   - 0x8266c `beqz s2,82fa0` (row 42) and 0x82674 / 0x8267c / 0x826c8 / 0x826f4 `bltu a0,s2,82fa0` (rows 43-46,
     a0 = -15 / -16 / -17 / -18): not taken from rgv 18 phi, 0 < phi, phi + 50 <= 2^64 (C_B82668_at body).
   - 0x826c0 `bne a0,a2,82fa4`: not taken, u16 (fr + 196) field16 /\ field16 = v14 + 256 * v15 (body).
   - 0x8271c `bne a0,a1,82fa4`: not taken, the body's (v16 =? 0 && v17 =? 0) = (t_k =? 1) equation.
   - the ASan report paths of the four one-byte checks (0x82698 -> 0x82d8c -> 0x83098, 0x826b0 -> 0x82d98 ->
     0x8309c, 0x826dc -> 0x82da4 -> 0x830a4, 0x82708 -> 0x82e1c -> 0x830c8, each `jal __asan_report_load1`):
     the `bnez` into the slow block is not taken, the shadow bytes of Phi + 14 .. Phi + 17 are 0 (body).
   All are discharged INSIDE seg_F20_pre_F, whose premises carry them. *)
Lemma seg_F20 : forall POST (j : nat),
  ctl_from POST (ix C_B82728_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82668_at [Z.of_nat j]).
Proof.
  intros POST j H728 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell): seg_F20_pre_F (0x82668 -> 0x83b94, ra = 0x82728, a0 = phi), whose continuation
     premise is the checksum callee's run HCKV_F (w4_evtF_join), ONE lift at RNG_W (w_H W3); the callee writes only
     [sp - 16, sp) (raw munch), so the journal moves by w4k_after_run, ctl_rt by w4k_ctlrt_run, and every body
     conjunct keeps its bytes; a0 = (if blocksum blk =? 0 then 0 else -1) is C_B82728_at's rgv 10. *)
  unfold ACtlCutP.C_B82668_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM & H18 & H24 & H10 & Hphi0 & Hphi50 &
    Hflen & Htk & Hblk & Hbsl & H25 & Hwin & HFT & HIFS &
    (v14 & v15 & v16 & v17 & f16 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & Rv14 & Rv15 & Rv16 & Rv17 &
     Hs14 & Hs15 & Hs16 & Hs17 & Hf16 & Hkeq)).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof HRT as (Hcells & _ & _ & _).
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & _ & Hbpr & _).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  assert (Hsp2 : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) = sp).
  { rewrite (w4_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  pose proof (w4_tg_len (ACtlCut.c_in cx) jj) as Htg.
  assert (Hreclen : length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 34 6) = 6%nat)
    by (unfold ACtlCutP.RFR.bsl; rewrite length_firstn, length_skipn, Htg; reflexivity).
  assert (Lblk : length (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj) = 32%nat).
  { change (length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 18 32) = 32%nat).
    unfold ACtlCutP.RFR.bsl. rewrite length_firstn, length_skipn, Htg. reflexivity. }
  (* the F20 entry group's spill [A + 280] = fr + 176 (FLI) *)
  pose proof HLK as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & S280 & _)).
  pose proof (w4m_spill regs3 mem3 280 (fr + 176) A S280 Hr9 ltac:(lia) ltac:(lia)) as Q280.
  (* 0x82668 -> 0x83b94 -> 0x82728: the inline checks, the call and the checksum callee, one lift *)
  apply w4m_enter.
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    apply w4_evtF_join.
    eapply (B.Prog.Seg.F20F.seg_F20_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
      (A := A) (fr := fr) (phi := phi) (k := ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj)
      (v14 := v14) (v15 := v15) (v16 := v16) (v17 := v17) (field16 := f16).
    - exact (w4_rgv_reg _ 10 _ eq_refl H10).
    - exact (w4_rgv_reg _ 9 _ eq_refl Hr9).
    - exact (w4_rgv_reg _ 18 _ eq_refl H18).
    - exact (w4_rgv_reg _ 24 _ eq_refl H24).
    - exact (w4_rgv_reg _ 26 _ eq_refl Hr26).
    - exact Hphi0.
    - exact Hphi50.
    - exact Htk.
    - exact Rv14.
    - exact Rv15.
    - exact Rv16.
    - exact Rv17.
    - lia.
    - exact Q280.
    - exact Hu16.
    - exact Hb14.
    - exact Hb15.
    - exact Hb16.
    - exact Hb17.
    - exact Hs14.
    - exact Hs15.
    - exact Hs16.
    - exact Hs17.
    - exact Hf16.
    - exact Hkeq.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia.
    - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
    - intros a1' a2' a3'.
      eapply (HCKV_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (m := mem3) (p := phi)
        (lo := bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) - 16)
        (bs := ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj);
        unfold B.Prog.reac_ctrl_checksum_verify_c.REAC_CTRL_CHECKSUM_VERIFY_FRAME; rewrite ?Hsp2.
      + exact Hphi0.
      + exact Hphi50.
      + reflexivity.
      + exact Lblk.
      + exact Hblk.
      + apply w4k_stk_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hpres x ltac:(lia))).
      + lia.
      + rewrite HspZ in Hwin. lia.
      + exact Hcells.
      + apply (w4_addr_sub mem3 phi _ (phi + 18) 32 (proj2 HHB)); lia.
      + intros x Hx. cbn [lib.Lib.Frame.outside]. split; [|exact I].
        unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
        lia.
      + apply B.ProgBridge.rng_of_visible.
        apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
      + apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.GOT_CELL_K.
        split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
      + apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.CELL_K.
        split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
      + apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hbpr a ltac:(lia)))).
      + apply B.ProgBridge.rng_of_visible.
        split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        split; [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        intros a Ha.
        destruct (w4_sh_between (phi + 18) (phi + 49) a ltac:(lia)
                    ltac:(unfold B.AsanRT.shadow_addr; lia)) as (z & Hz & <-).
        replace z with (phi + (z - phi)) by lia.
        apply (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). lia. }
  intros ms' md' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & _ & Hstk') Hsbm Hhid.
  unfold B.Prog.reac_ctrl_checksum_verify_c.REAC_CTRL_CHECKSUM_VERIFY_FRAME in MU, Hstk'.
  rewrite Hsp2 in MU, Hstk'.
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x82728) = Z_to_bv 64 0x82728) by (apply bv_eq; reflexivity).
  rewrite Eret.
  apply (w4m_exit W3 0x82728).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  assert (Hout : forall x, 0 <= x < sp - 16 \/ sp <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HW : forall a, ~ lib.Lib.Frame.outside [(sp - 16, sp)] a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. apply w4k_not_outside1 in Ha.
    assert (Hni : ~ Reusable.YG0d.in_img segs a) by (apply w4k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
    split; [exact Hni|].
    destruct Hstk' as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as (_ & b & Hb).
    exists b. exact (w4k_mrd_raw m' a b ltac:(lia) Hni Hb). }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4k_after_run cx ly3 S3 W3 mem3 md3 k m' md' [(sp - 16, sp)] HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    apply w4k_not_outside1 in Ha. apply w4k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia. }
  pose proof (w4k_ctlrt_run ly3 S3 mem3 m' _ HRT MU WM HW) as HRT'.
  assert (KS : MKEPT mem3 m' sp (ACtlCut.c_sp cx))
    by (apply (w4_munch_kept _ mem3 m' sp _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSA : MKEPT mem3 m' A (ACtlCut.c_sp cx)) by (intros x Hx; apply KS; lia).
  assert (KF : MKEPT mem3 m' fr (fr + 4096))
    by (apply (w4_munch_kept _ mem3 m' fr _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSH : MKEPT mem3 m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512)).
  { apply (w4_munch_kept _ mem3 m' _ _ MU);
      [unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia
      | unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
    intros x Hx. apply Hout.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. Z.div_mod_to_equations. lia. }
  assert (KK : MKEPT mem3 m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112)).
  { unfold ACtlCutP.KNA.KIND_NAME.
    apply (w4_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]. }
  assert (KB : MKEPT mem3 m' phi (phi + Reusable.YG00.req_size (ACtlCutP.flen cx jj)))
    by (apply (w4_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx jj) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. apply (w4k_mrd_munch _ mem3 m' _ MU).
    - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - apply Hout. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    destruct (proj2 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha')) as (b & Hb).
    exists b. rewrite (MU (Z_to_bv 64 a)); [exact Hb|].
    change (Z_to_bv 64 a) with (lib.Lib.Mem.wa a). rewrite lib.Lib.Mem.wa_unsigned by lia. apply Hout. lia. }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ')) as HKA.
  assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
  assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
  assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
  assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
  assert (E9 : getr R1 9 = getr regs3 9) by reflexivity.
  assert (E18 : getr R1 18 = getr regs3 18) by reflexivity.
  assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
  assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
  assert (E22 : getr R1 22 = getr regs3 22) by reflexivity.
  assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
  assert (E25 : getr R1 25 = getr regs3 25) by reflexivity.
  assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
  assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
  apply (H728 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  unfold ACtlCutP.C_B82728_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
  split; [reflexivity|].
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4m_bcmp_FRAC cx fr fr R1 regs3 mem3 m' E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. rewrite HspZ in Hx. lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  split; [exact (w4m_bcmp_LK cx fr jj R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                   ltac:(lia) KSA KF KSH KK HKA Hpr HLK)|].
  split; [exact (w4m_rgv_tr R1 regs3 20 _ E20 H20)|].
  split; [exact (w4_FM_keep cx jj phi fr R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                   ltac:(lia) ltac:(lia) KSA HFM)|].
  split; [unfold ACtlCut.rgv; reflexivity|].
  split; [exact (w4m_rgv_tr R1 regs3 18 _ E18 H18)|].
  split; [exact (w4m_rgv_tr R1 regs3 24 _ E24 H24)|].
  split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
  split; [apply (w4m_bcmp_bytes mem3 m' (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; lia | exact Hblk]|].
  split; [apply (w4m_bcmp_bytes mem3 m' (phi + 34) _); [intros x Hx; apply KB; rewrite Hreclen in Hx; lia
                                                         | exact Hbsl]|].
  split; [exact (w4m_rgv_tr R1 regs3 25 _ E25 H25)|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
  split.
  { apply (w4m_bcmp_FTURN cx jj phi R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFT].
    intros x Hx. apply KB. lia. }
  exact (w4m_bcmp_IFS cx fr (S jj) R1 regs3 mem3 m' KF KSH HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B827f8_at j (0x827f8) --S_F22--> B8283c_at j.
   The 6-turn record-sum loop 0x827f8-0x8281c (latch `bne a0,a7`), then 0x82830-0x82838
   s7 := (a1 & 127 = 0 ? 0 : -1) = t_want_v (Phi[18] / Phi[19] = 4 / 3).  No memory change (UB Seg/F22.v:5-17).
   SINK BRANCHES (objdump L85323-L85335):
   - 0x827f8 `bltu a3,a0,82fa0` (row 52, every turn i = 0 .. 5, a3 = 2^64 - (Phi + 35)): not taken because the
     cut pins a3 = 2^64 - (phi + 35), a0 = 0, a7 = 6 (C_B827f8_at body: rgv 13, rgv 10, rgv 17) and
     0 < phi /\ phi + 50 <= 2^64, so a3 >= 15 > 5 >= i, and the loop body never writes a3.
   - the report path of the per-turn byte check (`bnez` to 0x82824, then 0x82828 `bge a6,a5,83050`): the `bnez`
     is not taken, the body's zero shadow of [phi + 34, phi + 40).
   Discharged INSIDE seg_F22_F (its loop invariant is f22_loop's, UB Seg/F22.v:218, induction :234). *)
Lemma seg_F22 : forall POST (j : nat),
  ctl_from POST (ix C_B8283c_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B827f8_at [Z.of_nat j]).
Proof.
  intros POST j H83c.
  unfold ctl_from, ACtlCut.ctl_from.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HG1 Hk HBODY HRT.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B827f8_at ACtlCut.cut_pc] in HBODY |- *.
  destruct HBODY as (Hidx & phi & Hperm & HFRAC & Hcn & Hj255 & HHB & HLK & Hr20 & HFM &
                     Hr10 & Hr11 & Hr12 & Hr13 & Hr17 & Hr18 & Hr24 & Hphi0 & Hphi50 & Hflen & Htk &
                     Hcp18 & Hcp19 & Hbblk & Hbbsl & Hshz & Hr25 & Happ & Hwin & HFTURN & HIFS).
  (* the journal's AR at the cut, and the turn block phi live in it (V3 / V4 sources) *)
  assert (HAR : Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3) by (destruct HJ as [HAR _]; exact HAR).
  assert (Hmem : In (phi, ACtlCutP.flen cx (ACtlCutP.ixn 0 idx)) (Reusable.YG0d.ablocks B ly3 S3)).
  { eapply Permutation_in; [exact (Permutation_sym Hperm)|]. apply in_or_app. right. left. reflexivity. }
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx (ACtlCutP.ixn 0 idx))
                 = ACtlCutP.flen cx (ACtlCutP.ixn 0 idx)).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx (ACtlCutP.ixn 0 idx)) 0); lia. }
  (* FRAC pins s10 = ASAN_K, which the run's start states *)
  pose proof HFRAC as HFRAC0.
  destruct HFRAC0 as (A & sp & _ & _ & _ & _ & _ & _ & _ & _ & Hr26 & _).
  (* the six record bytes the loop sums *)
  assert (Hreclen : length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) (ACtlCutP.ixn 0 idx)) 34 6)
                    = 6%nat).
  { unfold ACtlCutP.RFR.bsl, ACtlCutP.SM.t_g, ACtlCutP.SM.fr50.
    rewrite length_firstn, length_skipn, length_firstn, length_app, repeat_length.
    change (Z.to_nat 6) with 6%nat. change (Z.to_nat 34) with 34%nat. lia. }
  (* the run's canonical start map: the cut's registers, with the six the run pins written as their values *)
  pose (CANON := lib.Lib.Frame.mkR
    (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
    (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
    (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 (2 ^ 64 - (phi + 35)))
    (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16)
    (Z_to_bv 64 6)
    (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
    (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
    (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
    (Z_to_bv 64 B.ACtlK.ASAN_K)
    (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
    (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  assert (Hxe : Lib.Regs6ss.xregs_eqv CANON regs3).
  { assert (HC : CANON = Lib.Regs6ss.mkR_of regs3).
    { unfold CANON, Lib.Regs6ss.mkR_of. unfold ACtlCut.rgv in Hr10, Hr11, Hr12, Hr13, Hr17, Hr26.
      f_equal; first [reflexivity | symmetry; assumption]. }
    rewrite HC. exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3)). }
  eapply (w4_seat_F W3 regs3 CANON 0x827f8 mem3 md3 _ (POST cx) Hxe).
  - (* the record-sum loop, B.Prog.Seg.F22F.seg_F22_F *)
    unfold CANON.
    apply (B.Prog.Seg.F22F.seg_F22_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
             (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
             (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
             (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
             (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
             (lib.Reusable.YK11.getr regs3 16)
             (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19)
             (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
             (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
             (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
             (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28)
             (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
             (lib.Reusable.YK11.getr regs3 31)
             lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 phi
             (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) (ACtlCutP.ixn 0 idx)) 34 6)).
    + exact Hphi0.
    + exact Hphi50.
    + intros t Ht. apply w4_bytes_at_byte; [exact Hbbsl | rewrite Hreclen; exact Ht].
    + intros t Ht. apply Hshz. lia.
    + intros t Ht.
      apply (w4_rng_block W3 mem3 ly3 S3 md3 phi (ACtlCutP.flen cx (ACtlCutP.ixn 0 idx))); try assumption;
        rewrite ?Hreq; lia.
    + intros t Ht.
      apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi (ACtlCutP.flen cx (ACtlCutP.ixn 0 idx))); try assumption;
        rewrite ?Hreq; lia.
  - (* continuation at 0x8283c: memory unchanged, so the journal moves with an empty write set *)
    intros ms' md' (a0' & a1' & a4' & a5' & ->) Hsbm Hhid.
    rewrite <- (w4_cfg_MS 0x8283c).
    apply (w4_after_run POST (ix C_B8283c_at [Z.of_nat j]) cx idx fr k ly3 S3 W3 mem3 md3 _ mem3 md'
             (fun _ => False) H83c HB HJ Hfr HG1 Hk).
    + intros x _. reflexivity.
    + apply lib.Reusable.YK1b.mem_grows_refl.
    + intros x _. reflexivity.
    + exact Hsbm.
    + intros a [].
    + cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B8283c_at].
      split; [exact Hidx|].
      exists phi.
      split; [exact Hperm|].
      split.
      { unfold ACtlCut.rgv in Hr26.
        apply (w4_FRAC_cong cx fr fr regs3); try reflexivity; [ rewrite Hr26; reflexivity | exact HFRAC ]. }
      split; [exact Hcn|]. split; [exact Hj255|]. split; [exact HHB|]. split; [exact HLK|].
      split; [exact Hr20|]. split; [exact HFM|]. split; [exact Hr18|].
      split.
      { unfold ACtlCut.rgv.
        rewrite <- (w4_f22_want (ACtlCut.c_in cx) (ACtlCutP.ixn 0 idx) Hcp18 Hcp19). reflexivity. }
      split; [exact Hr24|]. split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|].
      split; [exact Htk|]. split; [exact Hbblk|]. split; [exact Hbbsl|]. split; [exact Hr25|].
      split; [exact Happ|]. split; [exact Hwin|]. split; [exact HFTURN | exact HIFS].
    + exact HRT.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8283c_at j (0x8283c) --S_F22t--> B82844_at j.
   0x8283c `mv a0,s2`; 0x82840 `jal reac_ctrl_headamp_record_verify` (entry 0x858e4, ra 0x82844).  The callee reads
   Phi[18], Phi[19] and [Phi + 34, Phi + 40), writes only [sp - 16, sp), returns a0 = 0 when hv holds, else -1,
   which is t_want_v (UB Seg/F22.v:18-22).  SINK BRANCHES: none on 0x8283c-0x82840. *)
Lemma seg_F22t : forall POST (j : nat),
  ctl_from POST (ix C_B82844_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B8283c_at [Z.of_nat j]).
Proof.
  intros POST j H844 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell): seg_F22t_pre_F (0x8283c -> 0x858e4, ra = 0x82844, a0 = phi) joined by
     ExecF.evtF_cut to the head-amp callee's footprint contract HHRV_F, ONE lift at RNG_W (w_H W3); the callee writes
     only [sp - 16, sp) (raw munch), so the journal moves by w4k_after_run, ctl_rt by w4k_ctlrt_run, and every
     body conjunct keeps its bytes (they all lie outside [sp - 16, sp)); a0 = (if hv b0 b1 rec then 0 else -1) is
     t_want_v by definition (b0 / b1 = Phi[18] / Phi[19], rec = Phi[34 .. 40)). *)
  unfold ACtlCutP.C_B8283c_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM & H18 & H23 & H24 & Hphi0 & Hphi50 &
    Hflen & Htk & Hblk & Hbsl & H25 & Happ & Hwin & HFT & HIFS).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof HRT as (Hcells & _ & _ & _).
  (* the turn block phi: live, so its bytes and their shadow are visible and below the allocation ceiling *)
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & _ & Hbpr & _).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  (* sp as the run's word *)
  assert (Hsp2 : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) = sp).
  { rewrite (w4_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  (* the record bytes the callee reads *)
  pose proof (w4_tg_len (ACtlCut.c_in cx) jj) as Htg.
  assert (Hreclen : length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 34 6) = 6%nat)
    by (unfold ACtlCutP.RFR.bsl; rewrite length_firstn, length_skipn, Htg; reflexivity).
  assert (Lblk : length (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj) = 32%nat).
  { change (length (ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 18 32) = 32%nat).
    unfold ACtlCutP.RFR.bsl. rewrite length_firstn, length_skipn, Htg. reflexivity. }
  pose proof (w4_blk01 mem3 (phi + 18) _ Htg Hblk) as Hb01.
  (* 0x8283c -> 0x858e4 -> 0x82844: the call stretch and the callee, one lift *)
  apply w4m_enter.
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply (B.Prog.Seg.F22F.seg_F22t_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (phi := phi).
      exact (w4_rgv_reg _ 18 _ eq_refl H18). }
    intros ms1 ->.
    eapply (HHRV_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (m := mem3) (p := phi)
      (lo := bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) - 16)
      (b0 := ACtlCutP.RPA.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 18)
      (b1 := ACtlCutP.RPA.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 19)
      (rec := ACtlCutP.RFR.bsl (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 34 6);
      unfold B.Prog.reac_ctrl_headamp_record_verify_c.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Hsp2.
    - reflexivity.
    - exact Hphi0.
    - lia.
    - exact Hb01.
    - exact Hreclen.
    - exact Hbsl.
    - apply w4k_stk_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hpres x ltac:(lia))).
    - lia.
    - rewrite HspZ in Hwin. lia.
    - rewrite HspZ in Hwin. lia.
    - exact Hcells.
    - apply (w4_addr_sub mem3 phi _ (phi + 18) 2 (proj2 HHB)); lia.
    - apply (w4_addr_sub mem3 phi _ (phi + 34) 6 (proj2 HHB)); lia.
    - intros x Hx. cbn [lib.Lib.Frame.outside]. split; [|exact I].
      unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
        B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
      lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.GOT_CELL_K.
      split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
    - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.CELL_K.
      split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
    - apply B.ProgBridge.rng_of_visible.
      split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hbpr a ltac:(lia)))).
    - apply B.ProgBridge.rng_of_visible.
      split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hbpr a ltac:(lia)))).
    - apply B.ProgBridge.rng_of_visible.
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      intros a Ha. destruct (w4_sh_between (phi + 18) (phi + 19) a ltac:(lia) ltac:(lia)) as (z & Hz & <-).
      replace z with (phi + (z - phi)) by lia.
      apply (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). lia.
    - apply B.ProgBridge.rng_of_visible.
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      intros a Ha. destruct (w4_sh_between (phi + 34) (phi + 39) a ltac:(lia) ltac:(lia)) as (z & Hz & <-).
      replace z with (phi + (z - phi)) by lia.
      apply (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). lia. }
  intros ms' md' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & _ & Hstk') Hsbm Hhid.
  unfold B.Prog.reac_ctrl_headamp_record_verify_c.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, Hstk'.
  rewrite Hsp2 in MU, Hstk'.
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x82844) = Z_to_bv 64 0x82844) by (apply bv_eq; reflexivity).
  rewrite Eret.
  apply (w4m_exit W3 0x82844).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  (* the callee's write set [sp - 16, sp): outside the image, present afterwards, inside the journal's window *)
  assert (Hout : forall x, 0 <= x < sp - 16 \/ sp <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HW : forall a, ~ lib.Lib.Frame.outside [(sp - 16, sp)] a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. apply w4k_not_outside1 in Ha.
    assert (Hni : ~ Reusable.YG0d.in_img segs a) by (apply w4k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
    split; [exact Hni|].
    destruct Hstk' as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as (_ & b & Hb).
    exists b. exact (w4k_mrd_raw m' a b ltac:(lia) Hni Hb). }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4k_after_run cx ly3 S3 W3 mem3 md3 k m' md' [(sp - 16, sp)] HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    apply w4k_not_outside1 in Ha. apply w4k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia. }
  pose proof (w4k_ctlrt_run ly3 S3 mem3 m' _ HRT MU WM HW) as HRT'.
  (* the bytes the successor body reads, all outside [sp - 16, sp) *)
  assert (KS : MKEPT mem3 m' sp (ACtlCut.c_sp cx))
    by (apply (w4_munch_kept _ mem3 m' sp _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSA : MKEPT mem3 m' A (ACtlCut.c_sp cx)) by (intros x Hx; apply KS; lia).
  assert (KF : MKEPT mem3 m' fr (fr + 4096))
    by (apply (w4_munch_kept _ mem3 m' fr _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSH : MKEPT mem3 m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512)).
  { apply (w4_munch_kept _ mem3 m' _ _ MU);
      [unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia
      | unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
    intros x Hx. apply Hout.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. Z.div_mod_to_equations. lia. }
  assert (KK : MKEPT mem3 m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112)).
  { unfold ACtlCutP.KNA.KIND_NAME.
    apply (w4_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]. }
  assert (KB : MKEPT mem3 m' phi (phi + Reusable.YG00.req_size (ACtlCutP.flen cx jj)))
    by (apply (w4_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx jj) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. apply (w4k_mrd_munch _ mem3 m' _ MU).
    - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - apply Hout. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    destruct (proj2 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha')) as (b & Hb).
    exists b. rewrite (MU (Z_to_bv 64 a)); [exact Hb|].
    change (Z_to_bv 64 a) with (lib.Lib.Mem.wa a). rewrite lib.Lib.Mem.wa_unsigned by lia. apply Hout. lia. }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ')) as HKA.
  (* the callee-saved registers, and s2 = phi *)
  assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
  assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
  assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
  assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
  assert (E9 : getr R1 9 = getr regs3 9) by reflexivity.
  assert (E18 : getr R1 18 = getr regs3 18) by (transitivity (Z_to_bv 64 phi); [reflexivity | symmetry; exact H18]).
  assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
  assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
  assert (E22 : getr R1 22 = getr regs3 22) by reflexivity.
  assert (E23 : getr R1 23 = getr regs3 23) by reflexivity.
  assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
  assert (E25 : getr R1 25 = getr regs3 25) by reflexivity.
  assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
  assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
  apply (H844 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  unfold ACtlCutP.C_B82844_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
  split; [reflexivity|].
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4m_bcmp_FRAC cx fr fr R1 regs3 mem3 m' E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. rewrite HspZ in Hx. lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  split; [exact (w4m_bcmp_LK cx fr jj R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                   ltac:(lia) KSA KF KSH KK HKA Hpr HLK)|].
  split; [exact (w4m_rgv_tr R1 regs3 20 _ E20 H20)|].
  split; [exact (w4_FM_keep cx jj phi fr R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                   ltac:(lia) ltac:(lia) KSA HFM)|].
  split; [unfold ACtlCut.rgv; reflexivity|].
  split; [exact (w4m_rgv_tr R1 regs3 18 _ E18 H18)|].
  split; [exact (w4m_rgv_tr R1 regs3 23 _ E23 H23)|].
  split; [exact (w4m_rgv_tr R1 regs3 24 _ E24 H24)|].
  split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
  split; [apply (w4m_bcmp_bytes mem3 m' (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; lia | exact Hblk]|].
  split; [apply (w4m_bcmp_bytes mem3 m' (phi + 34) _); [intros x Hx; apply KB; rewrite Hreclen in Hx; lia
                                                         | exact Hbsl]|].
  split; [exact (w4m_rgv_tr R1 regs3 25 _ E25 H25)|].
  split; [exact Happ|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
  split.
  { apply (w4m_bcmp_FTURN cx jj phi R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFT].
    intros x Hx. apply KB. lia. }
  exact (w4m_bcmp_IFS cx fr (S jj) R1 regs3 mem3 m' KF KSH HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82728_at j (0x82728) --S_F21--> B827f8_at j (exit 1) | B82844_at j (exit 2).
   0x82728-0x8272c the checksum result against s9 - 1 (bne to 0x82fa4 not taken: sum_ok j <-> blocksum = 0);
   0x82730-0x82784 at k = 6 the record bytes Phi[18] / Phi[19] are 4 / 3; 0x82788-0x827f4 the bytes are read
   again, s7 := -1, and either the block falls through to the sum-loop head 0x827f8 (exit 1: a0 = 0, a1 = 0,
   a2 = Phi + 34, a3 = ~(Phi + 34), a7 = 6) or branches to 0x8283c `mv a0,s2` / 0x82840
   `jal reac_ctrl_headamp_record_verify` (entry 0x858e4) and lands at 0x82844 (exit 2) with a0 = s7 = -1 =
   t_want_v (UB Seg/F21.v:5-14).
   SINK BRANCHES (objdump L85271-L85320):
   - 0x8272c `bne a0,a1,82fa4`: not taken, the checksum result equals s9 - 1 (sum_ok j <-> blocksum blk = 0; the
     body's rgv 10 (if blocksum .. =? 0 then 0 else -1) and rgv 25 (b2z (t_sum_ok j))).
   - 0x8275c / 0x82784 `bne a0,a1,82fa4`: not taken, at k = 6 the record bytes Phi[18] / Phi[19] are 4 / 3
     (bytes (phi + 18) blk in the body; the model's record facts, Seg/F21.v:9-10).
   - 0x8273c / 0x82764 / 0x8278c / 0x827b8 / 0x827e0 `bltu a0,s2,82fa0` (rows 47-51, a0 = -19 / -20 / -19 / -20 /
     -35): not taken from rgv 18 phi, 0 < phi, phi + 50 <= 2^64 (C_B82728_at body).
   - the report paths of its one-byte checks (0x82750 -> 0x82dec -> 0x830b8, 0x82778 -> 0x82df8 -> 0x830bc,
     0x827a0 -> 0x82db0 -> 0x830a8, 0x827cc -> 0x82e04 -> 0x830c0): not taken, the bytes lie in the live block
     phi with len >= 50 (HB), so their shadow granules read 0 (Seg/F21.v:15-17).
   All are discharged INSIDE seg_F21_F. *)
Lemma seg_F21 : forall POST (j : nat),
  ctl_from POST (ix C_B827f8_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82844_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82728_at [Z.of_nat j]).
Proof.
  intros POST j H7f8 H844 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell): ONE lift of B.Prog.Seg.F21F.seg_F21_F at RNG_W (w_H W3), seated at its canonical
     start map (s2 / s8 / s9 / s10 written as their values; w4_seat_F), with the post Q := "the continuation holds
     at that state".  The run writes no memory, so the journal moves by w4m_aj_nowrite and ctl_rt is HRT.
     EXIT 1 (Phi[18] / Phi[19] = 4 / 3, pc 0x827f8): C_B827f8_at from the run's registers and the carried body.
     EXIT 2 (otherwise, pc 0x8283c, s7 = -1 = t_want_v by F21.want_m1): C_B8283c_at, then seg_F22t (proved above)
     carries the walk through the head-amp callee to B82844_at.  The model facts are B.Prog.Seg.F21's (in this
     file's closure through F21F): ckv_eq, sumok_range, k6_rec, want_m1, blk_b8, sh0. *)
  unfold ACtlCutP.C_B82728_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM & H10 & H18 & H24 & Hphi0 & Hphi50 &
    Hflen & Htk & Hblk & Hbsl & H25 & Hwin & HFT & HIFS).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1) as (_ & _ & Bfr1 & Bfr2 & HfrApp & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _).
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (Hp16 & Hp4096 & Hpc & _).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  assert (Hphi8 : phi mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the frame lies in application memory (AR's frame law through w4k_cut6) *)
  assert (Happ : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> ACtlCutP.ART.app_mem a).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    unfold ACtlCutP.ART.app_mem, B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in HfrApp. lia. }
  (* the run's canonical start map *)
  pose (CANON := lib.Lib.Frame.mkR
    (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
    (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
    (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
    (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
    (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
    (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17)
    (Z_to_bv 64 phi)
    (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
    (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
    (Z_to_bv 64 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj))
    (Z_to_bv 64 (ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj)))
    (Z_to_bv 64 B.AsanRT.ASAN_K)
    (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
    (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  assert (Hxe : Lib.Regs6ss.xregs_eqv CANON regs3).
  { assert (HC : CANON = Lib.Regs6ss.mkR_of regs3).
    { unfold CANON, Lib.Regs6ss.mkR_of. unfold ACtlCut.rgv in H18, H24, H25, Hr26.
      f_equal; first [reflexivity | symmetry; assumption]. }
    rewrite HC. exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3)). }
  (* the registers both exits keep, and those they write *)
  apply (w4_seat_F W3 regs3 CANON 0x82728 mem3 md3
           (fun ms' => forall md', Reusable.YK04.same_but_materialized md3 md' ->
                         Reusable.YA0n.SRr segs W3 (mkCfg ms' md') (POST cx)) (POST cx) Hxe);
    [| intros ms' md' HP Hsbm _; exact (HP md' Hsbm)].
  unfold CANON.
  eapply (B.Prog.Seg.F21F.seg_F21_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
    (phi := phi) (k := ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj)
    (sv := ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj))
    (y0 := ACtlCutP.RPA.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 18)
    (y1 := ACtlCutP.RPA.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 19).
  - rewrite (B.Prog.Seg.F21.ckv_eq (ACtlCut.c_in cx) jj Hflen) in H10. exact H10.
  - exact Hphi0.
  - exact Hphi50.
  - exact Htk.
  - exact (B.Prog.Seg.F21.sumok_range _ _).
  - exact (B.Prog.Seg.F21.ubyte _).
  - exact (B.Prog.Seg.F21.ubyte _).
  - exact (B.Prog.Seg.F21.k6_rec _ _).
  - exact (B.Prog.Seg.F21.blk_b8 mem3 phi _ _ 0 (phi + 18) 18 ltac:(lia) ltac:(lia) eq_refl Hblk).
  - exact (B.Prog.Seg.F21.blk_b8 mem3 phi _ _ 1 (phi + 19) 19 ltac:(lia) ltac:(lia) eq_refl Hblk).
  - exact (B.Prog.Seg.F21.sh0 mem3 phi _ 18 (proj2 HHB) Hphi8 ltac:(lia) ltac:(lia)).
  - exact (B.Prog.Seg.F21.sh0 mem3 phi _ 19 (proj2 HHB) Hphi8 ltac:(lia) ltac:(lia)).
  - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
  - apply (w4_rng_block W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
  - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
  - apply (w4_rng_block_shadow W3 mem3 ly3 S3 md3 phi _ _ HAR Hin); lia.
  - (* EXIT 1: the sum-loop head 0x827f8 *)
    intros Hy0 Hy1 md' Hsbm.
    apply (w4m_exit W3 0x827f8).
    match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
    assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
    assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
    assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
    assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
    assert (E9 : getr R1 9 = getr regs3 9) by reflexivity.
    assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
    assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
    assert (E22 : getr R1 22 = getr regs3 22) by reflexivity.
    assert (E24 : getr R1 24 = getr regs3 24) by (transitivity (Z_to_bv 64 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj));
                                                   [reflexivity | symmetry; exact H24]).
    assert (E25 : getr R1 25 = getr regs3 25)
      by (transitivity (Z_to_bv 64 (ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj)));
          [reflexivity | symmetry; exact H25]).
    assert (E26 : getr R1 26 = getr regs3 26)
      by (transitivity (Z_to_bv 64 B.AsanRT.ASAN_K); [reflexivity | symmetry; exact Hr26]).
    assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
    apply (H7f8 cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem3 md' HB (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hsbm) HF HG1 Hk);
      [| exact HRT].
    unfold ACtlCutP.C_B827f8_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
    split; [reflexivity|].
    exists phi.
    split; [exact Hperm|].
    split; [exact (w4m_FRAC_tr cx fr fr R1 regs3 mem3 E2 E3 E4 E8 E9 E19 E26 HFRAC)|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (w4m_LK_tr cx fr jj R1 regs3 mem3 E9 E27 HLK)|].
    split; [exact (w4m_rgv_tr R1 regs3 20 _ E20 H20)|].
    split; [exact (w4_FM_keep cx jj phi fr R1 regs3 mem3 mem3 A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                     ltac:(lia) ltac:(lia) (fun _ _ => eq_refl) HFM)|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [exact (w4m_rgv_tr R1 regs3 24 _ E24 H24)|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
    split; [exact Hy0|]. split; [exact Hy1|].
    split; [exact Hblk|]. split; [exact Hbsl|].
    split.
    { intros i Hi. replace (phi + 34 + i) with (phi + (34 + i)) by lia.
      exact (B.Prog.Seg.F21.sh0 mem3 phi _ (34 + i) (proj2 HHB) Hphi8 ltac:(lia)
               ltac:(Z.div_mod_to_equations; lia)). }
    split; [exact (w4m_rgv_tr R1 regs3 25 _ E25 H25)|].
    split; [exact Happ|].
    split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
    split; [exact (w4m_FTURN_tr cx jj phi R1 regs3 mem3 E9 HFT)|].
    exact (w4m_IFS_tr cx fr (S jj) R1 regs3 mem3 HIFS).
  - (* EXIT 2: the head-amp call site 0x8283c, then seg_F22t *)
    intros a0' a1' Hne md' Hsbm.
    apply (w4m_exit W3 0x8283c).
    match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R2 := R) end.
    assert (E2 : getr R2 2 = getr regs3 2) by reflexivity.
    assert (E3 : getr R2 3 = getr regs3 3) by reflexivity.
    assert (E4 : getr R2 4 = getr regs3 4) by reflexivity.
    assert (E8 : getr R2 8 = getr regs3 8) by reflexivity.
    assert (E9 : getr R2 9 = getr regs3 9) by reflexivity.
    assert (E19 : getr R2 19 = getr regs3 19) by reflexivity.
    assert (E20 : getr R2 20 = getr regs3 20) by reflexivity.
    assert (E22 : getr R2 22 = getr regs3 22) by reflexivity.
    assert (E24 : getr R2 24 = getr regs3 24) by (transitivity (Z_to_bv 64 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj));
                                                   [reflexivity | symmetry; exact H24]).
    assert (E25 : getr R2 25 = getr regs3 25)
      by (transitivity (Z_to_bv 64 (ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj)));
          [reflexivity | symmetry; exact H25]).
    assert (E26 : getr R2 26 = getr regs3 26)
      by (transitivity (Z_to_bv 64 B.AsanRT.ASAN_K); [reflexivity | symmetry; exact Hr26]).
    assert (E27 : getr R2 27 = getr regs3 27) by reflexivity.
    apply (seg_F22t POST j H844 cx [Z.of_nat j] fr k ly3 S3 W3 R2 mem3 md' HB
             (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hsbm) HF HG1 Hk); [| exact HRT].
    unfold ACtlCutP.C_B8283c_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
    split; [reflexivity|].
    exists phi.
    split; [exact Hperm|].
    split; [exact (w4m_FRAC_tr cx fr fr R2 regs3 mem3 E2 E3 E4 E8 E9 E19 E26 HFRAC)|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (w4m_LK_tr cx fr jj R2 regs3 mem3 E9 E27 HLK)|].
    split; [exact (w4m_rgv_tr R2 regs3 20 _ E20 H20)|].
    split; [exact (w4_FM_keep cx jj phi fr R2 regs3 mem3 mem3 A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia)
                     ltac:(lia) ltac:(lia) (fun _ _ => eq_refl) HFM)|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    split; [unfold ACtlCut.rgv; rewrite (B.Prog.Seg.F21.want_m1 _ _ Hne); reflexivity|].
    split; [exact (w4m_rgv_tr R2 regs3 24 _ E24 H24)|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
    split; [exact Hblk|]. split; [exact Hbsl|].
    split; [exact (w4m_rgv_tr R2 regs3 25 _ E25 H25)|].
    split; [exact Happ|].
    split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
    split; [exact (w4m_FTURN_tr cx jj phi R2 regs3 mem3 E9 HFT)|].
    exact (w4m_IFS_tr cx fr (S jj) R2 regs3 mem3 HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82844_at j (0x82844) --S_F23--> B82878_at j.
   0x82844 bne a0,s7,82fa4 (not taken: a0 = s7 = t_want_v); sd s8,272(s1) ([A+272] := k); mv s8,s9;
   sb zero,16(s3); li a0,4; sb a0,17(s3) (S(fr)+16 := 0, S(fr)+17 := 4: [fr+128, fr+140) usable);
   a1 := 0x21180 (`__const.check_ports.ports`, 12 read-only bytes = three int32 -7); li a2,12;
   ld s5,104(s1) (s5 = fr + 128); mv a0,s5; jal __asan_memcpy (0x52164, ra 0x82874); 0x82874 li s7,1
   (UB Seg/F23.v:5-24).
   SINK BRANCH: 0x82844 `bne a0,s7,82fa4` (objdump L85342): not taken, a0 = s7 = t_want_v (C_B82844_at body
   `rgv regs 10 (t_want_v j)` and `rgv regs 23 (t_want_v j)`); discharged INSIDE f23_pre_F. *)
Lemma seg_F23 : forall POST (j : nat),
  ctl_from POST (ix C_B82878_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82844_at [Z.of_nat j]).
Proof.
  intros POST j H878 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  (* Plan (kept from the shell, revised): (1) f23_pre_F (0x82844 -> the copy's entry 0x52164, ra = 0x82874), run on
     `normalize rsegs mem3` (it needs mem_inv, ctl_rt carries only ro_agree) and carried back by
     MemNormF.evtF_normalize_ro, one lift at RNG_W; its raw munch [(Sfr fr + 16, + 18); (A + 272, + 280)] moves the
     journal (w4k_after_run).  (2) The copy by the core's journal rule YCbq.aj_intrin_at (AMEMCPY), d = fr + 128,
     x = 0x21180 (ports, image read-only bytes: ctl_ports_addressable / ctl_ports_shadow_vis), n = 12.  (3) li s7,1
     by F23F.f23_li_F, one lift.  (4) C_B82878_at at the final state: every carried byte is kept over the visible
     addresses outside the copy's destination, its window and the stretch's write set (the w4_ ... 2 transports);
     the three words -7 from the copy; ctl_rt by w4_ctlrt. *)
  unfold ACtlCutP.C_B82844_at in *.
  cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H20 & HFM & H10 & H18 & H23 & H24 & Hphi0 & Hphi50 &
    Hflen & Htk & Hblk & Hbsl & H25 & Happ & Hwin & HFT & HIFS).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1)
    as (Efr & _ & Bfr1 & Bfr2 & HfrApp & _ & HfrNimg & Hfpres & _ & Hsp16 & Hlsp & Hshi47 & Hpres).
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof HfrApp as HfrAppU. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in HfrAppU.
  pose proof HJ as (HAR & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (ctl_frame_above_img ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as Habove.
  rewrite <- Efr in Habove.
  pose proof HRT as (Hcells & HsrwC & HsrwI & HRO).
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _).
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HSfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (HSfrb : fr / 8 + 0x7fff8000 + 512 <= A) by (Z.div_mod_to_equations; lia).
  (* the turn block, apart from the frame *)
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (Hp16 & Hp4096 & Hpc & Happp & Hbpr & _).
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hin Hin6)
    as Hsep.
  unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- Efr in Hsep.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep.
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  assert (Hsp2 : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) = sp).
  { rewrite (w4_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  (* the spills and shadow facts the stretch reads *)
  pose proof HLK as (_ & _ & _ & (H27 & _ & _ & _ & _ & _ & S136 & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & _)).
  pose proof (w4m_spill regs3 mem3 104 (fr + 128) A S104 Hr9 ltac:(lia) ltac:(lia)) as Q104.
  pose proof HFM as (S184 & _ & H22 & _ & S312).
  (* route (C): ctl_rt_C's two shadow regions, on the normalized memory the run starts from (ShadowRwOnT) *)
  assert (HSW0n : B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly3 S3) (B.MemNorm.normalize B.Img0.rsegs mem3))
    by exact (B.ShadowRwOnT.shadow_rw_on_normalize _ mem3 HRO HsrwC).
  assert (HSWIn : B.ShadowRwOn.shadow_rw_on B.ACtlRtC.img_shadow (B.MemNorm.normalize B.Img0.rsegs mem3))
    by exact (B.ShadowRwOnT.shadow_rw_on_normalize _ mem3 HRO HsrwI).
  assert (HshIS : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 -> B.AsanRT.in_shadow x).
  { intros x Hx. rewrite HSfr in Hx. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
      B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG. Z.div_mod_to_equations. lia. }
  assert (HWRsh : lib.Lib.Mem.wr_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (ACtlCutP.Sfr fr + 16) 2).
  { split; [rewrite HSfr; Z.div_mod_to_equations; lia|]. split; [rewrite HSfr; Z.div_mod_to_equations; lia|].
    intros i Hi.
    destruct (HSW0n (ACtlCutP.Sfr fr + 16 + i)
                (w4_cut_fsh cx ly3 S3 fr (ACtlCutP.Sfr fr + 16 + i) Hin6 Efr ltac:(lia))
                (HshIS (ACtlCutP.Sfr fr + 16 + i) ltac:(lia))) as (Hw & _).
    exact Hw. }
  assert (HWRsp : lib.Lib.Mem.wr_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (A + 272) 8).
  { apply (B.Prog.Seg.F23.f23_wr_norm mem3 (A + 272) 8 HRO); [unfold B.Contract.GT; lia|].
    apply w4k_wr_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hpres x ltac:(lia))). }
  assert (HRTnewN : forall mm,
            lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 16, ACtlCutP.Sfr fr + 18); (A + 272, A + 280)]
              (B.MemNorm.normalize B.Img0.rsegs mem3) mm ->
            lib.Lib.Frame.wmono B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) mm ->
            B.Prog.MemMono.rd_mono (B.MemNorm.normalize B.Img0.rsegs mem3) mm ->
            B.AsanRT.asan_cells mm /\
            (forall P, B.ShadowRwOn.shadow_rw_on P (B.MemNorm.normalize B.Img0.rsegs mem3) ->
                       B.ShadowRwOn.shadow_rw_on P mm)).
  { intros mm MU0 WM0 RD0. split.
    - apply (B.AsanRTFacts.asan_cells_kept _ (B.MemNorm.normalize B.Img0.rsegs mem3) mm
               (B.Prog.Seg.F23.f23_cells_norm mem3 HRO Hcells) MU0).
      unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI. cbn [lib.Lib.Frame.disjoint_from].
      rewrite HSfr. split; [Z.div_mod_to_equations; lia|]. split; [lia | exact I].
    - intros P HP. exact (B.ShadowRwOnT.shadow_rw_on_mem_mono P _ mm HP WM0 RD0). }
  destruct (w4k_cb_raw mem3 (fr + 128) 12 ltac:(lia) ltac:(lia)
              (fun x Hx => proj2 (Hfpres x ltac:(lia)))) as (junk & Hjunk).
  pose proof (ctl_ports_addressable _ _ _ _ _ HAR) as HADS.
  (* (1) 0x82844 -> 0x52164 on the normalized memory, one lift *)
  apply w4m_enter.
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply B.MemNormF.evtF_normalize_ro; [exact HRO |].
    eapply (B.Prog.Seg.F23F.f23_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
      (A := A) (K3 := ACtlCutP.Sfr fr) (D := fr + 128) (v := ACtlCutP.SM.t_want_v (ACtlCut.c_in cx) jj)
      (kk := ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj) (lo := sp - B.Prog.asan_memcpy_c.ASAN_MEMCPY_K)
      (junk := junk);
      rewrite ?Hsp2.
    - exact (w4_rgv_reg _ 9 _ eq_refl Hr9).
    - exact (w4_rgv_reg _ 10 _ eq_refl H10).
    - exact (w4_rgv_reg _ 23 _ eq_refl H23).
    - exact (w4_rgv_reg _ 19 _ eq_refl Hr19).
    - exact (w4_rgv_reg _ 24 _ eq_refl H24).
    - lia.
    - lia.
    - rewrite HSfr. Z.div_mod_to_equations. lia.
    - pose proof B.Prog.SlotInv.FRAME_SHADOW_val. rewrite HSfr. Z.div_mod_to_equations. lia.
    - rewrite HSfr. unfold B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - Z.div_mod_to_equations. lia.
    - rewrite HSfr. unfold B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - intros t Ht. apply Happ. unfold ACtlCutP.FRAME_BYTES. lia.
    - unfold B.Contract.GT. lia.
    - lia.
    - rewrite HSfr. lia.
    - rewrite HSfr. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K. Z.div_mod_to_equations. lia.
    - rewrite HSfr. Z.div_mod_to_equations. lia.
    - exact Htk.
    - exact HWRsh.
    - exact HWRsp.
    - exact HRTnewN.
    - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRO Q104).
    - apply (B.Prog.Seg.F23.f23_rw_norm mem3 _ _ HRO); [unfold B.Contract.GT; lia | exact Hjunk].
    - exact (B.Prog.Seg.F23.f23_addr_norm mem3 _ _ HRO HADS).
    - exact (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem3).
    - apply (B.Prog.Seg.F23.f23_stk_norm mem3 _ _ HRO);
        [unfold B.Contract.GT, B.Prog.asan_memcpy_c.ASAN_MEMCPY_K; lia |].
      apply w4k_stk_raw; [unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K; lia | lia |].
      intros x Hx. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K in Hx. exact (proj2 (Hpres x ltac:(lia))).
    - lia.
    - unfold B.AsanRT.HIGHMEM_BEG, B.Prog.asan_memcpy_c.ASAN_MEMCPY_K. lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - unfold B.AsanRT.RT_HI. lia.
    - left. unfold B.Prog.asan_memcpy_c.ASAN_MEMCPY_K. lia.
    - lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible.
      split; [rewrite HSfr; Z.div_mod_to_equations; lia|]. split; [rewrite HSfr; Z.div_mod_to_equations; lia|].
      intros a Ha. refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_intror _))).
      rewrite HSfr in Ha. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
  intros ms' md' (s0 & (m' & -> & MU & WM & _ & ST' & AC' & SW' & B16 & B17 & Q272 & _ & _ & ADD) & REL & SAME)
    Hsbm Hhid.
  destruct (B.Prog.Seg.F23.f23_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
  rewrite Ems in Hhid, SAME |- *. cbn [ms_mem] in Hhid, SAME.
  set (m1 := ms_mem ms') in *.
  (* the stretch's post, back on the walk's memory m1 *)
  assert (HRO1 : B.MemNorm.ro_agree B.Img0.rsegs m1) by exact (B.MemNorm.ro_agree_of_mem_rel B.Img0.rsegs m1 m' HREL).
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 HRO) as REL0.
  pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ mem3 (B.MemNorm.normalize B.Img0.rsegs mem3) m1 m' REL0 HREL SAME MU)
    as MU1.
  assert (B16' : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (ACtlCutP.Sfr fr + 16) [Z_to_bv 8 0])
    by (apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 m' _ _ HREL)); exact B16).
  assert (B17' : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (ACtlCutP.Sfr fr + 17) [Z_to_bv 8 4])
    by (apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 m' _ _ HREL)); exact B17).
  assert (Q272' : ACtlCutP.q64 m1 (A + 272) (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj)).
  { unfold ACtlCutP.q64. apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 m' _ _ HREL)). exact Q272. }
  assert (ADD1 : B.AsanRT.addressable m1 (fr + 128) 12).
  { apply (w4m_bcmp_addr m' m1 (fr + 128) 12); [| exact ADD].
    intros i Hi. exact (B.MemNorm.mrd_rel B.Img0.rsegs m1 m' _ HREL). }
  pose proof (B.ShadowRwOnT.shadow_rw_on_of_rel _ m1 m' HREL (SW' _ HSWIn)) as SW1.
  (* the stretch's write set *)
  assert (Hin2 : forall a, ~ lib.Lib.Frame.outside [(ACtlCutP.Sfr fr + 16, ACtlCutP.Sfr fr + 18); (A + 272, A + 280)] a ->
                   (ACtlCutP.Sfr fr + 16 <= a < ACtlCutP.Sfr fr + 18) \/ (A + 272 <= a < A + 280)).
  { intros a Ha. cbn [lib.Lib.Frame.outside] in Ha.
    destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 16) a); destruct (Z_lt_ge_dec a (ACtlCutP.Sfr fr + 18));
    destruct (Z_le_gt_dec (A + 272) a); destruct (Z_lt_ge_dec a (A + 280));
    first [left; lia | right; lia | exfalso; apply Ha; repeat split; lia]. }
  assert (Hout2 : forall x, (x < ACtlCutP.Sfr fr + 16 \/ ACtlCutP.Sfr fr + 18 <= x) -> (x < A + 272 \/ A + 280 <= x) ->
                    lib.Lib.Frame.outside [(ACtlCutP.Sfr fr + 16, ACtlCutP.Sfr fr + 18); (A + 272, A + 280)] x)
    by (intros x H1 H2; cbn [lib.Lib.Frame.outside]; split; [lia | split; [lia | exact I]]).
  assert (Hwr1 : forall a, ~ lib.Lib.Frame.outside [(ACtlCutP.Sfr fr + 16, ACtlCutP.Sfr fr + 18); (A + 272, A + 280)] a ->
            exists b, m1 (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. destruct (Hin2 a Ha) as [Ha' | Ha'].
    - assert (Hni : ~ Reusable.YG0d.in_img segs a)
        by (apply w4k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; rewrite HSfr in Ha'; Z.div_mod_to_equations; lia).
      assert (Hb : exists b, lib.Lib.Mem.mrd B.Img0.rsegs m1 (lib.Lib.Mem.wa a) = Some b).
      { destruct (Z.eq_dec a (ACtlCutP.Sfr fr + 16)) as [Ea|Ea].
        - apply (w4_ba_rd m1 _ _ a B16'). cbn [length]. lia.
        - apply (w4_ba_rd m1 _ _ a B17'). cbn [length]. lia. }
      destruct Hb as (b & Hb). exists b.
      exact (w4k_mrd_raw m1 a b ltac:(rewrite HSfr in Ha'; Z.div_mod_to_equations; lia) Hni Hb).
    - assert (Hni : ~ Reusable.YG0d.in_img segs a) by (apply w4k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
      destruct (w4_ba_rd m1 (A + 272) _ a Q272' ltac:(rewrite lib.Lib.Mem.length_le8; cbn; lia)) as (b & Hb).
      exists b. exact (w4k_mrd_raw m1 a b ltac:(lia) Hni Hb). }
  assert (HJ1 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md' k).
  { apply (w4k_after_run cx ly3 S3 W3 mem3 md3 k m1 md' _ HJ MU1 Hhid Hsbm).
    intros a Ha. split; [exact (Hwr1 a Ha)|].
    destruct (Hin2 a Ha) as [Ha' | Ha'].
    - apply (w4k_awr_fsh cx ly3 fr _ _ _ _ a Efr). lia.
    - apply w4k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia. }
  (* (2) the copy, by the core's journal rule *)
  apply (w4m_exit W3 0x52164).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  change 0x52164 with Reusable.YB1w.tfib_A_asan_memcpy.
  pose proof (ctl_ports_addressable _ _ _ _ _ (proj1 HJ1)) as HADS1.
  pose proof (ctl_ports_shadow_vis _ _ _ _ _ (proj1 HJ1)) as (_ & _ & HPV).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in HPV.
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  assert (Hsrc1 : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 0x21180 B.Prog.Seg.F23.f23_src).
  { apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 (B.MemNorm.normalize B.Img0.rsegs m1) _ _
                   (B.MemNorm.mem_rel_normalize B.Img0.rsegs m1 HRO1))).
    exact (B.Prog.Seg.F23.f23_src_ro _ (B.MemNorm.mem_inv_normalize B.Img0.rsegs m1)). }
  pose proof B.Prog.Seg.F23.f23_src_len as Lsrc.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_intrin_at segs B LAWS segs_low Reusable.YG0d.OCpy _ AMEMCPY W3 R1 m1
      Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md' k (fr + 128) 0x21180 12
      (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82874) HJ1).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspR1. lia.
    - rewrite Zminus_mod, Hspm, Hsp16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - transitivity (getr regs3 3); [reflexivity | rewrite Hr3; exact Hgp0].
    - exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity.
    - intros a Ha. split.
      + apply (w4k_awr_fr cx ly3 fr _ _ _ _ a Efr). lia.
      + unfold Reusable.YG0d.ESTACK. lia.
    - apply (w4k_amem_frame fr); [exact Bfr1 | exact Bfr2 | exact HfrApp | lia | lia].
    - apply (w4m_bcmp_range_addr W3 m1 (fr + 128) 12); [| exact ADD1].
      intros i Hi. refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 m1 md' k fr _ HJ1 HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4m_bcmp_hull_frame cx ly3 S3 W3 m1 md' k fr); [exact HJ1 | exact HG1 | lia | lia | lia].
    - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      + lia.
      + lia.
      + intros a Ha. split.
        * assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) by (apply Himg; lia).
          rewrite (aview_vis_mrd W3 m1 a Hv).
          destruct (w4_ba_rd m1 0x21180 _ a Hsrc1 ltac:(rewrite Lsrc; cbn; lia)) as (b & Hb).
          unfold lib.Lib.Mem.wa in Hb. rewrite Hb. discriminate.
        * rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
      + right. lia.
      + unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd. left. lia.
      + apply (w4m_bcmp_range_addr W3 m1 0x21180 12); [| exact HADS1].
        intros i Hi. apply HPV. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
      + intros _ s Hs.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hs.
        assert (Hvs : Reusable.YA0n.w_H W3 (Z_to_bv 64 s) = false)
          by (apply HPV; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia).
        destruct (SW1 s (w4_img_sh s ltac:(Z.div_mod_to_equations; lia))
                    ltac:(unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END;
                               Z.div_mod_to_equations; lia)) as (_ & b & Hb).
        rewrite (aview_vis_mrd W3 m1 s Hvs). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. discriminate. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hcpy & Hfr2 & Hpres2).
  (* (3) 0x82874 li s7,1 -> 0x82878, one lift *)
  apply (w4m_enter W3 0x82874 regs2 mem2 md2).
  eapply w4m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of. eapply B.Prog.Seg.F23F.f23_li_F. }
  intros ms3 md3' -> Hsbm3 _.
  apply (w4m_exit W3 0x82878).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R3 := R) end.
  pose proof (w4m_aj_nowrite _ _ _ _ _ _ _ _ _ HJ2 Hsbm3) as HJ3.
  (* (4) the final state: registers *)
  assert (E2 : getr R3 2 = getr regs3 2)
    by (transitivity (getr regs2 2); [reflexivity | exact (HP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E3 : getr R3 3 = getr regs3 3)
    by (transitivity (getr regs2 3); [reflexivity | exact (HP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E4 : getr R3 4 = getr regs3 4)
    by (transitivity (getr regs2 4); [reflexivity | exact (HP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E8 : getr R3 8 = getr regs3 8)
    by (transitivity (getr regs2 8); [reflexivity | exact (HP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E9 : getr R3 9 = getr regs3 9)
    by (transitivity (getr regs2 9); [reflexivity | exact (HP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E18 : getr R3 18 = getr regs3 18)
    by (transitivity (getr regs2 18); [reflexivity | exact (HP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E19 : getr R3 19 = getr regs3 19)
    by (transitivity (getr regs2 19); [reflexivity | exact (HP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E20 : getr R3 20 = getr regs3 20)
    by (transitivity (getr regs2 20); [reflexivity | exact (HP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E21 : getr R3 21 = Z_to_bv 64 (fr + 128))
    by (transitivity (getr regs2 21); [reflexivity | exact (HP 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E22 : getr R3 22 = getr regs3 22)
    by (transitivity (getr regs2 22); [reflexivity | exact (HP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E23 : getr R3 23 = Z_to_bv 64 1) by reflexivity.
  assert (E24 : getr R3 24 = getr regs3 25)
    by (transitivity (getr regs2 24); [reflexivity | exact (HP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E26 : getr R3 26 = getr regs3 26)
    by (transitivity (getr regs2 26); [reflexivity | exact (HP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  assert (E27 : getr R3 27 = getr regs3 27)
    by (transitivity (getr regs2 27); [reflexivity | exact (HP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia))]).
  (* memory: a visible byte outside the copy's destination, its window and the stretch's write set is kept *)
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
     ~ (fr + 128 <= x < fr + 140) -> ~ (sp - 4096 <= x < sp) ->
     (x < ACtlCutP.Sfr fr + 16 \/ ACtlCutP.Sfr fr + 18 <= x) -> (x < A + 272 \/ A + 280 <= x) ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx Hv Hd Hw H1 H2.
    etransitivity.
    - apply (w4m_bcmp_pt W3 m1 mem2 x Hv).
      apply Hfr2; [exact Hx | intros Hc; apply Hd; lia | unfold Reusable.YG0d.ESTACK; lia].
    - exact (w4k_mrd_munch _ mem3 m1 x MU1 Hx (Hout2 x H1 H2)). }
  assert (KS1 : MKEPT mem3 mem2 (A + 40) (A + 272)).
  { intros x Hx. apply KEEP; [lia | exact (proj1 (Hpres x ltac:(lia))) | lia | lia | rewrite HSfr; lia | lia]. }
  assert (KS2 : MKEPT mem3 mem2 (A + 280) (ACtlCut.c_sp cx)).
  { intros x Hx. apply KEEP; [lia | exact (proj1 (Hpres x ltac:(lia))) | lia | lia | rewrite HSfr; lia | lia]. }
  assert (KF1 : MKEPT mem3 mem2 fr (fr + 24)).
  { intros x Hx. apply KEEP;
      [lia | exact (proj1 (Hfpres x ltac:(lia))) | lia | lia | rewrite HSfr; Z.div_mod_to_equations; lia | lia]. }
  assert (KF2 : MKEPT mem3 mem2 (fr + 2624) (fr + 4096)).
  { intros x Hx. apply KEEP;
      [lia | exact (proj1 (Hfpres x ltac:(lia))) | lia | lia | rewrite HSfr; Z.div_mod_to_equations; lia | lia]. }
  assert (KSH : MKEPT mem3 mem2 (ACtlCutP.Sfr fr + 328) (ACtlCutP.Sfr fr + 512)).
  { intros x Hx.
    assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false).
    { refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr x HJ HG1 (or_intror _))).
      rewrite HSfr in Hx. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    rewrite HSfr in Hx.
    apply KEEP; [Z.div_mod_to_equations; lia | exact Hv | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
                | rewrite HSfr; lia | lia]. }
  assert (KK : MKEPT mem3 mem2 ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112)).
  { intros x Hx. unfold ACtlCutP.KNA.KIND_NAME in Hx.
    apply KEEP; [lia | apply Himg; lia | lia | lia | rewrite HSfr; Z.div_mod_to_equations; lia | lia]. }
  assert (KB : MKEPT mem3 mem2 phi (phi + Reusable.YG00.req_size (ACtlCutP.flen cx jj))).
  { intros x Hx. apply KEEP;
      [lia | exact (proj1 (proj1 (Hbpr x Hx))) | lia | lia | rewrite HSfr; Z.div_mod_to_equations; lia | lia]. }
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx jj) ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. rewrite (proj2 Hreq) in Hi.
    pose proof (w4m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ i HAR Hin Hi) as Hv.
    apply KEEP; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia | exact Hv | | | |];
      rewrite ?HSfr; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia. }
  assert (Hpr2 : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, mem2 (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    exact (proj2 (Hpres2 a (w4m_bcmp_frame_present cx ly3 S3 W3 m1 md' k fr a HJ1 HG1 Ha'))). }
  pose proof (w4_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2) as (_ & HSW2 & _ & _).
  assert (KSh2 : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
                   exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 x) = Some b).
  { intros x Hx. destruct (HSW2 x (w4_cut_fsh cx ly3 S3 fr x Hin6 Efr ltac:(lia)) (HshIS x ltac:(lia)))
      as (_ & b & Hb). exists b. exact Hb. }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) as HKA.
  assert (Q272m2 : ACtlCutP.q64 mem2 (A + 272) (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj)).
  { apply (w4m_bcmp_q64 m1 mem2 (A + 272) _); [| exact Q272'].
    intros x Hx. apply (w4m_bcmp_pt W3 m1 mem2 x).
    - exact (proj1 (Hpres x ltac:(lia))).
    - apply Hfr2; [lia | lia | unfold Reusable.YG0d.ESTACK; lia]. }
  assert (ADD2 : B.AsanRT.addressable mem2 (fr + 128) 12).
  { apply (w4m_bcmp_addr m1 mem2 (fr + 128) 12); [| exact ADD1].
    intros i Hi. apply (w4m_bcmp_pt W3 m1 mem2).
    - refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - apply Hfr2; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; [Z.div_mod_to_equations; lia | |];
        [intros Hc; Z.div_mod_to_equations; lia | unfold Reusable.YG0d.ESTACK; Z.div_mod_to_equations; lia]. }
  assert (HD2 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 128) B.Prog.Seg.F23.f23_src).
  { pose proof Hsrc1 as (_ & _ & Hs1).
    split; [lia|]. split; [rewrite Lsrc; lia|].
    intros i Hi. rewrite Lsrc in Hi.
    apply (w4_copy_byte W3 m1 mem2 (fr + 128 + Z.of_nat i) (0x21180 + Z.of_nat i)).
    - refine (proj1 (w4m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_introl _))). lia.
    - apply Himg. lia.
    - exact (Hcpy (Z.of_nat i) ltac:(lia)).
    - exact (Hs1 i ltac:(rewrite Lsrc; exact Hi)).
    - apply nth_error_Some. rewrite Lsrc. exact Hi. }
  destruct (B.Prog.Seg.F23.f23_src_u32 mem2 (fr + 128) HD2) as (U1 & U2 & U3).
  assert (Lblk : length (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj) = 32%nat)
    by exact (B.Prog.Seg.F23.f23_blk_len _ _).
  assert (Ebig : ACtlCutP.SM.t_big (ACtlCut.c_in cx) jj = true)
    by (unfold ACtlCutP.SM.t_big; apply Z.leb_le; exact Hflen).
  assert (SP2 : forall off v, 40 <= off /\ off + 8 <= 272 \/ 280 <= off <= 440 ->
                  ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R3 mem2 off v)
    by (intros off v Ho Hs; exact (w4_sp2 R3 regs3 mem3 mem2 A (ACtlCut.c_sp cx) off v Hr9 E9 ltac:(lia)
                                     ltac:(lia) ltac:(lia) KS1 KS2 Ho Hs)).
  pose proof (w4_LK2 cx fr jj R3 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia) ltac:(lia)
                KS1 KS2 KF2 KSH KK HKA Hpr2 HLK) as HLK'.
  pose proof (w4_FTURN2 cx jj phi R3 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 ltac:(lia) ltac:(lia) ltac:(lia)
                KS1 KS2 (fun x Hx => KB x ltac:(lia)) HFT) as HFT'.
  pose proof HFT' as (_ & _ & Hphi2 & _).
  assert (S272 : ACtlCutP.spill R3 mem2 272 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj))
    by (exists A; split; [exact (w4m_rgv_tr R3 regs3 9 _ E9 Hr9) | exact Q272m2]).
  assert (R24 : ACtlCut.rgv R3 24 (ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj)))
    by (unfold ACtlCut.rgv; rewrite E24; exact H25).
  assert (R21 : ACtlCut.rgv R3 21 (fr + 128)) by exact E21.
  pose proof (SP2 184 _ ltac:(lia) S184) as S184'.
  pose proof (SP2 312 _ ltac:(lia) S312) as S312'.
  assert (Hblk2 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (phi + 18) (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj))
    by (apply (w4m_bcmp_bytes mem3 mem2 _ _); [intros x Hx; apply KB; rewrite Lblk in Hx; lia | exact Hblk]).
  apply (H878 cx [Z.of_nat j] fr k ly3 S3 W3 R3 mem2 md3' HB HJ3 HF HG1 Hk);
    [| exact (w4_ctlrt cx _ ly3 S3 W3 mem2 md3' k HB HJ3)].
  unfold ACtlCutP.C_B82878_at. cbn [ACtlCut.cut_body ACtlCut.ix_cut]. cbv zeta. fold jj.
  split; [reflexivity|].
  split.
  { apply (w4_FRAC2 cx fr fr R3 regs3 mem3 mem2 E2 E3 E4 E8 E9 E19 E26); [| exact KF1 | exact KF2 | exact KSh2 | exact HFRAC].
    intros A' HA' HA'0 HA'1.
    assert (EA : A' = A).
    { apply w4k_bv_inj; [lia | lia |]. unfold ACtlCut.rgv in HA', Hr9. rewrite <- HA'. exact Hr9. }
    subst A'. exact (conj KS1 KS2). }
  exists phi.
  split; [exact Hperm|]. split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4m_bcmp_HB mem3 mem2 phi _ KBS HHB)|].
  split; [exact (w4m_rgv_tr R3 regs3 18 _ E18 H18)|].
  split; [exact (w4m_rgv_tr R3 regs3 20 _ E20 H20)|].
  split; [exact HFT'|].
  cbv beta.
  split; [exact HLK'|].
  split; [exact (conj R21 (conj S184' (conj S272 (conj R24 S312'))))|].
  split; [unfold ACtlCut.rgv; rewrite E22; exact H22|].
  split; [exact (w4_IFS2 cx fr (S jj) R3 regs3 mem3 mem2 KF2 KSH HIFS)|].
  split.
  { refine (conj HLK' (conj (w4m_rgv_tr R3 regs3 18 _ E18 H18) (conj (w4m_rgv_tr R3 regs3 27 _ E27 H27)
      (conj Hphi0 (conj Hphi50 (conj Hflen (conj Hblk2 (conj _ (conj S272 (conj R24
      (conj (SP2 104 _ ltac:(lia) S104) (SP2 136 _ ltac:(lia) S136)))))))))))).
    rewrite Ebig in S312'. exact S312'. }
  split; [exact (w4m_rgv_tr R3 regs3 20 _ E20 H20)|].
  split; [exact E23|].
  split; [exact S184'|].
  split; [exact R21|].
  split; [exact U1|].
  split; [replace (fr + 132) with (fr + 128 + 4) by lia; exact U2|].
  split; [replace (fr + 136) with (fr + 128 + 8) by lia; exact U3|].
  split; [exact ADD2|].
  split; [split; [exact Hphi2 | intros H50; exact (B.Prog.SlotInv.t_g_of_phi mem2 phi _ _ Hphi2 H50)]|].
  unfold Reusable.YG0d.spZ in *. rewrite E2. exact Hwin.
Qed.

End W4e1.

(* Stage lemmas of this file (route C: all seven close with Qed).  seg_F21
   comes after seg_F22t because its exit 2 is carried through the head-amp callee by seg_F22t.
     seg_F18  : forall POST j, ctl_from POST (ix C_B8264c_at [j]) -> ctl_from POST (ix C_B82abc_at [j]) ->
                                ctl_from POST (ix C_B82634_at [j])
     seg_F19  : forall POST j, ctl_from POST (ix C_B82668_at [j]) -> ctl_from POST (ix C_B8264c_at [j])
     seg_F20  : forall POST j, ctl_from POST (ix C_B82728_at [j]) -> ctl_from POST (ix C_B82668_at [j])
     seg_F21  : forall POST j, ctl_from POST (ix C_B827f8_at [j]) -> ctl_from POST (ix C_B82844_at [j]) ->
                                ctl_from POST (ix C_B82728_at [j])
     seg_F22  : forall POST j, ctl_from POST (ix C_B8283c_at [j]) -> ctl_from POST (ix C_B827f8_at [j])
     seg_F22t : forall POST j, ctl_from POST (ix C_B82844_at [j]) -> ctl_from POST (ix C_B8283c_at [j])
     seg_F23  : forall POST j, ctl_from POST (ix C_B82878_at [j]) -> ctl_from POST (ix C_B82844_at [j])
   ([j] abbreviates [Z.of_nat j].)  Helpers: all proved (w4_ ..., the w4k_ toolkit from W3a, the w4m_ toolkit
   from W4f).
   Trap obligations (plan 6.2 / F.4.1): row 41 (S_F19, rec_inv), rows 42-46 (S_F20, rgv 18 phi + 0 < phi +
   phi + 50 <= 2^64), rows 47-51 (S_F21, same), row 52 (S_F22, the pinned a3 / a0 / a7 + phi bounds); each
   discharged inside its `_F` stretch from the cut body's conjuncts named at the stage. *)
