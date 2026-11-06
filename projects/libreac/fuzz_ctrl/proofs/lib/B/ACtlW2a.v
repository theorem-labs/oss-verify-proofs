(* lib/B/ACtlW2a.v -- stage glue of image B's (asan-ubsan) cgif-form walk of fuzz_ctrl's LLVMFuzzerTestOneInput,
   piece W2a: the first nine cuts of the 7-pass round trip loop_rt (from
   cut-table-B.tsv rows 11-19 (a working note, not in this delivery): B816ec_at b .. B818a8_at b), and the walk's ONE local lemma
   per allocator site inside loop_rt (malloc 0x81760, free 0x81a9c; the free site is shared with W2b's S_R15 / S_R16 /
   S_R20, which cite it from here).  Written by a Theorem Labs lane (subagent of a Theorem Labs lane) by brief
   bwalk-piece.md (a working note, not in this delivery).  Single writer.  rule 24: no function proved (stage glue
   of a walk).

   STATUS.  BUILT against the route-C shell on a working branch (ACtlCut.v with ix_cut, ctl_from_ix, ctl_chain,
   ctl_trace_in and ctl_rt_C; ACtlCutP.v's records; ACtl.v's stage hypotheses seg_R6 .. seg_R21_a5c, whose names and
   statements the stage lemmas here take).  The relocated cgif core for image B (Reusable.YB1v, YA0n, YA0nR, YK04R,
   YCbq, YC5d, YG0d, YG0f, YCfn, YE2k ...), lib/B/ProgBridge.v and lib/B/ProgWorld.v are in the tree, and every lemma
   here ends in Qed.  No Axiom, no Parameter, no Admitted, no Abort.  What is not proved here is a NAMED Section
   hypothesis (list below), each discharged at the top (lib/B/ACtl.v) or by its owner's proved lemma.
   The shell-argument lists are confined to the Local Notations of section 1.

   HOW EACH STAGE IS PROVED (route (a), lead FINAL 22:18Z via a Theorem Labs lane 22:29Z).  A stage lemma is "successor cuts hold ->
   this cut holds", POINTWISE in the round-trip index (ix_cut X [Z.of_nat b]), exactly as ctrl's own seg_R* lemmas
   are stated (Seg/R6.v:1165 .. R21.v:1206 at 3803efccea0: `Hat .. Inv_<succ> b -> Hat .. Inv_<this> b`).  Its proof:
   (1) unfold the cut body of C_<this> (lib/B/ACtlCutP.v) and derive the entry premises of the segment's proved run in
       footprint form (`<run>_F` / `<run>_pre_F` / `<run>_post_F`, a Theorem Labs lane's shape, bF-brief.md:36-47 (a working note, not in this delivery)), with
       RNG := RNG_W (w_H W3) and each rng premise from the world (ProgBridge rng_of_visible: V1 stack window, V3 the
       turn block Phi, V5 the fake frame and its shadow, V2 / V6 image cells);
   (2) lift the run with the kit's Reusable.YA0nR.SRr_fevt_hid (at head lib/Reusable/YA0nR.v:64), the hidden-bytes form of Reusable.YA0nR.SRr_fevt (proved, written on a working branch eea54967566,
       YA0nR.v (at head lib/Reusable/YA0nR.v:38)) through ProgBridge's fevt_of_evtF (the lemma FEVT below), fp_avoids by fp_avoids_RNG_W;
   (3) at a call: the callee's contract in SRr form (program callee: its proved route-C contract inside the lifted run, not a `<f>_SRr_at` (a Theorem Labs lane); or, for the four
       cut-callees build_as / parse / identity_reply / catalogue_match, the owner's caller-journal spec; runtime
       callee: the ONE owner's contract, never walked here (a Theorem Labs lane 22:28Z)); at the allocator: the site lemma of
       section 4, nothing else touches the allocator;
   (4) in the continuation re-establish C_<succ>'s body over the new registers / memory, the journal (ajournal_exec
       for a silent run whose write set is in the frame / stack window; the rule's own post at a call), frames S3 =
       own6 cx, the event bound, and ctl_rt_C by w2_ctl_rt (B.ProgWorldCtlRtC.ctl_rt_C_of_AR) in place of ctl_rt (ctrl's keep lemmas across runs, T4; a Theorem Labs lane's ctlrt_of_AR after the
       allocator, T2 / T3 / T12).
   No top, no W_cutfree_ok, no cut-free twin, no LSCPS join (route (a) conditions).

   THE _F STATEMENTS.  a Theorem Labs lane's runs (texts at bF-statements/R<k>F.md (a working note, not in this delivery))
   are proved lemmas of the modules lib.B.Prog.Seg.<File>F, which this file Requires qualified and cites by name
   (porter 23:38Z: no copy, no Section hypothesis, and no statement of this file names their vocabulary).  Names of
   record (a Theorem Labs lane's naming, bF-brief.md:36-43 (a working note, not in this delivery); inventory bseg-runs.md:89-123 (a working note, not in this delivery)).  Every run below is proved: R6F-R10F at
   a working branch e055327a537, R11F-R14F at a working branch efac84ed592 (all image-B `_F`
   now also on a working branch).  Each `_post_F` takes 0 steps (its start pc IS the return pc = the
   successor cut) and repackages a callee post stated in ctrl's RAW run vocabulary (raw munch / wmono).  RULE (a Theorem Labs lane
   00:4xZ, from this lane's finding): after a WORLD-FORM callee (a core rule, a runtime contract or a cut-callee's
   caller-journal spec) whose post constrains only the visible view, a raw-munch `_post_F` CANNOT be applied: the stage
   goes from the callee's post straight to the successor cut's body (visible addresses: aview equality + visibility =
   raw equality there; the runtime calls through ProgWorld's ctl_post_<callee>, visible-only).  A `_post_F` is cited
   only after a LIFTED callee (`<f>_SRr_at`, whose post comes from the lifted ctrl run with hidden bytes kept, a Theorem Labs lane's
   SRr_fevt_hid); none here: r10_frag6 / r10_frag5 (fragment) and r11 / r12 (ingest) run the callee inside the lifted run.  Runs W2a needs (source lemma
   (from a working branch 3803efccea0) -> _F name; "not applied" marks a `_post_F` the rule excludes):
     S_R6   r6_evt R6.v:347 (calls reac_ctrl_build_as @0x8170c)        -> R6F.r6_evt_pre_F (R6F.v:45-62: 0x816ec ->
                                                                          build_as entry 0x8528c, ra 0x81710) +
                                                                          R6F.r6_evt_post_F (R6F.v:72-121, 0 steps;
                                                                          not applied: build_as is a cut-callee)
     S_R7   r7_evt R7.v:144 (0x81710 -> malloc entry 0x534b8)          -> R7F.r7_evt_F (R7F.v:51)
            r7_evt0 R7.v:165 (0x81710 -> 0x81ac0, n_b = 0)             -> R7F.r7_evt0_F (R7F.v:74)
     S_R8   r8_evt R8.v:59 (calls __asan_memcpy @0x81778)              -> R8F.r8_evt_pre_F (R8F.v:27-38: 0x81764 ->
                                                                          __asan_memcpy 0x52164, ra 0x8177c) +
                                                                          R8F.r8_evt_post_F (R8F.v:49-68; not applied)
     S_R9   r9_st R9.v:74 (0x8177c -> 0x81794, no call)                -> R9F.r9_st_F (R9F.v:49-65; compare
                                                                          r9_st_of_F :84)
            r9_call R9.v:107 (calls reac_ctrl_parse @0x817a0)          -> R9F.r9_call_pre_F (R9F.v:122-133: 0x81794
                                                                          -> reac_ctrl_parse 0x83e04, ra 0x817a4) +
                                                                          R9F.r9_call_post_F (R9F.v:143-176; not applied)
     S_R10  r10_cfg0 :134, r10_sum12 :196, r10_head_reply :252, r10_head_frag6 :301, r10_head_frag5 :351 (no call)
                                                                       -> R10F.r10_cfg0_F :71, r10_sum12_F :167,
                                                                          r10_head_reply_F :257, r10_head_frag6_F :337,
                                                                          r10_head_frag5_F :418 (each with an `_of_F`
                                                                          compare lemma)
            r10_reply_call :401 (reac_ctrl_identity_reply @0x817e8)    -> R10F.r10_reply_call_pre_F :501 (0x817d4 ->
                                                                          reply 0x848fc, ra 0x817ec) +
                                                                          r10_reply_call_post_F :525 (not applied)
            r10_frag6_call :534 (reac_ctrl_identity_fragment @0x81830) -> R10F.r10_frag6_call_pre_F :581 (0x81818 ->
                                                                          fragment 0x859e4, ra 0x81834) +
                                                                          r10_frag6_call_post_F :606
            r10_frag5_call :650 (reac_ctrl_identity_fragment @0x81910) -> R10F.r10_frag5_call_pre_F :649 (0x818f8 ->
                                                                          fragment 0x859e4, ra 0x81914) +
                                                                          r10_frag5_call_post_F :674
     S_R11  r11_evt R11.v (not in this delivery) (reac_identity_ingest @0x8185c)          -> R11F.r11_pre_F (R11F.v:47) + r11_post_F (:88)
     S_R12  r12_evt R12.v (not in this delivery) (reac_identity_ingest @0x8185c)          -> R12F.r12_pre_F (R12F.v:47) + r12_post_F (:89)
     S_R13  r13_evt R13.v:84 (0x81860 -> free entry 0x534b4)           -> R13F.r13_evt_F (R13F.v:42)
     S_R14  r14_loop R14.v:621 (32-turn block sum) + r14_evt R14.v:703 (reac_box_catalogue_match @0x819a4)
                                                                       -> R14F.r14_pre_F (R14F.v:134-157: ONE stretch
                                                                          from 0x818a8 at block-sum turn i, the
                                                                          32-turn loop included, to catalogue_match
                                                                          entry CMC.REAC_BOX_CATALOGUE_MATCH, ra
                                                                          0x819a8) + R14F.r14_post_F (R14F.v:187-205,
                                                                          0 steps; not applied: catalogue_match is a
                                                                          cut-callee).  The old names r14_loop_F /
                                                                          r14_evt_pre_F are gone.

   SECTION HYPOTHESES (each with its source; all are discharged at the top, lib/B/ACtl.v, or replaced by the named
   owner's lemma when it lands):
     AMALLOC4  Reusable.YC5d.amalloc04_rule segs B MT     the core's malloc rule (donor YC5d.v:56-74), carried as a
               Hypothesis exactly as every donor walk file does (A/ACf2.v:50); ctrl's instance from the core.
     AFREE4    Reusable.YC5d.afree04_rule segs B MT       the core's free rule (YC5d.v:75-96; donor A/ACf3.v:40).
     HMOK      forall S m, mo_ok MT S m                   the trivial meter (ACtlCut.v section header; donor A/AD2o.v:49
               MT_FREE := fun _ _ => I at MT := ameter_triv, YCbp.v:16).
     HPCM/HPCF the wrapper entries of B's code table, by the core's catalogue NAMES (porter 23:00Z: never a literal
               runtime pc): pc_wrap_malloc (as_code B) = Reusable.YB1w.tfib_A_malloc and pc_wrap_free (as_code B) =
               Reusable.YB1w.tfib_A_free (donor root YB1w.v:159-160, the 4-byte trampolines; image B values 0x534b8 /
               0x534b4, plan F.3 rows 16 / 18, ctrl's R7.v:144 / R13.v:84 run posts) -- the donor's tl_code B TL
               pattern (A/ACf2.v:52, :114); from the core's ctrl-B instance (a Theorem Labs lane).
     AMEMCPY   Reusable.YG0d.aintrin_realizes segs B OCpy Reusable.YB1w.tfib_A_asan_memcpy   the core's memcpy rule
               (YG0d.v:318; donor A/ACf2.v:51), at S_R8's call 0x81778; runtime callees are never walked here
               (a Theorem Labs lane 22:28Z), and their pc is the core's catalogue name (porter 23:00Z).
     ctl_post_memcpy  ProgWorld's raw-memory conversion after AMEMCPY's world-form post (visible-only mrd form,
               a Theorem Labs lane 00:42Z): now a LEMMA of that name, by B.ProgWorld.ctl_post_memcpy (ProgWorld.v:765).
     aview_vis_mrd  a Theorem Labs lane's one primitive: at a visible address the core's view is lib/Lib's mrd read, the
               address a Z.  Raw `mem x` equality is not derivable from a view post; mrd equality is.  Now a LEMMA of
               that name, by B.ProgWorld.aview_vis_mrd (ProgWorld.v:587).
     ctl_post_acall_kept  a Theorem Labs lane's allocator conversion: from acall_kept (where amalloc04_rule / afree04_rule end) the
               raw mrd read is kept at a visible address of a KEPT CLASS - high memory outside the window, a live block
               off E, a non-owned non-errno image byte, a live frame's bytes or shadow off E.  Used at S_R7 (E = the new
               block) and S_R13 (E = the freed block), with [slo, shi) = [sp - ASTACK, sp).  Now a LEMMA of that name,
               by B.ProgWorld.ctl_post_acall_kept (ProgWorld.v:681).
     CHAIN_OF_CUT  the frame-pointer chain and the call trace at the four allocator calls (ra 0x81764, 0x81aa0,
               0x81f50, 0x82d1c), over the shell's ctl_chain / ctl_trace_in (ACtlCut.v section 1b); the same name and
               text as the top's Section hypothesis (lib/B/ACtl.v), which discharges it (donor rt_chain + rt_trace_in,
               A/ACf2.v:101-107 / :133-136).
     img_vis_W the image range [IMG_LO, IMG_TOP) = [0x10000, 0x5fe000) is visible in every world, by the core's names
               Reusable.YImgTop.IMG_LO / IMG_TOP; text identical to the other stage files'.  Now a LEMMA of that name,
               by B.ProgBridge.img_vis_W (ProgBridge.v:121, over B/Prog/ImgBounds.v's IMG_LO / IMG_HI, the same
               numbers).  Cited where a W2a callee asks an image range: reac_ctrl_identity_fragment (S_R10, b = 5 / 6)
               and reac_identity_ingest (S_R11 / S_R12).
     FEVT      ProgBridge's fevt_of_evtF over segs (= B.Img0.rsegs by tfibsegs_rsegs): now a LEMMA of that name, by
               B.ProgBridge.fevt_of_evtF (ProgBridge.v:30).
   The caller-journal specs of the four cut-callees (PARSE, BUILD_AS, TREPLY, TMATCH), the RtPost data facts and the
   other shared members are pasted token for token from lib/B/RTPOST-SHARED-B.txt (section 3 below); the callees
   reac_identity_ingest and reac_ctrl_identity_fragment are cited by their owners' proved route-C contracts
   (B.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on, B.Prog.reac_ctrl_identity_fragment_F_closed.
   reac_ctrl_identity_fragment_holds_F_closed_on).

   UBSAN TRAPS IN W2a (plan section 6.2, F.4.1).  One branch to unimp 0x82fa0: row 4, 0x818b0 (bne a5,s11 / trap iff
   Phi_r + 18 + i = 0 mod 2^64), on S_R14's path from B818a8_at.  It is stepped INSIDE R14F.r14_pre_F (R14F.v:134;
   the 32-turn block sum 0x818a8 .. 0x818dc and on to the call), so its discharge is the run's premises 4096 <= p and
   p + 50 <= APPMEM_END (R14F.v:139), which the B818a8 stage derives: a3 = -(phi+18), a4 = 32-i, i < 32, s11 = 32
   from the body (rgv 13 / rgv 14 / i < 32 / rgv 27 32); RF -> RFb gives rnb cx b <> 0, so rnb >= 52 (SM.rt_n,
   SlotModel.v:80; R7's r7_nv); the body's live list puts (phi, rnb cx b) in ablocks B ly3 S3, and the core's
   AR_blocks_law (YG0d.v:422-433, al_blocks) gives 4096 <= phi and phi + req_size (rnb cx b) <= alloc_ceiling
   (0x7fff7f800000 < APPMEM_END - 50).  The other W2a segments have an empty trap set.

   ALLOCATOR SITES (brief: ONE local lemma per site, nothing else touching the allocator).  w2_malloc_81760 (S_R7) and
   w2_free_81a9c (S_R13 here; S_R15 / S_R16 / S_R20 in W2b) in section 4. *)
From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The core copies of the modules lib/B/Reusable shadows (YK11 YK0s YM05 YI16 YO09), Required from lib.Reusable only
   (porter 04:33Z amendment (b): a partial `Reusable.X` Require matches both copies). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK0s YM05 YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK06 Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
(* ProgBridge's proved glue (RNG_W, fp_avoids_RNG_W, rng_of_visible, rsegs_spans), Required only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge.
(* lib/Lib's raw-memory vocabulary of the call-post fact ctl_post_memcpy (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step.
(* a Theorem Labs lane's footprint runs of S_R6 .. S_R14 (lib/B/Prog/Seg/<File>F.v; RNG-first binder, `_pre_F` / `_post_F`
   split at every call), Required QUALIFIED, never Imported (porter 23:38Z rule (1)); they arrive with a Theorem Labs lane's line.
   No statement of this file names their vocabulary (rule (2)): they are used in proofs only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R6F R7F R8F R9F R10F R11F R12F R13F R14F.
(* The ctl_rt ONE FORM (walk line 0110c1f2b9b): a Theorem Labs lane's image-B ProgWorld (VIS0 / OWNED_RO texts, arodata_okP_of_S)
   and its proved B.ProgWorldCtlRt.ctlrt_of_AR; the PA layer's read-only names (B.Prog.CtrlBase re-exports
   lib/Reusable/APostBase); the core's CtrlTSyms (TFIB_SYMS's type).  Required only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldCtlRt B.Prog.CtrlBase.
(* Route C (a working branch): ctl_rt_C and its proved supply lemma ctl_rt_C_of_AR (f4e8c59008a), Required only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0m APostBase.
(* The image's closed contract of reac_identity_ingest (S_R11 / S_R12's callee), Required only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_identity_ingest_c B.Prog.reac_identity_ingestF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib.
(* The callee world specs on the walk line (statements only), Required only: reac_ctrl_parse (S_R9).  Image B's
   MemNorm route for the r9_st_F stretch (its callee form takes mem_inv; the stretch runs on B.MemNorm.normalize and
   B.ProgWorld.rebase_ro_normalize brings it back), by B's copies by full name. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_identity_reply
  B.Prog.C_reac_ctrl_build_as B.Prog.C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm B.MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
(* The fake stack lies above image B (ProgWorld_Fs.pw_F_above), for build_as's header homes (S_R6). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld_Fs.
(* S_R10's fragment arms (b = 5, 6): the callee's route-C statement, its closed corollary (a Theorem Labs lane's fragment run
   462b9de45af, of record; on a working branch 280beb39d1bb) and its R's leaves, the bcmp cells' homes, and ProgWorld's
   proved visibility lemmas (the callee window's shadow cover, a live block's shadow cover, a live frame's bytes and
   shadow cover).  Required only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_fragment_F_closed.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_identity_fragment_c B.Prog.sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memcpy_c_on B.Prog.bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.bcmp_wrap_c B.Prog.memcmp_c B.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldVisWin B.ProgWorldVisHeap B.ProgWorldVisFrame.
Import ListNotations.
Local Open Scope Z_scope.

Section W2a.

(* ---------------------------------------------------------------------------------------------------------
   1. The shell's parameters and this file's short names.  The Context / Variable list is the shell's (new form,
   a Theorem Labs lane 22:41Z (e) and 22:47Z); the sink instance is passed EXPLICITLY at the top (Reusable.YE2k.tfib_sink_head,
   ofl_head 0x5fcd48; porter 22:45Z), never resolved by instance search.  ONE PLACE TO ALIGN at the re-twin: the
   argument lists of CFb / CBASE / AJ and the record notations below. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.
Local Notation ctlcx := B.ACtlCut.ctlcx.
(* A cut at turn b, as lib/B/ACtl.v states every W2 stage hypothesis: ix_cut X [Z.of_nat b] (ACtlCut.v section 5). *)
Local Notation CFb POST X b :=
  (B.ACtlCut.ctl_from B MT XM_LIB RLO RHI FP POST (B.ACtlCut.ix_cut X [Z.of_nat b])).
Local Notation CBASE cx := (B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
     (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation ENTRYBL cx := (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)).
Local Notation rnb := B.ACtlCutP.rnb.
Local Notation own6 := B.ACtlCut.own6.

(* The cut records this piece and its successors name (lib/B/ACtlCutP.v, generated by a Theorem Labs lane; each applied to
   the asyms B its bodies read through ablocks / as_tp). *)
Local Notation C816ec := (B.ACtlCutP.C_B816ec_at B).
Local Notation C81710 := (B.ACtlCutP.C_B81710_at B).
Local Notation C81764 := (B.ACtlCutP.C_B81764_at B).
Local Notation C8177c := (B.ACtlCutP.C_B8177c_at B).
Local Notation C817a4 := (B.ACtlCutP.C_B817a4_at B).
Local Notation C817ec := (B.ACtlCutP.C_B817ec_at B).
Local Notation C81834 := (B.ACtlCutP.C_B81834_at B).
Local Notation C81860 := (B.ACtlCutP.C_B81860_at B).
Local Notation C818a8 := (B.ACtlCutP.C_B818a8_at B).
Local Notation C81914 := (B.ACtlCutP.C_B81914_at B).
Local Notation C8194c := (B.ACtlCutP.C_B8194c_at B).
Local Notation C819a8 := (B.ACtlCutP.C_B819a8_at B).
Local Notation C81aa0 := (B.ACtlCutP.C_B81aa0_at B).
Local Notation C81ac0 := (B.ACtlCutP.C_B81ac0_at B).

(* ---------------------------------------------------------------------------------------------------------
   2. Section hypotheses with a published text (sources in the header). *)

(* The core's allocator rules for ctrl's B (donor YC5d.v:56-74 / :75-96), as every donor walk file carries them. *)
Hypothesis AMALLOC4 : Reusable.YC5d.amalloc04_rule (fx:=fx) (rc:=rc) (SK:=SK) segs B MT.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (fx:=fx) (rc:=rc) (SK:=SK) segs B MT.

(* The trivial meter (donor A/AD2o.v:49, MT_FREE). *)
Hypothesis HMOK : forall S m, Reusable.YC5d.mo_ok MT S m.

(* The core's AR laws (donor A/ACf2.v:47 `Hypothesis LAWS : AR_laws tfibsegs B`; the same text as lib/B/ACtlW3a.v,
   ACtlW4e1.v, ACtlW4g.v): al_blocks for w2_phi_not_entry; supplied by the core's api_of_core (aa_laws). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The runtime fact at a cut is ctl_rt_C (route C, a working branch 78699c46fe7): every exit supplies it by the proved
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR, which takes CtrlTSyms and AR_laws (LAWS above) only (VIS0 / OWNED_RO are
   gone: VIS0 is false at an AR state).  TFIB_SYMS token-equal to lib/B/ACtl.v's (Section Ctl); the top supplies it. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.

(* ctl_rt_C_of_AR reads the read-only view as arodata_okP at the state it is applied to.  ctl_base carries
   arodata_okS at the cut's base state (YCfn.v:40); ProgWorld.arodata_okP_of_S turns it into arodata_okP and
   APostBase.arodata_ok_journalP (cited unchanged) carries it along the journal to the current state.  That lemma's
   section takes the read-only span in the image (RELRO_IMG, token-equal to lib/B/ACtl.v:152) and the instance
   ro_below_ofl.  RO_OFL: discharged by the TOP (owner a Theorem Labs lane) at SK := Reusable.YE2k.tfib_sink_head by
   computation; image-A twin lib/A/Prog/ACj1.v:179 (owner ruling a Theorem Labs lane 06:47Z, the ONE shared form). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* B's allocator wrapper entries, by the core's catalogue names (plan F.3 rows 16 / 18; R7.v:144 / R13.v:84 run posts
   reach them at the literal pcs 0x534b8 / 0x534b4, which the names unfold to after relocation). *)
Hypothesis HPCM : Reusable.YG0f.pc_wrap_malloc (Reusable.YG0f.as_code B) = Reusable.YB1w.tfib_A_malloc.
Hypothesis HPCF : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code B) = Reusable.YB1w.tfib_A_free.

(* The core's memcpy rule at B's __asan_memcpy (donor A/ACf2.v:51 `Hypothesis AMEMCPY : aintrin_realizes tfibsegs B
   OCpy A_asan_memcpy`; the entry by the core's catalogue name, porter 23:00Z).  Used at S_R8's call 0x81778. *)
Hypothesis AMEMCPY :
  Reusable.YG0d.aintrin_realizes (fx:=fx) (rc:=rc) segs B Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy.

(* reac_ctrl_parse's caller-journal spec (S_R9's call 0x817a0 -> 0x83e04), the SHARED form (owner ruling a Theorem Labs lane
   07:43Z; a Theorem Labs lane's W4a PARSE (ACtlW4a.v:279) is the same statement).  owner: a Theorem Labs lane, the prover of pb_reac_ctrl_parse
   (a Theorem Labs lane's line, lib/B/Prog/C_reac_ctrl_parse.v from 24eccbe90cb); top obligation. *)
Hypothesis PARSE : B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) segs B RLO RHI.

(* reac_ctrl_identity_reply's caller-journal spec (S_R10's call at b = 3, 4), the SHARED form (owner ruling a Theorem Labs lane
   07:49Z, corrected 08:17Z: the constant takes RLO RHI B); owner a Theorem Labs lane; top obligation. *)
Hypothesis TREPLY : B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec RLO RHI B.

(* reac_ctrl_build_as's caller-journal spec (S_R6's call), the SHARED form (RTPOST-SHARED-B.txt (a working note, not in this delivery) on a working branch 94da0a5cc85,
   token for token); owner a Theorem Labs lane, discharged at the top by pb_reac_ctrl_build_as.  11:20Z: RLO RHI are arguments
   (a Theorem Labs lane f0b81758c2d, order RLO RHI B GLOBS); 09:05Z: SK-generic, takes GLOBS. *)
Variable GLOBS : list (Z * Z).
Hypothesis BUILD_AS : B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_spec (SK := SK) RLO RHI B GLOBS.
(* The read-only-global facts the build_as call needs (ruling 09:08Z); owner: the top (a Theorem Labs lane), with a Theorem Labs lane's
   GLOBS list and globs_marked lemma. *)
Hypothesis ctl_cat_ro : B.Prog.C_reac_ctrl_build_as.EmitB.tctrl_emit_as_ro RLO RHI B GLOBS
  B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N).
Hypothesis ctl_names_ro : forall inp : list byte,
  B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb inp) <> 0 -> B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <> 0 ->
  B.Prog.C_reac_ctrl_build_as.EmitB.tctrl_emit_as_ro RLO RHI B GLOBS
    (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp)) (Z.of_nat (length (B.ACtlCutP.SM.rt_nb inp))).

(* reac_box_catalogue_match's spec (S_R14's call 0x819a4 -> 0x84e40), the SHARED form (a Theorem Labs lane 08:4xZ: the W4f name
   with the constant's own arguments {fx rc SK} RLO RHI B); owner a Theorem Labs lane (catmatch glue); top obligation. *)
Hypothesis TMATCH : B.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := SK) RLO RHI B.

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

(* BOXA's six bytes in the view form build_as's s-header premises consume (accepted by the owner a Theorem Labs lane 10:30Z,
   RTPOST at 829f8c8776e; proof owner a Theorem Labs lane, from CtrlRo.globs_marked + img_shadow_vis). *)
Hypothesis ctl_box_view : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF
    B.ACtlCutP.SM.BOXA 6 /\
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) B.ACtlCutP.SM.BOXA 6.

(* RtPost members this file uses, pasted token for token from the ONE shared text (a Theorem Labs lane's
   working branch 981c1faff75 RTPOST-SHARED-B.txt (a working note, not in this delivery); the B twins of a Theorem Labs lane's lib/A/ProgWorld.v
   at c03ce1627b6).  Do not edit here: change the shared text and re-paste. *)
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

(* aview_vis_mrd: proved as B.ProgWorld.aview_vis_mrd (lib/B/ProgWorld.v:587; RTPOST-SHARED-B.txt at 3131914eb3ca cites
   it).  The same name and statement, as a lemma; ProgWorld's segs is this file's Reusable.YB1v.tfibsegs. *)
Lemma aview_vis_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof. exact B.ProgWorld.aview_vis_mrd. Qed.

(* ctl_post_memcpy: proved as B.ProgWorld.ctl_post_memcpy (lib/B/ProgWorld.v:765, statement ctl_post_memcpy_stmt :633;
   RTPOST cites it).  WR = [d, d + n) + the callee window.  The same name and statement, as a lemma: the RtPost
   notations munch_vis / wmono_vis / rt_post_frame above unfold to ProgWorld's definitions of those names. *)
Lemma ctl_post_memcpy :
  forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp d x n : Z) (src : list byte),
    0 <= d -> d + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 -> Z.of_nat (length src) = n ->
    (forall a, d <= a < d + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem x src ->
    (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (x + i)) = false) ->
    (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' (d + i) =
                             Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem (x + i)) ->
    rt_post_frame W mem mem' ((d, d + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (Reusable.YA0n.w_H W) ((d, d + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' d (lib.Lib.Cells.CB (Z.to_nat n) src :: nil).
Proof. exact B.ProgWorld.ctl_post_memcpy. Qed.

(* kept_class / ctl_post_acall_kept: proved as B.ProgWorld.ctl_post_acall_kept (lib/B/ProgWorld.v:681; its kept_class is
   the Definition at :669, this notation's expansion; RTPOST cites it).  The ceiling is YM05's RunCeil field
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
Lemma ctl_post_acall_kept : forall (B : Reusable.YG0f.asyms) lyc Sc (W W2 : Reusable.YA0n.world segs)
    (memc mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop),
  Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E ->
  Reusable.YA0n.wle W W2 ->
  forall x : word, Reusable.YA0n.w_H W x = false -> kept_class B lyc Sc slo shi E (bv_unsigned x) ->
    lib.Lib.Mem.mrd B.Img0.rsegs mem2 x = lib.Lib.Mem.mrd B.Img0.rsegs memc x.
Proof. exact B.ProgWorld.ctl_post_acall_kept. Qed.

(* img_vis_W: proved as B.ProgBridge.img_vis_W (lib/B/ProgBridge.v:121; RTPOST cites it).  The same name and statement
   (the shape the stage files share, bounds by the core's names Reusable.YImgTop.IMG_LO / IMG_TOP, never the literals),
   as a lemma.  CONVERSION: ProgBridge states it as range_visible (w_H W) ImgBounds.IMG_LO (ImgBounds.IMG_HI -
   ImgBounds.IMG_LO), whose definition is this three-part conjunction; ImgBounds.IMG_LO / IMG_HI and
   Reusable.YImgTop.IMG_LO / IMG_TOP are both 0x10000 / 0x5fe000; world segs = world rsegs (tfibsegs_rsegs,
   reflexivity).  So the proof is the cited lemma after unfolding those constants. *)
Lemma img_vis_W : forall W : Reusable.YA0n.world segs,
  0 <= Reusable.YImgTop.IMG_LO /\
  Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) <= 2 ^ 64 /\
  forall a, Reusable.YImgTop.IMG_LO <= a <
              Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) ->
    Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof. intros W. exact (B.ProgBridge.img_vis_W W). Qed.

(* ---- Image-B data facts T10 / V6 (added 04:31Z by a Theorem Labs lane, the text's one writer; drafted by a Theorem Labs lane).
   OWNER: a Theorem Labs lane, who proves both in lib/B/ProgBridgeData.v by vm_compute over a Theorem Labs lane's REGENERATED
   as_owned_static B / CtrlBB tables (a working branch 8db247c6f3e), never the planning core's.
   Users: seg_R7 / seg_R8 / seg_R13 (W2), W4e / W4f where RBE's facts cross a malloc / free / memcpy.
   T10: the catalogue's read-only data is neither a static owned extent nor the errno cell, so ctl_post_acall_kept's
   image arm keeps it across an allocator call.
   V6: the row-name bytes RBE names stay addressable; it is a bridge fact from AR (ctlrt_of_AR's shape), not a fact
   over as_zero_shadow B: the row names are globals with a partial last granule (lib/B/FrameAPI.v:29 frame_AG,
   shadow byte 07), so an 8-aligned zero-shadow cover would be false, and the image's shadow is allocator-owned
   (YG0f.v:298-299), so acall_kept keeps nothing there. *)
Hypothesis ctl_relro_not_owned : forall a : Z,
  (B.ACtlCutP.BAC.BA_FR + 72 <= a < B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) \/
   B.ACtlCutP.SM.CAT <= a < B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

Hypothesis ctl_names_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md (inp : list byte),
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb inp) <> 0 -> B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <> 0 ->
  B.AsanRT.addressable mem (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp))
    (Z.of_nat (length (B.ACtlCutP.SM.rt_nb inp))).

(* ProgBridge.fevt_of_evtF, image B (bridge-stmt.md:102): proved there (lib/B/ProgBridge.v:30, over B.Img0.rsegs, which is
   segs = Reusable.YB1v.tfibsegs by ProgBridge.tfibsegs_rsegs, reflexivity).  The same name and statement, as a lemma. *)
Lemma FEVT : forall (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (ms : machine_state),
  Lib.ExecF.evtF B.Img0.rsegs RNG P ms -> exists ms', Reusable.YK04R.fsteps segs RNG ms ms' /\ P ms'.
Proof. intros RNG P ms H. exact (B.ProgBridge.fevt_of_evtF RNG P ms H). Qed.

(* The frame-pointer chain and the call trace at an allocator call, by the shell's names (ACtlCut.v section 1b:
   ctl_chain / ctl_trace_in).  The statement is the shell's ctl_chain_of_cut, which the top carries as its Section
   hypothesis CHAIN_OF_CUT (a Theorem Labs lane 23:5xZ); same name and same text here, so the top discharges this one with
   its own.  It came from this file's HCHAIN (ffb9cb21497). *)
Hypothesis CHAIN_OF_CUT : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word) (pc0 ra : Z),
  CBASE cx ->
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (B.ACtlCut.c_sp cx) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  lib.Lib.Mem.bytes_at segs mem3 (B.ACtlCut.c_sp cx - 104)
    (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 27) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 26) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 25) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 24) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 23) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 22) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 21) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 20) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 19) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 18) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 9) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 8) ++
     lib.Lib.Mem.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF)) ->
  B.ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 448 <= B.ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81764);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81aa0);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81f50);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82d1c)] ->
  exists ch, B.ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ B.ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   3. a Theorem Labs lane's `_F` runs: cited from their modules (Required above), never restated (porter 23:38Z: the stage files
   may Require the `_F` files and their closure, qualified; copying the texts is unnecessary).  All of R6F .. R14F are
   landed and proved, each checked against the stage plans below by its .v line: R6F (r6_evt_pre_F / r6_evt_post_F),
   R7F (r7_evt_F, r7_evt0_F), R8F (r8_evt_pre_F / r8_evt_post_F), R9F (r9_st_F, r9_call_pre_F / r9_call_post_F) and
   R10F (the five head runs and the three call pre / post pairs) at a working branch e055327a537;
   R11F (r11_pre_F / r11_post_F), R12F (r12_pre_F / r12_post_F), R13F (r13_evt_F) and R14F (r14_pre_F / r14_post_F)
   at a working branch efac84ed592. *)

(* ---------------------------------------------------------------------------------------------------------
   3b. Generic stage helpers: the image's segment facts, the lift of a footprint run from a cut's state, the journal
   across a run that writes nothing.  They use FEVT and LAWS only (and ProgBridge's proved lemmas). *)

(* The image's loaded segments end below the low-memory end (ProgBridge.rsegs_spans: the image hull). *)
Lemma w2_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Ha).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin) as Hm.
  change Reusable.YB1v.tfibsegs with B.Img0.rsegs in Hm. rewrite B.ProgBridge.rsegs_spans in Hm.
  unfold Reusable.YG0f.kLowMemEnd.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

(* No writable-executable segment wraps (the kit's once-per-unit fact, computed). *)
Lemma w2_wx : Reusable.YK04.wx_segs_nowrap segs.
Proof. apply Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The lift of a footprint run from a cut's state: cfg_at is lib/Lib's MS state (ProgBridge.cfg_at_MS), its register
   map moves to the canonical mkR_of form (Regs6ss.mkR_of_eqv), FEVT turns the evtF run into kit fsteps, and
   YA0nR.SRr_fevt_hid lifts it, keeping the hidden bytes for the journal. *)
Lemma w2_lift : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md (pc : Z)
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
  apply (Reusable.YA0nR.SRr_fevt_hid segs w2_wx W _ md RNG P Q (FEVT RNG P _ Hrun) Hav).
  intros ms' md' HP Hhid Hsbm. apply (K ms' md' HP); [| exact Hsbm].
  intros x Hx. rewrite (Hhid x Hx). reflexivity.
Qed.

(* Back from a run's end state (lib/Lib's MS, PropExec.seg_rom) to the cut form cfg_at (the same record). *)
Lemma w2_cfg_back : forall (W : Reusable.YA0n.world segs) (R : bvmap 5 word) (pc : Z) (mem : word -> option byte) md
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R mem md) Q ->
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md) Q.
Proof. intros W R pc mem md Q H. exact H. Qed.

(* The journal across a run that writes nothing: only the model is materialized (YCbq.ajournal_exec, empty write
   set). *)
Lemma w2_journal_mat : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 md'
           (fun _ => False) HJ).
  - intros x _. reflexivity.
  - intros x Hx. exact Hx.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* A register pin moves to a register map with the same value in that register. *)
Lemma w2_rgv_move : forall (R regs : bvmap 5 word) (r : bv 5) (v : Z),
  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs r -> B.ACtlCut.rgv regs r v -> B.ACtlCut.rgv R r v.
Proof. intros R regs r v E H. unfold B.ACtlCut.rgv in *. rewrite E. exact H. Qed.

(* FRAC reads the registers 2, 3, 4, 8, 9, 19 and 26 only. *)
Lemma w2_frac_regs : forall (cx : ctlcx) (fr sel : Z) (regs R : bvmap 5 word) (m : word -> option byte),
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs 26 ->
  B.ACtlCutP.FRAC B cx fr sel regs m -> B.ACtlCutP.FRAC B cx fr sel R m.
Proof.
  intros cx fr sel regs R m E2 E3 E4 E8 E9 E19 E26 H.
  unfold B.ACtlCutP.FRAC, B.ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

(* RBE reads the registers only through its spills' base, register 9. *)
Lemma w2_rbe_regs : forall (cx : ctlcx) (fr : Z) (regs R : bvmap 5 word) (m : word -> option byte),
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  B.ACtlCutP.RBE cx fr regs m -> B.ACtlCutP.RBE cx fr R m.
Proof.
  intros cx fr regs R m E9 H.
  unfold B.ACtlCutP.RBE, B.ACtlCutP.PRA, B.ACtlCutP.spill, B.ACtlCut.rgv in *. rewrite E9. exact H.
Qed.

(* CUR reads the registers 23 and 25 only. *)
Lemma w2_cur_regs : forall (cx : ctlcx) (c : Z) (regs R : bvmap 5 word),
  lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs 25 ->
  B.ACtlCutP.CUR cx c regs -> B.ACtlCutP.CUR cx c R.
Proof.
  intros cx c regs R E23 E25 H. unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in *. rewrite E23, E25. exact H.
Qed.

(* A pinned register's unsigned value is the pin, when the pin is in [0, 2^64). *)
Lemma w2_rgv_unsigned : forall (regs : bvmap 5 word) (r : bv 5) (v : Z),
  B.ACtlCut.rgv regs r v -> 0 <= v < 2 ^ 64 -> bv_unsigned (lib.Reusable.YK11.getr regs r) = v.
Proof.
  intros regs r v H Hv. unfold B.ACtlCut.rgv in H. rewrite H, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

(* Two pins of one register in [0, 2^64) are equal. *)
Lemma w2_rgv_eq : forall (regs : bvmap 5 word) (r : bv 5) (x y : Z),
  B.ACtlCut.rgv regs r x -> B.ACtlCut.rgv regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros regs r x y Hx Hy Hxr Hyr.
  rewrite <- (w2_rgv_unsigned regs r x Hx Hxr), <- (w2_rgv_unsigned regs r y Hy Hyr). reflexivity.
Qed.

(* The stack pointer read as a Z lies in [0, 2^64). *)
Lemma w2_spZ_range : forall regs : bvmap 5 word, 0 <= Reusable.YG0d.spZ regs < 2 ^ 64.
Proof.
  intros regs. unfold Reusable.YG0d.spZ.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* V1: every byte of the journal's stack window [c_sp - LLVMF_STK, c_sp) is visible (the journal's apresent clause,
   YCbq.v:368), and the window lies in [alloc_ceiling, 2^47] (astk_ok, YCbq.v:333-335). *)
Lemma w2_vis_stack : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (lo len : Z),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> 0 <= len -> lo + len <= B.ACtlCut.c_sp cx ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo len HJ Hlo Hlen Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hlo' & Hhi' & H47 & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hc _]. unfold Reusable.YG0f.ASAN_CEIL in Hc.
  split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (Hwin a ltac:(lia))).
Qed.

(* ctl_rt_C at any journal state of a cut (route C): the proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR at the journal's AR
   (its first conjunct), with arodata_okP there from ctl_base's arodata_okS (tfib_lib_pre_x's eleventh conjunct,
   YCfn.v:40) by ProgWorld.arodata_okP_of_S and APostBase.arodata_ok_journalP. *)
Lemma w2_ctl_rt : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k,
  CBASE cx -> AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
  pose proof HJ as (HAR & _).
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 HAR).
  apply (lib.Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  exact (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS ltac:(lia) ltac:(lia)).
Qed.

(* The core's read-only view fact (YE01.arodata_okS, the parse spec's premise) at any journal state of a cut: the PA
   form arodata_okP there (as in w2_ctl_rt) is the same statement with in_roP unfolded. *)
Lemma w2_arodataS : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k,
  CBASE cx -> AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
  pose proof (lib.Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
                (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS ltac:(lia) ltac:(lia))) as HP.
  exact HP.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3c. Memory across a world step: a cut fact survives when the raw reads of the bytes it names are kept.  The kept
   ranges come from the step's post: ctl_post_acall_kept's kept classes after the allocator, munch_vis after a runtime
   call, ctl_rt's ro_agree on both sides for read-only image bytes. *)

Local Notation KEEPR m m' lo hi :=
  (forall a : Z, lo <= a < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)).

Lemma w2_bytes_keep : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  KEEPR m m' a (a + Z.of_nat (length bs)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H2). split; [exact H0 |]. split; [exact H1 |].
  intros i Hi. unfold lib.Lib.Mem.wa. rewrite K by lia. exact (H2 i Hi).
Qed.

Lemma w2_addr_keep : forall (m m' : word -> option byte) (p n : Z),
  (forall i, 0 <= i < n ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H3). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |]. exists b. split; [| exact Hok].
  unfold lib.Lib.Mem.wa in *. rewrite (K i Hi). exact Hb.
Qed.

(* A spill of the cut's spill base A (register 9) survives when [A, A + 448) is kept. *)
Lemma w2_spill_keep : forall (regs : bvmap 5 word) (m m' : word -> option byte) (A off v : Z),
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  KEEPR m m' A (A + 448) -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill regs m' off v.
Proof.
  intros regs m m' A off v H9 HA0 HA1 Ho0 Ho1 K (A' & H9' & Hq). exists A'. split; [exact H9' |].
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
  assert (EA : A' = A).
  { unfold B.ACtlCut.rgv in H9, H9'. rewrite H9 in H9'.
    apply (f_equal bv_unsigned) in H9'. rewrite !Z_to_bv_unsigned in H9'. unfold bv_wrap in H9'.
    change (bv_modulus 64) with (2 ^ 64) in H9'. rewrite (Z.mod_small A) in H9' by lia.
    pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)). pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. eapply w2_bytes_keep; [| exact Hq]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply K. lia.
Qed.

(* A spill read at the spill base A itself (the spill's own base is A modulo 2^64, and both lie below 2^64 - 448). *)
Lemma w2_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  B.ACtlCutP.spill regs m off v -> B.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA1 Ho0 Ho1 (A' & H9' & Hq).
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
  assert (EA : A' = A).
  { unfold B.ACtlCut.rgv in H9, H9'. rewrite H9 in H9'.
    apply (f_equal bv_unsigned) in H9'. rewrite !Z_to_bv_unsigned in H9'. unfold bv_wrap in H9'.
    change (bv_modulus 64) with (2 ^ 64) in H9'. rewrite (Z.mod_small A) in H9' by lia.
    pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)). pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

(* A present byte is read by the view. *)
Lemma w2_aview_of_apresent : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.apresent H mem a -> Reusable.YG0n.aview segs H mem a <> None.
Proof.
  intros H mem a (Hh & b & Hb). unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
  cbv beta. rewrite Hh, Hb. discriminate.
Qed.

(* A byte whose signed value is in [0, 127] reads the same unsigned. *)
Lemma w2_unsigned_of_signed : forall b : bv 8, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr. revert Hb.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256 in *.
  intros Hb. lia.
Qed.

(* ctrl's raw addressability of a range whose shadow bytes are visible is the core's view-level range_addressable. *)
Lemma w2_range_addr_of_raw : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (p n : Z),
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W mem p n (H0 & H1 & H2 & H3) Hv x Hx.
  assert (Ex : p + (x - p) = x) by lia.
  destruct (H3 (x - p) ltac:(lia)) as (_ & b & Hb & Hok). rewrite Ex in Hb, Hok.
  pose proof (Hv (x - p) ltac:(lia)) as Hvx. rewrite Ex in Hvx.
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  unfold B.AsanRT.shadow_ok in Hok.
  exists (bv_signed b). split.
  - rewrite Es, (aview_vis_mrd W mem _ Hvx). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. cbn [option_map].
    f_equal. apply w2_unsigned_of_signed. lia.
  - unfold Reusable.YG0v.saddr_ok. lia.
Qed.

(* The raw reads that munch_vis keeps, over a whole range of visible bytes outside its write set. *)
Lemma w2_munch_keep : forall (H : word -> bool) (WR : list (Z * Z)) (m m' : word -> option byte) (lo hi : Z),
  munch_vis H WR m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> H (Z_to_bv 64 a) = false /\ lib.Lib.Frame.outside WR a) ->
  KEEPR m m' lo hi.
Proof.
  intros H WR m m' lo hi MV Hlo Hhi K a Ha. destruct (K a Ha) as [Hv Ho].
  apply (MV (Z_to_bv 64 a) Hv). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. exact Ho.
Qed.

(* RBE survives when its spill area, the fake frame's shadow (all but the bytes [Sfr fr + 296, Sfr fr + 318), the
   shadow of [fr + 2368, fr + 2544): the parse record and the reply / ports cells, which RBE's addressability
   conjuncts never read), the catalogue's read-only data (the build_as row table, the turn's catalogue row), the box
   bytes and the row-name bytes are kept, and the row name stays addressable. *)
Lemma w2_rbe_mem : forall (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m m' : word -> option byte) (A : Z),
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> fr mod 8 = 0 ->
  KEEPR m m' A (A + 448) ->
  (forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW ->
     ~ (B.ACtlCutP.Sfr fr + 296 <= a < B.ACtlCutP.Sfr fr + 318) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) ->
  KEEPR m m' (B.ACtlCutP.BAC.BA_FR + 72) (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl)) ->
  KEEPR m m' B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)) ->
  KEEPR m m' (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
    (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) + Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))) ->
  (B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   KEEPR m m' (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) +
      Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx)))) /\
   B.AsanRT.addressable m' (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))))) ->
  B.ACtlCutP.RBE cx fr regs m -> B.ACtlCutP.RBE cx fr regs m'.
Proof.
  intros cx fr regs m m' A H9 HA0 HA1 Hfr KA KSH KTBL KBOX KROW KNM HR.
  assert (SPK : forall off v, 0 <= off -> off + 8 <= 448 ->
                 B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill regs m' off v)
    by (intros off v Ho0 Ho1; exact (w2_spill_keep regs m m' A off v H9 HA0 HA1 Ho0 Ho1 KA)).
  assert (AK : forall X n, 0 <= X -> 0 <= n -> X + n <= B.ACtlCutP.FRAME_BYTES -> (X + n <= 2368 \/ 2544 <= X) ->
                 B.AsanRT.addressable m (fr + X) n -> B.AsanRT.addressable m' (fr + X) n).
  { intros X n HX Hn HXn HXw. apply w2_addr_keep. intros i Hi. apply KSH;
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in *; lia. }
  unfold B.ACtlCutP.RBE, B.ACtlCutP.PRA, B.ACtlCutP.OUTA in *.
  destruct HR as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 & S96 & S120 &
                  S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & H2176 & HNM & H2624 & HTBL & HBOX & HROW &
                  (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b) &
                  S152 & S112 & H2256 & S160).
  repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
  | |- B.ACtlCutP.spill _ _ _ _ => apply SPK; [lia | lia | assumption]
  | |- B.AsanRT.addressable _ (_ + _) _ =>
      apply AK; [lia | lia | unfold B.ACtlCutP.FRAME_BYTES; lia | lia | assumption]
  | |- lib.Lib.Mem.bytes_at _ _ _ _ =>
      eapply w2_bytes_keep; [| eassumption]; first [exact KTBL | exact KBOX | exact KROW]
  | |- _ -> _ =>
      intros [Hh Hr]; destruct (HNM (conj Hh Hr)) as (Hok & Hb & Ha & Hpos);
      destruct (KNM Hh Hr) as [K1 A1];
      refine (conj Hok (conj (w2_bytes_keep _ _ _ _ K1 Hb) (conj A1 Hpos)))
  end.
Qed.

(* FRAC survives when its stack reads (the spills at [A + 40, A + 344) and the saved registers at [c_sp - 104, c_sp),
   all at or above both sp and fr + FRAME_BYTES, since sp <= A and fr + FRAME_BYTES <= A), the fake frame's header
   [fr, fr + 24) and the class-6 frame's trailer word at fr + 4088 (FRAC's last conjunct, a218ac85be5) are kept and
   the new memory holds some bytes at the fake frame's shadow (FRAC names them only by length). *)
Lemma w2_frac_mem_sh : forall (cx : ctlcx) (fr sel : Z) (regs : bvmap 5 word) (m m' : word -> option byte),
  (forall a, Reusable.YG0d.spZ regs <= a < B.ACtlCut.c_sp cx -> fr + B.ACtlCutP.FRAME_BYTES <= a ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) ->
  KEEPR m m' fr (fr + 24) ->
  (exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr) sh /\
     length sh = Z.to_nat B.ACtlCutP.FRAME_SHADOW) ->
  KEEPR m m' (fr + 4088) (fr + 4088 + 8) ->
  B.ACtlCutP.FRAC B cx fr sel regs m -> B.ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' KH KF KS KT
    (A & sp & H2 & H16 & Hsp & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA & HfrA & HA448 & Hsp4 &
     Hc & Q336 & Q48 & Q40 & Qfr & Q16 & _ & Hsv & Qtr).
  exists A, sp. rewrite Hsp in KH.
  assert (Hlen : length (B.ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply w2_bytes_keep; [| exact Q336]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KH; lia.
  - eapply w2_bytes_keep; [| exact Q48]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KH; lia.
  - eapply w2_bytes_keep; [| exact Q40]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KH; lia.
  - eapply w2_bytes_keep; [| exact Qfr]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KF. lia.
  - eapply w2_bytes_keep; [| exact Q16]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KF. lia.
  - eapply w2_bytes_keep; [| exact Hsv]. intros a Ha. rewrite Hlen in Ha. apply KH; lia.
  - eapply w2_bytes_keep; [| exact Qtr]. intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha. apply KT. lia.
Qed.

(* The same with the fake frame's shadow kept too. *)
Lemma w2_frac_mem : forall (cx : ctlcx) (fr sel : Z) (regs : bvmap 5 word) (m m' : word -> option byte),
  (forall a, Reusable.YG0d.spZ regs <= a < B.ACtlCut.c_sp cx -> fr + B.ACtlCutP.FRAME_BYTES <= a ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) ->
  KEEPR m m' fr (fr + 24) ->
  KEEPR m m' (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW) ->
  KEEPR m m' (fr + 4088) (fr + 4088 + 8) ->
  B.ACtlCutP.FRAC B cx fr sel regs m -> B.ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' KH KF KS KT HF.
  apply (w2_frac_mem_sh cx fr sel regs m m' KH KF); [| exact KT | exact HF].
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    (sh & Hsh & Hshl) & _).
  exists sh. split; [| exact Hshl]. eapply w2_bytes_keep; [| exact Hsh]. intros a Ha. apply KS.
  rewrite Hshl in Ha. rewrite Z2Nat.id in Ha by (unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES; lia). lia.
Qed.

(* Two keeps in a row. *)
Lemma w2_keep_trans : forall (m1 m2 m3 : word -> option byte) (lo hi : Z),
  KEEPR m1 m2 lo hi -> KEEPR m2 m3 lo hi -> KEEPR m1 m3 lo hi.
Proof. intros m1 m2 m3 lo hi K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.

(* One kept class of ctl_post_acall_kept over a whole range. *)
Lemma w2_kept : forall (lyc : Reusable.YG0f.alayout) (Sc : Reusable.YG00.astate) (W W2 : Reusable.YA0n.world segs)
    (memc mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) (lo hi : Z),
  Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> Reusable.YA0n.wle W W2 ->
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi ->
     Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\ kept_class B lyc Sc slo shi E a) ->
  KEEPR memc mem2 lo hi.
Proof.
  intros lyc Sc W W2 memc mem2 slo shi E lo hi HK Hwle Hlo Hhi H a Ha. destruct (H a Ha) as [Hv Hc].
  apply (ctl_post_acall_kept B lyc Sc W W2 memc mem2 slo shi E HK Hwle (Z_to_bv 64 a) Hv).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact Hc.
Qed.

(* Read-only image bytes are kept between two memories that both agree with the image (ctl_rt_C's ro_agree). *)
Lemma w2_kept_ro : forall {ly S ly' S'} (m m' : word -> option byte) (lo hi : Z),
  B.ACtlRtC.ctl_rt_C B ly S m -> B.ACtlRtC.ctl_rt_C B ly' S' m' ->
  (forall a, lo <= a < hi -> lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = true) ->
  KEEPR m m' lo hi.
Proof.
  intros ly S ly' S' m m' lo hi (_ & _ & _ & R) (_ & _ & _ & R') Hro a Ha.
  unfold B.ACtlK.ro_agree_at in R, R'. rewrite (R' _ (Hro a Ha)), (R _ (Hro a Ha)). reflexivity.
Qed.

(* A byte the world view reads is visible: a hidden byte is no segment byte (w_Hoff), so its view is None. *)
Lemma w2_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Eh; [exfalso | reflexivity].
  apply Hv. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. cbv beta.
  rewrite Eh.
  cbv iota.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (Reusable.YA0n.w_Hoff W _ Eh). reflexivity.
Qed.

(* A byte value below 128 reads the same signed. *)
Lemma w2_signed_small : forall b : bv 8, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256 in *.
  rewrite Z.mod_small by lia. lia.
Qed.

(* T5 (plan 2.4), derived: a live block of the core's AR is addressable in ctrl's sense (AR_blocks_law places it in
   application memory, AR_shadow_law gives its shadow granules in the visible view, aview_vis_mrd reads them raw). *)
Lemma w2_block_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md (p n : Z),
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) -> 1 <= n ->
  B.AsanRT.addressable mem p n.
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4 & Hceil & Happ & _ & _ & Hmax).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [(Hp8 & _ & Hsh) _].
  assert (Er : Reusable.YG00.req_size n = n) by (unfold Reusable.YG00.req_size; destruct (n =? 0) eqn:E; lia).
  rewrite Er in Hceil, Happ, Hsh.
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hc _]. unfold Reusable.YG0f.ASAN_CEIL in Hc.
  split; [lia |]. split; [lia |]. split; [unfold B.AsanRT.APPMEM_END in *; lia |].
  intros i Hi. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ.
    lia.
  - assert (Hj : 0 <= i / 8 < (n + 7) / 8) by lia.
    pose proof (Hsh (i / 8) Hj) as Hv.
    assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF p + i / 8 = B.AsanRT.shadow_addr (p + i)).
    { unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K. lia. }
    rewrite Es in Hv.
    assert (Hvis : Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false)
      by (apply (w2_vis_of_aview W mem); rewrite Hv; discriminate).
    rewrite (aview_vis_mrd W mem _ Hvis) in Hv.
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) as [bb |] eqn:Eb;
      [| discriminate Hv].
    cbn [option_map] in Hv. injection Hv as Hv. exists bb. split; [exact Eb |].
    assert (Hs : bv_signed bb = bv_unsigned bb).
    { apply w2_signed_small. rewrite Hv. destruct (i / 8 <? n / 8); [lia |].
      pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
    unfold B.AsanRT.shadow_ok. rewrite Hs, Hv.
    destruct (i / 8 <? n / 8) eqn:Ej; [left; reflexivity | right].
    apply Z.ltb_ge in Ej. lia.
Qed.

(* The image hull is tiled by the segments (computed), so every hull address is a segment byte. *)
Lemma w2_img_tiles : Reusable.YG0n.tiles_b
  (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs)
  Reusable.YImgTop.IMG_LO Reusable.YImgTop.IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w2_in_img : forall a, Reusable.YImgTop.IMG_LO <= a < Reusable.YImgTop.IMG_TOP -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (H0 : 0 <= Reusable.YImgTop.IMG_LO) by lia.
  destruct (Reusable.YG0n.tiles_b_cover _ _ _ a H0 w2_img_tiles Ha) as (e & He & Hr & _).
  apply in_map_iff in He as (s & <- & Hs). exists s. split; [exact Hs | exact Hr].
Qed.

(* The box bytes are read-only image bytes (computed). *)
Lemma w2_box_ro_b : forallb (fun j => lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 (B.ACtlCutP.SM.BOXA + Z.of_nat j)))
  (seq 0 (length B.ACtlCutP.SM.box6)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w2_box_ro : forall a,
  B.ACtlCutP.SM.BOXA <= a < B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6) ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = true.
Proof.
  intros a Ha.
  assert (Hin : In (Z.to_nat (a - B.ACtlCutP.SM.BOXA)) (seq 0 (length B.ACtlCutP.SM.box6))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) w2_box_ro_b _ Hin) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia.
  replace (B.ACtlCutP.SM.BOXA + (a - B.ACtlCutP.SM.BOXA)) with a in H by lia. exact H.
Qed.

(* Every catalogue row's name bytes (when the row has a name) are read-only image bytes (computed over the
   catalogue's rows). *)
Lemma w2_names_ro_b : forallb (fun i =>
    (B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rowb (Z.of_nat i)) =? 0) ||
    (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rowb (Z.of_nat i)) =? 0) ||
    forallb (fun j => lib.Lib.Mem.ro_addr B.Img0.rsegs
                        (Z_to_bv 64 (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rowb (Z.of_nat i)) + Z.of_nat j)))
      (seq 0 (length (B.ACtlCutP.SM.img_cstr (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rowb (Z.of_nat i))) 16))))
  (seq 0 (Z.to_nat B.ACtlCutP.SM.CAT_N)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w2_names_ro : forall inp : list byte,
  B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb inp) <> 0 -> B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <> 0 ->
  forall a, B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <= a <
            B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) + Z.of_nat (length (B.ACtlCutP.SM.rt_nb inp)) ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = true.
Proof.
  intros inp Hh Hr a Ha.
  assert (Hi : 0 <= B.ACtlCutP.SM.istar inp < B.ACtlCutP.SM.CAT_N)
    by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
  assert (Hin : In (Z.to_nat (B.ACtlCutP.SM.istar inp)) (seq 0 (Z.to_nat B.ACtlCutP.SM.CAT_N)))
    by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) w2_names_ro_b _ Hin) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia.
  unfold B.ACtlCutP.SM.rt_nb, B.ACtlCutP.SM.rt_mb in *.
  apply Bool.orb_true_iff in H as [H | H];
    [apply Bool.orb_true_iff in H as [H | H]; apply Z.eqb_eq in H; contradiction |].
  set (rn := B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rowb (B.ACtlCutP.SM.istar inp))) in *.
  assert (Hin2 : In (Z.to_nat (a - rn))
                   (seq 0 (length (B.ACtlCutP.SM.img_cstr rn 16)))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) H _ Hin2) as H2.
  cbv beta in H2. rewrite Z2Nat.id in H2 by lia.
  replace (rn + (a - rn)) with a in H2 by lia.
  exact H2.
Qed.

(* A callee-saved register kept by a call keeps its value. *)
Lemma w2_pres_reg : forall (R R2 regs : bvmap 5 word) (z : Z) (r : bv 5),
  Reusable.YG0d.aregs_preserved R R2 -> Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs r ->
  lib.Reusable.YK11.getr R2 r = lib.Reusable.YK11.getr regs r.
Proof. intros R R2 regs z r HP Hz Er E. rewrite <- E. subst r. exact (HP z Hz). Qed.

(* A prefix of an addressable range is addressable. *)
Lemma w2_addr_prefix : forall (m : word -> option byte) (p n n' : Z),
  B.AsanRT.addressable m p n -> 0 <= n' <= n -> B.AsanRT.addressable m p n'.
Proof.
  intros m p n n' (H0 & H1 & H2 & H3) Hn. split; [exact H0 |]. split; [lia |]. split; [lia |].
  intros i Hi. apply H3. lia.
Qed.

(* Everything an own6 cut body reads that an allocator call keeps (ctl_post_acall_kept over acall_kept, the kept
   classes: the stack above the call's sp, the class-6 frame's bytes off E and its shadow (off E), the catalogue's
   read-only data by ctl_relro_not_owned), the read-only image bytes by ro_agree on both sides, the row name's
   addressability by ctl_names_addressable, and ctl_rt after the call by w2_ctl_rt at the call's post journal. *)
Lemma w2_acall_keeps : forall (cx : ctlcx) (fr k sp : Z) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3
    ly2 S2 (W2 : Reusable.YA0n.world segs) mem2 md2 own2 (k2 slo shi : Z) (E : Z -> Prop),
  CBASE cx ->
  AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  0 <= sp -> B.ACtlCut.c_sp cx - 4096 < sp -> shi <= sp ->
  Reusable.YCbq.acall_kept segs B ly3 S3 W3 mem3 W2 mem2 slo shi E -> Reusable.YA0n.wle W3 W2 ->
  AJ cx own2 ly2 S2 W2 mem2 md2 k2 ->
  (forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW -> ~ E a) ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  KEEPR mem3 mem2 sp (B.ACtlCut.c_sp cx) /\
  (forall a, fr <= a < fr + Reusable.YG00.fs_frame_bytes 6 -> ~ E a ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a)) /\
  KEEPR mem3 mem2 (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW) /\
  KEEPR mem3 mem2 (B.ACtlCutP.BAC.BA_FR + 72) (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl)) /\
  KEEPR mem3 mem2 (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
    (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) + Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))) /\
  KEEPR mem3 mem2 B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)) /\
  (B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   KEEPR mem3 mem2 (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) +
      Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx)))) /\
   B.AsanRT.addressable mem2 (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))))) /\
  B.ACtlRtC.ctl_rt_C B ly2 S2 mem2.
Proof.
  intros cx fr k sp ly3 S3 W3 mem3 md3 ly2 S2 W2 mem2 md2 own2 k2 slo shi E HB HJ Hfrs Hfr6 Hsp0 Hsp4 Hshi HK Hwle
    HJ2 HEs HRT.
  pose proof HJ2 as (HAR2 & _).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happ3 & Hfb3 & Hfs3).
  rewrite Hfa3, <- Hfr6, Hfsb in Happ3, Hfb3, Hfs3.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happ3.
  assert (HRT2 : B.ACtlRtC.ctl_rt_C B ly2 S2 mem2) by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ2).
  destruct (img_vis_W W3) as (_ & _ & VI).
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ sp (B.ACtlCut.c_sp cx) HK Hwle); [lia | lia |].
    intros a Ha. split.
    + exact (proj1 (Hwin a ltac:(lia))).
    + left. lia.
  - rewrite Hfsb. intros a Ha HEa.
    apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ a (a + 1) HK Hwle); [lia | lia | | lia].
    intros a' Ha'. replace a' with a by lia. split.
    + exact (proj1 (proj1 (Hfb3 a ltac:(lia)))).
    + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split.
      * left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd].
        rewrite Hfa3, <- Hfr6, Hfsb. lia.
      * exact HEa.
  - apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle);
      [unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia |
       unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
         B.ACtlCutP.FRAME_BYTES; lia |].
    intros a Ha. pose proof (HEs a Ha) as HEa.
    unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
      B.ACtlCutP.FRAME_BYTES in Ha.
    split.
    + assert (Hi : 0 <= a - Reusable.YG0f.shadow_addr fr < 4096 / 8)
        by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia).
      pose proof (proj1 (proj1 (Hfs3 _ Hi))) as V.
      replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in V by lia.
      exact V.
    + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split.
      * right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
      * exact HEa.
  - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht.
    apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle);
      [unfold B.ACtlCutP.BAC.BA_FR; lia | rewrite Ht; unfold B.ACtlCutP.BAC.BA_FR; lia |].
    intros a Ha. destruct (ctl_relro_not_owned a (or_introl Ha)) as [Hno Hne].
    rewrite Ht in Ha. unfold B.ACtlCutP.BAC.BA_FR in Ha. split.
    + apply VI. lia.
    + right; right; left. split; [apply w2_in_img; lia | split; assumption].
  - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
      by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
    rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
    unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
    apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle); [lia | lia |].
    intros a Ha.
    destruct (ctl_relro_not_owned a) as [Hno Hne].
    { right. unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N. lia. }
    split.
    + apply VI. lia.
    + right; right; left. split; [apply w2_in_img; lia | split; assumption].
  - exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 w2_box_ro).
  - intros Hh Hr. split.
    + exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 (w2_names_ro _ Hh Hr)).
    + exact (ctl_names_addressable _ _ _ _ _ _ HAR2 Hh Hr).
  - exact HRT2.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3d. The ingest call (S_R11, S_R12).  reac_identity_ingest (image B 0x87e0c) is leaf code: no runtime call, and
   its ASan checks read only the shadow and the two runtime cells in the image.  So its closed footprint contract
   (lib/B/Prog/reac_identity_ingestF.v reac_identity_ingest_F_holds_on, the premise-free route-C twin) runs under
   RNG_W when every byte it touches is visible; its post is a raw munch over the callee window and the identity record,
   which the journal follows by ajournal_exec and ctl_rt_C by w2_ctl_rt.  The byte / cell helpers are
   lib/B/Prog/Seg/R11.v:49-99's, restated over
   the qualified lib/Lib names (R11.v is not Required). *)

Lemma w2_ro8 : forall (m : word -> option byte) (a : Z) (v : word),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 v) ->
  lib.Lib.Step.ro_cells B.Img0.rsegs m a [lib.Lib.Cells.C8 v].
Proof.
  intros m a v H. split; [exact (conj I I) |].
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma w2_ro2 : forall (m : word -> option byte) (a : Z) (v : word),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le2 v) ->
  lib.Lib.Step.ro_cells B.Img0.rsegs m a [lib.Lib.Cells.C2 v].
Proof.
  intros m a v H. split; [exact (conj I I) |].
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma w2_rw_CB : forall (m : word -> option byte) (A : Z) (l : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m A l -> lib.Lib.Mem.wr_at B.Img0.rsegs m A (Z.of_nat (length l)) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m A [lib.Lib.Cells.CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split |].
  - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [reflexivity | exact I].
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma w2_cells_bytes : forall (m : word -> option byte) (a : Z) (n : nat) (bs : list byte),
  lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs] -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros m a n bs ((_ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
  rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma w2_ba_rd : forall (m : word -> option byte) (A : Z) (bs : list byte) (x : Z),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b |] eqn:En; [exists b; exact E |].
  apply nth_error_None in En. lia.
Qed.

Lemma w2_out_dec : forall (W : list lib.Lib.Frame.ivl) (x : Z), lib.Lib.Frame.outside W x \/ ~ lib.Lib.Frame.outside W x.
Proof.
  induction W as [| [lo hi] W IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I |].
  destruct (IH x) as [H | H]; [| right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1 | H1]; [left; split; [lia | exact H] |].
  destruct (Z_lt_le_dec x hi) as [H2 | H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* A raw byte the machine has is a writable-view byte. *)
Lemma w2_wview_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> wview B.Img0.rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

(* Off the image, a byte mrd reads is a raw byte (the segments' rom is empty there). *)
Lemma w2_mrd_raw : forall (m : word -> option byte) (a : Z) (b : byte),
  0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a) = Some b -> m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a b Ha Hn H. unfold lib.Lib.Mem.mrd in H. destruct (m (Z_to_bv 64 a)) as [b' |] eqn:E; [exact H |].
  assert (Hs : lib.Lib.PropExec.seg_rom B.Img0.rsegs (Z_to_bv 64 a) = None)
    by exact (Reusable.YCbq.seg_rom_none segs a Ha Hn).
  rewrite Hs in H. discriminate.
Qed.

(* A raw munch keeps the reads of every byte outside its interval list. *)
Lemma w2_munch_keepr : forall (W : list lib.Lib.Frame.ivl) (m m' : word -> option byte) (lo hi : Z),
  lib.Lib.Frame.munch W m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> lib.Lib.Frame.outside W a) -> KEEPR m m' lo hi.
Proof.
  intros W m m' lo hi MU Hlo Hhi K a Ha. unfold lib.Lib.Mem.mrd. rewrite (MU (Z_to_bv 64 a)); [reflexivity |].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact (K a Ha).
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma w2_addr_sub : forall (m : word -> option byte) (p n o n' : Z),
  B.AsanRT.addressable m p n -> 0 <= o -> 0 <= n' -> o + n' <= n -> B.AsanRT.addressable m (p + o) n'.
Proof.
  intros m p n o n' (H0 & H1 & H2 & H3) Ho Hn' Hon. split; [lia |]. split; [lia |]. split; [lia |].
  intros i Hi. replace (p + o + i) with (p + (o + i)) by lia. apply H3. lia.
Qed.

(* The bytes [k, k + n) of a frame's first 50 (fr50 pads past the end), when the frame has 50 bytes. *)
Lemma w2_bsl_fr50 : forall (F P : list byte) (k n : nat),
  (50 <= length F)%nat -> (k + n <= 50)%nat ->
  firstn n (skipn k (firstn 50 (F ++ P))) = firstn n (skipn k F).
Proof.
  intros F P k n HF Hkn. rewrite firstn_app. replace (50 - length F)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

(* The ingest call from its entry to its return at 0x81860, not refused (record and payload present). *)
Lemma w2_ingest_F : forall (RNG : lib.Lib.ExecF.footprint)
    (sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv id ad p len lo : Z) (idb pb : list byte),
  sp = Z_to_bv 64 spv -> 0 <= spv < 2 ^ 64 ->
  0 < id < 2 ^ 64 -> id mod 2 = 0 -> 0 < p < 2 ^ 64 -> 0 < len < 2 ^ 64 -> 0 <= ad < 65536 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m id idb -> length idb = 38%nat -> lib.Lib.Mem.wr_at B.Img0.rsegs m id 38 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m p pb -> length pb = Z.to_nat len ->
  (p + len <= id \/ id + 38 <= p) ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo spv -> lo + 32 <= spv ->
  (id + 38 <= spv - 32 \/ spv <= id) -> (p + len <= spv - 32 \/ spv <= p) ->
  B.AsanRT.asan_cells m ->
  B.AsanRT.addressable m id 38 -> B.AsanRT.addressable m p len ->
  (forall x, B.AsanRT.GOT_CELL_K <= x < B.AsanRT.GOT_CELL_K + 8 \/ B.AsanRT.CELL_K <= x < B.AsanRT.CELL_K + 8 \/
     B.AsanRT.in_shadow x -> lib.Lib.Frame.outside [(spv - 32, spv); (id, id + 38)] x) ->
  lib.Lib.ExecF.rng RNG (spv - 32) 32 -> lib.Lib.ExecF.rng RNG B.AsanRT.GOT_CELL_K 8 ->
  lib.Lib.ExecF.rng RNG B.AsanRT.CELL_K 8 -> lib.Lib.ExecF.rng RNG id 38 ->
  lib.Lib.ExecF.rng RNG (id / 8 + B.AsanRT.ASAN_K) ((id + 37) / 8 - id / 8 + 1) ->
  lib.Lib.ExecF.rng RNG p len ->
  lib.Lib.ExecF.rng RNG (p / 8 + B.AsanRT.ASAN_K) ((p + len - 1) / 8 - p / 8 + 1) ->
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms' = lib.Lib.MState.MS R F (Z_to_bv 64 0x81860) fc None m' (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
       lib.Reusable.YK11.getr R 2 = sp /\ lib.Reusable.YK11.getr R 3 = gp /\ lib.Reusable.YK11.getr R 4 = tp /\
       lib.Reusable.YK11.getr R 8 = s0 /\ lib.Reusable.YK11.getr R 9 = s1 /\
       lib.Reusable.YK11.getr R 18 = s2 /\ lib.Reusable.YK11.getr R 19 = s3 /\
       lib.Reusable.YK11.getr R 20 = s4 /\ lib.Reusable.YK11.getr R 21 = s5 /\
       lib.Reusable.YK11.getr R 22 = s6 /\ lib.Reusable.YK11.getr R 23 = s7 /\
       lib.Reusable.YK11.getr R 24 = s8 /\ lib.Reusable.YK11.getr R 25 = s9 /\
       lib.Reusable.YK11.getr R 26 = s10 /\ lib.Reusable.YK11.getr R 27 = s11 /\
       lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (fst (B.ACtlCutP.RIM.ING idb ad pb)) /\
       lib.Lib.Frame.munch [(spv - 32, spv); (id, id + 38)] m m' /\ lib.Lib.Frame.wmono B.Img0.rsegs m m' /\
       lib.Lib.Frame.stk B.Img0.rsegs m' lo spv /\
       lib.Lib.Step.rw_cells B.Img0.rsegs m' id [lib.Lib.Cells.CB 38 (snd (B.ACtlCutP.RIM.ING idb ad pb))])
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x81860) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 id)
        (Z_to_bv 64 ad) (Z_to_bv 64 p) (Z_to_bv 64 len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST) fc None m
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv id ad p len
    lo idb pb Esp Hspv Hid Hid2 Hp Hlen Had Hidb Hidl Hidw Hpb Hpbl Hpid ST HLO Hidsp Hpsp HAC ADid ADp Hcells
    G1 G2 G3 G4 G5 G6 G7.
  assert (Esp' : bv_unsigned sp = spv) by (rewrite Esp; apply lib.Lib.MState.unsigned_lit; exact Hspv).
  assert (Hrf : B.Prog.reac_identity_ingest_c.ingest_refused id p len = false).
  { unfold B.Prog.reac_identity_ingest_c.ingest_refused.
    rewrite (proj2 (Z.eqb_neq id 0)) by lia. rewrite (proj2 (Z.eqb_neq p 0)) by lia.
    rewrite andb_false_r. reflexivity. }
  eapply lib.Lib.ExecF.evtF_cut.
  { apply (B.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on RNG (Z_to_bv 64 0x81860) sp gp tp t0 t1 t2
             s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 ad) (Z_to_bv 64 p) (Z_to_bv 64 len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc m lo id ad p len idb pb).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Had.
    - lia.
    - lia.
    - intros _. split; [exact Hid2 |]. rewrite <- Hidl. apply w2_rw_CB; [exact Hidb | rewrite Hidl; exact Hidw].
    - exact Hpbl.
    - intros _ _. exact Hpb.
    - intros _ _ _. exact Hpid.
    - rewrite Esp'. exact ST.
    - unfold B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. rewrite Esp'. lia.
    - intros _. unfold B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. rewrite Esp'. lia.
    - intros _ _. unfold B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. rewrite Esp'. lia.
    - exact HAC.
    - intros _. exact ADid.
    - intros _ _. exact ADp.
    - unfold B.Prog.reac_identity_ingest_c.reac_identity_ingest_W,
        B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME.
      rewrite Esp'. exact Hcells.
    - unfold B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. rewrite Esp'. exact G1.
    - exact G2.
    - exact G3.
    - intros _. split; [exact G4 | exact G5].
    - intros _ _. split; [exact G6 | exact G7]. }
  intros ms' PO. unfold B.Prog.reac_identity_ingest_c.reac_identity_ingest_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & _ & STc & _ & Hnref).
  subst ms'.
  unfold B.Prog.reac_identity_ingest_c.reac_identity_ingest_W,
    B.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in MU.
  rewrite Esp' in MU, STc.
  pose proof (Hnref Hrf) as RWc.
  unfold B.Prog.reac_identity_ingest_c.ingest_ret. rewrite Hrf.
  replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x81860)) with (Z_to_bv 64 0x81860)
    by (symmetry; apply lib.Lib.MState.ret_pc_even; [lia | reflexivity]).
  apply lib.Lib.ExecF.evtF_done. do 2 eexists. split; [reflexivity |].
  repeat (split; [reflexivity |]).
  split; [exact MU |]. split; [exact WM |]. split; [exact STc | exact RWc].
Qed.

(* The reply payload r_pl of a frame's first 50 bytes is the slice [38, 38 + len) of the frame itself. *)
Lemma w2_r_pl : forall (inp : list byte) (b : Z),
  (50 <= length (B.ACtlCutP.SM.rt_F inp b))%nat ->
  14 <= B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g inp b) <= 23 ->
  B.ACtlCutP.SM.r_pl (B.ACtlCutP.SM.rt_g inp b) =
  firstn (Z.to_nat (B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g inp b) - 13)) (skipn 38 (B.ACtlCutP.SM.rt_F inp b)).
Proof.
  intros inp b H1 H2. unfold B.ACtlCutP.SM.r_pl, B.ACtlCutP.SM.r_pll, B.ACtlCutP.RFR.bsl.
  change (Z.to_nat 38) with 38%nat. unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50 in *.
  apply w2_bsl_fr50; [exact H1 | lia].
Qed.

(* Outside the ingest's write set: off the callee window and off the identity record. *)
Lemma w2_out_W : forall (fr sp x : Z),
  (x < sp - 32 \/ sp <= x) -> (x < fr + 2176 \/ fr + 2176 + 38 <= x) ->
  lib.Lib.Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x.
Proof. intros fr sp x H1 H2. cbn [lib.Lib.Frame.outside]. repeat split; lia. Qed.

Lemma w2_W_cases : forall (fr sp x : Z),
  lib.Lib.Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x \/
  (sp - 32 <= x < sp) \/ (fr + 2176 <= x < fr + 2176 + 38).
Proof.
  intros fr sp x.
  destruct (Z_lt_le_dec x (sp - 32)) as [H1 | H1];
    [| destruct (Z_lt_le_dec x sp) as [H2 | H2]; [right; left; lia |]];
    (destruct (Z_lt_le_dec x (fr + 2176)) as [H3 | H3];
     [left; apply w2_out_W; lia
     | destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [H4 | H4];
       [right; right; lia | left; apply w2_out_W; lia]]).
Qed.

(* One byte a raw munch keeps. *)
Lemma w2_munch_mrd : forall (W : list lib.Lib.Frame.ivl) (m m' : word -> option byte) (a : Z),
  lib.Lib.Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside W a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a).
Proof.
  intros W m m' a MU Ha Ho.
  apply (w2_munch_keepr W m m' a (a + 1) MU); [lia | lia | intros x Hx; replace x with a by lia; exact Ho | lia].
Qed.

(* The shadow byte of an application byte is a shadow byte. *)
Lemma w2_shadow_of_app : forall a, B.AsanRT.app_mem a -> B.AsanRT.in_shadow (B.AsanRT.shadow_addr a).
Proof.
  intros a Ha.
  unfold B.AsanRT.app_mem, B.AsanRT.in_shadow, B.AsanRT.shadow_addr, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
    B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END, B.AsanRT.ASAN_K in *.
  lia.
Qed.

(* Where an own6 cut's class-6 frame and its stack lie, and what of them is visible (AR at the cut state: al_frames,
   frames_bounds, al_client_img; the journal's stack window and astk_ok). *)
Lemma w2_frame_loc : forall (cx : ctlcx) (fr k sp : Z) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  B.ACtlCut.c_sp cx - 4096 < sp <= B.ACtlCut.c_sp cx ->
  4096 <= fr /\ fr + 4096 <= sp - 32 /\ lib.Reusable.YM05.alloc_ceiling <= sp - 32 /\
  0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling /\ B.ACtlCut.c_sp cx <= 2 ^ 47 /\
  ((fr + 4096 <= 0x7fff8000) \/ (0x10007fff8000 <= fr)) /\
  (forall a, fr <= a < fr + 4096 -> ~ Reusable.YG0d.in_img segs a) /\
  (forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) /\
  (forall a, Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) /\
  (forall a, sp - 32 <= a < B.ACtlCut.c_sp cx -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 Hsp.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (Hc16 & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happ3 & Hfb3 & Hfs3).
  rewrite Hfa3, <- Hfr6, Hfsb in Happ3, Hfb3, Hfs3.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (Hf4096 & Hfc & _).
  rewrite Hfa3, <- Hfr6 in Hf4096. rewrite Hfa3, <- Hfr6, Hfsb in Hfc.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL,
    Reusable.YG0f.kLowMemEnd in Happ3.
  pose proof (Reusable.YG0d.al_client_img segs B LAWS ly3 S3 W3 mem3 md3) as Hcli.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  split.
  { intros a Ha Hia.
    assert (Hxr : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) <= a <
                  Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6)
      by (rewrite Hfa3, <- Hfr6, Hfsb; lia).
    exact (proj2 (Hcli a HAR3 (or_intror (or_introl (ex_intro _ 6 (ex_intro _ (B.ACtlCut.c_fpos cx)
                                                                         (conj Hin6 Hxr)))))) Hia). }
  split.
  { intros a Ha. exact (proj1 (Hfb3 a Ha)). }
  split.
  { intros a Ha. assert (Hi : 0 <= a - Reusable.YG0f.shadow_addr fr < 4096 / 8) by lia.
    pose proof (proj1 (Hfs3 _ Hi)) as V.
    replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in V by lia. exact V. }
  { intros a Ha. exact (Hwin a ltac:(lia)). }
Qed.

(* After the ingest call (S_R11, S_R12): from the post at 0x81860 (the callee-saved registers kept, a0 = 1, a raw
   munch over the callee window [sp - 32, sp) and the identity record [fr + 2176, fr + 2214), the new record there)
   to C_B81860_at's body; the journal across the run by ajournal_exec, ctl_rt by w2_ctl_rt. *)
Lemma w2_after_ingest : forall POST (b : nat) (cx : ctlcx) (fr k sp phi : Z) ly3 S3 (W3 : Reusable.YA0n.world segs)
    (regs3 R : bvmap 5 word) (mem3 m' : word -> option byte) md3 md',
  CFb POST C81860 b ->
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  (forall cid pos, In (cid, pos) (own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  k <= 2 * Z.of_nat b + 1 -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, rnb cx b)]) ->
  B.ACtlCutP.FRAC B cx fr fr regs3 mem3 -> Reusable.YG0d.spZ regs3 = sp ->
  B.ACtlCut.c_n cx < 2 ^ 26 -> (b <= 6)%nat -> B.ACtlCutP.HB mem3 phi (rnb cx b) ->
  B.ACtlCut.rgv regs3 22 (Z.of_nat b) -> B.ACtlCutP.OURb cx fr mem3 -> B.ACtlCutP.CUR cx 7 regs3 ->
  B.ACtlCutP.RBE cx fr regs3 mem3 -> B.ACtlCut.rgv regs3 21 36 ->
  B.ACtlCutP.FGBr cx fr (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) (S b)) mem3 ->
  B.ACtlCut.rgv regs3 20 phi -> B.ACtlCut.rgv regs3 27 32 ->
  lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 ->
  lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 ->
  lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 ->
  lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 ->
  lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 ->
  lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 ->
  lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21 ->
  lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 ->
  lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 ->
  lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 ->
  lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 ->
  lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 ->
  lib.Reusable.YK11.getr R 10 = Z_to_bv 64 1 ->
  lib.Lib.Frame.munch [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] mem3 m' ->
  lib.Lib.Frame.stk B.Img0.rsegs m' (sp - 32) sp ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m' (fr + 2176)
    [lib.Lib.Cells.CB 38 (B.ACtlCutP.SM.RID (B.ACtlCut.c_in cx) (S b))] ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81860 R m' md') (POST cx).
Proof.
  intros POST b cx fr k sp phi ly3 S3 W3 regs3 R mem3 m' md3 md' H60 HB HJ Hfrs Hfa Hk HRT Hperm HFRAC Hsp Hcn Hb6
    HHB H22 HOUR HCUR HRBE H21 HFGB H20 H27 E2 E3 E4 E8 E9 E19 E20 E21 E22 E23 E25 E26 E27 E10 MU STc RWc Hhid
    Hsbm.
  pose proof HFRAC as (A & sp0 & _ & _ & Hspz & _ & _ & H9 & _ & _ & _ & Hfr32 & HA32 & HAc & HspA & HfrA & HA448 &
                       Hsp4 & _).
  rewrite Hsp in Hspz. subst sp0.
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hsp in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & _ & _ & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof HJ as (_ & Hlyle & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  (* outside the write set *)
  assert (OSH : forall x, B.AsanRT.in_shadow x ->
                  lib.Lib.Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x).
  { intros x Hx.
    unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hx.
    apply w2_out_W; lia. }
  assert (OIMG : forall x, Reusable.YImgTop.IMG_LO <= x < Reusable.YImgTop.IMG_TOP ->
                   lib.Lib.Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x).
  { intros x Hx. apply w2_out_W; [lia |].
    destruct (Z_lt_le_dec x (fr + 2176)) as [Hl | Hl]; [left; exact Hl |].
    destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [Hh | Hh]; [exfalso | right; exact Hh].
    apply (Hfimg x ltac:(lia)). apply w2_in_img. exact Hx. }
  (* the journal across the run *)
  assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
             (fun a => (sp - 32 <= a < sp) \/ (fr + 2176 <= a < fr + 2176 + 38)) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx |].
      pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
      assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
      { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        apply Z.mod_small. exact Hxr. }
      destruct (w2_W_cases fr sp (bv_unsigned x)) as [Ho | [Hs | Hr]].
      + rewrite (MU x Ho). exact Hx.
      + destruct STc as (_ & _ & STc'). destruct (STc' _ Hs) as (_ & bb & Hbb).
        assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
        { intros Hi. pose proof (w2_segs_low _ Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl. lia. }
        rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr Hni Hbb). discriminate.
      + pose proof (w2_cells_bytes _ _ _ _ RWc) as Hidn.
        destruct (w2_ba_rd m' (fr + 2176) _ (bv_unsigned x) Hidn
                    ltac:(rewrite B.Prog.Seg.RtmB.rb_RID_len; lia)) as (bb & Hbb).
        rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr (Hfimg (bv_unsigned x) ltac:(lia)) Hbb). discriminate.
    - exact Hhid.
    - exact Hsbm.
    - intros a [Ha | Ha].
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
      + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia. }
  pose proof HJ' as (HAR' & _).
  assert (HRT' : B.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ').
  (* the kept reads *)
  assert (KK : forall a, (a < sp - 32 \/ sp <= a) -> (a < fr + 2176 \/ fr + 2176 + 38 <= a) -> 0 <= a < 2 ^ 64 ->
                 lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a))
    by (intros a K1 K2 Ha; exact (w2_munch_mrd _ mem3 m' a MU Ha (w2_out_W fr sp a K1 K2))).
  assert (KA : KEEPR mem3 m' A (A + 448)) by (intros a Ha; apply KK; lia).
  assert (KS : KEEPR mem3 m' (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW)).
  { intros a Ha.
    unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
      B.ACtlCutP.FRAME_BYTES in Ha.
    apply KK; lia. }
  assert (KT : KEEPR mem3 m' (fr + 4088) (fr + 4088 + 8)) by (intros a Ha; apply KK; lia).
  assert (KF : KEEPR mem3 m' fr (fr + 24)) by (intros a Ha; apply KK; lia).
  assert (KHf : forall a, Reusable.YG0d.spZ regs3 <= a < B.ACtlCut.c_sp cx -> fr + B.ACtlCutP.FRAME_BYTES <= a ->
                  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a)).
  { intros a Ha Hb'. rewrite Hsp in Ha. unfold B.ACtlCutP.FRAME_BYTES in Hb'. apply KK; lia. }
  assert (KTBL : KEEPR mem3 m' (B.ACtlCutP.BAC.BA_FR + 72)
                   (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl))).
  { pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
    apply (w2_munch_keepr _ mem3 m' _ _ MU); [lia | lia |]. intros a Ha. apply OIMG. lia. }
  assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
    by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
  assert (KROW : KEEPR mem3 m' (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                   (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) +
                    Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))))).
  { rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
    unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
    apply (w2_munch_keepr _ mem3 m' _ _ MU); [lia | lia |]. intros a Ha. apply OIMG. lia. }
  assert (KBOX : KEEPR mem3 m' B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)))
    by exact (w2_kept_ro mem3 m' _ _ HRT HRT' w2_box_ro).
  (* the successor cut *)
  apply (H60 cx [Z.of_nat b] fr k ly3 S3 W3 R m' md' HB HJ' Hfrs Hfa).
  - unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81860_at, B.ACtlCutP.ixn.
    cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
  - unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81860_at, B.ACtlCutP.ixn.
    cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
    exists phi.
    refine (conj Hperm (conj _ (conj Hcn (conj Hb6 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ _)))))))))))))).
    + apply (w2_frac_regs cx fr fr regs3 R m' E2 E3 E4 E8 E9 E19 E26).
      exact (w2_frac_mem cx fr fr regs3 mem3 m' KHf KF KS KT HFRAC).
    + split; [exact (proj1 HHB) |]. apply (w2_addr_keep mem3); [| exact (proj2 HHB)].
      intros i Hi. destruct (proj2 HHB) as (_ & _ & _ & Hadb). destruct (Hadb i Hi) as (Happi & _).
      pose proof (w2_shadow_of_app _ Happi) as Hsh.
      apply (w2_munch_mrd _ mem3 m' _ MU); [| exact (OSH _ Hsh)].
      unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
        B.AsanRT.HIGHMEM_BEG in Hsh.
      lia.
    + exact (w2_rgv_move R regs3 22 _ E22 H22).
    + unfold B.ACtlCutP.OURb in *. eapply w2_bytes_keep; [| exact HOUR]. intros a Ha.
      unfold B.ACtlCutP.SM.OUR in Ha. rewrite length_map, length_seq in Ha. apply KK; lia.
    + exact (w2_cur_regs cx 7 regs3 R E23 E25 HCUR).
    + apply (w2_rbe_regs cx fr regs3 R m' E9).
      apply (w2_rbe_mem cx fr regs3 mem3 m' A H9 ltac:(lia) ltac:(lia) ltac:(lia) KA (fun a Ha _ => KS a Ha) KTBL
               KBOX KROW).
      * intros Hh Hr. split.
        -- exact (w2_kept_ro mem3 m' _ _ HRT HRT' (w2_names_ro _ Hh Hr)).
        -- exact (ctl_names_addressable _ _ _ _ _ _ HAR' Hh Hr).
      * exact HRBE.
    + exact (w2_rgv_move R regs3 21 _ E21 H21).
    + unfold B.ACtlCutP.IDBr. exact (w2_cells_bytes _ _ _ _ RWc).
    + unfold B.ACtlCutP.FGBr in *. eapply w2_bytes_keep; [| exact HFGB]. intros a Ha.
      rewrite (B.Prog.Seg.RtmB.rb_RFG_len _ (S b) ltac:(lia)) in Ha. apply KK; lia.
    + exact (w2_rgv_move R regs3 20 _ E20 H20).
    + unfold B.ACtlCut.a0v, B.ACtlCut.rgv. exact E10.
    + exact (w2_rgv_move R regs3 27 _ E27 H27).
  - exact HRT'.
Qed.

(* Turn 6 of the round-trip model (RtmB): the fragment call closed, the joined record names 0x1000 and 17 payload
   bytes at offset 19 of RFG 7; the ingest of RID 6 with them returns 1 and its new record is RID 7
   (lib/B/Prog/Seg/R12.v:306-327's r12_rtm, over RtmB only). *)
Lemma w2_r12_rtm : forall inp : list byte, B.ACtlCutP.SM.rt_n inp (Z.of_nat 6) <> 0 ->
  B.ACtlCutP.SM.fg_rf (B.ACtlCutP.SM.rt_n inp (Z.of_nat 6)) (B.ACtlCutP.SM.RFG inp 6)
    (B.ACtlCutP.SM.rt_g inp (Z.of_nat 6)) = 1 /\
  B.ACtlCutP.RFR.fg_addr (B.ACtlCutP.SM.RFG inp 6) (B.ACtlCutP.SM.rt_g inp (Z.of_nat 6)) = 0x1000 /\
  B.ACtlCutP.RFR.fg_T (B.ACtlCutP.SM.RFG inp 6) (B.ACtlCutP.SM.rt_g inp (Z.of_nat 6)) - 13 = 17 /\
  fst (B.ACtlCutP.RIM.ING (B.ACtlCutP.SM.RID inp 6) 0x1000 (B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG inp 7) 19 17)) = 1 /\
  B.ACtlCutP.SM.RID inp 7 =
    snd (B.ACtlCutP.RIM.ING (B.ACtlCutP.SM.RID inp 6) 0x1000 (B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG inp 7) 19 17)) /\
  length (B.ACtlCutP.SM.RFG inp 7) = 72%nat.
Proof.
  intros inp Hn. change (Z.of_nat 6) with 6 in *.
  pose proof (B.Prog.Seg.RtmB.rb_rtm_close inp Hn) as Hc.
  destruct (B.Prog.Seg.RtmB.rb_rtm_close_vals inp Hn) as (Ha & Hl).
  pose proof (B.Prog.Seg.RtmB.rb_rtm_ing6 inp Hn) as Hi.
  destruct (B.Prog.Seg.RtmB.rb_RS_56 inp 6%nat (or_intror eq_refl) Hn) as (HR & HF).
  change (Z.of_nat 6) with 6 in HR, HF.
  assert (Hrf : B.ACtlCutP.SM.fg_rf (B.ACtlCutP.SM.rt_n inp 6) (B.ACtlCutP.SM.RFG inp 6)
                  (B.ACtlCutP.SM.rt_g inp 6) = 1)
    by (unfold B.ACtlCutP.SM.fg_rf; rewrite Hc; reflexivity).
  assert (Hpl : B.ACtlCutP.SM.f_pl (B.ACtlCutP.SM.rt_n inp 6) (B.ACtlCutP.SM.RFG inp 6) (B.ACtlCutP.SM.rt_g inp 6) =
                B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG inp 7) 19 17).
  { unfold B.ACtlCutP.SM.f_pl. rewrite <- HF, Hl. reflexivity. }
  rewrite Hpl, Ha in Hi.
  split; [exact Hrf |]. split; [exact Ha |]. split; [exact Hl |]. split; [exact Hi |].
  split; [rewrite HR; unfold B.ACtlCutP.SM.fg_id; rewrite Hrf, Ha, Hpl; reflexivity |].
  apply B.Prog.Seg.RtmB.rb_RFG_len; lia.
Qed.

(* The three record-pointer spills [A + 224, A + 248) as one three-cell list (R12.v:92-102's r12_ro24). *)
Lemma w2_ro24 : forall (m : word -> option byte) (a : Z) (v1 v2 v3 : word),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 v1) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + 8) (lib.Lib.Mem.le8 v2) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + 16) (lib.Lib.Mem.le8 v3) ->
  lib.Lib.Step.ro_cells B.Img0.rsegs m a [lib.Lib.Cells.C8 v1; lib.Lib.Cells.C8 v2; lib.Lib.Cells.C8 v3].
Proof.
  intros m a v1 v2 v3 H1 H2 H3. split; [cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]; repeat split |].
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r.
  apply (proj2 (lib.Lib.Mem.bytes_at_app B.Img0.rsegs m a (lib.Lib.Mem.le8 v1)
                  (lib.Lib.Mem.le8 v2 ++ lib.Lib.Mem.le8 v3))).
  split; [exact H1 |].
  rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8.
  apply (proj2 (lib.Lib.Mem.bytes_at_app B.Img0.rsegs m (a + 8) (lib.Lib.Mem.le8 v2) (lib.Lib.Mem.le8 v3))).
  split; [exact H2 |].
  rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8. replace (a + 8 + 8) with (a + 16) by lia. exact H3.
Qed.

(* A slice of a byte run. *)
Lemma w2_bytes_bsl : forall (m : word -> option byte) (a : Z) (bs : list byte) (k n : nat),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> (k + n <= length bs)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hkn.
  rewrite <- (firstn_skipn k bs) in H. apply lib.Lib.Mem.bytes_at_app in H as (_ & H).
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply lib.Lib.Mem.bytes_at_app in H as (H & _). exact H.
Qed.

(* ---- S_R9's helpers.  r9_st_F writes the parse record's shadow [Sfr fr + 296, + 301) = 0, 0, 0, 0, 4: the 36 bytes
   [fr + 2368, fr + 2404) are then addressable (four granules of shadow 0, then 4 bytes of a granule with shadow 4). *)
Lemma w2_rec_addressable : forall (m : word -> option byte) (fr : Z) (c0 c1 c2 c3 c4 : byte),
  fr mod 8 = 0 -> 0 <= fr -> fr + 2404 <= B.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < 36 -> B.AsanRT.app_mem (fr + 2368 + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.ACtlCutP.Sfr fr + 296) [c0; c1; c2; c3; c4] ->
  bv_signed c0 = 0 -> bv_signed c1 = 0 -> bv_signed c2 = 0 -> bv_signed c3 = 0 -> bv_signed c4 = 4 ->
  B.AsanRT.addressable m (fr + 2368) 36.
Proof.
  intros m fr c0 c1 c2 c3 c4 Hfr Hfr0 Hfr1 Happ (_ & _ & Hb) E0 E1 E2 E3 E4.
  split; [lia |]. split; [lia |]. split; [lia |].
  intros i Hi. split; [exact (Happ i Hi) |].
  remember (Z.to_nat (i / 8)) as j eqn:Ej.
  assert (Es : B.AsanRT.shadow_addr (fr + 2368 + i) = B.ACtlCutP.Sfr fr + 296 + Z.of_nat j).
  { subst j. rewrite Z2Nat.id by lia. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr. lia. }
  pose proof (Hb j ltac:(subst j; cbn [length]; lia)) as Hbi. rewrite <- Es in Hbi.
  assert (Hj : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat) by (subst j; lia).
  unfold B.AsanRT.shadow_ok.
  destruct Hj as [-> | [-> | [-> | [-> | ->]]]]; cbn [nth_error] in Hbi; eexists; (split; [exact Hbi |]).
  - left. exact E0.
  - left. exact E1.
  - left. exact E2.
  - left. exact E3.
  - right. rewrite E4. split; [| lia].
    assert (Hi8 : i / 8 = 4) by lia. lia.
Qed.

(* The fake frame's shadow after r9_st_F: the old bytes outside [p + 296, p + 301), the five new ones inside. *)
Lemma w2_sh_splice : forall (m m' : word -> option byte) (p : Z) (sh : list byte) (c0 c1 c2 c3 c4 : byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m p sh -> length sh = 392%nat ->
  (forall a, p <= a < p + 392 -> ~ (p + 296 <= a < p + 301) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' (p + 296) [c0; c1; c2; c3; c4] ->
  exists sh', lib.Lib.Mem.bytes_at B.Img0.rsegs m' p sh' /\ length sh' = 392%nat.
Proof.
  intros m m' p sh c0 c1 c2 c3 c4 Hsh Hl K H5.
  exists (firstn 296 sh ++ [c0; c1; c2; c3; c4] ++ skipn 301 sh). split.
  - apply lib.Lib.Mem.bytes_at_app. split.
    + pose proof (w2_bytes_bsl m p sh 0 296 Hsh ltac:(lia)) as H1. cbn [skipn] in H1. rewrite Z.add_0_r in H1.
      eapply w2_bytes_keep; [| exact H1]. intros a Ha. rewrite length_firstn, Hl in Ha. apply K; lia.
    + rewrite length_firstn, Hl. change (Z.of_nat (Nat.min 296 392)) with 296.
      apply lib.Lib.Mem.bytes_at_app. split; [exact H5 |].
      cbn [length]. change (Z.of_nat 5) with 5.
      pose proof (w2_bytes_bsl m p sh 301 91 Hsh ltac:(lia)) as H2.
      rewrite firstn_all2 in H2 by (rewrite length_skipn; lia).
      replace (p + 296 + 5) with (p + Z.of_nat 301) by lia.
      eapply w2_bytes_keep; [| exact H2]. intros a Ha. rewrite length_skipn, Hl in Ha. apply K; lia.
  - rewrite !length_app, length_firstn, length_skipn, Hl. cbn [length]. lia.
Qed.

(* The same for any run of new bytes l at offset j of a 392-byte shadow. *)
Lemma w2_sh_splice_gen : forall (m m' : word -> option byte) (p : Z) (sh l : list byte) (j : nat),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m p sh -> length sh = 392%nat -> (j + length l <= 392)%nat ->
  (forall a, p <= a < p + 392 -> ~ (p + Z.of_nat j <= a < p + Z.of_nat j + Z.of_nat (length l)) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' (p + Z.of_nat j) l ->
  exists sh', lib.Lib.Mem.bytes_at B.Img0.rsegs m' p sh' /\ length sh' = 392%nat.
Proof.
  intros m m' p sh l j Hsh Hl Hj K H5.
  exists (firstn j sh ++ l ++ skipn (j + length l) sh). split.
  - apply lib.Lib.Mem.bytes_at_app. split.
    + pose proof (w2_bytes_bsl m p sh 0 j Hsh ltac:(lia)) as H1. cbn [skipn] in H1. rewrite Z.add_0_r in H1.
      eapply w2_bytes_keep; [| exact H1]. intros a Ha. rewrite length_firstn, Hl in Ha. apply K; lia.
    + rewrite length_firstn, Hl, Nat.min_l by lia.
      apply lib.Lib.Mem.bytes_at_app. split; [exact H5 |].
      pose proof (w2_bytes_bsl m p sh (j + length l) (392 - (j + length l)) Hsh ltac:(lia)) as H2.
      rewrite firstn_all2 in H2 by (rewrite length_skipn; lia).
      replace (p + Z.of_nat j + Z.of_nat (length l)) with (p + Z.of_nat (j + length l)) by lia.
      eapply w2_bytes_keep; [| exact H2]. intros a Ha. rewrite length_skipn, Hl in Ha. apply K; lia.
  - rewrite !length_app, length_firstn, length_skipn, Hl. lia.
Qed.

(* An 8-aligned granule whose shadow byte is c is addressable for its first n bytes when c = 0 or n <= c <= 7. *)
Lemma w2_addr_granule : forall (m : word -> option byte) (p n : Z) (c : byte),
  p mod 8 = 0 -> 0 <= p -> 0 <= n <= 8 -> p + n <= B.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < n -> B.AsanRT.app_mem (p + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.AsanRT.shadow_addr p) [c] ->
  (bv_signed c = 0 \/ (n <= bv_signed c /\ bv_signed c <= 7)) ->
  B.AsanRT.addressable m p n.
Proof.
  intros m p n c Hp8 Hp0 Hn HnA Happ (_ & _ & Hb) Hc.
  split; [lia |]. split; [lia |]. split; [lia |].
  intros i Hi. split; [exact (Happ i Hi) |].
  exists c. split.
  - assert (Es : B.AsanRT.shadow_addr (p + i) = B.AsanRT.shadow_addr p + Z.of_nat 0)
      by (unfold B.AsanRT.shadow_addr; cbn [Z.of_nat]; lia).
    unfold lib.Lib.Mem.wa in Hb. rewrite Es. exact (Hb 0%nat ltac:(cbn [length]; lia)).
  - unfold B.AsanRT.shadow_ok. destruct Hc as [Hc | Hc]; [left; exact Hc | right; lia].
Qed.

(* nth_error of a prefix inside it (R9.v:766-771's r9_nth_firstn). *)
Lemma w2_nth_firstn : forall (l : list byte) (n i : nat), (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros n i Hi; [rewrite firstn_nil; reflexivity |].
  destruct n as [|n]; [lia |]. cbn [firstn]. destruct i as [|i]; [reflexivity |].
  cbn [nth_error]. apply IH. lia.
Qed.

(* A byte of a frame's first 50, as the parse model reads it. *)
Lemma w2_cp_v : forall (F : list byte) (i : nat) (x : byte),
  (i < 50)%nat -> nth_error F i = Some x ->
  B.ACtlCutP.RPA.cp_v (B.ACtlCutP.SM.fr50 F) i = bv_unsigned x.
Proof.
  intros F i x Hi Hx.
  assert (E : nth_error (B.ACtlCutP.SM.fr50 F) i = Some x).
  { unfold B.ACtlCutP.SM.fr50. rewrite (w2_nth_firstn _ 50 i Hi).
    rewrite nth_error_app1; [exact Hx |]. apply nth_error_Some. rewrite Hx. discriminate. }
  unfold B.ACtlCutP.RPA.cp_v, B.ACtlCutP.RPA.cp_b. f_equal. apply nth_error_nth. exact E.
Qed.

(* The fragment state is the zero record at every turn b <= 5, and with it the fragment call returns 0
   (R9.v:738-763's r9_rfg_z72 / r9_fgrf_z72, over the model's names). *)
Lemma w2_rfg_z72 : forall inp b, (b <= 5)%nat -> B.ACtlCutP.SM.RFG inp b = B.ACtlCutP.SM.z72.
Proof.
  intros inp b. unfold B.ACtlCutP.SM.RFG. induction b as [|b IH]; intros Hb; [reflexivity |].
  cbn [B.ACtlCutP.SM.rt_st].
  destruct (B.ACtlCutP.SM.rt_n inp (Z.of_nat b) =? 0); [apply IH; lia |].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [snd]; [apply IH; lia |].
  destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) eqn:E5; cbn [snd]; [| apply IH; lia].
  exfalso. apply orb_true_iff in E5 as [E | E]; apply Z.eqb_eq in E; lia.
Qed.

Lemma w2_fgrf_z72 : forall len g, B.ACtlCutP.SM.fg_rf len B.ACtlCutP.SM.z72 g = 0.
Proof.
  intros len g. unfold B.ACtlCutP.SM.fg_rf, B.ACtlCutP.SM.fcls, B.ACtlCutP.RFR.fg_class.
  cbn [Z.eqb orb negb].
  destruct (B.ACtlCutP.RFR.fg_fr len g); cbn [negb]; [| reflexivity].
  destruct (B.ACtlCutP.RFR.bat g 19 =? 1); [reflexivity |].
  assert (Hk : B.ACtlCutP.RFR.fg_keep B.ACtlCutP.SM.z72 g = false).
  { unfold B.ACtlCutP.RFR.fg_keep, B.ACtlCutP.RFR.fg_hf.
    replace (B.ACtlCutP.RFR.bat B.ACtlCutP.SM.z72 6) with 0 by reflexivity.
    cbn [Z.eqb negb andb]. reflexivity. }
  rewrite Hk. cbn [negb]. reflexivity.
Qed.

(* ---- Callees in the core's afn_pre form (S_R14's reac_box_catalogue_match): their post is a journal from the call
   state with no own frame (APostBase.apost_base); the caller's facts come back through its view clauses. *)

(* A view kept between two worlds, at a byte visible before, is a raw read kept (aview_vis_mrd on both sides; the
   later world hides no more, YA0n.wle). *)
Lemma w2_view_keep : forall (W W' : Reusable.YA0n.world segs) (m m' : word -> option byte) (a : Z),
  Reusable.YA0n.wle W W' -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a).
Proof.
  intros W W' m m' a Hle Hv E.
  assert (Hv' : Reusable.YA0n.w_H W' (Z_to_bv 64 a) = false).
  { destruct (Reusable.YA0n.w_H W' (Z_to_bv 64 a)) eqn:E'; [| reflexivity].
    unfold Reusable.YA0n.wle, Reusable.YA0i.hsub in Hle. rewrite (Hle _ E') in Hv. discriminate. }
  rewrite (aview_vis_mrd W' m' a Hv'), (aview_vis_mrd W m a Hv) in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a)) as [x |],
    (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [y |]; cbn [option_map] in E; try discriminate;
    [| reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A visible byte's raw read is the core's restricted byte. *)
Lemma w2_mbyte_of_mrd : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (x : byte),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a) = Some x ->
  lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) a = Some x.
Proof.
  intros W m a x Hv Hx. pose proof (aview_vis_mrd W m a Hv) as E. rewrite Hx in E.
  unfold Reusable.YG0n.aview in E.
  destruct (lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) a) as [y |];
    cbn [option_map] in E; [| discriminate].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* One byte, as the core's one-byte value. *)
Lemma w2_le_byte1 : forall x : byte, Z_to_bv 8 (lib.Reusable.YO0f.le_byte (bv_unsigned x) 1 0) = x.
Proof.
  intros x. pose proof (bv_unsigned_in_range 8 x) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold lib.Reusable.YO0f.le_byte. rewrite Z.shiftr_0_r.
  change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small (bv_unsigned x) 256) by lia.
  rewrite (Z.mod_small (bv_unsigned x) 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The converse of w2_mbyte_of_mrd. *)
Lemma w2_mrd_of_mbyte : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (x : byte),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) a = Some x ->
  lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a) = Some x.
Proof.
  intros W m a x Hv Hx. pose proof (aview_vis_mrd W m a Hv) as E.
  unfold Reusable.YG0n.aview in E. rewrite Hx in E. cbn [option_map] in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [y |]; cbn [option_map] in E; [| discriminate].
  injection E as E. f_equal. apply bv_eq. symmetry. exact E.
Qed.

(* The k-th byte of an 8-byte little-endian word, as the core's le_byte. *)
Lemma w2_le_bytes_nth : forall (n k : nat) (z : Z), (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [| n IH]; intros k z Hk; [lia |].
  cbn [Z_to_le_bytes]. destruct k as [| k].
  - cbn [nth_error Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite (IH k (Z.shiftr z 8)) by lia. rewrite Z.shiftr_shiftr by lia.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia. reflexivity.
Qed.

Lemma w2_le8_nth : forall (v : Z) (k : nat), 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  nth_error (lib.Lib.Mem.le8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (lib.Reusable.YO0f.le_byte v 8 k)).
Proof.
  intros v k Hv Hk.
  assert (Ev : bv_unsigned (Z_to_bv 64 v) = v).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
  unfold lib.Lib.Mem.le8, word_to_le_bytes. rewrite Ev, (w2_le_bytes_nth 8 k v Hk). f_equal.
  apply lib.Lib.Mem.Z_to_bv8_mod. unfold lib.Reusable.YO0f.le_byte.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by exact Hv.
  change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* An 8-byte value the post states over the restricted view, at visible off-image bytes, is a raw cell. *)
Lemma w2_cells_of_val_mem : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (o v : Z),
  0 <= v < 2 ^ 64 -> 0 <= o -> o + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> Reusable.YA0n.w_H W (Z_to_bv 64 (o + i)) = false) ->
  (forall i, 0 <= i < 8 -> ~ Reusable.YG0d.in_img segs (o + i)) ->
  lib.Reusable.YI04.val_mem segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) o 8 v ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m o [lib.Lib.Cells.CB 8 (lib.Lib.Mem.le8 (Z_to_bv 64 v))].
Proof.
  intros W m o v Hv Ho0 Ho1 Hvis Hni HV.
  assert (E : forall k, (k < 8)%nat ->
                lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (o + Z.of_nat k)) =
                Some (Z_to_bv 8 (lib.Reusable.YO0f.le_byte v 8 k)))
    by (intros k Hk; exact (w2_mrd_of_mbyte W m _ _ (Hvis (Z.of_nat k) ltac:(lia)) (HV k Hk))).
  assert (Hb : lib.Lib.Mem.bytes_at B.Img0.rsegs m o (lib.Lib.Mem.le8 (Z_to_bv 64 v))).
  { split; [exact Ho0 |]. split; [rewrite lib.Lib.Mem.length_le8; lia |].
    intros k Hk. rewrite lib.Lib.Mem.length_le8 in Hk. unfold lib.Lib.Mem.wa.
    rewrite (E k Hk), (w2_le8_nth v k Hv Hk). reflexivity. }
  pose proof (w2_rw_CB m o _ Hb) as H. rewrite lib.Lib.Mem.length_le8 in H. apply H.
  split; [exact Ho0 |]. split; [lia |]. intros i Hi.
  pose proof (E (Z.to_nat i) ltac:(lia)) as Ei. rewrite Z2Nat.id in Ei by lia.
  pose proof (w2_mrd_raw m (o + i) _ ltac:(lia) (Hni i Hi) Ei) as Hr.
  exact (w2_wview_some _ _ _ Hr).
Qed.

(* A byte of a frame's first 50. *)
Lemma w2_fr50_nth : forall (F : list byte) (i : nat) (x : byte),
  (i < 50)%nat -> nth_error F i = Some x -> nth_error (B.ACtlCutP.SM.fr50 F) i = Some x.
Proof.
  intros F i x Hi Hx. unfold B.ACtlCutP.SM.fr50. rewrite (w2_nth_firstn _ 50 i Hi).
  rewrite nth_error_app1; [exact Hx |]. apply nth_error_Some. rewrite Hx. discriminate.
Qed.

(* What a callee journal with no own frame keeps of an own6 cut's memory: the stack above the call's window, the
   class-6 frame and its shadow (YCbq.ajournal's frame clause, the cut's frame is in frames S3), the catalogue's
   read-only data (its image clause, by ctl_relro_not_owned), the read-only image bytes (ro_agree on both sides) and a
   block live on both sides (its block clause). *)
Lemma w2_cj_keeps : forall (cx : ctlcx) (fr k sp STK1 k1 : Z) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3
    ly2 S2 (W2 : Reusable.YA0n.world segs) mem2 md2 (phi n : Z),
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  B.ACtlCut.c_sp cx - 4096 < sp <= B.ACtlCut.c_sp cx ->
  Reusable.YCbq.ajournal segs B STK1 sp [] ly3 S3 W3 mem3 md3 [] ly2 S2 W2 mem2 md2 k1 ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 -> B.ACtlRtC.ctl_rt_C B ly2 S2 mem2 ->
  In (phi, n) (Reusable.YG0d.ablocks B ly3 S3) -> In (phi, n) (Reusable.YG0d.ablocks B ly2 S2) ->
  KEEPR mem3 mem2 sp (B.ACtlCut.c_sp cx) /\
  KEEPR mem3 mem2 fr (fr + 4096) /\
  KEEPR mem3 mem2 (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW) /\
  KEEPR mem3 mem2 (B.ACtlCutP.BAC.BA_FR + 72) (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl)) /\
  KEEPR mem3 mem2 (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
    (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) + Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))) /\
  KEEPR mem3 mem2 B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)) /\
  (B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   KEEPR mem3 mem2 (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) +
      Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))))) /\
  KEEPR mem3 mem2 phi (phi + Reusable.YG00.req_size n).
Proof.
  intros cx fr k sp STK1 k1 ly3 S3 W3 mem3 md3 ly2 S2 W2 mem2 md2 phi n HB HJ Hfrs Hfr6 Hsp HJc HRT HRT2 Hin3
    Hin2.
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 Hsp)
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof HJ as (HAR3 & Hlyle & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof HJc as (_ & _ & _ & Hwle & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct (img_vis_W W3) as (_ & _ & VI).
  assert (VK : forall a, Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
                 Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2 a =
                 Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a ->
                 lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a))
    by (intros a Hv E; exact (w2_view_keep W3 W2 mem3 mem2 a Hwle Hv E)).
  assert (KIMG : forall a, Reusable.YImgTop.IMG_LO <= a < Reusable.YImgTop.IMG_TOP ->
                   ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) ->
                   ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4) ->
                   lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a)).
  { intros a Ha Ho He. apply VK; [apply VI; lia |].
    apply F3; [apply w2_in_img; exact Ha | exact Ho | exact He |].
    apply Reusable.YCbq.fp_spares_closed. exact Reusable.YCbq.sink_closed_nil. }
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - intros a Ha. apply VK; [exact (proj1 (Hsvis a ltac:(lia))) |].
    apply F1; lia.
  - intros a Ha. apply VK; [exact (proj1 (Hfvis a Ha)) |].
    apply (F4 6 (B.ACtlCut.c_fpos cx) a Hin6); [| apply lib.Reusable.YI04.inFP_nil].
    left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia.
  - intros a Ha.
    unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
      B.ACtlCutP.FRAME_BYTES in Ha.
    apply VK.
    + apply (proj1 (Hfsvis a ltac:(unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia))).
    + apply (F4 6 (B.ACtlCut.c_fpos cx) a Hin6); [| apply lib.Reusable.YI04.inFP_nil].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
  - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
    intros a Ha. destruct (ctl_relro_not_owned a) as [Hno Hne].
    { left. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR. lia. }
    apply KIMG; [lia | exact Hno | exact Hne].
  - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
      by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
    rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
    intros a Ha. destruct (ctl_relro_not_owned a) as [Hno Hne].
    { right. unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *. lia. }
    apply KIMG; [| exact Hno | exact Hne].
    unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *. lia.
  - exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 w2_box_ro).
  - intros Hh Hr. exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 (w2_names_ro _ Hh Hr)).
  - destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi n HAR3 Hin3)
      as (_ & _ & _ & _ & Hpbytes & _ & _).
    intros a Ha. apply VK; [exact (proj1 (proj1 (Hpbytes a Ha))) |].
    replace a with (phi + (a - phi)) by lia.
    apply (F2 phi n (a - phi) Hin3 Hin2); [lia | apply lib.Reusable.YI04.inFP_nil].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. The two allocator sites of loop_rt.  Each is the core's rule at this site's constants, with the rule's
   continuation folded into the caller's; nothing else in the walk applies AMALLOC4 / AFREE4.  The stage supplies the
   journal, the register pins (from FRAC) and the chain (CHAIN_OF_CUT); the site lemma discharges the size, room, event and
   meter premises. *)

(* malloc @0x81760 (S_R7, n_b <> 0): a0 = n = rnb cx b, ra = 0x81764, frames own6, live list = the entry blocks. *)
Lemma w2_malloc_81760 : forall (cx : ctlcx) (b : nat) ly3 S3 W3 (regsT : bvmap 5 word) memT md3 k (o : Z) ch
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  CBASE cx ->
  AJ cx (own6 cx) ly3 S3 W3 memT md3 k ->
  k <= 2 * Z.of_nat b -> (b <= 6)%nat ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx) ->
  lib.Reusable.YK11.getr regsT 10 = Z_to_bv 64 (rnb cx b) -> 0 < rnb cx b <= 1492 ->
  Reusable.YG0d.spZ regsT = B.ACtlCut.c_sp cx + o -> o mod 16 = 0 -> -4096 < o <= -448 ->
  lib.Reusable.YK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 0x81764 ->
  B.ACtlCut.ctl_chain ly3 W3 memT regsT ch ->
  B.ACtlCut.ctl_trace_in B (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B)) regsT ch ->
  (forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2 (res : Z),
     Reusable.YA0n.wle W3 W2 ->
     AJ cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) ->
     Reusable.YG0d.aregs_preserved regsT regs2 ->
     lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 res ->
     Reusable.YG01.frames S2 = own6 cx ->
     4096 <= res ->
     Permutation (Reusable.YG0d.ablocks B ly2 S2) (ENTRYBL cx ++ [(res, rnb cx b)]) ->
     Reusable.YCbq.acall_kept segs B ly3 S3 W3 memT W2 mem2
       (B.ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (B.ACtlCut.c_sp cx + o)
       (fun a => res <= a < res + Reusable.YG00.req_size (rnb cx b)) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x81764 regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_malloc regsT memT md3) Q.
Proof.
  (* The donor's A/ACf2.v:116-141 at this site. *)
  intros cx b ly3 S3 W3 regsT memT md3 k o ch Q HB HJ Hk Hb Hperm Ha0 Hn Hsp Ho16 Ho Hgp Htp Hra Hch Htr HK.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & Hlive0 & _) & _).   (* tfib_lib_pre_x, YCfn.v:32-45 *)
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).                      (* ajournal, YCbq.v:350-372 *)
  assert (Hbb : Reusable.YCbq.bsum (Reusable.YG0d.ablocks B ly3 S3) = Reusable.YCbq.bsum (ENTRYBL cx))
    by exact (Reusable.YCbq.bsum_perm _ _ Hperm).
  rewrite <- (Reusable.YCbq.blocks_bytes_bsum B ly3 S3),
          <- (Reusable.YCbq.blocks_bytes_bsum B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) in Hbb.
  unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64. rewrite <- HPCM.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (AMALLOC4 W3 regsT memT Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
              (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
              (own6 cx) ly3 S3 md3 k (rnb cx b) o (Z_to_bv 64 0x81764) ch HJ).
    - exact Ha0.
    - unfold Reusable.YG00.MALLOC_MAX; lia.
    - (* blocks_bytes S3 = blocks_bytes (c_S cx) (Hbb) and blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX (the pre);
         rnb <= 1492 <= LIVE_LIB = 2^33 *)
      unfold Reusable.YCfn.LIVE_LIB in Hlive0; lia.
    - exact Hsp.
    - exact Ho16.
    - lia.
    - unfold Reusable.YG0d.ASTACK, Reusable.YCfn.LLVMF_STK; lia.       (* 16384 + 4096 <= 32768 *)
    - exact Hgp.
    - exact Htp.
    - exact Hra.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - unfold Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *; lia.    (* st_nev S3 <= st_nev S + 12 *)
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

(* The live-list step of the free: removing the turn block from a list that is the entry blocks plus that block
   leaves a permutation of the entry blocks.  Stdlib only. *)
Lemma w2_perm_free : forall (E l1 l2 : list (Z * Z)) (x : Z * Z),
  Permutation (l1 ++ x :: l2) (E ++ [x]) -> Permutation (l1 ++ l2) E.
Proof.
  intros E l1 l2 x H.
  apply (Permutation_cons_inv (a := x)).
  apply (Permutation_trans (Permutation_middle l1 l2 x)).
  apply (Permutation_trans H).
  apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* free @0x81a9c (S_R13, S_R15, S_R16, S_R20): a0 = s4 = phi, ra = 0x81aa0; the live list is the entry blocks plus
   (phi, rnb cx b), and phi is not an entry block (so the rule's entry-block premise is vacuous). *)
Lemma w2_free_81a9c : forall (cx : ctlcx) (b : nat) (phi : Z) ly3 S3 W3 (regsT : bvmap 5 word) memT md3 k (o : Z) ch
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  CBASE cx ->
  AJ cx (own6 cx) ly3 S3 W3 memT md3 k ->
  k <= 2 * Z.of_nat b + 1 -> (b <= 6)%nat ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, rnb cx b)]) ->
  ~ In (phi, rnb cx b) (ENTRYBL cx) ->
  lib.Reusable.YK11.getr regsT 10 = Z_to_bv 64 phi ->
  Reusable.YG0d.spZ regsT = B.ACtlCut.c_sp cx + o -> o mod 16 = 0 -> -4096 < o <= -448 ->
  lib.Reusable.YK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 0x81aa0 ->
  B.ACtlCut.ctl_chain ly3 W3 memT regsT ch ->
  B.ACtlCut.ctl_trace_in B (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) regsT ch ->
  (forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     Reusable.YA0n.wle W3 W2 ->
     AJ cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) ->
     Reusable.YG0d.aregs_preserved regsT regs2 ->
     Reusable.YG01.frames S2 = own6 cx ->
     Permutation (Reusable.YG0d.ablocks B ly2 S2) (ENTRYBL cx) ->
     Reusable.YCbq.acall_kept segs B ly3 S3 W3 memT W2 mem2
       (B.ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (B.ACtlCut.c_sp cx + o)
       (fun a => phi <= a < phi + Reusable.YG00.req_size (rnb cx b)) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x81aa0 regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_free regsT memT md3) Q.
Proof.
  (* The donor's free pattern (A/ACf3.v:97-110) at this site. *)
  intros cx b phi ly3 S3 W3 regsT memT md3 k o ch Q HB HJ Hk Hb Hperm Hnin Ha0 Hsp Ho16 Ho Hgp Htp Hra Hch Htr HK.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
  assert (Hin : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64. rewrite <- HPCF.
  eapply Reusable.YA0n.SRr_bind.
  { eapply (AFREE4 W3 regsT memT Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
              (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
              (own6 cx) ly3 S3 md3 k phi (rnb cx b) o (Z_to_bv 64 0x81aa0) ch HJ Hin).
    - exact Ha0.
    - exact Hsp.
    - exact Ho16.
    - lia.
    - unfold Reusable.YG0d.ASTACK, Reusable.YCfn.LLVMF_STK; lia.
    - exact Hgp.
    - exact Htp.
    - exact Hra.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - unfold Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *; lia.    (* st_nev S3 <= st_nev S + 13 *)
    - exact Hch.
    - exact Htr.
    - intros Hent. exfalso. exact (Hnin Hent).
    - apply HMOK. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfrs2 & HK2 & _).
  apply (HK W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HP2).
  - rewrite Hfrs2, Hfrs, Hfr0, app_nil_r. reflexivity.
  - rewrite E2. apply (w2_perm_free (ENTRYBL cx) l1 l2 (phi, rnb cx b)). rewrite <- E1. exact Hperm.
  - exact HK2.
Qed.

(* A list on which an irreflexive relation holds pairwise has no duplicate.  Stdlib only (List.NoDup: stdpp, which
   BvBase brings in, has its own NoDup over ∈). *)
Lemma w2_pairwise_nodup : forall (X : Type) (R : X -> X -> Prop) (l : list X),
  Reusable.YG0f.pairwise R l -> (forall x, In x l -> ~ R x x) -> List.NoDup l.
Proof.
  intros X R l. induction l as [|x l IH]; cbn; intros Hp Hirr.
  - apply List.NoDup_nil.
  - apply List.NoDup_cons.
    + destruct Hp as [Hf _]. intros Hx. apply (Hirr x (or_introl eq_refl)).
      exact (proj1 (Forall_forall _ _) Hf x Hx).
    + destruct Hp as [_ Hp]. apply IH; [exact Hp |]. intros y Hy. apply Hirr. right. exact Hy.
Qed.

(* The turn block is not an entry block: the live list is a permutation of entry ++ [(phi, n)], and the core's
   AR_sep_law makes the live blocks pairwise disjoint with req_size >= 1, so (phi, n) cannot occur twice. *)
Lemma w2_phi_not_entry : forall (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (phi n : Z),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, n)]) ->
  ~ In (phi, n) (ENTRYBL cx).
Proof.
  (* AR is the journal's first conjunct (YCbq.v:354); the core's al_blocks (YG0d.v:423-429) makes the live blocks
     pairwise zdisjoint with 0 <= n, so req_size n >= 1 (YCbq.v:175 req_size_pos) and the live list has no duplicate;
     a permutation of entry ++ [(phi, n)] without duplicates has (phi, n) outside entry. *)
  intros cx own ly3 S3 W3 mem3 md3 k phi n HJ Hperm Hin.
  destruct HJ as (HAR & _).
  assert (Hin3 : In (phi, n) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi n HAR Hin3) as (_ & _ & _ & _ & _ & Hpw & _).
  assert (Hnd : List.NoDup (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (List.NoDup_map_inv (fun b0 : Z * Z => (fst b0, Reusable.YG00.req_size (snd b0)))).
    apply (w2_pairwise_nodup _ Reusable.YG0f.zdisjoint _ Hpw).
    intros x Hx. apply in_map_iff in Hx as ([p m] & <- & Hpm).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p m HAR Hpm) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (Reusable.YCbq.req_size_pos m (proj1 Hm)) as Hr.
    unfold Reusable.YG0f.zdisjoint. cbn [fst snd]. lia. }
  pose proof (Permutation.Permutation_NoDup Hperm Hnd) as Hnd2.
  apply (List.NoDup_remove_2 (ENTRYBL cx) [] (phi, n) Hnd2).
  rewrite app_nil_r. exact Hin.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. One lemma per cut, NAMED AND STATED AS lib/B/ACtl.v's stage hypothesis (ACtl.v:399-427, seg_R6 .. seg_R14), so
   the top cites each directly; the top's CF fixes SK := Reusable.YE2k.tfib_sink_head and FP := [], which these
   lemmas, proved for every SK and FP, discharge by instantiation (ACtl.v:177).  The loop itself is the top's
   (ACtl.v:733-768: turn_rt, loop_rt, vac_B816ec). *)

(* ---- S_R6's helpers: the build_as spec's premises in the core's view terms, and its post back in ctrl's. *)

(* Visible raw bytes are the view's byte array. *)
Lemma w2_garr8_of_bytes : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (q : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m q bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Reusable.YA0n.w_H W (Z_to_bv 64 (q + i)) = false) ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) q
    (map (fun x : byte => bv_unsigned x) bs).
Proof.
  intros W m q bs (H0 & H1 & Hb) Hv j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [x |] eqn:Ex; [| apply nth_error_None in Ex; lia].
  assert (En : nth j (map (fun x : byte => bv_unsigned x) bs) 0 = bv_unsigned x).
  { apply nth_error_nth. rewrite nth_error_map, Ex. reflexivity. }
  rewrite En. split.
  - intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, w2_le_byte1.
    apply (w2_mbyte_of_mrd W m _ x (Hv (Z.of_nat j) ltac:(lia))).
    pose proof (Hb j Hj) as Hj'. unfold lib.Lib.Mem.wa in Hj'. rewrite Ex in Hj'. exact Hj'.
  - pose proof (bv_unsigned_in_range 8 x) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

(* The converse, at visible bytes. *)
Lemma w2_bytes_of_garr8 : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (q : Z) (bs : list byte),
  0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Reusable.YA0n.w_H W (Z_to_bv 64 (q + i)) = false) ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) q
    (map (fun x : byte => bv_unsigned x) bs) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m q bs.
Proof.
  intros W m q bs H0 H1 Hv HG. split; [exact H0 |]. split; [exact H1 |].
  intros j Hj. destruct (nth_error bs j) as [x |] eqn:Ex; [| apply nth_error_None in Ex; lia].
  assert (Hj' : (j < length (map (fun x : byte => bv_unsigned x) bs))%nat) by (rewrite length_map; exact Hj).
  destruct (HG j Hj') as (HV & _).
  assert (En : nth j (map (fun x : byte => bv_unsigned x) bs) 0 = bv_unsigned x).
  { apply nth_error_nth. rewrite nth_error_map, Ex. reflexivity. }
  rewrite En in HV. pose proof (HV 0%nat ltac:(lia)) as H. cbn [Z.of_nat] in H.
  rewrite Z.add_0_r, w2_le_byte1 in H.
  unfold lib.Lib.Mem.wa. exact (w2_mrd_of_mbyte W m _ x (Hv (Z.of_nat j) ltac:(lia)) H).
Qed.

(* A sub-range of a registered read-only global range is one. *)
Lemma w2_emit_ro_sub : forall (q n q' n' : Z),
  B.Prog.C_reac_ctrl_build_as.EmitB.tctrl_emit_as_ro RLO RHI B GLOBS q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
  B.Prog.C_reac_ctrl_build_as.EmitB.tctrl_emit_as_ro RLO RHI B GLOBS q' n'.
Proof.
  intros q n q' n' ((q0 & sz & Hin & H1 & H2) & H3 & H4 & H5) Hq Hn' Hqn.
  split; [exists q0, sz; split; [exact Hin | lia] |]. split; [lia |]. split; [lia |].
  intros x Hx. apply H5. lia.
Qed.

(* The view's shadow hull of a range whose shadow bytes (and up to 7 below / 8 above) are present. *)
Lemma w2_hull_vis : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (x n : Z), 0 <= x -> 0 < n ->
  (forall s, B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem s) ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n.
Proof.
  intros W mem x n Hx Hn H s Hs. apply (Reusable.YCbq.aview_some_of_apresent segs). apply H.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The catalogue row of the round trip (lib/B/Prog/Seg/R6.v:282-290's r6_mrow_rng; R6.v is not Required). *)
Lemma w2_mrow_rng : forall inp, B.ACtlCutP.SM.CAT <= B.ACtlCutP.SM.mrow inp <= B.ACtlCutP.SM.CAT + 296 * 10 /\
  B.ACtlCutP.SM.mrow inp mod 8 = 0.
Proof.
  intros inp. unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.istar, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N,
    B.ACtlCutP.SM.CAT.
  pose proof (Z.mod_pos_bound (B.ACtlCutP.SM.mode inp / 2) 11 ltac:(lia)) as Hb.
  set (k := (B.ACtlCutP.SM.mode inp / 2) mod 11) in *.
  split; [lia |].
  replace (0x9f620 + 296 * k) with ((81604 + 37 * k) * 8) by lia.
  apply Z_mod_mult.
Qed.

(* build_as's `go` at the loop head (R6.v:333-340's r6_go). *)
Lemma w2_go : forall o md b, 0 < o -> 0 < md -> b <= 6 -> B.ACtlCutP.BAP.ba_go o md b = true.
Proof.
  intros o md b Ho Hm Hb. unfold B.ACtlCutP.BAP.ba_go. rewrite !andb_true_iff.
  split; [split |].
  - apply negb_true_iff. apply Z.eqb_neq. lia.
  - apply negb_true_iff. apply Z.eqb_neq. lia.
  - apply Z.leb_le. lia.
Qed.

(* The width the model reads from a catalogue row is non-negative (R6.v:302-308's r6_bmuw_nonneg). *)
Lemma w2_bmuw_nonneg : forall mp bs, 0 <= lib.Prog.RcPorts.bm_uw mp bs.
Proof.
  intros mp bs. unfold lib.Prog.RcPorts.bm_uw.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    try lia; pose proof (Z.le_max_r (lib.Prog.RcPorts.bm_in_ch bs) 2); lia.
Qed.

(* The request is 0 or a frame length 52 + 36 n, 2 <= n <= 40 (R6.v:293-300's r6_rtn_bnd). *)
Lemma w2_rtn_bnd : forall inp x, 0 <= B.ACtlCutP.SM.rt_n inp x <= 1492.
Proof.
  intros inp x. unfold B.ACtlCutP.SM.rt_n. destruct (B.ACtlCutP.SM.rt_E inp x) eqn:E; [| lia].
  unfold B.ACtlCutP.SM.rt_E, B.ACtlCutP.BAP.ba_E in E. apply andb_prop in E as [E _].
  unfold lib.Prog.RcEmit.em_wok in E. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* The build_as request of turn b is the round trip's n_b, and its frame is rt_F (SlotModel.v:78-84). *)
Lemma w2_ba_R : forall (inp : list byte) (o : Z) (b : nat), 0 < o -> (b <= 6)%nat ->
  B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_R o (B.ACtlCutP.SM.mrow inp) (Z.of_nat b)
    (B.ACtlCutP.SM.rt_mb inp) = B.ACtlCutP.SM.rt_n inp (Z.of_nat b).
Proof.
  intros inp o b Ho Hb. pose proof (w2_mrow_rng inp) as (Hm & _).
  unfold B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_R, B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_ok,
    B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_len, B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_n.
  rewrite (w2_go o (B.ACtlCutP.SM.mrow inp) (Z.of_nat b) Ho ltac:(unfold B.ACtlCutP.SM.CAT in Hm; lia) ltac:(lia)).
  cbn [andb].
  reflexivity.
Qed.

Lemma w2_ba_ok : forall (inp : list byte) (o : Z) (b : nat), 0 < o -> (b <= 6)%nat ->
  B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_ok o (B.ACtlCutP.SM.mrow inp) (Z.of_nat b)
    (B.ACtlCutP.SM.rt_mb inp) = B.ACtlCutP.SM.rt_E inp (Z.of_nat b).
Proof.
  intros inp o b Ho Hb. pose proof (w2_mrow_rng inp) as (Hm & _).
  unfold B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_ok, B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_n.
  rewrite (w2_go o (B.ACtlCutP.SM.mrow inp) (Z.of_nat b) Ho ltac:(unfold B.ACtlCutP.SM.CAT in Hm; lia) ltac:(lia)).
  cbn [andb].
  reflexivity.
Qed.

Lemma w2_rtn_E : forall (inp : list byte) (b : Z),
  B.ACtlCutP.SM.rt_n inp b <> 0 -> B.ACtlCutP.SM.rt_E inp b = true.
Proof.
  intros inp b H. unfold B.ACtlCutP.SM.rt_n in H. destruct (B.ACtlCutP.SM.rt_E inp b); [reflexivity |].
  exfalso. apply H. reflexivity.
Qed.

Lemma w2_rtE_n : forall (inp : list byte) (b : Z),
  B.ACtlCutP.SM.rt_E inp b = true -> B.ACtlCutP.SM.rt_n inp b = 52 + 36 * B.ACtlCutP.SM.rt_uw inp.
Proof. intros inp b H. unfold B.ACtlCutP.SM.rt_n. rewrite H. reflexivity. Qed.

(* B816ec_at b (Inv_B816ec_at SIv:1732) -> B81710_at b.  S_R6 (Slot.v:67; seg_R6 R6.v:1165), 0x816ec .. 0x81710.
   Run R6F.r6_evt_pre_F (R6F.v:42-59; 0x816ec -> build_as entry 0x8528c, ra = 0x81710; a0 = fr + 544, a1 = mdv,
   a2 = s6 = b, a3 = fr + 2624, a4 = BOXA, a5 = 0x1234, a6 = a7 = 0), then the callee
   reac_ctrl_build_as (cut-callee: its own fake-stack frames, via ctrl_lay_block's stack_malloc_1 and
   reac_box_model_block's stack_malloc_0 [UB Tk/AW/Sm1.v:72, Sm0.v:72]) by its caller-journal spec (owner: the
   build_as walk; not stated yet), which returns to 0x81710 = this stage's successor cut.  No trap.  k and frames are
   unchanged (the callee allocates no heap block; its fake frames are released before it returns).
   Body of C_B816ec_at -> the runs' premises (R6.v:347-...):
     r6_evt_pre_F's premises <- body:
     s1 = A, 0 <= A, A + 320 <= 2^64 ...... FRAC (rgv regs 9 A, A + 448 <= c_sp < APPMEM_END)
     ro_cells (A+312/272/264/256/248) .... RBE spills 312 (fr+544), 272 (SM.mrow), 264 (fr+2624), 256 0x21140 (= BOXA),
                                            248 0x1234; read-only-ness of the spill cells: V1 (stack window above sp)
     rng RNG (A+312/272/264/256/248) 8 ... V1 (rng_of_visible: the spill cells lie in [sp, c_sp))
     the build_as spec's premises <- body / world (what r6_evt R6.v:347 took from build_as's contract):
     s6 = bb = b, 0 <= b <= 6 ............ RS (rgv regs 22 (Z.of_nat b), (b <= 6)%nat)
     0 < fr, fr + 3136 <= APPMEM_END ...... FRAC (fr + FRAME_BYTES <= A, fr mod 32 = 0) and the frame's AR fact
                                            (al_frames: frame_addr >= 4096) through the journal
     mdv = mrow, 0 < mdv ................. RBE spill 272 (SM.mrow); mrow is the catalogue row CAT + 296 i (SlotModel.v:27)
     ba_go, Rv ........................... SlotModel (rt_n / rnb); seg_R6's model lemmas
     stk (sp - K) sp, sp mod 16 = 0 ...... FRAC (sp mod 16 = 0) + journal window [c_sp - LLVMF_STK, c_sp) (T1, V1)
     bytes_at (BA_FR + 72) ba_tbl, BOXA box6, mrow rt_mb, the name bytes ... RBE (and R6X)
     bytes_at (fr + 2624) dbv ............ OURb (SM.OUR, 6 bytes)
     rw_cells (fr + 544) [CB Rv junk] .... the fake frame's out[] slot: present / writable (T8, al_frames)
     addressable: window (T1), BA_SW 56 / BA_FR + 72 168 / BOXA 6 (T10, V6 image globals), fr + 2624 6 (RBE),
                  mdv 296 (T10), fr + 544 Rv (OUTA: addressable (fr + 544) 1492)
     ly_dj / app_mem / RT apartness ...... arithmetic over FRAC and the image map (T7, T13)
     mem_inv, asan_cells, shadow_rw ...... ctl_rt
   Post -> C_B81710_at body: Permutation kept (journal post, no block), FRAC kept (aregs_preserved + acall_kept: the
   spills are above sp, the frame bytes outside out[]), a0v regs (rnb cx b) (callee result Rv = rnb, SlotModel),
   (rnb <> 0 -> bytes_at (fr + 544) rt_F) from the callee post, (rnb = 0 -> R6X cx (S b)) from R6X cx b (R6X's b
   enters only through the (b = 5 \/ b = 6) guard, and rnb = 0 makes the name bytes RBE's), the rest kept.
   R6F.r6_evt_post_F (R6F.v:69-118, 0 steps) is NOT applied: build_as is a cut-callee whose caller-journal spec gives a
   world-form post (visible view only), so the stage goes from that post straight to C_B81710_at's body. *)
Lemma seg_R6 : forall POST (b : nat), CFb POST C81710 b -> CFb POST C816ec b.
Proof.
  intros POST b H710 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B816ec_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (Hperm & HFRAC & Hcn & HRS & HRBE & H21 & HR6X & HNMB & H27).
  destruct HRS as (Hb6 & HCUR & HOUR & H22 & HIDB & HFGB).
  destruct HR6X as (HOUTA6 & HA2624 & HTBL6 & HBOX6 & HROW6 & HNM6).
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & _).
  (* the cut's frame, stack and journal *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hstklo & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Hfc & Hfapp).
  rewrite Hfa3, <- Hfr6, Hfsb in Hfc, Hfapp.
  (* the frame lies off the image hull *)
  assert (Hfout : fr + 4096 <= 0x10000 \/ 0x5fe000 <= fr).
  { destruct (Z_lt_le_dec fr 0x5fe000) as [L1 | L1]; [| right; exact L1].
    destruct (Z_le_gt_dec (fr + 4096) 0x10000) as [L2 | L2]; [left; exact L2 |].
    exfalso. apply (Hfimg (Z.max fr 0x10000) ltac:(lia)). apply w2_in_img. lia. }
  destruct (img_vis_W W3) as (_ & _ & VI).
  (* the model of turn b *)
  pose proof (w2_mrow_rng (B.ACtlCut.c_in cx)) as (Hmrow & Hmrow8).
  pose proof (w2_rtn_bnd (B.ACtlCut.c_in cx) (Z.of_nat b)) as Hrnb.
  change (B.ACtlCutP.SM.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hrnb.
  pose proof (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)) as Hmbl.
  unfold B.ACtlCutP.SM.CAT in Hmrow.
  (* the five argument spills *)
  pose proof (w2_spill_at regs3 mem3 A 312 (fr + 544) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S312) as Q312.
  pose proof (w2_spill_at regs3 mem3 A 272 _ H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S272) as Q272.
  pose proof (w2_spill_at regs3 mem3 A 264 (fr + 2624) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S264) as Q264.
  pose proof (w2_spill_at regs3 mem3 A 256 0x21140 H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S256) as Q256.
  pose proof (w2_spill_at regs3 mem3 A 248 0x1234 H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S248) as Q248.
  pose proof (w2_spill_at regs3 mem3 A 128 0xe38f0000 H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S128) as Q128.
  assert (VST : forall off, 0 <= off -> off + 8 <= 448 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + off) 8).
  { intros off L1 L2. apply B.ProgBridge.rng_of_visible.
    apply (w2_vis_stack cx _ _ _ _ _ _ _ _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
  (* the run to the callee entry, then the call *)
  eapply w2_lift.
  - unfold Lib.Regs6ss.mkR_of.
    apply (B.Prog.Seg.R6F.r6_evt_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
      (A := A) (fr := fr) (mdv := B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx)).
    + exact H9.
    + lia.
    + lia.
    + exact (w2_ro8 _ _ _ Q312).
    + exact (w2_ro8 _ _ _ Q272).
    + exact (w2_ro8 _ _ _ Q264).
    + exact (w2_ro8 _ _ _ Q256).
    + exact (w2_ro8 _ _ _ Q248).
    + apply VST; lia.
    + apply VST; lia.
    + apply VST; lia.
    + apply VST; lia.
    + apply VST; lia.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' -> _ Hsbm.
    apply w2_cfg_back.
    match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (RT := R) end.
    pose proof (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
    pose proof HJ' as (HAR' & _).
    assert (R1 : lib.Reusable.YK11.getr RT 1 = Z_to_bv 64 0x81710) by reflexivity.
    assert (R2 : lib.Reusable.YK11.getr RT 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
    assert (R3 : lib.Reusable.YK11.getr RT 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
    assert (R4 : lib.Reusable.YK11.getr RT 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
    assert (R8 : lib.Reusable.YK11.getr RT 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
    assert (R9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
    assert (R12 : lib.Reusable.YK11.getr RT 12 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
    assert (R15 : lib.Reusable.YK11.getr RT 15 = Z_to_bv 64 0x1234) by reflexivity.
    assert (R19 : lib.Reusable.YK11.getr RT 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
    assert (R21 : lib.Reusable.YK11.getr RT 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
    assert (R22 : lib.Reusable.YK11.getr RT 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
    assert (R23 : lib.Reusable.YK11.getr RT 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
    assert (R25 : lib.Reusable.YK11.getr RT 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
    assert (R26 : lib.Reusable.YK11.getr RT 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
    assert (R27 : lib.Reusable.YK11.getr RT 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
    assert (HspR : Reusable.YG0d.spZ RT = sp) by (unfold Reusable.YG0d.spZ; rewrite R2; exact Hspz).
    assert (HSTK : B.Prog.C_reac_ctrl_build_as.REAC_CTRL_BUILD_AS_STK = 4640) by reflexivity.
    (* frame-side premise facts *)
    assert (FRV : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
      by (intros a Ha; exact (proj1 (Hfvis a Ha))).
    assert (FSV : forall s, B.AsanRT.shadow_addr fr <= s < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 s).
    { intros s Hs. apply Hfsvis.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia. }
    assert (RAF : forall x n, fr <= x -> 0 <= n -> x + n <= fr + 4096 -> B.AsanRT.addressable mem3 x n ->
                    Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3)
                      Reusable.YG0f.SHADOW_OFF x n).
    { intros x n L1 L2 L3 Hadd. apply (w2_range_addr_of_raw W3 mem3 x n Hadd). intros i Hi.
      apply (proj1 (FSV (B.AsanRT.shadow_addr (x + i)) ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia))). }
    assert (HUL : forall x n, fr + 64 <= x -> 0 < n -> x + n <= fr + 4000 ->
                    Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3) x n).
    { intros x n L1 L2 L3. apply (w2_hull_vis W3 mem3 x n ltac:(lia) L2). intros s Hs. apply FSV.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
    assert (FHOME : forall x n, fr <= x -> 0 <= n -> x + n <= fr + 4096 ->
                      B.Prog.C_reac_ctrl_build_as.EmitB.tctrl_emit_as_home ly3 S3 x n).
    { intros x n L1 L2 L3. right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split; [lia |].
      intros a Ha. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd].
      rewrite Hfa3, <- Hfr6, Hfsb. lia. }
    assert (FAPP : forall a, fr <= a < fr + 4096 -> Reusable.YG0f.app_addr a)
      by (intros a Ha; exact (Reusable.YG0f.in_app_addr _ _ a Hfapp ltac:(lia))).
    (* the call: reac_ctrl_build_as's caller-journal spec *)
    change 0x8528c with B.Prog.C_reac_ctrl_build_as.A_reac_ctrl_build_asP.
    pose proof (BUILD_AS Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)
                  (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 mem3 md' k RT
                  (fr + 544) (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx)) (Z.of_nat b) (fr + 2624) B.ACtlCutP.SM.BOXA 0
                  (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))
                  (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx)) B.ACtlCutP.SM.box6) as BA.
    cbv zeta in BA.
    eapply Reusable.YA0n.SRr_bind.
    { apply BA; clear BA.
      - exact HJ'.
      - exact (w2_arodataS cx _ _ _ _ _ _ _ HB HJ').
      - rewrite R1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
      - unfold Reusable.YG0d.raZ. rewrite R1, Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
      - rewrite R3, H3. exact Hgp0.
      - rewrite R4. exact H4.
      - reflexivity.
      - reflexivity.
      - rewrite R12. exact H22.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite HspR. exact Hsp16.
      - rewrite HspR, HSTK. unfold Reusable.YCfn.LLVMF_STK. lia.
      - rewrite HspR. lia.
      - rewrite Hfrs. vm_compute. reflexivity.
      - rewrite Hfrs. vm_compute. reflexivity.
      - unfold B.ACtlCutP.SM.OUR. rewrite length_map, length_seq. reflexivity.
      - apply (w2_garr8_of_bytes W3 mem3 _ _ HOUR). intros i Hi. apply FRV.
        unfold B.ACtlCutP.SM.OUR in Hi. rewrite length_map, length_seq in Hi. lia.
      - apply RAF; [lia | lia | lia | exact HA2624].
      - apply HUL; lia.
      - apply (Reusable.YG0f.in_app_sub _ _ _ _ Hfapp); lia.
      - apply FHOME; lia.
      - apply FAPP; lia.
      - apply FAPP; lia.
      - unfold lib.Prog.RcLay.ly_dj. right. rewrite HspR, HSTK. lia.
      - reflexivity.
      - apply (w2_garr8_of_bytes W3 mem3 _ _ HBOX6). intros i Hi. apply VI.
        unfold B.ACtlCutP.SM.BOXA in *. change (length B.ACtlCutP.SM.box6) with 6%nat in Hi. lia.
      - exact (proj1 (ctl_box_view _ _ _ _ _ HAR')).
      - exact (proj2 (ctl_box_view _ _ _ _ _ HAR')).
      - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, B.ACtlCutP.SM.BOXA. lia.
      - left. unfold lib.Prog.RcLay.ly_dj. right.
        pose proof (B.ProgWorld_Fs.pw_F_above B ly3 S3 W3 mem3 md' HAR') as HF.
        unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HF. unfold B.ACtlCutP.SM.BOXA. lia.
      - unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, B.ACtlCutP.SM.BOXA. lia.
      - unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, B.ACtlCutP.SM.BOXA. lia.
      - unfold lib.Prog.RcLay.ly_dj. right. rewrite HspR, HSTK. unfold B.ACtlCutP.SM.BOXA. lia.
      - intros _. split; [exact Hmrow8 |]. split; [lia |]. split; [exact Hmbl |].
        split; [| split].
        + apply (w2_garr8_of_bytes W3 mem3 _ _ HROW6). intros i Hi. apply VI. rewrite Hmbl in Hi. lia.
        + apply (w2_emit_ro_sub _ _ _ _ ctl_cat_ro); unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW,
            B.ACtlCutP.SM.CAT_N; lia.
        + unfold lib.Prog.RcLay.ly_dj. right. rewrite HspR, HSTK. lia.
      - intros _ (Hb56 & Hh & Hr).
        destruct (HNMB (conj Hh Hr)) as (Hok & Hnb & Hna & Hpos).
        pose proof (ctl_names_ro _ Hh Hr) as Hro.
        pose proof Hro as (_ & Hro1 & Hro2 & _).
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Hro1, Hro2.
        split; [exact Hok |]. split; [lia |]. split; [| split; [exact Hro |]].
        + apply (w2_garr8_of_bytes W3 mem3 _ _ Hnb). intros i Hi. apply VI. lia.
        + unfold lib.Prog.RcLay.ly_dj. right. rewrite HspR, HSTK. lia.
      - intros _. lia.
      - intros _. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split; [lia |].
        rewrite Hfa3, <- Hfr6, Hfsb. lia.
      - intros Hok.
        rewrite (w2_ba_ok (B.ACtlCut.c_in cx) (fr + 544) b ltac:(lia) Hb6) in Hok.
        pose proof (w2_rtE_n _ _ Hok) as Hlen.
        unfold B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_len, B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_n.
        change (lib.Prog.RcPorts.bm_uw (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                  (firstn 8 (skipn 16 (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))))
          with (B.ACtlCutP.SM.rt_uw (B.ACtlCut.c_in cx)).
        rewrite <- Hlen. change (B.ACtlCutP.SM.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b).
        assert (Hn52 : 52 <= rnb cx b).
        { unfold rnb. rewrite Hlen. unfold B.ACtlCutP.SM.rt_uw.
          pose proof (w2_bmuw_nonneg (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                        (firstn 8 (skipn 16 (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))))). lia. }
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        + exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split; [lia |].
          intros a Ha. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd].
          rewrite Hfa3, <- Hfr6, Hfsb. lia.
        + intros a Ha. split; [| exact (Hfvis a ltac:(lia))].
          right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia.
        + apply RAF; [lia | lia | lia |]. apply (w2_addr_prefix mem3 (fr + 544) 1492); [exact HOUTA6 | lia].
        + apply HUL; lia.
        + apply FAPP; lia.
        + unfold lib.Prog.RcLay.ly_dj. right. rewrite HspR, HSTK. lia.
        + unfold lib.Prog.RcLay.ly_dj. destruct Hfout as [Hfo | Hfo]; [left | right]; unfold B.ACtlCutP.SM.CAT in *;
            lia.
        + unfold lib.Prog.RcLay.ly_dj. left. lia.
        + unfold lib.Prog.RcLay.ly_dj. destruct Hfout as [Hfo | Hfo]; [left | right]; unfold B.ACtlCutP.SM.BOXA;
            lia.
        + intros (_ & Hh & Hr). pose proof (ctl_names_ro _ Hh Hr) as (_ & Hro1 & Hro2 & _).
          unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Hro1, Hro2.
          unfold lib.Prog.RcLay.ly_dj. destruct Hfout as [Hfo | Hfo]; [left | right]; lia. }
    cbv beta. intros W2 cf Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPR & Hfrs2 & Hbl2 & Ha02 & Hout & HK).
    unfold B.Prog.C_reac_ctrl_build_as.EV_REAC_CTRL_BUILD_AS in HJ2. rewrite Z.add_0_r in HJ2.
    rewrite HspR, HSTK in HK.
    pose proof HJ2 as (HAR2 & _).
    set (Rv := B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_R (fr + 544) (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                 (Z.of_nat b) (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))) in *.
    assert (ERv : Rv = rnb cx b) by (unfold Rv; exact (w2_ba_R (B.ACtlCut.c_in cx) (fr + 544) b ltac:(lia) Hb6)).
    assert (HEs : forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW ->
                    ~ B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_out (fr + 544) Rv a).
    { intros a Ha. unfold B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_out.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
        B.ACtlCutP.FRAME_BYTES in Ha.
      rewrite ERv. lia. }
    destruct (w2_acall_keeps cx fr k sp ly3 S3 W3 mem3 md' ly2 S2 W2 mem2 md2 _ _ (sp - 4640) sp
                (B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_out (fr + 544) Rv)
                HB HJ' Hfrs Hfr6 (proj1 Hspr) Hsp4 ltac:(lia) HK Hwle HJ2 HEs HRT)
      as (KH & KFW0 & KS & KTBL & KROW & KBOX & KNM & HRT2).
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> (hi <= fr + 544 \/ fr + 2036 <= lo) ->
                   KEEPR mem3 mem2 lo hi).
    { intros lo hi L1 L2 L3 a Ha. apply KFW0; [rewrite Hfsb; lia |].
      unfold B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_out. rewrite ERv. lia. }
    (* registers: regs2 keeps RT's callee-saved registers *)
    assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                  lib.Reusable.YK11.getr RT r = lib.Reusable.YK11.getr regs3 r ->
                  lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
      by (intros z r Hz' Er' E; exact (w2_pres_reg RT regs2 regs3 z r HPR Hz' Er' E)).
    assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
      by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
    assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact R2]).
    assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact R3]).
    assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact R4]).
    assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact R8]).
    assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact R9]).
    assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact R19]).
    assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
      by (apply (G 21); [apply CS; lia | apply bv_eq; reflexivity | exact R21]).
    assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact R22]).
    assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
      by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact R23]).
    assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact R25]).
    assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact R26]).
    assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact R27]).
    (* memory: FRAC, RBE, the frame records *)
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 mem2).
    { apply (w2_frac_mem cx fr fr regs3 mem3 mem2); [| apply KF; lia | exact KS | apply KF; lia | exact HFRAC].
      intros a Ha _. rewrite Hspz in Ha. apply KH. lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 mem2).
    { apply (w2_rbe_mem cx fr regs3 mem3 mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia)
               (fun a Ha => KH a ltac:(lia)) (fun a Ha _ => KS a Ha) KTBL KBOX KROW).
      - exact KNM.
      - exact HRBE. }
    assert (KOUTA : B.AsanRT.addressable mem2 (fr + 544) 1492).
    { apply (w2_addr_keep mem3); [| exact HOUTA6]. intros i Hi. apply KS.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES. lia. }
    assert (KA2624 : B.AsanRT.addressable mem2 (fr + 2624) 6).
    { apply (w2_addr_keep mem3); [| exact HA2624]. intros i Hi. apply KS.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES. lia. }
    rewrite R1.
    apply (H710 cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 (eq_trans Hfrs2 Hfrs) Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81710_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81710_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      split; [exact (Permutation_trans Hbl2 Hperm) |].
      split; [exact (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26 HFRAC2) |].
      exists A.
      split; [exact Hcn |]. split; [exact Hb6 |]. split; [unfold B.ACtlK.ANMAX; lia |].
      split; [unfold B.ACtlK.a_size; lia |]. split; [lia |].
      split; [exact (w2_rgv_move regs2 regs3 9 A F9 H9) |].
      split; [exact (w2_rgv_move regs2 regs3 21 _ F21 H21) |].
      split; [unfold B.ACtlCut.a0v, B.ACtlCut.rgv; rewrite Ha02, ERv; reflexivity |].
      split; [eapply w2_bytes_keep; [| exact Q128]; intros a Ha; rewrite lib.Lib.Mem.length_le8 in Ha;
              apply KH; lia |].
      split; [exact (w2_rbe_regs cx fr regs3 regs2 mem2 F9 HRBE2) |].
      split; [unfold B.ACtlCutP.IDBr in *; eapply w2_bytes_keep; [| exact HIDB];
              apply KF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia |].
      split; [unfold B.ACtlCutP.FGBr in *; eapply w2_bytes_keep; [| exact HFGB];
              apply KF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)); lia |].
      split.
      { intros Hn0.
        pose proof (w2_rtn_E _ _ Hn0) as HE.
        assert (Hok : B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_ok (fr + 544)
                        (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx)) (Z.of_nat b)
                        (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) = true)
          by (rewrite (w2_ba_ok (B.ACtlCut.c_in cx) (fr + 544) b ltac:(lia) Hb6); exact HE).
        destruct (Hout Hok) as (Hg & _).
        assert (Efr : lib.Prog.RcEmit.em_fr (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx)) B.ACtlCutP.SM.box6
                        (bv_unsigned (lib.Reusable.YK11.getr RT 15) mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234)
                        (B.ACtlCutP.BAP.ba_X (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                           (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))
                           (Z.of_nat b))
                        (B.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_len (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                           (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))) =
                      B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b)).
        { unfold B.ACtlCutP.SM.rt_F, B.ACtlCutP.SM.rt_X.
          rewrite (w2_rtE_n _ _ HE). rewrite R15. reflexivity. }
        rewrite Efr in Hg.
        pose proof (proj2 (proj2 (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hn0))) as HlF.
        change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in HlF.
        apply (w2_bytes_of_garr8 W2 mem2 _ _); [lia | rewrite HlF, Z2Nat.id by lia; lia | | exact Hg].
        intros i Hi. rewrite HlF, Z2Nat.id in Hi by lia.
        destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 (fr + 544 + i))) eqn:Eh; [| reflexivity].
        pose proof Hwle as Hwle'. unfold Reusable.YA0n.wle, Reusable.YA0i.hsub in Hwle'.
        pose proof (Hwle' _ Eh) as E3. rewrite (FRV (fr + 544 + i) ltac:(lia)) in E3. discriminate. }
      split; [exact (w2_rgv_move regs2 regs3 22 _ F22 H22) |].
      split; [unfold B.ACtlCutP.OURb in *; eapply w2_bytes_keep; [| exact HOUR];
              apply KF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia |].
      split; [exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR) |].
      split; [exact KOUTA |].
      split.
      { intros _. split; [exact KOUTA |]. split; [exact KA2624 |].
        split; [exact (w2_bytes_keep _ _ _ _ KTBL HTBL6) |].
        split; [exact (w2_bytes_keep _ _ _ _ KBOX HBOX6) |].
        split; [exact (w2_bytes_keep _ _ _ _ KROW HROW6) |].
        intros (_ & Hh & Hr). destruct (HNMB (conj Hh Hr)) as (Hok & Hnb & _ & Hpos).
        split; [exact Hok |]. split; [exact (w2_bytes_keep _ _ _ _ (proj1 (KNM Hh Hr)) Hnb) |].
        split; [exact (ctl_names_addressable _ _ _ _ _ _ HAR2 Hh Hr) | exact Hpos]. }
      exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
    + exact HRT2.
Qed.

(* B81710_at b (Inv_B81710_at SIv:1755) -> B81764_at b, B81ac0_at b.  S_R7 (Slot.v:70; seg_R7 R7.v:790), 0x81710 ..
   the malloc.  Split on n = rnb cx b (a0v regs (rnb cx b)):
   - n <> 0: r7_evt_F (0x81710 -> 0x534b8, ra = 0x81764, a0 = s2 = n; source R7.v:144: premises a0 = n, s5 = 36
     (rgv regs 21 36), r7_nv n (rnb's 20 values, SlotModel.v:80 rt_n with u even, 2 <= u <= 40), ro_cells (s1 + 128)
     0xe38f0000 (q64 m (A + 128) 0xe38f0000)); memory unchanged; then w2_malloc_81760 with o = sp - c_sp (FRAC:
     c_sp - 4096 < sp <= A, A + 448 <= c_sp, sp mod 16 = 0 and c_sp mod 16 = 0 from afn_pre), gp / tp (FRAC), the
     live list (body: Permutation bl ENTRYBL) and CHAIN_OF_CUT at (pc_malloc_ra0, 0x81764).  Post -> C_B81764_at body
     with phi := res: Permutation (from the site lemma), a0v regs phi, HB m phi n (phi <> 0 from 4096 <= res;
     addressable phi (a_size n) from the core's AR_shadow_law block_shadow (T5)), rgv 18 n (aregs_preserved s2),
     the frame / spill facts by ctl_post_acall_kept (E = the new block (res, rnb cx b), [slo, shi) = [sp - ASTACK,
     sp); each cut cell is of a kept class: the spills are high memory outside the window, the fake frame's bytes and
     shadow are a live frame's, the catalogue row and the name bytes are non-owned image), ctl_rt by ctlrt_of_AR (M4), event
     bound k + 1 <= 2b + 1.
   - n = 0: r7_evt0_F (0x81710 -> 0x81ac0; source R7.v:165, premise a0 = 0); memory and registers kept; C_B81ac0_at
     body from C_B81710_at's, with R6X cx (S b) from the conjunct (rnb cx b = 0 -> R6X cx (S b) fr regs m) and IDBr /
     FGBr at turn S b equal to turn b's when n = 0 (SlotModel RID / RFG: the turn is skipped).
   No trap. *)
Lemma seg_R7 : forall POST (b : nat), CFb POST C81764 b -> CFb POST C81ac0 b -> CFb POST C81710 b.
Proof.
  intros POST b H64 Hac cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B81710_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (Hperm & HFRAC & A & Hcn & Hb & Hn & Hasz & HA & H9 & H21 & Ha0 & H128 & HRBE & HID & HFG & HF544 &
                     H22 & HOUR & HCUR & HOUTA & HR6X & H27).
  destruct (Z.eq_dec (rnb cx b) 0) as [Hz | Hnz].
  - (* n_b = 0: R7F.r7_evt0_F, 0x81710 -> 0x81ac0, the registers and the memory kept. *)
    eapply w2_lift.
    + unfold Lib.Regs6ss.mkR_of. apply (B.Prog.Seg.R7F.r7_evt0_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      unfold B.ACtlCut.a0v in Ha0. rewrite Hz in Ha0. exact Ha0.
    + apply B.ProgBridge.fp_avoids_RNG_W.
    + intros ms' md' (R & -> & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR22 & HR23 & HR24 & HR25 & HR26 & HR18 &
                      HR27) _ Hsbm.
      apply w2_cfg_back.
      apply (Hac cx [Z.of_nat b] fr k ly3 S3 W3 R mem3 md' HB (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) Hfrs Hfa).
      * unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81ac0_at, B.ACtlCutP.ixn.
        cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
      * unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81ac0_at, B.ACtlCutP.ixn.
        cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
        assert (ERID : B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) (S b) = B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) b).
        { unfold B.Prog.SlotModel.RID. rewrite (B.Prog.Seg.R7.r7_st_skip (B.ACtlCut.c_in cx) b Hz). reflexivity. }
        assert (ERFG : B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) (S b) = B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) b).
        { unfold B.Prog.SlotModel.RFG. rewrite (B.Prog.Seg.R7.r7_st_skip (B.ACtlCut.c_in cx) b Hz). reflexivity. }
        refine (conj Hperm (conj _ (conj Hcn (conj Hb (conj _ (conj _ (conj HOUR (conj _ (conj _ (conj _ (conj _
                  (conj (HR6X Hz) _)))))))))))).
        -- exact (w2_frac_regs cx fr fr regs3 R mem3 HR2 HR3 HR4 HR8 HR9 HR19 HR26 HFRAC).
        -- exact (w2_rgv_move R regs3 22 _ HR22 H22).
        -- exact (w2_cur_regs cx 7 regs3 R HR23 HR25 HCUR).
        -- rewrite ERID. exact HID.
        -- rewrite ERFG. exact HFG.
        -- exact (w2_rbe_regs cx fr regs3 R mem3 HR9 HRBE).
        -- exact (w2_rgv_move R regs3 21 _ HR21 H21).
        -- exact (w2_rgv_move R regs3 27 _ HR27 H27).
      * exact HRT.
  - (* n_b <> 0: R7F.r7_evt_F, 0x81710 -> the malloc wrapper (memory kept), then the site lemma w2_malloc_81760;
       after it, the successor body over the allocator's post: registers by aregs_preserved, memory by the kept
       classes of ctl_post_acall_kept (stack above sp, the fake frame and its shadow, the catalogue's read-only data
       by ctl_relro_not_owned), ro_agree for read-only image bytes, ctl_names_addressable, the new block's shadow by
       w2_block_addressable, ctl_rt by ctlrt_of_AR. *)
    pose proof (B.Prog.Seg.R7.r7_rnb_nv (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as HNV.
    pose proof (B.Prog.Seg.R7.r7_nv_range _ HNV) as Hnr.
    change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnr.
    pose proof HFRAC as (A' & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9' & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                         HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & _ & HSAVE & _).
    pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr. unfold B.AsanRT.APPMEM_END in HcAPP.
    assert (EA : A' = A) by (apply (w2_rgv_eq regs3 9); [exact H9' | exact H9 | lia | exact HA]). subst A'.
    pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
    pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
    destruct Hstk as (Hc16 & _ & Hceil & Hstklo & Hstkhi & H47 & _).
    pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
    unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
    assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
      by (apply Hfa; left; reflexivity).
    pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
    assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
    assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
      as (_ & Happ3 & Hfb3 & Hfs3).
    rewrite Hfa3, <- Hfr6, Hfsb in Happ3, Hfb3, Hfs3.
    eapply w2_lift.
    + unfold Lib.Regs6ss.mkR_of.
      eapply (B.Prog.Seg.R7F.r7_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      * exact Ha0.
      * exact H21.
      * exact HNV.
      * match goal with |- context [bv_unsigned ?x + 128] =>
          replace (bv_unsigned x) with A by (symmetry; exact (w2_rgv_unsigned regs3 9 A H9 HA)) end.
        apply B.Prog.Seg.R7.r7_ro8. exact H128.
      * match goal with |- context [bv_unsigned ?x + 128] =>
          replace (bv_unsigned x) with A by (symmetry; exact (w2_rgv_unsigned regs3 9 A H9 HA)) end.
        apply B.ProgBridge.rng_of_visible.
        apply (w2_vis_stack cx _ _ _ _ _ _ _ _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    + apply B.ProgBridge.fp_avoids_RNG_W.
    + intros ms' md' (R & -> & HRa & HR10 & HR18 & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR22 & HR23 & HR24 &
                      HR25 & HR26 & HR27) _ Hsbm.
      apply w2_cfg_back. change 0x534b8 with Reusable.YB1w.tfib_A_malloc.
      pose proof (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
      assert (E2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact HR2.
      assert (E3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact HR3.
      assert (E4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact HR4.
      assert (E8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact HR8.
      assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact HR9.
      assert (E19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact HR19.
      assert (E21 : lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) by exact HR21.
      assert (E22 : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by exact HR22.
      assert (E23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by exact HR23.
      assert (E25 : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by exact HR25.
      assert (E26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact HR26.
      assert (E27 : lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27) by exact HR27.
      assert (HspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite E2; exact Hspz).
      destruct (CHAIN_OF_CUT cx (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k R
                  (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B)) 0x81764 HB HJ'
                  ltac:(rewrite E8; exact H8) HRa HSAVE ltac:(rewrite HspR; lia) ltac:(rewrite HspR; lia)
                  ltac:(left; reflexivity)) as (ch & Hch & Htr).
      apply (w2_malloc_81760 cx b ly3 S3 W3 R mem3 md' k (sp - B.ACtlCut.c_sp cx) ch (POST cx)
               HB HJ' Hk Hb Hperm HR10).
      * lia.
      * rewrite HspR. lia.
      * lia.
      * lia.
      * rewrite E3, H3. exact Hgp0.
      * rewrite E4. exact H4.
      * exact HRa.
      * exact Hch.
      * exact Htr.
      * intros W2 ly2 S2 regs2 mem2 md2 res Hwle HJ2 HPR Ha02 Hfrs2 H4096 Hperm2 HK.
        pose proof HJ2 as (HAR2 & Hlyle2 & _).
        assert (Hres2 : In (res, rnb cx b) (Reusable.YG0d.ablocks B ly2 S2))
          by (apply (Permutation_in _ (Permutation_sym Hperm2)); apply in_or_app; right; left; reflexivity).
        destruct (Reusable.YG0d.al_blocks segs B LAWS ly2 S2 W2 mem2 md2 res (rnb cx b) HAR2 Hres2)
          as (_ & _ & Hrc & Hrapp & _).
        assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
          by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
        rewrite Er in Hrc, Hrapp.
        pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly2 HAR0 Hlyle2) as (_ & Hfa2 & _).
        assert (Hin62 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfrs2; left; reflexivity).
        pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                      HAR2 Hres2 Hin62) as Hdj.
        rewrite Er, Hfa2, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
        unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
               Reusable.YG0f.ASAN_CEIL in Hrapp, Happ3.
        (* the kept ranges *)
        assert (KH : KEEPR mem3 mem2 sp (B.ACtlCut.c_sp cx)).
        { apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ sp (B.ACtlCut.c_sp cx) HK Hwle); [lia | lia |].
          intros a Ha. split.
          - exact (proj1 (Hwin a ltac:(lia))).
          - left. unfold Reusable.YG0d.ASTACK. lia. }
        assert (KA : KEEPR mem3 mem2 A (A + 448)) by (intros a Ha; apply KH; lia).
        assert (KFW : KEEPR mem3 mem2 fr (fr + Reusable.YG00.fs_frame_bytes 6)).
        { rewrite Hfsb.
          apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ fr (fr + 4096) HK Hwle); [lia | lia |].
          intros a Ha. split.
          - exact (proj1 (proj1 (Hfb3 a ltac:(lia)))).
          - right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split.
            + left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd].
              rewrite Hfa3, <- Hfr6, Hfsb. lia.
            + cbv beta. rewrite Er. lia. }
        assert (KF : KEEPR mem3 mem2 fr (fr + B.ACtlCutP.FRAME_BYTES))
          by (intros a Ha; apply KFW; rewrite Hfsb; unfold B.ACtlCutP.FRAME_BYTES in Ha; lia).
        assert (KT : KEEPR mem3 mem2 (fr + 4088) (fr + 4088 + 8))
          by (intros a Ha; apply KFW; rewrite Hfsb; lia).
        assert (KS : KEEPR mem3 mem2 (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW)).
        { apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle);
            [unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia |
             unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
               B.ACtlCutP.FRAME_BYTES; lia |].
          intros a Ha.
          unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
            B.ACtlCutP.FRAME_BYTES in Ha.
          split.
          - assert (Hi : 0 <= a - Reusable.YG0f.shadow_addr fr < 4096 / 8)
              by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia).
            pose proof (proj1 (proj1 (Hfs3 _ Hi))) as V.
            replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in V by lia.
            exact V.
          - right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split.
            + right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb.
              unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
            + cbv beta. rewrite Er. lia. }
        assert (KTBL : KEEPR mem3 mem2 (B.ACtlCutP.BAC.BA_FR + 72)
                         (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl))).
        { pose proof B.Prog.Seg.R7.r7_tbl_len as Ht.
          apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle);
            [unfold B.ACtlCutP.BAC.BA_FR; lia | rewrite Ht; unfold B.ACtlCutP.BAC.BA_FR; lia |].
          intros a Ha. destruct (ctl_relro_not_owned a (or_introl Ha)) as [Hno Hne].
          rewrite Ht in Ha. unfold B.ACtlCutP.BAC.BA_FR in Ha.
          destruct (img_vis_W W3) as (_ & _ & V). split.
          - apply V. lia.
          - right; right; left. split; [apply w2_in_img; lia | split; assumption]. }
        assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
          by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
        assert (KROW : KEEPR mem3 mem2 (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                         (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) +
                          Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))))).
        { rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
          unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
          apply (w2_kept ly3 S3 W3 W2 mem3 mem2 _ _ _ _ _ HK Hwle); [lia | lia |].
          intros a Ha.
          destruct (ctl_relro_not_owned a) as [Hno Hne].
          { right. unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N. lia. }
          destruct (img_vis_W W3) as (_ & _ & V). split.
          - apply V. lia.
          - right; right; left. split; [apply w2_in_img; lia | split; assumption]. }
        assert (HRT2 : B.ACtlRtC.ctl_rt_C B ly2 S2 mem2) by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ2).
        assert (KBOX : KEEPR mem3 mem2 B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)))
          by exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 w2_box_ro).
        (* registers: regs2 keeps R's callee-saved registers, which are regs3's *)
        assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                      lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs3 r ->
                      lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
          by (intros z r Hz' Er' E; exact (w2_pres_reg R regs2 regs3 z r HPR Hz' Er' E)).
        assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
          by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
        assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
          by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact E2]).
        assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
          by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact E3]).
        assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
          by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact E4]).
        assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
          by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact E8]).
        assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
          by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact E9]).
        assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
          by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact E19]).
        assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
          by (apply (G 21); [apply CS; lia | apply bv_eq; reflexivity | exact E21]).
        assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
          by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact E22]).
        assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
          by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact E23]).
        assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
          by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact E25]).
        assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
          by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact E26]).
        assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
          by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact E27]).
        assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr R 18)
          by (apply (w2_pres_reg R regs2 R 18); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | reflexivity]).
        apply (H64 cx [Z.of_nat b] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2 Hfa).
        -- unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81764_at, B.ACtlCutP.ixn.
           cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. lia.
        -- unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81764_at, B.ACtlCutP.ixn.
           cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
           exists res.
           unfold B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
           refine (conj Hperm2 (conj _ (conj Hcn (conj Hb (conj Hnz (conj Ha02 (conj _ (conj _ (conj _ (conj _
                     (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))).
           ++ apply (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26).
              apply (w2_frac_mem cx fr fr regs3 mem3 mem2);
                [intros a Ha _; apply KH; rewrite Hspz in Ha; exact Ha |
                 intros a Ha; apply KF; unfold B.ACtlCutP.FRAME_BYTES; lia | exact KS | exact KT | exact HFRAC].
           ++ split; [lia |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
              exact (w2_block_addressable _ _ _ _ _ _ _ HAR2 Hres2 ltac:(lia)).
           ++ unfold B.ACtlCut.rgv. rewrite F18. exact HR18.
           ++ apply (w2_rbe_regs cx fr regs3 regs2 mem2 F9).
              apply (w2_rbe_mem cx fr regs3 mem3 mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia) KA
                       (fun a Ha _ => KS a Ha) KTBL KBOX KROW).
              ** intros Hh Hr. split.
                 --- exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 (w2_names_ro _ Hh Hr)).
                 --- exact (ctl_names_addressable _ _ _ _ _ _ HAR2 Hh Hr).
              ** exact HRBE.
           ++ exact (w2_rgv_move regs2 regs3 21 _ F21 H21).
           ++ eapply w2_bytes_keep; [| exact HID]. intros a Ha.
              rewrite B.Prog.Seg.RtmB.rb_RID_len in Ha. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
           ++ eapply w2_bytes_keep; [| exact HFG]. intros a Ha.
              rewrite (B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)) in Ha. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
           ++ pose proof (HF544 Hnz) as HF. eapply w2_bytes_keep; [| exact HF]. intros a Ha.
              destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hr2 & Hl).
              rewrite Hl, Z2Nat.id in Ha by lia. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
           ++ exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
           ++ eapply w2_bytes_keep; [| exact HOUR]. intros a Ha.
              unfold B.ACtlCutP.SM.OUR in Ha. rewrite length_map, length_seq in Ha.
              apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
           ++ exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
           ++ apply (w2_addr_prefix mem2 (fr + 544) 1492); [| lia].
              unfold B.ACtlCutP.OUTA in HOUTA. apply (w2_addr_keep mem3); [| exact HOUTA].
              intros i Hi. apply KS.
              unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES. lia.
           ++ exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
        -- exact HRT2.
Qed.

(* B81764_at b (Inv_B81764_at SIv:1779) -> B8177c_at b.  S_R8 (Slot.v:73; seg_R8 R8.v:783), 0x81764 .. 0x8177c.
   R8F.r8_evt_pre_F (R8F.v:27-38; 0x81764 -> __asan_memcpy entry Reusable.YB1w.tfib_A_asan_memcpy (0x52164 in B),
   ra = 0x8177c; a1 = S = [A + 312], s4 := a0 = phi; premises <- body: a0 = phi (a0v regs phi), 0 < phi < 2^64
   (HB phi <> 0 and al_blocks), 0 <= S < 2^64 and ro_cells (s1 + 312) [C8 S] with S = fr + 544 (RBE spill 312),
   rng RNG (s1 + 312) 8 (V1); source R8.v:59), then the core's memcpy rule AMEMCPY (aintrin_realizes segs B OCpy,
   YG0d.v:318; journal form aj_intrin_at, YCbq.v:1955; never walked here,
   a Theorem Labs lane 22:28Z) with d = phi (a0v regs phi, `mv a0,s4` 0x8176c), x = [A+312] = fr + 544 (RBE spill 312), n =
   s2 = rnb (rgv 18); its premises: the destination block is a tmp block of the journal (awr_byte: in_tmp_block, the
   live list = entry ++ [(phi, n)]), source / destination addressable (HB, OUTA addressable (fr + 544) n),
   disjointness (phi is a heap block, fr + 544 a fake-frame byte: al_sep / sep_block_frame), shadow hull visible (V4).
   Return pc 0x8177c = the successor cut.  R8F.r8_evt_post_F (R8F.v:49-68, 0 steps; raw munch premise) is NOT
   applied: AMEMCPY's post (aj_intrin_at, YCbq.v:1955-1977) is the visible view only, so the raw facts at the cut come
   from ProgWorld's ctl_post_memcpy (section 2; munch_vis / wmono_vis / rw_cells phi [CB n src]).  Post -> C_B8177c_at
   body: rgv 20 phi (s4 = phi, callee-saved), bytes_at
   phi (rt_F ..) (the copy of out[]: aj_intrin_at's view equation, bytes_at (fr + 544) rt_F from the body), spill 184
   (fr + 2368) and addressable (fr + 2256) 72 (RBE), the rest kept; journal k unchanged (an intrinsic is not an
   allocator event).  No trap. *)
Lemma seg_R8 : forall POST (b : nat), CFb POST C8177c b -> CFb POST C81764 b.
Proof.
  intros POST b H7c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B81764_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb & Hnz & Ha0 & HHB & H18 & HRBE & H21 & HID & HFG & HF544 & H22 &
                     HOUR & HCUR & HADF & H27).
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & _ & HSAVE & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (Hc16 & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  pose proof (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnr & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnr, HlF.
  (* the turn block (live, apart from the frame, in application memory, off the image) *)
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & Hp4 & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happ3 & Hfb3 & Hfs3).
  rewrite Hfa3, <- Hfr6, Hfsb in Happ3, Hfb3, Hfs3.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Hfc & _).
  rewrite Hfa3, <- Hfr6, Hfsb in Hfc.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp, Happ3.
  pose proof (Reusable.YG0d.al_client_img segs B LAWS ly3 S3 W3 mem3 md3) as Hcli.
  (* the spills the run and the copy read *)
  pose proof HRBE as (_ & S312 & _ & _ & _ & _ & _ & S184 & _).
  pose proof (w2_spill_at regs3 mem3 A 312 (fr + 544) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S312) as Q312.
  eapply w2_lift.
  - unfold Lib.Regs6ss.mkR_of.
    eapply (B.Prog.Seg.R8F.r8_evt_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi (fr + 544)).
    + exact Ha0.
    + lia.
    + lia.
    + match goal with |- context [bv_unsigned ?x + 312] =>
        replace (bv_unsigned x) with A by (symmetry; exact (w2_rgv_unsigned regs3 9 A H9 ltac:(lia))) end.
      apply B.Prog.Seg.R7.r7_ro8. exact Q312.
    + match goal with |- context [bv_unsigned ?x + 312] =>
        replace (bv_unsigned x) with A by (symmetry; exact (w2_rgv_unsigned regs3 9 A H9 ltac:(lia))) end.
      apply B.ProgBridge.rng_of_visible.
      apply (w2_vis_stack cx _ _ _ _ _ _ _ _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' -> _ Hsbm.
    apply w2_cfg_back. change 0x52164 with Reusable.YB1w.tfib_A_asan_memcpy.
    match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (RT := R) end.
    pose proof (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
    assert (R1 : lib.Reusable.YK11.getr RT 1 = Z_to_bv 64 0x8177c) by reflexivity.
    assert (R2 : lib.Reusable.YK11.getr RT 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
    assert (R3 : lib.Reusable.YK11.getr RT 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
    assert (R4 : lib.Reusable.YK11.getr RT 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
    assert (R8 : lib.Reusable.YK11.getr RT 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
    assert (R9 : lib.Reusable.YK11.getr RT 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
    assert (R10 : lib.Reusable.YK11.getr RT 10 = lib.Reusable.YK11.getr regs3 10) by reflexivity.
    assert (R11 : lib.Reusable.YK11.getr RT 11 = Z_to_bv 64 (fr + 544)) by reflexivity.
    assert (R12 : lib.Reusable.YK11.getr RT 12 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
    assert (R18 : lib.Reusable.YK11.getr RT 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
    assert (R19 : lib.Reusable.YK11.getr RT 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
    assert (R20 : lib.Reusable.YK11.getr RT 20 = lib.Reusable.YK11.getr regs3 10) by reflexivity.
    assert (R21 : lib.Reusable.YK11.getr RT 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
    assert (R22 : lib.Reusable.YK11.getr RT 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
    assert (R23 : lib.Reusable.YK11.getr RT 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
    assert (R25 : lib.Reusable.YK11.getr RT 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
    assert (R26 : lib.Reusable.YK11.getr RT 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
    assert (R27 : lib.Reusable.YK11.getr RT 27 = lib.Reusable.YK11.getr regs3 27) by reflexivity.
    assert (HspR : Reusable.YG0d.spZ RT = sp) by (unfold Reusable.YG0d.spZ; rewrite R2; exact Hspz).
    (* the frame source's shadow is visible *)
    assert (VS : forall s, Reusable.YG0f.shadow_addr fr <= s < Reusable.YG0f.shadow_addr fr + 512 ->
                   Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 s).
    { intros s Hs. assert (Hi : 0 <= s - Reusable.YG0f.shadow_addr fr < 4096 / 8) by lia.
      pose proof (proj1 (Hfs3 _ Hi)) as V.
      replace (Reusable.YG0f.shadow_addr fr + (s - Reusable.YG0f.shadow_addr fr)) with s in V by lia. exact V. }
    unfold Reusable.YG0d.cfg_at, Reusable.YG0d.w64.
    eapply Reusable.YA0n.SRr_bind.
    { eapply (Reusable.YCbq.aj_intrin_at segs B LAWS w2_segs_low Reusable.YG0d.OCpy Reusable.YB1w.tfib_A_asan_memcpy
                AMEMCPY W3 RT mem3 Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
                (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
                (own6 cx) ly3 S3 md' k phi (fr + 544) (rnb cx b) (sp - B.ACtlCut.c_sp cx) (Z_to_bv 64 0x8177c) HJ').
      - rewrite R10. exact Ha0.
      - exact R11.
      - rewrite R12. exact H18.
      - lia.
      - lia.
      - lia.
      - rewrite HspR. lia.
      - lia.
      - lia.
      - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
      - rewrite R3, H3. exact Hgp0.
      - rewrite R4. exact H4.
      - exact R1.
      - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
      - intros a Ha. split.
        + right; right; left. exists phi, (rnb cx b). split; [exact Hin3 |]. split.
          * exact (w2_phi_not_entry _ _ _ _ _ _ _ _ _ _ HJ Hperm).
          * rewrite Er. lia.
        + unfold Reusable.YG0d.ESTACK. lia.
      - apply (Reusable.YCbq.amem_range_of_block segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b)); [exact HAR3 | exact Hin3 | lia | rewrite Er; lia].
      - apply (Reusable.YCbq.range_addressable_of_block segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b));
          [exact HAR3 | exact Hin3 | lia | rewrite Er; lia].
      - intros _. destruct (Reusable.YG0d.al_shadow segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3) as [_ Hh].
        rewrite Er in Hh. exact Hh.
      - split; [lia |]. split; [lia |]. split; [| split; [| split; [| split]]].
        + intros a Ha. split.
          * apply w2_aview_of_apresent. exact (proj1 (Hfb3 a ltac:(lia))).
          * rewrite HspR. unfold Reusable.YG0d.ESTACK. lia.
        + lia.
        + unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd.
          lia.
        + apply w2_range_addr_of_raw; [exact HADF |]. intros i Hi.
          refine (proj1 (VS _ _)).
          unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
        + intros _ s Hs. apply w2_aview_of_apresent. apply VS.
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. lia. }
    cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & Ha02 & Hcopy & Hfr & Hpres).
    pose proof HJ2 as (HAR2 & _).
    assert (HRT2 : B.ACtlRtC.ctl_rt_C B ly3 S3 mem2) by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ2).
    (* the raw memory after the copy *)
    assert (P4 : Z.of_nat (length (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b))) = rnb cx b)
      by (rewrite HlF; apply Z2Nat.id; lia).
    assert (P5 : forall a, phi <= a < phi + rnb cx b -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a)
      by (intros a Ha; exact (proj1 (Hpbytes a Ha))).
    assert (P7 : forall i, 0 <= i < rnb cx b -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (fr + 544 + i)) = false)
      by (intros i Hi; exact (proj1 (proj1 (Hfb3 (fr + 544 + i) ltac:(lia))))).
    assert (P9 : rt_post_frame W3 mem3 mem2 ((phi, phi + rnb cx b) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil)).
    { split.
      - intros a Ha (Ho1 & Ho2 & _). apply Hfr; [exact Ha | exact Ho1 |]. unfold Reusable.YG0d.ESTACK in *. lia.
      - exact Hpres. }
    pose proof (ctl_post_memcpy W3 mem3 mem2 sp phi (fr + 544) (rnb cx b) _ ltac:(lia) ltac:(lia) ltac:(lia)
                  P4 P5 HF544 P7 Hcopy P9) as (MV & _ & HRW).
    assert (MK : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
                   (forall a, lo <= a < hi -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
                      ~ (phi <= a < phi + rnb cx b) /\ ~ (sp - Reusable.YG0d.ESTACK <= a < sp)) ->
                   KEEPR mem3 mem2 lo hi).
    { intros lo hi Hlo Hhi K. apply (w2_munch_keep _ _ _ _ lo hi MV Hlo Hhi).
      intros a Ha. destruct (K a Ha) as (V & O1 & O2). split; [exact V |]. cbn [lib.Lib.Frame.outside]. tauto. }
    destruct (img_vis_W W3) as (_ & _ & VI).
    assert (Hoff_img : forall a, Reusable.YG0d.in_img segs a -> ~ (phi <= a < phi + rnb cx b)).
    { intros a Hia Ha.
      assert (Hblk : exists p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) /\ p <= a < p + Reusable.YG00.req_size n)
        by (exists phi, (rnb cx b); split; [exact Hin3 | rewrite Er; exact Ha]).
      exact (proj2 (Hcli a HAR3 (or_introl Hblk)) Hia). }
    assert (KH : KEEPR mem3 mem2 sp (B.ACtlCut.c_sp cx)).
    { apply MK; [lia | lia |]. intros a Ha. split; [exact (proj1 (Hwin a ltac:(lia))) |].
      unfold Reusable.YG0d.ESTACK. lia. }
    assert (KA : KEEPR mem3 mem2 A (A + 448)) by (intros a Ha; apply KH; lia).
    assert (KFW : KEEPR mem3 mem2 fr (fr + 4096)).
    { apply MK; [lia | lia |]. intros a Ha. split; [exact (proj1 (proj1 (Hfb3 a Ha))) |].
      unfold Reusable.YG0d.ESTACK. lia. }
    assert (KF : KEEPR mem3 mem2 fr (fr + B.ACtlCutP.FRAME_BYTES))
      by (intros a Ha; apply KFW; unfold B.ACtlCutP.FRAME_BYTES in Ha; lia).
    assert (KT : KEEPR mem3 mem2 (fr + 4088) (fr + 4088 + 8)) by (intros a Ha; apply KFW; lia).
    assert (KS : KEEPR mem3 mem2 (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW)).
    { apply MK;
        [unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia |
         unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
           B.ACtlCutP.FRAME_BYTES; lia |].
      intros a Ha.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
        B.ACtlCutP.FRAME_BYTES in Ha.
      split; [apply (proj1 (VS a ltac:(unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia))) |].
      unfold Reusable.YG0d.ESTACK. lia. }
    assert (KTBL : KEEPR mem3 mem2 (B.ACtlCutP.BAC.BA_FR + 72)
                     (B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl))).
    { pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
      apply MK; [lia | lia |]. intros a Ha.
      assert (Hia : Reusable.YG0d.in_img segs a) by (apply w2_in_img; lia).
      split; [apply VI; lia |]. split; [exact (Hoff_img a Hia) |]. unfold Reusable.YG0d.ESTACK. lia. }
    assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
      by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
    assert (KROW : KEEPR mem3 mem2 (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx))
                     (B.ACtlCutP.SM.mrow (B.ACtlCut.c_in cx) +
                      Z.of_nat (length (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx))))).
    { rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
      unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
      apply MK; [lia | lia |]. intros a Ha.
      assert (Hia : Reusable.YG0d.in_img segs a) by (apply w2_in_img; lia).
      split; [apply VI; lia |]. split; [exact (Hoff_img a Hia) |]. unfold Reusable.YG0d.ESTACK. lia. }
    assert (KBOX : KEEPR mem3 mem2 B.ACtlCutP.SM.BOXA (B.ACtlCutP.SM.BOXA + Z.of_nat (length B.ACtlCutP.SM.box6)))
      by exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 w2_box_ro).
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 mem2).
    { apply (w2_rbe_mem cx fr regs3 mem3 mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia) KA (fun a Ha _ => KS a Ha) KTBL
               KBOX KROW).
      - intros Hh Hr. split.
        + exact (w2_kept_ro mem3 mem2 _ _ HRT HRT2 (w2_names_ro _ Hh Hr)).
        + exact (ctl_names_addressable _ _ _ _ _ _ HAR2 Hh Hr).
      - exact HRBE. }
    (* registers: regs2 keeps RT's callee-saved registers *)
    assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                  lib.Reusable.YK11.getr RT r = lib.Reusable.YK11.getr regs3 r ->
                  lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
      by (intros z r Hz' Er' E; exact (w2_pres_reg RT regs2 regs3 z r HPR Hz' Er' E)).
    assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
      by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
    assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact R2]).
    assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact R3]).
    assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact R4]).
    assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact R8]).
    assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact R9]).
    assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
      by (apply (G 18); [apply CS; lia | apply bv_eq; reflexivity | exact R18]).
    assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact R19]).
    assert (F20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 10)
      by (rewrite <- R20; apply (w2_pres_reg RT regs2 RT 20); [exact HPR | apply CS; lia | apply bv_eq; reflexivity | reflexivity]).
    assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
      by (apply (G 21); [apply CS; lia | apply bv_eq; reflexivity | exact R21]).
    assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact R22]).
    assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
      by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact R23]).
    assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact R25]).
    assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact R26]).
    assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact R27]).
    pose proof (w2_rbe_regs cx fr regs3 regs2 mem2 F9 HRBE2) as HRBE3.
    pose proof HRBE3 as (_ & _ & _ & _ & _ & _ & _ & S184' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                         _ & _ & _ & _ & _ & _ & _ & _ & A2256 & _).

    apply (H7c cx [Z.of_nat b] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfrs Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B8177c_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B8177c_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi.
      unfold B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
      refine (conj Hperm (conj _ (conj Hcn (conj Hb (conj _ (conj _ (conj _ (conj _ (conj HRBE3 (conj _
                (conj Hnz (conj _ (conj _ (conj S184' (conj _ (conj _ (conj _ (conj A2256 _)))))))))))))))))).
      * apply (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26).
        apply (w2_frac_mem cx fr fr regs3 mem3 mem2);
          [intros a Ha _; apply KH; rewrite Hspz in Ha; exact Ha |
           intros a Ha; apply KF; unfold B.ACtlCutP.FRAME_BYTES; lia | exact KS | exact KT | exact HFRAC].
      * split; [lia |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR2 Hin3 ltac:(lia)).
      * exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
      * eapply w2_bytes_keep; [| exact HOUR]. intros a Ha.
        unfold B.ACtlCutP.SM.OUR in Ha. rewrite length_map, length_seq in Ha.
        apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
      * exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
      * exact (w2_rgv_move regs2 regs3 21 _ F21 H21).
      * unfold B.ACtlCut.rgv. rewrite F20. exact Ha0.
      * exact (w2_rgv_move regs2 regs3 18 _ F18 H18).
      * eapply w2_bytes_keep; [| exact HID]. intros a Ha.
        rewrite B.Prog.Seg.RtmB.rb_RID_len in Ha. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
      * eapply w2_bytes_keep; [| exact HFG]. intros a Ha.
        rewrite (B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)) in Ha. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
      * destruct HRW as [(_ & Hcb) _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hcb.
        rewrite app_nil_r in Hcb. exact Hcb.
      * exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
    + exact HRT2.
Qed.

(* B8177c_at b (Inv_B8177c_at SIv:1796) -> B817a4_at b.  S_R9 (Slot.v:75; seg_R9 R9.v:919), 0x8177c .. 0x817a4.
   R9F.r9_st_F (R9F.v:49-65; 0x8177c -> 0x81794; source R9.v:74: rw_cells (s3 + 296) [CB 5 junk] -- s3 = Sfr fr
   (FRAC rgv 19), the frame's shadow bytes 296..300 (V5), mem_inv (ctl_rt), rng RNG (s3 + 296) 5 (V5); post: the
   five shadow bytes 0,0,0,0,4 written, s5 = 4), then R9F.r9_call_pre_F (R9F.v:122-133; 0x81794 -> reac_ctrl_parse
   entry 0x83e04, ra = 0x817a4; a0 = s4 = phi, a1 = s2 = rnb, a2 = o = [A + 184]; premises <- body: 0 <= o < 2^64
   and ro_cells (s1 + 184) [C8 o] with o = fr + 2368 (the cut's spill 184), rng RNG (s1 + 184) 8 (V1); source
   R9.v:107), then reac_ctrl_parse
   (cut-callee, its own stack_malloc_1 at 0x83e74) by its caller-journal spec PARSE (:287; a Theorem Labs lane, treac_ctrl_parse_spec,
   image-A text spec-draft.md:141-157 (a working note, not in this delivery); image-B twin lib/B/Prog/C_reac_ctrl_parse.v:58) with f = phi (s4), n = rnb (s2), o = [A + 184] =
   fr + 2368 (spill 184); the spec's P9-P13 obligations: 50 <= n -> phi readable 50 (HB / bytes_at phi rt_F), the
   output record o writable 36 (fake frame, T8), stack window K (T1).  Return pc 0x817a4 = the successor cut.
   R9F.r9_call_post_F (R9F.v:138-171, 0 steps) is NOT applied (parse is a cut-callee: world-form post).  Post
   -> C_B817a4_at body: a0v regs (rt_k ..) (the parse result, RP.ctrlparse / SM.rt_k), RF (RFx: rnb <> 0, rgv 20 phi,
   bytes_at phi rt_F kept (the callee's write set is o and its window), rgv 18 rnb), rgv 21 4 (s5 = 4 from r9_st),
   the spills, addressable (fr + 2256) 72, and the b = 5 fragment-kind fact from the model (SM.fg_rf, R10.v:9-17).
   No trap. *)
Lemma seg_R9 : forall POST (b : nat), CFb POST C817a4 b -> CFb POST C8177c b.
Proof.
  intros POST b H7a4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B8177c_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hnz & H20 & H18 & S184 &
                     HIDB & HFGB & HFb & HAD2256 & H27).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnr & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnr, HlF.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  pose proof (w2_rgv_unsigned regs3 9 A H9 ltac:(lia)) as U9.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the shadow bytes r9_st_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 296 5 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 296) with 296 in Hjunk.
  assert (Hjl : length (firstn 5 (skipn 296 sh)) = 5%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 296) [lib.Lib.Cells.CB 5 (firstn 5 (skipn 296 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 296 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  (* the spill the call reads *)
  pose proof (w2_spill_at regs3 mem3 A 184 (fr + 2368) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S184) as Q184.
  (* the run: R9F.r9_st_F on the normalized memory (rebase_ro_normalize), then R9F.r9_call_pre_F *)
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x83e04) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x817a4 /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 10 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 11 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (fr + 2368) /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 4 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 296, B.ACtlCutP.Sfr fr + 301)] mem3 m' /\
      exists c0 c1 c2 c3 c4 : byte,
        lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 296) [c0; c1; c2; c3; c4] /\
        bv_signed c0 = 0 /\ bv_signed c1 = 0 /\ bv_signed c2 = 0 /\ bv_signed c3 = 0 /\ bv_signed c4 = 4).
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R9F.r9_st_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (junk := firstn 5 (skipn 296 sh)).
      * match goal with |- context [bv_unsigned ?x + 296] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 296] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & _ & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (s5' & m1 & c0 & c1 & c2 & c3 & c4 & -> & -> & MU1 & _ & _ & Hb5 & V0 & V1 & V2 & V3 & V4).
      match type of MU1 with context [bv_unsigned ?x + 296] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hb5 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      pose proof (proj2 (Hbyt _ _) Hb5) as Hb5'.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es.
      eapply lib.Lib.ExecF.evtF_cut.
      * eapply (B.Prog.Seg.R9F.r9_call_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (o := fr + 2368).
        -- lia.
        -- match goal with |- context [bv_unsigned ?x + 184] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. apply (w2_bytes_keep mem3); [| exact Q184].
           intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha.
           apply (w2_munch_mrd _ mem3 _ a MUc); [lia |].
           cbn [lib.Lib.Frame.outside]. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
           repeat split; lia.
        -- match goal with |- context [bv_unsigned ?x + 184] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
      * intros ms1 ->. apply lib.Lib.ExecF.evtF_done.
        do 2 eexists. split; [reflexivity |].
        repeat (split; [reflexivity |]).
        split; [exact MUc |].
        exists c0, c1, c2, c3, c4. split; [exact Hb5' |]. repeat split; assumption.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & -> & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 & G23 &
                    G25 & G26 & G27 & MUc & (c0 & c1 & c2 & c3 & c4 & Hb5 & V0 & V1 & V2 & V3 & V4)) Hhid Hsbm.
    apply w2_cfg_back.
    (* the raw memory m' keeps every byte off the five shadow bytes *)
    assert (MK : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
                   (forall a, lo <= a < hi -> a < B.ACtlCutP.Sfr fr + 296 \/ B.ACtlCutP.Sfr fr + 301 <= a) ->
                   KEEPR mem3 m' lo hi).
    { intros lo hi Hlo Hhi K. apply (w2_munch_keepr _ mem3 m' lo hi MUc Hlo Hhi).
      intros a Ha. cbn [lib.Lib.Frame.outside]. pose proof (K a Ha). repeat split; lia. }
    (* the journal across the run (it writes the five shadow bytes only) *)
    assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
    { apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
               (fun a => B.ACtlCutP.Sfr fr + 296 <= a < B.ACtlCutP.Sfr fr + 301) HJ).
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MUc x); [reflexivity |].
        cbn [lib.Lib.Frame.outside]. repeat split; lia.
      - intros x Hx. unfold Reusable.YK04.mrestrict in *.
        destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx |].
        pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
        assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
        { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          apply Z.mod_small. exact Hxr. }
        destruct (Z_lt_le_dec (bv_unsigned x) (B.ACtlCutP.Sfr fr + 296)) as [L1 | L1];
          [rewrite (MUc x) by (cbn [lib.Lib.Frame.outside]; repeat split; lia); exact Hx |].
        destruct (Z_lt_le_dec (bv_unsigned x) (B.ACtlCutP.Sfr fr + 301)) as [L2 | L2];
          [| rewrite (MUc x) by (cbn [lib.Lib.Frame.outside]; repeat split; lia); exact Hx].
        assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
        { intros Hi. pose proof (w2_segs_low _ Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl. lia. }
        destruct (w2_ba_rd m' (B.ACtlCutP.Sfr fr + 296) _ (bv_unsigned x) Hb5 ltac:(cbn [length]; lia))
          as (bb & Hbb).
        rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr Hni Hbb). discriminate.
      - exact Hhid.
      - exact Hsbm.
      - intros a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb, <- ESf. lia. }
    assert (HRT' : B.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ').
    pose proof HJ' as (HAR' & _).
    assert (HspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite G2; exact Hspz).
    (* the parse record is addressable after the five shadow bytes *)
    assert (Hrec : B.AsanRT.addressable m' (fr + 2368) 36).
    { apply (w2_rec_addressable m' fr c0 c1 c2 c3 c4); try assumption.
      - lia.
      - lia.
      - unfold B.AsanRT.APPMEM_END. lia.
      - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia. }
    (* the call: reac_ctrl_parse's caller-journal spec *)
    change 0x83e04 with B.Prog.C_reac_ctrl_parse.A_reac_ctrl_parseP.
    eapply Reusable.YA0n.SRr_bind.
    { apply (PARSE Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)
               (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 m' md' k R phi
               (rnb cx b) (fr + 2368) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) HJ').
      - exact (w2_arodataS cx _ _ _ _ _ _ _ HB HJ').
      - rewrite G1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
      - unfold Reusable.YG0d.raZ. rewrite G1, Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
      - rewrite G3, H3. exact Hgp0.
      - rewrite G4. exact H4.
      - rewrite G10. exact H20.
      - rewrite G11. exact H18.
      - exact G12.
      - lia.
      - rewrite HspR. exact Hsp16.
      - rewrite HspR. unfold Reusable.YCfn.LLVMF_STK, B.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK. lia.
      - rewrite HspR. lia.
      - rewrite Hfrs. vm_compute. reflexivity.
      - intros _. exists (rnb cx b). split; [exact Hin3 | rewrite Er; lia].
      - intros _. split; [| split].
        + exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split; [lia |].
          rewrite Hfa3, <- Hfr6, Hfsb. repeat split; lia.
        + lia.
        + apply w2_range_addr_of_raw; [exact Hrec |]. intros i Hi.
          exact (proj1 (Hfsvis (B.AsanRT.shadow_addr (fr + 2368 + i))
                          ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
                                  Reusable.YG0f.SHADOW_OFF; lia))).
      - intros _ a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia.
      - unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite length_firstn, length_app, repeat_length. lia.
      - intros _ i Hi.
        pose proof HFb as (_ & _ & HF3).
        pose proof (HF3 i ltac:(rewrite HlF; lia)) as Ei.
        destruct (nth_error (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b)) i) as [x |] eqn:Ex;
          [| apply nth_error_None in Ex; rewrite HlF in Ex; lia].
        rewrite (aview_vis_mrd W3 m' (phi + Z.of_nat i))
          by exact (proj1 (proj1 (Hpbytes (phi + Z.of_nat i) ltac:(lia)))).
        rewrite (MK (phi + Z.of_nat i) (phi + Z.of_nat i + 1)); [| lia | lia | intros a Ha; lia | lia].
        assert (Ei' : lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (phi + Z.of_nat i)) = Some x)
          by exact Ei.
        rewrite Ei'. cbn [option_map]. f_equal. symmetry.
        exact (w2_cp_v _ i x ltac:(lia) Ex). }
    cbv beta. intros W2 cf Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPR & Hfrs2 & Hbl2 & _ & Ha02 & _ & HK).
    pose proof HJ2 as (HAR2 & _).
    rewrite HspR in HK.
    assert (Hin2 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hbl2; exact Hin3).
    assert (HEs : forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW ->
                    ~ (fr + 2368 <= a < fr + 2368 + 36)).
    { intros a Ha. unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in Ha. lia. }
    destruct (w2_acall_keeps cx fr k sp ly3 S3 W3 m' md' ly2 S2 W2 mem2 md2 _ _
                (sp - B.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK) sp (fun a => fr + 2368 <= a < fr + 2368 + 36)
                HB HJ' Hfrs Hfr6 (proj1 Hspr) Hsp4 ltac:(lia) HK Hwle HJ2 HEs HRT')
      as (KH2 & KFW2 & KS2 & KTBL2 & KROW2 & KBOX2 & KNM2 & HRT2).
    (* keeps from the cut's memory to m' (the munch) and from m' to mem2 (the call) *)
    assert (KF2 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> (hi <= fr + 2368 \/ fr + 2404 <= lo) ->
                    KEEPR m' mem2 lo hi).
    { intros lo hi L1 L2 L3 a Ha. apply KFW2; [rewrite Hfsb; lia | lia]. }
    assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2; apply MK; [lia | lia | intros a Ha; lia]).
    assert (KFF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> (hi <= fr + 2368 \/ fr + 2404 <= lo) ->
                    KEEPR mem3 mem2 lo hi)
      by (intros lo hi L1 L2 L3; exact (w2_keep_trans _ _ _ lo hi (KF1 lo hi L1 L2) (KF2 lo hi L1 L2 L3))).
    (* registers: regs2 keeps R's callee-saved registers *)
    assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs3 r ->
                  lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
      by (intros z r Hz' Er' E; exact (w2_pres_reg R regs2 regs3 z r HPR Hz' Er' E)).
    assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
      by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
    assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact G2]).
    assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact G3]).
    assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact G4]).
    assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact G8]).
    assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact G9]).
    assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
      by (apply (G 18); [apply CS; lia | apply bv_eq; reflexivity | exact G18]).
    assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact G19]).
    assert (F20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
      by (apply (G 20); [apply CS; lia | apply bv_eq; reflexivity | exact G20]).
    assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact G22]).
    assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
      by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact G23]).
    assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact G25]).
    assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact G26]).
    assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact G27]).
    assert (F21 : lib.Reusable.YK11.getr regs2 21 = Z_to_bv 64 4).
    { rewrite <- G21. apply (w2_pres_reg R regs2 R 21); [exact HPR | apply CS; lia | apply bv_eq; reflexivity |
                                                         reflexivity]. }
    (* FRAC and RBE at m' (the five shadow bytes changed), then at mem2 *)
    assert (Hsh' : exists sh', lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr) sh' /\
                     length sh' = Z.to_nat B.ACtlCutP.FRAME_SHADOW).
    { destruct (w2_sh_splice mem3 m' (B.ACtlCutP.Sfr fr) sh c0 c1 c2 c3 c4 Hsh Hshl') as (sh' & Q1 & Q2).
      - intros a Ha Hn. apply (w2_munch_mrd _ mem3 m' a MUc); [lia |].
        cbn [lib.Lib.Frame.outside]. repeat split; lia.
      - exact Hb5.
      - exists sh'. split; [exact Q1 | rewrite Q2; reflexivity]. }
    assert (HFRAC' : B.ACtlCutP.FRAC B cx fr fr regs3 m').
    { apply (w2_frac_mem_sh cx fr fr regs3 mem3 m'); [| | exact Hsh' | | exact HFRAC].
      - intros a Ha _. rewrite Hspz in Ha. apply (MK a (a + 1)); [lia | lia | intros a' Ha'; lia | lia].
      - apply KF1; lia.
      - apply KF1; lia. }
    assert (HRBE' : B.ACtlCutP.RBE cx fr regs3 m').
    { apply (w2_rbe_mem cx fr regs3 mem3 m' A H9 ltac:(lia) ltac:(lia) ltac:(lia)).
      - apply MK; lia.
      - intros a Ha Hn. apply (w2_munch_mrd _ mem3 m' a MUc); [lia |].
        cbn [lib.Lib.Frame.outside]. repeat split; lia.
      - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
        apply MK; [lia | lia |]. intros a Ha. lia.
      - exact (w2_kept_ro mem3 m' _ _ HRT HRT' w2_box_ro).
      - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
          by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
        rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
        unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
        apply MK; [lia | lia |]. intros a Ha. lia.
      - intros Hh Hr. split.
        + exact (w2_kept_ro mem3 m' _ _ HRT HRT' (w2_names_ro _ Hh Hr)).
        + exact (ctl_names_addressable _ _ _ _ _ _ HAR' Hh Hr).
      - exact HRBE. }
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 mem2).
    { apply (w2_frac_mem cx fr fr regs3 m' mem2); [| | exact KS2 | | exact HFRAC'].
      - intros a Ha _. rewrite Hspz in Ha. apply KH2. lia.
      - apply KF2; lia.
      - apply KF2; lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 mem2).
    { apply (w2_rbe_mem cx fr regs3 m' mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia)
               (fun a Ha => KH2 a ltac:(lia)) (fun a Ha _ => KS2 a Ha) KTBL2 KBOX2 KROW2 KNM2 HRBE'). }
    pose proof (w2_rbe_regs cx fr regs3 regs2 mem2 F9 HRBE2) as HRBE3.
    pose proof HRBE3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S24 & S16 & S96 & S120 & _).
    (* the block's bytes: kept by the munch (application memory) and by the call (a live block off its record) *)
    assert (KB : KEEPR mem3 mem2 phi (phi + rnb cx b)).
    { apply (w2_keep_trans _ m').
      - apply MK; [lia | lia |]. intros a Ha.
        unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia.
      - apply (w2_kept ly3 S3 W3 W2 m' mem2 _ _ _ phi (phi + rnb cx b) HK Hwle); [lia | lia |].
        intros a Ha. split; [exact (proj1 (proj1 (Hpbytes a Ha))) |].
        right; left. exists phi, (rnb cx b), (a - phi). split; [exact Hin3 |]. split; [rewrite Er; lia |].
        split; [lia |]. lia. }
    rewrite G1.
    apply (H7a4 cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 (eq_trans Hfrs2 Hfrs) Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B817a4_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B817a4_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi. rewrite Hbl2.
      unfold B.ACtlCutP.RF, B.ACtlCutP.RFx, B.ACtlCutP.RFb, B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr,
        B.ACtlCutP.OURb in *.
      assert (KOUR : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 2624) (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx))).
      { eapply w2_bytes_keep; [| exact HOUR]. apply KFF;
          try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      assert (KCUR : B.ACtlCutP.CUR cx 7 regs2) by exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
      assert (K22 : B.ACtlCut.rgv regs2 22 (Z.of_nat b)) by exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
      refine (conj Hperm (conj _ (conj Hcn (conj Hb6 (conj _ (conj K22 (conj KOUR (conj KCUR (conj HRBE3 (conj _ (conj _
                (conj (conj (conj (conj Hb6 (conj KCUR (conj KOUR (conj K22 (conj _ _))))) (conj Hnz (conj _ _))) _)
                  (conj S24 (conj S16 (conj S96 (conj S120 (conj _ (conj _ _)))))))))))))))))).
      * exact (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26 HFRAC2).
      * split; [exact (proj1 HHB) |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR2 Hin2 ltac:(lia)).
      * unfold B.ACtlCut.rgv. exact F21.
      * unfold B.ACtlCut.a0v, B.ACtlCut.rgv, B.ACtlCutP.SM.rt_k. exact Ha02.
      * eapply w2_bytes_keep; [| exact HIDB]. apply KFF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia.
      * eapply w2_bytes_keep; [| exact HFGB].
        apply KFF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)); lia.
      * exact (w2_rgv_move regs2 regs3 20 _ F20 H20).
      * eapply w2_bytes_keep; [| exact HFb]. rewrite HlF, Z2Nat.id by lia. exact KB.
      * exact (w2_rgv_move regs2 regs3 18 _ F18 H18).
      * apply (w2_addr_keep m'); [| apply (w2_addr_keep mem3); [| exact HAD2256]].
        -- intros i Hi. apply KS2. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW,
             B.ACtlCutP.FRAME_BYTES. lia.
        -- intros i Hi. apply (w2_munch_mrd _ mem3 m' _ MUc).
           ++ unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. lia.
           ++ cbn [lib.Lib.Frame.outside]. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
              repeat split; lia.
      * intros ->. rewrite (w2_rfg_z72 _ 5 ltac:(lia)). apply w2_fgrf_z72.
      * exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
    + exact HRT2.
Qed.

(* ---- S_R10's helpers.  Every arm's head run writes one run of the class-6 frame's shadow inside
   [Sfr fr + 306, Sfr fr + 318) (the reply / ports cells' granules) and nothing else: the journal, ctl_rt_C, FRAC and
   RBE carry across it, and every byte off the run is kept.  The run is [Sfr fr + j, Sfr fr + h), h = j + |l|. *)
Lemma w2_fsh_write : forall (cx : ctlcx) (fr k : Z) ly3 S3 (W3 : Reusable.YA0n.world segs) (regs3 : bvmap 5 word)
    (mem3 m' : word -> option byte) md3 md' (j h : Z) (l : list byte),
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  B.ACtlCutP.FRAC B cx fr fr regs3 mem3 -> B.ACtlCutP.RBE cx fr regs3 mem3 ->
  296 <= j -> h = j + Z.of_nat (length l) -> h <= 318 ->
  lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + j, B.ACtlCutP.Sfr fr + h)] mem3 m' ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + j) l ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx (own6 cx) ly3 S3 W3 m' md' k /\ B.ACtlRtC.ctl_rt_C B ly3 S3 m' /\
  B.ACtlCutP.FRAC B cx fr fr regs3 m' /\ B.ACtlCutP.RBE cx fr regs3 m' /\
  (forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
     (forall a, lo <= a < hi -> a < B.ACtlCutP.Sfr fr + j \/ B.ACtlCutP.Sfr fr + h <= a) -> KEEPR mem3 m' lo hi).
Proof.
  intros cx fr k ly3 S3 W3 regs3 mem3 m' md3 md' j h l HB HJ Hfrs Hfr6 HRT HFRAC HRBE Hj0 Eh Hh1 MUc Hbl Hhid Hsbm.
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof HJ as (HAR3 & Hlyle & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  pose proof (Nat2Z.is_nonneg (length l)) as Hl0.
  assert (MK : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
                 (forall a, lo <= a < hi -> a < B.ACtlCutP.Sfr fr + j \/ B.ACtlCutP.Sfr fr + h <= a) ->
                 KEEPR mem3 m' lo hi).
  { intros lo hi Hlo Hhi K. apply (w2_munch_keepr _ mem3 m' lo hi MUc Hlo Hhi).
    intros a Ha. cbn [lib.Lib.Frame.outside]. pose proof (K a Ha). repeat split; lia. }
  (* the journal across the run (it writes the run's shadow bytes only) *)
  assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
             (fun a => B.ACtlCutP.Sfr fr + j <= a < B.ACtlCutP.Sfr fr + h) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MUc x); [reflexivity |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Eh'; [exact Hx |].
      pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
      assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
      { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        apply Z.mod_small. exact Hxr. }
      destruct (Z_lt_le_dec (bv_unsigned x) (B.ACtlCutP.Sfr fr + j)) as [L1 | L1];
        [rewrite (MUc x) by (cbn [lib.Lib.Frame.outside]; repeat split; lia); exact Hx |].
      destruct (Z_lt_le_dec (bv_unsigned x) (B.ACtlCutP.Sfr fr + h)) as [L2 | L2];
        [| rewrite (MUc x) by (cbn [lib.Lib.Frame.outside]; repeat split; lia); exact Hx].
      assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
      { intros Hi. pose proof (w2_segs_low _ Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl. lia. }
      destruct (w2_ba_rd m' (B.ACtlCutP.Sfr fr + j) _ (bv_unsigned x) Hbl ltac:(lia)) as (bb & Hbb).
      rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr Hni Hbb). discriminate.
    - exact Hhid.
    - exact Hsbm.
    - intros a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb, <- ESf. lia. }
  assert (HRT' : B.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ').
  pose proof HJ' as (HAR' & _).
  (* FRAC: the frame's shadow is the old one with the run spliced in *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  assert (Hsh' : exists sh', lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr) sh' /\
                   length sh' = Z.to_nat B.ACtlCutP.FRAME_SHADOW).
  { destruct (w2_sh_splice_gen mem3 m' (B.ACtlCutP.Sfr fr) sh l (Z.to_nat j) Hsh Hshl' ltac:(lia))
      as (sh' & Q1 & Q2).
    - intros a Ha Hn. rewrite Z2Nat.id in Hn by lia. apply (w2_munch_mrd _ mem3 m' a MUc); [lia |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - rewrite Z2Nat.id by lia. exact Hbl.
    - exists sh'. split; [exact Q1 | rewrite Q2; reflexivity]. }
  assert (HFRAC' : B.ACtlCutP.FRAC B cx fr fr regs3 m').
  { apply (w2_frac_mem_sh cx fr fr regs3 mem3 m'); [| | exact Hsh' | | exact HFRAC].
    - intros a Ha _. rewrite Hspz in Ha. apply (MK a (a + 1)); [lia | lia | intros a' Ha'; lia | lia].
    - apply MK; [lia | lia |]. intros a Ha. lia.
    - apply MK; [lia | lia |]. intros a Ha. lia. }
  assert (HRBE' : B.ACtlCutP.RBE cx fr regs3 m').
  { apply (w2_rbe_mem cx fr regs3 mem3 m' A H9 ltac:(lia) ltac:(lia) ltac:(lia)).
    - apply MK; [lia | lia |]. intros a Ha. lia.
    - intros a Ha Hn. apply (w2_munch_mrd _ mem3 m' a MUc); [lia |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
      apply MK; [lia | lia |]. intros a Ha. lia.
    - exact (w2_kept_ro mem3 m' _ _ HRT HRT' w2_box_ro).
    - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
        by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
      rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
      unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
      apply MK; [lia | lia |]. intros a Ha. lia.
    - intros Hh Hr. split.
      + exact (w2_kept_ro mem3 m' _ _ HRT HRT' (w2_names_ro _ Hh Hr)).
      + exact (ctl_names_addressable _ _ _ _ _ _ HAR' Hh Hr).
    - exact HRBE. }
  split; [exact HJ' |]. split; [exact HRT' |]. split; [exact HFRAC' |]. split; [exact HRBE' | exact MK].
Qed.

(* After the b = 0 head run: the ports slot [fr + 2528, fr + 2540) is addressable (shadow byte 316 = 0 for the first
   granule, 317 = 4 for the next four bytes). *)
Lemma w2_ports_addressable : forall (m : word -> option byte) (fr : Z) (c3 c4 : byte),
  fr mod 8 = 0 -> 0 <= fr -> fr + 2540 <= B.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < 12 -> B.AsanRT.app_mem (fr + 2528 + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.ACtlCutP.Sfr fr + 316) [c3] -> bv_signed c3 = 0 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.ACtlCutP.Sfr fr + 317) [c4] -> bv_signed c4 = 4 ->
  B.AsanRT.addressable m (fr + 2528) 12.
Proof.
  intros m fr c3 c4 Hfr Hfr0 Hfr1 Happ (_ & _ & H3) E3 (_ & _ & H4) E4.
  split; [lia |]. split; [lia |]. split; [lia |].
  intros i Hi. split; [exact (Happ i Hi) |].
  unfold B.AsanRT.shadow_ok.
  destruct (Z_lt_le_dec i 8) as [Hi8 | Hi8].
  - assert (Es : B.AsanRT.shadow_addr (fr + 2528 + i) = B.ACtlCutP.Sfr fr + 316 + Z.of_nat 0)
      by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
    pose proof (H3 0%nat ltac:(cbn [length]; lia)) as Hb. rewrite <- Es in Hb. cbn [nth_error] in Hb.
    eexists. split; [exact Hb |]. left. exact E3.
  - assert (Es : B.AsanRT.shadow_addr (fr + 2528 + i) = B.ACtlCutP.Sfr fr + 317 + Z.of_nat 0)
      by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
    pose proof (H4 0%nat ltac:(cbn [length]; lia)) as Hb. rewrite <- Es in Hb. cbn [nth_error] in Hb.
    eexists. split; [exact Hb |]. right. rewrite E4. split; [| lia]. lia.
Qed.

(* S_R10, b = 0: R10F.r10_cfg0_F, 0x817a4 -> 0x818a8 = C_B818a8_at with i := 0 (no call). *)
Lemma w2_R10_b0 : forall POST (b : nat), b = 0%nat -> CFb POST C818a8 b -> CFb POST C817a4 b.
Proof.
  intros POST b Hb0 H8a8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817a4_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Ha0 & HRF & S24 & S16 &
                     S96 & S120 & HAD2256 & _ & H27).
  subst b.
  destruct HRF as ((HRB & Hnz & H20 & HFb) & H18).
  destruct HRB as (_ & _ & _ & _ & HIDB & HFGB).
  destruct (B.Prog.Seg.R10.r10_rtk (B.ACtlCut.c_in cx) 0 ltac:(lia) Hnz) as (Hk0 & Hn52 & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 0)) with (rnb cx 0) in Hn52, HlF.
  unfold B.ACtlCut.a0v, B.ACtlCut.rgv in Ha0. rewrite Hk0 in Ha0.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HJ as (HAR3 & Hlyle & _).
  assert (Hin3 : In (phi, rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx 0) = rnb cx 0)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx 0 =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the twelve shadow bytes r10_cfg0_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 306 12 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 306) with 306 in Hjunk.
  assert (Hjl : length (firstn 12 (skipn 306 sh)) = 12%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 306) [lib.Lib.Cells.CB 12 (firstn 12 (skipn 306 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 306 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  (* the run: R10F.r10_cfg0_F on the normalized memory (rebase_ro_normalize) *)
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l12 : list byte)
                                            (c3 c4 : byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x818a8) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 36 /\ lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 18) /\
      lib.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\ lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (phi + 18) /\
      lib.Reusable.YK11.getr R 14 = Z_to_bv 64 32 /\ lib.Reusable.YK11.getr R 13 = Z_to_bv 64 (- (phi + 18)) /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 306, B.ACtlCutP.Sfr fr + 318)] mem3 m' /\
      lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 306) l12 /\ length l12 = 12%nat /\
      lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 316) [c3] /\ bv_signed c3 = 0 /\
      lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 317) [c4] /\ bv_signed c4 = 4).
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R10F.r10_cfg0_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (phi := phi) (junk := firstn 12 (skipn 306 sh)).
      * exact H20.
      * exact H21.
      * exact H22.
      * exact Ha0.
      * lia.
      * lia.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & _ & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (R & m1 & l12 & c3 & c4 & -> & G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & _ & G25 & G26 &
                      G21 & G10 & G11 & G12 & G14 & G13 & G18 & G27 & MU1 & _ & _ & Hl12 & Hl12l & Hc3 & V3 & Hc4 &
                      V4).
      match type of MU1 with context [bv_unsigned ?x + 306] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hl12, Hc3, Hc4 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es. apply lib.Lib.ExecF.evtF_done.
      exists R, (ms_mem s), l12, c3, c4. split; [reflexivity |].
      split; [exact G2 |]. split; [exact G3 |]. split; [exact G4 |]. split; [exact G8 |]. split; [exact G9 |].
      split; [exact G19 |]. split; [exact G20 |]. split; [exact G22 |]. split; [exact G23 |].
      split; [exact G25 |]. split; [exact G26 |]. split; [exact G21 |]. split; [exact G10 |].
      split; [exact G11 |]. split; [exact G12 |]. split; [exact G14 |]. split; [exact G13 |].
      split; [exact G18 |]. split; [exact G27 |]. split; [exact MUc |].
      split; [exact (proj2 (Hbyt _ _) Hl12) |]. split; [exact Hl12l |].
      split; [exact (proj2 (Hbyt _ _) Hc3) |]. split; [exact V3 |].
      split; [exact (proj2 (Hbyt _ _) Hc4) | exact V4].
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & l12 & c3 & c4 & -> & G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 &
                    G21 & G10 & G11 & G12 & G14 & G13 & G18 & G27 & MUc & Hl12 & Hl12l & Hc3 & V3 & Hc4 & V4)
      Hhid Hsbm.
    apply w2_cfg_back.
    destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 m' md3 md' 306 318 l12 HB HJ Hfrs Hfr6 HRT HFRAC HRBE
                ltac:(lia) ltac:(rewrite Hl12l; reflexivity) ltac:(lia) MUc Hl12 Hhid Hsbm)
      as (HJ' & HRT' & HFRAC' & HRBE' & MK).
    pose proof HJ' as (HAR' & _).
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2; apply MK; [lia | lia | intros a Ha; lia]).
    assert (KB : KEEPR mem3 m' phi (phi + rnb cx 0)).
    { apply MK; [lia | lia |]. intros a Ha.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
    pose proof (w2_rbe_regs cx fr regs3 R m' G9 HRBE') as HRBE3.
    pose proof HRBE3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S24' & S16' & S96' & S120' & _).
    apply (H8a8 cx [Z.of_nat 0] fr k ly3 S3 W3 R m' md' HB HJ' Hfrs Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B818a8_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B818a8_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi, 0%nat.
      split; [exact Hperm |].
      split; [exact (w2_frac_regs cx fr fr regs3 R m' G2 G3 G4 G8 G9 G19 G26 HFRAC') |].
      split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { split; [exact (proj1 HHB) |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR' Hin3 ltac:(lia)). }
      split; [exact (w2_rgv_move R regs3 22 _ G22 H22) |].
      split.
      { unfold B.ACtlCutP.OURb in *. eapply w2_bytes_keep; [| exact HOUR].
        apply KF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      split; [exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR) |].
      split; [exact HRBE3 |].
      split; [unfold B.ACtlCut.rgv; exact G21 |].
      split; [lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G10; f_equal; lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G12; f_equal; lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G14; f_equal; lia |].
      split; [reflexivity |].
      split; [lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G11; reflexivity |].
      split.
      { unfold B.ACtlCutP.RF, B.ACtlCutP.RFx, B.ACtlCutP.RFb, B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr,
          B.ACtlCutP.OURb in *.
        split; [split; [| split] |].
        - split; [exact Hb6 |].
          split; [exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR) |].
          split; [eapply w2_bytes_keep; [| exact HOUR];
                  apply KF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia |].
          split; [exact (w2_rgv_move R regs3 22 _ G22 H22) |].
          split; [eapply w2_bytes_keep; [| exact HIDB]; apply KF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia |].
          eapply w2_bytes_keep; [| exact HFGB].
          apply KF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ 0 ltac:(lia)); lia.
        - exact Hnz.
        - split; [exact (w2_rgv_move R regs3 20 _ G20 H20) |].
          eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. exact KB.
        - exact (w2_rgv_move R regs3 18 _ G18 H18). }
      split; [exact S24' |]. split; [exact S16' |]. split; [exact S96' |]. split; [exact S120' |].
      split.
      { apply (w2_ports_addressable m' fr c3 c4); try assumption.
        - lia.
        - lia.
        - unfold B.AsanRT.APPMEM_END. lia.
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
          lia. }
      split; [unfold B.ACtlCut.rgv; exact G13 |].
      exact (w2_rgv_move R regs3 27 _ G27 H27).
    + exact HRT'.
Qed.

(* S_R10, b = 1, 2: R10F.r10_sum12_F, 0x817a4 -> 0x8194c = C_B8194c_at with i := 0 (no call). *)
Lemma w2_R10_b12 : forall POST (b : nat), (b = 1 \/ b = 2)%nat -> CFb POST C8194c b -> CFb POST C817a4 b.
Proof.
  intros POST b Hb12 H94c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817a4_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Ha0 & HRF & S24 & S16 &
                     S96 & S120 & HAD2256 & _ & H27).
  destruct HRF as ((HRB & Hnz & H20 & HFb) & H18).
  pose proof HRB as (_ & _ & _ & _ & HIDB & HFGB).
  destruct (B.Prog.Seg.R10.r10_rtk (B.ACtlCut.c_in cx) b ltac:(lia) Hnz) as (Hk0 & Hn52 & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hn52, HlF.
  assert (Hkb : B.Prog.Seg.R10.r10_kind b = 5) by (destruct Hb12 as [-> | ->]; reflexivity).
  unfold B.ACtlCut.a0v, B.ACtlCut.rgv in Ha0. rewrite Hk0, Hkb in Ha0.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HJ as (HAR3 & Hlyle & _).
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the twelve shadow bytes r10_sum12_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 306 12 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 306) with 306 in Hjunk.
  assert (Hjl : length (firstn 12 (skipn 306 sh)) = 12%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 306) [lib.Lib.Cells.CB 12 (firstn 12 (skipn 306 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 306 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  (* the run: R10F.r10_sum12_F on the normalized memory (rebase_ro_normalize) *)
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l12 : list byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8194c) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 36 /\ lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 18) /\
      lib.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\ lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (phi + 18) /\
      lib.Reusable.YK11.getr R 14 = Z_to_bv 64 32 /\ lib.Reusable.YK11.getr R 13 = Z_to_bv 64 (- (phi + 18)) /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 306, B.ACtlCutP.Sfr fr + 318)] mem3 m' /\
      lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 306) l12 /\ length l12 = 12%nat).
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R10F.r10_sum12_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (phi := phi) (bz := Z.of_nat b) (junk := firstn 12 (skipn 306 sh)).
      * exact H20.
      * exact H21.
      * exact H22.
      * exact Ha0.
      * lia.
      * lia.
      * lia.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & _ & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (R & m1 & l12 & -> & G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & _ & G25 & G26 &
                      G21 & G10 & G11 & G12 & G14 & G13 & G18 & G27 & MU1 & _ & _ & Hl12 & Hl12l).
      match type of MU1 with context [bv_unsigned ?x + 306] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hl12 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es. apply lib.Lib.ExecF.evtF_done.
      exists R, (ms_mem s), l12. split; [reflexivity |].
      split; [exact G2 |]. split; [exact G3 |]. split; [exact G4 |]. split; [exact G8 |]. split; [exact G9 |].
      split; [exact G19 |]. split; [exact G20 |]. split; [exact G22 |]. split; [exact G23 |].
      split; [exact G25 |]. split; [exact G26 |]. split; [exact G21 |]. split; [exact G10 |].
      split; [exact G11 |]. split; [exact G12 |]. split; [exact G14 |]. split; [exact G13 |].
      split; [exact G18 |]. split; [exact G27 |]. split; [exact MUc |].
      split; [exact (proj2 (Hbyt _ _) Hl12) | exact Hl12l].
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & l12 & -> & G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 &
                    G21 & G10 & G11 & G12 & G14 & G13 & G18 & G27 & MUc & Hl12 & Hl12l) Hhid Hsbm.
    apply w2_cfg_back.
    destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 m' md3 md' 306 318 l12 HB HJ Hfrs Hfr6 HRT HFRAC HRBE
                ltac:(lia) ltac:(rewrite Hl12l; reflexivity) ltac:(lia) MUc Hl12 Hhid Hsbm)
      as (HJ' & HRT' & HFRAC' & HRBE' & MK).
    pose proof HJ' as (HAR' & _).
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2; apply MK; [lia | lia | intros a Ha; lia]).
    assert (KB : KEEPR mem3 m' phi (phi + rnb cx b)).
    { apply MK; [lia | lia |]. intros a Ha.
      unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
    pose proof (w2_rbe_regs cx fr regs3 R m' G9 HRBE') as HRBE3.
    apply (H94c cx [Z.of_nat b] fr k ly3 S3 W3 R m' md' HB HJ' Hfrs Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B8194c_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B8194c_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi, 0%nat.
      split; [exact Hperm |].
      split; [exact (w2_frac_regs cx fr fr regs3 R m' G2 G3 G4 G8 G9 G19 G26 HFRAC') |].
      split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { split; [exact (proj1 HHB) |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR' Hin3 ltac:(lia)). }
      split; [exact (w2_rgv_move R regs3 22 _ G22 H22) |].
      split.
      { unfold B.ACtlCutP.OURb in *. eapply w2_bytes_keep; [| exact HOUR].
        apply KF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      split; [exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR) |].
      split; [exact HRBE3 |].
      split; [unfold B.ACtlCut.rgv; exact G21 |].
      split; [lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G10; f_equal; lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G12; f_equal; lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G14; f_equal; lia |].
      split; [exact Hb12 |].
      split; [lia |].
      split; [unfold B.ACtlCut.rgv; rewrite G11; reflexivity |].
      split.
      { unfold B.ACtlCutP.RFb, B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
        split; [| split; [exact Hnz |]].
        - split; [exact Hb6 |].
          split; [exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR) |].
          split; [eapply w2_bytes_keep; [| exact HOUR];
                  apply KF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia |].
          split; [exact (w2_rgv_move R regs3 22 _ G22 H22) |].
          split; [eapply w2_bytes_keep; [| exact HIDB]; apply KF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia |].
          eapply w2_bytes_keep; [| exact HFGB].
          apply KF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)); lia.
        - split; [exact (w2_rgv_move R regs3 20 _ G20 H20) |].
          eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. exact KB. }
      split; [unfold B.ACtlCut.rgv; exact G13 |].
      exact (w2_rgv_move R regs3 27 _ G27 H27).
    + exact HRT'.
Qed.

(* A byte array the post states over the restricted view, at visible off-image bytes, is a raw writable cell run. *)
Lemma w2_rw_of_garr8 : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (q : Z) (bs : list byte),
  0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Reusable.YA0n.w_H W (Z_to_bv 64 (q + i)) = false) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ Reusable.YG0d.in_img segs (q + i)) ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) m) q
    (map (fun x : byte => bv_unsigned x) bs) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m q [lib.Lib.Cells.CB (length bs) bs].
Proof.
  intros W m q bs Hq0 Hq1 Hvis Hni Hg.
  pose proof (w2_bytes_of_garr8 W m q bs Hq0 Hq1 Hvis Hg) as Hb.
  apply (w2_rw_CB m q bs Hb).
  split; [exact Hq0 |]. split; [lia |]. intros i Hi.
  destruct (w2_ba_rd m q bs (q + i) Hb ltac:(lia)) as (bb & Hbb).
  pose proof (w2_mrd_raw m (q + i) bb ltac:(lia) (Hni i Hi) Hbb) as Hr.
  exact (w2_wview_some _ _ _ Hr).
Qed.

(* S_R10, b = 3, 4: R10F.r10_head_reply_F (0x817a4 -> 0x817d4; the reply cells' shadow [Sfr fr + 306, + 313)), then
   R10F.r10_reply_call_pre_F (-> reac_ctrl_identity_reply 0x848fc, ra = 0x817ec), then the call by its
   caller-journal spec TREPLY (a cut-callee: world-form post; r10_reply_call_post_F is not applied) ->
   C_B817ec_at. *)
Lemma w2_R10_b34 : forall POST (b : nat), (b = 3 \/ b = 4)%nat -> CFb POST C817ec b -> CFb POST C817a4 b.
Proof.
  intros POST b Hb34 H7ec cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817a4_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Ha0 & HRF & S24 & S16 &
                     S96 & S120 & HAD2256 & _ & H27).
  destruct HRF as ((HRB & Hnz & H20 & HFb) & H18).
  pose proof HRB as (_ & _ & _ & _ & HIDB & HFGB).
  destruct (B.Prog.Seg.R10.r10_rtk (B.ACtlCut.c_in cx) b ltac:(lia) Hnz) as (Hk0 & Hn52 & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hn52, HlF.
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnr & _).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnr.
  assert (Hkb : B.Prog.Seg.R10.r10_kind b = 5) by (destruct Hb34 as [-> | ->]; reflexivity).
  unfold B.ACtlCut.a0v, B.ACtlCut.rgv in Ha0. rewrite Hk0, Hkb in Ha0.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  pose proof (w2_rgv_unsigned regs3 9 A H9 ltac:(lia)) as U9.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the three reply-cell spills the call reads *)
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S240 & S232 & S224 & _).
  pose proof (w2_spill_at regs3 mem3 A 240 (fr + 2448) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S240) as Q240.
  pose proof (w2_spill_at regs3 mem3 A 232 (fr + 2464) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S232) as Q232.
  pose proof (w2_spill_at regs3 mem3 A 224 (fr + 2496) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S224) as Q224.
  (* the seven shadow bytes r10_head_reply_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 306 7 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 306) with 306 in Hjunk.
  assert (Hjl : length (firstn 7 (skipn 306 sh)) = 7%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 306) [lib.Lib.Cells.CB 7 (firstn 7 (skipn 306 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 306 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  (* the run: r10_head_reply_F on the normalized memory (rebase_ro_normalize), then r10_reply_call_pre_F *)
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x848fc) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x817ec /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 10 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 11 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (fr + 2448) /\
      lib.Reusable.YK11.getr R 13 = Z_to_bv 64 (fr + 2464) /\
      lib.Reusable.YK11.getr R 14 = Z_to_bv 64 (fr + 2496) /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 36 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 306, B.ACtlCutP.Sfr fr + 313)] mem3 m' /\
      exists (l7 : list byte) (c0 c1 c2 : byte),
        lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 306) l7 /\ length l7 = 7%nat /\
        lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 306) [c0] /\ bv_signed c0 = 2 /\
        lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 308) [c1] /\ bv_signed c1 = 0 /\
        lib.Lib.Mem.bytes_at B.Img0.rsegs m' (B.ACtlCutP.Sfr fr + 312) [c2] /\ bv_signed c2 = 0).
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R10F.r10_head_reply_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (bz := Z.of_nat b) (junk := firstn 7 (skipn 306 sh)).
      * exact H21.
      * exact H22.
      * exact Ha0.
      * lia.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & _ & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (m1 & l7 & c0 & c1 & c2 & -> & MU1 & _ & _ & Hc0 & V0 & Hc1 & V1 & Hc2 & V2 & Hl7 & Hl7l).
      match type of MU1 with context [bv_unsigned ?x + 306] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hc0, Hc1, Hc2, Hl7 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es.
      eapply lib.Lib.ExecF.evtF_cut.
      * eapply (B.Prog.Seg.R10F.r10_reply_call_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (fr := fr).
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. apply (w2_bytes_keep mem3); [| exact Q240].
           intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha.
           apply (w2_munch_mrd _ mem3 _ a MUc); [lia |].
           cbn [lib.Lib.Frame.outside]. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
           repeat split; lia.
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. apply (w2_bytes_keep mem3); [| exact Q232].
           intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha.
           apply (w2_munch_mrd _ mem3 _ a MUc); [lia |].
           cbn [lib.Lib.Frame.outside]. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
           repeat split; lia.
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. apply (w2_bytes_keep mem3); [| exact Q224].
           intros a Ha. rewrite lib.Lib.Mem.length_le8 in Ha.
           apply (w2_munch_mrd _ mem3 _ a MUc); [lia |].
           cbn [lib.Lib.Frame.outside]. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
           repeat split; lia.
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
      * intros ms1 ->. apply lib.Lib.ExecF.evtF_done.
        do 2 eexists. split; [reflexivity |].
        repeat (split; [reflexivity |]).
        split; [exact MUc |].
        exists l7, c0, c1, c2.
        split; [exact (proj2 (Hbyt _ _) Hl7) |]. split; [exact Hl7l |].
        split; [exact (proj2 (Hbyt _ _) Hc0) |]. split; [exact V0 |].
        split; [exact (proj2 (Hbyt _ _) Hc1) |]. split; [exact V1 |].
        split; [exact (proj2 (Hbyt _ _) Hc2) | exact V2].
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & -> & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G18 & G19 & G20 & G21 &
                    G22 & G23 & G25 & G26 & G27 & MUc & (l7 & c0 & c1 & c2 & Hl7 & Hl7l & Hc0 & V0 & Hc1 & V1 & Hc2 &
                    V2)) Hhid Hsbm.
    apply w2_cfg_back.
    destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 m' md3 md' 306 313 l7 HB HJ Hfrs Hfr6 HRT HFRAC HRBE
                ltac:(lia) ltac:(rewrite Hl7l; reflexivity) ltac:(lia) MUc Hl7 Hhid Hsbm)
      as (HJ' & HRT' & HFRAC' & HRBE' & MK).
    pose proof HJ' as (HAR' & _).
    assert (HspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite G2; exact Hspz).
    (* the three reply cells are addressable after the head (shadow 2, 0, 0) *)
    assert (Hpa : B.AsanRT.addressable m' (fr + 2448) 2).
    { apply (w2_addr_granule m' (fr + 2448) 2 c0); [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | right; lia].
      - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      - replace (B.AsanRT.shadow_addr (fr + 2448)) with (B.ACtlCutP.Sfr fr + 306)
          by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
        exact Hc0. }
    assert (Hpp : B.AsanRT.addressable m' (fr + 2464) 8).
    { apply (w2_addr_granule m' (fr + 2464) 8 c1); [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
      - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      - replace (B.AsanRT.shadow_addr (fr + 2464)) with (B.ACtlCutP.Sfr fr + 308)
          by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
        exact Hc1. }
    assert (Hpn : B.AsanRT.addressable m' (fr + 2496) 8).
    { apply (w2_addr_granule m' (fr + 2496) 8 c2); [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
      - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      - replace (B.AsanRT.shadow_addr (fr + 2496)) with (B.ACtlCutP.Sfr fr + 312)
          by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
        exact Hc2. }
    (* the message: the first 50 bytes of the frame at phi (kept by the head) *)
    assert (Eg : B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b) =
                 firstn 50 (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b))).
    { unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite firstn_app.
      replace (50 - length (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b)))%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r. reflexivity. }
    assert (Hg50 : lib.Lib.Mem.bytes_at B.Img0.rsegs m' phi (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))).
    { assert (HF' : lib.Lib.Mem.bytes_at B.Img0.rsegs m' phi (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b))).
      { eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. apply MK; [lia | lia |]. intros a Ha.
        unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
      pose proof (w2_bytes_bsl m' phi _ 0 50 HF' ltac:(lia)) as H50.
      cbn [skipn] in H50. change (Z.of_nat 0) with 0 in H50. rewrite Z.add_0_r in H50.
      rewrite Eg. exact H50. }
    assert (Hg50l : Z.of_nat (length (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))) = 50)
      by (unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50; rewrite length_firstn, length_app, repeat_length; lia).
    (* the call: reac_ctrl_identity_reply's caller-journal spec *)
    change 0x848fc with B.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP.
    eapply Reusable.YA0n.SRr_bind.
    { apply (TREPLY Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)
               (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx) (own6 cx) ly3 S3 W3 m' md' k R phi
               (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496)
               (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) HJ').
      - exact (w2_arodataS cx _ _ _ _ _ _ _ HB HJ').
      - rewrite G1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
      - unfold Reusable.YG0d.raZ. rewrite G1, Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
      - rewrite G3, H3. exact Hgp0.
      - rewrite G4. exact H4.
      - rewrite G10. exact H20.
      - rewrite G11. exact H18.
      - exact G12.
      - exact G13.
      - exact G14.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite HspR. exact Hsp16.
      - rewrite HspR. unfold Reusable.YCfn.LLVMF_STK,
          B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK. lia.
      - rewrite HspR. lia.
      - rewrite Hfrs. vm_compute. reflexivity.
      - unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite length_firstn, length_app, repeat_length. lia.
      - intros _ _. split.
        + exists (rnb cx b). split; [exact Hin3 | rewrite Er; lia].
        + apply w2_garr8_of_bytes; [exact Hg50 |].
          intros i Hi. rewrite Hg50l in Hi. exact (proj1 (proj1 (Hpbytes (phi + i) ltac:(lia)))).
      - intros Hargs.
        split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
        split; [| split; [| split]].
        + intros a Ha. unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ha. split.
          * exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6 |]. split; [lia |].
            unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia.
          * right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
            left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3, <- Hfr6, Hfsb. lia.
        + apply w2_range_addr_of_raw; [exact Hpa |]. intros i Hi.
          exact (proj1 (Hfsvis (B.AsanRT.shadow_addr (fr + 2448 + i))
                          ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
                                  Reusable.YG0f.SHADOW_OFF; lia))).
        + apply w2_range_addr_of_raw; [exact Hpp |]. intros i Hi.
          exact (proj1 (Hfsvis (B.AsanRT.shadow_addr (fr + 2464 + i))
                          ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
                                  Reusable.YG0f.SHADOW_OFF; lia))).
        + apply w2_range_addr_of_raw; [exact Hpn |]. intros i Hi.
          exact (proj1 (Hfsvis (B.AsanRT.shadow_addr (fr + 2496 + i))
                          ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
                                  Reusable.YG0f.SHADOW_OFF; lia))). }
    cbv beta. intros W2 cf Hwle (_ & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPR & Hfrs2 & Hbl2 & Ha02 & HK & HOK).
    unfold B.Prog.C_reac_ctrl_identity_reply.EV_REPLY in HJ2. rewrite Z.add_0_r in HJ2.
    pose proof HJ2 as (HAR2 & _).
    rewrite HspR in HK.
    assert (Hin2 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite Hbl2; exact Hin3).
    assert (HEs : forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW ->
                    ~ (B.ACtlCutP.RRP.reply_ok phi (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496)
                         (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) = true /\
                       B.Prog.C_reac_ctrl_identity_reply.treply_out (fr + 2448) (fr + 2464) (fr + 2496) a)).
    { intros a Ha (_ & Ht). unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ht.
      unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in Ha. lia. }
    destruct (w2_acall_keeps cx fr k sp ly3 S3 W3 m' md' ly2 S2 W2 mem2 md2 _ _
                (sp - B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK) sp _
                HB HJ' Hfrs Hfr6 (proj1 Hspr) Hsp4 ltac:(lia) HK Hwle HJ2 HEs HRT')
      as (KH2 & KFW2 & KS2 & KTBL2 & KROW2 & KBOX2 & KNM2 & HRT2).
    (* keeps from the cut's memory to m' (the head) and from m' to mem2 (the call) *)
    assert (KF2 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> (hi <= fr + 2448 \/ fr + 2504 <= lo) ->
                    KEEPR m' mem2 lo hi).
    { intros lo hi L1 L2 L3 a Ha. apply KFW2; [rewrite Hfsb; lia |].
      intros (_ & Ht). unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ht. lia. }
    assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2; apply MK; [lia | lia | intros a Ha; lia]).
    assert (KFF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> (hi <= fr + 2448 \/ fr + 2504 <= lo) ->
                    KEEPR mem3 mem2 lo hi)
      by (intros lo hi L1 L2 L3; exact (w2_keep_trans _ _ _ lo hi (KF1 lo hi L1 L2) (KF2 lo hi L1 L2 L3))).
    (* registers: regs2 keeps R's callee-saved registers *)
    assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                  lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs3 r ->
                  lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
      by (intros z r Hz' Er' E; exact (w2_pres_reg R regs2 regs3 z r HPR Hz' Er' E)).
    assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
      by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
    assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact G2]).
    assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact G3]).
    assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact G4]).
    assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact G8]).
    assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact G9]).
    assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
      by (apply (G 18); [apply CS; lia | apply bv_eq; reflexivity | exact G18]).
    assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact G19]).
    assert (F20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
      by (apply (G 20); [apply CS; lia | apply bv_eq; reflexivity | exact G20]).
    assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact G22]).
    assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
      by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact G23]).
    assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact G25]).
    assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact G26]).
    assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact G27]).
    assert (F21 : lib.Reusable.YK11.getr regs2 21 = Z_to_bv 64 36).
    { rewrite <- G21. apply (w2_pres_reg R regs2 R 21); [exact HPR | apply CS; lia | apply bv_eq; reflexivity |
                                                         reflexivity]. }
    (* FRAC and RBE at mem2 *)
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 mem2).
    { apply (w2_frac_mem cx fr fr regs3 m' mem2); [| | exact KS2 | | exact HFRAC'].
      - intros a Ha _. rewrite Hspz in Ha. apply KH2. lia.
      - apply KF2; lia.
      - apply KF2; lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 mem2).
    { apply (w2_rbe_mem cx fr regs3 m' mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia)
               (fun a Ha => KH2 a ltac:(lia)) (fun a Ha _ => KS2 a Ha) KTBL2 KBOX2 KROW2 KNM2 HRBE'). }
    pose proof (w2_rbe_regs cx fr regs3 regs2 mem2 F9 HRBE2) as HRBE3.
    (* the block's bytes: kept by the head (application memory) and by the call (a live block off the cells) *)
    assert (KB : KEEPR mem3 mem2 phi (phi + rnb cx b)).
    { apply (w2_keep_trans _ m').
      - apply MK; [lia | lia |]. intros a Ha.
        unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia.
      - apply (w2_kept ly3 S3 W3 W2 m' mem2 _ _ _ phi (phi + rnb cx b) HK Hwle); [lia | lia |].
        intros a Ha. split; [exact (proj1 (proj1 (Hpbytes a Ha))) |].
        right; left. exists phi, (rnb cx b), (a - phi). split; [exact Hin3 |]. split; [rewrite Er; lia |].
        split; [lia |]. intros (_ & Ht). unfold B.Prog.C_reac_ctrl_identity_reply.treply_out in Ht. lia. }
    (* the frame cells' visibility in W2 (wle) and their place off the image *)
    assert (FV2 : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
    { intros a Ha. destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 a)) eqn:Eh; [| reflexivity].
      pose proof Hwle as Hwle'. unfold Reusable.YA0n.wle, Reusable.YA0i.hsub in Hwle'.
      pose proof (Hwle' _ Eh) as E3. rewrite (proj1 (Hfvis a Ha)) in E3. discriminate. }
    rewrite G1.
    apply (H7ec cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 (eq_trans Hfrs2 Hfrs) Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B817ec_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B817ec_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi. rewrite Hbl2.
      unfold B.ACtlCutP.RF, B.ACtlCutP.RFx, B.ACtlCutP.RFb, B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr,
        B.ACtlCutP.OURb in *.
      assert (KOUR : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 2624) (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx))).
      { eapply w2_bytes_keep; [| exact HOUR]. apply KFF;
          try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      assert (KCUR : B.ACtlCutP.CUR cx 7 regs2) by exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
      assert (K22 : B.ACtlCut.rgv regs2 22 (Z.of_nat b)) by exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
      split; [exact Hperm |].
      split; [exact (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26 HFRAC2) |].
      split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { split; [exact (proj1 HHB) |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR2 Hin2 ltac:(lia)). }
      split; [exact K22 |]. split; [exact KOUR |]. split; [exact KCUR |]. split; [exact HRBE3 |].
      split; [unfold B.ACtlCut.rgv; exact F21 |].
      split; [exact Hb34 |].
      split.
      { split; [split; [| split; [exact Hnz | split]] |].
        - split; [exact Hb6 |]. split; [exact KCUR |]. split; [exact KOUR |]. split; [exact K22 |].
          split; [eapply w2_bytes_keep; [| exact HIDB]; apply KFF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia |].
          eapply w2_bytes_keep; [| exact HFGB].
          apply KFF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ b ltac:(lia)); lia.
        - exact (w2_rgv_move regs2 regs3 20 _ F20 H20).
        - eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. exact KB.
        - exact (w2_rgv_move regs2 regs3 18 _ F18 H18). }
      split; [unfold B.ACtlCut.a0v, B.ACtlCut.rgv; exact Ha02 |].
      split.
      { intros Hok. destruct (HOK Hok) as (Hg & Hv1 & Hv2).
        split; [| split].
        - assert (Hra : length (B.ACtlCutP.RRP.reply_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))) = 2%nat)
            by reflexivity.
          pose proof (w2_rw_of_garr8 W2 mem2 (fr + 2448)
                        (B.ACtlCutP.RRP.reply_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)))
                        ltac:(lia) ltac:(rewrite Hra; lia)
                        ltac:(rewrite Hra; intros i Hi; apply FV2; lia)
                        ltac:(rewrite Hra; intros i Hi; apply Hfimg; lia) Hg) as Hrw.
          exact Hrw.
        - apply (w2_cells_of_val_mem W2 mem2 (fr + 2464) (phi + 38)); [lia | lia | lia | | | exact Hv1].
          + intros i Hi. apply FV2. lia.
          + intros i Hi. apply Hfimg. lia.
        - apply (w2_cells_of_val_mem W2 mem2 (fr + 2496)); [| lia | lia | | | exact Hv2].
          + pose proof Hok as Hok'. unfold B.ACtlCutP.RRP.reply_ok in Hok'. apply andb_prop in Hok' as (_ & Hir).
            pose proof (B.ACtlCutP.RRP.ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
            lia.
          + intros i Hi. apply FV2. lia.
          + intros i Hi. apply Hfimg. lia. }
      exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
    + exact HRT2.
Qed.

(* ---- S_R10's fragment arms (b = 5, 6): helpers.  The callee runs on the normalized memory (its contract takes
   mem_inv), so its premises come from the cut-like facts after the head by MemNorm's transfers; its R (the shadow its
   callees read through shadow_rw_on) lies in ctl_rt_C's cut_shadow: the D side in the class-6 frame, the S side in
   the live block (a Theorem Labs lane's reac_ctrl_identity_fragment_shadow_R comment records this coverage). *)

(* Off the image, no address is read-only. *)
Lemma w2_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold lib.Lib.Mem.ro_addr. rewrite lib.Lib.MState.unsigned_lit by lia.
  assert (E : find_segment B.Img0.rsegs a 1 = None) by exact (Reusable.YCbq.find_segment_none segs a Hn).
  rewrite E. reflexivity.
Qed.

(* Present raw bytes are writable in the view. *)
Lemma w2_wr_of_present : forall (m : word -> option byte) (lo n : Z),
  0 <= lo -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists bb, m (Z_to_bv 64 (lo + i)) = Some bb) ->
  lib.Lib.Mem.wr_at B.Img0.rsegs m lo n.
Proof.
  intros m lo n H0 H1 H2 H. split; [exact H0 |]. split; [lia |]. intros i Hi.
  destruct (H i Hi) as (bb & Hbb). exact (w2_wview_some _ _ _ Hbb).
Qed.

(* A stack window every byte of which is present is a stk range. *)
Lemma w2_stk_of_present : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m a) ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros W m lo hi H0 H1 H. split; [exact H0 |]. split; [exact H1 |]. intros a Ha.
  destruct (H a Ha) as (_ & bb & Hbb). split; [exact (w2_wview_some _ _ _ Hbb) |].
  exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity.
Qed.

(* shadow_rw_on moves to the normalized memory (the shadow lies above the image). *)
Lemma w2_srw_on_normalize : forall (P : Z -> Prop) (m : word -> option byte),
  B.MemNorm.ro_agree B.Img0.rsegs m -> B.ShadowRwOn.shadow_rw_on P m ->
  B.ShadowRwOn.shadow_rw_on P (B.MemNorm.normalize B.Img0.rsegs m).
Proof.
  intros P m Hro H a HP Hs. destruct (H a HP Hs) as (Hw & bb & Hb).
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m Hro) as Hrel.
  assert (Hro0 : lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false).
  { apply B.MemNormTr.ro_addr_above_img.
    unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hs.
    unfold B.Prog.ImgBounds.IMG_HI. lia. }
  split.
  - rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m _ _ Hrel Hro0). exact Hw.
  - exists bb. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m _ _ Hrel). exact Hb.
Qed.

(* Visibility survives a later world (wle hides no more). *)
Lemma w2_rv_wle : forall (W W' : Reusable.YA0n.world segs) (lo len : Z),
  Reusable.YA0n.wle W W' -> B.ProgBridge.range_visible (Reusable.YA0n.w_H W) lo len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W') lo len.
Proof.
  intros W W' lo len Hle (H0 & H1 & H). split; [exact H0 |]. split; [exact H1 |]. intros a Ha.
  destruct (Reusable.YA0n.w_H W' (Z_to_bv 64 a)) eqn:Eh; [| reflexivity].
  pose proof Hle as Hle'. unfold Reusable.YA0n.wle, Reusable.YA0i.hsub in Hle'.
  pose proof (Hle' _ Eh) as E. rewrite (H a Ha) in E. discriminate.
Qed.

(* A hidden byte is off a run the head wrote (the frame's shadow is visible), so the head kept it. *)
Lemma w2_head_hid : forall (W : Reusable.YA0n.world segs) (mem m1 : word -> option byte) (lo hi : Z),
  lib.Lib.Frame.munch [(lo, hi)] mem m1 ->
  (forall a, lo <= a < hi -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  forall x, Reusable.YA0n.w_H W x = true -> m1 x = mem x.
Proof.
  intros W mem m1 lo hi MU Hv x Hx. apply MU. cbn [lib.Lib.Frame.outside]. split; [| exact I]. intros Hin.
  pose proof (Hv _ Hin) as Hf.
  assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
    apply Z.mod_small. exact Hxr. }
  rewrite Ex in Hf. congruence.
Qed.

(* An aligned shadow word cover of a run inside the class-6 frame is in the frame arm of cut_shadow. *)
Lemma w2_shw_frame : forall (cx : ctlcx) ly3 S3 (fr p n a : Z),
  Reusable.YG01.frames S3 = own6 cx ->
  Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr -> 0 <= fr ->
  fr + 64 <= p -> p + n + 64 <= fr + 4096 -> B.Prog.sh_word_on.sh_word_on p n a ->
  B.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros cx ly3 S3 fr p n a Hfrs Hfa Hfr0 Hp1 Hp2 (Hn & Ha).
  left. exists 6, (B.ACtlCut.c_fpos cx). split; [rewrite Hfrs; left; reflexivity |].
  rewrite Hfa. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* An aligned shadow word cover of a run inside a live block is in the block arm of cut_shadow. *)
Lemma w2_shw_block : forall ly3 S3 (q n0 p n a : Z),
  In (q, n0) (Reusable.YG0d.ablocks B ly3 S3) -> 1 <= n0 ->
  0 <= q -> q <= p -> p + n <= q + n0 -> B.Prog.sh_word_on.sh_word_on p n a ->
  B.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros ly3 S3 q n0 p n a Hin Hn0 Hq0 Hp1 Hp2 (Hn & Ha).
  right; left. exists q, n0. split; [exact Hin |].
  assert (Er : Reusable.YG00.req_size n0 = n0)
    by (unfold Reusable.YG00.req_size; destruct (n0 =? 0) eqn:E; lia).
  rewrite Er.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* The fragment call's R at S_R10 (f = fr + 2256 in the class-6 frame, the message at the live block phi) lies in
   cut_shadow. *)
Lemma w2_fragR_cut : forall (cx : ctlcx) ly3 S3 (fr phi n len : Z) (st g : list byte) (a : Z),
  Reusable.YG01.frames S3 = own6 cx ->
  Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr -> 0 <= fr -> fr + 4096 <= 2 ^ 64 ->
  In (phi, n) (Reusable.YG0d.ablocks B ly3 S3) -> 50 <= n -> 0 <= phi -> phi + n <= 2 ^ 64 ->
  B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R (fr + 2256) phi len (fr + 2448)
    (fr + 2464) (fr + 2496) st g a ->
  B.ACtlRtC.cut_shadow B ly3 S3 a.
Proof.
  intros cx ly3 S3 fr phi n len st g a Hfrs Hfa Hfr0 Hfr1 Hin Hn Hphi0 Hphi1 HR.
  unfold B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_shadow_R in HR.
  destruct HR as (_ & _ & _ & _ & _ & Hfg & HR).
  assert (Hng : 1 <= B.ACtlCutP.RFR.fg_n g <= 22).
  { unfold B.ACtlCutP.RFR.fg_fr in Hfg.
    destruct (1 <=? B.ACtlCutP.RFR.fg_n g) eqn:E1; destruct (B.ACtlCutP.RFR.fg_n g <=? 22) eqn:E2;
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l in Hfg; try discriminate.
    apply Z.leb_le in E1, E2. lia. }
  assert (Hlf : 0 <= B.ACtlCutP.RFR.fg_lf st < 256).
  { unfold B.ACtlCutP.RFR.fg_lf, B.ACtlCutP.RFR.bat.
    match goal with |- context [bv_unsigned ?b] => pose proof (bv_unsigned_in_range 8 b) as H8 end.
    change (bv_modulus 8) with 256 in H8. exact H8. }
  unfold B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R, B.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R in HR.
  rewrite ?lib.Lib.MState.unsigned_lit in HR by lia.
  destruct HR as [(_ & [[HR | HR] | [HR | HR]]) | (_ & _ & [[HR | HR] | (Hk & [HR | HR])])].
  - eapply (w2_shw_block ly3 S3 phi n _ _ a Hin); [lia | exact Hphi0 | | | exact HR]; lia.
  - eapply (w2_shw_frame cx ly3 S3 fr _ _ a Hfrs Hfa Hfr0); [| | exact HR]; lia.
  - eapply (w2_shw_block ly3 S3 phi n _ _ a Hin); [lia | exact Hphi0 | | | exact HR]; lia.
  - eapply (w2_shw_frame cx ly3 S3 fr _ _ a Hfrs Hfa Hfr0); [| | exact HR]; lia.
  - eapply (w2_shw_frame cx ly3 S3 fr _ _ a Hfrs Hfa Hfr0); [| | exact HR]; lia.
  - eapply (w2_shw_block ly3 S3 phi n _ _ a Hin); [lia | exact Hphi0 | | | exact HR]; lia.
  - eapply (w2_shw_block ly3 S3 phi n _ _ a Hin); [lia | exact Hphi0 | | | exact HR]; lia.
  - unfold B.ACtlCutP.RFR.fg_keep, B.ACtlCutP.RFR.fg_T in Hk.
    apply andb_prop in Hk as (_ & Hk). apply Z.leb_le in Hk.
    eapply (w2_shw_frame cx ly3 S3 fr _ _ a Hfrs Hfa Hfr0); [| | exact HR]; lia.
Qed.

(* S_R10, b = 6: R10F.r10_head_frag6_F (0x817a4 -> 0x81818; the reply cells' shadow [Sfr fr + 306, + 313)), then
   R10F.r10_frag6_call_pre_F (-> reac_ctrl_identity_fragment 0x859e4, ra = 0x81834), then the fragment by its route-C
   footprint contract on the normalized memory (a lifted callee: raw post; turn 6 is a closing fragment,
   RtmB.rb_rtm_close) -> C_B81834_at. *)
Lemma w2_R10_b6 : forall POST (b : nat), b = 6%nat -> CFb POST C81834 b -> CFb POST C817a4 b.
Proof.
  intros POST b Hb6' H834 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817a4_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Ha0 & HRF & S24 & S16 &
                     S96 & S120 & HAD2256 & _ & H27).
  subst b.
  destruct HRF as ((HRB & Hnz & H20 & HFb) & H18).
  pose proof HRB as (_ & _ & _ & _ & HIDB & HFGB).
  destruct (B.Prog.Seg.R10.r10_rtk (B.ACtlCut.c_in cx) 6 ltac:(lia) Hnz) as (Hk0 & Hn52 & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 6)) with (rnb cx 6) in Hn52, HlF.
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 6) Hnz) as (_ & Hnr & _).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 6)) with (rnb cx 6) in Hnr.
  unfold B.ACtlCut.a0v, B.ACtlCut.rgv in Ha0. rewrite Hk0 in Ha0.
  assert (Hphinz : phi <> 0) by exact (proj1 HHB).
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Usp : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp)
    by (unfold Reusable.YG0d.spZ in Hspz; exact Hspz).
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & Hwle0 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfa3' : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr) by (rewrite Hfa3, <- Hfr6; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Hfc & _).
  rewrite Hfa3', Hfsb in Hfc.
  assert (Hin3 : In (phi, rnb cx 6) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 6) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx 6) = rnb cx 6)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx 6 =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 6) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3', Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  pose proof (w2_rgv_unsigned regs3 9 A H9 ltac:(lia)) as U9.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the frame lies off the image (so off the runtime's cells) *)
  assert (HfRT : fr + 4096 <= Reusable.YImgTop.IMG_LO \/ Reusable.YImgTop.IMG_TOP <= fr).
  { destruct (Z_lt_le_dec fr Reusable.YImgTop.IMG_TOP) as [L1 | L1]; [left | right; exact L1].
    destruct (Z_lt_le_dec Reusable.YImgTop.IMG_LO (fr + 4096)) as [L2 | L2]; [exfalso | exact L2].
    apply (Hfimg (Z.max fr Reusable.YImgTop.IMG_LO) ltac:(lia)). apply w2_in_img. lia. }
  (* the closing class of turn 6 *)
  assert (Ecls : B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 6)
                   (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)) =
                 B.ACtlCutP.SM.fcls (rnb cx 6) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)
                   (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)))
    by (apply B.Prog.Seg.R10.r10_fgc; lia).
  assert (Hcls : B.ACtlCutP.SM.fcls (rnb cx 6) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)
                   (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)) = B.ACtlCutP.RFR.FgClose)
    by exact (B.Prog.Seg.RtmB.rb_rtm_close (B.ACtlCut.c_in cx) Hnz).
  assert (HstL : length (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) = 72%nat)
    by exact (B.Prog.Seg.RtmB.rb_RFG_len _ 6 ltac:(lia)).
  assert (HgL : length (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)) = 50%nat)
    by (unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50; rewrite length_firstn, length_app, repeat_length; lia).
  (* the seven shadow bytes r10_head_frag6_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 306 7 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 306) with 306 in Hjunk.
  assert (Hjl : length (firstn 7 (skipn 306 sh)) = 7%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 306) [lib.Lib.Cells.CB 7 (firstn 7 (skipn 306 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 306 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  pose proof B.Prog.reac_ctrl_identity_fragment_F_closed.reac_ctrl_identity_fragment_holds_F_closed_on as HFG.
  unfold B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract_F_on in HFG.
  (* the run: the head and the call's pre on rebased memory, then the fragment on the normalized memory again *)
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81834) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 36 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Reusable.YK11.getr R 10 =
        Z_to_bv 64 (B.ACtlCutP.RFR.fg_ret (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                      (fr + 2496) (rnb cx 6) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)
                      (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)))) /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 306, B.ACtlCutP.Sfr fr + 313)] mem3 m1 /\
      (exists (l7 : list byte) (c0 c1 c2 : byte),
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 306) l7 /\ length l7 = 7%nat /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 306) [c0] /\ bv_signed c0 = 2 /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 308) [c1] /\ bv_signed c1 = 0 /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 312) [c2] /\ bv_signed c2 = 0) /\
      lib.Lib.Frame.munch
        (B.ACtlCutP.RFR.fg_fp B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256)
           (fr + 2448) (fr + 2464) (fr + 2496) sp
           (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 6)
              (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6))))
        m1 m' /\
      lib.Lib.Frame.wmono B.Img0.rsegs m1 m' /\
      lib.Lib.Frame.stk B.Img0.rsegs m'
        (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) sp /\
      B.Prog.reac_ctrl_identity_fragment_c.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
        (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6))
        (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 6)
           (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6))) m').
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R10F.r10_head_frag6_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (junk := firstn 7 (skipn 306 sh)).
      * exact H21.
      * exact H22.
      * exact Ha0.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & HROs & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (m1 & l7 & c0 & c1 & c2 & -> & MU1 & _ & _ & Hc0 & V0 & Hc1 & V1 & Hc2 & V2 & Hl7 & Hl7l).
      match type of MU1 with context [bv_unsigned ?x + 306] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hc0, Hc1, Hc2, Hl7 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      pose proof (proj2 (Hbyt _ _) Hl7) as Hl7'.
      pose proof (proj2 (Hbyt _ _) Hc0) as Hc0'.
      pose proof (proj2 (Hbyt _ _) Hc1) as Hc1'.
      pose proof (proj2 (Hbyt _ _) Hc2) as Hc2'.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es.
      (* the cut-like facts after the head, at its raw memory *)
      assert (Hhid1 : forall x, Reusable.YA0n.w_H W3 x = true -> ms_mem s x = mem3 x).
      { apply (w2_head_hid W3 mem3 (ms_mem s) (B.ACtlCutP.Sfr fr + 306) (B.ACtlCutP.Sfr fr + 313) MUc).
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
      destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 (ms_mem s) md3 md3 306 313 l7 HB HJ Hfrs Hfr6 HRT HFRAC
                  HRBE ltac:(lia) ltac:(rewrite Hl7l; reflexivity) ltac:(lia) MUc Hl7' Hhid1
                  (Reusable.YK04.same_but_materialized_refl md3))
        as (HJ1 & HRT1 & HFRAC1 & HRBE1 & MK1).
      pose proof HJ1 as (HAR1 & _).
      pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1 & _).
      unfold Reusable.YCfn.LLVMF_STK in Hwin1.
      pose proof HRBE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S240' & S232' & S224' &
                           _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S112' & HAD2256' & _).
      pose proof (w2_spill_at regs3 (ms_mem s) A 112 (fr + 2256) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S112')
        as Q112.
      pose proof (w2_spill_at regs3 (ms_mem s) A 240 (fr + 2448) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S240')
        as Q240.
      pose proof (w2_spill_at regs3 (ms_mem s) A 232 (fr + 2464) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S232')
        as Q232.
      pose proof (w2_spill_at regs3 (ms_mem s) A 224 (fr + 2496) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S224')
        as Q224.
      assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 (ms_mem s) lo hi)
        by (intros lo hi L1 L2; apply MK1; [lia | lia | intros a Ha; lia]).
      assert (HPF1 : forall a, fr <= a < fr + 4096 -> exists bb, ms_mem s (Z_to_bv 64 a) = Some bb).
      { intros a Ha. destruct (proj2 (Hfvis a Ha)) as (bb & Hbb). exists bb.
        rewrite (MUc (Z_to_bv 64 a)); [exact Hbb |].
        rewrite lib.Lib.MState.unsigned_lit by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
      assert (Hrel1 : B.MemNorm.mem_rel B.Img0.rsegs (ms_mem s) (B.MemNorm.normalize B.Img0.rsegs (ms_mem s)))
        by exact (B.MemNorm.mem_rel_normalize B.Img0.rsegs (ms_mem s) HROs).
      assert (ROF : forall a n, fr <= a -> a + n <= fr + 4096 ->
                      forall i, 0 <= i < n -> lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa (a + i)) = false)
        by (intros a n L1 L2 i Hi; apply w2_ro_false; [lia | apply Hfimg; lia]).
      assert (WRN : forall a n, fr <= a -> 0 <= n -> a + n <= fr + 4096 ->
                      lib.Lib.Mem.wr_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs (ms_mem s)) a n).
      { intros a n L1 L2 L3. apply (B.MemNorm.wr_at_norm B.Img0.rsegs (ms_mem s)); [exact Hrel1 | | apply ROF; lia].
        apply w2_wr_of_present; [lia | lia | lia |]. intros i Hi. apply HPF1. lia. }
      assert (HFGB1 : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) (fr + 2256)
                        (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)).
      { unfold B.ACtlCutP.FGBr in HFGB. eapply w2_bytes_keep; [| exact HFGB]. apply KF1; rewrite ?HstL; lia. }
      assert (Hg1 : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) phi
                      (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6))).
      { assert (HF' : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) phi
                        (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat 6))).
        { eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. apply MK1; [lia | lia |]. intros a Ha.
          unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
        assert (HL50 : (50 <= length (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat 6)))%nat)
          by (apply Nat2Z.inj_le; rewrite HlF; lia).
        pose proof (w2_bytes_bsl (ms_mem s) phi _ 0 50 HF' HL50) as H50.
        cbn [skipn] in H50. change (Z.of_nat 0) with 0 in H50. rewrite Z.add_0_r in H50.
        unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite firstn_app.
        rewrite (proj2 (Nat.sub_0_le 50 _) HL50).
        rewrite firstn_O, app_nil_r. exact H50. }
      destruct (ctl_bcmp_cells_of_AR _ _ _ _ _ HAR1) as (CB1 & CB2 & CB3 & CB4 & CB5).
      assert (Hpa : B.AsanRT.addressable (ms_mem s) (fr + 2448) 2).
      { apply (w2_addr_granule (ms_mem s) (fr + 2448) 2 c0);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | right; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2448)) with (B.ACtlCutP.Sfr fr + 306)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc0'. }
      assert (Hpp : B.AsanRT.addressable (ms_mem s) (fr + 2464) 8).
      { apply (w2_addr_granule (ms_mem s) (fr + 2464) 8 c1);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2464)) with (B.ACtlCutP.Sfr fr + 308)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc1'. }
      assert (Hpn : B.AsanRT.addressable (ms_mem s) (fr + 2496) 8).
      { apply (w2_addr_granule (ms_mem s) (fr + 2496) 8 c2);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2496)) with (B.ACtlCutP.Sfr fr + 312)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc2'. }
      assert (Hph1 : B.AsanRT.addressable (ms_mem s) phi 50).
      { pose proof (w2_block_addressable _ _ _ _ _ _ _ HAR1 Hin3 ltac:(lia)) as (A0 & A1 & A2 & A3).
        split; [lia |]. split; [lia |]. split; [lia |]. intros i Hi. apply A3. lia. }
      assert (VF : forall lo len, Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) <= lo ->
                     lo + len <= Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) +
                                 Reusable.YG00.fs_frame_bytes 6 ->
                     B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len /\
                     (0 <= len -> Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) <= 64 * (lo / 64) ->
                      64 * ((lo + len - 1) / 64) + 64 <=
                        Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6 ->
                      len = 0 \/ B.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                                   (B.Prog.rng_asan.sh_al8_lo lo)
                                   (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo)))
        by (intros lo len;
            exact (B.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) lo len HAR3 Hin6)).
      rewrite Hfa3', Hfsb in VF.
      destruct (VF (fr + 2256) 72 ltac:(lia) ltac:(lia)) as (VFf & VFfs).
      destruct (VF (fr + 2448) 2 ltac:(lia) ltac:(lia)) as (VFa & VFas).
      destruct (VF (fr + 2464) 8 ltac:(lia) ltac:(lia)) as (VFp & VFps).
      destruct (VF (fr + 2496) 8 ltac:(lia) ltac:(lia)) as (VFn & VFns).
      destruct (img_vis_W W3) as (_ & _ & VI).
      eapply lib.Lib.ExecF.evtF_cut.
      * eapply (B.Prog.Seg.R10F.r10_frag6_call_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (fr := fr).
        -- match goal with |- context [bv_unsigned ?x + 112] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q112.
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q240.
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q232.
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q224.
        -- match goal with |- context [bv_unsigned ?x + 112] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
      * intros ms1 ->.
        eapply lib.Lib.ExecF.evtF_cut.
        -- eapply RB; [exact HROs |].
           eapply (HFG (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
             (f := fr + 2256) (fr := phi) (len := rnb cx 6) (pa := fr + 2448) (pp := fr + 2464) (pn := fr + 2496)
             (st := B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)
             (g := B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)).
           ++ reflexivity.
           ++ exact H20.
           ++ exact H18.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              exact Hsp16.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              apply B.MemNormTr.stk_normalize_ro; [exact HROs | |].
              ** unfold B.Prog.ImgBounds.IMG_HI, B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K.
                 lia.
              ** apply (w2_stk_of_present W3); [unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
                                                lia | lia |].
                 intros a Ha. unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in Ha.
                 apply Hwin1. lia.
           ++ exact HgL.
           ++ exact HstL.
           ++ intros _ _ _ _ _ _. exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs Hg1).
           ++ intros _ _ _ _ _.
              split.
              { apply B.MemNormTr.rw_cells_normalize; [exact HROs | |].
                - intros i Hi. cbn in Hi. apply (ROF (fr + 2256) 72); lia.
                - pose proof (w2_rw_CB (ms_mem s) _ _ HFGB1) as H. rewrite HstL in H. apply H.
                  apply w2_wr_of_present; [lia | lia | lia |]. intros i Hi. apply HPF1. lia. }
              split; [lia |]. split; [lia |]. split; [lia |].
              split; [apply WRN; lia |]. split; [apply WRN; lia |]. split; [apply WRN; lia |].
              match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              cbn [B.ACtlCutP.RFR.all_dj B.ACtlCutP.RFR.dj_from].
              unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. repeat split; lia.
           ++ apply B.MemNorm.mem_inv_normalize.
           ++ apply B.MemNormTr.asan_cells_normalize; [exact HROs | exact (proj1 HRT1)].
           ++ apply w2_srw_on_normalize; [exact HROs |].
              intros a HRa Hsha. apply (proj1 (proj2 HRT1)); [| exact Hsha].
              exact (w2_fragR_cut cx ly3 S3 fr phi (rnb cx 6) (rnb cx 6) _ _ a Hfrs Hfa3' ltac:(lia) ltac:(lia) Hin3
                       ltac:(lia) ltac:(lia) ltac:(lia) HRa).
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.AsanRT.HIGHMEM_BEG,
                B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.AsanRT.APPMEM_END. lia.
           ++ intros _ _ _ _ _ _. exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hph1).
           ++ intros _ _ _ _ _.
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs HAD2256') |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpa) |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpp) |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpn) |].
              split; [unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia |].
              cbn [B.ACtlCutP.RFR.dj_from]. unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI. repeat split; lia.
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB1).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB2).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB3).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB4).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB5).
           ++ apply B.ProgBridge.rng_bytes_RNG_W.
           ++ apply B.ProgBridge.rng_of_visible.
              split; [unfold B.Prog.ImgBounds.IMG_LO; lia |].
              split; [unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia |].
              intros a Ha. apply VI. unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Ha.
              lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              apply B.ProgBridge.rng_of_visible.
              apply (w2_vis_stack cx (own6 cx) ly3 S3 W3 mem3 md3 k); [exact HJ | | | ];
                unfold Reusable.YCfn.LLVMF_STK, B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
                lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.Prog.rng_asan.sh_word_rng. right. apply B.ProgBridge.rng_of_visible.
              apply (w2_rv_wle (B.ACtlCut.c_W cx) W3); [exact Hwle0 |].
              destruct (B.ProgWorldVisWin.win_sh_vis B LAWS (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx)
                          (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
                          (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K)
                          B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K HAR0
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia)
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia)
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia))
                as [E | V].
              ** unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in E. lia.
              ** exact V.
           ++ intros _ _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              split; [lia |]. split; [lia |]. intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
           ++ intros _ _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (B.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 6) phi 50 HAR3 Hin3
                          ltac:(lia) ltac:(rewrite Er; lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (phi + 49) with (phi + 50 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFf.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFfs ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2256 + 71) with (fr + 2256 + 72 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFa.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFas ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2448 + 1) with (fr + 2448 + 2 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFp.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFps ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2464 + 7) with (fr + 2464 + 8 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFn.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFns ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2496 + 7) with (fr + 2496 + 8 - 1) by lia. exact V.
        -- intros s2 (s20 & HQ2 & Hrel2 & _ & _ & _ & Hbyt2 & _ & Hmun2 & Hwm2 & _).
           destruct HQ2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                            -> & MUF0 & WMF0 & _ & STF0 & MEMF0 & _ & _).
           destruct (B.MemNormTr.ms_rel_MS s2 _ _ _ _ _ _ _ Hrel2) as (Es2 & Hmr2).
           pose proof (Hmun2 _ MUF0) as MUF.
           pose proof (Hwm2 WMF0) as WMF.
           pose proof (B.MemNormTr.stk_of_rel _ _ _ _ Hmr2 STF0) as STF.
           pose proof (B.Prog.Seg.R10.r10_fgmem_tr _ _ _ _ _ _ _ m0 (ms_mem s2)
                         (fun a bs (Hb : lib.Lib.Mem.bytes_at B.Img0.rsegs m0 a bs) => proj2 (Hbyt2 a bs) Hb) MEMF0)
             as MEMF.
           match type of STF with context [bv_unsigned ?x] =>
             replace (bv_unsigned x) with sp in MUF, STF by (symmetry; exact Usp) end.
           rewrite Es2.
           replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x81834)) with (Z_to_bv 64 0x81834)
             by (symmetry; apply lib.Lib.MState.ret_pc_even; [lia | reflexivity]).
           apply lib.Lib.ExecF.evtF_done.
           do 3 eexists. split; [reflexivity |].
           repeat (split; [reflexivity |]).
           split; [exact MUc |].
           split.
           { exists l7, c0, c1, c2. split; [exact Hl7' |]. split; [exact Hl7l |].
             split; [exact Hc0' |]. split; [exact V0 |]. split; [exact Hc1' |]. split; [exact V1 |].
             split; [exact Hc2' | exact V2]. }
           split; [exact MUF |]. split; [exact WMF |]. split; [exact STF | exact MEMF].
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m1 & m' & -> & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G26 & G27 &
                    G10 & MUh & (l7 & c0 & c1 & c2 & Hl7 & Hl7l & Hc0 & V0 & Hc1 & V1 & Hc2 & V2) & MUF & WMF & STF &
                    MEMF) Hhid Hsbm.
    rewrite Ecls in G10, MUF, MEMF.
    apply w2_cfg_back.
    assert (Hhid1 : forall x, Reusable.YA0n.w_H W3 x = true -> m1 x = mem3 x).
    { apply (w2_head_hid W3 mem3 m1 (B.ACtlCutP.Sfr fr + 306) (B.ACtlCutP.Sfr fr + 313) MUh).
      intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
    destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 m1 md3 md3 306 313 l7 HB HJ Hfrs Hfr6 HRT HFRAC HRBE
                ltac:(lia) ltac:(rewrite Hl7l; reflexivity) ltac:(lia) MUh Hl7 Hhid1
                (Reusable.YK04.same_but_materialized_refl md3))
      as (HJ1 & HRT1 & HFRAC1 & HRBE1 & MK1).
    pose proof HRBE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                         _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAD2256' & _).
    (* the journal across the call: it writes the record, the three cells (closing class) and its window *)
    set (WF := B.ACtlCutP.RFR.fg_fp B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256)
                 (fr + 2448) (fr + 2464) (fr + 2496) sp
                 (B.ACtlCutP.SM.fcls (rnb cx 6) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6)
                    (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6)))) in MUF.
    assert (Hin_W : forall x, ~ lib.Lib.Frame.outside WF x ->
                      (fr + 2256 <= x < fr + 2256 + 72) \/ (fr + 2448 <= x < fr + 2448 + 2) \/
                      (fr + 2464 <= x < fr + 2464 + 8) \/ (fr + 2496 <= x < fr + 2496 + 8) \/
                      (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= x < sp))
      by (intros x Hx; exact (B.Prog.Seg.R10.r10_fgfp_in _ _ _ _ _ _ _ x Hx)).
    assert (Hout_W : forall x, ~ (fr + 2256 <= x < fr + 2256 + 72) -> ~ (fr + 2448 <= x < fr + 2448 + 2) ->
                       ~ (fr + 2464 <= x < fr + 2464 + 8) -> ~ (fr + 2496 <= x < fr + 2496 + 8) ->
                       ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= x < sp) ->
                       lib.Lib.Frame.outside WF x).
    { intros x N1 N2 N3 N4 N5. destruct (B.Prog.Seg.R10.r10_out_dec WF x) as [Ho | Hno]; [exact Ho |].
      exfalso. destruct (Hin_W x Hno) as [H | [H | [H | [H | H]]]]; contradiction. }
    assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
    { apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
               (fun a => ~ lib.Lib.Frame.outside WF a) HJ1).
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MUF x); [reflexivity |].
        destruct (B.Prog.Seg.R10.r10_out_dec WF (bv_unsigned x)) as [Ho | Hno]; [exact Ho | exfalso; exact (Hx Hno)].
      - intros x Hx. unfold Reusable.YK04.mrestrict in *.
        destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx |].
        pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
        assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
        { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          apply Z.mod_small. exact Hxr. }
        destruct (B.Prog.Seg.R10.r10_out_dec WF (bv_unsigned x)) as [Ho | Hno];
          [rewrite (MUF x Ho); exact Hx |].
        destruct (B.Prog.Seg.R10.r10_fg_rd (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                    (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 6) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 6))
                    (rnb cx 6) m' B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K sp
                    (bv_unsigned x) MEMF HstL HgL STF Hno) as (bb & Hbb).
        assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
        { destruct (Hin_W _ Hno) as [H | [H | [H | [H | H]]]]; try (apply Hfimg; lia).
          intros Hi. pose proof (w2_segs_low _ Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl.
          unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in H. lia. }
        rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr Hni Hbb). discriminate.
      - intros x Hx. transitivity (mem3 x); [exact (Hhid x Hx) | symmetry; exact (Hhid1 x Hx)].
      - exact Hsbm.
      - intros a Ha. destruct (Hin_W a Ha) as [H | [H | [H | [H | H]]]].
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + left. unfold Reusable.YCfn.LLVMF_STK.
          unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in H. lia. }
    pose proof HJ' as (HAR' & _).
    assert (HRT' : B.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ').
    (* the kept reads across the call *)
    assert (KK : forall a, 0 <= a < 2 ^ 64 ->
                   ~ (fr + 2256 <= a < fr + 2256 + 72) -> ~ (fr + 2448 <= a < fr + 2448 + 2) ->
                   ~ (fr + 2464 <= a < fr + 2464 + 8) -> ~ (fr + 2496 <= a < fr + 2496 + 8) ->
                   ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= a < sp) ->
                   lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m1 (Z_to_bv 64 a))
      by (intros a Ha N1 N2 N3 N4 N5; exact (w2_munch_mrd _ m1 m' a MUF Ha (Hout_W a N1 N2 N3 N4 N5))).
    assert (KW : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
                   (forall a, lo <= a < hi ->
                      ~ (fr + 2256 <= a < fr + 2256 + 72) /\ ~ (fr + 2448 <= a < fr + 2448 + 2) /\
                      ~ (fr + 2464 <= a < fr + 2464 + 8) /\ ~ (fr + 2496 <= a < fr + 2496 + 8) /\
                      ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= a < sp)) ->
                   KEEPR m1 m' lo hi).
    { intros lo hi L1 L2 K a Ha. destruct (K a Ha) as (N1 & N2 & N3 & N4 & N5). apply KK; [lia | | | | |]; assumption. }
    unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in KK, KW.
    assert (KF2 : forall lo hi, fr <= lo -> hi <= fr + 4096 ->
                    (hi <= fr + 2256 \/ fr + 2328 <= lo) -> (hi <= fr + 2448 \/ fr + 2504 <= lo) -> KEEPR m1 m' lo hi)
      by (intros lo hi L1 L2 L3 L4; apply KW; [lia | lia |]; intros a Ha; repeat split; lia).
    assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m1 lo hi)
      by (intros lo hi L1 L2; apply MK1; [lia | lia | intros a Ha; lia]).
    assert (KFF : forall lo hi, fr <= lo -> hi <= fr + 4096 ->
                    (hi <= fr + 2256 \/ fr + 2328 <= lo) -> (hi <= fr + 2448 \/ fr + 2504 <= lo) ->
                    KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2 L3 L4; exact (w2_keep_trans _ _ _ lo hi (KF1 lo hi L1 L2) (KF2 lo hi L1 L2 L3 L4))).
    assert (KS2 : KEEPR m1 m' (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW)).
    { apply KW; [lia | unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES; lia |]. intros a Ha.
      unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in Ha. repeat split; lia. }
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 m').
    { apply (w2_frac_mem cx fr fr regs3 m1 m'); [| | exact KS2 | | exact HFRAC1].
      - intros a Ha Hb'. rewrite Hspz in Ha. unfold B.ACtlCutP.FRAME_BYTES in Hb'.
        apply KK; [lia | lia | lia | lia | lia | lia].
      - apply KF2; lia.
      - apply KF2; lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 m').
    { apply (w2_rbe_mem cx fr regs3 m1 m' A H9 ltac:(lia) ltac:(lia) ltac:(lia)).
      - apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - intros a Ha _. apply KS2. exact Ha.
      - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
        apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - exact (w2_kept_ro m1 m' _ _ HRT1 HRT' w2_box_ro).
      - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
          by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
        rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
        unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
        apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - intros Hh Hr. split.
        + exact (w2_kept_ro m1 m' _ _ HRT1 HRT' (w2_names_ro _ Hh Hr)).
        + exact (ctl_names_addressable _ _ _ _ _ _ HAR' Hh Hr).
      - exact HRBE1. }
    rewrite Hcls in MEMF. cbn [B.Prog.reac_ctrl_identity_fragment_c.fg_mem] in MEMF.
    destruct MEMF as (HfgN & Hfpa & Hfpp & Hfpn).
    (* the successor cut *)
    apply (H834 cx [Z.of_nat 6] fr k ly3 S3 W3 R m' md' HB HJ' Hfrs Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81834_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81834_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi.
      unfold B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
      split; [exact Hperm |].
      split; [exact (w2_frac_regs cx fr fr regs3 R m' G2 G3 G4 G8 G9 G19 G26 HFRAC2) |].
      split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { split; [exact Hphinz |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR' Hin3 ltac:(lia)). }
      split; [exact (w2_rgv_move R regs3 22 _ G22 H22) |].
      split.
      { eapply w2_bytes_keep; [| exact HOUR].
        apply KFF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      split; [exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR) |].
      split; [exact (w2_rbe_regs cx fr regs3 R m' G9 HRBE2) |].
      split; [unfold B.ACtlCut.rgv; exact G21 |].
      split; [reflexivity |].
      split; [exact Hnz |].
      split; [exact (w2_rgv_move R regs3 20 _ G20 H20) |].
      split; [eapply w2_bytes_keep; [| exact HIDB]; apply KFF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia |].
      split.
      { rewrite (B.Prog.Seg.R10.r10_st6 (B.ACtlCut.c_in cx) 6 eq_refl Hnz).
        change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 6)) with (rnb cx 6).
        unfold B.ACtlCutP.SM.fg_st. rewrite Hcls. cbn [B.ACtlCutP.SM.fg_next]. exact HfgN. }
      split.
      { apply (w2_addr_keep m1); [| exact HAD2256'].
        intros i Hi. apply KK; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia. }
      split; [unfold B.ACtlCut.a0v, B.ACtlCut.rgv, B.ACtlCutP.SM.fg_rf; exact G10 |].
      split; [intros _; split; [exact Hfpa |]; split; [exact Hfpp | exact Hfpn] |].
      exact (w2_rgv_move R regs3 27 _ G27 H27).
    + exact HRT'.
Qed.

(* S_R10, b = 5: R10F.r10_head_frag5_F (0x817a4 -> 0x818f8; the reply cells' shadow [Sfr fr + 306, + 313)), then
   R10F.r10_frag5_call_pre_F (-> reac_ctrl_identity_fragment 0x859e4, ra = 0x81914), then the fragment by its route-C
   footprint contract on the normalized memory, as at b = 6.  Turn 5 is not a closing fragment (the cut's
   fg_rf = 0 conjunct), so a0 = 0, RID 6 = RID 5 and RFG 6 = fg_st (R10.r10_st5, R10.r10_fgb) -> C_B81914_at. *)
Lemma w2_R10_b5 : forall POST (b : nat), b = 5%nat -> CFb POST C81914 b -> CFb POST C817a4 b.
Proof.
  intros POST b Hb5' H914 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817a4_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Ha0 & HRF & S24 & S16 &
                     S96 & S120 & HAD2256 & Hfg5 & H27).
  subst b.
  destruct HRF as ((HRB & Hnz & H20 & HFb) & H18).
  pose proof HRB as (_ & _ & _ & _ & HIDB & HFGB).
  destruct (B.Prog.Seg.R10.r10_rtk (B.ACtlCut.c_in cx) 5 ltac:(lia) Hnz) as (Hk0 & Hn52 & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 5)) with (rnb cx 5) in Hn52, HlF.
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 5) Hnz) as (_ & Hnr & _).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 5)) with (rnb cx 5) in Hnr.
  unfold B.ACtlCut.a0v, B.ACtlCut.rgv in Ha0. rewrite Hk0 in Ha0.
  assert (Hphinz : phi <> 0) by exact (proj1 HHB).
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Usp : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = sp)
    by (unfold Reusable.YG0d.spZ in Hspz; exact Hspz).
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & Hwle0 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfa3' : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr) by (rewrite Hfa3, <- Hfr6; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Hfc & _).
  rewrite Hfa3', Hfsb in Hfc.
  assert (Hin3 : In (phi, rnb cx 5) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 5) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx 5) = rnb cx 5)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx 5 =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 5) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3', Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (w2_rgv_unsigned regs3 19 _ H19
                ltac:(unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia)) as U19.
  pose proof (w2_rgv_unsigned regs3 9 A H9 ltac:(lia)) as U9.
  assert (HSf : 0x7fff8000 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  assert (ESf : B.ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr)
    by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
          Reusable.YG0f.SHADOW_OFF; lia).
  (* the frame lies off the image (so off the runtime's cells) *)
  assert (HfRT : fr + 4096 <= Reusable.YImgTop.IMG_LO \/ Reusable.YImgTop.IMG_TOP <= fr).
  { destruct (Z_lt_le_dec fr Reusable.YImgTop.IMG_TOP) as [L1 | L1]; [left | right; exact L1].
    destruct (Z_lt_le_dec Reusable.YImgTop.IMG_LO (fr + 4096)) as [L2 | L2]; [exfalso | exact L2].
    apply (Hfimg (Z.max fr Reusable.YImgTop.IMG_LO) ltac:(lia)). apply w2_in_img. lia. }
  (* turn 5: not a closing fragment; its records *)
  assert (Ecls : B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 5)
                   (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)) =
                 B.ACtlCutP.SM.fcls (rnb cx 5) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
                   (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)))
    by (apply B.Prog.Seg.R10.r10_fgc; lia).
  assert (Hrf : B.ACtlCutP.SM.fg_rf (rnb cx 5) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
                  (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)) = 0)
    by exact (Hfg5 eq_refl).
  destruct (B.Prog.Seg.R10.r10_st5 (B.ACtlCut.c_in cx) 5 eq_refl Hnz Hrf) as (EID & EFG).
  assert (HstL : length (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) = 72%nat)
    by exact (B.Prog.Seg.RtmB.rb_RFG_len _ 5 ltac:(lia)).
  assert (HgL : length (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)) = 50%nat)
    by (unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50; rewrite length_firstn, length_app, repeat_length; lia).
  (* the seven shadow bytes r10_head_frag5_F overwrites, writable on the normalized memory *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (w2_bytes_bsl mem3 (B.ACtlCutP.Sfr fr) sh 306 7 Hsh ltac:(lia)) as Hjunk.
  change (Z.of_nat 306) with 306 in Hjunk.
  assert (Hjl : length (firstn 7 (skipn 306 sh)) = 7%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RO3 : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  assert (RWn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                  (B.ACtlCutP.Sfr fr + 306) [lib.Lib.Cells.CB 7 (firstn 7 (skipn 306 sh))]).
  { apply B.MemNormTr.rw_cells_normalize; [exact RO3 | |].
    - intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img.
      unfold B.Prog.ImgBounds.IMG_HI. lia.
    - pose proof (w2_rw_CB mem3 _ _ Hjunk) as H. rewrite Hjl in H. apply H.
      split; [lia |]. split; [lia |]. intros i Hi.
      rewrite ESf in *.
      destruct (proj2 (Hfsvis (Reusable.YG0f.shadow_addr fr + 306 + i) ltac:(lia))) as (bb & Hbb).
      exact (w2_wview_some _ _ _ Hbb). }
  pose proof B.ProgWorld.rebase_ro_normalize as RB. unfold B.ProgWorld.rebase_ro_normalize_stmt in RB.
  pose proof B.Prog.reac_ctrl_identity_fragment_F_closed.reac_ctrl_identity_fragment_holds_F_closed_on as HFG.
  unfold B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract_F_on in HFG.
  (* the run: the head and the call's pre on rebased memory, then the fragment on the normalized memory again *)
  eapply w2_lift with (P := fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81914) lib.Reusable.YK11.fp_csr None m'
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
      lib.Reusable.YK11.getr R 21 = Z_to_bv 64 36 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
      lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
      lib.Reusable.YK11.getr R 10 =
        Z_to_bv 64 (B.ACtlCutP.RFR.fg_ret (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                      (fr + 2496) (rnb cx 5) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
                      (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)))) /\
      lib.Lib.Frame.munch [(B.ACtlCutP.Sfr fr + 306, B.ACtlCutP.Sfr fr + 313)] mem3 m1 /\
      (exists (l7 : list byte) (c0 c1 c2 : byte),
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 306) l7 /\ length l7 = 7%nat /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 306) [c0] /\ bv_signed c0 = 2 /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 308) [c1] /\ bv_signed c1 = 0 /\
         lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (B.ACtlCutP.Sfr fr + 312) [c2] /\ bv_signed c2 = 0) /\
      lib.Lib.Frame.munch
        (B.ACtlCutP.RFR.fg_fp B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256)
           (fr + 2448) (fr + 2464) (fr + 2496) sp
           (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 5)
              (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5))))
        m1 m' /\
      lib.Lib.Frame.wmono B.Img0.rsegs m1 m' /\
      lib.Lib.Frame.stk B.Img0.rsegs m'
        (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) sp /\
      B.Prog.reac_ctrl_identity_fragment_c.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
        (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5))
        (B.ACtlCutP.RFR.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) (rnb cx 5)
           (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5))) m').
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + eapply RB; [exact RO3 |].
      eapply (B.Prog.Seg.R10F.r10_head_frag5_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (junk := firstn 7 (skipn 306 sh)).
      * exact H21.
      * exact H22.
      * exact Ha0.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        exact RWn.
      * apply B.MemNorm.mem_inv_normalize.
      * match goal with |- context [bv_unsigned ?x + 306] =>
          replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) by (symmetry; exact U19) end.
        apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))).
    + intros s (s0 & HQ & Hrel & HROs & _ & _ & Hbyt & _ & Hmun & _ & _).
      destruct HQ as (m1 & l7 & c0 & c1 & c2 & -> & MU1 & _ & _ & Hc0 & V0 & Hc1 & V1 & Hc2 & V2 & Hl7 & Hl7l).
      match type of MU1 with context [bv_unsigned ?x + 306] =>
        replace (bv_unsigned x) with (B.ACtlCutP.Sfr fr) in MU1, Hc0, Hc1, Hc2, Hl7 by (symmetry; exact U19) end.
      pose proof (Hmun _ MU1) as MUc.
      pose proof (proj2 (Hbyt _ _) Hl7) as Hl7'.
      pose proof (proj2 (Hbyt _ _) Hc0) as Hc0'.
      pose proof (proj2 (Hbyt _ _) Hc1) as Hc1'.
      pose proof (proj2 (Hbyt _ _) Hc2) as Hc2'.
      destruct (B.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ Hrel) as (Es & _).
      rewrite Es.
      (* the cut-like facts after the head, at its raw memory *)
      assert (Hhid1 : forall x, Reusable.YA0n.w_H W3 x = true -> ms_mem s x = mem3 x).
      { apply (w2_head_hid W3 mem3 (ms_mem s) (B.ACtlCutP.Sfr fr + 306) (B.ACtlCutP.Sfr fr + 313) MUc).
        intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
      destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 (ms_mem s) md3 md3 306 313 l7 HB HJ Hfrs Hfr6 HRT HFRAC
                  HRBE ltac:(lia) ltac:(rewrite Hl7l; reflexivity) ltac:(lia) MUc Hl7' Hhid1
                  (Reusable.YK04.same_but_materialized_refl md3))
        as (HJ1 & HRT1 & HFRAC1 & HRBE1 & MK1).
      pose proof HJ1 as (HAR1 & _).
      pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1 & _).
      unfold Reusable.YCfn.LLVMF_STK in Hwin1.
      pose proof HRBE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S240' & S232' & S224' &
                           _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S112' & HAD2256' & _).
      pose proof (w2_spill_at regs3 (ms_mem s) A 112 (fr + 2256) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S112')
        as Q112.
      pose proof (w2_spill_at regs3 (ms_mem s) A 240 (fr + 2448) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S240')
        as Q240.
      pose proof (w2_spill_at regs3 (ms_mem s) A 232 (fr + 2464) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S232')
        as Q232.
      pose proof (w2_spill_at regs3 (ms_mem s) A 224 (fr + 2496) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S224')
        as Q224.
      assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 (ms_mem s) lo hi)
        by (intros lo hi L1 L2; apply MK1; [lia | lia | intros a Ha; lia]).
      assert (HPF1 : forall a, fr <= a < fr + 4096 -> exists bb, ms_mem s (Z_to_bv 64 a) = Some bb).
      { intros a Ha. destruct (proj2 (Hfvis a Ha)) as (bb & Hbb). exists bb.
        rewrite (MUc (Z_to_bv 64 a)); [exact Hbb |].
        rewrite lib.Lib.MState.unsigned_lit by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
      assert (Hrel1 : B.MemNorm.mem_rel B.Img0.rsegs (ms_mem s) (B.MemNorm.normalize B.Img0.rsegs (ms_mem s)))
        by exact (B.MemNorm.mem_rel_normalize B.Img0.rsegs (ms_mem s) HROs).
      assert (ROF : forall a n, fr <= a -> a + n <= fr + 4096 ->
                      forall i, 0 <= i < n -> lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa (a + i)) = false)
        by (intros a n L1 L2 i Hi; apply w2_ro_false; [lia | apply Hfimg; lia]).
      assert (WRN : forall a n, fr <= a -> 0 <= n -> a + n <= fr + 4096 ->
                      lib.Lib.Mem.wr_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs (ms_mem s)) a n).
      { intros a n L1 L2 L3. apply (B.MemNorm.wr_at_norm B.Img0.rsegs (ms_mem s)); [exact Hrel1 | | apply ROF; lia].
        apply w2_wr_of_present; [lia | lia | lia |]. intros i Hi. apply HPF1. lia. }
      assert (HFGB1 : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) (fr + 2256)
                        (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)).
      { unfold B.ACtlCutP.FGBr in HFGB. eapply w2_bytes_keep; [| exact HFGB]. apply KF1; rewrite ?HstL; lia. }
      assert (Hg1 : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) phi
                      (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5))).
      { assert (HF' : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) phi
                        (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat 5))).
        { eapply w2_bytes_keep; [| exact HFb]. rewrite HlF. apply MK1; [lia | lia |]. intros a Ha.
          unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
        assert (HL50 : (50 <= length (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat 5)))%nat)
          by (apply Nat2Z.inj_le; rewrite HlF; lia).
        pose proof (w2_bytes_bsl (ms_mem s) phi _ 0 50 HF' HL50) as H50.
        cbn [skipn] in H50. change (Z.of_nat 0) with 0 in H50. rewrite Z.add_0_r in H50.
        unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite firstn_app.
        rewrite (proj2 (Nat.sub_0_le 50 _) HL50).
        rewrite firstn_O, app_nil_r. exact H50. }
      destruct (ctl_bcmp_cells_of_AR _ _ _ _ _ HAR1) as (CB1 & CB2 & CB3 & CB4 & CB5).
      assert (Hpa : B.AsanRT.addressable (ms_mem s) (fr + 2448) 2).
      { apply (w2_addr_granule (ms_mem s) (fr + 2448) 2 c0);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | right; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2448)) with (B.ACtlCutP.Sfr fr + 306)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc0'. }
      assert (Hpp : B.AsanRT.addressable (ms_mem s) (fr + 2464) 8).
      { apply (w2_addr_granule (ms_mem s) (fr + 2464) 8 c1);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2464)) with (B.ACtlCutP.Sfr fr + 308)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc1'. }
      assert (Hpn : B.AsanRT.addressable (ms_mem s) (fr + 2496) 8).
      { apply (w2_addr_granule (ms_mem s) (fr + 2496) 8 c2);
          [lia | lia | lia | unfold B.AsanRT.APPMEM_END; lia | | | left; lia].
        - intros i Hi. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        - replace (B.AsanRT.shadow_addr (fr + 2496)) with (B.ACtlCutP.Sfr fr + 312)
            by (unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr; lia).
          exact Hc2'. }
      assert (Hph1 : B.AsanRT.addressable (ms_mem s) phi 50).
      { pose proof (w2_block_addressable _ _ _ _ _ _ _ HAR1 Hin3 ltac:(lia)) as (A0 & A1 & A2 & A3).
        split; [lia |]. split; [lia |]. split; [lia |]. intros i Hi. apply A3. lia. }
      assert (VF : forall lo len, Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) <= lo ->
                     lo + len <= Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) +
                                 Reusable.YG00.fs_frame_bytes 6 ->
                     B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len /\
                     (0 <= len -> Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) <= 64 * (lo / 64) ->
                      64 * ((lo + len - 1) / 64) + 64 <=
                        Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6 ->
                      len = 0 \/ B.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                                   (B.Prog.rng_asan.sh_al8_lo lo)
                                   (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo)))
        by (intros lo len;
            exact (B.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) lo len HAR3 Hin6)).
      rewrite Hfa3', Hfsb in VF.
      destruct (VF (fr + 2256) 72 ltac:(lia) ltac:(lia)) as (VFf & VFfs).
      destruct (VF (fr + 2448) 2 ltac:(lia) ltac:(lia)) as (VFa & VFas).
      destruct (VF (fr + 2464) 8 ltac:(lia) ltac:(lia)) as (VFp & VFps).
      destruct (VF (fr + 2496) 8 ltac:(lia) ltac:(lia)) as (VFn & VFns).
      destruct (img_vis_W W3) as (_ & _ & VI).
      eapply lib.Lib.ExecF.evtF_cut.
      * eapply (B.Prog.Seg.R10F.r10_frag5_call_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (fr := fr).
        -- match goal with |- context [bv_unsigned ?x + 112] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q112.
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q240.
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q232.
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply w2_ro8. exact Q224.
        -- match goal with |- context [bv_unsigned ?x + 112] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 240] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 232] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
        -- match goal with |- context [bv_unsigned ?x + 224] =>
             replace (bv_unsigned x) with A by (symmetry; exact U9) end.
           apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
           intros a Ha. exact (proj1 (Hsvis a ltac:(lia))).
      * intros ms1 ->.
        eapply lib.Lib.ExecF.evtF_cut.
        -- eapply RB; [exact HROs |].
           eapply (HFG (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
             (f := fr + 2256) (fr := phi) (len := rnb cx 5) (pa := fr + 2448) (pp := fr + 2464) (pn := fr + 2496)
             (st := B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
             (g := B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)).
           ++ reflexivity.
           ++ exact H20.
           ++ exact H18.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              exact Hsp16.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              apply B.MemNormTr.stk_normalize_ro; [exact HROs | |].
              ** unfold B.Prog.ImgBounds.IMG_HI, B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K.
                 lia.
              ** apply (w2_stk_of_present W3); [unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
                                                lia | lia |].
                 intros a Ha. unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in Ha.
                 apply Hwin1. lia.
           ++ exact HgL.
           ++ exact HstL.
           ++ intros _ _ _ _ _ _. exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs Hg1).
           ++ intros _ _ _ _ _.
              split.
              { apply B.MemNormTr.rw_cells_normalize; [exact HROs | |].
                - intros i Hi. cbn in Hi. apply (ROF (fr + 2256) 72); lia.
                - pose proof (w2_rw_CB (ms_mem s) _ _ HFGB1) as H. rewrite HstL in H. apply H.
                  apply w2_wr_of_present; [lia | lia | lia |]. intros i Hi. apply HPF1. lia. }
              split; [lia |]. split; [lia |]. split; [lia |].
              split; [apply WRN; lia |]. split; [apply WRN; lia |]. split; [apply WRN; lia |].
              match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              cbn [B.ACtlCutP.RFR.all_dj B.ACtlCutP.RFR.dj_from].
              unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. repeat split; lia.
           ++ apply B.MemNorm.mem_inv_normalize.
           ++ apply B.MemNormTr.asan_cells_normalize; [exact HROs | exact (proj1 HRT1)].
           ++ apply w2_srw_on_normalize; [exact HROs |].
              intros a HRa Hsha. apply (proj1 (proj2 HRT1)); [| exact Hsha].
              exact (w2_fragR_cut cx ly3 S3 fr phi (rnb cx 5) (rnb cx 5) _ _ a Hfrs Hfa3' ltac:(lia) ltac:(lia) Hin3
                       ltac:(lia) ltac:(lia) ltac:(lia) HRa).
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.AsanRT.HIGHMEM_BEG,
                B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.AsanRT.APPMEM_END. lia.
           ++ intros _ _ _ _ _ _. exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hph1).
           ++ intros _ _ _ _ _.
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs HAD2256') |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpa) |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpp) |].
              split; [exact (B.MemNormTr.addressable_normalize _ _ _ HROs Hpn) |].
              split; [unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia |].
              cbn [B.ACtlCutP.RFR.dj_from]. unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI. repeat split; lia.
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB1).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB2).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB3).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB4).
           ++ exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs _ _ _ HROs CB5).
           ++ apply B.ProgBridge.rng_bytes_RNG_W.
           ++ apply B.ProgBridge.rng_of_visible.
              split; [unfold B.Prog.ImgBounds.IMG_LO; lia |].
              split; [unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia |].
              intros a Ha. apply VI. unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Ha.
              lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              apply B.ProgBridge.rng_of_visible.
              apply (w2_vis_stack cx (own6 cx) ly3 S3 W3 mem3 md3 k); [exact HJ | | | ];
                unfold Reusable.YCfn.LLVMF_STK, B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K;
                lia.
           ++ match goal with |- context [bv_unsigned ?x] =>
                replace (bv_unsigned x) with sp by (symmetry; exact Usp) end.
              unfold B.Prog.rng_asan.sh_word_rng. right. apply B.ProgBridge.rng_of_visible.
              apply (w2_rv_wle (B.ACtlCut.c_W cx) W3); [exact Hwle0 |].
              destruct (B.ProgWorldVisWin.win_sh_vis B LAWS (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx)
                          (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
                          (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K)
                          B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K HAR0
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia)
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia)
                          ltac:(unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia))
                as [E | V].
              ** unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in E. lia.
              ** exact V.
           ++ intros _ _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              split; [lia |]. split; [lia |]. intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
           ++ intros _ _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (B.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 5) phi 50 HAR3 Hin3
                          ltac:(lia) ltac:(rewrite Er; lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (phi + 49) with (phi + 50 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFf.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFfs ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2256 + 71) with (fr + 2256 + 72 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFa.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFas ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2448 + 1) with (fr + 2448 + 2 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFp.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFps ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2464 + 7) with (fr + 2464 + 8 - 1) by lia. exact V.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible. exact VFn.
           ++ intros _ _ _ _ _. apply B.ProgBridge.rng_of_visible.
              destruct (VFns ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
              unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V.
              replace (fr + 2496 + 7) with (fr + 2496 + 8 - 1) by lia. exact V.
        -- intros s2 (s20 & HQ2 & Hrel2 & _ & _ & _ & Hbyt2 & _ & Hmun2 & Hwm2 & _).
           destruct HQ2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                            -> & MUF0 & WMF0 & _ & STF0 & MEMF0 & _ & _).
           destruct (B.MemNormTr.ms_rel_MS s2 _ _ _ _ _ _ _ Hrel2) as (Es2 & Hmr2).
           pose proof (Hmun2 _ MUF0) as MUF.
           pose proof (Hwm2 WMF0) as WMF.
           pose proof (B.MemNormTr.stk_of_rel _ _ _ _ Hmr2 STF0) as STF.
           pose proof (B.Prog.Seg.R10.r10_fgmem_tr _ _ _ _ _ _ _ m0 (ms_mem s2)
                         (fun a bs (Hb : lib.Lib.Mem.bytes_at B.Img0.rsegs m0 a bs) => proj2 (Hbyt2 a bs) Hb) MEMF0)
             as MEMF.
           match type of STF with context [bv_unsigned ?x] =>
             replace (bv_unsigned x) with sp in MUF, STF by (symmetry; exact Usp) end.
           rewrite Es2.
           replace (lib.Lib.MState.ret_pc (Z_to_bv 64 0x81914)) with (Z_to_bv 64 0x81914)
             by (symmetry; apply lib.Lib.MState.ret_pc_even; [lia | reflexivity]).
           apply lib.Lib.ExecF.evtF_done.
           do 3 eexists. split; [reflexivity |].
           repeat (split; [reflexivity |]).
           split; [exact MUc |].
           split.
           { exists l7, c0, c1, c2. split; [exact Hl7' |]. split; [exact Hl7l |].
             split; [exact Hc0' |]. split; [exact V0 |]. split; [exact Hc1' |]. split; [exact V1 |].
             split; [exact Hc2' | exact V2]. }
           split; [exact MUF |]. split; [exact WMF |]. split; [exact STF | exact MEMF].
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m1 & m' & -> & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G26 & G27 &
                    G10 & MUh & (l7 & c0 & c1 & c2 & Hl7 & Hl7l & Hc0 & V0 & Hc1 & V1 & Hc2 & V2) & MUF & WMF & STF &
                    MEMF) Hhid Hsbm.
    rewrite Ecls in G10, MUF, MEMF.
    apply w2_cfg_back.
    assert (Hhid1 : forall x, Reusable.YA0n.w_H W3 x = true -> m1 x = mem3 x).
    { apply (w2_head_hid W3 mem3 m1 (B.ACtlCutP.Sfr fr + 306) (B.ACtlCutP.Sfr fr + 313) MUh).
      intros a Ha. rewrite ESf in Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
    destruct (w2_fsh_write cx fr k ly3 S3 W3 regs3 mem3 m1 md3 md3 306 313 l7 HB HJ Hfrs Hfr6 HRT HFRAC HRBE
                ltac:(lia) ltac:(rewrite Hl7l; reflexivity) ltac:(lia) MUh Hl7 Hhid1
                (Reusable.YK04.same_but_materialized_refl md3))
      as (HJ1 & HRT1 & HFRAC1 & HRBE1 & MK1).
    (* the journal across the call: it writes at most the record, the three cells and its window *)
    set (WF := B.ACtlCutP.RFR.fg_fp B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256)
                 (fr + 2448) (fr + 2464) (fr + 2496) sp
                 (B.ACtlCutP.SM.fcls (rnb cx 5) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
                    (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)))) in MUF.
    assert (Hin_W : forall x, ~ lib.Lib.Frame.outside WF x ->
                      (fr + 2256 <= x < fr + 2256 + 72) \/ (fr + 2448 <= x < fr + 2448 + 2) \/
                      (fr + 2464 <= x < fr + 2464 + 8) \/ (fr + 2496 <= x < fr + 2496 + 8) \/
                      (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= x < sp))
      by (intros x Hx; exact (B.Prog.Seg.R10.r10_fgfp_in _ _ _ _ _ _ _ x Hx)).
    assert (Hout_W : forall x, ~ (fr + 2256 <= x < fr + 2256 + 72) -> ~ (fr + 2448 <= x < fr + 2448 + 2) ->
                       ~ (fr + 2464 <= x < fr + 2464 + 8) -> ~ (fr + 2496 <= x < fr + 2496 + 8) ->
                       ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= x < sp) ->
                       lib.Lib.Frame.outside WF x).
    { intros x N1 N2 N3 N4 N5. destruct (B.Prog.Seg.R10.r10_out_dec WF x) as [Ho | Hno]; [exact Ho |].
      exfalso. destruct (Hin_W x Hno) as [H | [H | [H | [H | H]]]]; contradiction. }
    assert (HJ' : AJ cx (own6 cx) ly3 S3 W3 m' md' k).
    { apply (Reusable.YCbq.ajournal_exec segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
               (fun a => ~ lib.Lib.Frame.outside WF a) HJ1).
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MUF x); [reflexivity |].
        destruct (B.Prog.Seg.R10.r10_out_dec WF (bv_unsigned x)) as [Ho | Hno]; [exact Ho | exfalso; exact (Hx Hno)].
      - intros x Hx. unfold Reusable.YK04.mrestrict in *.
        destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx |].
        pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
        assert (Ex : Z_to_bv 64 (bv_unsigned x) = x).
        { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          apply Z.mod_small. exact Hxr. }
        destruct (B.Prog.Seg.R10.r10_out_dec WF (bv_unsigned x)) as [Ho | Hno];
          [rewrite (MUF x Ho); exact Hx |].
        destruct (B.Prog.Seg.R10.r10_fg_rd (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                    (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5))
                    (rnb cx 5) m' B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K sp
                    (bv_unsigned x) MEMF HstL HgL STF Hno) as (bb & Hbb).
        assert (Hni : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
        { destruct (Hin_W _ Hno) as [H | [H | [H | [H | H]]]]; try (apply Hfimg; lia).
          intros Hi. pose proof (w2_segs_low _ Hi) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl.
          unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in H. lia. }
        rewrite <- Ex. rewrite (w2_mrd_raw m' _ bb Hxr Hni Hbb). discriminate.
      - intros x Hx. transitivity (mem3 x); [exact (Hhid x Hx) | symmetry; exact (Hhid1 x Hx)].
      - exact Hsbm.
      - intros a Ha. destruct (Hin_W a Ha) as [H | [H | [H | [H | H]]]].
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
          left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Hfa3', Hfsb. lia.
        + left. unfold Reusable.YCfn.LLVMF_STK.
          unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in H. lia. }
    pose proof HJ' as (HAR' & _).
    assert (HRT' : B.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ').
    (* the kept reads across the call *)
    assert (KK : forall a, 0 <= a < 2 ^ 64 ->
                   ~ (fr + 2256 <= a < fr + 2256 + 72) -> ~ (fr + 2448 <= a < fr + 2448 + 2) ->
                   ~ (fr + 2464 <= a < fr + 2464 + 8) -> ~ (fr + 2496 <= a < fr + 2496 + 8) ->
                   ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= a < sp) ->
                   lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m1 (Z_to_bv 64 a))
      by (intros a Ha N1 N2 N3 N4 N5; exact (w2_munch_mrd _ m1 m' a MUF Ha (Hout_W a N1 N2 N3 N4 N5))).
    assert (KW : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
                   (forall a, lo <= a < hi ->
                      ~ (fr + 2256 <= a < fr + 2256 + 72) /\ ~ (fr + 2448 <= a < fr + 2448 + 2) /\
                      ~ (fr + 2464 <= a < fr + 2464 + 8) /\ ~ (fr + 2496 <= a < fr + 2496 + 8) /\
                      ~ (sp - B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K <= a < sp)) ->
                   KEEPR m1 m' lo hi).
    { intros lo hi L1 L2 K a Ha. destruct (K a Ha) as (N1 & N2 & N3 & N4 & N5). apply KK; [lia | | | | |]; assumption. }
    unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in KK, KW.
    assert (KF2 : forall lo hi, fr <= lo -> hi <= fr + 4096 ->
                    (hi <= fr + 2256 \/ fr + 2328 <= lo) -> (hi <= fr + 2448 \/ fr + 2504 <= lo) -> KEEPR m1 m' lo hi)
      by (intros lo hi L1 L2 L3 L4; apply KW; [lia | lia |]; intros a Ha; repeat split; lia).
    assert (KF1 : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 m1 lo hi)
      by (intros lo hi L1 L2; apply MK1; [lia | lia | intros a Ha; lia]).
    assert (KFF : forall lo hi, fr <= lo -> hi <= fr + 4096 ->
                    (hi <= fr + 2256 \/ fr + 2328 <= lo) -> (hi <= fr + 2448 \/ fr + 2504 <= lo) ->
                    KEEPR mem3 m' lo hi)
      by (intros lo hi L1 L2 L3 L4; exact (w2_keep_trans _ _ _ lo hi (KF1 lo hi L1 L2) (KF2 lo hi L1 L2 L3 L4))).
    assert (KS2 : KEEPR m1 m' (B.ACtlCutP.Sfr fr) (B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW)).
    { apply KW; [lia | unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES; lia |]. intros a Ha.
      unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in Ha. repeat split; lia. }
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 m').
    { apply (w2_frac_mem cx fr fr regs3 m1 m'); [| | exact KS2 | | exact HFRAC1].
      - intros a Ha Hb'. rewrite Hspz in Ha. unfold B.ACtlCutP.FRAME_BYTES in Hb'.
        apply KK; [lia | lia | lia | lia | lia | lia].
      - apply KF2; lia.
      - apply KF2; lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 m').
    { apply (w2_rbe_mem cx fr regs3 m1 m' A H9 ltac:(lia) ltac:(lia) ltac:(lia)).
      - apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - intros a Ha _. apply KS2. exact Ha.
      - pose proof B.Prog.Seg.R7.r7_tbl_len as Ht. rewrite Ht. unfold B.ACtlCutP.BAC.BA_FR.
        apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - exact (w2_kept_ro m1 m' _ _ HRT1 HRT' w2_box_ro).
      - assert (Hist : 0 <= B.ACtlCutP.SM.istar (B.ACtlCut.c_in cx) < B.ACtlCutP.SM.CAT_N)
          by (unfold B.ACtlCutP.SM.istar; apply Z.mod_pos_bound; unfold B.ACtlCutP.SM.CAT_N; lia).
        rewrite (B.Prog.Seg.R7.r7_mb_len (B.ACtlCut.c_in cx)).
        unfold B.ACtlCutP.SM.mrow, B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in *.
        apply KW; [lia | lia |]. intros a Ha. repeat split; lia.
      - intros Hh Hr. split.
        + exact (w2_kept_ro m1 m' _ _ HRT1 HRT' (w2_names_ro _ Hh Hr)).
        + exact (ctl_names_addressable _ _ _ _ _ _ HAR' Hh Hr).
      - exact HRBE1. }
    (* the record the call leaves (non-closing class) *)
    assert (HFGB1 : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (fr + 2256) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)).
    { unfold B.ACtlCutP.FGBr in HFGB. eapply w2_bytes_keep; [| exact HFGB]. apply KF1; rewrite ?HstL; lia. }
    assert (HFGN : lib.Lib.Mem.bytes_at B.Img0.rsegs m' (fr + 2256)
                     (B.ACtlCutP.SM.fg_st (rnb cx 5) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
                        (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)))).
    { apply (B.Prog.Seg.R10.r10_fgb B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256)
               (fr + 2448) (fr + 2464) (fr + 2496) sp (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 5)
               (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 5)) (rnb cx 5) m1 m').
      - unfold B.ACtlCutP.SM.fg_rf in Hrf. exact Hrf.
      - exact HFGB1.
      - exact MUF.
      - intros x Hx. rewrite HstL in Hx.
        unfold B.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      - exact MEMF. }
    (* the successor cut *)
    apply (H914 cx [Z.of_nat 5] fr k ly3 S3 W3 R m' md' HB HJ' Hfrs Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81914_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81914_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi.
      unfold B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
      assert (KOUR : lib.Lib.Mem.bytes_at B.Img0.rsegs m' (fr + 2624) (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx))).
      { eapply w2_bytes_keep; [| exact HOUR].
        apply KFF; try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      assert (KCUR : B.ACtlCutP.CUR cx 7 R) by exact (w2_cur_regs cx 7 regs3 R G23 G25 HCUR).
      assert (K22 : B.ACtlCut.rgv R 22 (Z.of_nat 5)) by exact (w2_rgv_move R regs3 22 _ G22 H22).
      split; [exact Hperm |].
      split; [exact (w2_frac_regs cx fr fr regs3 R m' G2 G3 G4 G8 G9 G19 G26 HFRAC2) |].
      split; [exact Hcn |]. split; [exact Hb6 |].
      split.
      { split; [exact Hphinz |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR' Hin3 ltac:(lia)). }
      split; [exact K22 |]. split; [exact KOUR |]. split; [exact KCUR |].
      split; [exact (w2_rbe_regs cx fr regs3 R m' G9 HRBE2) |].
      split; [unfold B.ACtlCut.rgv; exact G21 |].
      split.
      { split; [exact Hb6 |]. split; [exact KCUR |]. split; [exact KOUR |]. split; [exact K22 |].
        split.
        - rewrite EID. eapply w2_bytes_keep; [| exact HIDB].
          apply KFF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia.
        - rewrite EFG. change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 5)) with (rnb cx 5).
          exact HFGN. }
      split; [exact (w2_rgv_move R regs3 20 _ G20 H20) |].
      split.
      { unfold B.ACtlCut.a0v, B.ACtlCut.rgv. rewrite G10.
        unfold B.ACtlCutP.SM.fg_rf in Hrf. rewrite Hrf. reflexivity. }
      exact (w2_rgv_move R regs3 27 _ G27 H27).
    + exact HRT'.
Qed.

(* B817a4_at b (Inv_B817a4_at SIv:1811) -> B817ec_at, B81834_at, B818a8_at, B81914_at, B8194c_at (all at b).
   S_R10 (Slot.v:77; seg_R10 R10.v:4381), dispatch on the turn b (R10.v:9-17; `bgeu a1,a3` 0x817c4):
   - b = 0: R10F.r10_cfg0_F (R10F.v:71; 0x817a4 -> 0x818a8; source R10.v:134: s4 = phi, s5 = 4, s6 = 0, a0 = 9
     (rt_k at b = 0), rw_cells (s3 + 306) [CB 12 junk] (frame shadow, V5), mem_inv, rng RNG (s3 + 306) 12 (V5)) ->
     C_B818a8_at with i := 0 (a0 = a2 = phi + 18, a1 = 0 = rsum b 0, a3 = -(phi + 18), a4 = 32, s11 = 32, s5 = 36;
     ART.addressable (fr + 2528) 12 is the ports slot, kept).
   - b = 1, 2: R10F.r10_sum12_F (R10F.v:166; 0x817a4 -> 0x8194c; source R10.v:196, a0 = 5, bz = b; rng RNG
     (s3 + 306) 12 (V5)) -> C_B8194c_at with i := 0.
   - b = 3, 4: R10F.r10_head_reply_F (R10F.v:257; 0x817a4 -> 0x817d4; R10.v:252; rng RNG (s3 + 306) 7 (V5)),
     R10F.r10_reply_call_pre_F (R10F.v:501; 0x817d4 -> reac_ctrl_identity_reply entry 0x848fc, ra = 0x817ec;
     R10.v:401; a0 = s4 = phi, a1 = s2 = rnb, a2 / a3 / a4 = fr + 2448 / 2464 / 2496 from the spills 240 / 232 / 224
     (RBE), rng RNG (s1 + 240 / 232 / 224) 8 (V1)), reac_ctrl_identity_reply (cut-callee: its own
     stack_malloc_1 at 0x84978 and the one inside reac_ctrl_parse) by its caller-journal spec TREPLY (:291; a Theorem Labs lane;
     ctrl's contract reac_ctrl_identity_reply_c.v:46) -> 0x817ec = C_B817ec_at (a0 = reply_ret, the three
     reply cells at fr + 2448 / 2464 / 2496 written when reply_ok).
   - b = 6: R10F.r10_head_frag6_F (R10F.v:337; 0x817a4 -> 0x81818; R10.v:301; rng RNG (s3 + 306) 7 (V5)),
     R10F.r10_frag6_call_pre_F (R10F.v:581; 0x81818 -> reac_ctrl_identity_fragment entry 0x859e4, ra = 0x81834;
     R10.v:534; a0 = fr + 2256 (spill 112), a1 = s4 = phi, a2 = s2 = rnb, a3 / a4 / a5 = the three reply cells
     (spills 240 / 232 / 224), rng RNG (s1 + 112 / 240 / 232 / 224) 8 (V1)),
     B.Prog.reac_ctrl_identity_fragment_F_closed.reac_ctrl_identity_fragment_holds_F_closed_on (:4817, :5421; a Theorem Labs lane,
     inside the lifted run; premises = reac_ctrl_identity_fragment_contract_F_on's, reac_ctrl_identity_fragment_c.v:264;
     its image-range premise `rng RNG IMG_LO (IMG_HI - IMG_LO)` (:291) <- img_vis_W with RNG := RNG_W
     (w_H W3)) with st72 at fr + 2256 (FGBr), g50 at phi (bytes_at phi rt_F), the reply cells, -> 0x81834 =
     C_B81834_at (a0 = fg_rf .., FGBr at turn S b = the fragment record fg_mem writes).
   - b = 5: R10F.r10_head_frag5_F (R10F.v:414; 0x817a4 -> 0x818f8; R10.v:351; rng RNG (s3 + 306) 7 (V5)),
     R10F.r10_frag5_call_pre_F (R10F.v:644; 0x818f8 -> fragment entry 0x859e4, ra = 0x81914; R10.v:650; the same
     register map as frag6's, rng RNG (s1 + 112 / 240 / 232 / 224) 8 (V1)),
     reac_ctrl_identity_fragment_SRr_at (image range <- img_vis_W, as frag6) -> 0x81914 = C_B81914_at (a0 = 0: the
     body's (b = 5 -> fg_rf .. = 0) conjunct; RB at turn S b).
   Premises common to the five arms: phi + 18 < 2^64 and 0 <= phi from the live block (al_blocks); s3 = Sfr fr
   (FRAC); the fragment / reply arms add stk / addressable for the callee window (T1), the GOT / CF / REAL_BCMP cells
   (T11, inside asan_cells), fr + 3136 <= RT_LO \/ RT_HI <= fr (T13), the tls / fake-stack package (fp, fra_fp
   Seg/Tac_fsfree.v:964).  The three `_post_F` (R10F.v:520 / :601 / :669) take 0 steps at the return pc:
   r10_reply_call_post_F is NOT applied (identity_reply is a cut-callee, world-form post); r10_frag6_call_post_F /
   r10_frag5_call_post_F ARE cited after reac_ctrl_identity_fragment_SRr_at (a lifted callee: raw post with hidden
   bytes kept).  No trap in S_R10 (plan 6.2). *)
Lemma seg_R10 : forall POST (b : nat),
  CFb POST C817ec b -> CFb POST C81834 b -> CFb POST C818a8 b -> CFb POST C81914 b -> CFb POST C8194c b ->
  CFb POST C817a4 b.
Proof.
  intros POST b H7ec H834 H8a8 H914 H94c.
  destruct b as [| [| [| [| [| [| [| b]]]]]]].
  - exact (w2_R10_b0 POST 0 eq_refl H8a8).
  - exact (w2_R10_b12 POST 1 (or_introl eq_refl) H94c).
  - exact (w2_R10_b12 POST 2 (or_intror eq_refl) H94c).
  - exact (w2_R10_b34 POST 3 (or_introl eq_refl) H7ec).
  - exact (w2_R10_b34 POST 4 (or_intror eq_refl) H7ec).
  - exact (w2_R10_b5 POST 5 eq_refl H914).
  - exact (w2_R10_b6 POST 6 eq_refl H834).
  - (* b >= 7: the cut's body says b <= 6 *)
    intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
    unfold B.ACtlCut.ix_cut in HBODY. cbn [B.ACtlCut.cut_body] in HBODY.
    destruct HBODY as [-> HBODY].
    unfold B.ACtlCutP.C_B817a4_at in HBODY. cbn [B.ACtlCut.cut_body] in HBODY.
    unfold B.ACtlCutP.ixn in HBODY. cbn [nth] in HBODY. rewrite Nat2Z.id in HBODY.
    destruct HBODY as (phi & _ & _ & _ & Hb6 & _). lia.
Qed.

(* B817ec_at b (Inv_B817ec_at SIv:1825) -> B81860_at b.  S_R11 (Slot.v:81; seg_R11 R11.v:423), b = 3, 4.
   R11F.r11_pre_F (R11F.v:47; 0x817ec -> reac_identity_ingest entry INGEST = 0x87e0c, ra = 0x81860, a0 = fr + 2176,
   a1 = ad, a2 = phi + 38, a3 = len; source R11.v (not in this delivery)) then
   B.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on (:1267; a Theorem Labs lane, inside the lifted run; premises = reac_identity_ingest_contract_F_on's,
   reac_identity_ingest_c.v:146) with the identity record at fr + 2176 (IDBr, 38 bytes; wr_at by the fake frame, T8),
   the reply cells (fr + 2448 ad, fr + 2464 phi + 38, fr + 2496 len: the body's reply_ok conjunct, when the reply
   succeeded -- the arm a0 = reply_ret = 1, R11.v (not in this delivery) a0 = 1), the payload bytes at phi + 38 (bytes_at phi rt_F), the
   32-byte window (T1), outside-cells (T9), rng RNG GOT_CELL_K 8 / CELL_K 8 (:165) <- img_vis_W (both cells lie in
   the image).  Then R11F.r11_post_F (R11F.v:87, 0 steps at 0x81860).  Post -> C_B81860_at:
   IDBr at turn S b = snd (ING ..) (SlotModel RID (S b)), FGBr (S b) kept, rgv 20 phi, a0v regs 1 (the ingest
   result), rgv 27 32.  No trap. *)
Lemma seg_R11 : forall POST (b : nat), CFb POST C81860 b -> CFb POST C817ec b.
Proof.
  intros POST b H60 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B817ec_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hb34 & HRF & Ha0 &
                     HRC & H27).
  destruct HRF as ((HRB & Hnz & H20 & HFb) & _).
  destruct HRB as (_ & _ & _ & _ & HIDB & HFGB).
  (* the turn's model (b = 3, 4; RtmB): the reply check passes, the ingest returns 1, the new record is RID (S b) *)
  assert (Hb34Z : Z.of_nat b = 3 \/ Z.of_nat b = 4) by lia.
  pose proof (B.Prog.Seg.RtmB.rb_rtm_ir (B.ACtlCut.c_in cx) (Z.of_nat b) Hb34Z) as Hir.
  assert (Hir' : B.ACtlCutP.RRP.ir (rnb cx b) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) = true)
    by exact Hir.
  pose proof (B.Prog.Seg.RtmB.rb_rtm_ing34 (B.ACtlCut.c_in cx) b Hb34) as Hing.
  destruct (B.Prog.Seg.RtmB.rb_RS_34 (B.ACtlCut.c_in cx) b Hb34 Hnz) as (HRIDS & HRFGS).
  unfold B.Prog.SlotModel.rp_id in HRIDS. rewrite Hir in HRIDS. cbv iota in HRIDS.
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnr & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnr, HlF.
  pose proof (B.ACtlCutP.RRP.ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1423 & _).
  pose proof (w2_r_pl (B.ACtlCut.c_in cx) (Z.of_nat b) ltac:(rewrite HlF; lia) Hs1423) as EPL.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA.
  pose proof HJ as (HAR3 & Hlyle & _).
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _).
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & _ & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx b) = rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx b =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  destruct (Reusable.YG0d.al_shadow segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3) as [(Hp8 & _ & Hpsh) _].
  rewrite Er in Hpsh.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Er, Hfa3, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (proj2 HHB) as (Hphi0 & _).
  pose proof (proj1 HHB) as Hphinz.
  (* the four spills the run reads *)
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & S144 & _ & _ & _ & _ & _ & _ & S240 & S232 & S224 & _ & _ & _ &
                      _ & HAD2176 & _).
  pose proof (w2_spill_at regs3 mem3 A 240 (fr + 2448) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S240) as Q240.
  pose proof (w2_spill_at regs3 mem3 A 232 (fr + 2464) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S232) as Q232.
  pose proof (w2_spill_at regs3 mem3 A 224 (fr + 2496) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S224) as Q224.
  pose proof (w2_spill_at regs3 mem3 A 144 (fr + 2176) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S144) as Q144.
  (* the reply cells *)
  assert (Hargs : B.ACtlCutP.RRP.reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true).
  { unfold B.ACtlCutP.RRP.reply_args.
    rewrite (proj2 (Z.eqb_neq phi 0)) by exact Hphinz.
    rewrite (proj2 (Z.eqb_neq (fr + 2448) 0)) by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2464) 0)) by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2496) 0)) by lia. reflexivity. }
  assert (Hok : B.ACtlCutP.RRP.reply_ok phi (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496)
                  (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) = true)
    by (unfold B.ACtlCutP.RRP.reply_ok; rewrite Hargs, Hir'; reflexivity).
  assert (Hret : B.ACtlCutP.RRP.reply_ret phi (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496)
                   (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) = 1)
    by (unfold B.ACtlCutP.RRP.reply_ret; rewrite Hargs, Hir'; reflexivity).
  rewrite Hret in Ha0.
  destruct (HRC Hok) as (Hpa & Hpp & Hpn).
  pose proof (B.ACtlCutP.RRP.cp_v_range' (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) 36) as R36.
  pose proof (B.ACtlCutP.RRP.cp_v_range' (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) 37) as R37.
  assert (Had : 0 <= B.ACtlCutP.SM.r_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) < 65536)
    by (unfold B.ACtlCutP.SM.r_addr; lia).
  assert (Hle2 : B.ACtlCutP.RRP.reply_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) =
                 lib.Lib.Mem.le2 (Z_to_bv 64 (B.ACtlCutP.SM.r_addr
                                                (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))))).
  { unfold B.ACtlCutP.RRP.reply_addr. symmetry. apply lib.Prog.RcIdentLib.le2_pair.
    rewrite lib.Lib.MState.unsigned_lit by lia. rewrite Z.mod_small by lia.
    unfold B.ACtlCutP.SM.r_addr. unfold B.ACtlCutP.RPA.cp_v in *. lia. }
  (* the payload: bytes 38 .. 38 + len of the frame at phi *)
  assert (Hpb : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 38)
                  (B.ACtlCutP.SM.r_pl (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)))).
  { rewrite EPL. pose proof HFb as HF2.
    rewrite <- (firstn_skipn 38 (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b))) in HF2.
    apply lib.Lib.Mem.bytes_at_app in HF2 as (_ & HF2).
    rewrite length_firstn, Nat.min_l in HF2 by (rewrite HlF; lia). change (Z.of_nat 38) with 38 in HF2.
    rewrite <- (firstn_skipn (Z.to_nat (B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) - 13))
                  (skipn 38 (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b)))) in HF2.
    apply lib.Lib.Mem.bytes_at_app in HF2 as (HF3 & _). exact HF3. }
  assert (Hpbl : length (B.ACtlCutP.SM.r_pl (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))) =
                 Z.to_nat (B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) - 13)).
  { rewrite EPL, length_firstn, length_skipn, HlF. lia. }
  (* what the run touches is visible *)
  assert (VST : forall lo len, sp - 32 <= lo -> 0 <= len -> lo + len <= B.ACtlCut.c_sp cx ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
    intros a Ha. exact (proj1 (Hsvis a ltac:(lia))). }
  assert (VFR : forall lo len, fr <= lo -> 0 <= len -> lo + len <= fr + 4096 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
    intros a Ha. exact (proj1 (Hfvis a ltac:(lia))). }
  assert (VFS : forall lo len, Reusable.YG0f.shadow_addr fr <= lo -> 0 <= len ->
                  lo + len <= Reusable.YG0f.shadow_addr fr + 512 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible.
    split; [unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in H1; lia |].
    split; [unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in H1''; lia |].
    intros a Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
  assert (VBL : forall lo len, phi <= lo -> 0 <= len -> lo + len <= phi + rnb cx b ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
    intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))). }
  assert (VBS : forall lo len, Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi <= lo -> 0 <= len ->
                  lo + len <= Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi + (rnb cx b + 7) / 8 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible.
    split; [unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF in H1; lia |].
    split; [unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF in H1''; lia |].
    intros a Ha.
    pose proof (Hpsh (a - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi) ltac:(lia)) as Hv.
    replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi +
             (a - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi)) with a in Hv by lia.
    apply (w2_vis_of_aview W3 mem3). rewrite Hv. discriminate. }
  destruct (img_vis_W W3) as (_ & _ & VI).
  pose proof HRT as (HAC & _ & _ & _).
  (* the run: R11F.r11_pre_F to the callee entry, then the ingest call *)
  eapply w2_lift.
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + apply (B.Prog.Seg.R11F.r11_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (A := A) (fr := fr) (phi := phi)
        (ad := B.ACtlCutP.SM.r_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)))
        (len := B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) - 13).
      * exact H9.
      * exact Ha0.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Had.
      * exact (w2_ro8 _ _ _ Q240).
      * exact (w2_ro8 _ _ _ Q232).
      * exact (w2_ro8 _ _ _ Q224).
      * exact (w2_ro8 _ _ _ Q144).
      * apply w2_ro2. rewrite <- Hle2. exact (w2_cells_bytes _ _ _ _ Hpa).
      * exact (w2_ro8 _ _ _ (w2_cells_bytes _ _ _ _ Hpp)).
      * exact (w2_ro8 _ _ _ (w2_cells_bytes _ _ _ _ Hpn)).
      * apply VST; lia.
      * apply VST; lia.
      * apply VST; lia.
      * apply VST; lia.
      * apply VFR; lia.
      * apply VFR; lia.
      * apply VFR; lia.
    + intros ms1 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                  -> & -> & -> & -> & -> & ->).
      eapply w2_ingest_F with (spv := sp) (id := fr + 2176)
        (ad := B.ACtlCutP.SM.r_addr (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)))
        (p := phi + 38) (len := B.ACtlCutP.RRP.ir_s (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b)) - 13)
        (lo := sp - 32) (idb := B.ACtlCutP.SM.RID (B.ACtlCut.c_in cx) b)
        (pb := B.ACtlCutP.SM.r_pl (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))).
      * exact H2.
      * exact Hspr.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Had.
      * exact HIDB.
      * apply B.Prog.Seg.RtmB.rb_RID_len.
      * split; [lia |]. split; [lia |]. intros i Hi.
        destruct (proj2 (Hfvis (fr + 2176 + i) ltac:(lia))) as (bb & Hbb).
        exact (w2_wview_some _ _ _ Hbb).
      * exact Hpb.
      * exact Hpbl.
      * lia.
      * split; [lia |]. split; [lia |]. intros a Ha.
        destruct (Hsvis a ltac:(lia)) as (_ & bb & Hbb).
        split; [exact (w2_wview_some _ _ _ Hbb) |].
        exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity.
      * lia.
      * left; lia.
      * left; lia.
      * exact HAC.
      * exact HAD2176.
      * apply (w2_addr_sub mem3 phi (B.ACtlK.a_size (rnb cx b)) 38 _ (proj2 HHB)); unfold B.ACtlK.a_size; lia.
      * intros x [Hx | [Hx | Hx]].
        -- apply w2_out_W; [unfold B.AsanRT.GOT_CELL_K in Hx; lia |].
           destruct (Z_lt_le_dec x (fr + 2176)) as [Hl | Hl]; [left; exact Hl |].
           destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [Hh | Hh]; [exfalso | right; exact Hh].
           apply (Hfimg x ltac:(lia)). apply w2_in_img. unfold B.AsanRT.GOT_CELL_K in Hx. lia.
        -- apply w2_out_W; [unfold B.AsanRT.CELL_K in Hx; lia |].
           destruct (Z_lt_le_dec x (fr + 2176)) as [Hl | Hl]; [left; exact Hl |].
           destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [Hh | Hh]; [exfalso | right; exact Hh].
           apply (Hfimg x ltac:(lia)). apply w2_in_img. unfold B.AsanRT.CELL_K in Hx. lia.
        -- unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
             B.AsanRT.HIGHMEM_BEG in Hx.
           apply w2_out_W; lia.
      * apply VST; lia.
      * apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.GOT_CELL_K; lia |].
        split; [unfold B.AsanRT.GOT_CELL_K; lia |]. intros a Ha. apply VI. unfold B.AsanRT.GOT_CELL_K in Ha. lia.
      * apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.CELL_K; lia |].
        split; [unfold B.AsanRT.CELL_K; lia |]. intros a Ha. apply VI. unfold B.AsanRT.CELL_K in Ha. lia.
      * apply VFR; lia.
      * apply VFS; unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia.
      * apply VBL; lia.
      * apply VBS; unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & -> & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 &
                    K27 & K10 & MU & _ & STc & RWc) Hhid Hsbm.
    apply w2_cfg_back.
    apply (w2_after_ingest POST b cx fr k sp phi ly3 S3 W3 regs3 R mem3 m' md3 md' H60 HB HJ Hfrs Hfa Hk HRT Hperm
             HFRAC Hspz Hcn Hb6 HHB H22 HOUR HCUR HRBE H21).
    + unfold B.ACtlCutP.FGBr in *. rewrite HRFGS. exact HFGB.
    + exact H20.
    + exact H27.
    + exact K2.
    + exact K3.
    + exact K4.
    + exact K8.
    + exact K9.
    + exact K19.
    + exact K20.
    + exact K21.
    + exact K22.
    + exact K23.
    + exact K25.
    + exact K26.
    + exact K27.
    + rewrite K10, Hing. reflexivity.
    + exact MU.
    + exact STc.
    + rewrite HRIDS. exact RWc.
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
Qed.

(* B81834_at b (Inv_B81834_at SIv:1845) -> B81860_at b.  S_R12 (Slot.v:83; seg_R12 R12.v:340), b = 6.
   R12F.r12_pre_F (R12F.v:46; 0x81834 -> INGEST, ra = 0x81860, a0 = idp, a1 = ad, a2 = p, a3 = len; source R12.v:132)
   then
   reac_identity_ingest_SRr_at with idp = fr + 2176 ([A + 144], RBE spill 144), the fragment-built reply cells
   (pa = fr + 2448, pp = fr + 2464 -> fr + 2256 + 19, pn = fr + 2496: the body's (fg_rf .. = 1 -> u16 / q64 / q64)
   conjunct, on the arm a0 = fg_rf = 1), GOT_CELL_K / CELL_K rng <- img_vis_W as for B817ec, then R12F.r12_post_F
   (R12F.v:88, 0 steps).  Post -> C_B81860_at as for B817ec.  No trap. *)
Lemma seg_R12 : forall POST (b : nat), CFb POST C81860 b -> CFb POST C81834 b.
Proof.
  intros POST b H60 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B81834_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hbe & Hnz & H20 & HIDB &
                     HFGB & HADfg & Ha0 & HCL & H27).
  subst b.
  (* turn 6 of the round-trip model: the fragment call closed, the ingest of the joined record returns 1 *)
  unfold B.ACtlCutP.rnb in Ha0, HCL.
  destruct (w2_r12_rtm (B.ACtlCut.c_in cx) Hnz) as (Hrf & Had & Hlen & Hing & HRID7 & Hfgl7).
  rewrite Hrf in Ha0.
  destruct (HCL Hrf) as (Hadb & Hq2464 & Hq2496).
  rewrite Had in Hadb. rewrite Hlen in Hq2496.
  replace (fr + 2256 + 19) with (fr + 2275) in Hq2464 by lia.
  (* the cut's frame and stack *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA.
  (* the four spills the run reads *)
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & S144 & _ & _ & _ & _ & _ & _ & S240 & S232 & S224 & _ & _ & _ &
                      _ & HAD2176 & _).
  pose proof (w2_spill_at regs3 mem3 A 240 (fr + 2448) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S240) as Q240.
  pose proof (w2_spill_at regs3 mem3 A 232 (fr + 2464) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S232) as Q232.
  pose proof (w2_spill_at regs3 mem3 A 224 (fr + 2496) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S224) as Q224.
  pose proof (w2_spill_at regs3 mem3 A 144 (fr + 2176) H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S144) as Q144.
  assert (RO24 : lib.Lib.Step.ro_cells B.Img0.rsegs mem3 (A + 224)
                   [lib.Lib.Cells.C8 (Z_to_bv 64 (fr + 2496)); lib.Lib.Cells.C8 (Z_to_bv 64 (fr + 2464));
                    lib.Lib.Cells.C8 (Z_to_bv 64 (fr + 2448))]).
  { apply w2_ro24; [exact Q224 | replace (A + 224 + 8) with (A + 232) by lia; exact Q232 |
                    replace (A + 224 + 16) with (A + 240) by lia; exact Q240]. }
  (* the payload: the 17 bytes at offset 19 of the fragment record RFG 7 *)
  assert (Hpbb : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (fr + 2275)
                   (B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 7) 19 17)).
  { unfold B.ACtlCutP.FGBr in HFGB. unfold B.ACtlCutP.RFR.bsl.
    change (Z.to_nat 19) with 19%nat. change (Z.to_nat 17) with 17%nat.
    pose proof (w2_bytes_bsl mem3 (fr + 2256) _ 19 17 HFGB ltac:(rewrite Hfgl7; lia)) as H.
    replace (fr + 2256 + Z.of_nat 19) with (fr + 2275) in H by lia. exact H. }
  assert (Hpbl : length (B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 7) 19 17) = Z.to_nat 17).
  { unfold B.ACtlCutP.RFR.bsl. rewrite length_firstn, length_skipn, Hfgl7. reflexivity. }
  (* what the run touches is visible *)
  assert (VST : forall lo len, sp - 32 <= lo -> 0 <= len -> lo + len <= B.ACtlCut.c_sp cx ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
    intros a Ha. exact (proj1 (Hsvis a ltac:(lia))). }
  assert (VFR : forall lo len, fr <= lo -> 0 <= len -> lo + len <= fr + 4096 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
    intros a Ha. exact (proj1 (Hfvis a ltac:(lia))). }
  assert (VFS : forall lo len, Reusable.YG0f.shadow_addr fr <= lo -> 0 <= len ->
                  lo + len <= Reusable.YG0f.shadow_addr fr + 512 ->
                  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H1' H1''. apply B.ProgBridge.rng_of_visible.
    split; [unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in H1; lia |].
    split; [unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in H1''; lia |].
    intros a Ha. exact (proj1 (Hfsvis a ltac:(lia))). }
  destruct (img_vis_W W3) as (_ & _ & VI).
  pose proof HRT as (HAC & _ & _ & _).
  (* the run: R12F.r12_pre_F to the callee entry, then the ingest call *)
  eapply w2_lift.
  - unfold Lib.Regs6ss.mkR_of.
    eapply lib.Lib.ExecF.evtF_cut.
    + apply (B.Prog.Seg.R12F.r12_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with
        (Ab := A) (idp := fr + 2176) (pa := fr + 2448) (pp := fr + 2464) (pn := fr + 2496) (ad := 0x1000)
        (p := fr + 2275) (len := 17).
      * exact H9.
      * exact Ha0.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact RO24.
      * exact (w2_ro8 _ _ _ Q144).
      * exact (w2_ro2 _ _ _ Hadb).
      * exact (w2_ro8 _ _ _ Hq2464).
      * exact (w2_ro8 _ _ _ Hq2496).
      * apply VST; lia.
      * apply VST; lia.
      * apply VFR; lia.
      * apply VFR; lia.
      * apply VFR; lia.
    + intros ms1 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                  -> & -> & -> & -> & -> & ->).
      eapply w2_ingest_F with (spv := sp) (id := fr + 2176) (ad := 0x1000) (p := fr + 2275) (len := 17)
        (lo := sp - 32) (idb := B.ACtlCutP.SM.RID (B.ACtlCut.c_in cx) 6)
        (pb := B.ACtlCutP.RFR.bsl (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 7) 19 17).
      * exact H2.
      * exact Hspr.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact HIDB.
      * apply B.Prog.Seg.RtmB.rb_RID_len.
      * split; [lia |]. split; [lia |]. intros i Hi.
        destruct (proj2 (Hfvis (fr + 2176 + i) ltac:(lia))) as (bb & Hbb).
        exact (w2_wview_some _ _ _ Hbb).
      * exact Hpbb.
      * exact Hpbl.
      * lia.
      * split; [lia |]. split; [lia |]. intros a Ha.
        destruct (Hsvis a ltac:(lia)) as (_ & bb & Hbb).
        split; [exact (w2_wview_some _ _ _ Hbb) |].
        exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity.
      * lia.
      * left; lia.
      * left; lia.
      * exact HAC.
      * exact HAD2176.
      * replace (fr + 2275) with (fr + 2256 + 19) by lia.
        apply (w2_addr_sub mem3 (fr + 2256) 72 19 17 HADfg); lia.
      * intros x [Hx | [Hx | Hx]].
        -- apply w2_out_W; [unfold B.AsanRT.GOT_CELL_K in Hx; lia |].
           destruct (Z_lt_le_dec x (fr + 2176)) as [Hl | Hl]; [left; exact Hl |].
           destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [Hh | Hh]; [exfalso | right; exact Hh].
           apply (Hfimg x ltac:(lia)). apply w2_in_img. unfold B.AsanRT.GOT_CELL_K in Hx. lia.
        -- apply w2_out_W; [unfold B.AsanRT.CELL_K in Hx; lia |].
           destruct (Z_lt_le_dec x (fr + 2176)) as [Hl | Hl]; [left; exact Hl |].
           destruct (Z_lt_le_dec x (fr + 2176 + 38)) as [Hh | Hh]; [exfalso | right; exact Hh].
           apply (Hfimg x ltac:(lia)). apply w2_in_img. unfold B.AsanRT.CELL_K in Hx. lia.
        -- unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
             B.AsanRT.HIGHMEM_BEG in Hx.
           apply w2_out_W; lia.
      * apply VST; lia.
      * apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.GOT_CELL_K; lia |].
        split; [unfold B.AsanRT.GOT_CELL_K; lia |]. intros a Ha. apply VI. unfold B.AsanRT.GOT_CELL_K in Ha. lia.
      * apply B.ProgBridge.rng_of_visible. split; [unfold B.AsanRT.CELL_K; lia |].
        split; [unfold B.AsanRT.CELL_K; lia |]. intros a Ha. apply VI. unfold B.AsanRT.CELL_K in Ha. lia.
      * apply VFR; lia.
      * apply VFS; unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia.
      * apply VFR; lia.
      * apply VFS; unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & m' & -> & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 &
                    K27 & K10 & MU & _ & STc & RWc) Hhid Hsbm.
    apply w2_cfg_back.
    apply (w2_after_ingest POST 6 cx fr k sp phi ly3 S3 W3 regs3 R mem3 m' md3 md' H60 HB HJ Hfrs Hfa Hk HRT Hperm
             HFRAC Hspz Hcn Hb6 HHB H22 HOUR HCUR HRBE H21 HFGB H20 H27 K2 K3 K4 K8 K9 K19 K20 K21 K22 K23 K25 K26
             K27).
    + rewrite K10, Hing. reflexivity.
    + exact MU.
    + exact STc.
    + rewrite HRID7. exact RWc.
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
Qed.

(* B81860_at b (Inv_B81860_at SIv:1865) -> B81aa0_at b.  S_R13 (Slot.v:85; seg_R13 R13.v:460).
   R13F.r13_evt_F (R13F.v:42; 0x81860 -> 0x534b4; source R13.v:84: one premise a0 = 1, from a0v regs 1; no memory
   access, so no rng premise is expected; post: ra = 0x81aa0, a0 = s4 = phi, memory unchanged, the callee-saved
   registers kept), then
   w2_free_81a9c with phi (rgv regs 20 phi), the live list (body: Permutation bl (ENTRYBL ++ [(phi, rnb)])),
   w2_phi_not_entry, o / gp / tp from FRAC, CHAIN_OF_CUT at (pc_free_ra0, 0x81aa0).  Post -> C_B81aa0_at body:
   Permutation (site lemma), FRAC / RBE / OURb / IDBr (S b) / FGBr (S b) kept by ctl_post_acall_kept (E = the freed block (phi, rnb cx b); frame and spill bytes are
   neither the freed block nor in the call window [sp - ASTACK, sp)), RB at turn S b (CUR 7, rgv 22 b, OURb, IDBr,
   FGBr, b <= 6), rgv 21 36, rgv 27 32 by aregs_preserved, ctl_rt by ctlrt_of_AR, k + 1 <= 2b + 2.  The abort edge
   0x81868 is not taken (a0 = 1); no UBSan trap. *)
Lemma seg_R13 : forall POST (b : nat), CFb POST C81aa0 b -> CFb POST C81860 b.
Proof.
  intros POST b Haa cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B81860_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hcn & Hb & HHB & H22 & HOUR & HCUR & HRBE & H21 & HID & HFG & H20 & Ha0 &
                     H27).
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _ & _ & _ & _ & _ & _ & HSAVE & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _) & _). pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (Hc16 & _ & Hceil & Hstklo & Hstkhi & H47 & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [HcR _]. unfold Reusable.YG0f.ASAN_CEIL in HcR.
  unfold Reusable.YCfn.LLVMF_STK in Hwin, Hstklo.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  (* The turn block is live before the free, apart from the frame and from every shadow byte. *)
  assert (Hin3 : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR3 Hin3)
    as (_ & Hp4 & Hpc & Hpapp & _ & _ & Hpn).
  pose proof (Reusable.YCbq.req_size_pos _ (proj1 Hpn)) as [Hrq1 _].
  pose proof (Reusable.YG0d.al_layout segs B LAWS _ _ _ _ _ ly3 HAR0 Hlyle) as (_ & Hfa3 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfsb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) 6 (B.ACtlCut.c_fpos cx)
                HAR3 Hin3 Hin6) as Hdj.
  rewrite Hfa3, <- Hfr6, Hfsb in Hdj. unfold Reusable.YG0f.zdisjoint in Hdj. cbn [fst snd] in Hdj.
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happ3 & _ & _).
  rewrite Hfa3, <- Hfr6, Hfsb in Happ3.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hpapp, Happ3.
  eapply w2_lift.
  - unfold Lib.Regs6ss.mkR_of. apply (B.Prog.Seg.R13F.r13_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    unfold B.ACtlCut.a0v in Ha0. exact Ha0.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & -> & HRa & HR10 & HR2 & HR3 & HR4 & HR8 & HR9 & HR27 & HR19 & HR21 & HR22 & HR23 & HR25 &
                    HR26) _ Hsbm.
    apply w2_cfg_back. change 0x534b4 with Reusable.YB1w.tfib_A_free.
    pose proof (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
    assert (E2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact HR2.
    assert (E3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact HR3.
    assert (E4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact HR4.
    assert (E8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact HR8.
    assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact HR9.
    assert (E10 : lib.Reusable.YK11.getr R 10 = lib.Reusable.YK11.getr regs3 20) by exact HR10.
    assert (E19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact HR19.
    assert (E21 : lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) by exact HR21.
    assert (E22 : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by exact HR22.
    assert (E23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by exact HR23.
    assert (E25 : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by exact HR25.
    assert (E26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact HR26.
    assert (E27 : lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27) by exact HR27.
    assert (HspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite E2; exact Hspz).
    destruct (CHAIN_OF_CUT cx (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k R
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) 0x81aa0 HB HJ'
                ltac:(rewrite E8; exact H8) HRa HSAVE ltac:(rewrite HspR; lia) ltac:(rewrite HspR; lia)
                ltac:(right; left; reflexivity)) as (ch & Hch & Htr).
    apply (w2_free_81a9c cx b phi ly3 S3 W3 R mem3 md' k (sp - B.ACtlCut.c_sp cx) ch (POST cx)
             HB HJ' Hk Hb Hperm (w2_phi_not_entry _ _ _ _ _ _ _ _ _ _ HJ Hperm)).
    + rewrite E10. exact H20.
    + rewrite HspR. lia.
    + lia.
    + lia.
    + rewrite E3, H3. exact Hgp0.
    + rewrite E4. exact H4.
    + exact HRa.
    + exact Hch.
    + exact Htr.
    + intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 HPR Hfrs2 Hperm2 HK.
      pose proof HJ2 as (HAR2 & _).
      assert (HEf : forall a, fr <= a < fr + Reusable.YG00.fs_frame_bytes 6 ->
                      ~ (phi <= a < phi + Reusable.YG00.req_size (rnb cx b)))
        by (intros a Ha; rewrite Hfsb in Ha; lia).
      assert (HEs : forall a, B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + B.ACtlCutP.FRAME_SHADOW ->
                      ~ (phi <= a < phi + Reusable.YG00.req_size (rnb cx b))).
      { intros a Ha.
        unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.FRAME_SHADOW,
          B.ACtlCutP.FRAME_BYTES in Ha.
        lia. }
      destruct (w2_acall_keeps cx fr k sp ly3 S3 W3 mem3 md' ly2 S2 W2 mem2 md2 _ _
                  (B.ACtlCut.c_sp cx + (sp - B.ACtlCut.c_sp cx) - Reusable.YG0d.ASTACK)
                  (B.ACtlCut.c_sp cx + (sp - B.ACtlCut.c_sp cx))
                  (fun a => phi <= a < phi + Reusable.YG00.req_size (rnb cx b))
                  HB HJ' Hfrs Hfr6 (proj1 Hspr) Hsp4 ltac:(lia) HK Hwle HJ2 HEs HRT)
        as (KH & KFW0 & KS & KTBL & KROW & KBOX & KNM & HRT2).
      assert (KFW : KEEPR mem3 mem2 fr (fr + Reusable.YG00.fs_frame_bytes 6))
        by (intros a Ha; exact (KFW0 a Ha (HEf a Ha))).
      assert (KA : KEEPR mem3 mem2 A (A + 448)) by (intros a Ha; apply KH; lia).
      assert (KF : KEEPR mem3 mem2 fr (fr + B.ACtlCutP.FRAME_BYTES))
        by (intros a Ha; apply KFW; rewrite Hfsb; unfold B.ACtlCutP.FRAME_BYTES in Ha; lia).
      assert (KT : KEEPR mem3 mem2 (fr + 4088) (fr + 4088 + 8))
        by (intros a Ha; apply KFW; rewrite Hfsb; lia).
      assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                    lib.Reusable.YK11.getr R r = lib.Reusable.YK11.getr regs3 r ->
                    lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr regs3 r)
        by (intros z r Hz' Er' E; exact (w2_pres_reg R regs2 regs3 z r HPR Hz' Er' E)).
      assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
        by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
      assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
        by (apply (G 2); [apply CS; lia | apply bv_eq; reflexivity | exact E2]).
      assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
        by (apply (G 3); [apply CS; lia | apply bv_eq; reflexivity | exact E3]).
      assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
        by (apply (G 4); [apply CS; lia | apply bv_eq; reflexivity | exact E4]).
      assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
        by (apply (G 8); [apply CS; lia | apply bv_eq; reflexivity | exact E8]).
      assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
        by (apply (G 9); [apply CS; lia | apply bv_eq; reflexivity | exact E9]).
      assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
        by (apply (G 19); [apply CS; lia | apply bv_eq; reflexivity | exact E19]).
      assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
        by (apply (G 21); [apply CS; lia | apply bv_eq; reflexivity | exact E21]).
      assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
        by (apply (G 22); [apply CS; lia | apply bv_eq; reflexivity | exact E22]).
      assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
        by (apply (G 23); [apply CS; lia | apply bv_eq; reflexivity | exact E23]).
      assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
        by (apply (G 25); [apply CS; lia | apply bv_eq; reflexivity | exact E25]).
      assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
        by (apply (G 26); [apply CS; lia | apply bv_eq; reflexivity | exact E26]).
      assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
        by (apply (G 27); [apply CS; lia | apply bv_eq; reflexivity | exact E27]).
      apply (Haa cx [Z.of_nat b] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2 Hfa).
      * unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81aa0_at, B.ACtlCutP.ixn.
        cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. lia.
      * unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B81aa0_at, B.ACtlCutP.ixn.
        cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
        unfold B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
        assert (KOUR : lib.Lib.Mem.bytes_at segs mem2 (fr + 2624) (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx))).
        { eapply w2_bytes_keep; [| exact HOUR]. intros a Ha.
          unfold B.ACtlCutP.SM.OUR in Ha. rewrite length_map, length_seq in Ha.
          apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia. }
        refine (conj Hperm2 (conj _ (conj Hcn (conj Hb (conj _ (conj KOUR (conj _ (conj _
                  (conj (conj Hb (conj _ (conj KOUR (conj _ (conj _ _))))) _))))))))).
        -- apply (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26).
           apply (w2_frac_mem cx fr fr regs3 mem3 mem2);
             [intros a Ha _; apply KH; rewrite Hspz in Ha; exact Ha |
              intros a Ha; apply KF; unfold B.ACtlCutP.FRAME_BYTES; lia | exact KS | exact KT | exact HFRAC].
        -- exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
        -- apply (w2_rbe_regs cx fr regs3 regs2 mem2 F9).
           exact (w2_rbe_mem cx fr regs3 mem3 mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia) KA (fun a Ha _ => KS a Ha)
                    KTBL KBOX KROW KNM
                    HRBE).
        -- exact (w2_rgv_move regs2 regs3 21 _ F21 H21).
        -- exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
        -- exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
        -- eapply w2_bytes_keep; [| exact HID]. intros a Ha.
           rewrite B.Prog.Seg.RtmB.rb_RID_len in Ha. apply KF. unfold B.ACtlCutP.FRAME_BYTES. lia.
        -- eapply w2_bytes_keep; [| exact HFG]. intros a Ha.
           rewrite (B.Prog.Seg.RtmB.rb_RFG_len _ (S b) ltac:(lia)) in Ha. apply KF.
           unfold B.ACtlCutP.FRAME_BYTES. lia.
        -- exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
      * exact HRT2.
Qed.

(* B818a8_at b (Inv_B818a8_at SIv:1886) -> B819a8_at b.  S_R14 (Slot.v:87; seg_R14 R14.v:1256), b = 0.
   R14F.r14_pre_F (R14F.v:134-157; ONE stretch from 0x818a8 at turn i, the 32-turn block sum included, to
   catalogue_match entry CMC.REAC_BOX_CATALOGUE_MATCH, ra = 0x819a8, a0 = p, a1 = len; sources R14.v:621 / :703).
   Its start state pins sp = Sp, a0 = a2 = p + 18 + i, a1 = psum bs i, a3 = 2^64 - 18 - p, a4 = 32 - i, s2 = len,
   s4 = p, s10 = ASAN_K, s11 = 32 <- body: FRAC (sp, rgv 26 ASAN_K), rgv 10 / 12 (phi + 18 + i), rgv 11 (rsum cx b i
   = psum bs i), rgv 13 (-(phi + 18)) with ctrl's r14_room (R14.v:592) for the 2^64 - 18 - p form, rgv 14 (32 - i),
   RF (rgv 18 rnb, rgv 20 phi), rgv 27 32; its premises <- body / world: 4096 <= p and p + 50 <= APPMEM_END
   (al_blocks on (phi, rnb), rnb >= 52), 0 <= len < 2^64, i < 32, length bs = 32 and bytes_at (p + 18) bs
   (RF bytes_at phi rt_F, skipn 18), psum bs 32 mod 256 = 0 (the turn-0 block checksum, SlotModel), addressable p 50
   (HB, rnb >= 52), rng RNG (p + 18) 32 (V3) and rng RNG over the shadow of [p + 18, p + 50) (V4).  Then
   reac_box_catalogue_match (cut-callee: stack_malloc_2 at 0x84eb0, the _1 inside reac_ctrl_parse, the _0 inside
   reac_box_model_block) by its caller-journal spec (a Theorem Labs lane's C_reac_box_catalogue_match; image B: TMATCH, :309)
   with p = phi, len = rnb (>= 50), fb = the 50-byte head of the block, psum bs 32 mod 256 = 0 (the turn-0 config
   checksum, SlotModel); return pc 0x819a8 = the successor cut.
   TRAP row 4 (0x818b0, F.4.1:1384): discharged INSIDE R14F.r14_pre_F by its premises 4096 <= p / p + 50 <=
   APPMEM_END (see the header): the
   stage proves 4096 <= phi and phi + 50 <= APPMEM_END from (phi, rnb) in ablocks B ly3 S3 (body Permutation) with
   al_blocks (YG0d.v:422-426: 4096 <= p, p + req_size n <= alloc_ceiling) and rnb >= 52 (RF -> RFb: rnb <> 0;
   SlotModel.v:80); a3 / a4 / s11 / i < 32 come from the body as listed.  The report stub 0x818e8 is refuted by
   addressable p 50 and the abort jump 0x81998 by the checksum premise, both inside r14_pre_F.  R14F.r14_post_F
   (R14F.v:187-205, 0 steps at 0x819a8) is NOT applied: catalogue_match is a cut-callee whose spec's post is
   world-form.  Post -> C_B819a8_at body: a0v regs mrow (the match result want CM_T len fb = SM.mrow, from the spec's
   post), spill 120 (fr + 2528), RFb, the spills 24 / 16 / 96, addressable (fr + 2528) 12; s11 = 32 (callee-saved). *)
Lemma seg_R14 : forall POST (b : nat), CFb POST C819a8 b -> CFb POST C818a8 b.
Proof.
  intros POST b H9a8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk HBODY HRT.
  unfold B.ACtlCut.ix_cut in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  destruct HBODY as [-> HBODY].
  unfold B.ACtlCutP.C_B818a8_at in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  cbn [B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.cut_kmax B.ACtlCut.cut_own] in Hk, HBODY, HJ, Hfrs, Hfa |- *.
  unfold B.ACtlCutP.ixn in Hk, HBODY. cbn [nth] in Hk, HBODY. rewrite Nat2Z.id in Hk, HBODY.
  destruct HBODY as (phi & i & Hperm & HFRAC & Hcn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hile & H10 & H12 &
                     H14 & Hb0 & Hi32 & H11 & HRF & S24 & S16 & S96 & S120 & HAD2528 & H13 & H27).
  subst b.
  unfold B.ACtlCutP.RF, B.ACtlCutP.RFx, B.ACtlCutP.RFb, B.ACtlCutP.RB in HRF.
  destruct HRF as ((( _ & _ & _ & _ & HIDB & HFGB) & Hnz & H20 & HFb) & H18).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 0) Hnz) as (_ & Hnr & HlF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 0)) with (rnb cx 0) in Hnr, HlF.
  (* the cut's frame, stack and block *)
  pose proof HFRAC as (A & sp & H2 & Hsp16 & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
                       HfrA & HA448 & Hsp4 & HcAPP & _).
  pose proof (w2_spZ_range regs3) as Hspr. rewrite Hspz in Hspr.
  assert (Hfr6 : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx))
    by (apply Hfa; left; reflexivity).
  destruct (w2_frame_loc cx fr k sp ly3 S3 W3 mem3 md3 HB HJ Hfrs Hfr6 ltac:(lia))
    as (Hf4096 & Hfsp & Hceilsp & Hceil0 & Hcsp47 & Happ & Hfimg & Hfvis & Hfsvis & Hsvis).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HcAPP.
  pose proof HB as ((HAFN & _ & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & Hlive0 & _) & _).
  pose proof HAFN as (HAR0 & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR3 & Hlyle & _ & _ & _ & Hfrs3 & Hnev3 & Hk0 & _).
  assert (Hin3 : In (phi, rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR3 Hin3)
    as (Hp16 & Hp4 & Hpc & Hpapp & Hpbytes & _ & _).
  assert (Er : Reusable.YG00.req_size (rnb cx 0) = rnb cx 0)
    by (unfold Reusable.YG00.req_size; destruct (rnb cx 0 =? 0) eqn:E; lia).
  rewrite Er in Hpc, Hpapp, Hpbytes.
  destruct (Reusable.YG0d.al_shadow segs B LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR3 Hin3) as [(Hp8 & _ & Hpsh) _].
  rewrite Er in Hpsh.
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as Hcv.
  (* the turn-0 model: the control block at phi + 18 sums to 0 mod 256; a1 is its running sum *)
  pose proof (B.Prog.Seg.R14.r14_blk_bytes (B.ACtlCut.c_in cx) (Z.of_nat 0) mem3 phi HFb) as Hblk.
  assert (Hblkl : length (B.Prog.SlotModel.rt_X (B.ACtlCut.c_in cx) (Z.of_nat 0)) = 32%nat)
    by (unfold B.Prog.SlotModel.rt_X; apply B.Prog.Seg.R14.r14_baX_len; apply B.Prog.Seg.R14.r14_mb_len).
  pose proof (B.Prog.Seg.R14.r14_blocksum0 (B.ACtlCut.c_in cx)) as Hsum.
  assert (Hrs : B.ACtlCutP.rsum cx 0 i =
                B.ACtlCutP.RMO.psum (B.Prog.SlotModel.rt_X (B.ACtlCut.c_in cx) (Z.of_nat 0)) i)
    by (unfold B.ACtlCutP.rsum; rewrite B.Prog.Seg.R14.r14_skip18; reflexivity).
  (* the run: R14F.r14_pre_F, 0x818a8 (block-sum turn i) -> reac_box_catalogue_match entry, memory kept *)
  eapply w2_lift with (P := fun ms' => exists R : bvmap 5 word,
      ms' = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs
              (Z_to_bv 64 B.Prog.C_reac_box_catalogue_match.A_reac_box_catalogue_matchP)
              lib.Reusable.YK11.fp_csr None mem3 (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
      lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x819a8 /\
      lib.Reusable.YK11.getr R 2 = Z_to_bv 64 sp /\
      lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
      lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
      lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
      lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
      lib.Reusable.YK11.getr R 10 = Z_to_bv 64 phi /\
      lib.Reusable.YK11.getr R 11 = Z_to_bv 64 (rnb cx 0) /\
      lib.Reusable.YK11.getr R 18 = Z_to_bv 64 (rnb cx 0) /\
      lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
      lib.Reusable.YK11.getr R 20 = Z_to_bv 64 phi /\
      lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21 /\
      lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22 /\
      lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
      lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
      lib.Reusable.YK11.getr R 26 = Z_to_bv 64 B.AsanRT.ASAN_K /\
      lib.Reusable.YK11.getr R 27 = Z_to_bv 64 32).
  - unfold Lib.Regs6ss.mkR_of.
    match goal with |- context [lib.Lib.Frame.mkR _ ?x2 _ _ _ _ _ _ _ ?x10 ?x11 ?x12 ?x13 ?x14 _ _ _ ?x18 _ ?x20
                                  _ _ _ _ _ ?x26 ?x27 _ _ _ _] =>
      replace x2 with (Z_to_bv 64 sp) by (symmetry; exact H2);
      replace x10 with (Z_to_bv 64 (phi + 18 + Z.of_nat i)) by (symmetry; exact H10);
      replace x11 with (Z_to_bv 64 (B.ACtlCutP.RMO.psum (B.Prog.SlotModel.rt_X (B.ACtlCut.c_in cx) (Z.of_nat 0)) i))
        by (symmetry; rewrite <- Hrs; exact H11);
      replace x12 with (Z_to_bv 64 (phi + 18 + Z.of_nat i)) by (symmetry; exact H12);
      replace x13 with (Z_to_bv 64 (18446744073709551598 - phi))
        by (symmetry; rewrite <- (B.Prog.Seg.R14.r14_room phi) by lia; exact H13);
      replace x14 with (Z_to_bv 64 (32 - Z.of_nat i)) by (symmetry; exact H14);
      replace x18 with (Z_to_bv 64 (rnb cx 0)) by (symmetry; exact H18);
      replace x20 with (Z_to_bv 64 phi) by (symmetry; exact H20);
      replace x26 with (Z_to_bv 64 B.AsanRT.ASAN_K) by (symmetry; exact H26);
      replace x27 with (Z_to_bv 64 32) by (symmetry; exact H27)
    end.
    eapply lib.Lib.ExecF.evtF_cut.
    + apply (B.Prog.Seg.R14F.r14_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      * lia.
      * unfold B.AsanRT.APPMEM_END. lia.
      * lia.
      * exact Hi32.
      * exact Hblkl.
      * exact Hblk.
      * exact Hsum.
      * replace (phi + 50 - 50) with phi by lia.
        apply (w2_addr_prefix mem3 phi (B.ACtlK.a_size (rnb cx 0)) 50 (proj2 HHB)).
        unfold B.ACtlK.a_size. lia.
      * apply B.ProgBridge.rng_of_visible. split; [lia |]. split; [lia |].
        intros a Ha. exact (proj1 (proj1 (Hpbytes a ltac:(lia)))).
      * apply B.ProgBridge.rng_of_visible.
        split; [unfold B.AsanRT.ASAN_K; lia |]. split; [unfold B.AsanRT.ASAN_K; lia |].
        intros a Ha.
        assert (Hj : 0 <= a - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi < (rnb cx 0 + 7) / 8)
          by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K in *; lia).
        pose proof (Hpsh _ Hj) as Hv.
        replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi +
                 (a - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF phi)) with a in Hv by lia.
        apply (w2_vis_of_aview W3 mem3). rewrite Hv. discriminate.
    + intros ms1 (a0' & a1' & a2' & a4' & a5' & a6' & -> & -> & ->).
      apply lib.Lib.ExecF.evtF_done. eexists. split; [reflexivity |].
      repeat (split; [reflexivity |]). reflexivity.
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' (R & -> & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G18 & G19 & G20 & G21 & G22 & G23 & G25 &
                    G26 & G27) _ Hsbm.
    apply w2_cfg_back.
    pose proof (w2_journal_mat _ _ _ _ _ _ _ _ _ HJ Hsbm) as HJ'.
    pose proof HJ' as (HAR' & _).
    assert (HspR : Reusable.YG0d.spZ R = sp).
    { unfold Reusable.YG0d.spZ. rewrite G2, Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hspr. }
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
    destruct Hstk as (Hc16 & _).
    (* the callee's own journal starts here: astk_ok, the window and qtight at the call *)
    pose proof (Reusable.YCbq.ajournal_sub_init segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  B.Prog.C_reac_box_catalogue_match.CM_STK sp [] (sp - B.ACtlCut.c_sp cx) HJ' ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(unfold B.Prog.C_reac_box_catalogue_match.CM_STK; lia)
                  ltac:(unfold B.Prog.C_reac_box_catalogue_match.CM_STK, Reusable.YCfn.LLVMF_STK; lia)) as HJ0.
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin0 & Hastk0 & _ & HQT0).
    change 0x84e40 with B.Prog.C_reac_box_catalogue_match.A_reac_box_catalogue_matchP.
    eapply Reusable.YA0n.SRr_bind.
    { apply (TMATCH ly3 S3 W3 R mem3 md' phi (rnb cx 0) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 0))).
      - exact HAR'.
      - rewrite G1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
      - unfold Reusable.YG0d.raZ. rewrite G1, Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
      - rewrite G3, H3. exact Hgp0.
      - rewrite G4. exact H4.
      - rewrite HspR. exact Hastk0.
      - rewrite HspR. exact Hwin0.
      - exact HQT0.
      - exact (w2_arodataS cx _ _ _ _ _ _ _ HB HJ').
      - exact G10.
      - exact G11.
      - lia.
      - lia.
      - unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50. rewrite length_firstn, length_app, repeat_length. lia.
      - intros _. exists (rnb cx 0). split; [exact Hin3 | rewrite Er; lia].
      - intros _ j Hj. rewrite length_map in Hj.
        unfold B.ACtlCutP.SM.rt_g, B.ACtlCutP.SM.fr50 in Hj. rewrite length_firstn, length_app, repeat_length in Hj.
        pose proof HFb as (_ & _ & HF3).
        pose proof (HF3 j ltac:(rewrite HlF; lia)) as Ej.
        destruct (nth_error (B.ACtlCutP.SM.rt_F (B.ACtlCut.c_in cx) (Z.of_nat 0)) j) as [x |] eqn:Ex;
          [| apply nth_error_None in Ex; rewrite HlF in Ex; lia].
        assert (Ej' : lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (phi + Z.of_nat j)) = Some x) by exact Ej.
        assert (Enth : nth j (map (fun b : byte => bv_unsigned b) (B.ACtlCutP.SM.rt_g (B.ACtlCut.c_in cx) (Z.of_nat 0))) 0
                       = bv_unsigned x).
        { apply nth_error_nth. rewrite nth_error_map. unfold B.ACtlCutP.SM.rt_g.
          rewrite (w2_fr50_nth _ j x ltac:(lia) Ex). reflexivity. }
        rewrite Enth. split.
        + intros kk Hkk. destruct kk as [| kk]; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, w2_le_byte1.
          exact (w2_mbyte_of_mrd W3 mem3 _ x (proj1 (proj1 (Hpbytes (phi + Z.of_nat j) ltac:(lia)))) Ej').
        + pose proof (bv_unsigned_in_range 8 x) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
      - intros a Ha. apply ctl_relro_not_owned. right.
        unfold B.Prog.C_reac_box_catalogue_match.A_CM_TBL, B.Prog.C_reac_box_catalogue_match.CM_ROWS in Ha.
        unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N. lia.
      - rewrite Hfrs. vm_compute. reflexivity.
      - rewrite Hfrs. vm_compute. reflexivity.
      - rewrite Hfrs. vm_compute. reflexivity.
      - unfold B.Prog.C_reac_box_catalogue_match.EV_CM, Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *. lia.
      - assert (Hbb : Reusable.YCbq.bsum (Reusable.YG0d.ablocks B ly3 S3) =
                      Reusable.YCbq.bsum (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) +
                      rnb cx 0)
          by (rewrite (Reusable.YCbq.bsum_perm _ _ Hperm), Reusable.YCbq.bsum_app; cbn; lia).
        rewrite <- (Reusable.YCbq.blocks_bytes_bsum B ly3 S3),
          <- (Reusable.YCbq.blocks_bytes_bsum B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) in Hbb.
        unfold B.Prog.C_reac_box_catalogue_match.LIVE_CM, Reusable.YCfn.LIVE_LIB in *. lia. }
    cbv beta. intros W2 cf Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HPR & Ha02 & Hbl2).
    (* the caller's journal across the call (YCbq.ajournal_sub: no own frame, an empty footprint) *)
    assert (HJ2 : AJ cx (own6 cx) ly2 S2 W2 mem2 md2 k).
    { pose proof (Reusable.YCbq.ajournal_sub segs B LAWS w2_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    B.Prog.C_reac_box_catalogue_match.CM_STK (Reusable.YG0d.spZ R) [] [] ly2 S2 W2 mem2 md2
                    B.Prog.C_reac_box_catalogue_match.EV_CM HJ' HJc) as Hsub.
      unfold B.Prog.C_reac_box_catalogue_match.EV_CM in Hsub. rewrite Z.add_0_r in Hsub. apply Hsub.
      - rewrite HspR. unfold B.Prog.C_reac_box_catalogue_match.CM_STK, Reusable.YCfn.LLVMF_STK. lia.
      - rewrite HspR. lia.
      - intros a Ha. exfalso. exact (lib.Reusable.YI04.inFP_nil a Ha). }
    pose proof HJ2 as (HAR2 & _).
    assert (HRT2 : B.ACtlRtC.ctl_rt_C B ly2 S2 mem2) by exact (w2_ctl_rt _ _ _ _ _ _ _ _ HB HJ2).
    assert (Hin2 : In (phi, rnb cx 0) (Reusable.YG0d.ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hbl2)); exact Hin3).
    rewrite HspR in HJc.
    destruct (w2_cj_keeps cx fr k sp _ _ ly3 S3 W3 mem3 md' ly2 S2 W2 mem2 md2 phi (rnb cx 0)
                HB HJ' Hfrs Hfr6 ltac:(lia) HJc HRT HRT2 Hin3 Hin2)
      as (KH & KFW & KS & KTBL & KROW & KBOX & KNM & KB).
    rewrite Er in KB.
    (* registers: regs2 keeps R's callee-saved registers *)
    assert (G : forall (z : Z) (r : bv 5), Reusable.YG0d.acallee_saved z -> Z_to_bv 5 z = r ->
                  lib.Reusable.YK11.getr regs2 r = lib.Reusable.YK11.getr R r)
      by (intros z r Hz' Er'; rewrite <- Er'; exact (HPR z Hz')).
    assert (CS : forall z, 2 <= z <= 4 \/ 8 <= z <= 9 \/ 18 <= z <= 27 -> Reusable.YG0d.acallee_saved z)
      by (intros z Hz'; unfold Reusable.YG0d.acallee_saved; lia).
    assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
      by (transitivity (lib.Reusable.YK11.getr R 2);
          [apply (G 2); [apply CS; lia | apply bv_eq; reflexivity] | rewrite G2, H2; reflexivity]).
    assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
      by (transitivity (lib.Reusable.YK11.getr R 3);
          [apply (G 3); [apply CS; lia | apply bv_eq; reflexivity] | exact G3]).
    assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
      by (transitivity (lib.Reusable.YK11.getr R 4);
          [apply (G 4); [apply CS; lia | apply bv_eq; reflexivity] | exact G4]).
    assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
      by (transitivity (lib.Reusable.YK11.getr R 8);
          [apply (G 8); [apply CS; lia | apply bv_eq; reflexivity] | exact G8]).
    assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
      by (transitivity (lib.Reusable.YK11.getr R 9);
          [apply (G 9); [apply CS; lia | apply bv_eq; reflexivity] | exact G9]).
    assert (F18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs3 18)
      by (transitivity (lib.Reusable.YK11.getr R 18);
          [apply (G 18); [apply CS; lia | apply bv_eq; reflexivity] | rewrite G18, H18; reflexivity]).
    assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
      by (transitivity (lib.Reusable.YK11.getr R 19);
          [apply (G 19); [apply CS; lia | apply bv_eq; reflexivity] | exact G19]).
    assert (F20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
      by (transitivity (lib.Reusable.YK11.getr R 20);
          [apply (G 20); [apply CS; lia | apply bv_eq; reflexivity] | rewrite G20, H20; reflexivity]).
    assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
      by (transitivity (lib.Reusable.YK11.getr R 21);
          [apply (G 21); [apply CS; lia | apply bv_eq; reflexivity] | exact G21]).
    assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
      by (transitivity (lib.Reusable.YK11.getr R 22);
          [apply (G 22); [apply CS; lia | apply bv_eq; reflexivity] | exact G22]).
    assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
      by (transitivity (lib.Reusable.YK11.getr R 23);
          [apply (G 23); [apply CS; lia | apply bv_eq; reflexivity] | exact G23]).
    assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
      by (transitivity (lib.Reusable.YK11.getr R 25);
          [apply (G 25); [apply CS; lia | apply bv_eq; reflexivity] | exact G25]).
    assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
      by (transitivity (lib.Reusable.YK11.getr R 26);
          [apply (G 26); [apply CS; lia | apply bv_eq; reflexivity] | rewrite G26, H26; reflexivity]).
    assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
      by (transitivity (lib.Reusable.YK11.getr R 27);
          [apply (G 27); [apply CS; lia | apply bv_eq; reflexivity] | rewrite G27, H27; reflexivity]).
    (* memory: the kept ranges of w2_cj_keeps *)
    assert (KF : forall lo hi, fr <= lo -> hi <= fr + 4096 -> KEEPR mem3 mem2 lo hi)
      by (intros lo hi L1 L2 a Ha; apply KFW; lia).
    assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr regs3 mem2).
    { apply (w2_frac_mem cx fr fr regs3 mem3 mem2); [| apply KF; lia | exact KS | apply KF; lia | exact HFRAC].
      intros a Ha _. rewrite Hspz in Ha. apply KH. lia. }
    assert (HRBE2 : B.ACtlCutP.RBE cx fr regs3 mem2).
    { apply (w2_rbe_mem cx fr regs3 mem3 mem2 A H9 ltac:(lia) ltac:(lia) ltac:(lia)
               (fun a Ha => KH a ltac:(lia)) (fun a Ha _ => KS a Ha) KTBL KBOX KROW).
      - intros Hh Hr. split; [exact (KNM Hh Hr) | exact (ctl_names_addressable _ _ _ _ _ _ HAR2 Hh Hr)].
      - exact HRBE. }
    pose proof (w2_rbe_regs cx fr regs3 regs2 mem2 F9 HRBE2) as HRBE3.
    pose proof HRBE3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S24' & S16' & S96' & S120' & _).
    rewrite G1.
    apply (H9a8 cx [Z.of_nat 0] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2 (eq_trans (proj1 (proj2 (proj2 (proj2 (proj2
             (proj2 HJc)))))) Hfrs) Hfa).
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B819a8_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_kmax nth]. rewrite Nat2Z.id. exact Hk.
    + unfold B.ACtlCut.ix_cut, B.ACtlCutP.C_B819a8_at, B.ACtlCutP.ixn.
      cbn [B.ACtlCut.cut_body nth]. split; [reflexivity |]. rewrite Nat2Z.id.
      exists phi.
      unfold B.ACtlCutP.RFb, B.ACtlCutP.RB, B.ACtlCutP.IDBr, B.ACtlCutP.FGBr, B.ACtlCutP.OURb in *.
      assert (KOUR : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 2624) (B.ACtlCutP.SM.OUR (B.ACtlCut.c_in cx))).
      { eapply w2_bytes_keep; [| exact HOUR]. apply KF;
          try unfold B.ACtlCutP.SM.OUR; rewrite ?length_map, ?length_seq; lia. }
      assert (KCUR : B.ACtlCutP.CUR cx 7 regs2) by exact (w2_cur_regs cx 7 regs3 regs2 F23 F25 HCUR).
      assert (K22 : B.ACtlCut.rgv regs2 22 (Z.of_nat 0)) by exact (w2_rgv_move regs2 regs3 22 _ F22 H22).
      assert (KIDB : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 2176) (B.ACtlCutP.SM.RID (B.ACtlCut.c_in cx) 0)).
      { eapply w2_bytes_keep; [| exact HIDB]. apply KF; rewrite ?B.Prog.Seg.RtmB.rb_RID_len; lia. }
      assert (KFGB : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 (fr + 2256) (B.ACtlCutP.SM.RFG (B.ACtlCut.c_in cx) 0)).
      { eapply w2_bytes_keep; [| exact HFGB]. apply KF; rewrite ?(B.Prog.Seg.RtmB.rb_RFG_len _ 0 ltac:(lia)); lia. }
      refine (conj (Permutation_trans Hbl2 Hperm) (conj _ (conj Hcn (conj Hb6 (conj _ (conj K22 (conj KOUR
                (conj KCUR (conj S120' (conj HRBE3 (conj _ (conj eq_refl (conj (conj (conj Hb6 (conj KCUR (conj KOUR
                (conj K22 (conj KIDB KFGB))))) (conj Hnz (conj _ _))) (conj _ (conj S24' (conj S16' (conj S96'
                (conj _ _)))))))))))))))))).
      * exact (w2_frac_regs cx fr fr regs3 regs2 mem2 F2 F3 F4 F8 F9 F19 F26 HFRAC2).
      * split; [exact (proj1 HHB) |]. unfold B.ACtlK.a_size. rewrite Z.max_l by lia.
        exact (w2_block_addressable _ _ _ _ _ _ _ HAR2 Hin2 ltac:(lia)).
      * exact (w2_rgv_move regs2 regs3 21 _ F21 H21).
      * exact (w2_rgv_move regs2 regs3 20 _ F20 H20).
      * eapply w2_bytes_keep; [| exact HFb]. rewrite HlF, Z2Nat.id by lia. exact KB.
      * unfold B.ACtlCut.a0v, B.ACtlCut.rgv. rewrite Ha02.
        rewrite <- (B.Prog.Seg.RtmB.rb_rtm_want (B.ACtlCut.c_in cx)). reflexivity.
      * apply (w2_addr_keep mem3); [| exact HAD2528].
        intros ii Hii. apply KS. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.ACtlCutP.FRAME_SHADOW,
          B.ACtlCutP.FRAME_BYTES. lia.
      * exact (w2_rgv_move regs2 regs3 27 _ F27 H27).
    + exact HRT2.
Qed.

End W2a.
