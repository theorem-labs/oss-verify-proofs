(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* lib/B/ACtlW3b.v -- piece W3b (cut-table-B.tsv rows 35-40 (a working note, not in this delivery): B81d80 .. B81e08; segments S_P7, S_P8, S_P9, S_P10,
   S_P11, S_P12) of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released
   cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane, by brief
   bwalk-piece.md (a working note, not in this delivery).
   rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one lemma per cut of W3b, NAMED AND STATED EXACTLY AS lib/B/ACtl.v's
   stage hypothesis (ACtl.v:492-502, seg_P7 .. seg_P12, after its CF / ix_cut notation), proved for every SK and FP
   (the top instantiates SK := Reusable.YE2k.tfib_sink_head, FP := []).
     seg_P7  B81d80 (0x81d80) -> B81da8   beq a0,s2 (taken), four spill loads, reac_ctrl_identity_fragment (a1 = 0)
     seg_P8  B81da8 (0x81da8) -> B81dbc   beq a0,s2 (taken), ld a0,64(s1), reac_ports_parse (q = 0)
     seg_P9  B81dbc (0x81dbc) -> B81dd4   li s2,-1, beq (taken), reac_ports_parse (p = q = 0)
     seg_P10 B81dd4 (0x81dd4) -> B81de8   beq a0,s2 (taken), reac_ports_unknown (p = 0, c = fr + 3040)
     seg_P11 B81de8 (0x81de8) -> B81e08   beq / lbu / beqz (taken), reac_ctrl_kind_name (a0 = 14)
     seg_P12 B81e08 (0x81e08) -> B81ec4_at [Z.of_nat 0] (left_0 >= 1) | B82eac (left_0 = 0, through 0x81ec4
                                         `bnez s9` not taken and 0x81ec8 `j 0x82eac`)
   Every cut owns the class-6 fake frame (own6), k <= 14; the successors' bounds are 14 (B81ec4_at at j = 0:
   14 + 2 * 0) and 526 (B82eac).  No allocator site, no fake-stack call, no runtime call, no loop of this piece.
   The four callees take no fake frame (16-byte frames; fragment: "No ASan stack frame",
   reac_ctrl_identity_fragment_c.v:12-13), so each call is LIFTED through the bridge by its footprint contract.

   TRAP OBLIGATIONS.  UBSan `unimp` 0x82fa0: none (plan 6.2 lists no branch for S_P7 .. S_P12; the listing has no
   branch to 0x82fa0 in [0x81d80, 0x81ec4)).  ASan abort sink 0x82fa4 and the report blocks 0x82fbc / 0x82fcc
   (`jal __asan_report_load1`): every branch into them in this stretch is NOT TAKEN inside a cited `_F` run, given
   a register / memory premise the stage supplies from the entry cut body:
     0x81d88 `j 82fa4`  guard 0x81d84 beq a0,s2 taken: s2 := -1 (0x81d80), a0 = -1 (C_B81d80's a0v regs (-1);
                        P7F.p7_pre_F's premise a0 = -1)                                         -- seg_P7;
     0x81dac `j 82fa4`  guard 0x81da8 beq a0,s2 taken: a0 = -1, s2 = -1 (C_B81da8's a0v (-1), rgv 18 (-1);
                        P8F.p8_pre_F's premises)                                                -- seg_P8;
     0x81dc4 `j 82fa4`  guard 0x81dc0 beq a0,s2 taken: s2 := -1 (0x81dbc), a0 = -1 (C_B81dbc's a0v (-1);
                        P9F.p9_pre_F)                                                           -- seg_P9;
     0x81dd8 `j 82fa4`  guard 0x81dd4 beq a0,s2 taken: a0 = -1, s2 = -1 (C_B81dd4's a0v (-1), rgv 18 (-1);
                        P10F.p10_pre_F)                                                         -- seg_P10;
     0x81df0 `j 82fa4`  guard 0x81dec beq a0,a1 taken: a1 := -1 (0x81de8), a0 = -1 (C_B81de8's a0v (-1);
                        P11F.p11_pre_F)                                                         -- seg_P11;
     0x81dfc `j 82fa4`  guard 0x81df8 beqz a0 taken: a0 = [fr + 3040] = 0 (C_B81de8's b8 m (fr + 3040) 0;
                        P11F.p11_pre_F's bytes_at Cc [0])                                       -- seg_P11;
     0x81e18 `j 82fb0`  taken only when the shadow byte k of QMARK is not 0; then 0x82fb4 bge a2,a1 with
                        a2 = QMARK & 7 = 0 < k (2 <= k <= 7) is not taken, back to 0x81e1c; 0x82fbc not reached
                        (P12F.p12_chk_F's premise bv_signed k = 0 \/ 2 <= .. <= 7)            -- seg_P12;
     0x81e28 `j 82fa4`  guard 0x81e24 beq a1,a2 taken: [QMARK] = 63 (read-only image byte)     -- seg_P12;
     0x81e40 `j 82fc0`  as 0x81e18 for QMARK + 1 (a2 = 1 < k); 0x82fcc not reached              -- seg_P12;
     0x81e4c `j 82fa4`  guard 0x81e48 beqz a0 taken: [QMARK + 1] = 0 (read-only image byte)     -- seg_P12.
   None is left unrefuted.

   ROUTE (lead FINAL 22:18Z via a Theorem Labs lane 22:29Z, route (a)).  Each stage is GLUE: a Theorem Labs lane's footprint re-run of
   ctrl's proved run up to the callee entry (`<run>_pre_F`), the callee's footprint contract (`<f>_contract_F`) and
   the empty return stretch (`<run>_post_F`), all at ONE RNG := ProgBridge.RNG_W (w_H W3), joined by ExecF.evtF_cut
   and lifted ONCE by Reusable.YA0nR.SRr_fsteps through ProgBridge's fevt_of_evtF (FEVT).  No `_F` steps a callee
   and none takes a callee contract as a premise (a Theorem Labs lane 23:15Z, binding).  Not used, by rule: a top,
   W_cutfree_ok, a cut-free twin, an LSCPS join.  (S_P12 has no callee: p12_chk_F then p12_body_F.)

   BUILD STATE (route (C), shell a working branch).  Every stage lemma seg_P7 .. seg_P12 is closed by
   Qed, over the named Section hypotheses below.  Each callee except reac_ports_parse is cited in its image-B region form (`_on`: the
   universal `shadow_rw m` premise, which ctl_rt_C does not give, is DROPPED or narrowed): reac_ports_unknown and
   reac_ctrl_kind_name by their PROVED `_F_on` theorems; reac_ctrl_identity_fragment (seg_P7) by its contract_F_on
   carried as a NAMED Section hypothesis until a Theorem Labs lane's B proof lands (WIP branch only until then).
   TYPE-CHECK on the prepared workspace, u19build a build machine; the commit messages carry each build's .prov, ws_hash and
   closure-scan label.  No Axiom, no Parameter, no Admitted, no admit.  The ONE place that names the shell's argument
   lists is the SHELL BINDING block below.

   ROUTE (C) (a Theorem Labs lane 09:20Z; shell a Theorem Labs lane 11:15Z): ctl_from's runtime premise is B.ACtlRtC.ctl_rt_C B ly3 S3 mem3
   = asan_cells_at /\ shadow_rw_on (cut_shadow ly3 S3) /\ shadow_rw_on img_shadow /\ ro_agree_at.  Every stage of this
   piece keeps ly3 / S3 (no allocation, no frame push or pop), so each exit supplies ctl_rt_C B ly3 S3 at the end
   memory by TRANSPORT from the entry's (w3b_ctl_rt_C: B.ShadowRwOnT.shadow_rw_on_kept for both shadow regions;
   seg_P12's own shadow stores re-read from p12_body_F's post under each region guard).  No stage uses
   ctlrt_of_AR, VIS0 or OWNED_RO.

   THE COMMON SHAPE OF A STAGE (proved once, below: w3b_cfg_MS, w3b_lift, w3b_journal, w3b_ctl_rt_C and the kept_on
   transports).  C0 intros in ctl_from's order, destruct the body and FRAC; C1 cfg_at = MState.MS over the canonical
   tree w3b_tree (Reusable.YA0nR.SRr_xregs_eqv); C2 the lift; C3 the journal by Reusable.YCbq.ajournal_exec over the
   run's write set (each written byte is the journal's: its stack window, or the own class-6 frame / frame shadow);
   C4 ctl_rt_C by lib/B/AsanRTFacts.v's and lib/B/ShadowRwOnT.v's kept lemmas (S_P12: its shadow stores are read back
   from p12_body_F's post); C5 the successor body, each reader moved by the kept_on of its own bytes.

   SECTION HYPOTHESES (obligation; owner).  Kept NAMED per the owner ruling a Theorem Labs lane 05:31Z (the TOP discharges):
   - tfibsegs_rsegs, Hwx, img_vis_W, FEVT: proved at their sources (lib/B/ProgBridge.v; core wx_segs_nowrap_of_b).
   - LAWS, segs_low: the core's AR laws / segment bound (record core).
   - mem_grows_fsteps: M3, the growth clause of ajournal_after_munch (a Theorem Labs lane).
   - own6_frame: T7 / T8 / V5, the own class-6 frame's placement (above the image, below alloc_ceiling) and
     presence (a Theorem Labs lane; proof in lib/B/ACtlOwn6.v, a Theorem Labs lane).
   - ctl_qmark_addressable: V6, QMARK's 2 bytes addressable (a Theorem Labs lane).
   - kn_relro, FP_nil: arithmetic / eq_refl at the TOP's instance (RLO / RHI; FP = []) (a Theorem Labs lane).
   - shared RtPost members, token for token (owner a Theorem Labs lane): aview_vis_mrd, ctl_kind_name_not_owned,
     ctl_bcmp_cells_of_AR, ctl_kind_name_shadow_vis, ctl_kind_name_str_shadow.
   - reac_ctrl_identity_fragment_holds_F_on (route (C); replaces reac_ctrl_identity_fragment_holds_F_closed): the
     fragment callee's image-B region form RFG.reac_ctrl_identity_fragment_contract_F_on (statement
     lib/B/Prog/reac_ctrl_identity_fragment_c.v 4b2a0e1f8a0 (the blob this tree had at release c5e779efe8c), a Theorem Labs lane 0cf5e518128, on a working branch
     a2ab7f5988a).  OBLIGATION: the B proof of contract_F_on, closed over its memcpy / bcmp_wrap / record-checksum
     callees.  OWNER a Theorem Labs lane.
   DISCHARGED in this file: PP_F / PU_F_on / KN_F_on by the callees' closed theorems (reac_ports_parse_F_holds;
   route (C): reac_ports_unknown_F_holds_on and reac_ctrl_kind_name_holds_F_on, the region forms with the premise
   shadow_rw m DROPPED, a Theorem Labs lane's lib/B/Prog/reac_ctrl_kind_name_F.v blob edeba4fddbe (the blob this tree had at release c5e779efe8c), taken by path from
   a working branch 924cd2205f6); ctl_input_block (T5 / T6) DERIVED from the pre's input block and the
   journal's block clause (lib/B/ACtlW4g.v's proof); WIN_SH_VIS (B.ProgWorld.win_sh_vis_stmt) by
   lib/B/ProgWorldVisWin.v's win_sh_vis (RULE a Theorem Labs lane 13:12Z: a proved ProgWorld statement is cited); win_shadow_vis
   (V6) from WIN_SH_VIS at the journal's AR; kn_fp_spares from FP_nil; kind_name_table (T10) DERIVED from the journal's
   static clause, the pre's arodata_okS and the image bytes; ctl_bcmp_cells from ctl_bcmp_cells_of_AR at the journal's
   AR.
   ITEM 23: the four callees are program callees, each joined to its `_pre_F` / `_post_F` and lifted WHOLE (C2), so
   every raw `munch` / `wmono` used is a footprint run's own post over the lifted run, never a world post; no
   hypothesis or statement of this file states raw memory of a runtime call.
   mem_inv: NO hypothesis.  The one premise of this file's callees that asks lib/Lib's mem_inv is
   reac_ctrl_identity_fragment's (seg_P7); the cut memory holds the image's read-only bytes, so mem_inv is false
   there (lib/B/ProgWorld.v:128-132).  seg_P7 runs that callee on MemNorm.normalize rsegs mem3
   (MemNorm.mem_inv_normalize) and moves the run back by MemNormF.evtF_normalize_ro under ctl_rt_C's ro_agree
   (lib/B/ACtlW4c.v's route for the same callee); the post comes back through MemNorm.ms_rel.
   a Theorem Labs lane's `_F` RUNS, CITED BY MODULE (Required qualified below, never Imported, never restated; from
   a working branch 12a7ea50807, the one branch of every image-B `_F` (a Theorem Labs lane 00:4xZ); blobs P7F
   edcdc73bc5c, P8F e2cbda5700f, P9F 5d973a465ef, P10F 5090b50aa09, P11F e0cbf0cbc2a, P12F 754949feaa6, equal to
   a working branch 4010484f278; texts bF-statements/P7F.md (a working note, not in this delivery) .. P12F.md (a working note, not in this delivery), 00:19Z.  None is a `_run` or `*_of_F_bounded` lemma; their
   bound premises (A + k <= 2^64, Cc + 1 <= 2^64, 0 <= x < 2^64) are discharged in each plan from FRAC's
   A + 448 <= S < APPMEM_END and the frame placement):
     P7F.p7_pre_F  / P7F.p7_post_F   (0x81d80 -> 0x859e4, ra = 0x81da8 / the return pc; source Seg/P7.v:33)
     P8F.p8_pre_F  / P8F.p8_post_F   (0x81da8 -> 0x883d0, ra = 0x81dbc; source Seg/P8.v:30)
     P9F.p9_pre_F  / P9F.p9_post_F   (0x81dbc -> 0x883d0, ra = 0x81dd4; source Seg/P9.v:29)
     P10F.p10_pre_F / P10F.p10_post_F (0x81dd4 -> 0x88628, ra = 0x81de8; source Seg/P10.v:30)
     P11F.p11_pre_F / P11F.p11_post_F (0x81de8 -> 0x83d98, ra = 0x81e08; source Seg/P11.v:36)
     P12F.p12_chk_F  (0x81e08 -> 0x81e50, the two checks; composes P12F.p12_ck1_F / p12_ck2_F; source Seg/P12.v:192)
     P12F.p12_body_F (0x81e50 -> 0x81ec4 (nl <> 0) | 0x82eac (nl = 0); source Seg/P12.v:225)
   Each `<run>_post_F` here steps no instruction (the callee returns at the exit cut); its premises are the
   callee's contract_F post, so the joined run ends in its post (Q of the source run).
   AC.GT: none of the `_F` lemmas cited states AC.GT (checked at 12a7ea50807), so this file has no AC.GT = IMG_TOP
   lemma.  P12F.p12_body_F's premises name SlotInv's FRAME_BYTES / FRAME_SHADOW and its post SlotInv's q64 / fragb
   and P12.p12_W: the stage only APPLIES it; the proof unfolds those (SlotInv's FRAME_BYTES_val /
   FRAME_SHADOW_val: 3136 / 392, the same literals as ACtlCutP's FRAME_BYTES / FRAME_SHADOW; q64 / fragb with
   ACtlCutP's bodies over rsegs = tfibsegs); no statement or hypothesis of this file names them.
   PENDING KIT / BRIDGE FACTS: as lib/B/ACtlW3a.v's header, plus T10 (the KIND_NAME table bytes from the core's
   arodata_okS RLO RHI, plan 2.4 T10) and the read-only image bytes of QMARK / the kind-name strings from ctl_rt_C's
   ro_agree (ctrl's p11_strings / p12_qmark argument, Seg/P11.v:115, Seg/P12.v:90, restated in the build).

   CLOSURE (rule (3); measured then: 303 files, a Require walk from this file over the then tip with a Theorem Labs lane's P7F-P12F
   from 12a7ea50807; the blob list below is not re-measured): the frame-route files reached through the `_F` modules were the v1.9 blobs of record:
   lib/B/Prog/SlotModel.v de18d111c37, lib/B/Prog/SlotInv.v dfc10b8f7a4, lib/B/Prog/Seg/* at 3803efccea0
   (Seg/P7.v d62a9469a6e, P8.v 32bfb16a8ea, P9.v 1722ad5cfbb, P10.v f615c6bb3a2, P11.v b8f0598ab1a,
   P12.v 1951f14dd81, the blobs a Theorem Labs lane re-runs), and through P12F -> lib/B/Contract.v
   65b05173b1a: lib/B/ClassConsDef.v 164f778c20b, lib/AZ/Spec/AsanCtrl.v 80ffbfc0a07, AsanCtrlProps.v b4f333a2672,
   STree.v 1293d54ecd2 (porter 00:24Z: closure only), lib/B/AsanRTInv.v 5cd1e53cede, FrameAPI.v c09def579bd,
   MemNorm.v a10a476ffd9, PContract.v 4f9a4d5ed82, AsanRT.v 32e0f5191fd, lib/MemNorm.v 248a639b490; and
   lib/AZ/LibA/AcctCore.v 0e06d81d553 through lib/Lib/ExecF.v (porter 00:25Z).  No other lib/AZ file.  seg_P7's proof
   also Requires lib/B/MemNormF.v (Requires only lib/B/Reusable/YK11, lib/Lib and lib/B Img0 / MemNorm).  No statement
   or hypothesis of this file names a frame-route identifier (SlotInv, lib/AZ, AsanRTInv, Contract, FrameAPI,
   SpinAlg, W6, MemNorm, QSlot / ClassConsDef / ClassRoomLow / AsanCtrl* / STree).

   PROVENANCE: cut table cut-table-B.tsv rows 35-40 (lines 36-41) (a working note, not in this delivery); plan
   llvmf-B-walk-plan.md 2.2 rows 35-40, 2.3 rows 35-40, 2.4 row S_P11, 6.2 (a working note, not in this delivery);
   ctrl's runs at a working branch 3803efccea0 (Seg/P7.v .. P12.v); objdump
   fuzz_ctrl.objdump.txt L84653-L84738, L85813-L85824 (a working note, not in this delivery). *)

From Coq Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six modules that exist twice (core lib/Reusable and the unit's lib/B/Reusable) are Required through the
   CORE prefix, never as `Reusable.X` (a Theorem Labs lane 04:24Z / 04:33Z, amendment (b)): YI04 YI16 YK11 YK1b YM05 YO09. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YI16 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI04 YP09 YO0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.RngBytes B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Cells Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.AsanRTFacts B.ProgBridge.
(* proof use only (seg_P7; no statement or hypothesis names them): image B's memory normalization, the copies the
   callee statements use (lib.B.MemNorm, never the root lib.MemNorm), and its evtF transfer MemNormF.evtF_normalize_ro *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm B.MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel Prog.RcIdentModel Prog.RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.bcmp_wrap_c B.Prog.memcmp_c Prog.RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.rng_asan B.Prog.ImgBounds B.ProgWorld.
(* seg_P12 applies three proof-internal facts of ctrl's own image-B frame route (closure only, already reached
   through P12F; no statement of this file names them): SlotInv.FRAME_BYTES_val / FRAME_SHADOW_val / id_ok_ID0, and
   Seg/P12.v's p12_qmark / p12_frag_ok_z72. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotInv B.Prog.Seg.P12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ports_parse_c B.Prog.reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_kind_name_c.
(* The three callees whose footprint contract is PROVED CLOSED in this unit (a Theorem Labs lane 04:29Z pattern (2): a
   `<f>_contract_F` premise is discharged by the callee's own closed theorem, never by a lift). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ports_parseF B.Prog.reac_ports_unknownF.
(* reac_ctrl_kind_name_F.v (route (C): blob edeba4fddbe (the blob this tree had at release c5e779efe8c), a working branch 924cd2205f6, taken by
   path): its reac_ctrl_kind_name_holds_F_on discharges KN_F_on (the region form, premise shadow_rw m DROPPED). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_kind_name_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
(* route (C): the cut's runtime form ctl_rt_C (a Theorem Labs lane's B twin of a Theorem Labs lane's cform) and its region transports. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ShadowRwOn B.ShadowRwOnT.
(* RULE a Theorem Labs lane 13:12Z: proved ProgWorld statements are cited: WIN_SH_VIS by lib/B/ProgWorldVisWin.v's win_sh_vis. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldVisWin.
(* a Theorem Labs lane's footprint runs of S_P7 .. S_P12 (a working branch 12a7ea50807), Required QUALIFIED, never
   Imported (porter 23:38Z); their closure is the CLOSURE paragraph of the header. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P7F P8F P9F P10F P11F P12F.
Import ListNotations.
Local Open Scope Z_scope.

Module RFG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.
Module RPP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_parse_c.
Module RPU := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknown_c.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
(* lib/Lib's memory vocabulary and the walk's own runtime file, qualified only (the SHADOWED NAMES rule of
   lib/B/ACtlCut.v: no lib/Lib module is Imported here). *)
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module MST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module PEX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module R6S := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module XF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRTFacts.
Module IMG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Img0.
Module PBR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgBridge.
Module SMD := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RLF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.
Module RFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module BWC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module RAS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.rng_asan.
Module IMB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ImgBounds.
Module YCB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module KIT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.

Section W3b.

(* The shell's contexts and variables, in its order (lib/B/ACtlCut.v section CtlCut).  SK is the core's sink head,
   instantiated EXPLICITLY at the top (Reusable.YE2k.tfib_sink_head). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists.  CF / ix_cut as in
   lib/B/ACtl.v, with SK and FP left generic. ---- *)
Local Notation CF POST X := (B.ACtlCut.ctl_from B MT XM_LIB RLO RHI FP POST X).
Local Notation ix_cut := B.ACtlCut.ix_cut.
Local Notation C_B81d80 := (B.ACtlCutP.C_B81d80 B).
Local Notation C_B81da8 := (B.ACtlCutP.C_B81da8 B).
Local Notation C_B81dbc := (B.ACtlCutP.C_B81dbc B).
Local Notation C_B81dd4 := (B.ACtlCutP.C_B81dd4 B).
Local Notation C_B81de8 := (B.ACtlCutP.C_B81de8 B).
Local Notation C_B81e08 := (B.ACtlCutP.C_B81e08 B).
Local Notation C_B81ec4_at := (B.ACtlCutP.C_B81ec4_at B).
Local Notation C_B82eac := (B.ACtlCutP.C_B82eac B).

(* ---- Section hypotheses (sources in the header).  Owner ruling a Theorem Labs lane 05:31Z: the bridge / shared facts stay
   NAMED Section hypotheses in every stage file and the TOP (lib/B/ACtl.v) discharges each once; each is PROVED in
   this tree at its source: tfibsegs_rsegs / img_vis_W / FEVT by lib/B/ProgBridge.v (tfibsegs_rsegs, img_vis_W over
   ImgBounds' IMG_LO / IMG_HI = 0x10000 / 0x5fe000, fevt_of_evtF), Hwx by the core's wx_segs_nowrap_of_b. ---- *)
Hypothesis tfibsegs_rsegs : Reusable.YB1v.tfibsegs = B.Img0.rsegs.
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* img_vis_W: the walk's image-visibility bridge name (a Theorem Labs lane ProgBridge.img_vis_W, 7b850582d6a); the shape the
   stage files already share (lib/B/ACtlW1.v, ACtlW3a.v, ACtlW4a-c.v), with the bounds by the core's names
   Reusable.YImgTop.IMG_LO (0x10000) / IMG_TOP (0x5fe000), never the literals (porter 23:40Z; a Theorem Labs lane 2026-10-29). *)
Hypothesis img_vis_W : forall W : Reusable.YA0n.world segs,
  0 <= Reusable.YImgTop.IMG_LO /\
  Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) <= 2 ^ 64 /\
  forall a, Reusable.YImgTop.IMG_LO <= a <
              Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) ->
    Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.

(* ProgBridge.fevt_of_evtF, image B (bridge-stmt.md:102). *)
Hypothesis FEVT : forall (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (ms : machine_state),
  Lib.ExecF.evtF B.Img0.rsegs RNG P ms -> exists ms', Reusable.YK04R.fsteps segs RNG ms ms' /\ P ms'.

(* ---- The callees' footprint contracts.  PP_F / PU_F_on / KN_F_on are DISCHARGED below by the callees' own PROVED CLOSED
   theorems in this unit (a Theorem Labs lane's image-B table, 04:40Z; pattern (2), a Theorem Labs lane 04:29Z: never by a lift).
   Route (C): reac_ports_unknown and reac_ctrl_kind_name are cited in their region form contract_F_on (premise shadow_rw m DROPPED; a Theorem Labs lane's
   reac_ctrl_kind_name_holds_F_on, and reac_ports_unknown_F_holds_on), because the cut carries ctl_rt_C, not the universal shadow_rw.
   Route (C): reac_ctrl_identity_fragment is carried in its region form contract_F_on as a NAMED Section hypothesis
   under its own statement (a Theorem Labs lane's B _on STATEMENTS, 0cf5e518128 via a working branch a2ab7f5988a; its R is
   guarded by f <> 0 /\ fr <> 0 /\ ..., so seg_P7's fr = 0 call needs no shadow byte).
   OBLIGATION: cite a Theorem Labs lane's closed B proof of contract_F_on by name once it lands (and delete this hypothesis).
   OWNER a Theorem Labs lane. ---- *)
Hypothesis reac_ctrl_identity_fragment_holds_F_on : RFG.reac_ctrl_identity_fragment_contract_F_on.

Lemma KN_F_on : KNC.reac_ctrl_kind_name_contract_F_on.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_F.reac_ctrl_kind_name_holds_F_on. Qed.

Lemma PP_F : RPP.reac_ports_parse_contract_F.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_parseF.reac_ports_parse_F_holds. Qed.

Lemma PU_F_on : RPU.reac_ports_unknown_contract_F_on.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on. Qed.

(* ---- The core's own facts, under which Reusable.YCbq's journal section is stated (donor YCbq.v:204-208); the
   same two names lib/B/ACtlW3a.v and lib/B/ACtlW4e1.v carry.
   OBLIGATION: the relocated core's AR laws for ctrl's B.  OWNER a Theorem Labs lane (record core). ---- *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* ---- The two PENDING bridge facts of plan M3 / M5 that this file consumes. ---- *)

(* M3, the growth half of ProgBridge's ajournal_after_munch: a footprint run only ADDS materialized bytes, so the
   visible memory of the world grows across it.  (The frozen half and the hidden half are proved below from the
   run's own munch and from Reusable.YA0nR.fsteps_keeps_hidden; this is the half no published lemma states.)
   OBLIGATION: ProgBridge's ajournal_after_munch (M3 (plan (a working note, not in this delivery))), growth clause.  OWNER a Theorem Labs lane. *)
Hypothesis mem_grows_fsteps : forall (W : Reusable.YA0n.world segs) (RNG : Lib.ExecF.footprint) (ms ms' : machine_state),
  Reusable.YK04R.fsteps segs RNG ms ms' ->
  lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms))
    (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms')).

(* M5 / plan 2.4 T7-T8 and V5: the placement of the walk's own class-6 fake frame.  The journal names the frame by
   the CURRENT layout ly3 while ctl_from's HFA names it by the entry layout c_ly cx (layout_le keeps ly_F, which no
   published lemma states); the frame's 4096 bytes and its 512 shadow bytes are present at the journal's world; and
   the frame sits ABOVE the loaded image and BELOW alloc_ceiling (the fake stack may be in low or in high
   application memory: the core's AR_frames_law gives in_app only, frames_bounds gives fr + 4096 <= alloc_ceiling;
   the stages take the low / high case split from AR_frames_law, w3b_own6_place below).
   OBLIGATION: ProgBridge's frame-placement transports T7 / T8 / V5 (plan (a working note, not in this delivery)).  OWNER a Theorem Labs lane
   (proof in lib/B/ACtlOwn6.v, a Theorem Labs lane). *)
Hypothesis own6_frame : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k fr,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) /\
  Reusable.YImgTop.IMG_TOP <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 \/ ART.shadow_addr fr <= a < ART.shadow_addr fr + 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).

(* The walk's shared RtPost members aview_vis_mrd and ctl_kind_name_not_owned, token for token from
   RTPOST-SHARED-B.txt (a working note, not in this delivery) (from a working branch 0110c1f2b9b; owner a Theorem Labs lane; kept named per the owner ruling 05:31Z). *)
(* aview_vis_mrd: lib/A/ProgWorld.v :556-559 (a version not in this delivery; at head lib/A/ProgWorld.v:564-567) (PROVED on A). *)
Hypothesis aview_vis_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).

Hypothesis ctl_kind_name_not_owned : forall a : Z,
  B.ACtlCutP.KNA.KIND_NAME <= a < B.ACtlCutP.KNA.KIND_NAME + 112 ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

(* kn_relro: the KIND_NAME table [0x9f580, + 112) lies in the read-only data span [RLO, RHI) of the core's pre
   (arodata_okS RLO RHI), which the T10 derivation of kind_name_table (below) reads.  It holds by arithmetic at the
   TOP's instance.  OBLIGATION: at the top RLO = 0x9f1a0, RHI = 0xa15e8 (lib/B/ACtlK.v header).  OWNER the top
   (a Theorem Labs lane, lib/B/ACtl.v). *)
Hypothesis kn_relro : RLO <= KNC.KIND_NAME /\ KNC.KIND_NAME + 112 <= RHI.

(* The freed-block list is the empty one: the top runs the walk with FP := [] (lib/B/ACtl.v's CF notation) and
   discharges this by eq_refl; the sibling lib/B/ACtlW4g.v's name and text.  The journal keeps an entry block's and an
   image byte's view only off FP (YCbq.ajournal's block and static clauses).  OWNER the top (a Theorem Labs lane). *)
Hypothesis FP_nil : FP = [].

Lemma kn_fp_spares : forall a, KNC.KIND_NAME <= a < KNC.KIND_NAME + 112 -> Reusable.YCbq.fp_spares (SK := SK) FP a.
Proof.
  intros a _. rewrite FP_nil. unfold Reusable.YCbq.fp_spares, lib.Reusable.YI16.sink_open_fp,
    lib.Reusable.YI16.in_fp. intros (r & Hr & _). destruct Hr.
Qed.

(* The walk's shared RtPost member ctl_bcmp_cells_of_AR (T11), token for token from RTPOST-SHARED-B.txt (a working note, not in this delivery)
   (from a working branch 0110c1f2b9b; owner a Theorem Labs lane): the five runtime cells reac_ctrl_identity_fragment's callees read by
   absolute address hold their load-time values under AR. *)
Hypothesis ctl_bcmp_cells_of_AR : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.REAL_BCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.bcmp_wrap_c.BCMP)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.REAL_MEMCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.memcmp_c.MEMCMP)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem B.Prog.bcmp_wrap_c.GOT_CF (lib.Lib.Mem.le8 (lib.Lib.Mem.wa B.Prog.bcmp_wrap_c.CF)) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem (B.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1] /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem (B.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1].

(* The same five cells at a journal memory: the journal's FIRST conjunct is AR at the cut state. *)
Lemma ctl_bcmp_cells : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  MEM.bytes_at B.Img0.rsegs mem3 BWC.REAL_BCMP (MEM.le8 (MEM.wa BWC.BCMP)) /\
  MEM.bytes_at B.Img0.rsegs mem3 BWC.REAL_MEMCMP (MEM.le8 (MEM.wa MCC.MEMCMP)) /\
  MEM.bytes_at B.Img0.rsegs mem3 BWC.GOT_CF (MEM.le8 (MEM.wa BWC.CF)) /\
  MEM.bytes_at B.Img0.rsegs mem3 (BWC.CF + 254) [Z_to_bv 8 1] /\
  MEM.bytes_at B.Img0.rsegs mem3 (BWC.CF + 255) [Z_to_bv 8 1].
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k _ HJ. destruct HJ as (HAR & _).
  exact (ctl_bcmp_cells_of_AR _ _ _ _ _ HAR).
Qed.

(* WIN_SH_VIS: the stack window's 8-aligned shadow cover is visible (statement B.ProgWorld.win_sh_vis_stmt).  RULE
   a Theorem Labs lane 13:12Z: a PROVED ProgWorld statement is CITED, not carried; its image-B proof is
   lib/B/ProgWorldVisWin.v's win_sh_vis (Qed, on a working branch a2ab7f5988a), so the former Section hypothesis of this name
   is now this one-line lemma.  win_shadow_vis (below) is its instance at the journal's AR over the walk's own
   window. *)
Lemma WIN_SH_VIS : B.ProgWorld.win_sh_vis_stmt B.
Proof. exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgWorldVisWin.win_sh_vis B). Qed.

(* The walk's shared RtPost member ctl_kind_name_shadow_vis, token for token from RTPOST-SHARED-B.txt (a working note, not in this delivery)
   (from a working branch adc9b58a03c; owner a Theorem Labs lane; Qed in lib/B/ProgBridgeData.v at fbe168f4d89, kept named per the owner ruling
   05:31Z): KIND_NAME's 14 shadow bytes are visible, which pays reac_ctrl_kind_name's `rng RNG (shadow_addr
   KIND_NAME) 14`. *)
Hypothesis ctl_kind_name_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr B.ACtlCutP.KNA.KIND_NAME) 14.

(* The walk's shared RtPost member ctl_kind_name_str_shadow, token for token from RTPOST-SHARED-B.txt (a working note, not in this delivery)
   (from a working branch adc9b58a03c; owner a Theorem Labs lane; Qed in lib/B/ProgBridgeData.v at fbe168f4d89, kept named per the owner ruling
   05:31Z).  seg_P12 uses its visibility half at v = 14 (kind_name_addr 14 = QMARK): the check block reads QMARK's
   shadow byte. *)
Hypothesis ctl_kind_name_str_shadow : forall ly S (W : Reusable.YA0n.world segs) mem md v,
  Reusable.YG0n.AR segs B ly S W mem md -> 0 <= v < 2 ^ 31 ->
  B.AsanRT.addressable mem (B.ACtlCutP.KNA.kind_name_addr v) 1 /\
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr (B.ACtlCutP.KNA.kind_name_addr v)) 1.

(* V6 (plan 2.4): BOTH bytes of the "?" string at QMARK ("?" and its 0) are addressable, i.e. QMARK is a registered
   2-byte global and its shadow byte is 0 or 2 .. 7.  seg_P12's check block (P12F.p12_chk_F) needs that bound:
   with one addressable byte (the shared ctl_kind_name_str_shadow) the shadow byte could be 1, and then the second
   check (0x81e2c .. 0x81e40) would take the report branch.  ctrl's own proof reads it from FRA's registered-globals
   clause (Seg/P12.v:391-406, frame_AG's (QMARK, 2) entry).
   OBLIGATION: plan 2.4 V6 for QMARK's 2 bytes (widen ctl_kind_name_str_shadow at v > 13, or a frame_AG twin).
   OWNER a Theorem Labs lane. *)
Hypothesis ctl_qmark_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem KNC.QMARK 2.

(* V6 at the walk's window, DERIVED from the shared WIN_SH_VIS: the journal's AR at the cut state (its first
   conjunct), layout_le keeps the stack bounds of the entry layout, and astk_ok puts the window
   [c_sp cx - LLVMF_STK, c_sp cx) inside [ly_stk_lo, ly_stk_hi).  reac_ctrl_identity_fragment_contract_F takes it as
   `sh_word_rng RNG (sp - K) K` (rng_asan.v). *)
Lemma win_shadow_vis : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k
    (lo n : Z),
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> 0 < n -> lo + n <= B.ACtlCut.c_sp cx ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (RAS.sh_al8_lo lo) (RAS.sh_al8_hi lo n - RAS.sh_al8_lo lo).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo n HJ Hlo Hn Hhi.
  pose proof HJ as (HAR & HLE & _).
  pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & _ & _ & Hslo & Hshi & _).
  destruct (WIN_SH_VIS LAWS ly3 S3 W3 mem3 md3 lo n HAR ltac:(rewrite Eslo; lia) ltac:(rewrite Eshi; lia)
              ltac:(lia)) as [E0 | HV]; [lia | exact HV].
Qed.

(* T10 (plan (a working note, not in this delivery)), DERIVED (owner ruling a Theorem Labs lane 06:19Z): the KIND_NAME pointer table [KIND_NAME, + 112)
   (GNU_RELRO, writable in rsegs, so not read through ctl_rt_C's ro_agree) holds the image's bytes at every journal
   memory.  The journal's static clause keeps the view of an image byte that is not owned-static, not the errno
   cell (ctl_kind_name_not_owned) and spared by FP (kn_fp_spares); the core's pre states the entry view of
   [RLO, RHI) as the image's (arodata_okS; kn_relro); a visible view read is the mrd byte (aview_vis_mrd); and the
   image's bytes there are kind_name_bytes (Seg/P11.v p11_kn_rom / p11_rom_nth, vm_compute over the image). *)
Lemma kind_name_table : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  MEM.bytes_at B.Img0.rsegs mem3 KNC.KIND_NAME KNC.kind_name_bytes.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HARO & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
  pose proof OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P11.p11_kn_len as HKL.
  split; [unfold KNC.KIND_NAME; lia |].
  split; [rewrite HKL; unfold KNC.KIND_NAME; cbn; lia |].
  intros i Hi. rewrite HKL in Hi.
  assert (Ha : KNC.KIND_NAME <= KNC.KIND_NAME + Z.of_nat i < KNC.KIND_NAME + 112) by lia.
  destruct (ctl_kind_name_not_owned _ Ha) as (Hno & Herr).
  assert (Hin : Reusable.YG0d.in_img segs (KNC.KIND_NAME + Z.of_nat i)).
  { assert (HM : In (0x9f000, 0x3000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
      by (rewrite PBR.rsegs_spans; right; right; left; reflexivity).
    apply in_map_iff in HM. destruct HM as (sg & Esg & Hsg). injection Esg as Eb Es.
    unfold Reusable.YG0d.in_img. exists sg. split; [exact Hsg |]. unfold KNC.KIND_NAME in *. lia. }
  pose proof (HST _ Hin Hno Herr (kn_fp_spares _ Ha)) as E1.
  assert (HRR : RLO <= KNC.KIND_NAME + Z.of_nat i < RHI) by (destruct kn_relro; lia).
  rewrite (HARO (KNC.KIND_NAME + Z.of_nat i) (or_intror HRR) Hno Herr) in E1.
  assert (Hvis : Reusable.YA0n.w_H W3 (Z_to_bv 64 (KNC.KIND_NAME + Z.of_nat i)) = false).
  { destruct (img_vis_W W3) as (_ & _ & H3). apply H3. unfold KNC.KIND_NAME in *. lia. }
  rewrite (aview_vis_mrd W3 mem3 _ Hvis) in E1.
  destruct (nth_error KNC.kind_name_bytes i) as [b |] eqn:Eb;
    [| apply nth_error_None in Eb; rewrite HKL in Eb; lia].
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P11.p11_rom_nth KNC.kind_name_bytes
                KNC.KIND_NAME i b OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P11.p11_kn_rom Eb) as Erom.
  assert (E2 : option_map (fun b0 : byte => bv_unsigned b0)
                 (MEM.mrd B.Img0.rsegs mem3 (MEM.wa (KNC.KIND_NAME + Z.of_nat i))) = Some (bv_unsigned b)).
  { etransitivity; [exact E1 |].
    (* P11 states the image byte with the unit copy's seg_rom (same body as the core's): equal by conversion. *)
    exact (f_equal (option_map (fun b0 : byte => bv_unsigned b0)) Erom). }
  destruct (MEM.mrd B.Img0.rsegs mem3 (MEM.wa (KNC.KIND_NAME + Z.of_nat i))) as [b' |] eqn:Em;
    cbn in E2; [| discriminate E2].
  injection E2 as Eb'. assert (Ebb : b' = b) by (apply bv_eq; exact Eb'). subst b'. reflexivity.
Qed.

(* T5 / T6 (plan (a working note, not in this delivery)), DERIVED (owner ruling a Theorem Labs lane 07:07Z; the proof of lib/B/ACtlW4g.v's w4g_f1_IN at
   a working branch ecd49084237, with this file's names): the entry input block at a journal memory.  Its
   bytes: the pre's garr8 (the entry view), kept by the journal's block clause (a block live at the entry and at the
   cut, off FP = []).  Its shadow: the core's block-shadow law (al_shadow) at the cut's AR, read through lib/Lib. *)
Lemma w3b_aview_present : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.apresent H mem a ->
  exists b, mem (Z_to_bv 64 a) = Some b /\
    Reusable.YG0n.aview segs H mem a = Some (bv_unsigned b) /\
    lib.Lib.Mem.mrd segs mem (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros H mem a [Hh [b Hb]]. exists b. split; [exact Hb |]. split.
  - unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite Hh, Hb. reflexivity.
  - unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
Qed.

Lemma w3b_mrd_of_aview : forall (H : word -> bool) (mem : word -> option byte) (a v : Z),
  0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  Reusable.YG0n.aview segs H mem a = Some v ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem a v Ha Hni Hv.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv.
  rewrite (Reusable.YCbq.seg_rom_none segs a Ha Hni) in Hv.
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  destruct (H (Z_to_bv 64 a)); [cbn in Hv; discriminate |].
  destruct (mem (Z_to_bv 64 a)) as [b |]; cbn in Hv; [| discriminate].
  injection Hv as Hv. exists b. split; [reflexivity | exact Hv].
Qed.

Lemma w3b_le_byte1 : forall v, 0 <= v < 256 -> lib.Reusable.YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold lib.Reusable.YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma w3b_signed_small : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ctl_input_block : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) ->
  0 < B.ACtlCut.c_n cx ->
  B.ACtlCutP.f1_IN cx mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ Hperm Hn.
  pose proof HB as ((_ & _ & _ & _ & Hdisj & Hlen & Hgarr & _) & _).
  destruct Hdisj as [[E0 _] | [_ Hin0]]; [lia |].
  assert (Hin3 : In (B.ACtlCut.c_p cx, B.ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
    by exact (Permutation_in _ (Permutation_sym Hperm) Hin0).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & HF2 & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hpres & _ & Hnmax).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (Hbsh & _).
  pose proof (Reusable.YG0f.ASAN_CEIL_range (rc := rc)) as [Hceil _]. unfold Reusable.YG0f.ASAN_CEIL in Hceil.
  assert (Hreq : Reusable.YG00.req_size (B.ACtlCut.c_n cx) = B.ACtlCut.c_n cx).
  { unfold Reusable.YG00.req_size. destruct (B.ACtlCut.c_n cx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
  rewrite Hreq in Hpceil, Hpapp, Hpres, Hbsh.
  split.
  - unfold B.AsanRT.addressable.
    split; [lia |]. split; [lia |]. split; [unfold B.AsanRT.APPMEM_END; lia |].
    intros i Hi. unfold B.AsanRT.addr_byte. split.
    + unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL in Hpapp.
      lia.
    + destruct Hbsh as (Hp8 & _ & Hsh).
      specialize (Hsh (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])).
      unfold Reusable.YG0v.shadow_of_addr in Hsh.
      assert (Esh : B.AsanRT.shadow_addr (B.ACtlCut.c_p cx + i) =
                    Reusable.YG0f.SHADOW_OFF + B.ACtlCut.c_p cx / 8 + i / 8).
      { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF. lia. }
      assert (Hsr : 0 <= Reusable.YG0f.SHADOW_OFF + B.ACtlCut.c_p cx / 8 + i / 8 < 2 ^ 64)
        by (unfold Reusable.YG0f.SHADOW_OFF; lia).
      assert (Hsi : ~ Reusable.YG0d.in_img segs (Reusable.YG0f.SHADOW_OFF + B.ACtlCut.c_p cx / 8 + i / 8)).
      { intros Himg. pose proof (segs_low _ Himg) as Hl.
        unfold Reusable.YG0f.kLowMemEnd, Reusable.YG0f.SHADOW_OFF in Hl. lia. }
      destruct (w3b_mrd_of_aview _ _ _ _ Hsr Hsi Hsh) as (b & Hb & Hbv).
      exists b. rewrite Esh. split; [exact Hb |].
      unfold B.AsanRT.shadow_ok.
      destruct (i / 8 <? B.ACtlCut.c_n cx / 8) eqn:Eg.
      * left. rewrite w3b_signed_small by lia. exact Hbv.
      * apply Z.ltb_ge in Eg. right. rewrite w3b_signed_small by (rewrite Hbv; lia). rewrite Hbv. lia.
  - unfold lib.Lib.Mem.bytes_at.
    split; [lia |]. split; [rewrite <- Hlen; lia |].
    intros i Hi.
    assert (Hi' : 0 <= Z.of_nat i < B.ACtlCut.c_n cx) by (rewrite Hlen; lia).
    destruct (Hpres (B.ACtlCut.c_p cx + Z.of_nat i) ltac:(lia)) as [Hpr _].
    destruct (w3b_aview_present _ _ _ Hpr) as (b & _ & Hav & Hmrd).
    rewrite Hmrd.
    rewrite (HF2 _ _ (Z.of_nat i) Hin0 Hin3 ltac:(rewrite Hreq; lia)) in Hav.
    2: { rewrite FP_nil. apply lib.Reusable.YI04.inFP_nil. }
    destruct (Hgarr i ltac:(rewrite length_map; exact Hi)) as [Hv Hr].
    specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
    unfold Reusable.YG0n.aview in Hav. rewrite Hv in Hav. cbn [option_map] in Hav. injection Hav as Hbv.
    rewrite (nth_error_nth' (B.ACtlCut.c_in cx) (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. rewrite <- Hbv.
    rewrite (nth_indep (map (fun b0 : byte => bv_unsigned b0) (B.ACtlCut.c_in cx)) 0
               (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; exact Hi).
    rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth i (B.ACtlCut.c_in cx) (Z_to_bv 8 0))) as Hbr.
    change (bv_modulus 8) with 256 in Hbr.
    cbv beta.
    rewrite (w3b_le_byte1 _ Hbr). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   C1-C4, proved once for every stage of this file. *)

(* C1.  The core's configuration at a pc IS ctrl's MState.MS state: YK11.mkst and MState.MS build the same record
   (the FP registers and fcsr from the Section's fx), and YK11.seg_rom / PropExec.seg_rom have one body. *)
Lemma w3b_cfg_MS : forall (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  Reusable.YG0d.cfg_at segs pc regs mem md =
  mkCfg (MST.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
           (PEX.seg_rom B.Img0.rsegs)) md.
Proof. intros pc regs mem md. rewrite <- tfibsegs_rsegs. reflexivity. Qed.

(* C2.  The lift.  The cut's register map is moved to the canonical tree the `_F` runs start from
   (Reusable.YA0nR.SRr_xregs_eqv of Regs6ss.mkR_of_eqv), the footprint run is turned into the kit's fsteps
   (ProgBridge.fevt_of_evtF) and lifted by Reusable.YA0nR.SRr_fsteps at RNG := ProgBridge.RNG_W (w_H W), whose
   fp_avoids is ProgBridge.fp_avoids_RNG_W.  The continuation is handed what the journal step needs: the run's
   post, the hidden bytes (Reusable.YA0nR.fsteps_keeps_hidden) and the growth (mem_grows_fsteps). *)
(* The canonical register tree the `_F` runs start from, written with the core's getr so that its slots can be
   named in a proof (it is Regs6ss.mkR_of up to conversion: getr r = reg_get r for r <> 0). *)
Definition w3b_tree (regs : bvmap 5 word) : bvmap 5 word :=
  FRM.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 3)
    (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 5) (lib.Reusable.YK11.getr regs 6)
    (lib.Reusable.YK11.getr regs 7) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
    (lib.Reusable.YK11.getr regs 10) (lib.Reusable.YK11.getr regs 11) (lib.Reusable.YK11.getr regs 12)
    (lib.Reusable.YK11.getr regs 13) (lib.Reusable.YK11.getr regs 14) (lib.Reusable.YK11.getr regs 15)
    (lib.Reusable.YK11.getr regs 16) (lib.Reusable.YK11.getr regs 17) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    (lib.Reusable.YK11.getr regs 28) (lib.Reusable.YK11.getr regs 29) (lib.Reusable.YK11.getr regs 30)
    (lib.Reusable.YK11.getr regs 31).

Lemma w3b_tree_eqv : forall regs, R6S.xregs_eqv regs (w3b_tree regs).
Proof. intros regs. exact (R6S.mkR_of_eqv regs). Qed.

Lemma w3b_lift : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs (PBR.RNG_W (Reusable.YA0n.w_H W)) P
    (MST.MS (w3b_tree regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
       (PEX.seg_rom B.Img0.rsegs)) ->
  (forall (ms' : machine_state) (md' : Model),
     P ms' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) mem)
       (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms')) ->
     Reusable.YK04.same_but_materialized md md' ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q HEV K.
  rewrite (w3b_cfg_MS pc regs mem md).
  apply (KIT.SRr_xregs_eqv segs W (w3b_tree regs) regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
           lib.Reusable.YK11.fp_csr None mem (PEX.seg_rom B.Img0.rsegs) md Q);
    [| exact (R6S.xregs_eqv_sym regs (w3b_tree regs) (w3b_tree_eqv regs))].
  destruct (FEVT _ _ _ HEV) as (ms' & HRUN & HP).
  apply (KIT.SRr_fsteps segs Hwx W _ ms' md (PBR.RNG_W (Reusable.YA0n.w_H W)) Q HRUN
           (PBR.fp_avoids_RNG_W (Reusable.YA0n.w_H W))).
  intros md' HSBM. apply (K ms' md' HP); [| | exact HSBM].
  - exact (KIT.fsteps_keeps_hidden segs Hwx (Reusable.YA0n.w_H W) (PBR.RNG_W (Reusable.YA0n.w_H W)) _ ms'
             (Reusable.YA0n.w_Hoff W) HRUN (PBR.fp_avoids_RNG_W (Reusable.YA0n.w_H W))).
  - exact (mem_grows_fsteps W (PBR.RNG_W (Reusable.YA0n.w_H W)) _ ms' HRUN).
Qed.

(* C3.  The journal across a stretch whose written bytes are the journal's own (Reusable.YCbq.ajournal_exec; the
   frozen clause is the run's raw munch read through mrestrict). *)
Lemma w3b_journal : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k
    (mem' : word -> option byte) (md' : Model) (Wr : Z -> Prop),
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mem' x = mem3 x) ->
  lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem3)
    (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W3) mem') ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, Wr a -> Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
     (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3 own a) ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem' md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k mem' md' Wr HJ HFRZ HGR HHID HSBM HW.
  eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := Wr);
    [exact HJ | | exact HGR | exact HHID | exact HSBM | exact HW].
  intros x Hx. unfold Reusable.YK04.mrestrict.
  destruct (Reusable.YA0n.w_H W3 x); [reflexivity | exact (HFRZ x Hx)].
Qed.

(* C4 (route (C)).  ctl_rt_C at the SAME ly / S across a stretch whose written ranges are application bytes apart from
   the runtime band, from the shadow band and from the image: asan_cells by lib/B/AsanRTFacts.v's asan_cells_kept,
   both shadow regions by lib/B/ShadowRwOnT.v's shadow_rw_on_kept (the stretch writes no shadow byte: munch_meta),
   ro_agree because the ranges hold no read-only image byte.  The stretches of this piece allocate nothing and push
   or pop no frame, so the successor cut is at the entry's ly3 / S3. *)
Lemma w3b_ctl_rt_C : forall ly (S : Reusable.YG00.astate) (WR : list FRM.ivl) (m m' : word -> option byte),
  B.ACtlRtC.ctl_rt_C B ly S m ->
  FRM.munch WR m m' -> FRM.wmono B.Img0.rsegs m m' ->
  ARF.all_app WR ->
  FRM.disjoint_from WR ART.RT_LO (ART.RT_HI - ART.RT_LO) ->
  (forall a : word, MEM.ro_addr B.Img0.rsegs a = true -> FRM.outside WR (bv_unsigned a)) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S WR m m' (HAC & HSC & HSI & HRO) HMU HWM HAPP HDJ HROUT.
  pose proof (ARF.munch_meta WR m m' HMU HAPP) as HMK.
  split; [exact (ARF.asan_cells_kept WR m m' HAC HMU HDJ) |].
  split; [exact (B.ShadowRwOnT.shadow_rw_on_kept _ m m' HSC HMK HWM) |].
  split; [exact (B.ShadowRwOnT.shadow_rw_on_kept _ m m' HSI HMK HWM) |].
  intros a Ha. unfold MEM.mrd. rewrite (HMU a (HROUT a Ha)). exact (HRO a Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The readers of a cut body across a stretch's write set.  `kept_on WR lo n` is "the stretch wrote no byte of
   [lo, lo + n)"; under it ctrl's byte readers (lib/B/ACtlCutP.v's q64 / b8 / spill, over lib/Lib's bytes_at)
   and AsanRT's addressable move to the end memory.  Nothing here is new vocabulary: each is the kept half of a
   reader the cut bodies already name. *)
Definition kept_on (WR : list FRM.ivl) (lo n : Z) : Prop := forall q, lo <= q < lo + n -> FRM.outside WR q.

Lemma kept_on_sub : forall WR lo n lo' n', kept_on WR lo n -> lo <= lo' -> 0 <= n' -> lo' + n' <= lo + n ->
  kept_on WR lo' n'.
Proof. intros WR lo n lo' n' H A C D q Hq. apply H. lia. Qed.

Lemma bytes_at_kept : forall WR m m' a bs,
  FRM.munch WR m m' -> MEM.bytes_at B.Img0.rsegs m a bs ->
  kept_on WR a (Z.of_nat (length bs)) -> MEM.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros WR m m' a bs HMU (HA & HL & H) HK.
  split; [exact HA |]. split; [exact HL |]. intros i Hi.
  rewrite <- (H i Hi). unfold MEM.mrd.
  rewrite (HMU (MEM.wa (a + Z.of_nat i))); [reflexivity |].
  rewrite MEM.wa_unsigned by lia. apply HK. lia.
Qed.

Lemma le8_len : forall w : word, Z.of_nat (length (MEM.le8 w)) = 8.
Proof. intros w. reflexivity. Qed.

Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma le4_len : forall w : word, Z.of_nat (length (MEM.le4 w)) = 4.
Proof. intros w. reflexivity. Qed.

Lemma our_len : forall inp, Z.of_nat (length (SMD.OUR inp)) = 6.
Proof. intros inp. reflexivity. Qed.

Lemma id0_len : Z.of_nat (length RIM.ID0) = 38.
Proof. reflexivity. Qed.

Lemma z72_len : Z.of_nat (length SMD.z72) = 72.
Proof. reflexivity. Qed.

Lemma fsbody0_len : forall inp, Z.of_nat (length (SMD.fs_body (SMD.fst_at inp 0))) = 0.
Proof. intros inp. reflexivity. Qed.

Lemma saved_len : forall cx, Z.of_nat (length (B.ACtlCutP.saved_bytes cx)) = 104.
Proof. intros cx. reflexivity. Qed.

Lemma q64_kept : forall WR m m' a v,
  FRM.munch WR m m' -> B.ACtlCutP.q64 m a v -> kept_on WR a 8 -> B.ACtlCutP.q64 m' a v.
Proof.
  intros WR m m' a v HMU H HK. unfold B.ACtlCutP.q64 in *. rewrite tfibsegs_rsegs in H |- *.
  apply (bytes_at_kept WR m m' a _ HMU H). rewrite le8_len. exact HK.
Qed.

Lemma b8_kept : forall WR m m' a v,
  FRM.munch WR m m' -> B.ACtlCutP.b8 m a v -> kept_on WR a 1 -> B.ACtlCutP.b8 m' a v.
Proof.
  intros WR m m' a v HMU H HK. unfold B.ACtlCutP.b8 in *. rewrite tfibsegs_rsegs in H |- *.
  apply (bytes_at_kept WR m m' a _ HMU H). cbn [length]. exact HK.
Qed.

(* ctrl's `spill` hides its own base in an existential (lib/B/ACtlCutP.v:449); at a cut FRAC already pins the base
   to A, and the reader's own bounds force the two to agree, so a spill is read at A and rebuilt at A. *)
Lemma spill_at : forall (regs : bvmap 5 word) m off v A,
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  B.ACtlCutP.spill regs m off v -> B.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HA HA0 HA64 Ho0 Ho8 (A0 & HA0' & HQ).
  assert (EA : A0 = A).
  { unfold B.ACtlCut.rgv in HA, HA0'. rewrite HA in HA0'.
    pose proof (f_equal bv_unsigned HA0') as E.
    rewrite !MST.unsigned_lit_wrap in E.
    destruct HQ as (Hlo & Hhi & _).
    rewrite le8_len in Hhi. Z.div_mod_to_equations. lia. }
  rewrite EA in HQ. exact HQ.
Qed.

Lemma spill_mk : forall (regs : bvmap 5 word) m off v A,
  B.ACtlCut.rgv regs 9 A -> B.ACtlCutP.q64 m (A + off) v -> B.ACtlCutP.spill regs m off v.
Proof. intros regs m off v A HA HQ. exists A. split; [exact HA | exact HQ]. Qed.

(* addressable moves on the shadow bytes alone (lib/B/AsanRT.v addr_byte), so lib/B/AsanRTFacts.v's
   addressable_kept under a meta_kept is all a stage needs for it. *)
Lemma addressable_kept : forall WR m m' p n,
  FRM.munch WR m m' -> ARF.all_app WR -> ART.addressable m p n -> ART.addressable m' p n.
Proof. intros WR m m' p n HMU HAP H. exact (ARF.addressable_kept m m' p n H (ARF.munch_meta WR m m' HMU HAP)). Qed.

(* ---------------------------------------------------------------------------------------------------------
   The cut bodies' bundles across a stretch's write set.  Each takes the register equalities the bundle reads and
   one `kept_on` per range it reads: the frame header [fr, fr + 24), the frame shadow [Sfr fr, + 392), the
   record area [fr + 2624, + 416), the spill area [A, A + 448) and the saved registers [c_sp cx - 104, + 104). *)

Lemma ourb_kept : forall cx fr m m' WR,
  FRM.munch WR m m' -> B.ACtlCutP.OURb cx fr m -> kept_on WR (fr + 2624) 6 ->
  B.ACtlCutP.OURb cx fr m'.
Proof.
  intros cx fr m m' WR HMU H HK. unfold B.ACtlCutP.OURb in *.
  rewrite tfibsegs_rsegs in H |- *.
  apply (bytes_at_kept WR m m' _ _ HMU H). rewrite our_len. exact HK.
Qed.

Lemma pro_kept : forall fr (regs regs' : bvmap 5 word) m m' WR A,
  FRM.munch WR m m' -> ARF.all_app WR -> B.ACtlCutP.PRO fr regs m ->
  B.ACtlCut.rgv regs 9 A -> B.ACtlCut.rgv regs' 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  kept_on WR A 448 ->
  B.ACtlCutP.PRO fr regs' m'.
Proof.
  intros fr regs regs' m m' WR A HMU HAP HPRO HA HA' HA0 HA64 HK.
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 -> B.ACtlCutP.spill regs m off v ->
                 B.ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho8 HS.
    apply (spill_mk regs' m' off v A HA').
    apply (q64_kept WR m m' (A + off) v HMU (spill_at regs m off v A HA HA0 HA64 Ho0 Ho8 HS)).
    eapply kept_on_sub; [exact HK | lia | lia | lia]. }
  destruct HPRO as ((P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11) & Q1 & Q2 & Q3 & Q4).
  split; [repeat split; solve [apply SP; [lia | lia | assumption]] |].
  split; [apply SP; [lia | lia | exact Q1] |].
  split; [apply SP; [lia | lia | exact Q2] |].
  split; [exact (addressable_kept WR m m' _ _ HMU HAP Q3) |].
  apply SP; [lia | lia | exact Q4].
Qed.

Lemma pl0_kept : forall cx fr (regs regs' : bvmap 5 word) m m' WR A,
  FRM.munch WR m m' -> ARF.all_app WR -> B.ACtlCutP.PL0 cx fr regs m ->
  B.ACtlCut.rgv regs 9 A -> B.ACtlCut.rgv regs' 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  kept_on WR A 448 -> kept_on WR (fr + 2624) 416 ->
  B.ACtlCutP.PL0 cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' WR A HMU HAP HPL HA HA' HA0 HA64 H23 H25 HK HKF.
  assert (SP : forall off v, 0 <= off -> off + 8 <= 448 -> B.ACtlCutP.spill regs m off v ->
                 B.ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho8 HS.
    apply (spill_mk regs' m' off v A HA').
    apply (q64_kept WR m m' (A + off) v HMU (spill_at regs m off v A HA HA0 HA64 Ho0 Ho8 HS)).
    eapply kept_on_sub; [exact HK | lia | lia | lia]. }
  destruct HPL as ((C1 & C2 & C3) & HID & HFG & (R1 & R2 & R3) & S176 & S208 & (F1 & F2 & F3 & F4 & F5)).
  split.
  { split; [exact C1 |]. split; [unfold B.ACtlCut.rgv in C2 |- *; rewrite H23; exact C2 |].
    unfold B.ACtlCut.rgv in C3 |- *; rewrite H25; exact C3. }
  split.
  { unfold B.ACtlCutP.IDBe in HID |- *. rewrite tfibsegs_rsegs in HID |- *.
    apply (bytes_at_kept WR m m' _ _ HMU HID).
    rewrite id0_len. eapply kept_on_sub; [exact HKF | lia | lia | lia]. }
  split.
  { unfold B.ACtlCutP.FGBe in HFG |- *. rewrite tfibsegs_rsegs in HFG |- *.
    apply (bytes_at_kept WR m m' _ _ HMU HFG).
    rewrite z72_len. eapply kept_on_sub; [exact HKF | lia | lia | lia]. }
  split.
  { split; [exact (addressable_kept WR m m' _ _ HMU HAP R1) |].
    split; [exact (addressable_kept WR m m' _ _ HMU HAP R2) |].
    exact (addressable_kept WR m m' _ _ HMU HAP R3). }
  split; [apply SP; [lia | lia | exact S176] |].
  split; [apply SP; [lia | lia | exact S208] |].
  split.
  { unfold B.ACtlCutP.u32 in F1 |- *. rewrite tfibsegs_rsegs in F1 |- *.
    apply (bytes_at_kept WR m m' _ _ HMU F1).
    rewrite le4_len. eapply kept_on_sub; [exact HKF | lia | lia | lia]. }
  split; [exact (b8_kept WR m m' _ _ HMU F2 ltac:(eapply kept_on_sub; [exact HKF | lia | lia | lia])) |].
  split.
  { rewrite tfibsegs_rsegs in F3 |- *. apply (bytes_at_kept WR m m' _ _ HMU F3).
    rewrite fsbody0_len. eapply kept_on_sub; [exact HKF | lia | lia | lia]. }
  split; [exact (addressable_kept WR m m' _ _ HMU HAP F4) | exact F5].
Qed.

Lemma frac_kept : forall cx fr sel (regs regs' : bvmap 5 word) m m' WR A,
  FRM.munch WR m m' -> B.ACtlCutP.FRAC B cx fr sel regs m ->
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  kept_on WR fr 24 -> kept_on WR (B.ACtlCutP.Sfr fr) 392 ->
  kept_on WR (A + 40) 304 -> kept_on WR (B.ACtlCut.c_sp cx - 104) 104 ->
  kept_on WR (fr + 4088) 8 ->
  B.ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' WR A HMU HF HA9 HA0 HA64 H2 H3 H4 H8 H9 H19 H26 KH KS KA KV KT.
  destruct HF as (A1 & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    H336 & H48 & H40 & Hhdr & Hent & (sh & HSH & HSHl) & HSAV & HTRL).
  assert (EA : A1 = A).
  { unfold B.ACtlCut.rgv in E9, HA9. rewrite HA9 in E9.
    pose proof (f_equal bv_unsigned E9) as E. rewrite !MST.unsigned_lit_wrap in E.
    destruct H40 as (Hlo & Hhi & _). rewrite le8_len in Hhi.
    destruct H336 as (Hlo' & Hhi' & _). rewrite le8_len in Hhi'.
    Z.div_mod_to_equations. lia. }
  rewrite EA in E9, H336, H48, H40, HAmod, HAle, HspA, HfrA, HA448.
  exists A, spv.
  split; [rewrite H2; exact E2 |]. split; [exact Emod |].
  split; [unfold Reusable.YG0d.spZ in EspZ |- *; rewrite H2; exact EspZ |].
  split; [rewrite H4; exact E4 |].
  split; [unfold B.ACtlCut.rgv in E8 |- *; rewrite H8; exact E8 |].
  split; [unfold B.ACtlCut.rgv in E9 |- *; rewrite H9; exact E9 |].
  split; [rewrite H3; exact E3 |].
  split; [unfold B.ACtlCut.rgv in E19 |- *; rewrite H19; exact E19 |].
  split; [unfold B.ACtlCut.rgv in E26 |- *; rewrite H26; exact E26 |].
  split; [exact Hfrmod |]. split; [exact HAmod |]. split; [exact HAle |]. split; [exact HspA |].
  split; [exact HfrA |]. split; [exact HA448 |]. split; [exact Hsp4096 |]. split; [exact HspAPP |].
  split; [exact (q64_kept WR m m' _ _ HMU H336 ltac:(eapply kept_on_sub; [exact KA | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU H48 ltac:(eapply kept_on_sub; [exact KA | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU H40 ltac:(eapply kept_on_sub; [exact KA | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU Hhdr ltac:(eapply kept_on_sub; [exact KH | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU Hent ltac:(eapply kept_on_sub; [exact KH | lia | lia | lia])) |].
  split.
  { exists sh. split; [| exact HSHl].
    rewrite tfibsegs_rsegs in HSH |- *. apply (bytes_at_kept WR m m' _ _ HMU HSH).
    rewrite HSHl. unfold B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES.
    eapply kept_on_sub; [exact KS | lia | lia | cbn; lia]. }
  split.
  { rewrite tfibsegs_rsegs in HSAV |- *. apply (bytes_at_kept WR m m' _ _ HMU HSAV).
    rewrite saved_len. eapply kept_on_sub; [exact KV | lia | lia | lia]. }
  exact (q64_kept WR m m' _ _ HMU HTRL ltac:(eapply kept_on_sub; [exact KT | lia | lia | lia])).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The journal's own window and the placement facts every stage of this file reads from it. *)

(* The journal's presence clause, at the walk's stack window [c_sp cx - LLVMF_STK, c_sp cx). *)
Lemma w3b_win_present : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k a,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < B.ACtlCut.c_sp cx ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k a HJ Ha.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact (HP a Ha).
Qed.

(* astk_ok, the journal's stack law at the entry layout. *)
Lemma w3b_astk : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  Reusable.YCbq.astk_ok Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_ly cx) (B.ACtlCut.c_sp cx).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _). exact HS.
Qed.

(* The window lies in the high application band: above the ASan shadow, below APPMEM_END.  From astk_ok
   (alloc_ceiling <= ly_stk_lo, ly_stk_lo + STK <= sp0, sp0 <= ly_stk_hi <= 2 ^ 47) and the core's constants
   (Reusable.YCbq.asan_consts: 0x7fff7f800000 <= alloc_ceiling). *)
Lemma w3b_win_band : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  ART.HIGHMEM_BEG <= B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK /\
  B.ACtlCut.c_sp cx <= ART.APPMEM_END /\ B.ACtlCut.c_sp cx mod 16 = 0.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  destruct (w3b_astk cx own ly3 S3 W3 mem3 md3 k HJ)
    as (Hmod & Hstk0 & Hceil & Hlo & Hhi & Htop & _ & _ & _).
  pose proof (proj1 Reusable.YCbq.asan_consts) as HAC.
  unfold ART.HIGHMEM_BEG, ART.APPMEM_END, Reusable.YCfn.LLVMF_STK in *.
  split; [lia |]. split; [lia | exact Hmod].
Qed.

(* The own class-6 frame's placement (gap of own6_frame, whose bound is alloc_ceiling only): the core's
   AR_frames_law (in_app, under LAWS) puts it in the LOW application band below the low shadow, or in the HIGH band
   below ASAN_CEIL = alloc_ceiling; astk_ok (alloc_ceiling <= ly_stk_lo, ly_stk_lo + LLVMF_STK <= c_sp) puts the
   window above alloc_ceiling.  So the frame and its shadow lie below the window, the frame misses the shadow band,
   and the frame and its shadow are apart (low band: the shadow above the frame; high band: below it). *)
Lemma w3b_own6_place : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k fr,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) ->
  fr + 4096 <= B.ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK /\
  ART.LOWMEM_END <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= ART.HIGHMEM_BEG /\
  ((4096 <= fr /\ fr + 4096 <= ART.LOWMEM_END /\ fr + 4096 <= ART.shadow_addr fr) \/
   (ART.HIGHMEM_BEG <= fr /\ fr + 4096 <= ART.APPMEM_END /\ ART.shadow_addr fr + 512 <= fr)).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k fr HJ Hin Efr.
  pose proof HJ as (HAR & _).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Happ & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ. rewrite <- Efr in Happ.
  destruct (w3b_astk cx own ly3 S3 W3 mem3 md3 k HJ) as (_ & _ & Hceil & Hlo & _).
  pose proof (proj1 Reusable.YCbq.asan_consts) as HAC.
  clear - Happ Hceil Hlo HAC.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ.
  unfold ART.shadow_addr, ART.ASAN_K, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
  unfold Reusable.YCfn.LLVMF_STK in Hlo |- *.
  Z.div_mod_to_equations. lia.
Qed.

(* lib/Lib's stk over a present range: the journal's apresent gives the byte itself, hence both the writable view
   and the read. *)
Lemma w3b_stk_of_present : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m a) ->
  FRM.stk B.Img0.rsegs m lo hi.
Proof.
  intros W m lo hi Hlo Hhi HP. split; [exact Hlo |]. split; [exact Hhi |].
  intros a Ha. destruct (HP a Ha) as (_ & b & Hb). unfold MEM.wa.
  split; [unfold wview; rewrite Hb; discriminate | exists b; unfold MEM.mrd; rewrite Hb; reflexivity].
Qed.

(* lib/Lib's wr_at over a present range (the byte is materialized, so the writable view is not None). *)
Lemma w3b_wr_of_present : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m x) ->
  MEM.wr_at B.Img0.rsegs m a n.
Proof.
  intros W m a n Ha Hn HP. split; [exact Ha |]. split; [exact Hn |].
  intros i Hi. destruct (HP (a + i) ltac:(lia)) as (_ & b & Hb). unfold MEM.wa.
  unfold wview. rewrite Hb. discriminate.
Qed.

(* ProgBridge.rng_of_visible over a present range: apresent says the world hides none of it. *)
Lemma w3b_rng_of_present : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) lo n,
  0 <= lo -> lo + n <= 2 ^ 64 ->
  (forall a, lo <= a < lo + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m a) ->
  Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W)) lo n.
Proof.
  intros W m lo n Hlo Hhi HP. apply PBR.rng_of_visible.
  split; [exact Hlo |]. split; [exact Hhi |].
  intros a Ha. exact (proj1 (HP a Ha)).
Qed.

(* The image hull is one footprint range of RNG_W (ProgBridge.img_vis_W), and so is every sub-range of it. *)
Lemma w3b_rng_img : forall (W : Reusable.YA0n.world segs) lo n,
  Reusable.YImgTop.IMG_LO <= lo -> 0 <= n -> lo + n <= Reusable.YImgTop.IMG_TOP ->
  Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W)) lo n.
Proof.
  intros W lo n Hlo Hn Hhi. apply PBR.rng_of_visible.
  destruct (img_vis_W W) as (H1 & H2 & H3).
  split; [lia |]. split; [lia |]. intros a Ha. apply H3. lia.
Qed.

(* A read-only address of this image is an image address (lib/Lib/Mem.v ro_addr through the core's
   Reusable.YK1j segment spec and ProgBridge.rsegs_spans). *)
Lemma w3b_ro_img : forall a : word, MEM.ro_addr B.Img0.rsegs a = true ->
  Reusable.YImgTop.IMG_LO <= bv_unsigned a < Reusable.YImgTop.IMG_TOP.
Proof.
  intros a Ha. unfold MEM.ro_addr in Ha.
  destruct (find_segment B.Img0.rsegs (bv_unsigned a) 1) as [sg|] eqn:E; [| discriminate].
  pose proof (lib.Reusable.YK1j.find_segment_in B.Img0.rsegs (bv_unsigned a) 1 sg E) as Hin.
  pose proof (lib.Reusable.YK1j.find_segment_range B.Img0.rsegs (bv_unsigned a) 1 sg E) as (H1 & H2).
  assert (HM : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by (exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s)))
                 B.Img0.rsegs sg Hin)).
  rewrite PBR.rsegs_spans in HM.
  cbn [In] in HM.
  destruct HM as [E1 | [E1 | [E1 | [E1 | []]]]]; injection E1 as Eb Es; lia.
Qed.

(* No address at or above the image top is read-only (w3b_ro_img read backwards). *)
Lemma w3b_ro_off_img : forall a, Reusable.YImgTop.IMG_TOP <= a < 2 ^ 64 ->
  MEM.ro_addr B.Img0.rsegs (MEM.wa a) = false.
Proof.
  intros a Ha. destruct (MEM.ro_addr B.Img0.rsegs (MEM.wa a)) eqn:E; [| reflexivity].
  pose proof (w3b_ro_img _ E) as Hi. rewrite MEM.wa_unsigned in Hi by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Readers for S_P12, whose prologue WRITES four spill ranges and sixteen bytes of the own frame's shadow (P12.p12_W):
   the bundle transports above take a write set that misses the spill area and the shadow, so P12 moves each
   reader by the kept_on of its own bytes (or of its own shadow bytes, for addressable). *)

(* addressable moves when its own shadow bytes are not written (lib/B/AsanRT.v addr_byte reads only those). *)
Lemma addressable_kept_on : forall WR m m' p n,
  FRM.munch WR m m' -> ART.addressable m p n ->
  (forall i, 0 <= i < n -> FRM.outside WR (ART.shadow_addr (p + i))) ->
  ART.addressable m' p n.
Proof.
  intros WR m m' p n HMU (H1 & H2 & H3 & H) HK. split; [lia |]. split; [lia |]. split; [lia |].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha |]. exists b. split; [| exact Hok].
  rewrite <- Hb. unfold MEM.mrd. rewrite (HMU (MEM.wa (ART.shadow_addr (p + i)))); [reflexivity |].
  assert (Hd : 0 <= (p + i) / 8 <= p + i) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite MEM.wa_unsigned; [exact (HK i Hi) |].
  unfold ART.shadow_addr, ART.ASAN_K, ART.APPMEM_END in *. lia.
Qed.

(* apresent moves at a byte the stretch did not write. *)
Lemma apresent_kept : forall WR (H : word -> bool) m m' a,
  FRM.munch WR m m' -> 0 <= a < 2 ^ 64 -> FRM.outside WR a ->
  Reusable.YG0n.apresent H m a -> Reusable.YG0n.apresent H m' a.
Proof.
  intros WR H m m' a HMU Ha HO (Hh & b & Hb). split; [exact Hh |]. exists b.
  rewrite (HMU (Z_to_bv 64 a)); [exact Hb |]. rewrite MST.unsigned_lit by lia. exact HO.
Qed.

(* A range all of whose bytes are readable holds SOME byte list: the bytes the memory reads there. *)
Lemma w3b_bytes_of_readable : forall (m : word -> option byte) (n : nat) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, MEM.mrd B.Img0.rsegs m (MEM.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, MEM.bytes_at B.Img0.rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [| n IH]; intros a Ha Hn HR.
  - exists []. split; [| reflexivity]. split; [exact Ha |]. split; [cbn; lia |]. intros i Hi. cbn in Hi. lia.
  - destruct (HR 0%nat ltac:(lia)) as (b & Hb). rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & HB & HL).
    { intros i Hi. destruct (HR (S i) ltac:(lia)) as (b' & Hb'). exists b'.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb'. }
    exists (b :: bs). split; [| cbn; rewrite HL; reflexivity].
    apply (proj2 (MEM.bytes_at_app B.Img0.rsegs m a [b] bs)). split.
    + split; [exact Ha |]. split; [cbn; lia |]. intros i Hi. cbn in Hi.
      assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r. exact Hb.
    + cbn [length Z.of_nat Pos.of_succ_nat]. replace (a + 1) with (a + Z.of_nat 1) in HB by reflexivity. exact HB.
Qed.

(* A present range is a writable cell of its own current bytes (lib/Lib/Step.v rw_cells over one CB cell). *)
Lemma w3b_rw_of_present : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) (n : nat) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) m x) ->
  exists bs, STP.rw_cells B.Img0.rsegs m a [CEL.CB n bs].
Proof.
  intros W m n a Ha Hn HP.
  destruct (w3b_bytes_of_readable m n a Ha Hn) as (bs & HB & HL).
  { intros i Hi. destruct (HP (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb). exists b.
    unfold MEM.mrd, MEM.wa. rewrite Hb. reflexivity. }
  exists bs. split.
  - split; [cbn; split; [exact HL | exact I] |]. cbn [CEL.cells_bytes CEL.cbytes]. rewrite app_nil_r. exact HB.
  - cbn [CEL.cells_size CEL.csize]. rewrite Nat.add_0_r. exact (w3b_wr_of_present W m a (Z.of_nat n) Ha Hn HP).
Qed.

(* The shadow byte of a frame offset: with fr 8-aligned, shadow_addr (fr + c) = shadow_addr fr + c / 8. *)
Lemma sh_off : forall fr c, fr mod 8 = 0 -> 0 <= c -> ART.shadow_addr (fr + c) = ART.shadow_addr fr + c / 8.
Proof.
  intros fr c Hm Hc. unfold ART.shadow_addr.
  assert (E : fr = fr / 8 * 8) by (rewrite (Z.div_mod fr 8) at 1 by lia; lia).
  rewrite E at 1. replace (fr / 8 * 8 + c) with (c + fr / 8 * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* FRAC across a write set that may hit the frame shadow: as frac_kept, with the shadow conjunct supplied for the
   end memory and each spill word kept on its own 8 bytes. *)
Lemma frac_kept_sh : forall cx fr sel (regs regs' : bvmap 5 word) m m' WR A,
  FRM.munch WR m m' -> B.ACtlCutP.FRAC B cx fr sel regs m ->
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  kept_on WR fr 24 ->
  (exists sh, MEM.bytes_at segs m' (B.ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat B.ACtlCutP.FRAME_SHADOW) ->
  kept_on WR (A + 40) 16 -> kept_on WR (A + 336) 8 -> kept_on WR (B.ACtlCut.c_sp cx - 104) 104 ->
  kept_on WR (fr + 4088) 8 ->
  B.ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' WR A HMU HF HA9 HA0 HA64 H2 H3 H4 H8 H9 H19 H26 KH SH KA KB KV KT.
  destruct HF as (A1 & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    H336 & H48 & H40 & Hhdr & Hent & _ & HSAV & HTRL).
  assert (EA : A1 = A).
  { unfold B.ACtlCut.rgv in E9, HA9. rewrite HA9 in E9.
    pose proof (f_equal bv_unsigned E9) as E. rewrite !MST.unsigned_lit_wrap in E.
    destruct H40 as (Hlo & Hhi & _). rewrite le8_len in Hhi.
    destruct H336 as (Hlo' & Hhi' & _). rewrite le8_len in Hhi'.
    Z.div_mod_to_equations. lia. }
  rewrite EA in E9, H336, H48, H40, HAmod, HAle, HspA, HfrA, HA448.
  exists A, spv.
  split; [rewrite H2; exact E2 |]. split; [exact Emod |].
  split; [unfold Reusable.YG0d.spZ in EspZ |- *; rewrite H2; exact EspZ |].
  split; [rewrite H4; exact E4 |].
  split; [unfold B.ACtlCut.rgv in E8 |- *; rewrite H8; exact E8 |].
  split; [unfold B.ACtlCut.rgv in E9 |- *; rewrite H9; exact E9 |].
  split; [rewrite H3; exact E3 |].
  split; [unfold B.ACtlCut.rgv in E19 |- *; rewrite H19; exact E19 |].
  split; [unfold B.ACtlCut.rgv in E26 |- *; rewrite H26; exact E26 |].
  split; [exact Hfrmod |]. split; [exact HAmod |]. split; [exact HAle |]. split; [exact HspA |].
  split; [exact HfrA |]. split; [exact HA448 |]. split; [exact Hsp4096 |]. split; [exact HspAPP |].
  split; [exact (q64_kept WR m m' _ _ HMU H336 KB) |].
  split; [exact (q64_kept WR m m' _ _ HMU H48 ltac:(eapply kept_on_sub; [exact KA | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU H40 ltac:(eapply kept_on_sub; [exact KA | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU Hhdr ltac:(eapply kept_on_sub; [exact KH | lia | lia | lia])) |].
  split; [exact (q64_kept WR m m' _ _ HMU Hent ltac:(eapply kept_on_sub; [exact KH | lia | lia | lia])) |].
  split; [exact SH |].
  split.
  { rewrite tfibsegs_rsegs in HSAV |- *. apply (bytes_at_kept WR m m' _ _ HMU HSAV).
    rewrite saved_len. eapply kept_on_sub; [exact KV | lia | lia | lia]. }
  exact (q64_kept WR m m' _ _ HMU HTRL ltac:(eapply kept_on_sub; [exact KT | lia | lia | lia])).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81d80 (0x81d80, own6, k <= 14) --S_P7--> B81da8 (0x81da8, own6, k <= 14).  Seg/P7.v seg_P7 :124.
   li s2,-1, beq a0,s2 (taken), ld a0,208(s1) (f), li a1,0, li a2,0, ld a3,88(s1), ld a4,80(s1), ld a5,72(s1),
   jal reac_ctrl_identity_fragment (fr = a1 = 0: fg_class = FgRefuse, Seg/P7.v:29-30), return at 0x81da8.
   ROUTE (C): the callee is cited in its region form RFG.reac_ctrl_identity_fragment_contract_F_on (Section
   hypothesis reac_ctrl_identity_fragment_holds_F_on).  At this call the callee reads and writes neither buffer
   (fr = 0, len = 0: every buffer premise and the region R are guarded by fr <> 0), so its shadow premise is
   vacuous. *)
Lemma seg_P7 : forall POST, CF POST C_B81da8 -> CF POST C_B81d80.
Proof.
  (* C0: ctl_from's premises, then the body of C_B81d80 (ACtlCutP.v:1611-1623). *)
  intros POST HDA8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HA0 & HPRO & (v208 & S208) & (v88 & S88) & (v80 & S80) &
                     (v72 & S72) & H64 & H24 & HC1 & HKN & HPL0).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & QSH & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  pose proof HJ as (HAR & _).
  pose proof HRT as (HAC & _ & _ & HRO).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  (* the own frame's placement, in low or in high application memory (w3b_own6_place): the frame and its shadow lie
     below the window *)
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & _).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hdiv : 0 <= fr / 8 <= fr)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSf : 0 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr; lia).
  unfold Reusable.YG0d.spZ in EspZ.
  assert (HspU : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv) by exact EspZ.
  (* the four spilled record pointers, read at FRAC's base A; their values are taken mod 2 ^ 64 (the word they
     name is the same), which is the callee's bound premise. *)
  pose proof (spill_at regs3 mem3 208 v208 A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S208) as Q208.
  pose proof (spill_at regs3 mem3 88 v88 A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S88) as Q88.
  pose proof (spill_at regs3 mem3 80 v80 A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S80) as Q80.
  pose proof (spill_at regs3 mem3 72 v72 A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72) as Q72.
  pose proof (Z.mod_pos_bound v208 (2 ^ 64) ltac:(lia)) as Bf.
  pose proof (Z.mod_pos_bound v88 (2 ^ 64) ltac:(lia)) as Bpa.
  pose proof (Z.mod_pos_bound v80 (2 ^ 64) ltac:(lia)) as Bpp.
  pose proof (Z.mod_pos_bound v72 (2 ^ 64) ltac:(lia)) as Bpn.
  assert (HWA : forall a, A <= a < A + 448 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (RA : forall off, 0 <= off -> off + 8 <= 448 ->
                 lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (A + off) 8).
  { intros off H1 H2. apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWA; lia]. }
  (* the callee's window [sp - 4672, sp) (REAC_CTRL_IDENTITY_FRAGMENT_K) inside the journal's window. *)
  assert (HWP : forall a, spv - 4672 <= a < spv -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HSTK : FRM.stk B.Img0.rsegs mem3 (spv - 4672) spv)
    by (apply (w3b_stk_of_present W3 mem3); [lia | lia | exact HWP]).
  assert (HRNG : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 4672) 4672)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWP; lia]).
  assert (HRNGI : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) IMB.IMG_LO (IMB.IMG_HI - IMB.IMG_LO))
    by (apply w3b_rng_img; unfold IMB.IMG_LO, IMB.IMG_HI; lia).
  assert (HSWR : RAS.sh_word_rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 4672) 4672).
  { unfold RAS.sh_word_rng. right. apply PBR.rng_of_visible.
    exact (win_shadow_vis cx _ ly3 S3 W3 mem3 md3 k (spv - 4672) 4672 HJ
             ltac:(rewrite HLS; lia) ltac:(lia) ltac:(lia)). }
  destruct (ctl_bcmp_cells cx _ ly3 S3 W3 mem3 md3 k HB HJ) as (CB1 & CB2 & CB3 & CB4 & CB5).
  (* The fragment contract asks lib/Lib's mem_inv, which mem3 does not have (it holds the loaded image's read-only
     bytes).  The callee runs on n3 := MemNorm.normalize rsegs mem3 (mem_inv by MemNorm.mem_inv_normalize) and the
     run comes back to mem3 by MemNormF.evtF_normalize_ro under ctl_rt_C's ro_agree (HRO).  Its memory premises move to
     n3 (the window and the shadow band lie above the image, so none of their bytes is read-only); its post comes
     back to mem3 through MemNorm.ms_rel (munch_rel, wmono_rel, and stk by wview_rel_rw / mrd_rel). *)
  assert (HRON : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact HRO.
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 HRON) as HRL.
  assert (HspHB : ART.HIGHMEM_BEG <= spv - 4672) by (unfold ART.HIGHMEM_BEG; lia).
  assert (HspAE : spv <= ART.APPMEM_END) by (unfold ART.APPMEM_END; lia).
  assert (HSTKN : FRM.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (spv - 4672) spv).
  { destruct HSTK as (T1 & T2 & T3). split; [exact T1 |]. split; [exact T2 |].
    intros a Ha. destruct (T3 a Ha) as (Hw & b & Hb).
    assert (Hr : MEM.ro_addr B.Img0.rsegs (MEM.wa a) = false).
    { apply w3b_ro_off_img. unfold ART.HIGHMEM_BEG, ART.APPMEM_END in HspHB, HspAE. lia. }
    split.
    - rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs mem3 _ _ HRL Hr). exact Hw.
    - exists b. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs mem3 _ _ HRL). exact Hb. }
  assert (HACN : ART.asan_cells (B.MemNorm.normalize B.Img0.rsegs mem3)).
  { clear - HRON HAC. unfold B.ACtlK.asan_cells_at, ART.asan_cells in *.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    repeat match goal with |- _ /\ _ => split end.
    all: apply (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON); assumption. }
  (* a state that MemNorm.ms_rel relates to an MS state is that MS state with its own memory *)
  assert (HMS : forall s R F pc fc rv m0 ro,
            B.MemNorm.ms_rel B.Img0.rsegs s (MST.MS R F pc fc rv m0 ro) ->
            s = MST.MS R F pc fc rv (ms_mem s) ro /\ B.MemNorm.mem_rel B.Img0.rsegs (ms_mem s) m0).
  { intros s R F pc fc rv m0 ro (Er1 & Er2 & Er3 & Er4 & Er5 & Er6 & Er7 & Er8). split; [| exact Er8].
    destruct s as [z_r1 z_r2 z_r3 z_r4 z_r5 z_r6 z_r7 z_r8].
    cbn in Er1, Er2, Er3, Er4, Er5, Er6, Er7 |- *.
    subst z_r1 z_r2 z_r3 z_r4 z_r5 z_r6 z_r8. reflexivity. }
  assert (KALL : forall lo n, 0 <= n -> (lo + n <= spv - 4672 \/ spv <= lo) ->
                   kept_on ((spv - 4672, spv) :: nil) lo n).
  { intros lo n Hn Hd q Hq. cbn. split; [lia | exact I]. }
  assert (HALLAPP : ARF.all_app ((spv - 4672, spv) :: nil)).
  { cbn. split; [| exact I]. intros a Ha.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  pose proof reac_ctrl_identity_fragment_holds_F_on as HFG.
  unfold RFG.reac_ctrl_identity_fragment_contract_F_on, RFG.REAC_CTRL_IDENTITY_FRAGMENT,
    RFG.REAC_CTRL_IDENTITY_FRAGMENT_K in HFG.
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P7F.p7_pre_F: 0x81d80 -> 0x859e4 with ra = 0x81da8.  li s2,-1 and a0 = -1 take the beq at 0x81d84
          (sink branch 0x81d88 not taken); a0 := f, a1 := a2 := 0, a3 / a4 / a5 := pa / pp / pn. *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P7F.p7_pre_F with (Ab := A) (f := v208 mod 2 ^ 64) (pa := v88 mod 2 ^ 64)
                                (pp := v80 mod 2 ^ 64) (pn := v72 mod 2 ^ 64).
      - exact E9.
      - exact HA0.
      - exact Bf.
      - exact Bpa.
      - exact Bpp.
      - exact Bpn.
      - lia.
      - lia.
      - rewrite zbv_mod. exact (ARF.ro_c8 _ _ _ Q208).
      - rewrite zbv_mod. exact (ARF.ro_c8 _ _ _ Q88).
      - rewrite zbv_mod. exact (ARF.ro_c8 _ _ _ Q80).
      - rewrite zbv_mod. exact (ARF.ro_c8 _ _ _ Q72).
      - apply RA; lia.
      - apply RA; lia.
      - apply RA; lia.
      - apply RA; lia. }
    intros ms1 ->.
    (* 2. reac_ctrl_identity_fragment at fr = 0, len = 0 (fg_class = FgRefuse, P7.p7_refuse0): every buffer
          premise is guarded by fr <> 0 and so vacuous; window [sp - 4672, sp).  On n3, back to mem3 (above). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply (B.MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mem3 _ HRON).
      eapply HFG with (f := v208 mod 2 ^ 64) (fr := 0) (len := 0) (pa := v88 mod 2 ^ 64)
                       (pp := v80 mod 2 ^ 64) (pn := v72 mod 2 ^ 64)
                       (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Bf.
      - lia.
      - lia.
      - exact Bpa.
      - exact Bpp.
      - exact Bpn.
      - rewrite HspU. exact Emod.
      - rewrite HspU. exact HSTKN.
      - reflexivity.
      - reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - exact (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem3).
      - exact HACN.
      - (* route (C): the region R is guarded by fr <> 0, and fr = 0 here. *)
        intros a HR _. unfold RFG.reac_ctrl_identity_fragment_shadow_R in HR.
        destruct HR as (_ & Hfr & _). exfalso. apply Hfr. reflexivity.
      - rewrite HspU. unfold ART.HIGHMEM_BEG. lia.
      - rewrite HspU. unfold ART.APPMEM_END. lia.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON CB1).
      - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON CB2).
      - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON CB3).
      - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON CB4).
      - exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem3 _ _ HRON CB5).
      - exact (PBR.rng_bytes_RNG_W _).
      - exact HRNGI.
      - rewrite HspU. exact HRNG.
      - rewrite HspU. exact HSWR.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity. }
    intros ms2 (s0 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 &
                      Ems & HPmu & WM & MI2 & ST2 & FGM & AC2 & SW2) & Hrel & Hro2).
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P7.p7_refuse0 in Ems, HPmu.
    cbn [RFR.fg_fp] in HPmu. subst s0.
    destruct (HMS _ _ _ _ _ _ _ _ Hrel) as (Ems2 & HR2).
    set (m2r := ms_mem ms2) in *. clearbody m2r. subst ms2.
    rewrite (MST.ret_pc_even 0x81da8 ltac:(lia) ltac:(reflexivity)).
    rewrite HspU in HPmu, ST2.
    pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ mem3 _ m2r m2 HRL HR2 Hro2 HPmu) as MUr.
    pose proof (B.MemNorm.wmono_rel B.Img0.rsegs mem3 _ m2r m2 HRL HR2 Hro2 WM) as WMr.
    assert (STr : FRM.stk B.Img0.rsegs m2r (spv - 4672) spv).
    { destruct ST2 as (T1 & T2 & T3). split; [exact T1 |]. split; [exact T2 |].
      intros a Ha. destruct (T3 a Ha) as (Hw & b & Hb). split.
      - rewrite <- (B.MemNorm.wview_rel_rw B.Img0.rsegs m2r m2 _ HR2
                     (B.MemNorm.ro_false_of_wview B.Img0.rsegs m2r m2 _ HR2 Hw)). exact Hw.
      - exists b. rewrite (B.MemNorm.mrd_rel B.Img0.rsegs m2r m2 _ HR2). exact Hb. }
    (* 3. P7F.p7_post_F: the return cut 0x81da8. *)
    eapply P7F.p7_post_F with (m := mem3) (S := spv)
      (sp := lib.Reusable.YK11.getr regs3 2) (gp := lib.Reusable.YK11.getr regs3 3)
      (tp := lib.Reusable.YK11.getr regs3 4) (s0 := lib.Reusable.YK11.getr regs3 8)
      (s1 := Z_to_bv 64 A) (s3 := lib.Reusable.YK11.getr regs3 19)
      (s7 := lib.Reusable.YK11.getr regs3 23) (s8 := lib.Reusable.YK11.getr regs3 24)
      (s9 := lib.Reusable.YK11.getr regs3 25) (s10 := lib.Reusable.YK11.getr regs3 26);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact MUr | exact WMr | exact STr ]. }
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & m2 & -> & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 & K18 &
                     MU2 & WM2 & ST3).
  cbn [ms_mem] in HHID, HGR.
  rewrite <- (w3b_cfg_MS 0x81da8 R2 m2 md2).
  assert (HA9' : B.ACtlCut.rgv R2 9 A) by exact K9.
  assert (K9' : lib.Reusable.YK11.getr R2 9 = lib.Reusable.YK11.getr regs3 9)
    by (etransitivity; [exact K9 | symmetry; exact E9]).
  eapply (HDA8 cx idx fr k ly3 S3 W3 R2 m2 md2 HB).
  - eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2 (fun a => spv - 4672 <= a < spv) HJ).
    + intros x Hx. apply MU2. cbn. split; [exact Hx | exact I].
    + exact HGR.
    + exact HHID.
    + exact HSBM.
    + intros a Ha. unfold Reusable.YCbq.awr_byte. left. rewrite HLS. lia.
  - exact HFRS.
  - exact HFA.
  - exact Hk.
  - (* C5: the body of C_B81da8 (ACtlCutP.v:1628-1639). *)
    split; [exact HPERM |].
    split.
    { eapply (frac_kept cx fr fr regs3 R2 mem3 m2 ((spv - 4672, spv) :: nil) A).
      - exact MU2.
      - exact HFRACk.
      - exact E9.
      - lia.
      - lia.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9'.
      - exact K19.
      - exact K26.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact HN |].
    split; [exact (ourb_kept cx fr mem3 m2 _ MU2 HOUR ltac:(apply KALL; lia)) |].
    split; [exact K10 |].
    split.
    { eapply (pro_kept fr regs3 R2 mem3 m2 ((spv - 4672, spv) :: nil) A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPRO.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - apply KALL; lia. }
    split; [exact K18 |].
    split.
    { apply (spill_mk R2 m2 64 (fr + 3056) A HA9').
      apply (q64_kept _ mem3 m2 _ _ MU2
               (spill_at regs3 mem3 64 (fr + 3056) A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H64)).
      apply KALL; lia. }
    split; [unfold B.ACtlCut.rgv; etransitivity; [exact K24 | exact H24] |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HC1) |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HKN) |].
    eapply (pl0_kept cx fr regs3 R2 mem3 m2 ((spv - 4672, spv) :: nil) A).
    + exact MU2.
    + exact HALLAPP.
    + exact HPL0.
    + exact E9.
    + exact HA9'.
    + lia.
    + lia.
    + exact K23.
    + exact K25.
    + apply KALL; lia.
    + apply KALL; lia.
  - eapply (w3b_ctl_rt_C ly3 S3 ((spv - 4672, spv) :: nil) mem3 m2 HRT MU2 WM2 HALLAPP).
    + cbn. split; [| exact I]. unfold ART.RT_LO, ART.RT_HI. left. lia.
    + intros a Ha. pose proof (w3b_ro_img a Ha) as HI. cbn. split; [| exact I]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81da8 (0x81da8, own6, k <= 14) --S_P8--> B81dbc (0x81dbc, own6, k <= 14).  Seg/P8.v seg_P8 :101.
   beq a0,s2 (taken), ld a0,64(s1) (p = fr + 3056), li a1,0, jal reac_ports_parse (q = 0: ports_ok p 0 bs = false,
   Seg/P8.v:26-27), return at 0x81dbc. *)
Lemma seg_P8 : forall POST, CF POST C_B81dbc -> CF POST C_B81da8.
Proof.
  (* C0: ctl_from's premises, then the body of C_B81da8 (ACtlCutP.v:1628-1639). *)
  intros POST HDBC cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HA0 & HPRO & H18 & H64 & H24 & HC1 & HKN & HPL0).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & QSH & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & _).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hdiv : 0 <= fr / 8 <= fr)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSf : 0 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr; lia).
  unfold Reusable.YG0d.spZ in EspZ.
  assert (HspU : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv) by exact EspZ.
  (* the spill word [A + 64] = p = fr + 3056 (FRAC's base), read-only to the stretch, inside the stack window. *)
  assert (Q64 : B.ACtlCutP.q64 mem3 (A + 64) (fr + 3056)) by (apply (spill_at regs3 mem3 64 _ A E9); lia || exact H64).
  assert (HWA : forall a, A <= a < A + 448 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HWP : forall a, spv - 16 <= a < spv -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HSTK : FRM.stk B.Img0.rsegs mem3 (spv - 16) spv)
    by (apply (w3b_stk_of_present W3 mem3); [lia | lia | exact HWP]).
  assert (HRNG : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 16) 16)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWP; lia]).
  assert (HRNG64 : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (A + 64) 8)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWA; lia]).
  assert (KALL : forall lo n, 0 <= n -> (lo + n <= spv - 16 \/ spv <= lo) ->
                   kept_on ((spv - 16, spv) :: nil) lo n).
  { intros lo n Hn Hd q Hq. cbn. split; [lia | exact I]. }
  assert (HALLAPP : ARF.all_app ((spv - 16, spv) :: nil)).
  { cbn. split; [| exact I]. intros a Ha.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  pose proof PP_F as HPP.
  unfold RPP.reac_ports_parse_contract_F, RPP.REAC_PORTS_PARSE, RPP.REAC_PORTS_PARSE_FRAME in HPP.
  assert (HNOK : RLF.ports_ok (fr + 3056) 0 (@nil byte) = false).
  { unfold RLF.ports_ok. rewrite (Z.eqb_refl 0). cbn [negb]. rewrite Bool.andb_false_r. reflexivity. }
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P8F.p8_pre_F: 0x81da8 -> 0x883d0 with ra = 0x81dbc.  a0 = s2 = -1 takes the beq at 0x81da8, so the sink
          branch 0x81dac `j 82fa4` is not taken; a0 := [A + 64] = fr + 3056, a1 := 0. *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P8F.p8_pre_F with (Ab := A) (p := fr + 3056).
      - exact E9.
      - exact HA0.
      - exact H18.
      - lia.
      - lia.
      - lia.
      - exact (ARF.ro_c8 mem3 (A + 64) (Z_to_bv 64 (fr + 3056)) Q64).
      - exact HRNG64. }
    intros ms1 ->.
    (* 2. reac_ports_parse at q = 0 (ports_ok p 0 [] = false), window [sp - 16, sp). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply HPP with (p := fr + 3056) (q := 0) (lo := spv - 16) (bs := @nil byte).
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - rewrite HspU. exact HSTK.
      - rewrite HspU. lia.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - intros _ H0; exfalso; apply H0; reflexivity.
      - rewrite HspU. exact HRNG.
      - intros _ H0; exfalso; apply H0; reflexivity. }
    intros ms2 HPO. unfold RPP.reac_ports_parse_post in HPO.
    destruct HPO as (u0 & u1 & u2 & u3 & u4 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 &
                     Ems & WM & MI & ST2 & HPmu).
    rewrite HNOK in Ems, HPmu. subst ms2.
    rewrite (MST.ret_pc_even 0x81dbc ltac:(lia) ltac:(reflexivity)).
    rewrite HspU in HPmu, ST2.
    (* 3. P8F.p8_post_F: the return cut 0x81dbc. *)
    eapply P8F.p8_post_F with (m := mem3) (S := spv)
      (sp := lib.Reusable.YK11.getr regs3 2) (gp := lib.Reusable.YK11.getr regs3 3)
      (tp := lib.Reusable.YK11.getr regs3 4) (s0 := lib.Reusable.YK11.getr regs3 8)
      (s1 := Z_to_bv 64 A) (s3 := lib.Reusable.YK11.getr regs3 19)
      (s7 := lib.Reusable.YK11.getr regs3 23) (s8 := lib.Reusable.YK11.getr regs3 24)
      (s9 := lib.Reusable.YK11.getr regs3 25) (s10 := lib.Reusable.YK11.getr regs3 26);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact HPmu | exact WM | exact ST2 ]. }
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & m2 & -> & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 &
                     MU2 & WM2 & ST3).
  cbn [ms_mem] in HHID, HGR.
  rewrite <- (w3b_cfg_MS 0x81dbc R2 m2 md2).
  assert (HA9' : B.ACtlCut.rgv R2 9 A) by exact K9.
  assert (K9' : lib.Reusable.YK11.getr R2 9 = lib.Reusable.YK11.getr regs3 9)
    by (etransitivity; [exact K9 | symmetry; exact E9]).
  eapply (HDBC cx idx fr k ly3 S3 W3 R2 m2 md2 HB).
  - eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2 (fun a => spv - 16 <= a < spv) HJ).
    + intros x Hx. apply MU2. cbn. split; [exact Hx | exact I].
    + exact HGR.
    + exact HHID.
    + exact HSBM.
    + intros a Ha. unfold Reusable.YCbq.awr_byte. left. rewrite HLS. lia.
  - exact HFRS.
  - exact HFA.
  - exact Hk.
  - (* C5: the body of C_B81dbc (ACtlCutP.v:1644-1654). *)
    split; [exact HPERM |].
    split.
    { eapply (frac_kept cx fr fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HFRACk.
      - exact E9.
      - lia.
      - lia.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9'.
      - exact K19.
      - exact K26.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact HN |].
    split; [exact (ourb_kept cx fr mem3 m2 _ MU2 HOUR ltac:(apply KALL; lia)) |].
    split; [exact K10 |].
    split.
    { eapply (pro_kept fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPRO.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - apply KALL; lia. }
    split; [unfold B.ACtlCut.rgv; etransitivity; [exact K24 | exact H24] |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HC1) |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HKN) |].
    eapply (pl0_kept cx fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
    + exact MU2.
    + exact HALLAPP.
    + exact HPL0.
    + exact E9.
    + exact HA9'.
    + lia.
    + lia.
    + exact K23.
    + exact K25.
    + apply KALL; lia.
    + apply KALL; lia.
  - eapply (w3b_ctl_rt_C ly3 S3 ((spv - 16, spv) :: nil) mem3 m2 HRT MU2 WM2 HALLAPP).
    + cbn. split; [| exact I]. unfold ART.RT_LO, ART.RT_HI. left. lia.
    + intros a Ha. pose proof (w3b_ro_img a Ha) as HI. cbn. split; [| exact I]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81dbc (0x81dbc, own6, k <= 14) --S_P9--> B81dd4 (0x81dd4, own6, k <= 14).  Seg/P9.v seg_P9 :98.
   li s2,-1, beq a0,s2 (taken), li a0,0, li a1,0, jal reac_ports_parse (p = q = 0), return at 0x81dd4. *)
Lemma seg_P9 : forall POST, CF POST C_B81dd4 -> CF POST C_B81dbc.
Proof.
  (* C0: ctl_from's premises in its order (ACtlCut.v:214-229), then the body of C_B81dbc (ACtlCutP.v:1644-1654). *)
  intros POST HDD4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HA0 & HPRO & H24 & HC1 & HKN & HPL0).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & QSH & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & _).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hdiv : 0 <= fr / 8 <= fr)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSf : 0 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr; lia).
  unfold Reusable.YG0d.spZ in EspZ.
  assert (HspU : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv) by exact EspZ.
  (* T1 / V1: the callee's 16-byte window lies inside the journal's own window [c_sp cx - LLVMF_STK, c_sp cx),
     so it is present; presence gives lib/Lib's stk and one footprint range of ProgBridge.RNG_W. *)
  assert (HWP : forall a, spv - 16 <= a < spv -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HSTK9 : FRM.stk B.Img0.rsegs mem3 (spv - 16) spv)
    by (apply (w3b_stk_of_present W3 mem3); [lia | lia | exact HWP]).
  assert (HRNG9 : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 16) 16)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWP; lia]).
  assert (KALL : forall lo n, 0 <= n -> (lo + n <= spv - 16 \/ spv <= lo) ->
                   kept_on ((spv - 16, spv) :: nil) lo n).
  { intros lo n Hn Hd q Hq. cbn. split; [lia | exact I]. }
  assert (HALLAPP : ARF.all_app ((spv - 16, spv) :: nil)).
  { cbn. split; [| exact I]. intros a Ha.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  pose proof PP_F as HPP.
  unfold RPP.reac_ports_parse_contract_F, RPP.REAC_PORTS_PARSE, RPP.REAC_PORTS_PARSE_FRAME in HPP.
  assert (HNOK : RLF.ports_ok 0 0 (@nil byte) = false) by reflexivity.
  (* C1 / C2: the cut state as the canonical register tree, then ONE lift of pre + callee + post. *)
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P9F.p9_pre_F: 0x81dbc -> 0x883d0 with ra = 0x81dd4.  a0 = -1 takes the beq at 0x81dc0, so the sink
          branch 0x81dc4 `j 82fa4` is not taken; the stretch touches no memory, so it has no rng premise. *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P9F.p9_pre_F. exact HA0. }
    intros ms1 ->.
    (* 2. reac_ports_parse at p = q = 0 (ports_ok 0 0 [] = false), window [sp - 16, sp). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply HPP with (p := 0) (q := 0) (lo := spv - 16) (bs := @nil byte).
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - rewrite HspU. exact HSTK9.
      - rewrite HspU. lia.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros H0; exfalso; apply H0; reflexivity.
      - rewrite HspU. exact HRNG9.
      - intros H0; exfalso; apply H0; reflexivity. }
    intros ms2 HPO. unfold RPP.reac_ports_parse_post in HPO.
    destruct HPO as (u0 & u1 & u2 & u3 & u4 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 &
                     Ems & WM & MI & ST2 & HPmu).
    rewrite HNOK in Ems, HPmu. subst ms2.
    rewrite (MST.ret_pc_even 0x81dd4 ltac:(lia) ltac:(reflexivity)).
    rewrite HspU in HPmu, ST2.
    (* 3. P9F.p9_post_F: the return cut 0x81dd4, no instruction left in the stretch. *)
    eapply P9F.p9_post_F with (m := mem3) (S := spv)
      (sp := lib.Reusable.YK11.getr regs3 2) (gp := lib.Reusable.YK11.getr regs3 3)
      (tp := lib.Reusable.YK11.getr regs3 4) (s0 := lib.Reusable.YK11.getr regs3 8)
      (s1 := lib.Reusable.YK11.getr regs3 9) (s3 := lib.Reusable.YK11.getr regs3 19)
      (s7 := lib.Reusable.YK11.getr regs3 23) (s8 := lib.Reusable.YK11.getr regs3 24)
      (s9 := lib.Reusable.YK11.getr regs3 25) (s10 := lib.Reusable.YK11.getr regs3 26);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact HPmu | exact WM | exact ST2 ]. }
  (* C3 / C4 / C5 at the lifted post. *)
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & m2 & -> & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 & K18 &
                     MU2 & WM2 & ST3).
  cbn [ms_mem] in HHID, HGR.
  rewrite <- (w3b_cfg_MS 0x81dd4 R2 m2 md2).
  assert (HA9' : B.ACtlCut.rgv R2 9 A)
    by (unfold B.ACtlCut.rgv; etransitivity; [exact K9 | exact E9]).
  eapply (HDD4 cx idx fr k ly3 S3 W3 R2 m2 md2 HB).
  - (* C3: the journal across the callee's window, which is inside the journal's own stack window. *)
    eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2 (fun a => spv - 16 <= a < spv) HJ).
    + intros x Hx. apply MU2. cbn. split; [exact Hx | exact I].
    + exact HGR.
    + exact HHID.
    + exact HSBM.
    + intros a Ha. unfold Reusable.YCbq.awr_byte. left. rewrite HLS. lia.
  - exact HFRS.
  - exact HFA.
  - exact Hk.
  - (* C5: the body of C_B81dd4 (ACtlCutP.v:1659-1669); every reader is kept, a0 and s2 come from the post. *)
    split; [exact HPERM |].
    split.
    { eapply (frac_kept cx fr fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HFRACk.
      - exact E9.
      - lia.
      - lia.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9.
      - exact K19.
      - exact K26.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact HN |].
    split; [exact (ourb_kept cx fr mem3 m2 _ MU2 HOUR ltac:(apply KALL; lia)) |].
    split; [exact K10 |].
    split; [exact K18 |].
    split.
    { eapply (pro_kept fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPRO.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - apply KALL; lia. }
    split; [unfold B.ACtlCut.rgv; etransitivity; [exact K24 | exact H24] |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HC1) |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HKN) |].
    eapply (pl0_kept cx fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
    + exact MU2.
    + exact HALLAPP.
    + exact HPL0.
    + exact E9.
    + exact HA9'.
    + lia.
    + lia.
    + exact K23.
    + exact K25.
    + apply KALL; lia.
    + apply KALL; lia.
  - (* C4: ctl_rt_C.  The window is application memory above the loaded image, apart from the ASan runtime band
       and from every read-only image byte, so the four carried facts move by the kept lemmas (w3b_ctl_rt_C). *)
    eapply (w3b_ctl_rt_C ly3 S3 ((spv - 16, spv) :: nil) mem3 m2 HRT MU2 WM2 HALLAPP).
    + cbn. split; [| exact I]. unfold ART.RT_LO, ART.RT_HI. left. lia.
    + intros a Ha. pose proof (w3b_ro_img a Ha) as HI. cbn. split; [| exact I]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81dd4 (0x81dd4, own6, k <= 14) --S_P10--> B81de8 (0x81de8, own6, k <= 14).  Seg/P10.v seg_P10 :108.
   beq a0,s2 (taken), li a0,0, mv a1,s8 (c = fr + 3040), jal reac_ports_unknown (p = 0: pu_ok 0 bs = false,
   Seg/P10.v:26-27; the callee writes 0 to the code byte c), return at 0x81de8.
   ROUTE (C): the callee is cited in its region form RPU.reac_ports_unknown_contract_F_on (premise shadow_rw m
   DROPPED; PU_F_on, discharged by reac_ports_unknown_F_holds_on, lib/B/Prog/reac_ports_unknownF.v from
   a working branch 076e983605e, taken by path). *)
Lemma seg_P10 : forall POST, CF POST C_B81de8 -> CF POST C_B81dd4.
Proof.
  (* C0: ctl_from's premises, then the body of C_B81dd4 (ACtlCutP.v:1659-1669). *)
  intros POST HDE8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HA0 & H18 & HPRO & H24 & HC1 & HKN & HPL0).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & QSH & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  pose proof HRT as (HAC & _ & _ & HRO).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  (* the own frame's placement (w3b_own6_place): low or high application memory; the code byte fr + 3040 is
     application memory either way, and the frame and its shadow are apart (low: shadow above; high: below). *)
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & HPL).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  unfold ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in HPL.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hdiv : 0 <= fr / 8 <= fr)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSf : 0 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr; lia).
  assert (HSf' : fr + 4096 <= B.ACtlCutP.Sfr fr \/ B.ACtlCutP.Sfr fr + 512 <= fr)
    by (unfold B.ACtlCutP.Sfr; lia).
  (* the code byte Cc = fr + 3040: its shadow byte is the own frame's shadow byte 380 (fr mod 32 = 0). *)
  assert (EDc : (fr + 3040) / 8 = fr / 8 + 380).
  { replace (fr + 3040) with (fr + 380 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (HCc0 : fr + 3040 <> 0) by lia.
  unfold Reusable.YG0d.spZ in EspZ.
  assert (HspU : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv) by exact EspZ.
  assert (HWP : forall a, spv - 16 <= a < spv -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HSTK : FRM.stk B.Img0.rsegs mem3 (spv - 16) spv)
    by (apply (w3b_stk_of_present W3 mem3); [lia | lia | exact HWP]).
  assert (HRNG : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 16) 16)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWP; lia]).
  assert (HRNGC : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (fr + 3040) 1)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HfrP; left; lia]).
  assert (HRNGCS : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (ART.shadow_addr (fr + 3040)) 1).
  { apply (w3b_rng_of_present W3 mem3).
    - unfold ART.shadow_addr, ART.ASAN_K. lia.
    - unfold ART.shadow_addr, ART.ASAN_K. lia.
    - intros a Ha. apply HfrP. right. unfold ART.shadow_addr in Ha |- *. rewrite EDc in Ha. lia. }
  assert (HWRC : MEM.wr_at B.Img0.rsegs mem3 (fr + 3040) 1)
    by (apply (w3b_wr_of_present W3 mem3); [lia | lia | intros a Ha; apply HfrP; left; lia]).
  assert (HRNGG : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) ART.GOT_CELL_K 8)
    by (apply w3b_rng_img; unfold ART.GOT_CELL_K; lia).
  assert (HRNGK : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) ART.CELL_K 8)
    by (apply w3b_rng_img; unfold ART.CELL_K; lia).
  set (WR := (spv - 16, spv) :: (fr + 3040, fr + 3040 + 1) :: nil).
  assert (KALL : forall lo n, 0 <= n -> (lo + n <= spv - 16 \/ spv <= lo) ->
                   (lo + n <= fr + 3040 \/ fr + 3041 <= lo) -> kept_on WR lo n).
  { intros lo n Hn Hd Hd' q Hq. unfold WR. cbn. split; [lia |]. split; [lia | exact I]. }
  assert (HALLAPP : ARF.all_app WR).
  { unfold WR. cbn. split; [| split; [| exact I]]; intros a Ha;
      unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END; [right; lia | lia]. }
  pose proof PU_F_on as HPU.
  unfold RPU.reac_ports_unknown_contract_F_on, RPU.REAC_PORTS_UNKNOWN, RPU.REAC_PORTS_UNKNOWN_FRAME in HPU.
  assert (HNOK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.pu_ok 0 (@nil byte) = false)
    by reflexivity.
  assert (EW : forall sp, RPU.reac_ports_unknown_W sp (fr + 3040) = (sp - 16, sp) :: (fr + 3040, fr + 3040 + 1) :: nil).
  { intros sp. unfold RPU.reac_ports_unknown_W, RPU.REAC_PORTS_UNKNOWN_FRAME.
    rewrite (proj2 (Z.eqb_neq _ _) HCc0). reflexivity. }
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P10F.p10_pre_F: 0x81dd4 -> 0x88628 with ra = 0x81de8.  a0 = s2 = -1 takes the beq at 0x81dd4 (sink branch
          0x81dd8 not taken); a0 := 0, a1 := s8 = Cc. *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P10F.p10_pre_F with (Cc := fr + 3040).
      - exact HA0.
      - exact H18.
      - exact H24. }
    intros ms1 ->.
    (* 2. reac_ports_unknown at p = 0 (pu_ok 0 [] = false): it writes 0 to the code byte Cc, window
          [sp - 16, sp). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply HPU with (p := 0) (c := fr + 3040) (lo := spv - 16) (bs := @nil byte).
      - reflexivity.
      - apply MST.unsigned_lit. lia.
      - rewrite HspU. exact HSTK.
      - rewrite HspU. lia.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros _. split; [exact HWRC |]. split; [intros H0; exfalso; apply H0; reflexivity |].
        rewrite HspU. left. lia.
      - exact HAC.
      - intros _. exact HC1.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros x Hx. rewrite HspU, EW. cbn. split; [| split; [| exact I]];
          unfold ART.GOT_CELL_K, ART.CELL_K, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
            ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Hx; lia.
      - rewrite HspU. exact HRNG.
      - exact HRNGG.
      - exact HRNGK.
      - intros H0; exfalso; apply H0; reflexivity.
      - intros _. split; [exact HRNGC | exact HRNGCS]. }
    intros ms2 HPO. unfold RPU.reac_ports_unknown_post in HPO.
    destruct HPO as (b2 & b3 & b4 & b5 & b6 & b7 & u0 & u1 & u2 & u3 & m2 &
                     Ems & HPmu & WM & ST2 & MI & HCB2).
    rewrite HNOK in Ems, HCB2. subst ms2.
    rewrite (MST.ret_pc_even 0x81de8 ltac:(lia) ltac:(reflexivity)).
    rewrite HspU, EW in HPmu. rewrite HspU in ST2.
    (* 3. P10F.p10_post_F: the return cut 0x81de8. *)
    eapply P10F.p10_post_F with (m := mem3) (S := spv) (Cc := fr + 3040)
      (sp := lib.Reusable.YK11.getr regs3 2) (gp := lib.Reusable.YK11.getr regs3 3)
      (tp := lib.Reusable.YK11.getr regs3 4) (s0 := lib.Reusable.YK11.getr regs3 8)
      (s1 := lib.Reusable.YK11.getr regs3 9) (s3 := lib.Reusable.YK11.getr regs3 19)
      (s7 := lib.Reusable.YK11.getr regs3 23) (s8 := Z_to_bv 64 (fr + 3040))
      (s9 := lib.Reusable.YK11.getr regs3 25) (s10 := lib.Reusable.YK11.getr regs3 26);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact HPmu | exact WM | exact ST2 | exact (HCB2 HCc0) ]. }
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & m2 & -> & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 &
                     MU2 & WM2 & ST3 & HCB3).
  cbn [ms_mem] in HHID, HGR.
  rewrite <- (w3b_cfg_MS 0x81de8 R2 m2 md2).
  assert (HA9' : B.ACtlCut.rgv R2 9 A)
    by (unfold B.ACtlCut.rgv; etransitivity; [exact K9 | exact E9]).
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  eapply (HDE8 cx idx fr k ly3 S3 W3 R2 m2 md2 HB).
  - (* C3: the writes are the callee's window (the journal's stack window) and the code byte (own frame). *)
    eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2
              (fun a => spv - 16 <= a < spv \/ fr + 3040 <= a < fr + 3040 + 1) HJ).
    + intros x Hx. apply MU2. cbn. split; [intros H; apply Hx; left; exact H |].
      split; [intros H; apply Hx; right; exact H | exact I].
    + exact HGR.
    + exact HHID.
    + exact HSBM.
    + intros a [Ha | Ha]; unfold Reusable.YCbq.awr_byte.
      * left. rewrite HLS. lia.
      * right. right. right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3, FB6. lia.
  - exact HFRS.
  - exact HFA.
  - exact Hk.
  - (* C5: the body of C_B81de8 (ACtlCutP.v:1674-1684). *)
    split; [exact HPERM |].
    split.
    { eapply (frac_kept cx fr fr regs3 R2 mem3 m2 WR A).
      - exact MU2.
      - exact HFRACk.
      - exact E9.
      - lia.
      - lia.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9.
      - exact K19.
      - exact K26.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact HN |].
    split; [exact (ourb_kept cx fr mem3 m2 _ MU2 HOUR ltac:(apply KALL; lia)) |].
    split; [exact K10 |].
    split.
    { eapply (pro_kept fr regs3 R2 mem3 m2 WR A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPRO.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - apply KALL; lia. }
    split; [exact HCB3 |].
    split; [split; [exact K24 | exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HC1)] |].
    split; [exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HKN) |].
    eapply (pl0_kept cx fr regs3 R2 mem3 m2 WR A).
    + exact MU2.
    + exact HALLAPP.
    + exact HPL0.
    + exact E9.
    + exact HA9'.
    + lia.
    + lia.
    + exact K23.
    + exact K25.
    + apply KALL; lia.
    + apply KALL; lia.
  - eapply (w3b_ctl_rt_C ly3 S3 WR mem3 m2 HRT MU2 WM2 HALLAPP).
    + unfold WR. cbn [FRM.disjoint_from]. unfold ART.RT_LO, ART.RT_HI.
      split; [left; lia | split; [left; lia | exact I]].
    + intros a Ha. pose proof (w3b_ro_img a Ha) as HI. unfold WR. cbn.
      split; [lia | split; [lia | exact I]].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81de8 (0x81de8, own6, k <= 14) --S_P11--> B81e08 (0x81e08, own6, k <= 14).  Seg/P11.v seg_P11 :184.
   li a1,-1, beq a0,a1 (taken), lbu a0,0(s8) (the code byte, 0), beqz a0 (taken), li a0,14,
   jal reac_ctrl_kind_name (14 > 13: result QMARK = 0x211e0, Seg/P11.v:32-33), return at 0x81e08. *)
Lemma seg_P11 : forall POST, CF POST C_B81e08 -> CF POST C_B81de8.
Proof.
  (* C0: ctl_from's premises, then the body of C_B81de8 (ACtlCutP.v:1674-1684). *)
  intros POST HE08 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HA0 & HPRO & HCB & HXC & HKN & HPL0).
  pose proof HXC as (H24 & HC1).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & QSH & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  pose proof HJ as (HAR & _).
  pose proof HRT as (HAC & _ & _ & HRO).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & _).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hdiv : 0 <= fr / 8 <= fr)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSf : 0 <= B.ACtlCutP.Sfr fr /\ B.ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold B.ACtlCutP.Sfr; lia).
  unfold Reusable.YG0d.spZ in EspZ.
  assert (HspU : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv) by exact EspZ.
  assert (HWP : forall a, spv - 16 <= a < spv -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (HSTK : FRM.stk B.Img0.rsegs mem3 (spv - 16) spv)
    by (apply (w3b_stk_of_present W3 mem3); [lia | lia | exact HWP]).
  assert (HRNG : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (spv - 16) 16)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWP; lia]).
  (* the code byte Cc = fr + 3040 is a byte of the own frame (own6_frame's presence). *)
  assert (HRNGC : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (fr + 3040) 1)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HfrP; left; lia]).
  (* the image hull and KIND_NAME's shadow (the shared ctl_kind_name_shadow_vis at the journal's AR). *)
  assert (HRNGI : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) 0x10000 0x5ee000)
    by (apply w3b_rng_img; lia).
  assert (HRNGK : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (ART.shadow_addr KNC.KIND_NAME) 14)
    by (apply PBR.rng_of_visible; exact (ctl_kind_name_shadow_vis _ _ _ _ _ HAR)).
  assert (HKT : MEM.bytes_at B.Img0.rsegs mem3 KNC.KIND_NAME KNC.kind_name_bytes)
    by exact (kind_name_table cx _ ly3 S3 W3 mem3 md3 k HB HJ).
  assert (HKS : KNC.kind_name_strings mem3)
    by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P11.p11_strings mem3 HRO).
  assert (KALL : forall lo n, 0 <= n -> (lo + n <= spv - 16 \/ spv <= lo) ->
                   kept_on ((spv - 16, spv) :: nil) lo n).
  { intros lo n Hn Hd q Hq. cbn. split; [lia | exact I]. }
  assert (HALLAPP : ARF.all_app ((spv - 16, spv) :: nil)).
  { cbn. split; [| exact I]. intros a Ha.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  pose proof KN_F_on as HKN_F.
  unfold KNC.reac_ctrl_kind_name_contract_F_on, KNC.REAC_CTRL_KIND_NAME, KNC.REAC_CTRL_KIND_NAME_FRAME in HKN_F.
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P11F.p11_pre_F: 0x81de8 -> 0x83d98 with ra = 0x81e08.  a0 = -1 takes the beq at 0x81dec (sink branch
          0x81df0 not taken); the code byte [Cc] = 0 takes the beqz at 0x81df8 (sink branch 0x81dfc not taken). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P11F.p11_pre_F with (Cc := fr + 3040).
      - exact HA0.
      - exact H24.
      - lia.
      - lia.
      - exact HCB.
      - exact HRNGC. }
    intros ms1 ->.
    (* 2. reac_ctrl_kind_name at a0 = 14 (14 > 13: the result is QMARK), window [sp - 16, sp). *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply HKN_F with (lo := spv - 16).
      - exact HKT.
      - exact HKS.
      - rewrite HspU. exact HSTK.
      - rewrite HspU. lia.
      - rewrite HspU. unfold KNC.KIND_NAME. lia.
      - exact HAC.
      - exact HKN.
      - intros x Hx. rewrite HspU. cbn. split; [| exact I].
        unfold ART.GOT_CELL_K, ART.CELL_K, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
          ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Hx. lia.
      - exact HRNGI.
      - rewrite HspU. exact HRNG.
      - exact HRNGK. }
    intros ms2 (b1 & b2 & b3 & m2 & Ems & HPmu & WM & MI & ST2 & HSTR). subst ms2.
    rewrite (MST.ret_pc_even 0x81e08 ltac:(lia) ltac:(reflexivity)).
    rewrite HspU in HPmu, ST2. unfold KNC.REAC_CTRL_KIND_NAME_FRAME in HPmu.
    (* 3. P11F.p11_post_F: the return cut 0x81e08. *)
    eapply P11F.p11_post_F with (m := mem3) (S := spv)
      (sp := lib.Reusable.YK11.getr regs3 2) (gp := lib.Reusable.YK11.getr regs3 3)
      (tp := lib.Reusable.YK11.getr regs3 4) (s0 := lib.Reusable.YK11.getr regs3 8)
      (s1 := lib.Reusable.YK11.getr regs3 9) (s3 := lib.Reusable.YK11.getr regs3 19)
      (s7 := lib.Reusable.YK11.getr regs3 23) (s8 := Z_to_bv 64 (fr + 3040))
      (s9 := lib.Reusable.YK11.getr regs3 25) (s10 := lib.Reusable.YK11.getr regs3 26);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact HPmu | exact WM | exact ST2 ]. }
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & m2 & -> & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 &
                     MU2 & WM2 & ST3).
  cbn [ms_mem] in HHID, HGR.
  rewrite <- (w3b_cfg_MS 0x81e08 R2 m2 md2).
  assert (HA9' : B.ACtlCut.rgv R2 9 A)
    by (unfold B.ACtlCut.rgv; etransitivity; [exact K9 | exact E9]).
  eapply (HE08 cx idx fr k ly3 S3 W3 R2 m2 md2 HB).
  - eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2 (fun a => spv - 16 <= a < spv) HJ).
    + intros x Hx. apply MU2. cbn. split; [exact Hx | exact I].
    + exact HGR.
    + exact HHID.
    + exact HSBM.
    + intros a Ha. unfold Reusable.YCbq.awr_byte. left. rewrite HLS. lia.
  - exact HFRS.
  - exact HFA.
  - exact Hk.
  - (* C5: the body of C_B81e08 (ACtlCutP.v:1689-1697). *)
    split; [exact HPERM |].
    split.
    { eapply (frac_kept cx fr fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HFRACk.
      - exact E9.
      - lia.
      - lia.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9.
      - exact K19.
      - exact K26.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact HN |].
    split; [exact (ourb_kept cx fr mem3 m2 _ MU2 HOUR ltac:(apply KALL; lia)) |].
    split.
    { eapply (pro_kept fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPRO.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - apply KALL; lia. }
    split.
    { eapply (pl0_kept cx fr regs3 R2 mem3 m2 ((spv - 16, spv) :: nil) A).
      - exact MU2.
      - exact HALLAPP.
      - exact HPL0.
      - exact E9.
      - exact HA9'.
      - lia.
      - lia.
      - exact K23.
      - exact K25.
      - apply KALL; lia.
      - apply KALL; lia. }
    split; [exact K10 |].
    split.
    { rewrite tfibsegs_rsegs. apply (bytes_at_kept _ mem3 m2 _ _ MU2 HKT).
      apply KALL; [lia |]. unfold KNC.KIND_NAME. left. cbn. lia. }
    exact (addressable_kept _ mem3 m2 _ _ MU2 HALLAPP HKN).
  - eapply (w3b_ctl_rt_C ly3 S3 ((spv - 16, spv) :: nil) mem3 m2 HRT MU2 WM2 HALLAPP).
    + cbn. split; [| exact I]. unfold ART.RT_LO, ART.RT_HI. left. lia.
    + intros a Ha. pose proof (w3b_ro_img a Ha) as HI. cbn. split; [| exact I]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81e08 (0x81e08, own6, k <= 14) --S_P12--> B81ec4_at [Z.of_nat 0] (left_0 = n - c0 >= 1) | B82eac (left_0 = 0).
   Seg/P12.v seg_P12 :321.  The two instrumented checks of the name bytes at QMARK (0x81e08 .. 0x81e4c; the slow
   blocks 0x82fb0 / 0x82fc0 come back), then the frame-loop prologue (0x81e50 .. 0x81ec0: a3 = 0, s11 = -8, seven
   spills, s6 = 1, eight frame-shadow stores of 0xf8 into Sh + 370 .. 385), then the head test 0x81ec4 `bnez s9`. *)
Lemma seg_P12 : forall POST,
  CF POST (ix_cut C_B81ec4_at [Z.of_nat 0]) -> CF POST C_B82eac -> CF POST C_B81e08.
Proof.
  (* C0: ctl_from's premises, then the body of C_B81e08 (ACtlCutP.v:1689-1697). *)
  (* kn_relro is seg_P11's (kind_name_table); cleared so that no arithmetic tactic below picks it up as a spurious
     dependency of this stage. *)
  clear kn_relro.
  intros POST HEC4 HEAC cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HFRS HFA Hk HBODY HRT.
  destruct HBODY as (HPERM & HFRAC & HN & HOUR & HPRO & HPL0 & HA0 & HKNT).
  pose proof HFRAC as HFRACk.
  destruct HFRAC as (A & spv & E2 & Emod & EspZ & E4 & E8 & E9 & E3 & E19 & E26 &
    Hfrmod & HAmod & HAle & HspA & HfrA & HA448 & Hsp4096 & HspAPP &
    Q336 & Q48 & Q40 & Qhdr & Qent & (sh0 & QSH & QSHl) & QSAV & QTRL).
  destruct (own6_frame cx ly3 S3 W3 mem3 md3 k fr HJ HFRS
              (HFA 6 (B.ACtlCut.c_fpos cx) ltac:(left; reflexivity))) as (Efr3 & HfrLO & HfrHI & HfrP).
  destruct (w3b_win_band cx _ ly3 S3 W3 mem3 md3 k HJ) as (HBlo & HBhi & HBmod).
  pose proof HJ as (HAR & _).
  pose proof HRT as (HAC & HSC & HSI & HRO).
  pose proof HB as ((_ & _ & _ & _ & _ & HLEN & _) & _).
  assert (HLS : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HLS in HBlo.
  unfold ART.HIGHMEM_BEG in HBlo. unfold ART.APPMEM_END in HBhi, HspAPP.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA.
  (* the own frame's placement (w3b_own6_place): low or high application memory; the frame and its shadow are
     apart (low: shadow above the frame; high: below it), and both lie below the window. *)
  destruct (w3b_own6_place cx _ ly3 S3 W3 mem3 md3 k fr HJ ltac:(rewrite HFRS; left; reflexivity) Efr3)
    as (HfrW & HSlo & HShi & HPL).
  rewrite HLS in HfrW. unfold ART.LOWMEM_END in HSlo. unfold ART.HIGHMEM_BEG in HShi.
  unfold ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in HPL.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HSf : 2147450880 + 785408 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= 0x10007fff8000).
  { split; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia | exact HShi]. }
  assert (HSfr : fr + 4096 <= ART.shadow_addr fr \/ ART.shadow_addr fr + 512 <= fr) by lia.
  clear HPL HSlo HShi.
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotInv.FRAME_BYTES_val as HFBv.
  pose proof OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotInv.FRAME_SHADOW_val as HFSv.
  destruct HPRO as ((S136 & S280 & S168 & S192 & S200 & S216 & S104 & S288 & S296 & S304 & S168b) &
                    S152 & S264 & AD6 & S160).
  destruct HPL0 as ((C0a & C23 & C25) & HIDB & HFGB & (RAD1 & RAD2 & RAD3) & S176 & S208 & HFS0).
  destruct HFS0 as (F1 & F2 & F3 & F4 & F5).
  destruct HKNT as (HKTb & HKTa).
  assert (HWA : forall a, A <= a < A + 448 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. apply (w3b_win_present cx _ ly3 S3 W3 mem3 md3 k a HJ). rewrite HLS. lia. }
  assert (RA : forall off len, 0 <= off -> 0 <= len -> off + len <= 448 ->
                 lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (A + off) len).
  { intros off len H1 H2 H3. apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HWA; lia]. }
  (* ---- 1. the check block: the shadow byte kb of QMARK (its 2 name bytes addressable: kb = 0 or 2 <= kb <= 7)
     and the two read-only name bytes "?" / 0. *)
  pose proof (ctl_qmark_addressable _ _ _ _ _ HAR) as HQA.
  destruct (ARF.meta_byte mem3 KNC.QMARK 2 HQA ltac:(lia)) as (kb & HKB & HKBok & _).
  assert (Ekb : Z.shiftr KNC.QMARK 3 + ART.ASAN_K = 2147467836) by reflexivity.
  rewrite Ekb in HKB.
  assert (HQ8 : KNC.QMARK mod 8 = 0) by reflexivity.
  assert (Hk' : bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) by lia.
  destruct HKB as (_ & HKB').
  cbn [CEL.cells_bytes CEL.cbytes app] in HKB'.
  pose proof (MEM.bytes_at_ov_read B.Img0.rsegs mem3 2147467836 [kb] 0 1 HKB' ltac:(cbn; lia)) as HQS.
  cbn [Z.of_nat firstn skipn] in HQS. rewrite Z.add_0_r in HQS.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_qmark mem3 HRO) as HQM.
  pose proof (MEM.bytes_at_ov_read B.Img0.rsegs mem3 KNC.QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 0 1 HQM
                ltac:(cbn; lia)) as HQ0.
  cbn [Z.of_nat firstn skipn] in HQ0. rewrite Z.add_0_r in HQ0.
  pose proof (MEM.bytes_at_ov_read B.Img0.rsegs mem3 KNC.QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 1 1 HQM
                ltac:(cbn; lia)) as HQ1.
  cbn [Z.of_nat firstn skipn] in HQ1.
  destruct (ctl_kind_name_str_shadow _ _ _ _ _ 14 HAR ltac:(lia)) as (_ & HVQ).
  assert (HRNGQ : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) 2147467836 1)
    by (apply PBR.rng_of_visible; exact HVQ).
  assert (HRNG0 : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) 135648 1) by (apply w3b_rng_img; lia).
  assert (HRNG1 : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) 135649 1) by (apply w3b_rng_img; lia).
  (* ---- 2. the prologue's cells: four spill ranges and the own frame's shadow bytes 370 .. 385. *)
  destruct (w3b_rw_of_present W3 mem3 16 (A + 88) ltac:(lia) ltac:(cbn; lia)
              ltac:(intros a Ha; apply HWA; cbn in Ha; lia)) as (j88 & C88).
  destruct (w3b_rw_of_present W3 mem3 24 (A + 112) ltac:(lia) ltac:(cbn; lia)
              ltac:(intros a Ha; apply HWA; cbn in Ha; lia)) as (j112 & C112).
  destruct (w3b_rw_of_present W3 mem3 8 (A + 144) ltac:(lia) ltac:(cbn; lia)
              ltac:(intros a Ha; apply HWA; cbn in Ha; lia)) as (j144 & C144).
  destruct (w3b_rw_of_present W3 mem3 8 (A + 256) ltac:(lia) ltac:(cbn; lia)
              ltac:(intros a Ha; apply HWA; cbn in Ha; lia)) as (j256 & C256).
  destruct (w3b_rw_of_present W3 mem3 16 (ART.shadow_addr fr + 370) ltac:(lia) ltac:(cbn; lia)
              ltac:(intros a Ha; apply HfrP; right; cbn in Ha; lia)) as (jsh & CSH).
  pose proof (spill_at regs3 mem3 168 _ A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S168) as Q168.
  pose proof (spill_at regs3 mem3 208 _ A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S208) as Q208.
  pose proof (spill_at regs3 mem3 216 _ A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S216) as Q216.
  pose proof (spill_at regs3 mem3 280 _ A E9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S280) as Q280.
  assert (HRSH : lib.Lib.ExecF.rng (PBR.RNG_W (Reusable.YA0n.w_H W3)) (ART.shadow_addr fr + 370) 16)
    by (apply (w3b_rng_of_present W3 mem3); [lia | lia | intros a Ha; apply HfrP; right; lia]).
  eapply w3b_lift.
  { unfold w3b_tree.
    (* 1. P12F.p12_chk_F: 0x81e08 -> 0x81e50.  The not-taken obligations 0x81e18 / 0x82fb4 / 0x82fbc, 0x81e28,
          0x81e40 / 0x82fc4 / 0x82fcc and 0x81e4c (header, TRAP OBLIGATIONS) are discharged inside it by kb and the
          two name bytes. *)
    eapply lib.Lib.ExecF.evtF_cut.
    { eapply P12F.p12_chk_F with (kb := kb).
      - exact HA0.
      - exact E26.
      - exact HQS.
      - exact HQ0.
      - exact HQ1.
      - exact Hk'.
      - exact HRNGQ.
      - exact HRNG0.
      - exact HRNG1. }
    intros ms1 (a1' & a2' & ->).
    (* 2. P12F.p12_body_F: 0x81e50 -> 0x81ec4 (nl <> 0) | 0x82eac (nl = 0), nl = n - c0. *)
    eapply P12F.p12_body_F with (nl := B.ACtlCut.c_n cx - SMD.c0 (B.ACtlCut.c_in cx)) (Ab := A)
      (Sh := ART.shadow_addr fr) (fr := fr) (j88 := j88) (j112 := j112) (j144 := j144) (j256 := j256)
      (jsh := jsh).
    - exact C25.
    - lia.
    - exact E9.
    - exact E19.
    - lia.
    - rewrite HFSv. lia.
    - lia.
    - lia.
    - rewrite HFBv. lia.
    - exact C88.
    - exact C112.
    - exact C144.
    - exact C256.
    - exact (ARF.ro_c8 _ _ _ Q168).
    - exact (ARF.ro_c8 _ _ _ Q208).
    - exact (ARF.ro_c8 _ _ _ Q216).
    - exact (ARF.ro_c8 _ _ _ Q280).
    - exact CSH.
    - apply RA; lia.
    - apply RA; lia.
    - apply RA; lia.
    - apply RA; lia.
    - apply RA; lia.
    - apply RA; lia.
    - apply RA; lia.
    - exact HRSH. }
  (* C3 / C4 at the lifted post. *)
  intros ms2 md2 HPOST HHID HGR HSBM.
  destruct HPOST as (R2 & pc2 & m2 & -> & G2 & G3 & G4 & G8 & G9 & G19 & G26 & G23 & G25 & G13 & G27 & G22 &
                     Hpc & MU & WM & Q88 & Q96 & Q112 & Q120 & Q128 & Q144 & Q256 & HRD).
  cbn [ms_mem] in HHID, HGR.
  (* P12F states its post with the unit copy's seg_rom (lib/B/Reusable/YK11, the same body as the core's): the
     cut configuration is that state up to conversion. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs pc2 R2 m2 md2) (POST cx)).
  assert (HA9' : B.ACtlCut.rgv R2 9 A)
    by (unfold B.ACtlCut.rgv; etransitivity; [exact G9 | exact E9]).
  (* the write set (P12.p12_W A (Sfr fr)) and the readers it misses *)
  set (WR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W A (ART.shadow_addr fr)) in *.
  assert (KALL : forall lo n, 0 <= n ->
            (forall q, lo <= q < lo + n ->
               ~ (A + 88 <= q < A + 104) /\ ~ (A + 112 <= q < A + 136) /\ ~ (A + 144 <= q < A + 152) /\
               ~ (A + 256 <= q < A + 264) /\ ~ (ART.shadow_addr fr + 370 <= q < ART.shadow_addr fr + 386)) ->
            kept_on WR lo n).
  { intros lo n Hn H q Hq. unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W.
    cbn [FRM.outside]. destruct (H q Hq) as (N1 & N2 & N3 & N4 & N5).
    split; [exact N1 |]. split; [exact N2 |]. split; [exact N3 |]. split; [exact N4 |]. split; [exact N5 | exact I]. }
  assert (OUTQ : forall q, (q < A + 88 \/ A + 264 <= q \/ (A + 104 <= q < A + 112) \/ (A + 136 <= q < A + 144) \/
                             (A + 152 <= q < A + 256)) ->
                   ~ (ART.shadow_addr fr + 370 <= q < ART.shadow_addr fr + 386) -> FRM.outside WR q).
  { intros q H1 H2. unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W.
    cbn [FRM.outside]. repeat split; try exact I; try exact H2; lia. }
  assert (SHK : forall c n, 0 <= c -> c + n <= 2960 ->
            forall i, 0 <= i < n -> FRM.outside WR (ART.shadow_addr (fr + c + i))).
  { intros c n Hc Hcn i Hi. replace (fr + c + i) with (fr + (c + i)) by lia.
    rewrite (sh_off fr (c + i) Hfr8 ltac:(lia)).
    assert (Hd : (c + i) / 8 < 370) by (apply Z.div_lt_upper_bound; lia).
    assert (Hd0 : 0 <= (c + i) / 8) by (apply Z.div_pos; lia).
    apply OUTQ; lia. }
  assert (SPK : forall off v, 0 <= off -> off + 8 <= 448 ->
            (forall q, A + off <= q < A + off + 8 ->
               ~ (A + 88 <= q < A + 104) /\ ~ (A + 112 <= q < A + 136) /\ ~ (A + 144 <= q < A + 152) /\
               ~ (A + 256 <= q < A + 264) /\ ~ (ART.shadow_addr fr + 370 <= q < ART.shadow_addr fr + 386)) ->
            B.ACtlCutP.spill regs3 mem3 off v -> B.ACtlCutP.spill R2 m2 off v).
  { intros off v H1 H2 H3 HS. apply (spill_mk R2 m2 off v A HA9').
    apply (q64_kept WR mem3 m2 (A + off) v MU (spill_at regs3 mem3 off v A E9 ltac:(lia) ltac:(lia) H1 H2 HS)).
    apply KALL; [lia | exact H3]. }
  assert (HJ2 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
            (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
            (B.ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
  { eapply (w3b_journal cx _ ly3 S3 W3 mem3 md3 k m2 md2
              (fun a => (A + 88 <= a < A + 104) \/ (A + 112 <= a < A + 136) \/ (A + 144 <= a < A + 152) \/
                        (A + 256 <= a < A + 264) \/ (ART.shadow_addr fr + 370 <= a < ART.shadow_addr fr + 386))
              HJ).
    - intros x Hx. apply MU. unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W.
      cbn [FRM.outside]. repeat split; try exact I; intros Hc; apply Hx; tauto.
    - exact HGR.
    - exact HHID.
    - exact HSBM.
    - intros a Ha. unfold Reusable.YCbq.awr_byte.
      destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]]; try (left; rewrite HLS; lia).
      right. right. right. exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity |].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3, FB6.
      change (4096 / 8) with 512. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      unfold ART.shadow_addr, ART.ASAN_K in Ha. lia. }
  (* C4 (route (C)): each shadow region of ctl_rt_C moves to m2 under its own guard: a byte outside the stores keeps
     its value, a stored byte [Sh + 370, Sh + 386) is read back from p12_body_F's post (HRD). *)
  assert (SRW2 : forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P mem3 -> B.ShadowRwOn.shadow_rw_on P m2).
  { intros P HP a Hp Ha. destruct (HP a Hp Ha) as (Hw & b & Hb). split; [apply WM; exact Hw |].
    pose proof (ARF.in_shadow_range a Ha) as (Ha0 & Ha1).
    destruct (Z_lt_le_dec a (ART.shadow_addr fr + 370)) as [L1 | L1];
      [| destruct (Z_lt_le_dec a (ART.shadow_addr fr + 386)) as [L2 | L2]].
    + exists b. rewrite <- Hb. unfold MEM.mrd. rewrite MU; [reflexivity |].
      rewrite MEM.wa_unsigned by lia. unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
        ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Ha. apply OUTQ; lia.
    + apply HRD. intros HO. unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W in HO.
      cbn [FRM.outside] in HO. destruct HO as (_ & _ & _ & _ & HO5 & _). apply HO5. lia.
    + exists b. rewrite <- Hb. unfold MEM.mrd. rewrite MU; [reflexivity |].
      rewrite MEM.wa_unsigned by lia. unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
        ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Ha. apply OUTQ; lia. }
  assert (HRT2 : B.ACtlRtC.ctl_rt_C B ly3 S3 m2).
  { split; [| split; [| split]].
    - apply (ARF.asan_cells_kept WR mem3 m2 HAC MU).
      unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W.
      cbn [FRM.disjoint_from]. unfold ART.RT_LO, ART.RT_HI.
      repeat split; try exact I; left; lia.
    - exact (SRW2 _ HSC).
    - exact (SRW2 _ HSI).
    - intros a Ha. unfold MEM.mrd. rewrite (MU a); [exact (HRO a Ha) |].
      pose proof (w3b_ro_img a Ha) as HI. apply OUTQ; lia. }
  (* the frame shadow [Sfr fr, + 392) is readable at m2: written bytes by HRD, the rest kept from FRAC's shadow *)
  assert (SH2 : exists sh, MEM.bytes_at segs m2 (B.ACtlCutP.Sfr fr) sh /\
                           length sh = Z.to_nat B.ACtlCutP.FRAME_SHADOW).
  { destruct (w3b_bytes_of_readable m2 392 (ART.shadow_addr fr) ltac:(lia) ltac:(cbn; lia)) as (sh2 & HB2 & HL2).
    - intros i Hi.
      destruct (Nat.lt_ge_cases i 370) as [L1 | L1];
        [| destruct (Nat.lt_ge_cases i 386) as [L2 | L2]].
      + destruct QSH as (_ & _ & QR). rewrite QSHl in QR.
        change (Z.to_nat B.ACtlCutP.FRAME_SHADOW) with 392%nat in QR, QSHl.
        pose proof (QR i ltac:(lia)) as Hi'.
        destruct (nth_error sh0 i) as [b |] eqn:Eb; [| apply nth_error_None in Eb; rewrite QSHl in Eb; lia].
        exists b. rewrite <- Hi'. unfold MEM.mrd. rewrite MU; [reflexivity |].
        rewrite MEM.wa_unsigned by lia. apply OUTQ; lia.
      + apply HRD. intros HO. unfold WR, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_W in HO.
        cbn [FRM.outside] in HO. destruct HO as (_ & _ & _ & _ & HO5 & _). apply HO5. lia.
      + destruct QSH as (_ & _ & QR). rewrite QSHl in QR.
        change (Z.to_nat B.ACtlCutP.FRAME_SHADOW) with 392%nat in QR, QSHl.
        pose proof (QR i ltac:(lia)) as Hi'.
        destruct (nth_error sh0 i) as [b |] eqn:Eb; [| apply nth_error_None in Eb; rewrite QSHl in Eb; lia].
        exists b. rewrite <- Hi'. unfold MEM.mrd. rewrite MU; [reflexivity |].
        rewrite MEM.wa_unsigned by lia. apply OUTQ; lia.
    - exists sh2. split; [exact HB2 | rewrite HL2; reflexivity]. }
  assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr R2 m2).
  { eapply (frac_kept_sh cx fr fr regs3 R2 mem3 m2 WR A).
    - exact MU.
    - exact HFRACk.
    - exact E9.
    - lia.
    - lia.
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G19.
    - etransitivity; [exact G26 | symmetry; exact E26].
    - apply KALL; [lia | intros q Hq; repeat split; lia].
    - exact SH2.
    - apply KALL; [lia | intros q Hq; repeat split; lia].
    - apply KALL; [lia | intros q Hq; repeat split; lia].
    - apply KALL; [lia | intros q Hq; repeat split; lia].
    - apply KALL; [lia | intros q Hq; repeat split; lia]. }
  assert (HOUR2 : B.ACtlCutP.OURb cx fr m2)
    by exact (ourb_kept cx fr mem3 m2 WR MU HOUR ltac:(apply KALL; [lia | intros q Hq; repeat split; lia])).
  assert (HIDB2 : B.ACtlCutP.IDBe cx fr RIM.ID0 m2).
  { unfold B.ACtlCutP.IDBe in HIDB |- *. apply (bytes_at_kept WR mem3 m2 _ _ MU HIDB).
    rewrite id0_len. apply KALL; [lia | intros q Hq; repeat split; lia]. }
  assert (HRAD1 : ART.addressable m2 (fr + 2688) 38)
    by exact (addressable_kept_on WR mem3 m2 _ _ MU RAD1 (SHK 2688 38 ltac:(lia) ltac:(lia))).
  assert (S1762 : B.ACtlCutP.spill R2 m2 176 (fr + 2688))
    by (apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S176]).
  destruct Hpc as [(Epc & Hnl) | (Epc & Hnl)]; subst pc2.
  - (* C5, nl <> 0: the head of the frame loop at j = 0 (ix_cut C_B81ec4_at [Z.of_nat 0]; ACtlCutP.v:1702-1711). *)
    eapply (HEC4 cx [Z.of_nat 0] fr k ly3 S3 W3 R2 m2 md2 HB HJ2 HFRS HFA).
    + cbn in Hk |- *. lia.
    + cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity |].
      cbn [B.ACtlCut.cut_body B.ACtlCutP.C_B81ec4_at].
      change (B.ACtlCutP.ixn 0 [Z.of_nat 0]) with 0%nat.
      split; [exact HPERM |].
      split; [exact HFRAC2 |].
      split; [exact HN |].
      split.
      { (* LI cx fr 0 *)
        split; [lia |].
        split; [exact G13 |].
        split; [exact HOUR2 |].
        split.
        { split; [exact C0a |]. split.
          - unfold B.ACtlCut.rgv; etransitivity; [exact G23 | exact C23].
          - unfold B.ACtlCut.rgv; etransitivity; [exact G25 | exact C25]. }
        split.
        { change (SMD.t_left (B.ACtlCut.c_in cx) 0) with
            (SMD.nlen (B.ACtlCut.c_in cx) - SMD.c0 (B.ACtlCut.c_in cx)).
          unfold SMD.nlen. lia. }
        split.
        { (* IFS cx fr 0: the turn-0 records ID0 / z72 and the turn-0 fragment state. *)
          split; [split; [exact HIDB2 | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotInv.id_ok_ID0] |].
          split.
          { split; [| exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.P12.p12_frag_ok_z72].
            unfold B.ACtlCutP.FGBe in HFGB |- *. apply (bytes_at_kept WR mem3 m2 _ _ MU HFGB).
            rewrite z72_len. apply KALL; [lia | intros q Hq; repeat split; lia]. }
          split.
          { unfold B.ACtlCutP.u32 in F1 |- *. apply (bytes_at_kept WR mem3 m2 _ _ MU F1).
            rewrite le4_len. apply KALL; [lia | intros q Hq; repeat split; lia]. }
          split; [exact (b8_kept WR mem3 m2 _ _ MU F2
                           ltac:(apply KALL; [lia | intros q Hq; repeat split; lia])) |].
          split.
          { apply (bytes_at_kept WR mem3 m2 _ _ MU F3). rewrite fsbody0_len.
            apply KALL; [lia | intros q Hq; repeat split; lia]. }
          split; [exact (addressable_kept_on WR mem3 m2 _ _ MU F4 (SHK 2880 40 ltac:(lia) ltac:(lia))) |].
          exact F5. }
        (* FLI cx fr *)
        split; [exact G27 |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S168] |].
        split; [exact (spill_mk R2 m2 96 _ A HA9' Q96) |].
        split; [exact (spill_mk R2 m2 112 _ A HA9' Q112) |].
        split; [exact (spill_mk R2 m2 120 _ A HA9' Q120) |].
        split; [exact (spill_mk R2 m2 128 _ A HA9' Q128) |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S136] |].
        split; [exact (spill_mk R2 m2 144 _ A HA9' Q144) |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S152] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S280] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S160] |].
        split; [exact S1762 |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S192] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S200] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S216] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S208] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S104] |].
        split; [exact (spill_mk R2 m2 256 _ A HA9' Q256) |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S264] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S288] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S296] |].
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S304] |].
        split; [exact (addressable_kept_on WR mem3 m2 _ _ MU AD6 (SHK 2624 6 ltac:(lia) ltac:(lia))) |].
        split.
        { apply (w3b_stk_of_present W3 m2); [lia | unfold B.ACtlCutP.FRAME_BYTES; lia |].
          intros a Ha. unfold B.ACtlCutP.FRAME_BYTES in Ha.
          apply (apresent_kept WR _ mem3 m2 a MU ltac:(lia)); [apply OUTQ; lia |].
          apply HfrP. left. lia. }
        split.
        { split; [exact HRAD1 |].
          split; [exact (addressable_kept_on WR mem3 m2 _ _ MU RAD2 (SHK 2768 72 ltac:(lia) ltac:(lia))) |].
          exact (addressable_kept_on WR mem3 m2 _ _ MU RAD3 (SHK 2880 40 ltac:(lia) ltac:(lia))). }
        split.
        { split.
          - unfold B.ACtlCutP.KNT. apply (bytes_at_kept WR mem3 m2 _ _ MU HKTb).
            apply KALL; [lia |]. intros q Hq. unfold KNC.KIND_NAME in Hq. cbn in Hq. repeat split; lia.
          - apply (addressable_kept_on WR mem3 m2 _ _ MU HKTa). intros i Hi.
            assert (Hd : (KNC.KIND_NAME + i) / 8 <= 100000)
              by (apply Z.div_le_upper_bound; unfold KNC.KIND_NAME; lia).
            assert (Hd0 : 0 <= (KNC.KIND_NAME + i) / 8) by (apply Z.div_pos; unfold KNC.KIND_NAME; lia).
            assert (Es : ART.shadow_addr (KNC.KIND_NAME + i) = (KNC.KIND_NAME + i) / 8 + 2147450880)
              by reflexivity.
            rewrite Es. apply OUTQ; lia. }
        split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S168b] |].
        exact (spill_mk R2 m2 88 _ A HA9' Q88). }
      split; [exact (ctl_input_block cx _ ly3 S3 W3 m2 md2 k HB HJ2 HPERM ltac:(lia)) |].
      split; [apply SPK; [lia | lia | intros q Hq; repeat split; lia | exact S280] |].
      exact G22.
    + exact HRT2.
  - (* C5, nl = 0: the loop's exit edge 0x81ec4 `bnez s9` not taken, 0x81ec8 `j 0x82eac`
       (C_B82eac, ACtlCutP.v:2710-2721). *)
    eapply (HEAC cx idx fr k ly3 S3 W3 R2 m2 md2 HB HJ2 HFRS HFA).
    + cbn in Hk |- *. unfold B.ACtlK.EV_LLVMF. lia.
    + split; [exact HPERM |].
      split; [exact HFRAC2 |].
      split; [exact HN |].
      split; [exact HOUR2 |].
      split; [exact S1762 |].
      split.
      { exists (firstn 21 RIM.ID0). split; [| split].
        - unfold B.ACtlCutP.IDBe in HIDB2.
          rewrite <- (firstn_skipn 21 RIM.ID0) in HIDB2.
          exact (proj1 (proj1 (MEM.bytes_at_app _ m2 (fr + 2688) (firstn 21 RIM.ID0) (skipn 21 RIM.ID0)) HIDB2)).
        - reflexivity.
        - intros Hc. vm_compute in Hc. discriminate Hc. }
      replace (fr + 2691) with (fr + 2688 + 3) by lia.
      exact (ARF.addressable_sub m2 (fr + 2688) 38 3 17 HRAD1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact HRT2.
Qed.

End W3b.

(* Stage lemmas of this file, each closed by Qed and named and stated as lib/B/ACtl.v's stage hypothesis
   (ACtl.v:492-502):
     seg_P7  : forall POST, CF POST C_B81da8 -> CF POST C_B81d80
     seg_P8  : forall POST, CF POST C_B81dbc -> CF POST C_B81da8
     seg_P9  : forall POST, CF POST C_B81dd4 -> CF POST C_B81dbc
     seg_P10 : forall POST, CF POST C_B81de8 -> CF POST C_B81dd4
     seg_P11 : forall POST, CF POST C_B81e08 -> CF POST C_B81de8
     seg_P12 : forall POST, CF POST (ix_cut C_B81ec4_at [Z.of_nat 0]) -> CF POST C_B82eac -> CF POST C_B81e08
   Trap obligations: UBSan none; the ten abort / report branches of the header, all refuted inside the cited `_F`
   runs. *)
