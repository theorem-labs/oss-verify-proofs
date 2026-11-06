(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* lib/B/ACtlW3a.v -- piece W3a (cut-table-B.tsv rows 28-34: B81c58 .. B81d68; segments S_P1, S_P1_bfc, S_P2,
   S_P3, S_P4, S_P5, S_P6) of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released
   cgif_file_fuzzer form.  One writer: a Theorem Labs lane's glue lane, by brief
   bwalk-piece.md (a working note, not in this delivery).
   rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one lemma per cut of W3a, NAMED AND STATED EXACTLY AS lib/B/ACtl.v's
   stage hypothesis (ACtl.v:478-490, seg_P1 .. seg_P6, after its CF notation), proved for every SK and FP (the top
   instantiates SK := Reusable.YE2k.tfib_sink_head, FP := []), so the top cites it directly.
     seg_P1     B81c58 (0x81c58, k <= 14) -> B81ca8   beqz a0 (taken), 14 frame-shadow stores, __asan_set_shadow_f8
     seg_P1_bfc B81c60 (0x81c60, k <= 12) -> B81ca8   the same run from its second entry
     seg_P2     B81ca8 (0x81ca8, k <= 14) -> B81cb0   one frame-shadow store, one spill load (no call)
     seg_P3     B81cb0 (0x81cb0, k <= 14) -> B81d18   29 frame-shadow stores, __asan_memset (fr + 2880, 0, 40),
                                                      reac_identity_init (fr + 2688)
     seg_P4     B81d18 (0x81d18, k <= 14) -> B81d28   __asan_memset (fr + 2768, 0, 72)
     seg_P5     B81d28 (0x81d28, k <= 14) -> B81d68   16 frame-shadow stores, the code byte, __asan_memset
                                                      (fr + 3056, 0, 32)
     seg_P6     B81d68 (0x81d68, k <= 14) -> B81d80   reac_ctrl_identity_reply, refused call (a0 = 0, a1 = 0)
   Every cut owns the class-6 fake frame (own6).  No allocator site; no fake-stack call of this function; no loop.

   TRAP OBLIGATIONS.  UBSan `unimp` 0x82fa0: none (plan 6.2 lists no branch for S_P1 .. S_P6; the listing has no
   branch to 0x82fa0 in [0x81c58, 0x81d80), objdump L84579-L84652).  ASan abort sink 0x82fa4: one branch,
     0x81c5c `j 82fa4`  guard 0x81c58 beqz a0,0x81c60 taken: a0 = 0 (C_B81c58's a0v regs 0), stepped inside
                        P1F.p1_pre_F (its premise a0 = Z_to_bv 64 0) -- seg_P1.
   No other branch of [0x81c58, 0x81d80) targets 0x82fa0, 0x82fa4 or a report stub.

   ROUTE (lead FINAL 22:18Z via a Theorem Labs lane 22:29Z, route (a)).  Each stage is GLUE: a Theorem Labs lane's footprint re-run of
   ctrl's proved run up to the callee entry (`<run>_pre_F`), lifted by a Theorem Labs lane's kit corollary
   Reusable.YA0nR.SRr_fevt_hid through B.ProgBridge.fevt_of_evtF (a run whose `_F` asks mem_inv is first moved to
   MemNorm.normalize of the cut memory and back by MemNormF.evtF_normalize_ro: w3a_SRr_norm), then the callee: a
   runtime callee by its ONE owner's SRr-form contract (never walked here), a program callee with a footprint
   contract joined to the `_pre_F` by ExecF.evtF_cut BEFORE the lift (one RNG, one lift), a program callee with a
   world spec (S_P6) by that spec.  No `_F` steps a callee and none takes a callee contract as a premise.
   THE EMPTY `_post_F` STRETCHES.  Every callee of W3a returns AT the exit cut, so no `<run>_post_F` is applied:
   after a call the stage goes from the callee's post to the exit body directly, taking the memory facts at VISIBLE
   addresses (munch_vis / wmono_vis / rw_cells) from B.ProgWorld.ctl_post_set_shadow / ctl_post_memset (PROVED)
   or, after the world spec of S_P6, from YCbq.acall_kept's view clauses (w3a_mrd_view_eq), and ctl_rt_C from
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w3a_ctlrt).

   ROUTE (C) (a Theorem Labs lane 09:20Z / 11:15Z; shell a working branch a2ab7f5988a).  A cut carries
   B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (asan_cells, shadow_rw_on (cut_shadow ly3 S3), shadow_rw_on img_shadow, ro_agree)
   in place of the full ctl_rt.  The runs are the `_on` twins (P1F.p1_pc_pre_F_on: its region [Q, Q + 187) comes from
   cut_shadow's owned-frame disjunct, w3a_srw_frame_norm; P3F.p3_pre_F_on / P5F.p5_pre_F_on: no shadow premise); the
   callee reac_identity_init by its `_on` contract (region: the shadow words of [fr + 2688, fr + 2726), inside the
   owned frame's shadow, w3a_srw_frame_norm).  ctl_rt_C after a call: ctl_rt_C_of_AR on the journal's AR
   (w3a_ctlrt); after a silent run: w3a_ctlrt_run.

   BUILD STATE (honest; type-check, u19build on a build machine).
   EVERY STAGE IS PROVED (Qed); each stage's `Proof using` names exactly the Section hypotheses it closes over:
     seg_P2           Hwx, LAWS, segs_low (the core's own facts);
     seg_P4           Hwx, LAWS, segs_low, AMEMSET, TFIB_SYMS, RELRO_IMG, RO_OFL, ctl_kind_name_addressable;
     seg_P5           seg_P4's list and ctl_parse_bc_addressable;
     seg_P3           seg_P4's list and reac_identity_init_holds_F_on;
     seg_P1, _bfc     Hwx, LAWS, segs_low, ASF8, TFIB_SYMS, RELRO_IMG, RO_OFL, ctl_kind_name_addressable (one
                      proof, w3a_P1);
     seg_P6           Hwx, LAWS, segs_low, TREPLY, TFIB_SYMS, RELRO_IMG, RO_OFL, ctl_kind_name_addressable.
   The LOCAL HELPERS block (after the Section hypotheses) is proved from the core, lib/Lib and B's ProgBridge /
   ProgWorld / ProgWorldCtlRtC / ShadowRwOn(T) / MemNorm(F); the helpers use only the core's own facts (Hwx, LAWS,
   segs_low) and, in w3a_ctlrt / w3a_aro, TFIB_SYMS, RELRO_IMG, RO_OFL.
   No Axiom, no Parameter, no Admitted.  The ONE place that names the shell's argument lists is the SHELL BINDING.

   THE COMMON SHAPE OF A STAGE (steps C0-C5).
   C0  intros POST HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT (ctl_from's premises in its
       order); w3a_cut6 gives the frame's placement and presence, its shadow's presence, and the stack window's
       presence from the journal (AR's frame law, astk_ok, the window clause).  S := c_sp cx, Sh := Sfr fr.
   C1  cfg_at segs pc regs3 mem3 md3 is the MS state over Regs6ss.mkR_of regs3 (ProgBridge.cfg_at_MS,
       YA0nR.SRr_xregs_eqv).
   C2  The run, lifted at RNG := ProgBridge.RNG_W (w_H W3) (fp_avoids_RNG_W); each `rng RNG lo len` premise by
       ProgBridge.rng_of_visible from the journal's presence facts (w3a_vis); image and runtime ranges by
       ProgBridge.img_vis_W / rt_vis_W; the stack window's shadow by AR's zero-shadow law (w3a_stk_sh_cover).
   C3  The journal after a run: YCbq.ajournal_exec over the run's write set (w3a_after_run; frame shadow, frame bytes
       and stack window are YCbq.awr_byte); after a runtime call: the call rule's own journal (YCbq.aj_intrin_at) or
       YCbq.ajournal_after_write (set_shadow); after S_P6's callee: its spec's journal.
   C4  ctl_rt_C: after a silent run w3a_ctlrt_run (writes off the image); after a call w3a_ctlrt.
   C5  The successor: apply HY at the same cx, idx, fr and frames (S_P6: the post's ly2 S2 W2 and k + EV_REPLY);
       kmax: every successor bound is 14 and every W3a bound is <= 14.

   SECTION HYPOTHESES (source of each text):
   - Hwx (YK04.wx_segs_nowrap segs), LAWS (YG0d.AR_laws), segs_low: the core's own facts (YCbq's sections).
   - ASF8: __asan_set_shadow_f8 (entry 0x55144) by Reusable.SetShadowDefP.aset_shadow_realizesP (shared form,
     RTPOST, walk line 5826fdf4d4d; owner a Theorem Labs lane).
   - AMEMSET: __asan_memset by the core's aintrin_realizes segs B OSet at Reusable.YB1w.tfib_A_asan_memset, used
     through YCbq.aj_intrin_at.
   - TFIB_SYMS, RELRO_IMG, Context RO_OFL: the texts ctl_rt_C_of_AR's route takes (ACtl.v Section Ctl; owner: the
     top / a Theorem Labs lane).
   - ctl_kind_name_addressable (RTPOST, owner a Theorem Labs lane); ctl_parse_bc_addressable (its twin for
     REAC_CTRL_PARSE_BC, owner a Theorem Labs lane; seg_P5's exit cut carries it).
   - reac_identity_init_holds_F_on: reac_identity_init's footprint contract in route (C)'s form
     (RII.reac_identity_init_contract_F_on, statements by path from a working branch c1ab8e42e7f;
     obligation: its image-B proof; owner a Theorem Labs lane).
   - TREPLY: reac_ctrl_identity_reply's world spec (B.Prog.C_reac_ctrl_identity_reply; owner a Theorem Labs lane).  Its
     statement takes no shadow premise (the caller-journal form), so route (C) changes nothing at S_P6's call.
   a Theorem Labs lane's `_F` RUNS, CITED BY MODULE (Required qualified below, never Imported, never restated):
     P1F.p1_pc_pre_F_on (0x81c58 / 0x81c60 -> 0x55144, ra = 0x81ca8; route (C), a working branch)
     P2F.p2_evt_F     (0x81ca8 -> 0x81cb0, no call)
     P3F.p3_pre_F_on  (0x81cb0 -> 0x52600, ra = 0x81d10; route (C));  P3F.p3_pre2_F (0x81d10 -> 0x87de8, ra = 0x81d18)
     P4F.p4_pre_F     (0x81d18 -> 0x52600, ra = 0x81d28)
     P5F.p5_pre_F_on  (0x81d28 -> 0x52600, ra = 0x81d68; route (C))
     P6F.p6_pre_F     (0x81d68 -> 0x848fc, ra = 0x81d80)
   Their bound premises are discharged at the use site from FRAC's A + 448 <= S <= APPMEM_END and the frame's
   placement.

   CLOSURE (rule (3); measured BEFORE route (C): 239 files, a Require walk from this file over the then tip with
   a Theorem Labs lane's P1F-P6F from 12a7ea50807; on a working branch a2ab7f5988a standin_scan.py counts 455 files and no stand-in, and the
   blob list below is not re-measured): the frame-route files reached through the `_F` modules were the v1.9 blobs:
   lib/B/Prog/SlotModel.v de18d111c37, lib/B/Prog/SlotInv.v dfc10b8f7a4, lib/B/Prog/Seg/* at 3803efccea0
   (Seg/P1.v 0de0b82c0a6, P2.v d84d761a5b9, P3.v a5b65d45f85, P4.v 08a43f8a230, P5.v 97ba3fa3f27, P6.v 23917ccc08f,
   the blobs a Theorem Labs lane re-runs), and through Seg/Tac_bp.v -> lib/B/Contract.v 65b05173b1a:
   lib/B/ClassConsDef.v 164f778c20b, lib/AZ/Spec/AsanCtrl.v 80ffbfc0a07, AsanCtrlProps.v b4f333a2672, STree.v
   1293d54ecd2 (porter 00:24Z: closure only), lib/B/AsanRTInv.v 5cd1e53cede, FrameAPI.v c09def579bd, MemNorm.v
   a10a476ffd9, PContract.v 4f9a4d5ed82, AsanRT.v 32e0f5191fd; and lib/AZ/LibA/AcctCore.v 0e06d81d553 through
   lib/Lib/ExecF.v (porter 00:25Z).  No other lib/AZ file.  No statement or hypothesis of this file names a
   frame-route identifier (SlotInv, lib/AZ, AsanRTInv, Contract, FrameAPI, SpinAlg, W6, MemNorm, QSlot /
   ClassConsDef / ClassRoomLow / AsanCtrl* / STree).

   PROVENANCE: cut table cut-table-B.tsv rows 28-34 (lines 29-35) (a working note, not in this delivery); plan
   llvmf-B-walk-plan.md 2.2 rows 28-34, 2.3 rows 28-34, 2.4 row S_P3, 6.2 (a working note, not in this delivery);
   ctrl's runs at a working branch 3803efccea0 (Seg/P1.v .. P6.v); objdump
   fuzz_ctrl.objdump.txt (L84579-L84652) (a working note, not in this delivery). *)

From Coq Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1w Reusable.YCfn.
(* set_shadow_f8's contract (a Theorem Labs lane): the expected path of the relocated SetShadowDef (see header). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.SetShadowDefP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.AsanRTFacts B.ProgBridge.
(* proof use only (no statement or hypothesis names them): the normalized-memory transport of a footprint run
   (MemNormF.evtF_normalize_ro, over MemNorm) and the fake-frame facts of the core (YG0s.frame_facts) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNormF Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss.
(* a Theorem Labs lane's image-B ProgWorld layer (arodata_okP_of_S, ctl_post_set_shadow / ctl_post_memset, aview_vis_mrd) and
   route (C)'s cut form (a Theorem Labs lane 09:20Z / 11:15Z; a working branch ad8c0a4792a): the narrowed runtime conjunct
   B.ACtlRtC.ctl_rt_C, its producer B.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws + AR + arodata_okP; no
   AR_states_vis0_shadow, no AR_states_owned_ro), the region form B.ShadowRwOn.shadow_rw_on and its transports
   B.ShadowRwOnT. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ShadowRwOn B.ShadowRwOnT B.ProgWorldCtlRtC.
(* the read-only data route of the owner's ruling (06:46Z): ro_below_ofl, arodata_ok_journalP *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_parse_c.
(* reac_ctrl_identity_reply's world spec (TREPLY) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's footprint runs of S_P1 .. S_P6 (a working branch 12a7ea50807), Required QUALIFIED, never
   Imported (porter 23:38Z); their closure is the CLOSURE paragraph of the header. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P1F P2F P3F P4F P5F P6F.
Import ListNotations.
Local Open Scope Z_scope.

(* lib/Lib's memory vocabulary and ctrl's callee statement files, qualified only (the SHADOWED NAMES rule,
   ACtlCut.v: no lib/Lib module is Imported here). *)
Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.
Module RCP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.

Section W3a.

(* The shell's contexts and variables, in its order (lib/B/ACtlCut.v section CtlCut).  SK is the core's sink head;
   the top instantiates it EXPLICITLY with Reusable.YE2k.tfib_sink_head; nothing here relies on instance search. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists.  CF is lib/B/ACtl.v's CF
   with SK and FP left generic. ---- *)
Local Notation CF POST X := (B.ACtlCut.ctl_from B MT XM_LIB RLO RHI FP POST X).
Local Notation C_B81c58 := (B.ACtlCutP.C_B81c58 B).
Local Notation C_B81c60 := (B.ACtlCutP.C_B81c60 B).
Local Notation C_B81ca8 := (B.ACtlCutP.C_B81ca8 B).
Local Notation C_B81cb0 := (B.ACtlCutP.C_B81cb0 B).
Local Notation C_B81d18 := (B.ACtlCutP.C_B81d18 B).
Local Notation C_B81d28 := (B.ACtlCutP.C_B81d28 B).
Local Notation C_B81d68 := (B.ACtlCutP.C_B81d68 B).
Local Notation C_B81d80 := (B.ACtlCutP.C_B81d80 B).

(* ---- Section hypotheses (sources in the header) ---- *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.


(* The core's facts under which YCbq's lemmas used here are stated (AR_laws, the image below kLowMemEnd). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* __asan_set_shadow_f8 @0x81ca4 (entry 0x55144), value 0xf8: the shared form (lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery), walk line
   5826fdf4d4d): a Theorem Labs lane's Reusable.SetShadowDefP.aset_shadow_realizesP = SetShadowDef.aset_shadow_realizes plus the
   presence clause.  OWNER a Theorem Labs lane; the top discharges it (B Rt/SetShadow.v ctrl_set_shadow_f8P). *)
Hypothesis ASF8 : Reusable.SetShadowDefP.aset_shadow_realizesP segs B 0x55144 0xf8.

(* __asan_memset @0x81d0c / 0x81d24 / 0x81d64: the core's memset rule at B's catalogue name. *)
Hypothesis AMEMSET :
  Reusable.YG0d.aintrin_realizes segs B Reusable.YG0d.OSet Reusable.YB1w.tfib_A_asan_memset.

(* ---- RtPost, image B: the members W3a uses of the walk's ONE shared block of record (lib/B/RTPOST-SHARED-B.txt),
   token for token.  munch_vis / wmono_vis / rt_post_frame are Local Notations here (over H := w_H W), the bodies of
   B.ProgWorld's Definitions of the same names.  aview_vis_mrd and ctl_post_memset are NOT hypotheses: they are
   PROVED on the walk line as B.ProgWorld.aview_vis_mrd and B.ProgWorld.ctl_post_memset (statement
   B.ProgWorld.ctl_post_memset_stmt, the same text the block carries), and the stages cite them by name. ---- *)
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


(* ctl_rt_C at a cut (route (C), ACtlCut.v ctl_from's runtime premise; a working branch ad8c0a4792a): after a runtime call it is
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED; statement ctl_rt_C_of_AR_stmt) on the journal's AR, which takes
   CtrlTSyms and AR_laws only (no AR_states_vis0_shadow, no AR_states_owned_ro).  TFIB_SYMS carries ACtl.v's exact
   name and text (Section Ctl; the top supplies it).  Used by w3a_ctlrt below, after each core runtime call (the
   memsets of seg_P3 .. seg_P5, the set_shadow of seg_P1 / seg_P1_bfc) and after S_P6's callee. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
(* The read-only data route (owner ruling, a Theorem Labs lane 06:46Z), token for token: ctl_base's arodata_okS ->
   Reusable.APostBase.arodata_ok_journalP -> arodata_okP at the cut / post state -> ctl_rt_C_of_AR.  The journal lemma
   takes the read-only span inside the image and the span below the sink head (Context form).  OWNER: the top
   (a Theorem Labs lane, ACtl.v). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* V6 twin for the KIND_NAME table: lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery) (adc9b58a03c), token for token; owner a Theorem Labs lane
   (lib/B/ProgBridgeData.v; the top discharges it).  W3a: every cut of W3a carries `addressable m KNA.KIND_NAME 112`
   across the runtime calls. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* V6 twin for reac_ctrl_parse's .bss byte block REAC_CTRL_PARSE_BC (6 bytes), the shape of the shared
   ctl_kind_name_addressable: the image's shadow is allocator-owned, so its addressability after a runtime call
   comes only from AR.  OBLIGATION: from AR (B's as_zero_shadow / CtrlBB tables), addressable mem REAC_CTRL_PARSE_BC 6.
   OWNER: a Theorem Labs lane (lib/B/ProgBridgeData.v, with the six shared data facts).  W3a: seg_P5 (the exit cut B81d68
   carries it; the entry cut B81d28 does not). *)
Hypothesis ctl_parse_bc_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.RCP.REAC_CTRL_PARSE_BC 6.

(* reac_identity_init @0x81d14 (callee 0x87de8): its footprint contract in route (C)'s narrowed form,
   reac_identity_init_contract_F_on (lib/B/Prog/reac_identity_init_c.v, the image-B _on STATEMENTS taken by path from
   a working branch c1ab8e42e7f; region reac_identity_init_shadow_R id := id <> 0 /\ sh_word_on id 38).
   OBLIGATION: its image-B proof (reac_identity_init_F_holds_on / closed corollary).  OWNER: a Theorem Labs lane. *)
Hypothesis reac_identity_init_holds_F_on : RII.reac_identity_init_contract_F_on.

(* reac_ctrl_identity_reply @0x81d7c (callee 0x848fc) at S_P6's refused call (a0 = fr = 0, a1 = len = 0): its world
   spec in the caller-journal form, the shared name (walk line 5826fdf4d4d, a Theorem Labs lane 08:06Z; a Theorem Labs lane's
   lib/B/Prog/C_reac_ctrl_identity_reply.v, 024ef401073).  OWNER a Theorem Labs lane (pb_reac_ctrl_identity_reply); the top
   discharges it. *)
Hypothesis TREPLY : B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec RLO RHI B.

(* ---------------------------------------------------------------------------------------------------------
   LOCAL HELPERS (this file only).  Generic facts the stages share: memory readers over raw bytes, the journal
   after a silent run (YCbq.ajournal_exec), ctl_rt after a silent run, the cut context of an own6 cut (step C0),
   and the transports of the carried body bundles.  Every one is PROVED here from the core (YCbq, YG0d's AR laws,
   the journal), lib/Lib and B's ProgBridge; none is a hypothesis. *)

Local Notation rsegs := B.Img0.rsegs.

Lemma w3a_P64 : 2 ^ 64 = 18446744073709551616.
Proof using. reflexivity. Qed.

Lemma w3a_outside_dec : forall W x, lib.Lib.Frame.outside W x \/ ~ lib.Lib.Frame.outside W x.
Proof using.
  induction W as [|[lo hi] W IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
    + right. intros [H1 _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma w3a_not_outside1 : forall lo hi a, ~ lib.Lib.Frame.outside [(lo, hi)] a -> lo <= a < hi.
Proof using.
  intros lo hi a H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma w3a_not_outside2 : forall lo1 hi1 lo2 hi2 a, ~ lib.Lib.Frame.outside [(lo1, hi1); (lo2, hi2)] a ->
  lo1 <= a < hi1 \/ lo2 <= a < hi2.
Proof using.
  intros lo1 hi1 lo2 hi2 a H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_le_gt_dec lo1 a); destruct (Z_lt_ge_dec a hi1); destruct (Z_le_gt_dec lo2 a);
    destruct (Z_lt_ge_dec a hi2);
    first [lia | exfalso; apply H; split; [lia | split; [lia | exact I]]].
Qed.

Lemma w3a_raw_mrd : forall (m : word -> option byte) x b, m x = Some b -> lib.Lib.Mem.mrd rsegs m x = Some b.
Proof using. intros m x b H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma w3a_raw_wview : forall (m : word -> option byte) x b, m x = Some b -> wview rsegs m x <> None.
Proof using. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

Lemma w3a_not_img_high : forall a, Reusable.YG0f.kLowMemEnd <= a -> ~ Reusable.YG0d.in_img segs a.
Proof using segs_low. intros a Ha Hi. pose proof (segs_low a Hi) as H. lia. Qed.

Lemma w3a_mrd_raw : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa a) = Some b -> m (lib.Lib.Mem.wa a) = Some b.
Proof using.
  intros m a b Ha Hn H. unfold lib.Lib.Mem.mrd in H. destruct (m (lib.Lib.Mem.wa a)) as [b'|] eqn:E; [exact H|].
  exfalso. pose proof (Reusable.YCbq.seg_rom_none segs a Ha Hn) as R.
  assert (H' : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) by exact H.
  rewrite R in H'. discriminate.
Qed.

(* The image hull [0x10000, 0x5fe000) is covered by the segments (ProgBridge.rsegs_spans). *)
Lemma w3a_img_hull : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
Proof using.
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

Lemma w3a_mrd_munch : forall W (m m' : word -> option byte) x, lib.Lib.Frame.munch W m m' -> 0 <= x < 2 ^ 64 ->
  lib.Lib.Frame.outside W x -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x).
Proof using.
  intros W m m' x MU Hx Ho. unfold lib.Lib.Mem.mrd. rewrite (MU (lib.Lib.Mem.wa x)); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho.
Qed.

Lemma w3a_bytes_keep : forall (m m' : word -> option byte) a bs,
  lib.Lib.Mem.bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  lib.Lib.Mem.bytes_at rsegs m' a bs.
Proof using.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite K; [exact (H i Hi) | lia].
Qed.

Lemma w3a_addr_keep : forall (m m' : word -> option byte) p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof using.
  intros m m' p n (H1 & H2 & H3 & H) K. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b.
  split; [rewrite (K i Hi); exact Hb | exact Hk].
Qed.

Lemma w3a_stk_raw : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Frame.stk rsegs m lo hi.
Proof using.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [b Hb].
  split; [exact (w3a_raw_wview m _ b Hb) | exists b; exact (w3a_raw_mrd m _ b Hb)].
Qed.

Lemma w3a_wr_raw : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Mem.wr_at rsegs m a n.
Proof using.
  intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (H (a + i) ltac:(lia)) as [b Hb]. exact (w3a_raw_wview m _ b Hb).
Qed.

Lemma w3a_rw8 : forall m a v, lib.Lib.Mem.bytes_at rsegs m a (lib.Lib.Mem.le8 v) -> lib.Lib.Mem.wr_at rsegs m a 8 ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 v].
Proof using.
  intros m a v H Hw. split; [split; [exact (conj I I) | cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]; rewrite app_nil_r; exact H]|].
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. exact Hw.
Qed.

Lemma w3a_rw1 : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> m (lib.Lib.Mem.wa a) = Some b ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C1 b].
Proof using.
  intros m a b Ha Hb. split; [split; [exact (conj I I)|] |].
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
    exact (w3a_raw_mrd m _ b Hb).
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. apply w3a_wr_raw; [lia | lia|].
    intros x Hx. replace x with a by lia. exists b. exact Hb.
Qed.

Lemma w3a_cb_raw : forall (m : word -> option byte) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, m (lib.Lib.Mem.wa x) = Some b) ->
  exists junk, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n junk].
Proof using.
  intros m a n H0 H1 H.
  destruct (lib.Lib.Frame.stk_carve rsegs m a (a + Z.of_nat n) n (w3a_stk_raw m a (a + Z.of_nat n) H0 H1 H) ltac:(lia))
    as (_ & junk & Hj).
  replace (a + Z.of_nat n - Z.of_nat n) with a in Hj by lia. exists junk. exact Hj.
Qed.

Lemma w3a_bytes_of_mrd : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x) = Some b) ->
  exists bs, length bs = n /\ lib.Lib.Mem.bytes_at rsegs m a bs.
Proof using.
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
Lemma w3a_spill_A : forall regs m off v A, B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 ->
  0 <= off <= 512 -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.q64 m (A + off) v.
Proof using.
  intros regs m off v A HA HA0 HA1 Hoff (A' & HA' & Hq).
  unfold B.ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
  apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
  change (bv_modulus 64) with (2 ^ 64) in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat Pos.of_succ_nat] in Hq1.
  pose proof w3a_P64 as P64. rewrite P64 in HA', HA1, Hq1.
  assert (E : A = A') by (Z.div_mod_to_equations; lia). subst A'. exact Hq.
Qed.

Lemma w3a_spill_keep : forall regs R (m m' : word -> option byte) off v A,
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 -> 0 <= off <= 512 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill R m' off v.
Proof using.
  intros regs R m m' off v A HA HA0 HA1 Hoff E9 K Hs.
  pose proof (w3a_spill_A regs m off v A HA HA0 HA1 Hoff Hs) as Hq.
  exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact HA|].
  apply (w3a_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

(* The carried bundle PRO across a memory step that keeps [A, A + 512) and our[]'s shadow byte. *)
Lemma w3a_PRO_keep : forall fr regs R (m m' : word -> option byte) A,
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  (forall i, 0 <= i < 6 -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (fr + 2624 + i))) =
                           lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (fr + 2624 + i)))) ->
  B.ACtlCutP.PRO fr regs m -> B.ACtlCutP.PRO fr R m'.
Proof using.
  intros fr regs R m m' A HA HA0 HA1 E9 K KS
    ((P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11) & P12 & P13 & P14 & P15).
  assert (SK8 : forall off v, 0 <= off <= 440 -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill R m' off v).
  { intros off v Hoff Hs. apply (w3a_spill_keep regs R m m' off v A HA HA0 HA1 ltac:(lia) E9); [|exact Hs].
    intros x Hx. apply K. lia. }
  unfold B.ACtlCutP.PRO, B.ACtlCutP.PRA.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))
    (conj _ (conj _ (conj (w3a_addr_keep m m' _ _ P14 KS) _))));
    apply SK8; first [lia | assumption].
Qed.

(* A shadow_rw_on region after a silent run whose written bytes are present afterwards (wmono keeps wview; outside
   the write set the byte is unchanged, inside it the run's own presence fact gives it). *)
Lemma w3a_srw_on_run : forall (P : Z -> Prop) (m m' : word -> option byte) Wr,
  B.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.munch Wr m m' -> lib.Lib.Frame.wmono rsegs m m' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a -> exists b, m' (lib.Lib.Mem.wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof using.
  intros P m m' Wr HSW MU WM HW a Hp Ha.
  destruct (HSW a Hp Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  pose proof (B.AsanRTFacts.in_shadow_range a Ha) as Hr.
  destruct (w3a_outside_dec Wr a) as [H|H].
  - exists b. rewrite (w3a_mrd_munch Wr m m' a MU ltac:(lia) H). exact Hb.
  - destruct (HW a H) as (b' & Hb'). exists b'. exact (w3a_raw_mrd _ _ _ Hb').
Qed.

(* ctl_rt_C (at the same layout and state) after a silent run whose written bytes lie outside the image and are
   present afterwards: the cells and the read-only bytes are image bytes the run keeps; both shadow regions by
   w3a_srw_on_run. *)
Lemma w3a_ctlrt_run : forall ly S (m m' : word -> option byte) Wr,
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch Wr m m' -> lib.Lib.Frame.wmono rsegs m m' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a -> ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof using.
  intros ly S m m' Wr (HAC & HSWC & HSWI & HRO) MU WM HW.
  assert (KI : forall x, 0 <= x < 2 ^ 64 -> ~ ~ Reusable.YG0d.in_img segs x ->
             lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)).
  { intros x Hx Hi. apply (w3a_mrd_munch Wr); [exact MU | exact Hx |].
    destruct (w3a_outside_dec Wr x) as [H|H]; [exact H|]. exfalso. exact (Hi (proj1 (HW x H))). }
  assert (HWp : forall a, ~ lib.Lib.Frame.outside Wr a -> exists b, m' (lib.Lib.Mem.wa a) = Some b)
    by (intros a Ha; exact (proj2 (HW a Ha))).
  pose proof w3a_P64 as P64.
  split; [|split; [|split]].
  - unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells in HAC |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; (eapply w3a_bytes_keep; [eassumption|]); intros x Hx;
      (apply KI; [| intros Hn; apply Hn; apply w3a_img_hull]);
      rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx;
      unfold B.AsanRT.CELL_K, B.AsanRT.UAR, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.CANPOISON,
        B.AsanRT.HIEND, B.AsanRT.MIDBEG, B.AsanRT.MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
        B.AsanRT.GOT_CELL_K, B.AsanRT.GOT_UAR, B.AsanRT.GOT_REPLACE, B.AsanRT.GOT_HIEND, B.AsanRT.GOT_MIDBEG,
        B.AsanRT.GOT_MIDEND, B.AsanRT.GOT_REAL_MEMSET in Hx; lia.
  - exact (w3a_srw_on_run _ m m' Wr HSWC MU WM HWp).
  - exact (w3a_srw_on_run _ m m' Wr HSWI MU WM HWp).
  - unfold B.ACtlK.ro_agree_at in HRO |- *. intros a Ha. rewrite <- (HRO a Ha).
    pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    assert (E : lib.Lib.Mem.wa (bv_unsigned a) = a) by (unfold lib.Lib.Mem.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
    rewrite <- E. apply KI; [lia|]. intros Hn. unfold lib.Lib.Mem.ro_addr in Ha.
    assert (Hn' : find_segment rsegs (bv_unsigned a) 1 = None) by exact (Reusable.YCbq.find_segment_none segs _ Hn).
    rewrite Hn' in Ha. discriminate.
Qed.

(* ctl_rt_C at any own6 cut state of the walk: B.ProgWorldCtlRtC.ctl_rt_C_of_AR on the journal's AR (route (C): no
   AR_states_vis0_shadow, no AR_states_owned_ro); its arodata_okP premise is ctl_base's arodata_okS at the entry view
   (ProgWorld.arodata_okP_of_S) moved along the journal (APostBase.arodata_ok_journalP, under RELRO_IMG and RO_OFL;
   the owner's route, 06:46Z). *)
Lemma w3a_ctlrt : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof using LAWS TFIB_SYMS RELRO_IMG RO_OFL.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 (proj1 HJ)).
  destruct HB as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  apply (Reusable.APostBase.arodata_ok_journalP (SK := SK) (RO := RO_OFL) segs RLO RHI RELRO_IMG B _ _ FP _ _ _ _ _
           own ly3 S3 W3 mem3 md3 k HJ).
  exact (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro (Z.le_refl _) (Z.le_refl _)).
Qed.

(* A sub-region of an owned frame's shadow, on the normalized memory: route (C)'s cut_shadow (F) disjunct of
   ctl_rt_C (B.ShadowRwOn.shadow_rw_on_mono), moved to MemNorm.normalize by B.ShadowRwOnT.shadow_rw_on_normalize
   under ctl_rt_C's ro_agree. *)
Lemma w3a_srw_frame_norm : forall ly S (m : word -> option byte) (cid pos : Z) (P : Z -> Prop),
  B.ACtlRtC.ctl_rt_C B ly S m -> In (cid, pos) (Reusable.YG01.frames S) ->
  (forall a, P a ->
     Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly cid pos) <= a <
     Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly cid pos) + Reusable.YG00.fs_frame_bytes cid / 8) ->
  B.ShadowRwOn.shadow_rw_on P (B.MemNorm.normalize rsegs m).
Proof using.
  intros ly S m cid pos P (_ & HSWC & _ & HRO) Hin HP.
  apply (B.ShadowRwOnT.shadow_rw_on_normalize P m HRO).
  apply (B.ShadowRwOn.shadow_rw_on_mono (B.ACtlRtC.cut_shadow B ly S) P m); [|exact HSWC].
  intros a Ha. left. exists cid, pos. exact (conj Hin (HP a Ha)).
Qed.

(* The journal after a silent run (YCbq.ajournal_exec) whose written bytes are journal-writable. *)
Lemma w3a_after_run : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k
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
Proof using LAWS segs_low.
  intros cx ly3 S3 W3 mem3 md3 k m' md' Wr HJ MU Hhid Hsame HW.
  refine (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
            (fun a => ~ lib.Lib.Frame.outside Wr a) HJ _ _ Hhid Hsame _).
  - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (w3a_outside_dec Wr (bv_unsigned x)) as [H|H]; [exact H | exfalso; exact (Hx H)].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (w3a_outside_dec Wr (bv_unsigned x)) as [H|H]; [rewrite (MU x H); exact Hx|].
    destruct (HW _ H) as ((b & Hb) & _). unfold lib.Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
    rewrite Hb. discriminate.
  - intros a Ha. exact (proj2 (HW a Ha)).
Qed.

Lemma w3a_awr_fsh : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) ->
  B.ACtlCutP.Sfr fr <= a < B.ACtlCutP.Sfr fr + 512 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 (B.ACtlCut.own6 cx) a.
Proof using.
  intros cx ly3 fr STK sp0 bl0 blc a Efr Ha. right. right. right.
  exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity|]. right. rewrite <- Efr.
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
Qed.

Lemma w3a_awr_fr : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) -> fr <= a < fr + 4096 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 (B.ACtlCut.own6 cx) a.
Proof using.
  intros cx ly3 fr STK sp0 bl0 blc a Efr Ha. right. right. right.
  exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity|]. left. rewrite <- Efr.
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

Lemma w3a_awr_stk : forall ly3 own STK sp0 bl0 blc a, sp0 - STK <= a < sp0 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 own a.
Proof using. intros ly3 own STK sp0 bl0 blc a Ha. left. exact Ha. Qed.

(* Step C0 for an own6 cut: the frame's placement and presence, the frame shadow's presence, the stack window's
   presence and placement, all from the journal (its AR, YG0d's AR_frames_law, astk_ok, the window clause) and
   the shell's frame law. *)
Lemma w3a_cut6 : forall (cx : B.ACtlCut.ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
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
Proof using LAWS.
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
    exfalso. apply (Himg (Z.max fr 0x10000)); [lia | apply w3a_img_hull; lia]. }
  split; [exact Himg|]. split; [intros a Ha; exact (proj1 (Hfb a Ha))|].
  split.
  { intros a Ha. pose proof (proj1 (Hfsh (a - B.ACtlCutP.Sfr fr) ltac:(lia))) as H.
    replace (Reusable.YG0f.shadow_addr fr + (a - B.ACtlCutP.Sfr fr)) with a in H; [exact H|].
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.ACtlCutP.Sfr, B.AsanRT.shadow_addr,
      B.AsanRT.ASAN_K. lia. }
  split; [exact H16|]. split; [lia|]. split; [lia|]. exact Hpres.
Qed.

(* The machine-stack range of the layout at an own6 cut (the journal's astk_ok at the entry layout, which layout_le
   keeps). *)
Lemma w3a_stk_ly : forall (cx : B.ACtlCut.ctlcx) k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YM05.alloc_ceiling <= Reusable.YG0f.ly_stk_lo ly3 /\
  Reusable.YG0f.ly_stk_lo ly3 + Reusable.YCfn.LLVMF_STK <= B.ACtlCut.c_sp cx /\
  B.ACtlCut.c_sp cx <= Reusable.YG0f.ly_stk_hi ly3 /\ Reusable.YG0f.ly_stk_hi ly3 <= 2 ^ 47.
Proof using.
  intros cx k ly3 S3 W3 mem3 md3 HJ.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El & Eh & _).
  destruct Hstk as (_ & _ & Hc & Hlo & Hhi & H47 & _).
  rewrite El, Eh. split; [exact Hc|]. split; [exact Hlo|]. split; [exact Hhi | exact H47].
Qed.

Lemma w3a_vis : forall (W : Reusable.YA0n.world segs) mem lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof using.
  intros W mem lo len H0 H1 H. apply B.ProgBridge.rng_of_visible. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (proj1 (H a Ha)).
Qed.

Lemma w3a_sh_off : forall fr off i, fr mod 8 = 0 -> off mod 8 = 0 -> 0 <= i < 8 ->
  B.AsanRT.shadow_addr (fr + off + i) = B.ACtlCutP.Sfr fr + off / 8.
Proof using.
  intros fr off i Hf Ho Hi. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. pose proof (Z.div_mod off 8 ltac:(lia)) as E2.
  rewrite Hf in E1. rewrite Ho in E2.
  replace (fr + off + i) with (i + (fr / 8 + off / 8) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small i 8) by lia. lia.
Qed.

Lemma w3a_kn_shadow : forall i, 0 <= i < 112 ->
  2147450880 + 81584 <= B.AsanRT.shadow_addr (B.ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597.
Proof using.
  intros i Hi. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.KNA.KIND_NAME.
  split; Z.div_mod_to_equations; lia.
Qed.

(* The carried bundle FRAC across a memory step that keeps the registers it pins, the stack words above sp and the
   frame header, and leaves the 392 frame-shadow bytes readable. *)
Lemma w3a_FRAC_keep : forall (cx : B.ACtlCut.ctlcx) fr sel regs R (m m' : word -> option byte),
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
Proof using.
  intros cx fr sel regs R m m' (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 &
    HAS & HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & (sh & Hsh & Hshl) & Hsaved &
    Htr)
    E2 E3 E4 E8 E9 E19 E26 KS KF KSh.
  pose proof w3a_P64 as P64.
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
    { intros a v H1 H2 Hq. apply (w3a_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KS. lia. }
    refine (conj (HQ _ _ _ _ Hq336) (conj (HQ _ _ _ _ Hq48) (conj (HQ _ _ _ _ Hq40)
      (conj _ (conj _ (conj _ (conj _ _)))))));
      try lia.
    + apply (w3a_bytes_keep m m' _ _ Hqh0). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + apply (w3a_bytes_keep m m' _ _ Hqh16). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + change (Z.to_nat B.ACtlCutP.FRAME_SHADOW) with 392%nat in Hshl |- *.
      destruct Hsh as (Hs0 & Hs1 & _). rewrite Hshl in Hs1.
      destruct (w3a_bytes_of_mrd m' 392 (B.ACtlCutP.Sfr fr) Hs0 Hs1 KSh) as (sh' & Hl & Hb).
      exists sh'. split; [exact Hb | exact Hl].
    + assert (Hlen : length (B.ACtlCutP.saved_bytes cx) = 104%nat).
      { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
      apply (w3a_bytes_keep m m' _ _ Hsaved). rewrite Hlen. intros x Hx. apply KS. lia.
    + apply (w3a_bytes_keep m m' _ _ Htr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
Qed.

Lemma w3a_bv_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof using.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma w3a_signed_nonneg : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof using.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of a frame address, by its offset from the 8-aligned frame base. *)
Lemma w3a_sh_frame : forall fr x, fr mod 8 = 0 -> fr <= x ->
  B.AsanRT.shadow_addr x = B.ACtlCutP.Sfr fr + (x - fr) / 8 /\
  8 * ((x - fr) / 8) <= x - fr < 8 * ((x - fr) / 8) + 8.
Proof using.
  intros fr x Hf Hx. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. rewrite Hf in E1.
  pose proof (Z.div_mod (x - fr) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (x - fr) 8 ltac:(lia)) as E3.
  split; [|lia].
  assert (Ex : x = (x - fr) + (fr / 8) * 8) by lia. rewrite Ex at 1. rewrite Z.div_add by lia. lia.
Qed.

Lemma w3a_hull_in : forall x n s, 0 <= x -> 0 < n ->
  Reusable.YG0f.shadow_addr x / 8 * 8 <= s < Reusable.YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8.
Proof using.
  intros x n s Hx Hn Hs.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* T5 at a call site: ctrl's addressable (mrd of the shadow bytes) gives the core's range_addressable over the view,
   where the shadow bytes are visible (aview_vis_mrd). *)
Lemma w3a_range_addr : forall (W : Reusable.YA0n.world segs) mem p n,
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF p n.
Proof using.
  intros W mem p n (H1 & H2 & H3 & H) HV x Hx.
  destruct (H (x - p) ltac:(lia)) as (Ha & b & Hb & Hk). pose proof (HV (x - p) ltac:(lia)) as Hv.
  replace (p + (x - p)) with x in Ha, Hb, Hk, Hv by lia.
  assert (E : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  exists (bv_unsigned b). rewrite E. split.
  - rewrite (B.ProgWorld.aview_vis_mrd W mem _ Hv).
    change (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) with (Z_to_bv 64 (B.AsanRT.shadow_addr x)) in Hb.
    rewrite Hb. reflexivity.
  - unfold B.AsanRT.shadow_ok in Hk. unfold Reusable.YG0v.saddr_ok.
    destruct Hk as [Hk|Hk]; [left | right]; rewrite w3a_signed_nonneg by lia; lia.
Qed.

Lemma w3a_hull_vis : forall (W : Reusable.YA0n.world segs) mem x n, 0 <= x -> 0 < n ->
  (forall s, B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem s) ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n.
Proof using.
  intros W mem x n Hx Hn H s Hs. apply (Reusable.YCbq.aview_some_of_apresent segs). apply H.
  exact (w3a_hull_in x n s Hx Hn Hs).
Qed.

(* mrd at a visible address outside the written range, from a munch_vis post. *)
Lemma w3a_mvis : forall (H : word -> bool) WR (m m' : word -> option byte) x,
  munch_vis H WR m m' -> 0 <= x < 2 ^ 64 -> H (Z_to_bv 64 x) = false -> lib.Lib.Frame.outside WR x ->
  lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x).
Proof using.
  intros H WR m m' x MV Hx Hh Ho. apply MV; [exact Hh |]. rewrite lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho.
Qed.

Lemma w3a_q64_of_c8 : forall m a v, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 (Z_to_bv 64 v)] ->
  B.ACtlCutP.q64 m a v.
Proof using.
  intros m a v ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

Lemma w3a_bytes_of_cb : forall m a n bs, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n bs] ->
  lib.Lib.Mem.bytes_at rsegs m a bs.
Proof using.
  intros m a n bs ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

(* FSj at turn 0 (the all-zero first-fragment state, fs_body = []) across a step that keeps [fr + 2880, fr + 2885)
   and the object's shadow. *)
Lemma w3a_FSj0_keep : forall cx fr regs regs' (m m' : word -> option byte),
  B.ACtlCutP.FSj cx fr 0 regs m ->
  (forall x, fr + 2880 <= x < fr + 2885 ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  (forall i, 0 <= i < 40 -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (fr + 2880 + i))) =
                           lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (fr + 2880 + i)))) ->
  B.ACtlCutP.FSj cx fr 0 regs' m'.
Proof using.
  intros cx fr regs regs' m m' (H1 & H2 & H3 & H4 & H5) K KS.
  refine (conj _ (conj _ (conj _ (conj (w3a_addr_keep m m' _ _ H4 KS) H5)))).
  - unfold B.ACtlCutP.u32 in *. apply (w3a_bytes_keep m m' _ _ H1). rewrite lib.Lib.Mem.length_le4.
    intros x Hx. apply K. lia.
  - unfold B.ACtlCutP.b8 in *. apply (w3a_bytes_keep m m' _ _ H2). cbn [length Z.of_nat Pos.of_succ_nat].
    intros x Hx. apply K. lia.
  - change (B.ACtlCutP.SM.fs_body (B.ACtlCutP.SM.fst_at (B.ACtlCut.c_in cx) 0)) with (@nil byte) in H3 |- *.
    destruct H3 as (A0 & A1 & _). split; [exact A0|]. split; [exact A1|]. intros i Hi. cbn [length] in Hi. lia.
Qed.

(* The entry's gp (the core's afn_pre inside the lib pre). *)
Lemma w3a_gp : forall cx, B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B).
Proof using.
  intros cx ((HAF & _) & _). destruct HAF as (_ & _ & _ & Hgp & _). exact Hgp.
Qed.

Lemma w3a_amem_frame : forall fr d n, 4096 <= fr -> fr + 4096 <= lib.Reusable.YM05.alloc_ceiling ->
  (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/ Reusable.YG0f.kHighMemBeg <= fr) ->
  fr <= d -> d + n <= fr + 4096 -> Reusable.YG0d.amem_range d n.
Proof using.
  intros fr d n H0 H1 H2 H3 H4. pose proof Reusable.YG0f.ASAN_CEIL_range as (HC & _).
  unfold Reusable.YG0f.ASAN_CEIL in HC. unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd,
    Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd, Reusable.YG0f.kLowShadowBeg in *. lia.
Qed.

(* The class-6 fake frame lies above the image hull and the runtime data: fr = ly_F + fs_frame_off 6 pos with
   4096 <= ly_F and fs_frame_off 6 pos >= kFakeFramesOff + 6 * 2^20 (YG0s.frame_facts from the journal's AR). *)
Lemma w3a_fr_lo : forall (cx : B.ACtlCut.ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (B.ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  6332416 <= fr.
Proof using.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA.
  pose proof HJ as (HAR & Hly & _).
  assert (Hin : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  rewrite (HFA 6 (B.ACtlCut.c_fpos cx) (or_introl eq_refl)). unfold Reusable.YG0f.frame_addr.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite <- EF.
  destruct (Reusable.YG0s.frame_facts B ly3 S3 _ 6 (B.ACtlCut.c_fpos cx) (proj1 HAR) Hin)
    as (_ & _ & (HF0 & _) & _ & _ & Hoff & _).
  change (Reusable.YG0f.kFakeFramesOff + 6 * 2 ^ 20) with 6328320 in Hoff. lia.
Qed.

Lemma w3a_q64_of_bytes : forall m a bs, lib.Lib.Mem.bytes_at rsegs m a bs -> length bs = 8%nat ->
  exists v, 0 <= v < 2 ^ 64 /\ B.ACtlCutP.q64 m a v.
Proof using.
  intros m a bs H Hl. exists (bytes_le_to_Z bs).
  pose proof (lib.Lib.PropExec.bytes_le_to_Z_bound bs) as Hb. pose proof (lib.Lib.PropExec.bytes_le_to_Z_nonneg bs) as H0.
  rewrite Hl in Hb. change (8 * Z.of_nat 8) with 64 in Hb. split; [lia|].
  unfold B.ACtlCutP.q64, lib.Lib.Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. rewrite <- Hl.
  rewrite B.ACtlCutP.SFA.Z_to_le_bytes_to_Z. exact H.
Qed.

Lemma w3a_rwC1s : forall m a xs, lib.Lib.Mem.bytes_at rsegs m a xs ->
  lib.Lib.Mem.wr_at rsegs m a (Z.of_nat (length xs)) -> lib.Lib.Step.rw_cells rsegs m a (map lib.Lib.Cells.C1 xs).
Proof using.
  intros m a xs Hb Hw.
  assert (E1 : lib.Lib.Cells.cells_bytes (map lib.Lib.Cells.C1 xs) = xs)
    by (clear Hb Hw; induction xs as [|x xs IH]; cbn; [reflexivity | rewrite IH; reflexivity]).
  assert (E2 : lib.Lib.Cells.cells_size (map lib.Lib.Cells.C1 xs) = length xs)
    by (clear Hb Hw E1; induction xs as [|x xs IH]; cbn; [reflexivity | rewrite IH; reflexivity]).
  assert (E3 : lib.Lib.Cells.cells_wf (map lib.Lib.Cells.C1 xs))
    by (clear Hb Hw E1 E2; induction xs as [|x xs IH]; cbn; [exact I | split; [exact I | exact IH]]).
  split; [split; [exact E3 | rewrite E1; exact Hb] | rewrite E2; exact Hw].
Qed.

(* The normalized memory (MemNorm.normalize drops the read-only image bytes) keeps every byte off the image. *)
Lemma w3a_norm_raw : forall (m : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
  B.MemNorm.normalize rsegs m (lib.Lib.Mem.wa x) = m (lib.Lib.Mem.wa x).
Proof using.
  intros m x Hx Hn. unfold B.MemNorm.normalize, lib.Lib.Mem.ro_addr.
  rewrite lib.Lib.Mem.wa_unsigned by exact Hx.
  assert (E : find_segment rsegs x 1 = None) by exact (Reusable.YCbq.find_segment_none segs x Hn).
  rewrite E. reflexivity.
Qed.

Lemma w3a_asan_norm : forall m, B.ACtlK.ro_agree_at m -> B.AsanRT.asan_cells m ->
  B.AsanRT.asan_cells (B.MemNorm.normalize rsegs m).
Proof using.
  intros m Hro H. unfold B.AsanRT.asan_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; apply (B.MemNorm.bytes_at_normalize rsegs m _ _ Hro); assumption.
Qed.

(* A footprint run on the normalized memory, lifted to the world walk from the real memory (MemNormF's
   evtF_normalize_ro under ro_agree, then YA0nR.SRr_fevt_hid at the caller's footprint). *)
Lemma w3a_SRr_norm : forall (W : Reusable.YA0n.world segs) (R : bvmap 5 word) (pc : word) mem md RNG
    (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  B.ACtlK.ro_agree_at mem ->
  Lib.ExecF.evtF rsegs RNG P (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs pc lib.Reusable.YK11.fp_csr None
    (B.MemNorm.normalize rsegs mem) (lib.Reusable.YK11.seg_rom segs)) ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall s s0 md', P s0 -> B.MemNorm.ms_rel rsegs s s0 -> B.MemNorm.ro_same rsegs mem (ms_mem s) ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem s x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg s md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs pc lib.Reusable.YK11.fp_csr None
    mem (lib.Reusable.YK11.seg_rom segs)) md) Q.
Proof using Hwx.
  intros W R pc mem md RNG P Q Hro Hev Hfp K.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W _ md RNG).
  - apply B.ProgBridge.fevt_of_evtF. exact (B.MemNormF.evtF_normalize_ro RNG P R _ pc _ None mem _ Hro Hev).
  - exact Hfp.
  - intros s md' (s0 & HP & Hrel & Hro') Hhid Hsame. exact (K s s0 md' HP Hrel Hro' Hhid Hsame).
Qed.

Lemma w3a_ms_rel_MS : forall s R F pc fc rv m0 ro,
  B.MemNorm.ms_rel rsegs s (lib.Lib.MState.MS R F pc fc rv m0 ro) ->
  s = lib.Lib.MState.MS R F pc fc rv (ms_mem s) ro /\ B.MemNorm.mem_rel rsegs (ms_mem s) m0.
Proof using.
  intros [r fr pcv svc rsv fcs mm rom] R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn in E1, E2, E3, E4, E5, E6, E7, E8. subst. split; [reflexivity | exact E8].
Qed.

(* V1 for a window of the machine stack: AR's zero-shadow law on the stack range [ly_stk_lo, ly_stk_hi) (YG0n
   zero_shadow_ranges' first entry) makes every byte of an interior window addressable. *)
Lemma w3a_stk_addr : forall ly S (W : Reusable.YA0n.world segs) mem md p n,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YG0f.ly_stk_lo ly + 8 <= p -> p + n + 16 <= Reusable.YG0f.ly_stk_hi ly -> 0 <= n ->
  Reusable.YG0f.kHighMemBeg <= Reusable.YG0f.ly_stk_lo ly -> Reusable.YG0f.ly_stk_hi ly <= 2 ^ 47 ->
  B.AsanRT.addressable mem p n.
Proof using LAWS segs_low.
  intros ly S W mem md p n HAR H1 H2 Hn H3 H4. pose proof w3a_P64 as P64.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof (Reusable.YG0d.al_zshadow segs B LAWS ly S W mem md
                (Reusable.YG0f.ly_stk_lo ly, Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) HAR
                (or_introl eq_refl)) as HZ.
  cbn [fst snd] in HZ. unfold Reusable.YG0f.kHighMemBeg in H3.
  split; [lia|]. split; [exact Hn|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
  intros i Hi.
  assert (Hj : 0 <= (p + i) / 8 - Reusable.YG0f.ly_stk_lo ly / 8 <
                 (Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) / 8)
    by (clear - H1 H2 Hn Hi H3 H4; Z.div_mod_to_equations; lia).
  pose proof (HZ _ Hj) as Hv.
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (Reusable.YG0f.ly_stk_lo ly) +
                 ((p + i) / 8 - Reusable.YG0f.ly_stk_lo ly / 8) = B.AsanRT.shadow_addr (p + i))
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Es in Hv. set (sa := B.AsanRT.shadow_addr (p + i)) in *.
  assert (Hsa : 2147450880 <= sa < 2 ^ 64)
    by (unfold sa, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - H1 H2 Hn Hi H3 H4 P64; Z.div_mod_to_equations; lia).
  assert (Hni : ~ Reusable.YG0d.in_img segs sa) by (apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. cbv beta in Hv.
  pose proof (Reusable.YCbq.seg_rom_none segs sa ltac:(lia) Hni) as R0.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 sa)); [| destruct (mem (Z_to_bv 64 sa)) as [b|] eqn:Eb];
    cbn [option_map] in Hv.
  - rewrite R0 in Hv. cbn [option_map] in Hv. discriminate.
  - injection Hv as Hv. split.
    + unfold B.AsanRT.app_mem, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. right. lia.
    + exists b. split; [exact (w3a_raw_mrd mem _ b Eb)|]. left.
      unfold bv_signed. rewrite Hv. reflexivity.
  - rewrite R0 in Hv. cbn [option_map] in Hv. discriminate.
Qed.

Lemma w3a_wview_raw : forall (m : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
  wview rsegs m (lib.Lib.Mem.wa x) <> None -> exists b, m (lib.Lib.Mem.wa x) = Some b.
Proof using.
  intros m x Hx Hn H. unfold wview in H. destruct (m (lib.Lib.Mem.wa x)) as [b|]; [exists b; reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned in H by exact Hx.
  assert (E : find_segment rsegs x 1 = None) by exact (Reusable.YCbq.find_segment_none segs x Hn).
  rewrite E in H. exfalso. exact (H eq_refl).
Qed.

Lemma w3a_wmono_raw : forall (m m' : word -> option byte) x, lib.Lib.Frame.wmono rsegs m m' ->
  0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
  (exists b, m (lib.Lib.Mem.wa x) = Some b) -> exists b, m' (lib.Lib.Mem.wa x) = Some b.
Proof using.
  intros m m' x WM Hx Hn [b Hb]. apply (w3a_wview_raw m' x Hx Hn). apply WM. exact (w3a_raw_wview m _ b Hb).
Qed.

Lemma w3a_bytes_rep : forall (m : word -> option byte) a (b : byte) (k o l : nat),
  lib.Lib.Mem.bytes_at rsegs m a (repeat b k) -> (o + l <= k)%nat ->
  lib.Lib.Mem.bytes_at rsegs m (a + Z.of_nat o) (repeat b l).
Proof using.
  intros m a b k o l (H0 & H1 & H) Hol. rewrite repeat_length in H1.
  split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
  replace (a + Z.of_nat o + Z.of_nat i) with (a + Z.of_nat (o + i)) by lia.
  rewrite H by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
Qed.

(* An 8-aligned object whose shadow bytes are k zeros is addressable on its first 8k bytes. *)
Lemma w3a_addr_zero : forall (m : word -> option byte) p n (k : nat), 0 <= p -> p mod 8 = 0 ->
  p + n <= B.AsanRT.APPMEM_END -> 0 <= n <= 8 * Z.of_nat k -> (forall i, 0 <= i < n -> B.AsanRT.app_mem (p + i)) ->
  lib.Lib.Mem.bytes_at rsegs m (B.AsanRT.shadow_addr p) (repeat (Z_to_bv 8 0) k) ->
  B.AsanRT.addressable m p n.
Proof using.
  intros m p n k H0 H8 H1 Hn Happ (_ & _ & Hb).
  split; [exact H0|]. split; [lia|]. split; [exact H1|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists (Z_to_bv 8 0). split.
  - assert (Hj : (Z.to_nat (i / 8) < k)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). clear - Hi Hn. Z.div_mod_to_equations. lia. }
    assert (E : B.AsanRT.shadow_addr (p + i) = B.AsanRT.shadow_addr p + Z.of_nat (Z.to_nat (i / 8))).
    { rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold B.AsanRT.shadow_addr.
      pose proof (Z.div_mod p 8 ltac:(lia)) as Ep. rewrite H8 in Ep.
      replace (p + i) with (i + (p / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
    rewrite E. rewrite Hb by (rewrite repeat_length; exact Hj). apply nth_error_repeat. exact Hj.
  - unfold B.AsanRT.shadow_ok. left. reflexivity.
Qed.

(* FSj at turn 0 from the memset's 40 zero bytes at fr + 2880 and their addressability (the all-zero first-fragment
   state SM.fs0; image A's Tac_bp.bp_fsj0, over ACtlCutP's names). *)
Lemma w3a_FSj0_zero : forall cx fr regs (m : word -> option byte),
  lib.Lib.Mem.bytes_at rsegs m (fr + 2880) (repeat (Z_to_bv 8 0) 40) -> B.AsanRT.addressable m (fr + 2880) 40 ->
  B.ACtlCutP.FSj cx fr 0 regs m.
Proof using.
  intros cx fr regs m Hb Had.
  unfold B.ACtlCutP.FSj, B.ACtlCutP.FSb, B.ACtlCutP.u32, B.ACtlCutP.b8.
  change (B.ACtlCutP.SM.fst_at (B.ACtlCut.c_in cx) 0) with B.ACtlCutP.SM.fs0.
  change (B.ACtlCutP.SM.t_FG (B.ACtlCut.c_in cx) 0) with B.ACtlCutP.SM.z72.
  unfold B.ACtlCutP.SM.fs0. cbn [B.ACtlCutP.SM.fs_have B.ACtlCutP.SM.fs_n B.ACtlCutP.SM.fs_body].
  pose proof (w3a_bytes_rep m (fr + 2880) (Z_to_bv 8 0) 40 0 4 Hb ltac:(lia)) as H4.
  pose proof (w3a_bytes_rep m (fr + 2880) (Z_to_bv 8 0) 40 4 1 Hb ltac:(lia)) as H1.
  pose proof (w3a_bytes_rep m (fr + 2880) (Z_to_bv 8 0) 40 5 0 Hb ltac:(lia)) as H0.
  replace (fr + 2880 + Z.of_nat 0) with (fr + 2880) in H4 by lia.
  replace (fr + 2880 + Z.of_nat 4) with (fr + 2884) in H1 by lia.
  replace (fr + 2880 + Z.of_nat 5) with (fr + 2885) in H0 by lia.
  split; [change (lib.Lib.Mem.le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4); exact H4|].
  split; [exact H1|]. split; [exact H0|]. split; [exact Had|].
  unfold B.ACtlCutP.SM.FI. intros H. exfalso. vm_compute in H. discriminate H.
Qed.

(* The shadow of the machine stack is visible: AR's zero-shadow law on the stack range reads 0 there, and a hidden
   byte reads None (the shadow is off the image). *)
Lemma w3a_stk_sh_vis : forall ly S (W : Reusable.YA0n.world segs) mem md a,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YG0f.kHighMemBeg <= Reusable.YG0f.ly_stk_lo ly -> Reusable.YG0f.ly_stk_hi ly <= 2 ^ 47 ->
  Reusable.YG0f.ly_stk_lo ly + 8 <= a -> a + 16 <= Reusable.YG0f.ly_stk_hi ly ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr a)) = false.
Proof using LAWS segs_low.
  intros ly S W mem md a HAR H3 H4 H1 H2. pose proof w3a_P64 as P64.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof (Reusable.YG0d.al_zshadow segs B LAWS ly S W mem md
                (Reusable.YG0f.ly_stk_lo ly, Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) HAR
                (or_introl eq_refl)) as HZ.
  cbn [fst snd] in HZ. unfold Reusable.YG0f.kHighMemBeg in H3.
  assert (Hj : 0 <= a / 8 - Reusable.YG0f.ly_stk_lo ly / 8 <
                 (Reusable.YG0f.ly_stk_hi ly - Reusable.YG0f.ly_stk_lo ly) / 8)
    by (clear - H1 H2 H3 H4; Z.div_mod_to_equations; lia).
  pose proof (HZ _ Hj) as Hv.
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (Reusable.YG0f.ly_stk_lo ly) +
                 (a / 8 - Reusable.YG0f.ly_stk_lo ly / 8) = B.AsanRT.shadow_addr a)
    by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; lia).
  rewrite Es in Hv. set (sa := B.AsanRT.shadow_addr a) in *.
  assert (Hsa : 2147450880 <= sa < 2 ^ 64)
    by (unfold sa, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - H1 H2 H3 H4 P64; Z.div_mod_to_equations; lia).
  assert (Hni : ~ Reusable.YG0d.in_img segs sa) by (apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. cbv beta in Hv.
  pose proof (Reusable.YCbq.seg_rom_none segs sa ltac:(lia) Hni) as R0.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 sa)); [| reflexivity].
  cbn [option_map] in Hv. rewrite R0 in Hv. cbn [option_map] in Hv. discriminate.
Qed.

(* The 8-aligned shadow word cover of a stack window is visible. *)
Lemma w3a_stk_sh_cover : forall ly S (W : Reusable.YA0n.world segs) mem md p n t,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YG0f.kHighMemBeg <= Reusable.YG0f.ly_stk_lo ly -> Reusable.YG0f.ly_stk_hi ly <= 2 ^ 47 ->
  Reusable.YG0f.ly_stk_lo ly + 128 <= p -> p + n + 128 <= Reusable.YG0f.ly_stk_hi ly -> 0 < n ->
  (p / 8 + B.AsanRT.ASAN_K) / 8 * 8 <= t < ((p + n - 1) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 ->
  Reusable.YA0n.w_H W (Z_to_bv 64 t) = false.
Proof using LAWS segs_low.
  intros ly S W mem md p n t HAR H3 H4 H1 H2 Hn Ht.
  unfold B.AsanRT.ASAN_K in Ht. unfold Reusable.YG0f.kHighMemBeg in H3.
  assert (Et : B.AsanRT.shadow_addr (8 * (t - 2147450880)) = t).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  rewrite <- Et. apply (w3a_stk_sh_vis ly S W mem md _ HAR); try lia; unfold Reusable.YG0f.kHighMemBeg; try lia;
    clear - H1 H2 H3 H4 Hn Ht; Z.div_mod_to_equations; lia.
Qed.

(* seg_P1 and seg_P1_bfc share one proof: the same run from either entry (P1F.p1_pc_pre_F_on), the same body
   (C_B81c58's and C_B81c60's bodies are one text), the same call and the same exit cut. *)
Lemma w3a_P1 : forall POST pc, (pc = 0x81c58 \/ pc = 0x81c60) -> CF POST C_B81ca8 ->
  forall (cx : B.ACtlCut.ctlcx) (idx : list Z) (fr k : Z) ly3 S3 W3 (regs3 : bvmap 5 word)
         (mem3 : word -> option byte) md3,
    B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
    Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
      (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
      (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
    Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
    (forall cid pos, In (cid, pos) (B.ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
    k <= 14 ->
    B.ACtlCut.cut_body C_B81c58 cx idx (Reusable.YG0d.ablocks B ly3 S3) fr fr regs3 mem3 ->
    B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
    Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs pc regs3 mem3 md3) (POST cx).
Proof using Hwx LAWS segs_low ASF8 TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
  intros POST pc Hpc HCA cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81c58 B.ACtlCut.cut_body] in HBODY.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & Ha0 & HPRO & (Q & HQs & HQ1 & HQ2) & H56 & H176 & H208 & H64 &
    HCUR & HKN).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof (w3a_fr_lo cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA) as Hfrlo.
  pose proof HRT as (HAC & HSWC & HSWI & HRO).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof Hfrlh as Hfrlh0. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  assert (Hr9' : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (Hr19' : lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 Sh) by exact Hr19.
  pose proof (w3a_spill_A regs3 mem3 8 Q A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) HQs) as Hq8.
  assert (HQr : 0 <= Q < 2 ^ 64) by lia.
  assert (VF : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hfrp x Hx))).
  assert (VS : forall x, Sh <= x < Sh + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hshp x Hx))).
  assert (VK : forall x, S - 32768 <= x < S -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hstkp x Hx))).
  assert (NIH : forall x, 2147450880 <= x -> ~ Reusable.YG0d.in_img segs x)
    by (intros x Hx; apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  assert (SH3 : forall x, Sh <= x < Sh + 512 -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hshp x Hx))).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (HshF : Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx)) = Sh).
  { rewrite <- Efr. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh. lia. }
  (* ---- the run 0x81c58 / 0x81c60 -> 0x55144 (P1F.p1_pc_pre_F_on) on the normalized memory ---- *)
  set (n3 := B.MemNorm.normalize rsegs mem3).
  assert (NR : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
                 (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, n3 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hni Hb. unfold n3. rewrite (w3a_norm_raw mem3 x Hx Hni). exact Hb. }
  destruct (w3a_bytes_of_mrd n3 19 (Sh + 272) ltac:(lia) ltac:(lia)) as (xs & Hxl & Hxs).
  { intros x Hx. destruct (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))) as [b Hb].
    exists b. exact (w3a_raw_mrd n3 _ b Hb). }
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (w3a_SRr_norm W3 _ _ mem3 md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { exact HRO. }
  { eapply (P1F.p1_pc_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) pc) with (Sh := Sh) (Ab := A) (Q := Q)
      (xs := xs).
    - exact Hpc.
    - exact Hr19'.
    - exact Hr9'.
    - exact Ha0.
    - unfold B.AsanRT.RT_HI. lia.
    - lia.
    - lia.
    - exact HQ1.
    - lia.
    - intros i Hi. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
        B.AsanRT.HIGHMEM_BEG. rewrite ESh in HQ1, HQ2.
      clear - HQ1 HQ2 Hi Hfrlh Hfr4 Hfrc HC1. Z.div_mod_to_equations. lia.
    - exact Hxl.
    - apply w3a_rwC1s; [exact Hxs |]. rewrite Hxl. apply w3a_wr_raw; [lia | lia |].
      intros x Hx. exact (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))).
    - exact (B.AsanRTFacts.ro_c8 n3 (A + 8) _ (B.MemNorm.bytes_at_normalize rsegs mem3 _ _ HRO Hq8)).
    - exact (B.MemNorm.mem_inv_normalize rsegs mem3).
    - exact (w3a_asan_norm mem3 HRO HAC).
    - (* route (C): the callee window [Q, Q + 187) lies in the owned frame's shadow (cut_shadow (F)) *)
      refine (w3a_srw_frame_norm ly3 S3 mem3 6 (B.ACtlCut.c_fpos cx) _ HRT Hin6 _).
      intros a Ha. unfold P1F.p1_pc_pre_F_shadow_R in Ha. cbv beta in Ha. rewrite HshF.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hshp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros s s0 md1 HP Hrel Hro' Hhid Hsame1.
  destruct HP as (a2' & a3' & a4' & a5' & a6' & a7' & m1 & junkQ & Es0 & MU1 & WM1 & MI1 & AC1 & SR1 & RWQ1 & PRES1).
  subst s0.
  destruct (w3a_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es MR].
  set (m' := ms_mem s) in *. clearbody m'. rewrite Es. clear Es Hrel.
  pose proof (B.MemNorm.mem_rel_normalize rsegs mem3 HRO) as MRN.
  pose proof (B.MemNorm.munch_rel rsegs _ mem3 n3 m' m1 MRN MR Hro' MU1) as MU.
  pose proof (B.MemNorm.wmono_rel rsegs mem3 n3 m' m1 MRN MR Hro' WM1) as WM.
  assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (Sh + 272 <= x < Sh + 291) ->
            lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx H1. apply (w3a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside]. split; [exact H1 | exact I]. }
  assert (PM1 : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
            (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, m' (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx Hni Hb; exact (w3a_wmono_raw mem3 m' x WM Hx Hni Hb)).
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 m' md1 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k m' md1 _ HJ MU Hhid Hsame1).
    intros a Ha. apply w3a_not_outside1 in Ha.
    split; [apply PM1; [lia | apply NIH; lia | apply SH3; lia] | apply (w3a_awr_fsh cx ly3 fr _ _ _ _ a Efr); lia]. }
  (* ---- the call: __asan_set_shadow_f8 (Q, 187) by ASF8 at the journal's state ---- *)
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x55144) _ _ _ _] => set (R1 := R) end.
  assert (R1_1 : lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x81ca8) by reflexivity.
  assert (R1_2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R1_3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R1_4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R1_8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R1_9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite Hr9'; reflexivity).
  assert (R1_10 : lib.Reusable.YK11.getr R1 10 = Reusable.YG0d.w64 Q) by reflexivity.
  assert (R1_11 : lib.Reusable.YK11.getr R1 11 = Reusable.YG0d.w64 187) by reflexivity.
  assert (R1_19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite Hr19'; reflexivity).
  assert (R1_23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R1_25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R1_26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR1 : Reusable.YG0d.spZ R1 = S + (sp - S)).
  { unfold Reusable.YG0d.spZ in HspZ |- *. rewrite R1_2, HspZ. lia. }
  assert (Hgp1 : lib.Reusable.YK11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B))
    by (rewrite R1_3, Hr3; exact (w3a_gp cx HB)).
  assert (Htp1 : lib.Reusable.YK11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (rewrite R1_4; exact Hr4).
  assert (Ho16 : (sp - S) mod 16 = 0) by (clear - Hsp16 HS16; Z.div_mod_to_equations; lia).
  assert (RETOK : lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr R1 1)) by (rewrite R1_1; vm_compute; reflexivity).
  assert (Hecall : Reusable.YG0d.ecall_pre segs B ly3 S3 W3 R1 m' md1).
  { apply (Reusable.YCbq.ecall_pre_at segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 (sp - S) HJ1 HspR1 Ho16);
      [lia | rewrite HSTK; change Reusable.YG0d.ESTACK with 4096; lia | exact RETOK | exact Hgp1 | exact Htp1]. }
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x55144 R1 m' md1) (POST cx)).
  eapply (Reusable.YA0n.SRr_bind segs).
  { exact (ASF8 ly3 S3 W3 R1 m' md1 6 (B.ACtlCut.c_fpos cx) Q 187 Hecall Hin6 R1_10 R1_11 ltac:(lia)
             ltac:(rewrite HshF; lia)
             ltac:(rewrite HshF; change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia)). }
  intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HAR2 & Hpreg & Hsame2 & Hset & Hfrm & Hwin & Hpres2).
  pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT1).
  assert (HJ2 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 mem2 md2 k).
  { apply (Reusable.YCbq.ajournal_after_write segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md2
             (fun a => Q <= a < Q + 187) S3 (B.ACtlCut.own6 cx) HJ1 Hfrm Hpres2 Hsame2).
    - intros a Ha. left. apply (w3a_awr_fsh cx ly3 fr _ _ _ _ a Efr). lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs1.
    - exact HQT1. }
  assert (HRPF : rt_post_frame W3 m' mem2 [(Q, Q + 187)]).
  { split; [|exact Hpres2]. intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho1 & _).
    exact (Hfrm a Ha Ho1). }
  destruct (B.ProgWorld.ctl_post_set_shadow W3 m' mem2 Q 187 0xf8 ltac:(lia) ltac:(lia) ltac:(lia)
              (fun a Ha => conj (VS a ltac:(lia)) (PM1 a ltac:(lia) (NIH a ltac:(lia)) (SH3 a ltac:(lia))))
              Hset HRPF) as (MV & WMV & RWQ).
  assert (KV2 : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false -> ~ (Q <= x < Q + 187) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1. apply (w3a_mvis _ _ _ _ x MV Hx Hv). cbn [lib.Lib.Frame.outside]. split; [exact H1 | exact I]. }
  assert (KK : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false -> ~ (Q <= x < Q + 187) ->
             ~ (Sh + 272 <= x < Sh + 291) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. rewrite (KV2 x Hx Hv H1). exact (KEEP1 x Hx H2). }
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- R1_2; exact (Hpreg 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- R1_3; exact (Hpreg 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- R1_4; exact (Hpreg 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- R1_8; exact (Hpreg 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite <- R1_9; exact (Hpreg 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- R1_19; exact (Hpreg 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- R1_23; exact (Hpreg 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- R1_25; exact (Hpreg 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- R1_26; exact (Hpreg 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (Era : Reusable.YG0d.raZ R1 = 0x81ca8) by reflexivity.
  rewrite Era.
  (* C5: the exit cut B81ca8. *)
  unfold B.ACtlCut.ctl_from in HCA.
  apply (HCA cx idx fr k ly3 S3 W3 regs2 mem2 md2 HB);
    cbn [B.ACtlCutP.C_B81ca8 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - exact HJ2.
  - exact Hfr.
  - exact HFA.
  - exact Hk.
  - refine (conj Hperm (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + apply (w3a_FRAC_keep cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
      * intros x Hx. apply KK; [lia | apply VF; lia | lia | lia].
      * intros x Hx. destruct (Z_lt_le_dec x Q) as [HxQ|HxQ]; [|destruct (Z_lt_le_dec x (Q + 187)) as [HxQ'|HxQ']].
        -- rewrite (KV2 x ltac:(lia) (VS x ltac:(lia)) ltac:(lia)).
           destruct (PM1 x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))) as [b Hb].
           exists b. exact (w3a_raw_mrd _ _ _ Hb).
        -- destruct RWQ as ((_ & _ & _ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
           rewrite app_nil_r in Hb. change (Z.to_nat 187) with 187%nat in Hb.
           specialize (Hb (Z.to_nat (x - Q)) ltac:(rewrite repeat_length; lia)).
           rewrite nth_error_repeat in Hb by lia.
           replace (Q + Z.of_nat (Z.to_nat (x - Q))) with x in Hb by lia. eexists. exact Hb.
        -- rewrite (KV2 x ltac:(lia) (VS x ltac:(lia)) ltac:(lia)).
           destruct (PM1 x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))) as [b Hb].
           exists b. exact (w3a_raw_mrd _ _ _ Hb).
    + unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HOUR).
      rewrite B.ACtlCutP.SM.OUR_length. intros x Hx. apply KK; [lia | apply VF; lia | lia | lia].
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 56 (fr + 3040) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H56].
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
    + apply (w3a_PRO_keep fr regs3 regs2 mem3 mem2 A Hr9 ltac:(lia) ltac:(lia) E9); [| | exact HPRO].
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
      * intros i Hi. rewrite (w3a_sh_off fr 2624 i ltac:(lia) ltac:(reflexivity) ltac:(lia)).
        change (B.ACtlCutP.Sfr fr) with Sh. apply KK; [lia | apply VS; lia | lia | lia].
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H176].
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 208 (fr + 2768) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H208].
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 64 (fr + 3056) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H64].
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia].
    + destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
      refine (conj Hc0 (conj _ _)); [rewrite E23; exact Hc23 | rewrite E25; exact Hc25].
    + exact (ctl_kind_name_addressable ly3 S3 W3 mem2 md2 HAR2).
  - exact (w3a_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2).
Qed.

(* A byte visible in a world is visible in every later world (wle: the later hidden set is smaller). *)
Lemma w3a_vis_wle : forall (W W2 : Reusable.YA0n.world segs) x, Reusable.YA0n.wle W W2 ->
  Reusable.YA0n.w_H W x = false -> Reusable.YA0n.w_H W2 x = false.
Proof using.
  intros W W2 x Hle Hx. destruct (Reusable.YA0n.w_H W2 x) eqn:E; [|reflexivity].
  rewrite (Hle x E) in Hx. discriminate.
Qed.

(* A view equality at an address visible in both worlds is an mrd equality. *)
Lemma w3a_mrd_view_eq : forall (W W2 : Reusable.YA0n.world segs) (m m2 : word -> option byte) x,
  Reusable.YA0n.w_H W (Z_to_bv 64 x) = false -> Reusable.YA0n.w_H W2 (Z_to_bv 64 x) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) m2 x = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m x ->
  lib.Lib.Mem.mrd rsegs m2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x).
Proof using.
  intros W W2 m m2 x H1 H2 E.
  rewrite (B.ProgWorld.aview_vis_mrd W2 m2 x H2), (B.ProgWorld.aview_vis_mrd W m x H1) in E.
  change (lib.Lib.Mem.wa x) with (Z_to_bv 64 x).
  destruct (lib.Lib.Mem.mrd rsegs m2 (Z_to_bv 64 x)) as [b2|], (lib.Lib.Mem.mrd rsegs m (Z_to_bv 64 x)) as [b|];
    cbn [option_map] in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ctl_base's read-only data fact at any cut state, by the journal (the owner's route, 06:46Z); arodata_okP and
   arodata_okS have one body. *)
Lemma w3a_aro : forall (cx : B.ACtlCut.ctlcx) own ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k,
  B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof using RELRO_IMG RO_OFL.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  destruct HB as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  exact (Reusable.APostBase.arodata_ok_journalP (SK := SK) (RO := RO_OFL) segs RLO RHI RELRO_IMG B _ _ FP _ _ _ _ _
           own ly3 S3 W3 mem3 md3 k HJ (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro (Z.le_refl _) (Z.le_refl _))).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81c58 (0x81c58, own6, k <= 14) --S_P1--> B81ca8 (0x81ca8, own6, k <= 14).  Seg/P1.v seg_P1 :399.
   0x81c58 beqz a0,0x81c60 (taken: a0 = 0), li s2,-8, 14 stores of 0xf8 into Sh + 272 .. 276 / 282 .. 290,
   li a1,187, ld a0,8(s1) (Q = [A + 8]), jal __asan_set_shadow_f8 (Q, 187), return at 0x81ca8. *)
Lemma seg_P1 : forall POST, CF POST C_B81ca8 -> CF POST C_B81c58.
Proof using Hwx LAWS segs_low ASF8 TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
  intros POST HCA cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  exact (w3a_P1 POST 0x81c58 (or_introl eq_refl) HCA cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81c60 (0x81c60, own6, k <= 12) --S_P1_bfc--> B81ca8 (0x81ca8, own6, k <= 14).  Seg/P1.v seg_P1_bfc :410.
   The same run from the second entry (reached from S_R21_a5c's 0x81c0c beqz). *)
Lemma seg_P1_bfc : forall POST, CF POST C_B81ca8 -> CF POST C_B81c60.
Proof using Hwx LAWS segs_low ASF8 TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
  intros POST HCA cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81c60 B.ACtlCut.cut_kmax] in Hk.
  exact (w3a_P1 POST 0x81c60 (or_intror eq_refl) HCA cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA
           ltac:(lia) HBODY HRT).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81ca8 (0x81ca8, own6, k <= 14) --S_P2--> B81cb0 (0x81cb0, own6, k <= 14).  Seg/P2.v seg_P2 :90.
   sb s2,332(s3) (one frame-shadow byte), ld s8,56(s1) (s8 := [A + 56] = fr + 3040).  No call. *)
Lemma seg_P2 : forall POST, CF POST C_B81cb0 -> CF POST C_B81ca8.
Proof using Hwx LAWS segs_low.
  (* C0: the cut's facts. *)
  intros POST HCB cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81ca8 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body]
    in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & H56 & HPRO & H176 & H208 & H64 & HCUR & HKN).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr = 8 * (fr / 8)) by (Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  pose proof (w3a_spill_A regs3 mem3 56 (fr + 3040) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H56) as Hq56.
  pose proof (w3a_spill_A regs3 mem3 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H176) as Hq176.
  pose proof (w3a_spill_A regs3 mem3 208 (fr + 2768) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H208) as Hq208.
  destruct (Hshp (Sh + 332) ltac:(lia)) as [_ (xb & Hxb)].
  (* C1/C2: the run 0x81ca8 -> 0x81cb0 (P2F.p2_evt_F), lifted by YA0nR.SRr_fevt_hid at RNG_W. *)
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF. eapply (P2F.p2_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (Sh := Sh) (Ab := A) (v := fr + 3040) (xb := xb).
    - exact Hr19.
    - exact Hr9.
    - lia.
    - lia.
    - lia.
    - exact (w3a_rw1 mem3 (Sh + 332) xb ltac:(lia) Hxb).
    - exact (B.AsanRTFacts.ro_c8 mem3 (A + 56) _ Hq56).
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hshp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' (R & m' & Hms & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K24 & K23 & K25 & MU & WM & b332 & RD332)
    Hhid Hsame.
  subst ms'.
  assert (Hhid' : forall x, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) by exact Hhid.
  assert (E2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact K2.
  assert (E3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact K3.
  assert (E4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact K4.
  assert (E8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact K8.
  assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
  assert (E19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact K19.
  assert (E26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact K26.
  assert (E23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by exact K23.
  assert (E25 : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by exact K25.
  assert (E24 : lib.Reusable.YK11.getr R 24 = Z_to_bv 64 (fr + 3040)) by exact K24.
  (* the memory after the run: every byte but Sh + 332 is the old one *)
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (Sh + 332 <= x < Sh + 333) ->
            lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hnx. apply (w3a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside]. split; [exact Hnx | exact I]. }
  assert (RAWK : forall x, 0 <= x < 2 ^ 64 -> ~ (Sh + 332 <= x < Sh + 333) -> m' (lib.Lib.Mem.wa x) = mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hnx. apply MU. rewrite lib.Lib.Mem.wa_unsigned by exact Hx. cbn [lib.Lib.Frame.outside].
    split; [exact Hnx | exact I]. }
  assert (FRm : forall x, fr <= x < fr + 4096 -> exists b, m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. rewrite RAWK by lia. exact (proj2 (Hfrp x Hx)). }
  assert (STm : forall x, S - 32768 <= x < S -> exists b, m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. rewrite RAWK by lia. exact (proj2 (Hstkp x Hx)). }
  assert (W332 : exists b, m' (lib.Lib.Mem.wa (Sh + 332)) = Some b).
  { exists b332. apply (w3a_mrd_raw m' (Sh + 332) b332 ltac:(lia)); [| exact RD332].
    apply w3a_not_img_high. unfold Reusable.YG0f.kLowMemEnd. lia. }
  (* C5: the successor cut B81cb0 at the post state. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81cb0 R m' md') (POST cx)).
  unfold B.ACtlCut.ctl_from in HCB.
  apply (HCB cx idx fr k ly3 S3 W3 R m' md' HB);
    cbn [B.ACtlCutP.C_B81cb0 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - (* C3: the journal *)
    apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k m' md' [(Sh + 332, Sh + 333)] HJ MU Hhid' Hsame).
    intros a Ha. apply w3a_not_outside1 in Ha. replace a with (Sh + 332) by lia. split; [exact W332|].
    apply (w3a_awr_fsh cx ly3 fr _ _ _ _ (Sh + 332) Efr). lia.
  - exact Hfr.
  - exact HFA.
  - exact Hk.
  - (* the body of B81cb0 *)
    refine (conj Hperm (conj _ (conj Hn (conj _ (conj E24 (conj _ (conj _ (conj _ (conj _ _))))))))).
    + apply (w3a_FRAC_keep cx fr fr regs3 R mem3 m' HFRAC E2 E3 E4 E8 E9 E19 E26).
      * intros x Hx. apply KEEP; lia.
      * intros x Hx. apply KEEP; lia.
      * intros x Hx. destruct (Z.eq_dec x (Sh + 332)) as [->|Hne].
        -- exists b332. exact RD332.
        -- rewrite KEEP by lia. destruct (Hshp x ltac:(lia)) as [_ (b & Hb)]. exists b. exact (w3a_raw_mrd _ _ _ Hb).
    + unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 m' _ _ HOUR). rewrite B.ACtlCutP.SM.OUR_length.
      intros x Hx. apply KEEP; lia.
    + apply (w3a_PRO_keep fr regs3 R mem3 m' A Hr9 ltac:(lia) ltac:(lia) E9); [| | exact HPRO].
      * intros x Hx. apply KEEP; lia.
      * intros i Hi. rewrite (w3a_sh_off fr 2624 i ltac:(lia) ltac:(reflexivity) ltac:(lia)).
        fold Sh. apply KEEP; lia.
    + apply (w3a_spill_keep regs3 R mem3 m' 64 (fr + 3056) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9); [|exact H64].
      intros x Hx. apply KEEP; lia.
    + destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
      refine (conj Hc0 (conj _ _)); [rewrite E23; exact Hc23 | rewrite E25; exact Hc25].
    + apply (w3a_addr_keep mem3 m' _ _ HKN). intros i Hi. pose proof (w3a_kn_shadow i Hi) as Hk'.
      apply KEEP; [lia|]. rewrite ESh. destruct Hfrhull; lia.
    + destruct (w3a_cb_raw m' (fr + 2688) 38 ltac:(lia) ltac:(lia) (fun x Hx => FRm x ltac:(lia))) as (idb & Hidb).
      destruct (w3a_cb_raw m' (fr + 2768) 72 ltac:(lia) ltac:(lia) (fun x Hx => FRm x ltac:(lia))) as (jk & Hjk).
      destruct (w3a_cb_raw m' (fr + 2880) 40 ltac:(lia) ltac:(lia) (fun x Hx => FRm x ltac:(lia))) as (jf & Hjf).
      exists sp, A, idb, jk.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hidb (conj Hjk (ex_intro _ jf Hjf))))))))).
      * rewrite E2. exact Hr2.
      * rewrite E9. exact Hr9.
      * lia.
      * lia.
      * apply (w3a_bytes_keep mem3 m' _ _ Hq176). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KEEP; lia.
      * apply w3a_rw8.
        -- apply (w3a_bytes_keep mem3 m' _ _ Hq208). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KEEP; lia.
        -- apply w3a_wr_raw; [lia | lia | intros x Hx; apply STm; lia].
  - (* C4: ctl_rt_C at the same layout and state (a silent run) *)
    apply (w3a_ctlrt_run ly3 S3 mem3 m' [(Sh + 332, Sh + 333)] HRT MU WM).
    intros a Ha. apply w3a_not_outside1 in Ha. replace a with (Sh + 332) by lia. split; [|exact W332].
    apply w3a_not_img_high. unfold Reusable.YG0f.kLowMemEnd. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81cb0 (0x81cb0, own6, k <= 14) --S_P3--> B81d18 (0x81d18, own6, k <= 14).  Seg/P3.v seg_P3 :268.
   29 frame-shadow stores (Sh + 336 .. 340 = 00 00 00 00 06, Sh + 346 .. 354 = 0, Sh + 360 .. 364 = 0), li a2,40,
   ld a0,168(s1) (fr + 2880), li a1,0, jal __asan_memset; ld a0,176(s1) (fr + 2688), jal reac_identity_init. *)
Lemma seg_P3 : forall POST, CF POST C_B81d18 -> CF POST C_B81cb0.
Proof using Hwx LAWS segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable
  reac_identity_init_holds_F_on.
  (* C0 *)
  intros POST HD18 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81cb0 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body]
    in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & H24 & HPRO & H64 & HCUR & HKN &
    spv0 & A0 & idb & junk & Hg2 & Hg9 & HA0 & Hspv0 & Hq176 & Hrw208 & Hidb & Hjunk & junkf & Hjf).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof (w3a_fr_lo cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA) as Hfrlo.
  destruct (w3a_stk_ly cx k ly3 S3 W3 mem3 md3 HJ) as (HLc & HLlo & HLhi & HL47).
  pose proof HRT as (HAC & HSWC & HSWI & HRO).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp, HLlo.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof Hfrlh as Hfrlh0. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  assert (Hr9' : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (Hr19' : lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 Sh) by exact Hr19.
  assert (H24' : lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 (fr + 3040)) by exact H24.
  assert (EA0 : A0 = A) by (apply w3a_bv_inj; [lia | lia | rewrite <- Hg9; exact Hr9']).
  subst A0.
  pose proof HPRO as ((_ & _ & H168 & _) & _).
  pose proof (w3a_spill_A regs3 mem3 168 (fr + 2880) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H168) as Hq168.
  pose proof (w3a_spill_A regs3 mem3 64 (fr + 3056) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H64) as Hq64.
  pose proof (w3a_q64_of_c8 mem3 (A + 208) (fr + 2768) Hrw208) as Hq208.
  assert (VF : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hfrp x Hx))).
  assert (VS : forall x, Sh <= x < Sh + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hshp x Hx))).
  assert (VK : forall x, S - 32768 <= x < S -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hstkp x Hx))).
  assert (NIH : forall x, 2147450880 <= x -> ~ Reusable.YG0d.in_img segs x)
    by (intros x Hx; apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  assert (FR3 : forall x, fr <= x < fr + 4096 -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hfrp x Hx))).
  assert (SH3 : forall x, Sh <= x < Sh + 512 -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hshp x Hx))).
  assert (ST3 : forall x, S - 32768 <= x < S -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hstkp x Hx))).
  (* ---- step 1: the run 0x81cb0 -> 0x52600 (P3F.p3_pre_F) on the normalized memory ---- *)
  set (n3 := B.MemNorm.normalize rsegs mem3).
  assert (NR : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
                 (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, n3 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hni Hb. unfold n3. rewrite (w3a_norm_raw mem3 x Hx Hni). exact Hb. }
  destruct (w3a_bytes_of_mrd n3 29 (Sh + 336) ltac:(lia) ltac:(lia)) as (xs & Hxl & Hxs).
  { intros x Hx. destruct (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))) as [b Hb].
    exists b. exact (w3a_raw_mrd n3 _ b Hb). }
  destruct (w3a_cb_raw n3 (fr + 2688) 38 ltac:(lia) ltac:(lia)) as (idb' & Hidb').
  { intros x Hx. exact (NR x ltac:(lia) (Hfrimg x ltac:(lia)) (FR3 x ltac:(lia))). }
  destruct (w3a_cb_raw n3 (fr + 2880) 40 ltac:(lia) ltac:(lia)) as (fpb' & Hfpb').
  { intros x Hx. exact (NR x ltac:(lia) (Hfrimg x ltac:(lia)) (FR3 x ltac:(lia))). }
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (w3a_SRr_norm W3 _ _ mem3 md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { exact HRO. }
  { eapply (P3F.p3_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Sh := Sh) (Ab := A)
      (idp := fr + 2688) (fp := fr + 2880) (lo := S - 32768) (xs := xs) (idb := idb') (fpb := fpb').
    - exact Hr2.
    - exact Hr19'.
    - exact Hr9'.
    - unfold B.AsanRT.RT_HI. lia.
    - lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold B.AsanRT.RT_HI. lia.
    - clear - Efr8. Z.div_mod_to_equations. lia.
    - destruct (w3a_sh_frame fr (fr + 2688) Efr8 ltac:(lia)) as [E1 _]. rewrite E1.
      change (B.ACtlCutP.Sfr fr) with Sh. replace (fr + 2688 - fr) with 2688 by lia. reflexivity.
    - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
    - lia.
    - unfold B.AsanRT.RT_HI. lia.
    - clear - Efr8. Z.div_mod_to_equations. lia.
    - destruct (w3a_sh_frame fr (fr + 2880) Efr8 ltac:(lia)) as [E1 _]. rewrite E1.
      change (B.ACtlCutP.Sfr fr) with Sh. replace (fr + 2880 - fr) with 2880 by lia. reflexivity.
    - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
    - exact Hxl.
    - apply w3a_rwC1s; [exact Hxs |]. rewrite Hxl. apply w3a_wr_raw; [lia | lia |].
      intros x Hx. exact (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))).
    - exact Hidb'.
    - exact Hfpb'.
    - exact (B.AsanRTFacts.ro_c8 n3 (A + 168) _ (B.MemNorm.bytes_at_normalize rsegs mem3 _ _ HRO Hq168)).
    - exact (B.AsanRTFacts.ro_c8 n3 (A + 176) _ (B.MemNorm.bytes_at_normalize rsegs mem3 _ _ HRO Hq176)).
    - exact (B.MemNorm.mem_inv_normalize rsegs mem3).
    - apply w3a_stk_raw; [lia | lia |]. intros x Hx.
      exact (NR x ltac:(lia) (NIH x ltac:(lia)) (ST3 x ltac:(lia))).
    - exact (w3a_asan_norm mem3 HRO HAC).
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hshp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros s s0 md1 HP Hrel Hro' Hhid Hsame1.
  destruct HP as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & Es0 & MU1 & WM1 &
    MI1 & STK1 & AC1 & SR1 & RWF1 & ADF1 & RWI1 & ADI1 & RO176 & B336 & B346 & B360).
  subst s0.
  destruct (w3a_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es MR].
  set (m' := ms_mem s) in *. clearbody m'. rewrite Es. clear Es Hrel.
  pose proof (B.MemNorm.mem_rel_normalize rsegs mem3 HRO) as MRN.
  pose proof (B.MemNorm.munch_rel rsegs _ mem3 n3 m' m1 MRN MR Hro' MU1) as MU.
  pose proof (B.MemNorm.wmono_rel rsegs mem3 n3 m' m1 MRN MR Hro' WM1) as WM.
  assert (MRD : forall a, lib.Lib.Mem.mrd rsegs m' a = lib.Lib.Mem.mrd rsegs m1 a)
    by (intros a; exact (B.MemNorm.mrd_rel rsegs m' m1 a MR)).
  assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (Sh + 336 <= x < Sh + 365) ->
            lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx H1. apply (w3a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside]. split; [exact H1 | exact I]. }
  assert (PM1 : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
            (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, m' (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx Hni Hb; exact (w3a_wmono_raw mem3 m' x WM Hx Hni Hb)).
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 m' md1 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k m' md1 _ HJ MU Hhid Hsame1).
    intros a Ha. apply w3a_not_outside1 in Ha.
    split; [apply PM1; [lia | apply NIH; lia | apply SH3; lia] | apply (w3a_awr_fsh cx ly3 fr _ _ _ _ a Efr); lia]. }
  (* ---- step 2: __asan_memset (fr + 2880, 0, 40) ---- *)
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x52600) _ _ _ _] => set (R1 := R) end.
  assert (R1_1 : lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x81d10) by reflexivity.
  assert (R1_2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R1_3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R1_4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R1_8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R1_9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite Hr9'; reflexivity).
  assert (R1_10 : lib.Reusable.YK11.getr R1 10 = Reusable.YG0d.w64 (fr + 2880)) by reflexivity.
  assert (R1_11 : lib.Reusable.YK11.getr R1 11 = Reusable.YG0d.w64 0) by reflexivity.
  assert (R1_12 : lib.Reusable.YK11.getr R1 12 = Reusable.YG0d.w64 40) by reflexivity.
  assert (R1_19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite Hr19'; reflexivity).
  assert (R1_23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R1_24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (R1_25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R1_26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR1 : Reusable.YG0d.spZ R1 = S + (sp - S)).
  { unfold Reusable.YG0d.spZ in HspZ |- *. rewrite R1_2, HspZ. lia. }
  assert (Hgp1 : lib.Reusable.YK11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B))
    by (rewrite R1_3, Hr3; exact (w3a_gp cx HB)).
  assert (Htp1 : lib.Reusable.YK11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (rewrite R1_4; exact Hr4).
  assert (Ho16 : (sp - S) mod 16 = 0) by (clear - Hsp16 HS16; Z.div_mod_to_equations; lia).
  assert (Hbud : Reusable.YG0d.ESTACK - (sp - S) <= Reusable.YCfn.LLVMF_STK)
    by (rewrite HSTK; change Reusable.YG0d.ESTACK with 4096; lia).
  assert (RETOK : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x81d10)) by (vm_compute; reflexivity).
  assert (HDEST : forall a, fr + 2880 <= a < fr + 2880 + 40 ->
            Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK S FP
              (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (B.ACtlCut.own6 cx) a /\
            ~ (S + (sp - S) - Reusable.YG0d.ESTACK <= a < S + (sp - S))).
  { intros a Ha. split; [apply (w3a_awr_fr cx ly3 fr _ _ _ _ a Efr); lia|].
    change Reusable.YG0d.ESTACK with 4096. lia. }
  assert (ADF' : B.AsanRT.addressable m' (fr + 2880) 40)
    by exact (w3a_addr_keep m1 m' _ _ ADF1 (fun i _ => MRD _)).
  assert (ADI' : B.AsanRT.addressable m' (fr + 2688) 38)
    by exact (w3a_addr_keep m1 m' _ _ ADI1 (fun i _ => MRD _)).
  assert (HRAD' : Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m')
                    Reusable.YG0f.SHADOW_OFF (fr + 2880) 40).
  { apply (w3a_range_addr W3 m' _ _ ADF'). intros i Hi.
    destruct (w3a_sh_frame fr (fr + 2880 + i) Efr8 ltac:(lia)) as [E1 E2]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply VS. lia. }
  assert (HHULL : 0 < 40 -> Reusable.YG0d.shadow_hull_vis
                    (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m') (fr + 2880) 40).
  { intros _. apply (w3a_hull_vis W3 m'); [lia | lia|]. intros t Ht.
    destruct (w3a_sh_frame fr (fr + 2880) Efr8 ltac:(lia)) as [E1 E2].
    destruct (w3a_sh_frame fr (fr + 2880 + 40 - 1) Efr8 ltac:(lia)) as [E3 E4].
    rewrite E1, E3 in Ht. change (B.ACtlCutP.Sfr fr) with Sh in Ht.
    split; [apply VS; lia | apply PM1; [lia | apply NIH; lia | apply SH3; lia]]. }
  eapply (Reusable.YA0n.SRr_bind segs).
  { exact (Reusable.YCbq.aj_intrin_at segs B LAWS segs_low Reusable.YG0d.OSet
             Reusable.YB1w.tfib_A_asan_memset AMEMSET W3 R1 m' Reusable.YCfn.LLVMF_STK S FP
             (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
             (B.ACtlCut.own6 cx) ly3 S3 md1 k (fr + 2880) 0 40 (sp - S) (Z_to_bv 64 0x81d10)
             HJ1 R1_10 R1_11 R1_12 ltac:(lia) ltac:(lia) ltac:(lia) HspR1 Ho16 ltac:(lia) Hbud
             Hgp1 Htp1 R1_1 RETOK HDEST
             (w3a_amem_frame fr (fr + 2880) 40 Hfr4 Hfrc Hfrlh0 ltac:(lia) ltac:(lia)) HRAD' HHULL I). }
  intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpreg & E10 & Hset & Hfrm & Hpres2).
  assert (HRPF : rt_post_frame W3 m' mem2 [(fr + 2880, fr + 2880 + 40); (sp - Reusable.YG0d.ESTACK, sp)]).
  { split; [|exact Hpres2]. intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
    apply Hfrm; [exact Ha | exact Ho1 |]. intros H'. apply Ho2. lia. }
  assert (FRm' : forall x, fr <= x < fr + 4096 -> exists b, m' (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; apply PM1; [lia | apply Hfrimg; exact Hx | apply FR3; exact Hx]).
  destruct (B.ProgWorld.ctl_post_memset W3 m' mem2 sp (fr + 2880) 0 40 ltac:(lia) ltac:(lia) ltac:(lia)
              (fun a Ha => conj (VF a ltac:(lia)) (FRm' a ltac:(lia))) Hset HRPF) as (MV & WMV & RW40).
  assert (KV2 : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 2880 <= x < fr + 2920) -> ~ (sp - 4096 <= x < sp) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. apply (w3a_mvis _ _ _ _ x MV Hx Hv). cbn [lib.Lib.Frame.outside].
    change Reusable.YG0d.ESTACK with 4096. split; [lia | split; [lia | exact I]]. }
  assert (PR2 : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
             Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, mem2 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx Hni Hv Hb; exact (proj2 (Hpres2 x (conj Hv (PM1 x Hx Hni Hb))))).
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- R1_2; exact (Hpreg 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- R1_3; exact (Hpreg 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- R1_4; exact (Hpreg 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- R1_8; exact (Hpreg 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite <- R1_9; exact (Hpreg 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- R1_19; exact (Hpreg 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- R1_23; exact (Hpreg 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (rewrite <- R1_24; exact (Hpreg 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- R1_25; exact (Hpreg 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- R1_26; exact (Hpreg 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (Hsp2u : bv_unsigned (lib.Reusable.YK11.getr regs2 2) = sp)
    by (rewrite E2, Hr2; exact (lib.Lib.Mem.wa_unsigned sp ltac:(lia))).
  pose proof (w3a_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2) as HRT2.
  pose proof HRT2 as (HAC2 & HSWC2 & HSWI2 & HRO2).
  assert (ADI2 : B.AsanRT.addressable mem2 (fr + 2688) 38).
  { apply (w3a_addr_keep m' mem2 _ _ ADI'). intros i Hi.
    destruct (w3a_sh_frame fr (fr + 2688 + i) Efr8 ltac:(lia)) as [E1 E5]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply KV2; [lia | apply VS; lia | lia | lia]. }
  assert (KK2 : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 2880 <= x < fr + 2920) -> ~ (sp - 4096 <= x < sp) -> ~ (Sh + 336 <= x < Sh + 365) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2 H3. rewrite (KV2 x Hx Hv H1 H2). exact (KEEP1 x Hx H3). }
  (* ---- step 3: the second stretch (P3F.p3_pre2_F) and reac_identity_init, one lift ---- *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81d10 regs2 mem2 md2) (POST cx)).
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs2) regs2);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs2))].
  unfold Lib.Regs6ss.mkR_of.
  set (n2 := B.MemNorm.normalize rsegs mem2).
  assert (NR2 : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
                  (exists b, mem2 (lib.Lib.Mem.wa x) = Some b) -> exists b, n2 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hni Hb. unfold n2. rewrite (w3a_norm_raw mem2 x Hx Hni). exact Hb. }
  destruct (w3a_cb_raw n2 (fr + 2688) 38 ltac:(lia) ltac:(lia)) as (idb2 & Hidb2).
  { intros x Hx. apply NR2; [lia | apply Hfrimg; lia |].
    apply PR2; [lia | apply Hfrimg; lia | apply VF; lia | apply FR3; lia]. }
  assert (Hq176' : B.ACtlCutP.q64 mem2 (A + 176) (fr + 2688)).
  { apply (w3a_bytes_keep mem3 mem2 _ _ Hq176). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply KK2; [lia | apply VK; lia | lia | lia | lia]. }
  eapply (w3a_SRr_norm W3 _ _ mem2 md2 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { exact HRO2. }
  { eapply Lib.ExecF.evtF_cut.
    - eapply (P3F.p3_pre2_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Ab := A) (idp := fr + 2688).
      + exact (eq_trans E9 Hr9').
      + lia.
      + lia.
      + lia.
      + exact (B.AsanRTFacts.ro_c8 n2 (A + 176) _ (B.MemNorm.bytes_at_normalize rsegs mem2 _ _ HRO2 Hq176')).
      + apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia].
    - intros ms' Hms'. cbv beta in Hms'. subst ms'.
      eapply (reac_identity_init_holds_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (sp := lib.Reusable.YK11.getr regs2 2) (lo := S - 32768) (id := fr + 2688) (idb := idb2).
      + reflexivity.
      + lia.
      + intros _. split; [clear - Efr8; Z.div_mod_to_equations; lia | exact Hidb2].
      + exact (B.MemNorm.mem_inv_normalize rsegs mem2).
      + rewrite Hsp2u. apply w3a_stk_raw; [lia | lia |]. intros x Hx.
        apply NR2; [lia | apply NIH; lia |].
        apply PR2; [lia | apply NIH; lia | apply VK; lia | apply ST3; lia].
      + rewrite Hsp2u. unfold RII.REAC_IDENTITY_INIT_K. lia.
      + unfold B.AsanRT.HIGHMEM_BEG. lia.
      + rewrite Hsp2u. unfold B.AsanRT.APPMEM_END. lia.
      + exact (w3a_asan_norm mem2 HRO2 HAC2).
      + (* route (C): reac_identity_init_shadow_R (fr + 2688) is the span of shadow words of [fr + 2688, fr + 2726),
           inside the owned frame's shadow: cut_shadow (F) of ctl_rt_C at mem2 (w3a_srw_frame_norm) *)
        assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
        assert (HshF : Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx)) = Sh).
        { rewrite <- Efr. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh. lia. }
        refine (w3a_srw_frame_norm ly3 S3 mem2 6 (B.ACtlCut.c_fpos cx) _ HRT2 Hin6 _).
        intros a (_ & _ & Ha). rewrite HshF. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
        rewrite ESh. clear - Ha Efr8 Hfr32. Z.div_mod_to_equations. lia.
      + intros _. split.
        * apply (w3a_addr_keep mem2 n2 _ _ ADI2). intros i Hi.
          exact (eq_sym (B.MemNorm.mrd_rel rsegs mem2 n2 _ (B.MemNorm.mem_rel_normalize rsegs mem2 HRO2))).
        * unfold B.AsanRT.end_in_app. right.
          unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      + intros _. right. unfold B.AsanRT.RT_HI. lia.
      + intros _. rewrite Hsp2u. left. unfold RII.REAC_IDENTITY_INIT_K. lia.
      + exact (B.ProgBridge.rng_bytes_RNG_W _).
      + exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
      + rewrite Hsp2u. unfold RII.REAC_IDENTITY_INIT_K.
        apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia].
      + rewrite Hsp2u. unfold RII.REAC_IDENTITY_INIT_K. right.
        unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr.
        apply B.ProgBridge.rng_RNG_W; [unfold B.AsanRT.ASAN_K; clear - HSlo HC1 HSsp HspA HAS448 HSapp;
          Z.div_mod_to_equations; lia | unfold B.AsanRT.ASAN_K; clear - HSlo HC1 HSsp HspA HAS448 HSapp P64;
          Z.div_mod_to_equations; lia |].
        intros t Ht. apply (w3a_stk_sh_cover ly3 S3 W3 mem3 md3 (sp - 2224) 2224 t (proj1 HJ)); try lia.
        unfold Reusable.YG0f.kHighMemBeg. lia.
      + rewrite Hsp2u. unfold RII.REAC_IDENTITY_INIT_K.
        apply B.ProgBridge.rng_RNG_W; [unfold B.AsanRT.ASAN_K; clear - HSlo HC1 HSsp HspA HAS448 HSapp;
          Z.div_mod_to_equations; lia | unfold B.AsanRT.ASAN_K; clear - HSlo HC1 HSsp HspA HAS448 HSapp P64;
          Z.div_mod_to_equations; lia |].
        intros t Ht. apply (w3a_stk_sh_cover ly3 S3 W3 mem3 md3 (sp - 2224) 2224 t (proj1 HJ));
          first [lia | unfold Reusable.YG0f.kHighMemBeg; lia |
                 unfold B.AsanRT.ASAN_K in Ht |- *; clear - Ht; Z.div_mod_to_equations; lia].
      + exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.rt_vis_W W3)).
      + intros _. split.
        * apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hfrp; lia].
        * apply B.ProgBridge.rng_RNG_W; [unfold B.AsanRT.ASAN_K; clear - Hfrc HC1 Hfr4; Z.div_mod_to_equations; lia |
            unfold B.AsanRT.ASAN_K; clear - Hfrc HC1 Hfr4 P64; Z.div_mod_to_equations; lia |].
          intros t Ht. apply VS. rewrite ESh. unfold B.AsanRT.ASAN_K in Ht.
          clear - Ht Efr8 Hfr32. Z.div_mod_to_equations. lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros s4 s40 md4 HP Hrel Hro4 Hhid4 Hsame4.
  destruct HP as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
    m4n & Es0 & MU4 & WM4 & MI4 & STK4 & AC4 & SR4 & _ & RW4).
  subst s40.
  destruct (w3a_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es MR4].
  set (m4 := ms_mem s4) in *. clearbody m4. rewrite Es. clear Es Hrel.
  unfold RII.reac_identity_init_W, RII.REAC_IDENTITY_INIT_K in MU4. rewrite Hsp2u in MU4, STK4.
  specialize (RW4 ltac:(lia)).
  pose proof (B.MemNorm.mem_rel_normalize rsegs mem2 HRO2) as MRN2.
  pose proof (B.MemNorm.munch_rel rsegs _ mem2 n2 m4 m4n MRN2 MR4 Hro4 MU4) as MU4'.
  assert (MRD4 : forall a, lib.Lib.Mem.mrd rsegs m4 a = lib.Lib.Mem.mrd rsegs m4n a)
    by (intros a; exact (B.MemNorm.mrd_rel rsegs m4 m4n a MR4)).
  assert (KEEP4 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 2224 <= x < sp) -> ~ (fr + 2688 <= x < fr + 2726) ->
            lib.Lib.Mem.mrd rsegs m4 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x)).
  { intros x Hx H1 H2. apply (w3a_mrd_munch _ _ _ x MU4' Hx). cbn [lib.Lib.Frame.outside].
    split; [lia | split; [lia | exact I]]. }
  assert (RAWK4 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 2224 <= x < sp) -> ~ (fr + 2688 <= x < fr + 2726) ->
            m4 (lib.Lib.Mem.wa x) = mem2 (lib.Lib.Mem.wa x)).
  { intros x Hx H1 H2. apply MU4'. rewrite lib.Lib.Mem.wa_unsigned by exact Hx. cbn [lib.Lib.Frame.outside].
    split; [lia | split; [lia | exact I]]. }
  assert (WP4 : forall x, sp - 2224 <= x < sp \/ fr + 2688 <= x < fr + 2726 ->
            exists b, m4 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct Hx as [Hx|Hx].
    - destruct STK4 as (_ & _ & Hs). destruct (Hs x ltac:(lia)) as (_ & b & Hb). rewrite <- MRD4 in Hb.
      exists b. apply (w3a_mrd_raw m4 x b ltac:(lia)); [apply NIH; lia | exact Hb].
    - destruct RW4 as ((_ & _ & _ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
      rewrite app_nil_r in Hb.
      specialize (Hb (Z.to_nat (x - (fr + 2688))) ltac:(rewrite repeat_length; lia)).
      rewrite nth_error_repeat in Hb by lia. replace (fr + 2688 + Z.of_nat (Z.to_nat (x - (fr + 2688)))) with x in Hb
        by lia. rewrite <- MRD4 in Hb. exists (Z_to_bv 8 0).
      apply (w3a_mrd_raw m4 x _ ltac:(lia)); [apply Hfrimg; lia | exact Hb]. }
  assert (HJ4 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 m4 md4 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem2 md2 k m4 md4 _ HJ2 MU4' Hhid4 Hsame4).
    intros a Ha. destruct (w3a_not_outside2 _ _ _ _ a Ha) as [Ha1|Ha1].
    - split; [apply WP4; lia | apply w3a_awr_stk; lia].
    - split; [apply WP4; lia | apply (w3a_awr_fr cx ly3 fr _ _ _ _ a Efr); lia]. }
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x81d18) = Z_to_bv 64 0x81d18) by (apply bv_eq; reflexivity).
  rewrite Eret.
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x81d18) _ _ _ _] => set (R4 := R) end.
  assert (G2 : lib.Reusable.YK11.getr R4 2 = lib.Reusable.YK11.getr regs3 2) by exact E2.
  assert (G3 : lib.Reusable.YK11.getr R4 3 = lib.Reusable.YK11.getr regs3 3) by exact E3.
  assert (G4 : lib.Reusable.YK11.getr R4 4 = lib.Reusable.YK11.getr regs3 4) by exact E4.
  assert (G8 : lib.Reusable.YK11.getr R4 8 = lib.Reusable.YK11.getr regs3 8) by exact E8.
  assert (G9 : lib.Reusable.YK11.getr R4 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite Hr9'; reflexivity).
  assert (G19 : lib.Reusable.YK11.getr R4 19 = lib.Reusable.YK11.getr regs3 19) by exact E19.
  assert (G23 : lib.Reusable.YK11.getr R4 23 = lib.Reusable.YK11.getr regs3 23) by exact E23.
  assert (G24 : lib.Reusable.YK11.getr R4 24 = lib.Reusable.YK11.getr regs3 24) by exact E24.
  assert (G25 : lib.Reusable.YK11.getr R4 25 = lib.Reusable.YK11.getr regs3 25) by exact E25.
  assert (G26 : lib.Reusable.YK11.getr R4 26 = lib.Reusable.YK11.getr regs3 26) by exact E26.
  (* every memory fact of the successor reads mem3 (unwritten bytes) or the run's / the callees' writes *)
  assert (KK : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 2880 <= x < fr + 2920) -> ~ (sp - 4096 <= x < sp) -> ~ (Sh + 336 <= x < Sh + 365) ->
             ~ (fr + 2688 <= x < fr + 2726) ->
             lib.Lib.Mem.mrd rsegs m4 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2 H3 H4. rewrite (KEEP4 x Hx ltac:(lia) H4). exact (KK2 x Hx Hv H1 H2 H3). }
  assert (KSm : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 2880 <= x < fr + 2920) -> ~ (sp - 4096 <= x < sp) -> ~ (fr + 2688 <= x < fr + 2726) ->
             lib.Lib.Mem.mrd rsegs m4 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m1 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2 H4. rewrite (KEEP4 x Hx ltac:(lia) H4), (KV2 x Hx Hv H1 H2). exact (MRD _). }
  assert (KSHX : forall x, fr <= x < fr + 2688 ->
            lib.Lib.Mem.mrd rsegs m4 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
            lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))).
  { intros x Hx. destruct (w3a_sh_frame fr x Efr8 ltac:(lia)) as [E1 E5]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply KK; [lia | apply VS; lia | lia | lia | lia | lia]. }
  assert (PR4 : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
             Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false -> ~ (sp - 2224 <= x < sp) ->
             ~ (fr + 2688 <= x < fr + 2726) ->
             (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, m4 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hni Hv H1 H2 Hb. rewrite (RAWK4 x Hx H1 H2). exact (PR2 x Hx Hni Hv Hb). }
  assert (B336m : forall off (k0 : nat) (z : list byte), 336 <= off -> off + Z.of_nat k0 <= 365 ->
            lib.Lib.Mem.bytes_at rsegs m1 (Sh + off) z -> length z = k0 ->
            lib.Lib.Mem.bytes_at rsegs m4 (Sh + off) z).
  { intros off k0 z Ho1 Ho2 Hz Hl. apply (w3a_bytes_keep m1 m4 _ _ Hz). rewrite Hl. intros x Hx.
    apply KSm; [lia | apply VS; lia | lia | lia | lia]. }
  assert (HspZ4 : Reusable.YG0d.spZ R4 = sp) by (unfold Reusable.YG0d.spZ in HspZ |- *; rewrite G2; exact HspZ).
  destruct (w3a_cb_raw m4 (fr + 2768) 72 ltac:(lia) ltac:(lia)) as (junkD & HjunkD).
  { intros x Hx. apply PR4; [lia | apply Hfrimg; lia | apply VF; lia | lia | lia | apply FR3; lia]. }
  (* C5: the successor cut B81d18. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81d18 R4 m4 md4) (POST cx)).
  unfold B.ACtlCut.ctl_from in HD18.
  apply (HD18 cx idx fr k ly3 S3 W3 R4 m4 md4 HB);
    cbn [B.ACtlCutP.C_B81d18 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - exact HJ4.
  - exact Hfr.
  - exact HFA.
  - exact Hk.
  - refine (conj Hperm (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
    + (* FRAC *)
      apply (w3a_FRAC_keep cx fr fr regs3 R4 mem3 m4 HFRAC G2 G3 G4 G8 G9 G19 G26).
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia | lia].
      * intros x Hx. apply KK; [lia | apply VF; lia | lia | lia | lia | lia].
      * intros x Hx. destruct (PR4 x ltac:(lia) (NIH x ltac:(lia)) (VS x ltac:(lia)) ltac:(lia) ltac:(lia)
                                 (SH3 x ltac:(lia))) as [b Hb].
        exists b. exact (w3a_raw_mrd _ _ _ Hb).
    + (* OURb *)
      unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 m4 _ _ HOUR).
      rewrite B.ACtlCutP.SM.OUR_length. intros x Hx. apply KK; [lia | apply VF; lia | lia | lia | lia | lia].
    + (* s8 *)
      unfold B.ACtlCut.rgv. rewrite G24. exact H24'.
    + (* PRO *)
      apply (w3a_PRO_keep fr regs3 R4 mem3 m4 A Hr9 ltac:(lia) ltac:(lia) G9); [| | exact HPRO].
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia | lia].
      * intros i Hi. apply KSHX. lia.
    + (* CUR *)
      destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
      refine (conj Hc0 (conj _ _)); [rewrite G23; exact Hc23 | rewrite G25; exact Hc25].
    + (* KIND_NAME *)
      exact (ctl_kind_name_addressable ly3 S3 W3 m4 md4 (proj1 HJ4)).
    + (* IDBe: the 38 zero bytes reac_identity_init wrote *)
      unfold B.ACtlCutP.IDBe. change B.ACtlCutP.RIM.ID0 with (repeat (Z_to_bv 8 0) 38).
      destruct RW4 as ((_ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
      rewrite app_nil_r in Hb. apply (w3a_bytes_keep m4n m4 _ _ Hb). intros x _. exact (MRD4 _).
    + (* addressable (fr + 2688) 38 *)
      apply (w3a_addr_keep m1 m4 _ _ ADI1). intros i Hi.
      destruct (w3a_sh_frame fr (fr + 2688 + i) Efr8 ltac:(lia)) as [E1 E5]. rewrite E1.
      change (B.ACtlCutP.Sfr fr) with Sh. apply KSm; [lia | apply VS; lia | lia | lia | lia].
    + (* spill 176 *)
      exists A. split; [unfold B.ACtlCut.rgv; rewrite G9; exact Hr9'|].
      apply (w3a_bytes_keep mem3 m4 _ _ Hq176). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia | lia].
    + (* the group *)
      exists (fr + 2768), sp, A, junkD. cbv zeta.
      assert (HshD : B.AsanRT.shadow_addr (fr + 2768) = Sh + 346).
      { destruct (w3a_sh_frame fr (fr + 2768) Efr8 ltac:(lia)) as [E1 _]. rewrite E1.
        change (B.ACtlCutP.Sfr fr) with Sh. replace (fr + 2768 - fr) with 2768 by lia. reflexivity. }
      assert (HshF : B.AsanRT.shadow_addr (fr + 2880) = Sh + 360).
      { destruct (w3a_sh_frame fr (fr + 2880) Efr8 ltac:(lia)) as [E1 _]. rewrite E1.
        change (B.ACtlCutP.Sfr fr) with Sh. replace (fr + 2880 - fr) with 2880 by lia. reflexivity. }
      assert (AD40 : B.AsanRT.addressable m4 (fr + 2880) 40).
      { apply (w3a_addr_zero m4 (fr + 2880) 40 5%nat); [lia | clear - Efr8; Z.div_mod_to_equations; lia |
          unfold B.AsanRT.APPMEM_END; lia | lia |
          intros i Hi; unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia |].
        rewrite HshF. apply (B336m 360 5%nat); [lia | lia | exact B360 | apply repeat_length]. }
      unfold B.ACtlCutP.AMC.ASAN_MEMSET_K.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj HjunkD (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl
        (conj _ (conj _ AD40)))))))))))))))))))))))).
      * rewrite G2. exact Hr2.
      * rewrite G9. exact Hr9'.
      * lia.
      * lia.
      * lia.
      * apply w3a_rw8.
        -- apply (w3a_bytes_keep mem3 m4 _ _ Hq208). rewrite lib.Lib.Mem.length_le8.
           intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia | lia].
        -- apply w3a_wr_raw; [lia | lia |]. intros x Hx.
           apply PR4; [lia | apply NIH; lia | apply VK; lia | lia | lia | apply ST3; lia].
      * apply (w3a_addr_zero m4 (fr + 2768) 72 9%nat); [lia | clear - Efr8; Z.div_mod_to_equations; lia |
          unfold B.AsanRT.APPMEM_END; lia | lia |
          intros i Hi; unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia |].
        rewrite HshD. apply (B336m 346 9%nat); [lia | lia | exact B346 | apply repeat_length].
      * unfold B.AsanRT.end_in_app. right.
        unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      * unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      * right. unfold B.AsanRT.RT_HI. lia.
      * left. lia.
      * intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros A1 HA1 HA1r x Hx.
        assert (EA1 : A1 = A) by (apply w3a_bv_inj; [lia | lia | rewrite <- HA1, G9; exact Hr9']). subst A1.
        cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros A1 HA1 HA1r x Hx.
        assert (EA1 : A1 = A) by (apply w3a_bv_inj; [lia | lia | rewrite <- HA1, G9; exact Hr9']). subst A1.
        cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros x Hx. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros x Hx. change B.ACtlCutP.FRAME_SHADOW with 392 in Hx. change (B.ACtlCutP.Sfr fr) with Sh in Hx.
        cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * intros x Hx. rewrite B.ACtlCutP.SM.OUR_length in Hx.
        cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * cbn [B.ACtlCutP.ARF.all_app]. split; [| split; [| exact I]]; intros a Ha;
          unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia.
      * unfold B.ACtlCutP.rt_disjoint. cbn [lib.Lib.Frame.disjoint_from].
        unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI, B.AsanRT.RT_AF, B.AsanRT.RT_GOT_AF, B.AsanRT.RT_VERB,
          B.AsanRT.RT_GOT_VERB, B.AsanRT.RT_CF, B.AsanRT.RT_GOT_CF, B.AsanRT.RT_TSDI, B.AsanRT.RT_TSDK,
          B.AsanRT.RT_PGSZ, B.AsanRT.RT_TSDMAIN, B.AsanRT.RT_IMAP, B.AsanRT.RT_IMEM, B.AsanRT.RT_TP,
          B.AsanRT.RT_REAL_LO, B.AsanRT.RT_REAL_HI, B.AsanRT.RT_MUG, B.AsanRT.RT_AGLOB, B.AsanRT.RT_AGLOB_LEN.
        repeat split; lia.
      * apply (w3a_bytes_keep mem3 m4 _ _ Hq64). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia | lia].
      * apply w3a_FSj0_zero; [| exact AD40].
        destruct RW40 as ((_ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
        rewrite app_nil_r in Hb. change (Z.to_nat 40) with 40%nat in Hb.
        change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in Hb.
        apply (w3a_bytes_keep mem2 m4 _ _ Hb). rewrite repeat_length. intros x Hx. apply KEEP4; lia.
  - (* C4 *)
    exact (w3a_ctlrt cx _ ly3 S3 W3 m4 md4 k HB HJ4).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81d18 (0x81d18, own6, k <= 14) --S_P4--> B81d28 (0x81d28, own6, k <= 14).  Seg/P4.v seg_P4 :128.
   li a2,72, ld a0,208(s1) (D = fr + 2768), li a1,0, jal __asan_memset (D, 0, 72), return at 0x81d28. *)
Lemma seg_P4 : forall POST, CF POST C_B81d28 -> CF POST C_B81d18.
Proof using Hwx LAWS segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
  (* C0 *)
  intros POST HD28 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81d18 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body]
    in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & H24 & HPRO & HCUR & HKN & HIDB & H2688 & H176 & HG).
  destruct HG as (D & spv & A0 & junk & HG). cbv zeta in HG.
  destruct HG as (Hg2 & Hg9 & HA0r & HDr & Hspvr & Hrw208 & HrwD & HaddD & HeiaD & Happ7 & HRTa & HWIN &
    O1 & O2 & O3 & O4 & O5 & O6 & O7 & Hallapp & Hrtd & ED & Hq64 & HFSJ & H2880).
  subst D.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof Hfrlh as Hfrlh0. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Efr8' : fr = 8 * (fr / 8)) by (clear - Efr8; Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  assert (Hr9' : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (EA0 : A0 = A) by (apply w3a_bv_inj; [lia | lia | rewrite <- Hg9; exact Hr9']). subst A0.
  pose proof (w3a_spill_A regs3 mem3 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H176) as Hq176.
  pose proof (w3a_q64_of_c8 mem3 (A + 208) (fr + 2768) Hrw208) as Hq208.
  assert (VF : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hfrp x Hx))).
  assert (VS : forall x, Sh <= x < Sh + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hshp x Hx))).
  assert (VK : forall x, S - 32768 <= x < S -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hstkp x Hx))).
  (* C1/C2: the run 0x81d18 -> 0x52600 (P4F.p4_pre_F), memory unchanged. *)
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (P4F.p4_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Ab := A) (fg := fr + 2768).
    - exact Hr9.
    - lia.
    - lia.
    - lia.
    - exact (proj1 Hrw208).
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md1 Hms _ Hsame1. cbv beta in Hms. subst ms'.
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md1 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k mem3 md1 [] HJ (lib.Lib.Frame.munch_refl [] mem3)
             (fun _ _ => eq_refl) Hsame1).
    intros a Ha. exfalso. apply Ha. exact I. }
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x52600) _ _ _ _] => set (R1 := R) end.
  assert (R1_1 : lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x81d28) by reflexivity.
  assert (R1_2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R1_3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R1_4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R1_8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R1_9 : lib.Reusable.YK11.getr R1 9 = Z_to_bv 64 A) by reflexivity.
  assert (R1_10 : lib.Reusable.YK11.getr R1 10 = Reusable.YG0d.w64 (fr + 2768)) by reflexivity.
  assert (R1_11 : lib.Reusable.YK11.getr R1 11 = Reusable.YG0d.w64 0) by reflexivity.
  assert (R1_12 : lib.Reusable.YK11.getr R1 12 = Reusable.YG0d.w64 72) by reflexivity.
  assert (R1_19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (R1_23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R1_24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (R1_25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R1_26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR1 : Reusable.YG0d.spZ R1 = S + (sp - S)).
  { unfold Reusable.YG0d.spZ in HspZ |- *. rewrite R1_2, HspZ. lia. }
  assert (Hgp1 : lib.Reusable.YK11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B))
    by (rewrite R1_3, Hr3; exact (w3a_gp cx HB)).
  assert (Htp1 : lib.Reusable.YK11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (rewrite R1_4; exact Hr4).
  assert (Ho16 : (sp - S) mod 16 = 0) by (clear - Hsp16 HS16; Z.div_mod_to_equations; lia).
  assert (Hbud : Reusable.YG0d.ESTACK - (sp - S) <= Reusable.YCfn.LLVMF_STK)
    by (rewrite HSTK; change Reusable.YG0d.ESTACK with 4096; lia).
  assert (RETOK : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x81d28)) by (vm_compute; reflexivity).
  assert (HDEST : forall a, fr + 2768 <= a < fr + 2768 + 72 ->
            Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK S FP
              (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (B.ACtlCut.own6 cx) a /\
            ~ (S + (sp - S) - Reusable.YG0d.ESTACK <= a < S + (sp - S))).
  { intros a Ha. split; [apply (w3a_awr_fr cx ly3 fr _ _ _ _ a Efr); lia|].
    change Reusable.YG0d.ESTACK with 4096. lia. }
  assert (HRAD : Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3)
                   Reusable.YG0f.SHADOW_OFF (fr + 2768) 72).
  { apply (w3a_range_addr W3 mem3 _ _ HaddD). intros i Hi.
    destruct (w3a_sh_frame fr (fr + 2768 + i) Efr8 ltac:(lia)) as [E1 E2]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply VS. lia. }
  assert (HHULL : 0 < 72 -> Reusable.YG0d.shadow_hull_vis
                    (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3) (fr + 2768) 72).
  { intros _. apply (w3a_hull_vis W3 mem3); [lia | lia|]. intros s Hs.
    destruct (w3a_sh_frame fr (fr + 2768) Efr8 ltac:(lia)) as [E1 E2].
    destruct (w3a_sh_frame fr (fr + 2768 + 72 - 1) Efr8 ltac:(lia)) as [E3 E4].
    rewrite E1, E3 in Hs. change (B.ACtlCutP.Sfr fr) with Sh in Hs. apply Hshp. lia. }
  (* C2': __asan_memset (fr + 2768, 0, 72) by the core's rule at the journal (YCbq.aj_intrin_at). *)
  eapply (Reusable.YA0n.SRr_bind segs).
  { exact (Reusable.YCbq.aj_intrin_at segs B LAWS segs_low Reusable.YG0d.OSet
             Reusable.YB1w.tfib_A_asan_memset AMEMSET W3 R1 mem3 Reusable.YCfn.LLVMF_STK S FP
             (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
             (B.ACtlCut.own6 cx) ly3 S3 md1 k (fr + 2768) 0 72 (sp - S) (Z_to_bv 64 0x81d28)
             HJ1 R1_10 R1_11 R1_12 ltac:(lia) ltac:(lia) ltac:(lia) HspR1 Ho16 ltac:(lia) Hbud
             Hgp1 Htp1 R1_1 RETOK HDEST
             (w3a_amem_frame fr (fr + 2768) 72 Hfr4 Hfrc Hfrlh0 ltac:(lia) ltac:(lia)) HRAD HHULL I). }
  intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpreg & E10 & Hset & Hfrm & Hpres2).
  (* C3: the raw memory after the call, by ProgWorld's ctl_post_memset (WR = the 72 bytes + the callee window). *)
  assert (HRPF : rt_post_frame W3 mem3 mem2 [(fr + 2768, fr + 2768 + 72); (sp - Reusable.YG0d.ESTACK, sp)]).
  { split; [|exact Hpres2]. intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
    apply Hfrm; [exact Ha | exact Ho1 |]. intros H'. apply Ho2. lia. }
  destruct (B.ProgWorld.ctl_post_memset W3 mem3 mem2 sp (fr + 2768) 0 72 ltac:(lia) ltac:(lia) ltac:(lia)
              (fun a Ha => Hfrp a ltac:(lia)) Hset HRPF) as (MV & WMV & RW72).
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 2768 <= x < fr + 2840) -> ~ (sp - 4096 <= x < sp) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. apply (w3a_mvis _ _ _ _ x MV Hx Hv). cbn [lib.Lib.Frame.outside].
    change Reusable.YG0d.ESTACK with 4096. split; [lia | split; [lia | exact I]]. }
  assert (KSHX : forall x, fr <= x < fr + 4096 ->
            lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
            lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))).
  { intros x Hx. destruct (w3a_sh_frame fr x Efr8 ltac:(lia)) as [E1 E2]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply KV; [lia | apply VS; lia | lia | lia]. }
  assert (FRm2 : forall x, fr <= x < fr + 4096 -> exists b, mem2 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hpres2 x (Hfrp x Hx)))).
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- R1_2; exact (Hpreg 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- R1_3; exact (Hpreg 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- R1_4; exact (Hpreg 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- R1_8; exact (Hpreg 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite Hr9', <- R1_9; exact (Hpreg 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- R1_19; exact (Hpreg 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- R1_23; exact (Hpreg 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (rewrite <- R1_24; exact (Hpreg 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- R1_25; exact (Hpreg 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- R1_26; exact (Hpreg 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  (* C5: the successor cut B81d28. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81d28 regs2 mem2 md2) (POST cx)).
  unfold B.ACtlCut.ctl_from in HD28.
  apply (HD28 cx idx fr k ly3 S3 W3 regs2 mem2 md2 HB);
    cbn [B.ACtlCutP.C_B81d28 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - exact HJ2.
  - exact Hfr.
  - exact HFA.
  - exact Hk.
  - refine (conj Hperm (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ _)))))))))))).
    + apply (w3a_FRAC_keep cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
      * intros x Hx. apply KV; [lia | apply VK; lia | lia | lia].
      * intros x Hx. apply KV; [lia | apply VF; lia | lia | lia].
      * intros x Hx. rewrite (KV x ltac:(lia) (VS x ltac:(lia)) ltac:(lia) ltac:(lia)).
        destruct (Hshp x ltac:(lia)) as [_ (b & Hb)]. exists b. exact (w3a_raw_mrd _ _ _ Hb).
    + unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HOUR).
      rewrite B.ACtlCutP.SM.OUR_length. intros x Hx. apply KV; [lia | apply VF; lia | lia | lia].
    + apply (w3a_PRO_keep fr regs3 regs2 mem3 mem2 A Hr9 ltac:(lia) ltac:(lia) E9); [| | exact HPRO].
      * intros x Hx. apply KV; [lia | apply VK; lia | lia | lia].
      * intros i Hi. apply KSHX. lia.
    + destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
      refine (conj Hc0 (conj _ _)); [rewrite E23; exact Hc23 | rewrite E25; exact Hc25].
    + exact (ctl_kind_name_addressable ly3 S3 W3 mem2 md2 (proj1 HJ2)).
    + unfold B.ACtlCutP.IDBe in HIDB |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HIDB).
      change (length B.ACtlCutP.RIM.ID0) with 38%nat. intros x Hx. apply KV; [lia | apply VF; lia | lia | lia].
    + unfold B.ACtlCutP.FGBe. exact (w3a_bytes_of_cb mem2 (fr + 2768) _ _ RW72).
    + unfold B.ACtlCutP.RAD, B.ACtlCutP.fragb.
      refine (conj (w3a_addr_keep mem3 mem2 _ _ H2688 _) (conj (w3a_addr_keep mem3 mem2 _ _ HaddD _)
        (w3a_addr_keep mem3 mem2 _ _ H2880 _))); intros i Hi; apply KSHX; lia.
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H176].
      intros x Hx. apply KV; [lia | apply VK; lia | lia | lia].
    + exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact Hr9'|].
      unfold B.ACtlCutP.fragb. apply (w3a_bytes_keep mem3 mem2 _ _ Hq208). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KV; [lia | apply VK; lia | lia | lia].
    + destruct (w3a_cb_raw mem2 (fr + 3040) 1 ltac:(lia) ltac:(lia) (fun x Hx => FRm2 x ltac:(lia))) as (jy & Hjy).
      destruct (w3a_cb_raw mem2 (fr + 3056) 32 ltac:(lia) ltac:(lia) (fun x Hx => FRm2 x ltac:(lia)))
        as (jk & Hjk).
      exists A, jy, jk.
      refine (conj _ (conj _ (conj _ (conj _ (conj Hjy (conj Hjk _)))))).
      * unfold B.ACtlCut.rgv. rewrite E9. exact Hr9'.
      * lia.
      * unfold B.ACtlCut.rgv in H24 |- *. rewrite E24. exact H24.
      * apply (w3a_bytes_keep mem3 mem2 _ _ Hq64). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply KV; [lia | apply VK; lia | lia | lia].
      * apply (w3a_FSj0_keep cx fr regs3 regs2 mem3 mem2 HFSJ).
        -- intros x Hx. apply KV; [lia | apply VF; lia | lia | lia].
        -- intros i Hi. apply KSHX. lia.
  - (* C4 *)
    exact (w3a_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81d28 (0x81d28, own6, k <= 14) --S_P5--> B81d68 (0x81d68, own6, k <= 14).  Seg/P5.v seg_P5 :216.
   16 frame-shadow stores (Sh + 370 = 2, 372 = 376 = 0, 380 = 1, 382 .. 385 = 0), the code byte [s8] := -18,
   li a2,32, ld a0,64(s1) (D = fr + 3056), li a1,0, jal __asan_memset (D, 0, 32), return at 0x81d68. *)
Lemma seg_P5 : forall POST, CF POST C_B81d68 -> CF POST C_B81d28.
Proof using Hwx LAWS segs_low AMEMSET TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable
  ctl_parse_bc_addressable.
  (* C0 *)
  intros POST HD68 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81d28 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body]
    in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & HPRO & HCUR & HKN & HIDB & HFGB & HRAD & H176 & H208 &
    A0 & jy & junk & Hg9 & HA0 & H24 & Hq64 & Hjy & Hjunk & HFSJ).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof (w3a_fr_lo cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA) as Hfrlo.
  destruct (w3a_stk_ly cx k ly3 S3 W3 mem3 md3 HJ) as (HLc & HLlo & HLhi & HL47).
  pose proof HRT as (HAC & HSWC & HSWI & HRO).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp, HLlo.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof Hfrlh as Hfrlh0. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  assert (Hr9' : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (Hr19' : lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 Sh) by exact Hr19.
  assert (H24' : lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 (fr + 3040)) by exact H24.
  assert (EA0 : A0 = A).
  { pose proof Hq64 as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat] in Hq1. unfold B.ACtlCut.rgv in Hg9.
    apply w3a_bv_inj; [lia | lia | rewrite <- Hg9; exact Hr9']. }
  subst A0.
  pose proof (w3a_spill_A regs3 mem3 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H176) as Hq176.
  pose proof (w3a_spill_A regs3 mem3 208 (fr + 2768) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H208) as Hq208.
  assert (VF : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hfrp x Hx))).
  assert (VS : forall x, Sh <= x < Sh + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hshp x Hx))).
  assert (VK : forall x, S - 32768 <= x < S -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hstkp x Hx))).
  assert (NIH : forall x, 2147450880 <= x -> ~ Reusable.YG0d.in_img segs x)
    by (intros x Hx; apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  assert (FR3 : forall x, fr <= x < fr + 4096 -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hfrp x Hx))).
  assert (SH3 : forall x, Sh <= x < Sh + 512 -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hshp x Hx))).
  assert (ST3 : forall x, S - 32768 <= x < S -> exists b, mem3 (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; exact (proj2 (Hstkp x Hx))).
  (* C1 / C2: the run 0x81d28 -> 0x52600 (P5F.p5_pre_F) on the normalized memory (P5F asks mem_inv), moved to the
     cut's memory by MemNormF.evtF_normalize_ro (w3a_SRr_norm). *)
  set (n3 := B.MemNorm.normalize rsegs mem3).
  assert (NR : forall x, 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
                 (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) -> exists b, n3 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hni Hb. unfold n3. rewrite (w3a_norm_raw mem3 x Hx Hni). exact Hb. }
  destruct (w3a_bytes_of_mrd n3 16 (Sh + 370) ltac:(lia) ltac:(lia)) as (xs & Hxl & Hxs).
  { intros x Hx. destruct (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))) as [b Hb].
    exists b. exact (w3a_raw_mrd n3 _ b Hb). }
  destruct (NR (fr + 3040) ltac:(lia) (Hfrimg (fr + 3040) ltac:(lia)) (FR3 (fr + 3040) ltac:(lia))) as [yb Hyb].
  destruct (w3a_cb_raw n3 (fr + 3056) 32 ltac:(lia) ltac:(lia)) as (junk' & Hjunk').
  { intros x Hx. exact (NR x ltac:(lia) (Hfrimg x ltac:(lia)) (FR3 x ltac:(lia))). }
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (w3a_SRr_norm W3 _ _ mem3 md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { exact HRO. }
  { eapply (P5F.p5_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Sh := Sh) (Ab := A)
      (Y := fr + 3040) (D := fr + 3056) (lo := S - 32768) (xs := xs) (yb := yb) (junk := junk').
    - exact Hr2.
    - exact Hr19'.
    - exact Hr9'.
    - exact H24'.
    - unfold B.AsanRT.RT_HI. lia.
    - lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - lia.
    - lia.
    - unfold B.AsanRT.RT_HI. lia.
    - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
    - lia.
    - lia.
    - clear - Efr8. Z.div_mod_to_equations. lia.
    - destruct (w3a_sh_frame fr (fr + 3056) Efr8 ltac:(lia)) as [E1 _]. rewrite E1.
      change (B.ACtlCutP.Sfr fr) with Sh. replace (fr + 3056 - fr) with 3056 by lia. reflexivity.
    - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
    - lia.
    - lia.
    - exact Hxl.
    - apply w3a_rwC1s; [exact Hxs |]. rewrite Hxl. apply w3a_wr_raw; [lia | lia |].
      intros x Hx. exact (NR x ltac:(lia) (NIH x ltac:(lia)) (SH3 x ltac:(lia))).
    - exact (w3a_rw1 n3 (fr + 3040) yb ltac:(lia) Hyb).
    - exact Hjunk'.
    - exact (B.AsanRTFacts.ro_c8 n3 (A + 64) _ (B.MemNorm.bytes_at_normalize rsegs mem3 _ _ HRO Hq64)).
    - exact (B.MemNorm.mem_inv_normalize rsegs mem3).
    - apply w3a_stk_raw; [lia | lia |]. intros x Hx.
      exact (NR x ltac:(lia) (NIH x ltac:(lia)) (ST3 x ltac:(lia))).
    - exact (w3a_asan_norm mem3 HRO HAC).
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hshp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hfrp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros s s0 md1 HP Hrel Hro' Hhid Hsame1.
  destruct HP as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & Es0 & MU1 & WM1 &
    MI1 & STK1 & AC1 & SR1 & RWD1 & ADD1 & B380 & PRES1).
  subst s0.
  destruct (w3a_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es MR].
  set (m' := ms_mem s) in *. clearbody m'. rewrite Es. clear Es Hrel.
  (* C3: the cut's memory after the run, through the normalization relation *)
  pose proof (B.MemNorm.munch_rel rsegs _ mem3 n3 m' m1 (B.MemNorm.mem_rel_normalize rsegs mem3 HRO) MR Hro' MU1)
    as MU.
  assert (MRD : forall a, lib.Lib.Mem.mrd rsegs m' a = lib.Lib.Mem.mrd rsegs m1 a)
    by (intros a; exact (B.MemNorm.mrd_rel rsegs m' m1 a MR)).
  assert (RAWK : forall x, 0 <= x < 2 ^ 64 ->
            lib.Lib.Frame.outside [(Sh + 370, Sh + 386); (fr + 3040, fr + 3040 + 1)] x ->
            m' (lib.Lib.Mem.wa x) = mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Ho. apply MU. rewrite lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (Sh + 370 <= x < Sh + 386) -> ~ (fr + 3040 <= x < fr + 3041) ->
            lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx H1 H2. apply (w3a_mrd_munch _ _ _ x MU Hx). cbn [lib.Lib.Frame.outside].
    split; [lia | split; [lia | exact I]]. }
  assert (WP : forall x, Sh + 370 <= x < Sh + 386 \/ fr + 3040 <= x < fr + 3041 ->
            exists b, m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct (PRES1 x ltac:(lia)) as [b Hb]. rewrite <- MRD in Hb. exists b.
    apply (w3a_mrd_raw m' x b ltac:(lia)); [| exact Hb].
    destruct Hx as [Hx|Hx]; [apply NIH; lia | apply Hfrimg; lia]. }
  assert (PM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mem3 (lib.Lib.Mem.wa x) = Some b) ->
            exists b, m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx Hb. destruct (w3a_outside_dec [(Sh + 370, Sh + 386); (fr + 3040, fr + 3040 + 1)] x) as [Ho|Ho].
    - rewrite (RAWK x Hx Ho). exact Hb.
    - apply WP. destruct (w3a_not_outside2 _ _ _ _ x Ho); lia. }
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 m' md1 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k m' md1 _ HJ MU Hhid Hsame1).
    intros a Ha. destruct (w3a_not_outside2 _ _ _ _ a Ha) as [Ha1|Ha1].
    - split; [apply WP; lia | apply (w3a_awr_fsh cx ly3 fr _ _ _ _ a Efr); lia].
    - split; [apply WP; lia | apply (w3a_awr_fr cx ly3 fr _ _ _ _ a Efr); lia]. }
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x52600) _ _ _ _] => set (R1 := R) end.
  assert (R1_1 : lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x81d68) by reflexivity.
  assert (R1_2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R1_3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R1_4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R1_8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R1_9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite Hr9'; reflexivity).
  assert (R1_10 : lib.Reusable.YK11.getr R1 10 = Reusable.YG0d.w64 (fr + 3056)) by reflexivity.
  assert (R1_11 : lib.Reusable.YK11.getr R1 11 = Reusable.YG0d.w64 0) by reflexivity.
  assert (R1_12 : lib.Reusable.YK11.getr R1 12 = Reusable.YG0d.w64 32) by reflexivity.
  assert (R1_19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite Hr19'; reflexivity).
  assert (R1_23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R1_24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by (rewrite H24'; reflexivity).
  assert (R1_25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R1_26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR1 : Reusable.YG0d.spZ R1 = S + (sp - S)).
  { unfold Reusable.YG0d.spZ in HspZ |- *. rewrite R1_2, HspZ. lia. }
  assert (Hgp1 : lib.Reusable.YK11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B))
    by (rewrite R1_3, Hr3; exact (w3a_gp cx HB)).
  assert (Htp1 : lib.Reusable.YK11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (rewrite R1_4; exact Hr4).
  assert (Ho16 : (sp - S) mod 16 = 0) by (clear - Hsp16 HS16; Z.div_mod_to_equations; lia).
  assert (Hbud : Reusable.YG0d.ESTACK - (sp - S) <= Reusable.YCfn.LLVMF_STK)
    by (rewrite HSTK; change Reusable.YG0d.ESTACK with 4096; lia).
  assert (RETOK : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x81d68)) by (vm_compute; reflexivity).
  assert (HDEST : forall a, fr + 3056 <= a < fr + 3056 + 32 ->
            Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK S FP
              (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (B.ACtlCut.own6 cx) a /\
            ~ (S + (sp - S) - Reusable.YG0d.ESTACK <= a < S + (sp - S))).
  { intros a Ha. split; [apply (w3a_awr_fr cx ly3 fr _ _ _ _ a Efr); lia|].
    change Reusable.YG0d.ESTACK with 4096. lia. }
  assert (ADD' : B.AsanRT.addressable m' (fr + 3056) 32)
    by exact (w3a_addr_keep m1 m' _ _ ADD1 (fun i _ => MRD _)).
  assert (HRAD' : Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m')
                    Reusable.YG0f.SHADOW_OFF (fr + 3056) 32).
  { apply (w3a_range_addr W3 m' _ _ ADD'). intros i Hi.
    destruct (w3a_sh_frame fr (fr + 3056 + i) Efr8 ltac:(lia)) as [E1 E2]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply VS. lia. }
  assert (HHULL : 0 < 32 -> Reusable.YG0d.shadow_hull_vis
                    (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m') (fr + 3056) 32).
  { intros _. apply (w3a_hull_vis W3 m'); [lia | lia|]. intros t Ht.
    destruct (w3a_sh_frame fr (fr + 3056) Efr8 ltac:(lia)) as [E1 E2].
    destruct (w3a_sh_frame fr (fr + 3056 + 32 - 1) Efr8 ltac:(lia)) as [E3 E4].
    rewrite E1, E3 in Ht. change (B.ACtlCutP.Sfr fr) with Sh in Ht.
    split; [apply VS; lia | apply PM; [lia | apply SH3; lia]]. }
  (* C2': __asan_memset (fr + 3056, 0, 32) by the core's rule at the journal (YCbq.aj_intrin_at). *)
  eapply (Reusable.YA0n.SRr_bind segs).
  { exact (Reusable.YCbq.aj_intrin_at segs B LAWS segs_low Reusable.YG0d.OSet
             Reusable.YB1w.tfib_A_asan_memset AMEMSET W3 R1 m' Reusable.YCfn.LLVMF_STK S FP
             (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
             (B.ACtlCut.own6 cx) ly3 S3 md1 k (fr + 3056) 0 32 (sp - S) (Z_to_bv 64 0x81d68)
             HJ1 R1_10 R1_11 R1_12 ltac:(lia) ltac:(lia) ltac:(lia) HspR1 Ho16 ltac:(lia) Hbud
             Hgp1 Htp1 R1_1 RETOK HDEST
             (w3a_amem_frame fr (fr + 3056) 32 Hfr4 Hfrc Hfrlh0 ltac:(lia) ltac:(lia)) HRAD' HHULL I). }
  intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpreg & E10 & Hset & Hfrm & Hpres2).
  (* C3: the raw memory after the call, by ProgWorld's ctl_post_memset (WR = the 32 bytes + the callee window). *)
  assert (HRPF : rt_post_frame W3 m' mem2 [(fr + 3056, fr + 3056 + 32); (sp - Reusable.YG0d.ESTACK, sp)]).
  { split; [|exact Hpres2]. intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
    apply Hfrm; [exact Ha | exact Ho1 |]. intros H'. apply Ho2. lia. }
  assert (FRm' : forall x, fr <= x < fr + 4096 -> exists b, m' (lib.Lib.Mem.wa x) = Some b)
    by (intros x Hx; apply PM; [lia | apply FR3; exact Hx]).
  destruct (B.ProgWorld.ctl_post_memset W3 m' mem2 sp (fr + 3056) 0 32 ltac:(lia) ltac:(lia) ltac:(lia)
              (fun a Ha => conj (VF a ltac:(lia)) (FRm' a ltac:(lia))) Hset HRPF) as (MV & WMV & RW32).
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 3056 <= x < fr + 3088) -> ~ (sp - 4096 <= x < sp) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. apply (w3a_mvis _ _ _ _ x MV Hx Hv). cbn [lib.Lib.Frame.outside].
    change Reusable.YG0d.ESTACK with 4096. split; [lia | split; [lia | exact I]]. }
  assert (KK : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             ~ (fr + 3040 <= x < fr + 3088) -> ~ (sp - 4096 <= x < sp) -> ~ (Sh + 370 <= x < Sh + 386) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2 H3. rewrite (KV x Hx Hv ltac:(lia) H2). apply KEEP; lia. }
  assert (KSHX : forall x, fr <= x < fr + 2960 ->
            lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
            lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))).
  { intros x Hx. destruct (w3a_sh_frame fr x Efr8 ltac:(lia)) as [E1 E2]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply KK; [lia | apply VS; lia | lia | lia | lia]. }
  assert (STK2 : forall x, A <= x < S -> exists b, lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. rewrite (KK x ltac:(lia) (VK x ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct (ST3 x ltac:(lia)) as [b Hb]. exists b. exact (w3a_raw_mrd _ _ _ Hb). }
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- R1_2; exact (Hpreg 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- R1_3; exact (Hpreg 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- R1_4; exact (Hpreg 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- R1_8; exact (Hpreg 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite <- R1_9; exact (Hpreg 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- R1_19; exact (Hpreg 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- R1_23; exact (Hpreg 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (rewrite <- R1_24; exact (Hpreg 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- R1_25; exact (Hpreg 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- R1_26; exact (Hpreg 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (HspZ2 : Reusable.YG0d.spZ regs2 = sp) by (unfold Reusable.YG0d.spZ in HspZ |- *; rewrite E2; exact HspZ).
  pose proof (proj1 HJ2) as HAR2.
  (* C5: the successor cut B81d68. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81d68 regs2 mem2 md2) (POST cx)).
  unfold B.ACtlCut.ctl_from in HD68.
  apply (HD68 cx idx fr k ly3 S3 W3 regs2 mem2 md2 HB);
    cbn [B.ACtlCutP.C_B81d68 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - exact HJ2.
  - exact Hfr.
  - exact HFA.
  - exact Hk.
  - refine (conj Hperm (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    + (* FRAC *)
      apply (w3a_FRAC_keep cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
      * intros x Hx. apply KK; [lia | apply VF; lia | lia | lia | lia].
      * intros x Hx. rewrite (KV x ltac:(lia) (VS x ltac:(lia)) ltac:(lia) ltac:(lia)).
        destruct (PM x ltac:(lia) (SH3 x ltac:(lia))) as [b Hb]. exists b. exact (w3a_raw_mrd _ _ _ Hb).
    + (* OURb *)
      unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HOUR).
      rewrite B.ACtlCutP.SM.OUR_length. intros x Hx. apply KK; [lia | apply VF; lia | lia | lia | lia].
    + (* XC *)
      split.
      * unfold B.ACtlCut.rgv. rewrite E24. exact H24'.
      * split; [lia|]. split; [lia|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
        intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r. split.
        -- unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
        -- exists (Z_to_bv 8 1).
           destruct (w3a_sh_frame fr (fr + 3040) Efr8 ltac:(lia)) as [E1 _].
           replace (fr + 3040 - fr) with 3040 in E1 by lia. change (B.ACtlCutP.Sfr fr) with Sh in E1.
           change (3040 / 8) with 380 in E1. rewrite E1. split.
           ++ rewrite (KV (Sh + 380) ltac:(lia) (VS (Sh + 380) ltac:(lia)) ltac:(lia) ltac:(lia)), MRD.
              destruct B380 as (_ & _ & HB0). specialize (HB0 0%nat ltac:(cbn [length]; lia)).
              cbn [Z.of_nat nth_error] in HB0. rewrite Z.add_0_r in HB0. exact HB0.
           ++ unfold B.AsanRT.shadow_ok. right.
              assert (Hs1 : bv_signed (Z_to_bv 8 1) = 1) by reflexivity. rewrite Hs1.
              split; [clear - Efr8; Z.div_mod_to_equations; lia | lia].
    + (* PRO *)
      apply (w3a_PRO_keep fr regs3 regs2 mem3 mem2 A Hr9 ltac:(lia) ltac:(lia) E9); [| | exact HPRO].
      * intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
      * intros i Hi. apply KSHX. lia.
    + (* spill 64 *)
      exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact Hr9'|].
      apply (w3a_bytes_keep mem3 mem2 _ _ Hq64). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
    + (* PL0 *)
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
        refine (conj Hc0 (conj _ _)); [rewrite E23; exact Hc23 | rewrite E25; exact Hc25].
      * unfold B.ACtlCutP.IDBe in HIDB |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HIDB).
        change (length B.ACtlCutP.RIM.ID0) with 38%nat. intros x Hx.
        apply KK; [lia | apply VF; lia | lia | lia | lia].
      * unfold B.ACtlCutP.FGBe in HFGB |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HFGB).
        change (length B.ACtlCutP.SM.z72) with 72%nat. intros x Hx.
        apply KK; [lia | apply VF; lia | lia | lia | lia].
      * unfold B.ACtlCutP.RAD, B.ACtlCutP.fragb in HRAD |- *. destruct HRAD as (R1a & R2a & R3a).
        refine (conj (w3a_addr_keep mem3 mem2 _ _ R1a _) (conj (w3a_addr_keep mem3 mem2 _ _ R2a _)
          (w3a_addr_keep mem3 mem2 _ _ R3a _))); intros i Hi; apply KSHX; lia.
      * apply (w3a_spill_keep regs3 regs2 mem3 mem2 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
          [| exact H176].
        intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
      * apply (w3a_spill_keep regs3 regs2 mem3 mem2 208 (B.ACtlCutP.fragb fr) A Hr9 ltac:(lia) ltac:(lia)
                 ltac:(lia) E9); [| exact H208].
        intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
      * apply (w3a_FSj0_keep cx fr regs3 regs2 mem3 mem2 HFSJ).
        -- intros x Hx. apply KK; [lia | apply VF; lia | lia | lia | lia].
        -- intros i Hi. apply KSHX. lia.
    + (* KIND_NAME *)
      exact (ctl_kind_name_addressable ly3 S3 W3 mem2 md2 HAR2).
    + (* the group *)
      destruct (w3a_bytes_of_mrd mem2 8 (A + 88) ltac:(lia) ltac:(lia) (fun x Hx => STK2 x ltac:(lia)))
        as (b88 & L88 & B88).
      destruct (w3a_bytes_of_mrd mem2 8 (A + 80) ltac:(lia) ltac:(lia) (fun x Hx => STK2 x ltac:(lia)))
        as (b80 & L80 & B80).
      destruct (w3a_bytes_of_mrd mem2 8 (A + 72) ltac:(lia) ltac:(lia) (fun x Hx => STK2 x ltac:(lia)))
        as (b72 & L72 & B72).
      destruct (w3a_q64_of_bytes mem2 _ _ B88 L88) as (pa & Hpa & Q88).
      destruct (w3a_q64_of_bytes mem2 _ _ B80 L80) as (pp & Hpp & Q80).
      destruct (w3a_q64_of_bytes mem2 _ _ B72 L72) as (pn & Hpn & Q72).
      exists A, pa, pp, pn, (fr + 2768).
      refine (conj _ (conj _ (conj Hpa (conj Hpp (conj Hpn (conj Q88 (conj Q80 (conj Q72
        (conj _ (conj _ _)))))))))).
      * unfold B.ACtlCut.rgv. rewrite E9. exact Hr9'.
      * lia.
      * apply (w3a_bytes_keep mem3 mem2 _ _ Hq208). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply KK; [lia | apply VK; lia | lia | lia | lia].
      * rewrite HspZ2. change B.ACtlCutP.RCIR.REAC_CTRL_IDENTITY_REPLY_K with 9072.
        apply (w3a_stk_addr ly3 S3 W3 mem2 md2 (sp - 9072) 9072 HAR2); try lia.
        unfold Reusable.YG0f.kHighMemBeg. lia.
      * exact (ctl_parse_bc_addressable ly3 S3 W3 mem2 md2 HAR2).
  - (* C4 *)
    exact (w3a_ctlrt cx _ ly3 S3 W3 mem2 md2 k HB HJ2).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81d68 (0x81d68, own6, k <= 14) --S_P6--> B81d80 (0x81d80, own6, k <= 14).  Seg/P6.v seg_P6 :237.
   li a0,0, li a1,0, ld a2,88(s1), ld a3,80(s1), ld a4,72(s1), jal reac_ctrl_identity_reply (refused call: fr = 0,
   so reply_args is false and the result is -1, Seg/P6.v:41-45), return at 0x81d80.  The stretch is CUT at the
   call (the callee takes its own class-1 fake frame; a Theorem Labs lane 23:01Z via a Theorem Labs lane). *)
Lemma seg_P6 : forall POST, CF POST C_B81d80 -> CF POST C_B81d68.
Proof using Hwx LAWS segs_low TREPLY TFIB_SYMS RELRO_IMG RO_OFL ctl_kind_name_addressable.
  (* C0 *)
  intros POST HD80 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [B.ACtlCutP.C_B81d68 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body]
    in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & (H24 & HAD3040) & HPRO & H64 &
    (HCUR & HIDB & HFGB & HRAD & H176 & H208 & HFSJ) & HKN &
    A0 & pa & pp & pn & f & Hg9 & HA0 & Hpa & Hpp & Hpn & Q88 & Q80 & Q72 & Q208 & HADW & HBC).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HAS448 & HSsp & HSapp & Hq336 & Hq48 & Hq40 & Hqh0 & Hqh16 & Hsh & Hsaved & Htr).
  destruct (w3a_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ Hfr HFA)
    as (Efr & _ & Hfr4 & Hfrc & Hfrlh & Hfrhull & Hfrimg & Hfrp & Hshp & HS16 & HSlo & HShi & Hstkp).
  pose proof w3a_P64 as P64. assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HC1 & _). unfold Reusable.YG0f.ASAN_CEIL in HC1.
  assert (HSTK : Reusable.YCfn.LLVMF_STK = 32768) by reflexivity. rewrite HSTK in HSlo, Hstkp.
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof Hfrlh as Hfrlh0. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrlh.
  assert (Efr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (ESh : B.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  set (Sh := B.ACtlCutP.Sfr fr) in *. set (S := B.ACtlCut.c_sp cx) in *.
  assert (PL1 : Sh + 512 <= fr \/ fr + 4096 <= Sh) by (rewrite ESh; destruct Hfrlh; lia).
  assert (PL2 : Sh + 512 <= S - 32768) by (rewrite ESh; lia).
  assert (PL3 : 2147450880 <= Sh) by (rewrite ESh; lia).
  assert (Hr9' : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 A) by exact Hr9.
  assert (Hr19' : lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 Sh) by exact Hr19.
  assert (H24' : lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 (fr + 3040)) by exact H24.
  assert (EA0 : A0 = A).
  { unfold B.ACtlCut.rgv in Hg9. apply w3a_bv_inj; [lia | lia | rewrite <- Hg9; exact Hr9']. }
  subst A0.
  assert (VS : forall x, Sh <= x < Sh + 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hshp x Hx))).
  assert (VF : forall x, fr <= x < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hfrp x Hx))).
  assert (VK : forall x, S - 32768 <= x < S -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
    by (intros x Hx; exact (proj1 (Hstkp x Hx))).
  assert (NIH : forall x, 2147450880 <= x -> ~ Reusable.YG0d.in_img segs x)
    by (intros x Hx; apply w3a_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
  (* C1 / C2: the run 0x81d68 -> 0x848fc (P6F.p6_pre_F), memory unchanged *)
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (P6F.p6_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Ab := A) (pa := pa) (pp := pp) (pn := pn).
    - exact Hr9'.
    - exact Hpa.
    - exact Hpp.
    - exact Hpn.
    - lia.
    - lia.
    - exact (B.AsanRTFacts.ro_c8 mem3 (A + 88) _ Q88).
    - exact (B.AsanRTFacts.ro_c8 mem3 (A + 80) _ Q80).
    - exact (B.AsanRTFacts.ro_c8 mem3 (A + 72) _ Q72).
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia].
    - apply (w3a_vis W3 mem3); [lia | lia | intros a Ha; apply Hstkp; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md1 Hms _ Hsame1. cbv beta in Hms. subst ms'.
  assert (HJ1 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK S FP
                  (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
                  (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md1 k).
  { apply (w3a_after_run cx ly3 S3 W3 mem3 md3 k mem3 md1 [] HJ (lib.Lib.Frame.munch_refl [] mem3)
             (fun _ _ => eq_refl) Hsame1).
    intros a Ha. exfalso. apply Ha. exact I. }
  match goal with |- context [lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x848fc) _ _ _ _] => set (R1 := R) end.
  assert (R1_1 : lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x81d80) by reflexivity.
  assert (R1_2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (R1_3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (R1_4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (R1_8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (R1_9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite Hr9'; reflexivity).
  assert (R1_19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (R1_23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (R1_24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (R1_25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (R1_26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by (unfold Reusable.YG0d.spZ in HspZ |- *; rewrite R1_2; exact HspZ).
  assert (Hgp1 : lib.Reusable.YK11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B))
    by (rewrite R1_3, Hr3; exact (w3a_gp cx HB)).
  assert (Htp1 : lib.Reusable.YK11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (rewrite R1_4; exact Hr4).
  assert (Eok : forall g, B.ACtlCutP.RRP.reply_ok 0 0 pa pp pn g = false) by (intros g; reflexivity).
  (* C2': reac_ctrl_identity_reply (a0 = fr = 0, a1 = len = 0) by its world spec TREPLY at the journal *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs B.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP R1 mem3 md1)
            (POST cx)).
  eapply (Reusable.YA0n.SRr_bind segs).
  { apply (TREPLY Reusable.YCfn.LLVMF_STK S FP (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx)
             (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx) (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md1 k R1 0 0 pa pp pn
             (repeat (Z_to_bv 8 0) 50) HJ1 (w3a_aro cx _ ly3 S3 W3 mem3 md1 k HB HJ1)).
    - rewrite R1_1. vm_compute. reflexivity.
    - unfold Reusable.YG0d.raZ. rewrite R1_1. change (Z_to_bv 64 0x81d80) with (lib.Lib.Mem.wa 0x81d80).
      rewrite lib.Lib.Mem.wa_unsigned by lia. lia.
    - exact Hgp1.
    - exact Htp1.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - exact Hpa.
    - exact Hpp.
    - exact Hpn.
    - rewrite HspR1. exact Hsp16.
    - rewrite HspR1, HSTK. unfold B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK. lia.
    - rewrite HspR1. lia.
    - rewrite Hfr. vm_compute. reflexivity.
    - reflexivity.
    - intros H. exfalso. cbv [B.ACtlCutP.RRP.reply_args] in H. cbn in H. discriminate H.
    - intros H. exfalso. cbv [B.ACtlCutP.RRP.reply_args] in H. cbn in H. discriminate H. }
  intros W2 c2 _ (Hwle & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hpreg & Hfr2 & Hperm2 & Hret & Hkept & _).
  destruct Hkept as (Kst & _ & _ & Kfr & Pst & _).
  rewrite HspR1 in Kst, Pst. unfold B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK in Kst, Pst.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (V2 : forall x, Reusable.YA0n.w_H W3 x = false -> Reusable.YA0n.w_H W2 x = false)
    by (intros x Hx; exact (w3a_vis_wle W3 W2 x Hwle Hx)).
  assert (KST : forall x, 0 <= x < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false ->
             lib.Reusable.YM05.alloc_ceiling <= x -> ~ (sp - 9072 <= x < sp) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hv H1 H2. apply (w3a_mrd_view_eq W3 W2 mem3 mem2 x Hv (V2 _ Hv)). apply Kst; [lia | exact H2]. }
  assert (KFR : forall x, 0 <= x < 2 ^ 64 -> (fr <= x < fr + 4096 \/ Sh <= x < Sh + 512) ->
             lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx Hr. assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false)
      by (destruct Hr; [apply VF | apply VS]; lia).
    apply (w3a_mrd_view_eq W3 W2 mem3 mem2 x Hv (V2 _ Hv)).
    apply (Kfr 6 (B.ACtlCut.c_fpos cx) x Hin6).
    - unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Hr. lia.
    - intros [Hok _]. rewrite Eok in Hok. discriminate. }
  assert (PRF : forall x, Sh <= x < Sh + 512 -> exists b, lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. rewrite (KFR x ltac:(lia) ltac:(lia)). destruct (Hshp x Hx) as [_ (b & Hb)].
    exists b. exact (w3a_raw_mrd _ _ _ Hb). }
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- R1_2; exact (Hpreg 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- R1_3; exact (Hpreg 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- R1_4; exact (Hpreg 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- R1_8; exact (Hpreg 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite <- R1_9; exact (Hpreg 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- R1_19; exact (Hpreg 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- R1_23; exact (Hpreg 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E24 : lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs3 24)
    by (rewrite <- R1_24; exact (Hpreg 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- R1_25; exact (Hpreg 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- R1_26; exact (Hpreg 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (KSs : forall x, A <= x < S -> lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa x))
    by (intros x Hx; apply KST; [lia | apply VK; lia | lia | lia]).
  assert (KSHX : forall x, fr <= x < fr + 4096 ->
            lib.Lib.Mem.mrd rsegs mem2 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
            lib.Lib.Mem.mrd rsegs mem3 (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))).
  { intros x Hx. destruct (w3a_sh_frame fr x Efr8 ltac:(lia)) as [E1 E5]. rewrite E1.
    change (B.ACtlCutP.Sfr fr) with Sh. apply KFR; lia. }
  assert (SPK : forall off v, 0 <= off <= 440 -> B.ACtlCutP.q64 mem3 (A + off) v ->
            B.ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hoff Hq. exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact Hr9'|].
    apply (w3a_bytes_keep mem3 mem2 _ _ Hq). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KSs. lia. }
  (* C5: the exit cut B81d80. *)
  change (Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x81d80 regs2 mem2 md2) (POST cx)).
  unfold B.ACtlCut.ctl_from in HD80.
  apply (HD80 cx idx fr (k + B.Prog.C_reac_ctrl_identity_reply.EV_REPLY) ly2 S2 W2 regs2 mem2 md2 HB);
    cbn [B.ACtlCutP.C_B81d80 B.ACtlCut.cut_pc B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body].
  - exact HJ2.
  - rewrite Hfr2. exact Hfr.
  - exact HFA.
  - unfold B.Prog.C_reac_ctrl_identity_reply.EV_REPLY. lia.
  - refine (conj (Permutation_trans Hperm2 Hperm) (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))).
    + (* FRAC *)
      apply (w3a_FRAC_keep cx fr fr regs3 regs2 mem3 mem2 HFRAC E2 E3 E4 E8 E9 E19 E26).
      * intros x Hx. apply KST; [lia | apply VK; lia | lia | lia].
      * intros x Hx. apply KFR; lia.
      * intros x Hx. exact (PRF x ltac:(lia)).
    + (* OURb *)
      unfold B.ACtlCutP.OURb in HOUR |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HOUR).
      rewrite B.ACtlCutP.SM.OUR_length. intros x Hx. apply KFR; lia.
    + (* a0 = -1 *)
      unfold B.ACtlCut.a0v, B.ACtlCut.rgv. exact Hret.
    + (* PRO *)
      apply (w3a_PRO_keep fr regs3 regs2 mem3 mem2 A Hr9 ltac:(lia) ltac:(lia) E9); [| | exact HPRO].
      * intros x Hx. apply KSs. lia.
      * intros i Hi. apply KSHX. lia.
    + exists f. apply SPK; [lia | exact Q208].
    + exists pa. apply SPK; [lia | exact Q88].
    + exists pp. apply SPK; [lia | exact Q80].
    + exists pn. apply SPK; [lia | exact Q72].
    + apply (w3a_spill_keep regs3 regs2 mem3 mem2 64 (fr + 3056) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [| exact H64].
      intros x Hx. apply KSs. lia.
    + unfold B.ACtlCut.rgv. rewrite E24. exact H24'.
    + apply (w3a_addr_keep mem3 mem2 _ _ HAD3040). intros i Hi. apply KSHX. lia.
    + exact (ctl_kind_name_addressable ly2 S2 W2 mem2 md2 (proj1 HJ2)).
    + (* PL0 *)
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * destruct HCUR as (Hc0 & Hc23 & Hc25). unfold B.ACtlCutP.CUR, B.ACtlCut.rgv in Hc23, Hc25 |- *.
        refine (conj Hc0 (conj _ _)); [rewrite E23; exact Hc23 | rewrite E25; exact Hc25].
      * unfold B.ACtlCutP.IDBe in HIDB |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HIDB).
        change (length B.ACtlCutP.RIM.ID0) with 38%nat. intros x Hx. apply KFR; lia.
      * unfold B.ACtlCutP.FGBe in HFGB |- *. apply (w3a_bytes_keep mem3 mem2 _ _ HFGB).
        change (length B.ACtlCutP.SM.z72) with 72%nat. intros x Hx. apply KFR; lia.
      * unfold B.ACtlCutP.RAD, B.ACtlCutP.fragb in HRAD |- *. destruct HRAD as (R1a & R2a & R3a).
        refine (conj (w3a_addr_keep mem3 mem2 _ _ R1a _) (conj (w3a_addr_keep mem3 mem2 _ _ R2a _)
          (w3a_addr_keep mem3 mem2 _ _ R3a _))); intros i Hi; apply KSHX; lia.
      * apply (w3a_spill_keep regs3 regs2 mem3 mem2 176 (fr + 2688) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
          [| exact H176].
        intros x Hx. apply KSs. lia.
      * apply (w3a_spill_keep regs3 regs2 mem3 mem2 208 (B.ACtlCutP.fragb fr) A Hr9 ltac:(lia) ltac:(lia)
                 ltac:(lia) E9); [| exact H208].
        intros x Hx. apply KSs. lia.
      * apply (w3a_FSj0_keep cx fr regs3 regs2 mem3 mem2 HFSJ).
        -- intros x Hx. apply KFR; lia.
        -- intros i Hi. apply KSHX. lia.
  - (* C4 *)
    exact (w3a_ctlrt cx _ ly2 S2 W2 mem2 md2 _ HB HJ2).
Qed.

End W3a.

(* Stage lemmas of this file (all proved, Qed; their Section hypotheses are listed in the header's BUILD STATE),
   each named and stated as lib/B/ACtl.v's stage hypothesis:
     seg_P1     : forall POST, CF POST C_B81ca8 -> CF POST C_B81c58
     seg_P1_bfc : forall POST, CF POST C_B81ca8 -> CF POST C_B81c60
     seg_P2     : forall POST, CF POST C_B81cb0 -> CF POST C_B81ca8
     seg_P3     : forall POST, CF POST C_B81d18 -> CF POST C_B81cb0
     seg_P4     : forall POST, CF POST C_B81d28 -> CF POST C_B81d18
     seg_P5     : forall POST, CF POST C_B81d68 -> CF POST C_B81d28
     seg_P6     : forall POST, CF POST C_B81d80 -> CF POST C_B81d68
   Trap obligations: UBSan none; the abort branch 0x81c5c is not taken (a0 = 0, inside P1F.p1_pc_pre_F). *)
