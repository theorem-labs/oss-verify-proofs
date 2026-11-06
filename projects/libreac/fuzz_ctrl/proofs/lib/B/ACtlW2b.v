(* lib/B/ACtlW2b.v -- stage glue of image B's (asan-ubsan) cgif-form walk of fuzz_ctrl's LLVMFuzzerTestOneInput,
   piece W2b: the last eight cuts of the 7-pass round trip loop_rt (cut-table-B.tsv rows 20-27
   (a working note, not in this delivery): B81914_at b .. B81ac0_at b).  The loop itself (turn_rt,
   loop_rt, vac_B816ec) is the top's, lib/B/ACtl.v:767-788, :790-797, :319-325.  Written by a Theorem Labs lane (subagent of a Theorem Labs lane) by brief
   bwalk-piece.md (a working note, not in this delivery).  Single writer.  rule 24: no function proved (stage glue
   of a walk; drafting).

   STATUS.  Proved against this branch's core and callee texts, with the same conventions as lib/B/ACtlW2a.v (read its header
   first: route (a), the four proof steps of a stage, the `_F` naming, the Section-hypothesis rule, the build-pass
   rule that turns every unclosed proof into a NAMED Section hypothesis).  No Axiom, no Parameter, no Admitted.
   Closes here: w2_gt_img_top (two equal literals) and every stage lemma seg_R15 .. seg_R21_a5c (Qed modulo this
   Section's named hypotheses, each with its owner).
   Each stage lemma carries the NAME AND STATEMENT of lib/B/ACtl.v's
   stage hypothesis (seg_R15 .. seg_R21_a5c, ACtl.v:429-453), so the top cites it directly.

   THE LATCH.  The round trip's latch (S_R21's 0x81ac4 `addiw s6,s6,1; li a0,7; bne s6,a0`) goes back to B816ec_at at
   turn S b while b < 6; at b = 6 the walk leaves through the tail (strcmp 0x81c54, set_shadow_f8 0x81ca4) to
   B81c58 / B81ca8 (S_R21) or B81c58 / B81c60 (S_R21_a5c).  As ctrl's seg_R21 / seg_R21_a5c (Seg/R21.v:661 / :1206)
   and the top's hypotheses, the latch stages take the head at S b unconditionally; at b = 6 the premise is unused,
   and the top supplies the head at turn 7 by vac_B816ec (ACtl.v:319-325).

   RUNS W2b NEEDS (source lemma at 3803efccea0 -> a Theorem Labs lane's `_F` name, bF-brief.md:36-43 (a working note, not in this delivery); bseg-runs.md:108-123 (a working note, not in this delivery)):
     S_R15     r15_evt R15.v:80 (0x81914 -> free entry, a0 = 0)              -> R15F.r15_evt_F (R15F.v:42)
     S_R16     r16_loop_ind R16.v:84 + r16_evt R16.v:150                     -> R16F.r16_evt_F (R16F.v:119-135: ONE
                                                                               run from 0x8194c at turn i, the
                                                                               32-turn loop included, to the free
                                                                               entry 0x534b4; compare r16_evt_of_F
                                                                               :177)
     S_R17     r17_evt R17.v:60 (reac_ports_parse @0x819cc)                 -> R17F.r17_pre_F (R17F.v:36; no post:
                                                                               return = cut)
     S_R18     r18_evt R18.v:115 (declaration_of @0x81a4c)                  -> R18F.r18_pre_F (R18F.v:227; no post:
                                                                               return = cut)
     S_R19     r19_evt_n R19.v:93 / r19_evt R19.v:157 (bcmp @0x81a64)       -> R19F.r19_pre_F (R19F.v:39; one stretch
                                                                               for both runs)
     S_R20     r20_evt R20.v:194 (0x81a68 -> free entry)                     -> R20F.r20_evt_F (R20F.v:53)
     S_R21     r21_latch_next R21.v:221 (b <= 5, -> 0x816ec)                 -> R21F.r21_latch_next_F (R21F.v:112)
               r21_latch_last R21.v:253 (b = 6, -> 0x81b00)                  -> R21F.r21_latch_last_F (:146)
               r21_tail_evt R21.v:330 (0x81b00 -> strcmp @0x81c54 | 0x81c60) -> R21F.r21_tail_pre_F (:357; h = 0 arm
                                                                               inside it)
               r21_p1_evt_n :475 / r21_p1_evt :557 (set_shadow_f8 @0x81ca4) -> R21F.r21_p1_pre_F (:273; no post:
                                                                               return = cut)
     S_R21_a5c r21_a5c_next R21.v:284 (b <= 5, -> 0x816ec)                   -> R21F.r21_a5c_next_F (R21F.v:65)
               r21_a5c_last R21.v:307 (b = 6, -> 0x81b00), then r21_tail_evt as above, the h = 0 arm stopping at the
               cut 0x81c60.

   SECTION HYPOTHESES OF THIS FILE (sources):
     H_bcmp    Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry   the shared SRr-form contract of B's bcmp
               TRAMPOLINE (porter 23:17Z: owner a Theorem Labs lane, the trampoline composed onto cgif's interceptor-body rule
               abcmp_realizes, YG0d.v:353; journal form aj_bcmp_at YCbq.v:2062), at S_R19's call 0x81a64.  Its entry
               is the Variable B_bcmp_tramp_entry, equal to B.Prog.bcmp_wrap_c.BCMP_WRAP (0x42aac) by the Section
               hypothesis B_bcmp_tramp_at, which the top discharges by reflexivity.
     ASF8      Reusable.SetShadowDefP.aset_shadow_realizesP segs B 0x55144 0xf8   set_shadow_f8 at S_R21's call
               0x81ca4, WITH presence preservation (a Theorem Labs lane's additive lib/Reusable/SetShadowDefP.v; the shared
               ASF8 text of RTPOST-SHARED-B.txt (a working note, not in this delivery)).  Owner a Theorem Labs lane; the top discharges it with
               B.Rt.SetShadow.ctrl_set_shadow_f8P.
     H_strcmp  Reusable.AStrcmpDef.astrcmp_realizes segs B B_strcmp_tramp_entry   the shared SRr-form strcmp contract
               (a Theorem Labs lane, 23:53Z: a working branch 04d425a4ce3, lib/Reusable/AStrcmpDef.v; one Definition for the
               trampoline __wrap_strcmp, 0x42aa0 in B, and the interceptor; shaped like abcmp_realizes: ecall_pre,
               the 2 * ESTACK window, a0 = x, a1 = y, str_meet W mem x y k c1 c2, src_ok / amem_range /
               range_addressable / shadow_hull_vis on both k + 1 byte strings; post a0 = w64 (strcmp_res c1 c2), AR,
               aregs_preserved, memory kept outside the window).  At S_R21 / S_R21_a5c's call 0x81c54 (b = 6, h <> 0);
               the entry is the Variable B_strcmp_tramp_entry, equal to B.Prog.strcmp_wrap_c.STRCMP_WRAP (0x42aa0)
               by the Section hypothesis B_strcmp_tramp_at (the top: reflexivity).
     ctl_post_set_shadow   ProgWorld's raw-memory conversion after the world-form set_shadow_f8 post at S_R21
               (visible-only mrd form, a Theorem Labs lane 00:42Z; the walk's callee window, RTPOST-SHARED-B.txt (a working note, not in this delivery)).
   PROVED MEMBERS, Lemmas of this Section with the shared text as statement and a cited proof (RTPOST-SHARED-B.txt (a working note, not in this delivery)'s
   SWAP OWED list, a working branch 3131914eb3ca):
     img_vis_W            B.ProgBridge.img_vis_W (ProgBridge.v:121): the image range [0x10000, 0x5fe000) is visible
               in every world.  Cited where a W2b callee asks an image range: reac_ports_parse (S_R17: `ExecF.rng RNG
               GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8`, reac_ports_parse_c.v:70).
     ctl_post_bcmp / ctl_post_strcmp   B.ProgWorld.ctl_post_bcmp / ctl_post_strcmp (ProgWorld.v:660 / :661): the
               raw-memory facts after bcmp at S_R19 and strcmp at S_R21 / S_R21_a5c.
     ctl_post_acall_kept  B.ProgWorld.ctl_post_acall_kept (ProgWorld.v:681): from acall_kept the raw mrd read is kept
               at a visible address of a kept class.  Used after B.ACtlW2a.w2_free_81a9c at S_R15 / S_R16 / S_R20,
               with E = the freed block and [slo, shi) = [sp - ASTACK, sp).
     WIN_SH_VIS           B.ProgWorldVisWin.win_sh_vis (ProgWorldVisWin.v:69): the stack window's shadow word cover
               is visible (S_R18).
     from W2a  (B.ACtlW2a): the free-site lemma w2_free_81a9c and w2_phi_not_entry.  W2b states the W2a Section
               hypotheses it needs with W2a's texts: AFREE4, HMOK, HPCF and LAWS go to those lemmas as arguments,
               CHAIN_OF_CUT gives the frame chain at the free site.
   Each `_F` run is lifted here by Reusable.YA0nR.SRr_fevt_hid with B.ProgBridge.fevt_of_evtF at
   B.ProgBridge.RNG_W; the journal moves by Reusable.YCbq.ajournal_exec; every successor cut's ctl_rt_C comes from
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w2b_ctlrt).

   UBSAN TRAPS IN W2b (plan 6.2 / F.4.1 rows 5-8), each stepped inside a `_F` run, so each is discharged by that run's
   premises, which the stage derives:
     row 5  0x81954 (S_R16, B8194c_at): inside R16F.r16_evt_F (R16F.v:119); premise 0 < q (q = phi + 18) and the
            block bytes, from (phi, rnb) in ablocks (al_blocks: 4096 <= phi, phi + req_size rnb <= alloc_ceiling)
            and rnb >= 52
            (RFb: rnb <> 0; SlotModel.v:80); a3 / a4 / i < 32 / s11 = 32 from the body (SIv:1907-1910).
     row 6  0x819bc (S_R17, B819a8_at): inside r17_pre_F (0x819b4 li a0,-18; bltu s4,a0): s4 = phi (RFb rgv 20
            phi) and phi + 50 <= 2^64 (r17_evt premise R17.v:64) from al_blocks.
     row 7  0x819e0 (S_R18, B819d0_at): inside r18_pre_F (0x819d8 ld a0,32(s1); beqz): [A + 32] = 0 from RBE
            `spill regs m 32 0` (ACtlCutP.v:825) = r18_evt premise ov_read (A + 32) = 0 (R18.v:129); a0 = 0 at the
            cut (a0v regs 0) for the beqz at 0x819d0.
     row 8  0x81b18 (S_R21 / S_R21_a5c at b = 6): inside r21_tail_pre_F (0x81b10 ld a0,32(s1); beqz): the same
            [A + 32] = 0 (RBE), r21_tail_evt premise R21.v:339; on S_R21's path r21_latch_last_F's write set is the
            frame shadow (s3 + 296 .. s3 + 313), apart from the spill slot A + 32 (s3 = Sfr fr is shadow memory,
            A + 32 application memory: lib/B/AsanRT.v:15-17), so the RBE fact survives the latch run.
   The branches into the ASan abort sink 0x82fa4 and the report stubs in this stretch are listed, with the run premise
   that refutes each, in a Theorem Labs lane's report (table:
   sink-table.md (a working note, not in this delivery)); in the glue each is a premise of the `_F` run that steps the guard. *)

From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six modules lib/B/Reusable shadows (YI04 YI16 YK11 YK1b YM05 YO09): Required from the core's own path only
   (porter 04:33Z amendment (b)); every use writes lib.Reusable.<X>. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YO09 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG0f Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG00 Reusable.YG01 Reusable.YK06.
(* lib/Lib's raw-memory vocabulary of the call-post facts ctl_post_* (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YB1v Reusable.YB1w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlCut B.ACtlCutP B.ACtlW2a.
(* set_shadow_f8's contract WITH presence preservation (a Theorem Labs lane's additive lib/Reusable/SetShadowDefP.v; the shared
   ASF8 text of RTPOST-SHARED-B.txt (a working note, not in this delivery) at 5826fdf4d4d). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.SetShadowDefP.
(* a Theorem Labs lane's footprint runs of S_R15 .. S_R21_a5c (lib/B/Prog/Seg/<File>F.v), Required QUALIFIED, never Imported
   (porter 23:38Z rule (1)); W2c (R17F-R21F) landed type-check only at a working branch 75ee2d4f9f5.
   Their closure includes lib/B/Contract.v; no statement of this file names it except the one bridge lemma below
   (porter 23:40Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R15F R16F R17F R18F R19F R20F R21F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Contract Reusable.YImgTop.
(* strcmp's shared contract (a working branch 04d425a4ce3). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.AStrcmpDef.
(* The stage proofs' machinery, Required qualified and used in proofs only (no statement of this file names it):
   the kit lift (YA0nR.SRr_fevt_hid / SRr_xregs_eqv over YK04R.fsteps), B's bridge lemmas (ProgBridge:
   fevt_of_evtF, RNG_W, rng_of_visible, cfg_at_MS, rsegs_spans, tfibsegs_rsegs; all proved), the hidden-rom fact
   YA0o.seg_rom_hidden, lib/Lib's machine-state and register-map vocabulary, the proved callee contract of
   reac_ports_parse (S_R17) and ctrl's model / byte lemmas of the round trip (RtmB, RHelp, RcAsanFPLib; all in the
   `_F` runs' closure already). *)
From Coq Require Import Bool.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0nR Reusable.YK04 Reusable.YK04R Reusable.YA0o.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn B.ProgBridge B.AsanRT B.AsanRTFacts B.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState PropExec Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require SlotModel reac_ports_parse_c reac_ports_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFPLib bcmp_wrap_c strcmp_wrap_c declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require rng_asan.
(* declaration_of's closed route-(C) footprint contract (S_R18's call 0x81a4c): a Theorem Labs lane's corollary
   declaration_of_F_holds_closed_on (74be6b218f4, on a working branch 5c9971a4a2b7), cited at S_R18. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require declaration_of_F_closed sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require RtmB RHelp R16 R18 R21 R21Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcIdentModel Prog.RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcSynth Prog.RcEmit Prog.RcLeaf.
(* ProgWorld: the cited RTPOST proofs and win_sh_vis_stmt; Reusable.YF0m: CtrlTSyms. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m B.ProgWorld.
(* WIN_SH_VIS's proof (a Theorem Labs lane's lib/B/ProgWorldVisWin.v). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldVisWin.
(* route (C) (11:15Z): the cut carries B.ACtlRtC.ctl_rt_C, from AR by B.ProgWorldCtlRtC.ctl_rt_C_of_AR. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo.
(* S_R18: the frame facts (YG0s.frame_facts) and declaration_of's mem_inv through MemNorm(F)'s normalization. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0s B.MemNorm B.MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require APostBase.
Import ListNotations.
Local Open Scope Z_scope.

(* The one place Contract's image end meets the walk (porter 23:40Z): R18F.r18_pre_F and R21F.r21_p1_pre_F /
   r21_tail_pre_F state `AC.GT <= x`; the stage proofs rewrite with this lemma, so every statement of this file says
   Reusable.YImgTop.IMG_TOP only.  Both are the literal 0x5fe000 (lib/B/Contract.v:73; YImgTop IMG_TOP 0x5fe000). *)
Lemma w2_gt_img_top : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------
   0. Generic facts of image B's segment list and the core's world, proof-internal (no stage statement names them). *)

(* The kit's segment premise (YA0nR Section e), by computation. *)
Lemma w2b_wx : Reusable.YK04.wx_segs_nowrap Reusable.YB1v.tfibsegs.
Proof. apply Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* Image B's four PT_LOAD spans are contiguous: an image byte is exactly an address of [0x10000, 0x5fe000)
   (ProgBridge.rsegs_spans). *)
Lemma w2b_in_img : forall a,
  Reusable.YG0d.in_img Reusable.YB1v.tfibsegs a <-> 0x10000 <= a < 0x5fe000.
Proof.
  intros a. rewrite B.ProgBridge.tfibsegs_rsegs. split.
  - intros (sg & Hin & H1 & H2).
    pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin) as Hm.
    rewrite B.ProgBridge.rsegs_spans in Hm. cbn [In] in Hm.
    destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
  - intros Ha.
    assert (K : forall b sz, In (b, sz) [(65536, 135168); (200704, 450560); (651264, 12288); (663552, 5619712)] ->
              b <= a < b + sz -> Reusable.YG0d.in_img B.Img0.rsegs a).
    { intros b sz Hb Hr. rewrite <- B.ProgBridge.rsegs_spans in Hb. apply in_map_iff in Hb.
      destruct Hb as (sg & E & Hsg). injection E as E1 E2. exists sg. split; [exact Hsg | lia]. }
    destruct (Z_lt_dec a 200704); [apply (K 65536 135168); [cbn; tauto | lia]|].
    destruct (Z_lt_dec a 651264); [apply (K 200704 450560); [cbn; tauto | lia]|].
    destruct (Z_lt_dec a 663552); [apply (K 651264 12288); [cbn; tauto | lia]|].
    apply (K 663552 5619712); [cbn; tauto | lia].
Qed.

(* YCbq's segs_low premise for image B. *)
Lemma w2b_segs_low : forall a,
  Reusable.YG0d.in_img Reusable.YB1v.tfibsegs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof. intros a Ha. apply w2b_in_img in Ha. unfold Reusable.YG0f.kLowMemEnd. lia. Qed.

(* A byte the core's view reads is visible: a hidden address has no rom byte (YA0o.seg_rom_hidden). *)
Lemma w2b_vis_aview : forall (W : Reusable.YA0n.world Reusable.YB1v.tfibsegs) (mem : word -> option byte) (a : Z),
  Reusable.YG0n.aview Reusable.YB1v.tfibsegs (Reusable.YA0n.w_H W) mem a <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a H. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply H. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite E.
  rewrite (Reusable.YA0o.seg_rom_hidden _ _ _ (Reusable.YA0n.w_Hoff W) E). reflexivity.
Qed.

(* ProgBridge.range_visible from pointwise visibility. *)
Lemma w2b_rv : forall (H : word -> bool) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> H (Z_to_bv 64 a) = false) -> B.ProgBridge.range_visible H lo len.
Proof. intros H lo len H0 H1 H2. split; [exact H0|]. split; [exact H1 | exact H2]. Qed.

(* The shadow bytes of a sub-range [lo, hi] of a block [x, x + n) lie in the block's shadow hull (YG0d.shadow_hull_vis
   form, with YG0f.shadow_addr = SHADOW_OFF + a / 8). *)
Lemma w2b_hull : forall K x n lo hi s, 0 <= x -> x <= lo -> hi <= x + n - 1 -> lo / 8 + K <= s <= hi / 8 + K ->
  (K + x / 8) / 8 * 8 <= s < (K + (x + n - 1) / 8) / 8 * 8 + 8.
Proof. intros K x n lo hi s H0 H1 H2 H3. Z.div_mod_to_equations. lia. Qed.

(* Two-interval write sets: a byte that is not outside is inside one of them. *)
Lemma w2b_out2 : forall a b c d x, ~ lib.Lib.Frame.outside [(a, b); (c, d)] x -> (a <= x < b) \/ (c <= x < d).
Proof.
  intros a b c d x H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_lt_dec x b), (Z_le_dec a x), (Z_lt_dec x d), (Z_le_dec c x);
    first [left; lia | right; lia | exfalso; apply H; repeat split; lia].
Qed.

Lemma w2b_out2_intro : forall a b c d x, (x < a \/ b <= x) -> (x < c \/ d <= x) ->
  lib.Lib.Frame.outside [(a, b); (c, d)] x.
Proof. intros a b c d x H1 H2. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]]. Qed.

(* The frame's shadow lies apart from the frame's own bytes (low frames: the shadow is above LOWMEM_END; high frames:
   the shadow is below them). *)
Lemma w2b_sfr_apart : forall fr, 4096 <= fr ->
  (fr + 4096 <= B.AsanRT.LOWMEM_END \/ (B.AsanRT.HIGHMEM_BEG <= fr /\ fr + 4096 <= B.AsanRT.APPMEM_END)) ->
  fr / 8 + B.AsanRT.ASAN_K + 512 <= fr \/ fr + 4096 <= fr / 8 + B.AsanRT.ASAN_K.
Proof.
  intros fr H0 H. unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A row with an identity record (has <> 0) names a C string of the image: [rname, rname + |rt_nb|) lies in
   [0x10000, 0x5fe000) (RtmB.rb_row_facts: nonzero, + 17 <= 0x5fe000, read-only image bytes; rb_rtm_name: at most
   16 bytes). *)
Lemma w2b_name_img : forall inp, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has (B.Prog.SlotModel.rt_mb inp) <> 0 ->
  0x10000 <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (B.Prog.SlotModel.rt_mb inp) /\
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (B.Prog.SlotModel.rt_mb inp) +
    Z.of_nat (length (B.Prog.SlotModel.rt_nb inp)) <= 0x5fe000.
Proof.
  intros inp Hh.
  pose proof (B.Prog.Seg.RtmB.rb_row_facts (B.Prog.SlotModel.istar inp) (B.Prog.Seg.RtmB.rb_istar_range inp))
    as (_ & Hiff & Hn).
  assert (Hhid : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.em_hid (B.Prog.SlotModel.rt_mb inp) <> 0).
  { intros E. apply Hh. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has.
    unfold B.Prog.SlotModel.rt_mb in *. apply Hiff. exact E. }
  pose proof (proj2 (B.Prog.Seg.RtmB.rb_rtm_hid inp) Hhid) as Hn6.
  pose proof (B.Prog.Seg.RtmB.rb_rtm_name inp Hn6) as (_ & _ & _ & _ & Hlen).
  apply andb_true_iff in Hlen as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
  unfold B.Prog.SlotModel.rt_mb in Hhid. destruct (Hn Hhid) as (Hnm0 & Hnm17 & Hro & _).
  unfold B.Prog.SlotModel.rt_nb, B.Prog.SlotModel.rt_mb in *.
  set (nm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname
               (B.Prog.SlotModel.rowb (B.Prog.SlotModel.istar inp))) in *.
  split; [|lia].
  destruct (B.Prog.SlotModel.img_cstr nm 16) as [|b0 bs] eqn:Ec; [cbn [length] in Hl1; lia|].
  cbn [lib.Lib.Image.ro_bytes_b] in Hro.
  lazymatch type of Hro with
  | context [match ?t with Some _ => _ | None => _ end] => destruct t as [b'|] eqn:Er
  end; [|cbn iota in Hro; discriminate Hro].
  apply andb_true_iff in Hro as [Hro _]. apply andb_true_iff in Hro as [_ Hro].
  unfold lib.Lib.Mem.ro_addr in Hro.
  destruct (Z_lt_le_dec nm 0x10000) as [Hlt|Hge]; [exfalso | exact Hge].
  rewrite Reusable.YCbq.find_segment_none in Hro; [cbn iota in Hro; discriminate Hro|].
  unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia.
  rewrite <- B.ProgBridge.tfibsegs_rsegs. rewrite w2b_in_img. lia.
Qed.

Section W2b.

(* ---------------------------------------------------------------------------------------------------------
   1. The shell's parameters and short names (as lib/B/ACtlW2a.v section 1; ONE PLACE TO ALIGN). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.
Local Notation CF POST X := (B.ACtlCut.ctl_from B MT XM_LIB RLO RHI FP POST X).
(* A cut at turn b, as lib/B/ACtl.v states every W2 stage hypothesis. *)
Local Notation CFb POST X b :=
  (B.ACtlCut.ctl_from B MT XM_LIB RLO RHI FP POST (B.ACtlCut.ix_cut X [Z.of_nat b])).

Local Notation C816ec := (B.ACtlCutP.C_B816ec_at B).
Local Notation C81860 := (B.ACtlCutP.C_B81860_at B).
Local Notation C81914 := (B.ACtlCutP.C_B81914_at B).
Local Notation C8194c := (B.ACtlCutP.C_B8194c_at B).
Local Notation C819a8 := (B.ACtlCutP.C_B819a8_at B).
Local Notation C819d0 := (B.ACtlCutP.C_B819d0_at B).
Local Notation C81a50 := (B.ACtlCutP.C_B81a50_at B).
Local Notation C81a68 := (B.ACtlCutP.C_B81a68_at B).
Local Notation C81aa0 := (B.ACtlCutP.C_B81aa0_at B).
Local Notation C81ac0 := (B.ACtlCutP.C_B81ac0_at B).
Local Notation C81c58 := (B.ACtlCutP.C_B81c58 B).
Local Notation C81c60 := (B.ACtlCutP.C_B81c60 B).
Local Notation C81ca8 := (B.ACtlCutP.C_B81ca8 B).
(* The shell's argument lists for the free-site premises, as lib/B/ACtlW2a.v section 1 writes them (same names, same
   text), so W2a's site lemma and CHAIN_OF_CUT read the same here. *)
Local Notation ctlcx := B.ACtlCut.ctlcx.
Local Notation CBASE cx := (B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
     (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation ENTRYBL cx := (Reusable.YG0d.ablocks B (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx)).
Local Notation rnb := B.ACtlCutP.rnb.
Local Notation own6 := B.ACtlCut.own6.

(* ---------------------------------------------------------------------------------------------------------
   2. Section hypotheses with a published text (sources in the header). *)

(* B's bcmp trampoline entry (porter 23:17Z: intended = the core's bcmp_tramp, lib/Reusable/YTramp.v (not in this delivery); never the
   literal) and its shared SRr-form contract (owner a Theorem Labs lane; the core's abcmp_realizes shape, YG0d.v:353). *)
Variable B_bcmp_tramp_entry : Z.
(* Discharged by the TOP (owner a Theorem Labs lane) by reflexivity when it instantiates the Variable with that constant; no
   YTramp.v (not in this delivery) exists on adc9b58a03c (a Theorem Labs lane ruling 06:2xZ). *)
Hypothesis B_bcmp_tramp_at : B_bcmp_tramp_entry = B.Prog.bcmp_wrap_c.BCMP_WRAP.
Hypothesis H_bcmp : Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry.
(* set_shadow WITH presence preservation (added 08:02Z; a Theorem Labs lane's additive lib/Reusable/SetShadowDefP.v: the
   aset_shadow_realizes premises and post + `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a`; the
   journal updates and B.ProgWorld.ctl_post_set_shadow need it).  The top discharges both with
   B.Rt.SetShadow.ctrl_set_shadow_00P / ctrl_set_shadow_f8P (AR_laws, CtrlTSyms).  Owner a Theorem Labs lane. *)
Hypothesis ASF8 : Reusable.SetShadowDefP.aset_shadow_realizesP segs B 0x55144 0xf8.
(* strcmp (a Theorem Labs lane 23:53Z, Reusable.AStrcmpDef): one Definition for the trampoline and the interceptor; the entry is
   a Variable until the core names it (B's __wrap_strcmp 0x42aa0). *)
Variable B_strcmp_tramp_entry : Z.
(* Discharged by the TOP (owner a Theorem Labs lane) by reflexivity when it instantiates the Variable with that constant; no
   YTramp.v (not in this delivery) exists on adc9b58a03c (a Theorem Labs lane ruling 06:2xZ). *)
Hypothesis B_strcmp_tramp_at : B_strcmp_tramp_entry = B.Prog.strcmp_wrap_c.STRCMP_WRAP.
Hypothesis H_strcmp : Reusable.AStrcmpDef.astrcmp_realizes segs B B_strcmp_tramp_entry.

(* RtPost members this file uses, pasted token for token from the ONE shared text (a Theorem Labs lane's
   working branch 981c1faff75 lib/B/RTPOST-SHARED-B.txt (a working note, not in this delivery); the B twins of a Theorem Labs lane's lib/A/ProgWorld.v
   at c03ce1627b6).  Do not edit here: change the shared text and re-paste.  The members that file's SWAP OWED list
   (15:40Z, a working branch 3131914eb3ca) names PROVED are Lemmas here, each with the shared text as its statement and the
   cited proof (ctl_post_bcmp, ctl_post_strcmp, ctl_post_acall_kept, img_vis_W, WIN_SH_VIS); the rest stay pasted
   Section hypotheses. *)
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

(* ctl_post_bcmp: lib/A/ProgWorld.v at c03ce1627b6 :617-622, ctl_post_window_stmt at K = 2 * ESTACK.  PROVED: B.ProgWorld.ctl_post_bcmp
   (lib/B/ProgWorld.v:660). *)
Lemma ctl_post_bcmp :
  forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp : Z),
    rt_post_frame W mem mem' ((sp - 2 * Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (Reusable.YA0n.w_H W) ((sp - 2 * Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (Reusable.YA0n.w_H W) mem mem'.
Proof. exact B.ProgWorld.ctl_post_bcmp. Qed.

(* ctl_post_strcmp: lib/A/ProgWorld.v at c03ce1627b6 :617-623, ctl_post_window_stmt at K = 2 * ESTACK.  PROVED: B.ProgWorld.ctl_post_strcmp
   (lib/B/ProgWorld.v:661). *)
Lemma ctl_post_strcmp :
  forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp : Z),
    rt_post_frame W mem mem' ((sp - 2 * Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (Reusable.YA0n.w_H W) ((sp - 2 * Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (Reusable.YA0n.w_H W) mem mem'.
Proof. exact B.ProgWorld.ctl_post_strcmp. Qed.

(* ctl_post_set_shadow: lib/A/ProgWorld.v at c03ce1627b6 :678-686 (stated on A; rw_cells open) PLUS THE WALK'S CALLEE WINDOW: the binder sp and
   the second interval (sp - ESTACK, sp) of WR, in rt_post_frame and in munch_vis, are a Theorem Labs lane's agreement 2,
   not lib/A/ProgWorld.v's text. *)
Hypothesis ctl_post_set_shadow :
  forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp q n v : Z),
    0 <= q -> q + n <= 2 ^ 64 -> 0 < n ->
    (forall a, q <= a < q + n -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
    (forall i, 0 <= i < n -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' (q + i) = Some v) ->
    rt_post_frame W mem mem' ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (Reusable.YA0n.w_H W) ((q, q + n) :: (sp - Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' q (lib.Lib.Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) :: nil).

(* kept_class / ctl_post_acall_kept: lib/A/ProgWorld.v at c03ce1627b6 :638-655.  PROVED: B.ProgWorld.ctl_post_acall_kept (lib/B/ProgWorld.v:681,
   kept_class :669 as a Definition).  The ceiling is YM05's RunCeil field
   alloc_ceiling, as acall_kept (Reusable/YCbq.v:826) uses it; lyc / Sc are Reusable.YG0f.alayout /
   Reusable.YG00.astate (lib/A/ProgWorld.v's kept_class binders; untyped in lib/A/ProgWorld.v's lemma, fixed there by acall_kept).  At an
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

(* img_vis_W: the walk's image-visibility bridge name; the shape the stage files already share (lib/B/ACtlW1.v,
   ACtlW3a.v, ACtlW4a-c.v), with the bounds by the core's names Reusable.YImgTop.IMG_LO (0x10000) / IMG_TOP (0x5fe000),
   never the literals (porter 23:40Z; a Theorem Labs lane 2026-10-29).  PROVED: B.ProgBridge.img_vis_W (lib/B/ProgBridge.v:121),
   whose statement is range_visible (w_H W) ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO) over world rsegs
   (rsegs = tfibsegs by ProgBridge.tfibsegs_rsegs, reflexivity). *)
Lemma img_vis_W : forall W : Reusable.YA0n.world segs,
  0 <= Reusable.YImgTop.IMG_LO /\
  Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) <= 2 ^ 64 /\
  forall a, Reusable.YImgTop.IMG_LO <= a <
              Reusable.YImgTop.IMG_LO + (Reusable.YImgTop.IMG_TOP - Reusable.YImgTop.IMG_LO) ->
    Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  pose proof B.ProgBridge.img_vis_W as V. rewrite <- B.ProgBridge.tfibsegs_rsegs in V.
  intros W. exact (V W).
Qed.

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

(* The row names' 8-aligned shadow cover is visible (drafted by a Theorem Labs lane for the strcmp call of seg_R21 /
   seg_R21_a5c, whose AStrcmpDef premises need the name's shadow hull visible; the ctl_kind_name_shadow_vis twin;
   accepted token for token by the walk owner a Theorem Labs lane, 08:2xZ; owner a Theorem Labs lane). *)
Hypothesis ctl_names_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md (inp : list byte),
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb inp) <> 0 -> B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp) <> 0 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W)
    (B.Prog.rng_asan.sh_al8_lo (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp)))
    (B.Prog.rng_asan.sh_al8_hi (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp))
       (Z.of_nat (length (B.ACtlCutP.SM.rt_nb inp))) -
     B.Prog.rng_asan.sh_al8_lo (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb inp))).

(* V6 twin for the KIND_NAME table (added 04:35Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as V6): FLI's KNT (ACtlCutP.v, `addressable m KNA.KIND_NAME 112`, carried by every LK cut) crosses a runtime
   call only through AR, since the image's shadow is allocator-owned. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* The catalogue rows (BOX_CATALOGUE [0x9f620, 0x9f620 + 3256) in .data.rel.ro, a registered 8-aligned global) are
   addressable and their shadow is visible (drafted by a Theorem Labs lane for seg_R18 / seg_R21 / seg_R21_a5c, whose
   runs read the row's shadow bytes; accepted in the pair shape of ctl_kind_name_addressable / ctl_kind_name_shadow_vis
   by the walk owner a Theorem Labs lane, 07:1xZ; owner a Theorem Labs lane). *)
Hypothesis ctl_cat_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.AsanRT.addressable mem B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N).
Hypothesis ctl_cat_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT)
    (B.Prog.rng_asan.sh_al8_hi B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) -
     B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT).

(* The stack window's 8-aligned shadow word cover is visible (S_R18: declaration_of_contract_F's sh_word_rng over
   [sp - DECLARATION_OF_K, sp)).  Statement B.ProgWorld.win_sh_vis_stmt (ProgWorld.v:324).  PROVED:
   B.ProgWorldVisWin.win_sh_vis (lib/B/ProgWorldVisWin.v:69, a Theorem Labs lane). *)
Lemma WIN_SH_VIS : B.ProgWorld.win_sh_vis_stmt B.
Proof. exact (B.ProgWorldVisWin.win_sh_vis B). Qed.

(* The core's AR laws (donor A/ACf2.v:47 `Hypothesis LAWS : AR_laws tfibsegs B`; the same text as lib/B/ACtlW2a.v,
   ACtlW3a.v, ACtlW4e1.v, ACtlW4g.v): al_blocks / al_frames / al_shadow / al_client_img for the visibility of the cut
   ranges a run touches, and YCbq's ajournal_exec / sep_block_frame / frames_bounds; supplied by the core's
   YG0q.AR_laws_ok (lib/B/ACtlAll.v:303).  Accepted as a top obligation by the walk owner (a Theorem Labs lane 04:24Z). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ctl_rt_C, route (C) (11:15Z): every successor cut's ctl_rt_C comes from the PROVED
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR, applied with the two facts below and the current view's arodata_okP, which
   APostBase.arodata_ok_journalP carries from ctl_base's arodata_okS across the journal.  TFIB_SYMS: token for token
   as lib/B/ACtl.v (owner a Theorem Labs lane; the top supplies it).  RELRO_IMG: token for token as lib/B/ACtl.v:152.  RO_OFL: the sink head's
   offset-list head lies above the read-only span (owner: the TOP, by computation at SK := Reusable.YE2k.tfib_sink_head;
   image-A twin lib/A/Prog/ACj1.v:179 states it as the instance RO over the PA layer's segs and relro bounds; walk owner a Theorem Labs lane's ruling 06:47Z, text token for token as lib/B/ACtlW2a.v:272). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* ctl_rt_C at any journal state of a cut (proof-internal). *)
Lemma w2b_ctlrt : forall (cx : ctlcx) own ly S (W : Reusable.YA0n.world segs) mem md k,
  CBASE cx -> AJ cx own ly S W mem md k -> B.ACtlRtC.ctl_rt_C B ly S mem.
Proof.
  intros cx own ly S W mem md k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO0 & _) & _).
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly S W mem md (proj1 HJ)).
  exact (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ own ly S W mem md k HJ HRO0).
Qed.

(* The free site 0x81a9c (S_R15 / S_R16 / S_R20) through lib/B/ACtlW2a.v's site lemma w2_free_81a9c, whose closed
   statement takes these three Section hypotheses of W2a; the texts are W2a's (ACtlW2a.v:251 / :254 / :277), and the
   top discharges them with its own (donor A/ACf3.v:40 / A/AD2o.v:49 / the core's ctrl-B code table, a Theorem Labs lane). *)
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (fx:=fx) (rc:=rc) (SK:=SK) segs B MT.
Hypothesis HMOK : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis HPCF : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code B) = Reusable.YB1w.tfib_A_free.

(* The frame-pointer chain and the call trace at an allocator call: lib/B/ACtlW2a.v's CHAIN_OF_CUT (:316-334), same
   name and text (its lib/Lib names written lib.Lib.X, porter rule (b)); the top's CHAIN_OF_CUT (lib/B/ACtl.v:367)
   discharges it. *)
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
   3. a Theorem Labs lane's `_F` runs: cited from their modules (Required above), never restated (porter 23:38Z).  Statements
   (all proved; R15F and R16F at a working branch efac84ed592, R17F-R21F at
   a working branch 75ee2d4f9f5): R15F.r15_evt_F (R15F.v:42), R16F.r16_evt_F (R16F.v:119),
   R17F.r17_pre_F (R17F.v:36), R18F.r18_pre_F (R18F.v:66), R19F.r19_pre_F (R19F.v:39; the one pre-call
   stretch of r19_evt_n and r19_evt), R20F.r20_evt_F (R20F.v:53), R21F.r21_a5c_next_F (:65) / r21_a5c_last_F (:89) /
   r21_latch_next_F (:112) / r21_latch_last_F (:146) / r21_p1_pre_F (:269) / r21_tail_pre_F (:342).  No `_post_F`
   exists in W2c: each exit cut IS the callee's return pc. *)

(* ---------------------------------------------------------------------------------------------------------
   3b. Stage helpers, proof-internal (no stage statement names them). *)

(* A cut's configuration (YG0d.cfg_at, over YK11.mkst) and lib/Lib's MState.MS state with the Section's fp registers
   are the same record (the SHADOWED NAMES rule of ACtlCut.v: equal by conversion only). *)
Lemma w2b_to_MS : forall (W : Reusable.YA0n.world segs) pc (regs : bvmap 5 word) mem md Q,
  Reusable.YA0n.SRr segs W {| cfg_ms := lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
                                 lib.Reusable.YK11.fp_csr None mem (lib.Reusable.YK11.seg_rom segs);
                              cfg_model := md |} Q ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma w2b_of_MS : forall (W : Reusable.YA0n.world segs) pc (regs : bvmap 5 word) mem md Q,
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q ->
  Reusable.YA0n.SRr segs W {| cfg_ms := lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
                                 lib.Reusable.YK11.fp_csr None mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs);
                              cfg_model := md |} Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

(* RB across a run that keeps s6 / s7 / s9 and misses our[], the identity record and the fragment record. *)
Lemma w2b_RB_keep : forall cx fr b idb fgb (regs regs' : bvmap 5 word) (m m' : word -> option byte) W,
  B.ACtlCutP.RB cx fr b idb fgb regs m -> lib.Lib.Frame.munch W m m' ->
  length idb = 38%nat -> length fgb = 72%nat ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  (forall x, fr + 2176 <= x < fr + 2214 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 2256 <= x < fr + 2328 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> lib.Lib.Frame.outside W x) ->
  B.ACtlCutP.RB cx fr b idb fgb regs' m'.
Proof.
  intros cx fr b idb fgb regs regs' m m' W (Hb & (Hc & Hc23 & Hc25) & HO & H22 & HI & HG) MU Hli Hlg E22 E23 E25
    W1 W2 W3.
  unfold B.ACtlCut.rgv in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; unfold B.ACtlCut.rgv; split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]|].
  split.
  { unfold B.ACtlCutP.OURb in *. apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HO MU).
    rewrite B.Prog.SlotModel.OUR_length. intros x Hx. apply W3. lia. }
  split; [unfold B.ACtlCut.rgv; rewrite E22; exact H22|].
  split.
  { unfold B.ACtlCutP.IDBr in *. apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HI MU).
    rewrite Hli. intros x Hx. apply W1. lia. }
  unfold B.ACtlCutP.FGBr in *. apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HG MU).
  rewrite Hlg. intros x Hx. apply W2. lia.
Qed.

(* RBE across a run that keeps s1 and writes no spill, no shadow byte and no image byte (the name bytes by
   w2b_name_img, the build_as table / box / catalogue row by their image places). *)
Lemma w2b_RBE_keep : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) W A,
  B.ACtlCutP.RBE cx fr regs m -> lib.Lib.Frame.munch W m m' ->
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A <= x < A + 448 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  (forall x, 0x10000 <= x < 0x5fe000 -> lib.Lib.Frame.outside W x) ->
  B.ACtlCutP.RBE cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' W A H MU H9 HA0 HA1 E9 HWA HWsh HWimg.
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  unfold B.ACtlCutP.PRA in HPRA.
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 ->
            B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    exact (B.Prog.Seg.RHelp.rh_spill_keep regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU
             (fun x Hx => HWA x ltac:(lia))). }
  assert (KA : forall p n, B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n)
    by (intros p n Ha; exact (B.Prog.RcAsanFPLib.fl_addressable W m m' p n Ha MU HWsh)).
  assert (KB : forall a bs, 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x5fe000 ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs H0 H1 Hb. apply (B.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU). intros x Hx. apply HWimg. lia. }
  pose proof (B.Prog.Seg.RtmB.rb_mrow_range (B.ACtlCut.c_in cx)) as (Hmr0 & Hmr1 & _).
  pose proof (B.Prog.Seg.RtmB.rb_mb_len (B.ACtlCut.c_in cx)) as Hmbl.
  unfold B.Prog.SlotModel.CAT in Hmr0, Hmr1.
  unfold B.ACtlCutP.RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split; [unfold B.ACtlCutP.OUTA in *; exact (KA _ _ HOUT)|].
  split; [exact (KA _ _ HA2176)|].
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos).
    pose proof (w2b_name_img (B.ACtlCut.c_in cx) (proj1 Hc)) as (Hn0 & Hn1).
    split; [exact Hok|]. split; [apply KB; [exact Hn0 | exact Hn1 | exact Hbytes]|].
    split; [exact (KA _ _ Haddr) | exact Hpos]. }
  split; [exact (KA _ _ HOUR)|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HTBL]|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HBOX]|].
  split; [apply KB; [lia | rewrite Hmbl; lia | exact HMROW]|].
  split; [unfold B.ACtlCutP.PRA; do 10 (split; [apply K; [lia | lia | assumption]|]);
          apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [exact (KA _ _ HA2256)|].
  apply K; [lia | lia | assumption].
Qed.

(* FRAC across a run that keeps sp / gp / tp / s0 / s1 / s3 / s10 and misses the spill area, the frame header, the
   frame shadow, the saved registers and the fake frame's trailer word [fr + 4088, fr + 4096). *)
Lemma w2b_FRAC_keep : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) W,
  B.ACtlCutP.FRAC B cx fr fr regs m -> lib.Lib.Frame.munch W m m' ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall A x, B.ACtlCut.rgv regs 9 A -> fr + 3136 <= A -> A <= x < A + 448 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 392 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.ACtlCut.c_sp cx - 104 <= x < B.ACtlCut.c_sp cx -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 4088 <= x < fr + 4096 -> lib.Lib.Frame.outside W x) ->
  B.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros cx fr regs regs' m m' W
    (A & sp & H2 & Hsp & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr & HA & HAS & HspA & HfrA & HA448 & HS & HSapp &
     Q336 & Q48 & Q40 & Qh & Qe & (sh & Hsh & Hshl) & Hsv & Qtr)
    MU E2 E3 E4 E8 E9 E19 E26 WA WF WS WC WT.
  pose proof HfrA as HfrA'. unfold B.ACtlCutP.FRAME_BYTES in HfrA'.
  pose proof (WA A) as WA'.
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W x) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs)
    by (intros a bs Hx Hb; exact (B.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU Hx)).
  pose proof (lib.Lib.Mem.length_le8) as L8.
  exists A, sp.
  split; [rewrite E2; exact H2|]. split; [exact Hsp|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact H4|].
  unfold B.ACtlCut.rgv in *.
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E3; exact H3|].
  split; [rewrite E19; exact H19|]. split; [rewrite E26; exact H26|].
  do 8 (split; [assumption|]).
  unfold B.ACtlCutP.q64 in *.
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q336]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q48]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q40]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WF; lia | exact Qh]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WF; lia | exact Qe]|].
  split.
  { exists sh. split; [|exact Hshl]. apply KB; [|exact Hsh].
    rewrite Hshl. unfold B.ACtlCutP.Sfr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES.
    change (Z.to_nat (3136 / 8)) with 392%nat. intros x Hx. apply WS. lia. }
  split.
  { apply KB; [|exact Hsv]. intros x Hx. apply WC. split; [lia|].
    assert (Hlen : Z.of_nat (length (B.ACtlCutP.saved_bytes cx)) = 104).
    { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !L8. reflexivity. }
    lia. }
  apply KB; [rewrite L8; intros x Hx; apply WT; lia | exact Qtr].
Qed.

(* FRAC across a run that may write the frame's shadow bytes (each written byte reads back after the run). *)
Lemma w2b_FRAC_keep_sh : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) W,
  B.ACtlCutP.FRAC B cx fr fr regs m -> lib.Lib.Frame.munch W m m' ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall A x, B.ACtlCut.rgv regs 9 A -> fr + 3136 <= A -> A <= x < A + 448 -> lib.Lib.Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> lib.Lib.Frame.outside W x) ->
  (forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 392 ->
     lib.Lib.Frame.outside W x \/ exists bb, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb) ->
  (forall x, B.ACtlCut.c_sp cx - 104 <= x < B.ACtlCut.c_sp cx -> lib.Lib.Frame.outside W x) ->
  (forall x, fr + 4088 <= x < fr + 4096 -> lib.Lib.Frame.outside W x) ->
  B.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros cx fr regs regs' m m' W
    (A & sp & H2 & Hsp & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr & HA & HAS & HspA & HfrA & HA448 & HS & HSapp &
     Q336 & Q48 & Q40 & Qh & Qe & (sh & Hsh & Hshl) & Hsv & Qtr)
    MU E2 E3 E4 E8 E9 E19 E26 WA WF WS WC WT.
  pose proof HfrA as HfrA'. unfold B.ACtlCutP.FRAME_BYTES in HfrA'.
  pose proof (WA A) as WA'.
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W x) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs)
    by (intros a bs Hx Hb; exact (B.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU Hx)).
  pose proof (lib.Lib.Mem.length_le8) as L8.
  exists A, sp.
  split; [rewrite E2; exact H2|]. split; [exact Hsp|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact H4|].
  unfold B.ACtlCut.rgv in *.
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E3; exact H3|].
  split; [rewrite E19; exact H19|]. split; [rewrite E26; exact H26|].
  do 8 (split; [assumption|]).
  unfold B.ACtlCutP.q64 in *.
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q336]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q48]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WA'; [exact H9 | lia | lia] | exact Q40]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WF; lia | exact Qh]|].
  split; [apply KB; [rewrite L8; intros x Hx; apply WF; lia | exact Qe]|].
  split.
  { unfold B.ACtlCutP.Sfr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in *.
    change (Z.to_nat (3136 / 8)) with 392%nat in *.
    pose proof Hsh as (Hs0 & Hs1 & Hsr).
    destruct (B.Prog.Seg.RHelp.rh_bytes_of_present 392 m' (B.AsanRT.shadow_addr fr) ltac:(lia) ltac:(lia))
      as (sh' & Hsh' & Hl').
    { intros k0 Hk0. destruct (WS (B.AsanRT.shadow_addr fr + Z.of_nat k0) ltac:(lia)) as [Ho|Hp]; [|exact Hp].
      destruct (nth_error sh k0) as [bb|] eqn:Eb; [|apply nth_error_None in Eb; lia].
      exists bb. rewrite <- Eb. rewrite <- (Hsr k0 ltac:(lia)). unfold lib.Lib.Mem.mrd.
      rewrite (MU _); [reflexivity|]. unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia. exact Ho. }
    exists sh'. split; [exact Hsh' | exact Hl']. }
  split.
  { apply KB; [|exact Hsv]. intros x Hx. apply WC. split; [lia|].
    assert (Hlen : Z.of_nat (length (B.ACtlCutP.saved_bytes cx)) = 104).
    { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !L8. reflexivity. }
    lia. }
  apply KB; [rewrite L8; intros x Hx; apply WT; lia | exact Qtr].
Qed.

(* FRAC from a byte-run transfer over FRAC's own ranges (the spill area, the frame, the frame shadow, the saved
   registers) and kept registers. *)
Lemma w2b_FRAC_transfer : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  B.ACtlCutP.FRAC B cx fr fr regs m ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall a bs,
     (forall x, a <= x < a + Z.of_nat (length bs) ->
        (exists A, B.ACtlCut.rgv regs 9 A /\ fr + 3136 <= A /\ A + 448 <= B.ACtlCut.c_sp cx /\ A <= x < A + 448) \/
        fr <= x < fr + 4096 \/
        B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 392 \/
        B.ACtlCut.c_sp cx - 104 <= x < B.ACtlCut.c_sp cx) ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs) ->
  B.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros cx fr regs regs' m m'
    (A & sp & H2 & Hsp & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr & HA & HAS & HspA & HfrA & HA448 & HS & HSapp &
     Q336 & Q48 & Q40 & Qh & Qe & (sh & Hsh & Hshl) & Hsv & Qtr)
    E2 E3 E4 E8 E9 E19 E26 KB.
  pose proof HfrA as HfrA'. unfold B.ACtlCutP.FRAME_BYTES in HfrA'.
  pose proof (lib.Lib.Mem.length_le8) as L8.
  exists A, sp.
  split; [rewrite E2; exact H2|]. split; [exact Hsp|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact H4|].
  unfold B.ACtlCut.rgv in *.
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E3; exact H3|].
  split; [rewrite E19; exact H19|]. split; [rewrite E26; exact H26|].
  do 8 (split; [assumption|]).
  unfold B.ACtlCutP.q64 in *.
  split; [apply KB; [rewrite L8; intros x Hx; left; exists A; repeat split; (exact H9 || lia) | exact Q336]|].
  split; [apply KB; [rewrite L8; intros x Hx; left; exists A; repeat split; (exact H9 || lia) | exact Q48]|].
  split; [apply KB; [rewrite L8; intros x Hx; left; exists A; repeat split; (exact H9 || lia) | exact Q40]|].
  split; [apply KB; [rewrite L8; intros x Hx; right; left; lia | exact Qh]|].
  split; [apply KB; [rewrite L8; intros x Hx; right; left; lia | exact Qe]|].
  split.
  { exists sh. split; [|exact Hshl]. apply KB; [|exact Hsh].
    rewrite Hshl. unfold B.ACtlCutP.Sfr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES.
    change (Z.to_nat (3136 / 8)) with 392%nat. intros x Hx. right; right; left. lia. }
  split.
  { apply KB; [|exact Hsv]. intros x Hx. right; right; right. split; [lia|].
    assert (Hlen : Z.of_nat (length (B.ACtlCutP.saved_bytes cx)) = 104).
    { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !L8. reflexivity. }
    lia. }
  apply KB; [rewrite L8; intros x Hx; right; left; lia | exact Qtr].
Qed.

(* RBE from transfers of its spills, of the frame's addressability, of the read-only-data image bytes (the build_as
   table, the catalogue), of read-only image bytes (the box, the row name), and the row name's addressability. *)
Lemma w2b_ro_bytes_b_addr : forall bs A, lib.Lib.Image.ro_bytes_b B.Img0.rsegs A bs = true ->
  forall x, A <= x < A + Z.of_nat (length bs) -> lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true.
Proof.
  induction bs as [|b0 bs IH]; intros A H x Hx; [cbn [length Z.of_nat] in Hx; lia|].
  cbn [lib.Lib.Image.ro_bytes_b] in H.
  lazymatch type of H with
  | context [match ?t with Some _ => _ | None => _ end] => destruct t as [b'|]
  end; [|discriminate H].
  apply andb_true_iff in H as [H Hr]. apply andb_true_iff in H as [_ Ha].
  destruct (Z.eq_dec x A) as [->|Hne]; [exact Ha|].
  apply (IH (A + 1) Hr). cbn [length] in Hx. lia.
Qed.

Lemma w2b_name_ro : forall inp,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has (B.Prog.SlotModel.rt_mb inp) <> 0 ->
  forall x, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (B.Prog.SlotModel.rt_mb inp) <= x <
            OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (B.Prog.SlotModel.rt_mb inp) +
            Z.of_nat (length (B.Prog.SlotModel.rt_nb inp)) ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true.
Proof.
  intros inp Hh.
  pose proof (B.Prog.Seg.RtmB.rb_row_facts (B.Prog.SlotModel.istar inp) (B.Prog.Seg.RtmB.rb_istar_range inp))
    as (_ & Hiff & Hn).
  assert (Hhid : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.em_hid
                   (B.Prog.SlotModel.rowb (B.Prog.SlotModel.istar inp)) <> 0).
  { intros E. apply Hh. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has.
    unfold B.Prog.SlotModel.rt_mb. apply Hiff. exact E. }
  destruct (Hn Hhid) as (_ & _ & Hro & _).
  unfold B.Prog.SlotModel.rt_nb, B.Prog.SlotModel.rt_mb.
  exact (w2b_ro_bytes_b_addr _ _ Hro).
Qed.

Lemma w2b_box_ro : forall x, B.Prog.SlotModel.BOXA <= x < B.Prog.SlotModel.BOXA + 6 ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true.
Proof.
  intros x Hx. unfold B.Prog.SlotModel.BOXA in Hx.
  assert (E : x = 0x21140 \/ x = 0x21141 \/ x = 0x21142 \/ x = 0x21143 \/ x = 0x21144 \/ x = 0x21145) by lia.
  destruct E as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; reflexivity.
Qed.

Lemma w2b_RBE_transfer : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  B.ACtlCutP.RBE cx fr regs m ->
  (forall off v, 0 <= off -> off + 8 <= 448 -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill regs' m' off v) ->
  (forall p n, (p = fr + 544 /\ n = 1492) \/ (p = fr + 2176 /\ n = 38) \/ (p = fr + 2624 /\ n = 6) \/
               (p = fr + 2256 /\ n = 72) ->
     B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n) ->
  (forall a bs,
     (B.ACtlCutP.BAC.BA_FR + 72 <= a /\
      a + Z.of_nat (length bs) <= B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) \/
      B.ACtlCutP.SM.CAT <= a /\ a + Z.of_nat (length bs) <= B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs) ->
  (forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true) ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs) ->
  (B.ACtlCutP.RS6.has (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) <> 0 ->
   B.AsanRT.addressable m' (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)))
     (Z.of_nat (length (B.ACtlCutP.SM.rt_nb (B.ACtlCut.c_in cx))))) ->
  B.ACtlCutP.RBE cx fr regs' m'.
Proof.
  intros cx fr regs regs' m m' H K KA KI KR KN.
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  unfold B.ACtlCutP.PRA in HPRA.
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  pose proof (B.Prog.Seg.RtmB.rb_mrow_range (B.ACtlCut.c_in cx)) as (Hmr0 & Hmr1 & _).
  pose proof (B.Prog.Seg.RtmB.rb_mb_len (B.ACtlCut.c_in cx)) as Hmbl.
  unfold B.ACtlCutP.RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split; [unfold B.ACtlCutP.OUTA in *; apply KA; [left; split; reflexivity | exact HOUT]|].
  split; [apply KA; [right; left; split; reflexivity | exact HA2176]|].
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos).
    split; [exact Hok|]. split; [apply KR; [exact (w2b_name_ro _ (proj1 Hc)) | exact Hbytes]|].
    split; [exact (KN (proj1 Hc) (proj2 Hc)) | exact Hpos]. }
  split; [apply KA; [right; right; left; split; reflexivity | exact HOUR]|].
  split; [apply KI; [left; lia | exact HTBL]|].
  split; [apply KR; [unfold B.Prog.SlotModel.box6; cbn [length map Z.of_nat]; exact w2b_box_ro | exact HBOX]|].
  split; [apply KI; [right; rewrite Hmbl; unfold B.Prog.SlotModel.CAT_ROW, B.Prog.SlotModel.CAT_N in *; lia
                    | exact HMROW]|].
  split; [unfold B.ACtlCutP.PRA; do 10 (split; [apply K; [lia | lia | assumption]|]);
          apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply KA; [right; right; right; split; reflexivity | exact HA2256]|].
  apply K; [lia | lia | assumption].
Qed.

(* Allocator-call transfers (ctl_post_acall_kept): a raw byte run, and an addressability run whose shadow bytes are
   kept, both visible before the call. *)
Lemma w2b_kept_bytes : forall lyc Sc (W W2 : Reusable.YA0n.world segs) memc mem2 slo shi (E : Z -> Prop) a bs,
  Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> Reusable.YA0n.wle W W2 ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     Reusable.YA0n.w_H W (Z_to_bv 64 x) = false /\ kept_class B lyc Sc slo shi E x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs memc a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs.
Proof.
  intros lyc Sc W W2 memc mem2 slo shi E a bs Hk Hwle HX (H0 & H1 & H).
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold lib.Lib.Mem.wa.
  destruct (HX (a + Z.of_nat i) ltac:(lia)) as (Hv & Hc).
  apply (ctl_post_acall_kept B lyc Sc W W2 memc mem2 slo shi E Hk Hwle (Z_to_bv 64 (a + Z.of_nat i)) Hv).
  rewrite lib.Lib.MState.unsigned_lit by lia. exact Hc.
Qed.

Lemma w2b_kept_addr : forall lyc Sc (W W2 : Reusable.YA0n.world segs) memc mem2 slo shi (E : Z -> Prop) p n,
  Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> Reusable.YA0n.wle W W2 ->
  (forall i, 0 <= i < n ->
     Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false /\
     kept_class B lyc Sc slo shi E (B.AsanRT.shadow_addr (p + i))) ->
  B.AsanRT.addressable memc p n -> B.AsanRT.addressable mem2 p n.
Proof.
  intros lyc Sc W W2 memc mem2 slo shi E p n Hk Hwle HX (H0 & Hn & He & HA).
  split; [exact H0|]. split; [exact Hn|]. split; [exact He|]. intros i Hi.
  destruct (HA i Hi) as (Happ & bb & Hbb & Hok). split; [exact Happ|]. exists bb. split; [|exact Hok].
  rewrite <- Hbb. unfold lib.Lib.Mem.wa. destruct (HX i Hi) as (Hv & Hc).
  apply (ctl_post_acall_kept B lyc Sc W W2 memc mem2 slo shi E Hk Hwle _ Hv).
  rewrite lib.Lib.MState.unsigned_lit; [exact Hc|].
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* A run of read-only image bytes is the rom's in every memory that agrees with the rom (ctl_rt's ro_agree). *)
Lemma w2b_ro_bytes : forall memc mem2 a bs,
  B.ACtlK.ro_agree_at memc -> B.ACtlK.ro_agree_at mem2 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs memc a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs.
Proof.
  intros memc mem2 a bs Rc R2 HX (H0 & H1 & H).
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold lib.Lib.Mem.wa.
  pose proof (HX (a + Z.of_nat i) ltac:(lia)) as Hro.
  rewrite (R2 _ Hro), (Rc _ Hro). reflexivity.
Qed.

(* A view read at a visible address is the mrd byte. *)
Lemma w2b_aview_vis : forall (H : word -> bool) (mem : word -> option byte) a, H (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs H mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a)).
Proof.
  intros H mem a Hv.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  rewrite Hv. destruct (mem (Z_to_bv 64 a)); [reflexivity|].
  first [reflexivity | rewrite B.ProgBridge.tfibsegs_rsegs; reflexivity].
Qed.

Lemma w2b_aview_some : forall (H : word -> bool) (mem : word -> option byte) a,
  Reusable.YG0n.apresent H mem a -> Reusable.YG0n.aview segs H mem a <> None.
Proof.
  intros H mem a (Hv & b & Hb). rewrite (w2b_aview_vis H mem a Hv).
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. discriminate.
Qed.

(* A byte run at visible addresses outside a visible-only munch's write set keeps its bytes. *)
Lemma w2b_bytes_mv : forall (H : word -> bool) WR (m m' : word -> option byte) a bs,
  munch_vis H WR m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> H (Z_to_bv 64 x) = false /\ lib.Lib.Frame.outside WR x) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros H WR m m' a bs MV HX (H0 & H1 & Hb). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (Hb i Hi). unfold lib.Lib.Mem.wa. destruct (HX (a + Z.of_nat i) ltac:(lia)) as (Hv & Ho).
  apply MV; [exact Hv|]. rewrite lib.Lib.MState.unsigned_lit by lia. exact Ho.
Qed.

(* Addressability across a visible-only munch whose write set misses the (visible) shadow bytes of the range. *)
Lemma w2b_addr_mv : forall (H : word -> bool) WR (m m' : word -> option byte) p n,
  munch_vis H WR m m' ->
  (forall i, 0 <= i < n -> H (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false /\
     lib.Lib.Frame.outside WR (B.AsanRT.shadow_addr (p + i))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros H WR m m' p n MV HX (H0 & Hn & He & HA).
  split; [exact H0|]. split; [exact Hn|]. split; [exact He|]. intros i Hi.
  destruct (HA i Hi) as (Happ & bb & Hbb & Hok). split; [exact Happ|]. exists bb. split; [|exact Hok].
  rewrite <- Hbb. unfold lib.Lib.Mem.wa. destruct (HX i Hi) as (Hv & Ho).
  apply MV; [exact Hv|]. rewrite lib.Lib.MState.unsigned_lit; [exact Ho|].
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* A byte whose signed value is nonnegative has the same unsigned value (lib/B/BzBridge.v:103, same proof). *)
Lemma w2b_byte_signed_nonneg : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
  revert H. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul Z.div Z.pow].
  change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256. intros H.
  pose proof (Z.div_mod (bv_unsigned b + 128) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned b + 128) 256 ltac:(lia)). lia.
Qed.

(* The core's range_addressable over the view from B's addressable, the shadow bytes visible. *)
Lemma w2b_ra_of_addr : forall (H : word -> bool) (mem : word -> option byte) p n,
  B.AsanRT.addressable mem p n ->
  (forall i, 0 <= i < n -> H (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs H mem) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros H mem p n (H0 & Hn & He & HA) HV x Hx.
  destruct (HA (x - p) ltac:(lia)) as (_ & bb & Hbb & Hok).
  replace (p + (x - p)) with x in Hbb, Hok by lia.
  exists (bv_unsigned bb). split.
  - unfold Reusable.YG0v.shadow_of_addr.
    assert (Es : Reusable.YG0f.SHADOW_OFF + x / 8 = B.AsanRT.shadow_addr x)
      by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
    rewrite Es. pose proof (HV (x - p) ltac:(lia)) as Hv. replace (p + (x - p)) with x in Hv by lia.
    rewrite (w2b_aview_vis H mem _ Hv). rewrite Hbb. reflexivity.
  - unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
    destruct Hok as [Hk|Hk].
    + left. rewrite (w2b_byte_signed_nonneg bb ltac:(lia)). exact Hk.
    + right. rewrite (w2b_byte_signed_nonneg bb ltac:(lia)). lia.
Qed.

(* RB from a byte-run transfer over the frame and kept s6 / s7 / s9. *)
Lemma w2b_RB_transfer : forall cx fr b idb fgb (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  B.ACtlCutP.RB cx fr b idb fgb regs m ->
  length idb = 38%nat -> length fgb = 72%nat ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs 25 ->
  (forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs) ->
  B.ACtlCutP.RB cx fr b idb fgb regs' m'.
Proof.
  intros cx fr b idb fgb regs regs' m m' (Hb & (Hc & Hc23 & Hc25) & HO & H22 & HI & HG) Hli Hlg E22 E23 E25 KB.
  split; [exact Hb|].
  split; [split; [exact Hc|]; unfold B.ACtlCut.rgv in *; split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]|].
  split; [unfold B.ACtlCutP.OURb in *; apply KB; [lia | rewrite B.Prog.SlotModel.OUR_length; lia | exact HO]|].
  split; [unfold B.ACtlCut.rgv in *; rewrite E22; exact H22|].
  split; [unfold B.ACtlCutP.IDBr in *; apply KB; [lia | rewrite Hli; lia | exact HI]|].
  unfold B.ACtlCutP.FGBr in *; apply KB; [lia | rewrite Hlg; lia | exact HG].
Qed.

(* The spill base A is the least nonnegative value of s1: any other nonnegative value is above it. *)
Lemma w2b_rg9_ge : forall (regs : bvmap 5 word) A A', B.ACtlCut.rgv regs 9 A -> B.ACtlCut.rgv regs 9 A' ->
  0 <= A < 2 ^ 64 -> 0 <= A' -> A <= A'.
Proof.
  intros regs A A' H H' HA HA'. unfold B.ACtlCut.rgv in *. rewrite H in H'. apply (f_equal bv_unsigned) in H'.
  rewrite !lib.Lib.MState.unsigned_lit_wrap in H'. rewrite (Z.mod_small A) in H' by lia.
  change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

(* Base equality of the spill base A: two Z values of s1 inside [0, 2^64) are equal. *)
Lemma w2b_rg9_eq : forall (regs : bvmap 5 word) A A', B.ACtlCut.rgv regs 9 A -> B.ACtlCut.rgv regs 9 A' ->
  0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H H' HA HA'. unfold B.ACtlCut.rgv in *. rewrite H in H'. apply (f_equal bv_unsigned) in H'.
  rewrite !lib.Lib.MState.unsigned_lit in H' by lia. lia.
Qed.

(* THE FREE SITE 0x81a9c TO THE CUT B81aa0_at (shared by S_R15 / S_R16 / S_R20): at the free entry with ra = 0x81aa0,
   a0 = phi and the cut facts of the round trip's turn b (FRAC, our[], RBE, RB at turn S b, s5 / s6 / s11) over the
   entry registers regsT and memory memT, W2a's site lemma w2_free_81a9c (CHAIN_OF_CUT for its chain) frees the turn
   block and returns to 0x81aa0, where every fact is kept: registers by aregs_preserved, the bytes by
   ctl_post_acall_kept (spills / saved registers: high memory outside the call window; frame bytes and frame shadow:
   a live frame's, apart from the freed block; the build_as table and the catalogue: image data that is neither owned
   nor errno, ctl_relro_not_owned), the read-only box and row name by ro_agree on both sides, the row name's
   addressability by ctl_names_addressable, and ctl_rt_C by w2b_ctlrt (B.ProgWorldCtlRtC.ctl_rt_C_of_AR). *)
Lemma w2b_free_to_81aa0 : forall POST (b : nat) (cx : ctlcx) fr k phi ly3 S3 (W3 : Reusable.YA0n.world segs)
    (regsT : bvmap 5 word) memT md3,
  CFb POST C81aa0 b ->
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 memT md3 k ->
  Reusable.YG01.frames S3 = own6 cx ->
  (forall cid pos, In (cid, pos) (own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  k <= 2 * Z.of_nat b + 1 -> (b <= 6)%nat ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, rnb cx b)]) ->
  B.ACtlCutP.FRAC B cx fr fr regsT memT -> B.ACtlCut.c_n cx < 2 ^ 26 ->
  B.ACtlCut.rgv regsT 22 (Z.of_nat b) -> B.ACtlCutP.OURb cx fr memT -> B.ACtlCutP.RBE cx fr regsT memT ->
  B.ACtlCut.rgv regsT 21 36 ->
  B.ACtlCutP.RB cx fr b (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) (S b))
    (B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) (S b)) regsT memT ->
  B.ACtlCut.rgv regsT 27 32 ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 memT ->
  B.ACtlCut.rgv regsT 10 phi -> B.ACtlCut.rgv regsT 1 0x81aa0 ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs Reusable.YB1w.tfib_A_free regsT memT md3) (POST cx).
Proof.
  intros POST b cx fr k phi ly3 S3 W3 regsT memT md3 HY HB HJ Hfrs Hfa Hk Hb6 Hperm HFRAC Hn H22 HOUR HRBE H21
    HRB H27 Hrt Ha0 Hra.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qhdr & Qent & Hsh & Hsaved & Qtrl).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (Hsp0m & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 memT md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 memT md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Hinb : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 memT md3 phi (rnb cx b) HAR Hinb)
    as (_ & Hphi4k & Hphice & Hphiapp & _).
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hphiapp.
  pose proof (Reusable.YCbq.sep_block_frame _ _ LAWS ly3 S3 W3 memT md3 phi (rnb cx b) 6
                (B.ACtlCut.c_fpos cx) HAR Hinb Hin6) as Hsep.
  rewrite EF, HFB6 in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  pose proof Hrt as (HAC & HSWc & HSWi & HRO).
  (* ---- the call ---- *)
  pose proof (B.ACtlW2a.w2_phi_not_entry B FP LAWS cx (own6 cx) ly3 S3 W3 memT md3 k phi (rnb cx b) HJ Hperm) as Hnin.
  pose proof HB as ((Hafn & _) & _). pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  destruct (CHAIN_OF_CUT cx (own6 cx) ly3 S3 W3 memT md3 k regsT
              (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) 0x81aa0 HB HJ Hr8 Hra Hsaved
              ltac:(rewrite Hspz; lia) ltac:(rewrite Hspz; lia) ltac:(right; left; reflexivity)) as (ch & Hch & Htr).
  refine (B.ACtlW2a.w2_free_81a9c B MT XM_LIB RLO RHI FP AFREE4 HMOK HPCF cx b phi ly3 S3 W3 regsT memT md3 k
            (sp - B.ACtlCut.c_sp cx) ch (POST cx) HB HJ Hk Hb6 Hperm Hnin Ha0 _ _ _ _ Hr4 Hra Hch Htr _).
  - rewrite Hspz. lia.
  - clear - Hsp16 Hsp0m. Z.div_mod_to_equations. lia.
  - lia.
  - rewrite Hr3. exact Hgp0.
  - intros W2 ly2 S2 regs2 mem2 md2 Hwle HJ2 Hpres Hfrs2 Hperm2 Hkept.
    set (E := fun a => phi <= a < phi + Reusable.YG00.req_size (rnb cx b)) in Hkept.
    set (slo := B.ACtlCut.c_sp cx + (sp - B.ACtlCut.c_sp cx) - Reusable.YG0d.ASTACK) in Hkept.
    set (shi := B.ACtlCut.c_sp cx + (sp - B.ACtlCut.c_sp cx)) in Hkept.
    pose proof (proj1 HJ2) as HAR2.
    pose proof (w2b_ctlrt cx (own6 cx) ly2 S2 W2 mem2 md2 (k + 1) HB HJ2) as Hrt2.
    pose proof Hrt2 as (HAC2 & HSW2c & HSW2i & HRO2).
    assert (G : forall r : Z, Reusable.YG0d.acallee_saved r ->
              lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr regsT (Z_to_bv 5 r))
      by exact Hpres.
    assert (G2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regsT 2)
      by (apply (G 2); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regsT 3)
      by (apply (G 3); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regsT 4)
      by (apply (G 4); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regsT 8)
      by (apply (G 8); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regsT 9)
      by (apply (G 9); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regsT 19)
      by (apply (G 19); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regsT 21)
      by (apply (G 21); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regsT 22)
      by (apply (G 22); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regsT 23)
      by (apply (G 23); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regsT 25)
      by (apply (G 25); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regsT 26)
      by (apply (G 26); unfold Reusable.YG0d.acallee_saved; lia).
    assert (G27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regsT 27)
      by (apply (G 27); unfold Reusable.YG0d.acallee_saved; lia).
    (* the kept classes, each byte visible before the call *)
    assert (KCst : forall x, sp <= x < B.ACtlCut.c_sp cx ->
              Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ kept_class B ly3 S3 slo shi E x).
    { intros x Hx. split; [exact (proj1 (Hwin x ltac:(lia)))|]. left. split; [lia|].
      unfold slo, shi, Reusable.YG0d.ASTACK. lia. }
    assert (KCfr : forall x, fr <= x < fr + 4096 ->
              Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ kept_class B ly3 S3 slo shi E x).
    { intros x Hx. split; [exact (proj1 (proj1 (Hfrb x Hx)))|]. right; right; right.
      exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      - left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite EF, HFB6. lia.
      - unfold E. destruct Hsep as [Hs|Hs]; lia. }
    assert (KCfs : forall x, 2147450880 + fr / 8 <= x < 2147450880 + fr / 8 + 512 ->
              Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ kept_class B ly3 S3 slo shi E x).
    { intros x Hx. split.
      - pose proof (proj1 (Hfrsh (x - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
        replace (2147450880 + fr / 8 + (x - (2147450880 + fr / 8))) with x in Hp by lia. exact (proj1 Hp).
      - right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
        + right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512. lia.
        + unfold E. clear - Hx Hfrapp Hphiapp Hceil. Z.div_mod_to_equations. lia. }
    assert (KCimg : forall x,
              (B.ACtlCutP.BAC.BA_FR + 72 <= x < B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) \/
               B.ACtlCutP.SM.CAT <= x < B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) ->
              Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ kept_class B ly3 S3 slo shi E x).
    { intros x Hx. pose proof (ctl_relro_not_owned x Hx) as (Hno & Hne).
      assert (HBA : 0x10000 <= B.ACtlCutP.BAC.BA_FR + 72 /\
                    B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
        by (split; apply Z.leb_le; vm_compute; reflexivity).
      assert (Hix : 0x10000 <= x < 0x5fe000).
      { destruct Hx as [Hx|Hx]; [lia|].
        unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hx. lia. }
      split; [apply Vimg; lia|]. right; right; left.
      split; [apply w2b_in_img; exact Hix|]. split; assumption. }
    assert (KBfr : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
              lib.Lib.Mem.bytes_at B.Img0.rsegs memT a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
    { intros a bs H0 H1 Hb. apply (w2b_kept_bytes ly3 S3 W3 W2 memT mem2 slo shi E a bs Hkept Hwle); [|exact Hb].
      intros x Hx. apply KCfr. lia. }
    assert (KBst : forall a bs, sp <= a -> a + Z.of_nat (length bs) <= B.ACtlCut.c_sp cx ->
              lib.Lib.Mem.bytes_at B.Img0.rsegs memT a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
    { intros a bs H0 H1 Hb. apply (w2b_kept_bytes ly3 S3 W3 W2 memT mem2 slo shi E a bs Hkept Hwle); [|exact Hb].
      intros x Hx. apply KCst. lia. }
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 ->
              B.ACtlCutP.spill regsT memT off v -> B.ACtlCutP.spill regs2 mem2 off v).
    { intros off v Ho0 Ho1 Hs.
      pose proof (B.Prog.Seg.RHelp.rh_spill_at regsT memT A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1) as Hq.
      exists A. split; [unfold B.ACtlCut.rgv in *; rewrite G9; exact Hr9|].
      unfold B.ACtlCutP.q64 in *. apply KBst; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Hq]. }
    refine (HY cx [Z.of_nat b] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2 Hfrs2 Hfa _ _ Hrt2).
    + cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B81aa0_at]. unfold B.ACtlCutP.ixn. cbn [nth].
      rewrite Nat2Z.id. lia.
    + unfold B.ACtlCutP.C_B81aa0_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
      cbv zeta.
      assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
      rewrite Eb.
      split; [exact Hperm2|].
      split.
      { apply (w2b_FRAC_transfer cx fr regsT regs2 memT mem2 HFRAC G2 G3 G4 G8 G9 G19 G26).
        intros a bs HR Hb. apply (w2b_kept_bytes ly3 S3 W3 W2 memT mem2 slo shi E a bs Hkept Hwle); [|exact Hb].
        intros x Hx. destruct (HR x Hx) as [(A' & HA' & HA'r & HA'c & Hx')|[Hx'|[Hx'|Hx']]].
        - assert (EA : A' = A) by (apply (w2b_rg9_eq regsT A A' Hr9 HA'); lia). subst A'. apply KCst. lia.
        - apply KCfr. exact Hx'.
        - apply KCfs. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx'. lia.
        - apply KCst. lia. }
      split; [exact Hn|]. split; [exact Hb6|].
      split; [unfold B.ACtlCut.rgv in *; rewrite G22; exact H22|].
      split.
      { unfold B.ACtlCutP.OURb in *. apply KBfr; [lia | rewrite B.Prog.SlotModel.OUR_length; lia | exact HOUR]. }
      split.
      { apply (w2b_RBE_transfer cx fr regsT regs2 memT mem2 HRBE KS).
        - intros p n Hpn Ha.
          assert (Hb : fr <= p /\ 0 <= n /\ p + n <= fr + 4096)
            by (destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; lia).
          apply (w2b_kept_addr ly3 S3 W3 W2 memT mem2 slo shi E p n Hkept Hwle); [|exact Ha].
          intros i Hi. apply KCfs. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hi Hb Hfr32.
          Z.div_mod_to_equations. lia.
        - intros a bs Hr Hb. apply (w2b_kept_bytes ly3 S3 W3 W2 memT mem2 slo shi E a bs Hkept Hwle); [|exact Hb].
          intros x Hx. apply KCimg. destruct Hr as [Hr|Hr]; [left | right]; lia.
        - intros a bs Hr Hb. exact (w2b_ro_bytes memT mem2 a bs HRO HRO2 Hr Hb).
        - intros Hh Hr. exact (ctl_names_addressable ly2 S2 W2 mem2 md2 (B.ACtlCut.c_in cx) HAR2 Hh Hr). }
      split; [unfold B.ACtlCut.rgv in *; rewrite G21; exact H21|].
      split.
      { destruct HRB as (Hb' & (Hc & Hc23 & Hc25) & HO & H22' & HI & HG).
        split; [exact Hb'|].
        split; [split; [exact Hc|]; unfold B.ACtlCut.rgv in *; split; [rewrite G23; exact Hc23 | rewrite G25; exact Hc25]|].
        split; [unfold B.ACtlCutP.OURb in *; apply KBfr; [lia | rewrite B.Prog.SlotModel.OUR_length; lia | exact HO]|].
        split; [unfold B.ACtlCut.rgv in *; rewrite G22; exact H22'|].
        split; [unfold B.ACtlCutP.IDBr in *; apply KBfr; [lia | rewrite B.Prog.Seg.RtmB.rb_RID_len; lia | exact HI]|].
        unfold B.ACtlCutP.FGBr in *; apply KBfr;
          [lia | rewrite (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) (S b) ltac:(lia)); lia | exact HG]. }
      unfold B.ACtlCut.rgv in *; rewrite G27; exact H27.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. One lemma per cut, NAMED AND STATED AS lib/B/ACtl.v's stage hypothesis (ACtl.v:429-453, seg_R15 ..
   seg_R21_a5c), proved for every SK and FP (the top instantiates SK := Reusable.YE2k.tfib_sink_head, FP := []). *)

(* B81914_at b (Inv_B81914_at SIv:1896) -> B81aa0_at b.  S_R15 (Slot.v:89; seg_R15 R15.v:456), b = 5 after the
   fragment call (R10's arm, its result a0 = 0).  R15F.r15_evt_F (R15F.v:42; 0x81914 -> the free entry; source
   R15.v:80: premise a0 = 0 from the body's a0v regs 0; no memory access; the guard 0x81914 `beqz a0,0x81a98` takes
   the free path, so the
   abort jump 0x81918 is not reached), then B.ACtlW2a.w2_free_81a9c with phi (rgv regs 20 phi), the live list
   (Permutation bl (ENTRYBL ++ [(phi, rnb)])), w2_phi_not_entry, o / gp / tp from FRAC, CHAIN_OF_CUT at (pc_free_ra0,
   0x81aa0).  Post -> C_B81aa0_at body: Permutation from the site lemma; RB at turn S b is already the body's
   (RB cx fr b (RID (S b)) (RFG (S b))), kept by ctl_post_acall_kept (E = the freed block (phi, rnb cx b); frame
   bytes and frame shadow are a live frame's kept class); RBE / OURb / FRAC kept (the spills are high memory outside
   the window, the image cells non-owned image); rgv 21 36, rgv 22 b, rgv 27 32 by aregs_preserved; ctl_rt_C by
   w2b_ctlrt; k + 1 <= 2b + 2.
   No UBSan trap. *)
Lemma seg_R15 : forall POST (b : nat), CFb POST C81aa0 b -> CFb POST C81914 b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B81914_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & Hperm & HFRAC & Hn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & HRB & H20 & Ha0 & H27).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  (* ---- the run 0x81914 -> the free entry (R15F.r15_evt_F; no memory access), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF. eapply (R15F.r15_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    exact Ha0. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & -> & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P27 & P19 & P21 & P22 & P23 & P25 & P26)
    Hhid1 Hsbm1.
  apply w2b_of_MS.
  assert (G2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by exact P2.
  assert (G3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by exact P3.
  assert (G4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by exact P4.
  assert (G8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by exact P8.
  assert (G9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by exact P9.
  assert (G19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by exact P19.
  assert (G21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by exact P21.
  assert (G22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by exact P22.
  assert (G23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by exact P23.
  assert (G25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by exact P25.
  assert (G26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by exact P26.
  assert (G27 : lib.Reusable.YK11.getr R1 27 = lib.Reusable.YK11.getr regs3 27) by exact P27.
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem3 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem3) (mdc' := md1)
      (Wr := fun _ => False); [exact HJ | | | | | ].
    - intros x _. reflexivity.
    - intros x Hx. exact Hx.
    - intros x _. reflexivity.
    - exact Hsbm1.
    - intros a []. }
  apply (w2b_free_to_81aa0 POST b cx fr k phi ly3 S3 W3 R1 mem3 md1 HY HB HJ1 Hfrs Hfa Hk Hb6 Hperm).
  - apply (w2b_FRAC_keep cx fr regs3 R1 mem3 mem3 [] HFRAC (lib.Lib.Frame.munch_refl [] mem3)
             G2 G3 G4 G8 G9 G19 G26); intros; exact I.
  - exact Hn.
  - unfold B.ACtlCut.rgv in *. rewrite G22. exact H22.
  - exact HOUR.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
    pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
    pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
    unfold Reusable.YCfn.LLVMF_STK in Hstklo2.
    apply (w2b_RBE_keep cx fr regs3 R1 mem3 mem3 [] A HRBE (lib.Lib.Frame.munch_refl [] mem3) Hr9
             ltac:(lia) ltac:(lia) G9); intros; exact I.
  - unfold B.ACtlCut.rgv in *. rewrite G21. exact H21.
  - apply (w2b_RB_keep cx fr b _ _ regs3 R1 mem3 mem3 [] HRB (lib.Lib.Frame.munch_refl [] mem3)
             (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) (S b))
             (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) (S b) ltac:(lia)) G22 G23 G25); intros; exact I.
  - unfold B.ACtlCut.rgv in *. rewrite G27. exact H27.
  - exact Hrt.
  - unfold B.ACtlCut.rgv in *. exact (eq_trans P10 H20).
  - exact P1.
Qed.

(* B8194c_at b (Inv_B8194c_at SIv:1907) -> B81aa0_at b.  S_R16 (Slot.v:91; seg_R16 R16.v:735), b = 1, 2.
   R16F.r16_evt_F (R16F.v:119-135; ONE run from 0x8194c at turn i of the 32-turn block sum (body: rgv 10 / 12
   (phi + 18 + i), rgv 11 (rsum cx b i), rgv 14 (32 - i), rgv 13 (-(phi + 18)), i < 32; q := phi + 18, xs := the 32
   block bytes skipn 18 rt_g, from RFb's bytes_at phi rt_F) to the free entry 0x534b4; sources R16.v:84 / :150:
   a0 .. a4, s11 = 32 (rgv 27 32), s10 = ASAN_K (FRAC rgv 26), i < 32, 0 < q, bytes_at q xs, addressable q 32 (HB:
   addressable phi (a_size rnb) with rnb >= 52), rng RNG q 32 (V3), rng RNG over the shadow of [q, q + 32) (V4),
   psum xs 32 mod 256 = 0 (the block checksum of turns 1 / 2, SlotModel; seg_R16's model lemma); post: memory
   unchanged, ra = 0x81aa0, a0 = s4 = phi), then
   B.ACtlW2a.w2_free_81a9c as for B81914.  TRAP row 5 (0x81954) is stepped inside R16F.r16_evt_F: refuted by 0 < q
   and q + 32 <= alloc_ceiling (al_blocks on (phi, rnb), rnb >= 52), see the header.  The checksum guards (0x81994
   beqz after `zext.b a0,a1`; abort jump 0x81998) are refuted by psum xs 32 mod 256 = 0.  Post -> C_B81aa0_at body
   as for B81914, with RB at turn S b from RFb's RB at (RID b) (RFG b) and the model fact RID (S b) = RID b,
   RFG (S b) = RFG b for b = 1, 2 (the block-sum turns write no record; SlotModel). *)
Lemma seg_R16 : forall POST (b : nat), CFb POST C81aa0 b -> CFb POST C8194c b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B8194c_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & i & Hperm & HFRAC & Hn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hi32 & H10 & H12 &
                     H14 & Hb12 & Hilt & H11 & HRFb & H13 & H27).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2.
  (* the turn block and its 32 checksum bytes at phi + 18 *)
  assert (Hinb : In (phi, rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR Hinb)
    as (_ & Hphi4k & Hphice & _ & Hphipres & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx b) HAR Hinb) as (_ & Hphish).
  pose proof HRFb as (HRB0 & Hnz & H20 & HF).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat b)) with (rnb cx b) in Hnb, HLF.
  assert (Hreq : Reusable.YG00.req_size (rnb cx b) = rnb cx b).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
  rewrite Hreq in Hphice, Hphipres, Hphish.
  unfold Reusable.YG0d.shadow_hull_vis, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hphish.
  destruct (B.Prog.Seg.R16.r16_blk_at mem3 phi (B.Prog.SlotModel.rt_F (B.ACtlCut.c_in cx) (Z.of_nat b)) HF
              ltac:(rewrite HLF; lia)) as (Hxs & Hxsl).
  destruct HHB as (Hphinz & HAphi0).
  assert (Hasz : B.ACtlK.a_size (rnb cx b) = rnb cx b) by (unfold B.ACtlK.a_size; lia).
  pose proof HAphi0 as HAphi. rewrite Hasz in HAphi.
  assert (HAq : B.AsanRT.addressable mem3 (phi + 18) 32)
    by (apply (B.AsanRTFacts.addressable_sub mem3 phi _ 18 32 HAphi); lia).
  assert (Hsum : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.psum
                   (skipn 18 (B.Prog.SlotModel.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))) 32 mod 256 = 0)
    by (apply B.Prog.Seg.R16.r16_rtm_sum; lia).
  (* ---- the run 0x8194c (turn i of the 32-byte block sum) -> the free entry (R16F.r16_evt_F), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (R16F.r16_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (q := phi + 18) (xs := skipn 18 (B.Prog.SlotModel.rt_g (B.ACtlCut.c_in cx) (Z.of_nat b))) (i := i).
    - exact H10.
    - exact H11.
    - exact H12.
    - exact H13.
    - exact H14.
    - exact H27.
    - exact Hr26.
    - exact Hilt.
    - lia.
    - exact Hxsl.
    - exact Hxs.
    - exact HAq.
    - exact Hsum.
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia |].
      intros a Ha. exact (proj1 (proj1 (Hphipres a ltac:(lia)))).
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia | unfold B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
      intros a Ha. apply (w2b_vis_aview W3 mem3). apply Hphish. unfold B.AsanRT.ASAN_K in Ha.
      apply (w2b_hull 2147450880 phi (rnb cx b) (phi + 18) (phi + 18 + 31)); lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & pc1 & m1 & -> & -> & -> & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P22 & P23 &
                  P24 & P25 & P26 & P27) Hhid1 Hsbm1.
  apply w2b_of_MS.
  assert (G2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by exact P2.
  assert (G3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by exact P3.
  assert (G4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by exact P4.
  assert (G8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by exact P8.
  assert (G9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by exact P9.
  assert (G19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by exact P19.
  assert (G21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by exact P21.
  assert (G22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by exact P22.
  assert (G23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by exact P23.
  assert (G25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by exact P25.
  assert (G26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by exact P26.
  assert (G27 : lib.Reusable.YK11.getr R1 27 = lib.Reusable.YK11.getr regs3 27) by exact P27.
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem3 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem3) (mdc' := md1)
      (Wr := fun _ => False); [exact HJ | | | | | ].
    - intros x _. reflexivity.
    - intros x Hx. exact Hx.
    - intros x _. reflexivity.
    - exact Hsbm1.
    - intros a []. }
  (* the block-sum turns b = 1, 2 write no record: RID / RFG at turn S b are turn b's *)
  destruct (B.Prog.Seg.R16.r16_RS_012 (B.ACtlCut.c_in cx) b ltac:(lia)) as (ERID & ERFG).
  apply (w2b_free_to_81aa0 POST b cx fr k phi ly3 S3 W3 R1 mem3 md1 HY HB HJ1 Hfrs Hfa ltac:(lia) Hb6 Hperm).
  - apply (w2b_FRAC_keep cx fr regs3 R1 mem3 mem3 [] HFRAC (lib.Lib.Frame.munch_refl [] mem3)
             G2 G3 G4 G8 G9 G19 G26); intros; exact I.
  - exact Hn.
  - unfold B.ACtlCut.rgv in *. rewrite G22. exact H22.
  - exact HOUR.
  - apply (w2b_RBE_keep cx fr regs3 R1 mem3 mem3 [] A HRBE (lib.Lib.Frame.munch_refl [] mem3) Hr9
             ltac:(lia) ltac:(lia) G9); intros; exact I.
  - unfold B.ACtlCut.rgv in *. rewrite G21. exact H21.
  - rewrite ERID, ERFG.
    apply (w2b_RB_keep cx fr b _ _ regs3 R1 mem3 mem3 [] HRB0 (lib.Lib.Frame.munch_refl [] mem3)
             (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) b)
             (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) b ltac:(lia)) G22 G23 G25); intros; exact I.
  - unfold B.ACtlCut.rgv in *. rewrite G27. exact H27.
  - exact Hrt.
  - unfold B.ACtlCut.rgv in *. exact (eq_trans P10 H20).
  - exact P1.
Qed.

(* B819a8_at b (Inv_B819a8_at SIv:1916) -> B819d0_at b.  S_R17 (Slot.v:93; seg_R17 R17.v:149), b = 0.
   R17F.r17_pre_F (R17F.v:36; 0x819a8 -> reac_ports_parse entry, ra = 0x819d0; source R17.v:60: s1 = A, a0 = mr
   (a0v regs mrow, the catalogue match result), s4 = phi (RFb rgv 20 phi), A + 448 <= 2^64 (FRAC), phi + 50 <= 2^64
   (al_blocks),
   bytes_at (A + 272) (le8 mrow) (RBE spill 272), bytes_at (A + 120) (le8 q) with q = fr + 2528 (spill 120), the 20
   port bytes at phi + 18 (RFb bytes_at phi rt_F), q 4-aligned and writable 12 (fake frame, T8), the 16-byte callee
   window (T1), outside-cells (T9), ports_ok (SlotModel / RcLeaf: rt_pbs at b = 0)); the guards: 0x819ac `beq
   a0,a1` with a1 = [A + 272] = mrow (abort jump 0x819b0 refuted by a0 = mrow), TRAP row 6 0x819bc refuted by
   phi < 2^64 - 18.  Then reac_ports_parse_F_holds_on (a Theorem Labs lane, whole lift by SRr_fevt_hid; premises = reac_ports_parse_contract_F_on's,
   reac_ports_parse_c.v:129; its `rng RNG GOT_CELL_K 8 /\ rng RNG CELL_K 8` (:146) <- img_vis_W with RNG := RNG_W
   (w_H W3)) -> 0x819d0 = the successor cut.  Post -> C_B819d0_at body: rgv 18 (phi + 18), a0v regs 0
   (the parse result), u32 (fr + 2528) (4 n_in rt_pbs), u32 (fr + 2532) (4 n_out rt_pbs) (the parse writes q, q + 4),
   spills 120 / 24 / 16 / 96 kept, RFb kept (the callee's write set is q .. q + 12 and its window). *)
Lemma seg_R17 : forall POST (b : nat), CFb POST C819d0 b -> CFb POST C819a8 b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B819a8_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & Hperm & HFRAC & Hn & Hb6 & HHB & H22 & HOUR & HCUR & S120 & HRBE & H21 & Hb0 & HRFb &
                     Ha0 & S24 & S16 & S96 & HAQ & H27).
  subst b.
  (* ---- the cut's facts ---- *)
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & Q336 & Q48 & Q40 & Qhdr & Qent & Hsh & Hsaved & Qtrl).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfrb a Ha)))).
  assert (Pfr : forall a, fr <= a < fr + 4096 -> exists bb, mem3 (Z_to_bv 64 a) = Some bb)
    by (intros a Ha; exact (proj2 (proj1 (Hfrb a Ha)))).
  assert (Vfrsh : forall a, Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. pose proof (proj1 (Hfrsh (a - Reusable.YG0f.shadow_addr fr) ltac:(lia))) as Hp.
    replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hp by lia.
    exact (proj1 Hp). }
  assert (Fnoimg : forall a, fr <= a < fr + 4096 -> ~ (0x10000 <= a < 0x5fe000)).
  { intros a Ha Hi. apply w2b_in_img in Hi.
    refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR _) Hi).
    right. left. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite EF, HFB6. exact Ha. }
  assert (Hinb : In (phi, B.ACtlCutP.rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (B.ACtlCutP.rnb cx 0) HAR Hinb)
    as (_ & Hphi4k & Hphice & _ & Hphipres & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi (B.ACtlCutP.rnb cx 0) HAR Hinb)
    as (_ & Hphish).
  pose proof (Reusable.YCbq.sep_block_frame _ _ LAWS ly3 S3 W3 mem3 md3 phi (B.ACtlCutP.rnb cx 0) 6
                (B.ACtlCut.c_fpos cx) HAR Hinb Hin6) as Hsep.
  pose proof HRFb as (HRB0 & Hnz & H20 & HF).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 0)) with (B.ACtlCutP.rnb cx 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  assert (Hreq : Reusable.YG00.req_size (B.ACtlCutP.rnb cx 0) = B.ACtlCutP.rnb cx 0).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
  rewrite Hreq in Hphice, Hphipres, Hphish, Hsep.
  rewrite EF, HFB6 in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  unfold Reusable.YG0d.shadow_hull_vis, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hphish.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Vfrsh.
  assert (HLS : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 18) (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx))).
  { rewrite (B.Prog.Seg.RtmB.rb_pbs_F (B.ACtlCut.c_in cx)).
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 phi (B.Prog.SlotModel.rt_F (B.ACtlCut.c_in cx) 0) 18 20 HF
                  ltac:(rewrite HLF; lia)) as Hs.
    replace (phi + Z.of_nat 18) with (phi + 18) in Hs by lia. exact Hs. }
  pose proof (B.Prog.Seg.RtmB.rb_pbs_len (B.ACtlCut.c_in cx)) as Hpbslen.
  destruct HHB as (Hphinz & HAphi0).
  assert (Hasz : B.ACtlK.a_size (B.ACtlCutP.rnb cx 0) = B.ACtlCutP.rnb cx 0) by (unfold B.ACtlK.a_size; lia).
  pose proof HAphi0 as HAphi. rewrite Hasz in HAphi.
  assert (HAp : B.AsanRT.addressable mem3 (phi + 18) 20)
    by (apply (B.AsanRTFacts.addressable_sub mem3 phi _ 18 20 HAphi); lia).
  pose proof (B.AsanRTFacts.addressable_app mem3 _ _ HAQ) as Happq.
  assert (Hok : B.ACtlCutP.RLF.ports_ok (phi + 18) (fr + 2528) (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)) = true).
  { unfold B.ACtlCutP.RLF.ports_ok. rewrite (B.Prog.Seg.RtmB.rb_rtm_decl (B.ACtlCut.c_in cx)), !andb_true_r.
    apply andb_true_intro. split; apply negb_true_iff; apply Z.eqb_neq; lia. }
  assert (Vstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hwin a Ha))).
  assert (Pstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   exists bb, mem3 (Z_to_bv 64 a) = Some bb)
    by (intros a Ha; exact (proj2 (Hwin a Ha))).
  destruct Hrt as (HAC & HSWc & HSWi & HRO).
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  pose proof HRBE as (S128 & S312 & S272 & _).
  assert (Q272 : B.ACtlCutP.q64 mem3 (A + 272) (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)))
    by exact (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 272 _ S272 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (Q120 : B.ACtlCutP.q64 mem3 (A + 120) (fr + 2528))
    by exact (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 120 _ S120 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  (* ---- the run 0x819a8 -> reac_ports_parse (R17F.r17_pre_F), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (R17F.r17_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (A := A) (phi := phi) (q := fr + 2528) (mr := B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)).
    - exact Hr9.
    - exact Ha0.
    - exact H20.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Q272.
    - exact Q120.
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & -> & P1 & P10 & P11 & P18 & P2 & P3 & P4 & P8 & P9 & P19 & P20 & P21 & P22 & P23 & P24 &
                  P25 & P26 & P27) Hhid1 Hsbm1.
  assert (ER2 : Sem.reg_get R1 2 = Z_to_bv 64 sp) by (transitivity (Sem.reg_get regs3 2); [exact P2 | exact Hr2]).
  assert (Esp : bv_unsigned (Sem.reg_get R1 2) = sp) by (rewrite ER2; apply lib.Lib.MState.unsigned_lit; lia).
  assert (ER1 : Sem.reg_get R1 1 = Z_to_bv 64 0x819d0) by exact P1.
  (* ---- reac_ports_parse by its proved footprint contract, lifted ---- *)
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of R1) R1 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv R1))].
  unfold Lib.Regs6ss.mkR_of.
  pose proof B.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on as PP.
  unfold B.Prog.reac_ports_parse_c.reac_ports_parse_contract_F_on in PP.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md1 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply PP with (p := phi + 18) (q := fr + 2528) (lo := sp - 16)
                   (bs := B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)).
    all: unfold B.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; try rewrite Esp.
    - exact P10.
    - exact P11.
    - lia.
    - lia.
    - split; [lia|]. split; [lia|]. intros a Ha.
      destruct (Pstk a ltac:(lia)) as (bb & Hbb).
      unfold lib.Lib.Mem.wa, wview, lib.Lib.Mem.mrd. rewrite Hbb. split; [discriminate | exists bb; reflexivity].
    - lia.
    - intros _ _. split; [exact Hpbslen | exact HLS].
    - intros _ _. split; [clear - Hfr32; Z.div_mod_to_equations; lia|].
      split.
      { split; [lia|]. split; [lia|]. intros i Hi.
        destruct (Pfr (fr + 2528 + i) ltac:(lia)) as (bb & Hbb).
        unfold lib.Lib.Mem.wa, wview. rewrite Hbb. discriminate. }
      split; [destruct Hsep as [Hs|Hs]; [right | left]; lia|].
      split; [left; lia | left; lia].
    - intros _ _. split; [exact HAC|]. split; [exact HAp | exact HAQ].
    - intros _ _ x Hx. apply w2b_out2_intro.
      + left. destruct Hx as [Hx|[Hx|Hx]];
          unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END,
            B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in *; lia.
      + destruct (Z_lt_dec x (fr + 2528)) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_le_dec (fr + 2528 + 12) x) as [Hr|Hr]; [right; exact Hr|]. exfalso.
        destruct Hx as [Hx|[Hx|Hx]].
        * apply (Fnoimg x); [lia|]. unfold B.AsanRT.GOT_CELL_K in Hx. lia.
        * apply (Fnoimg x); [lia|]. unfold B.AsanRT.CELL_K in Hx. lia.
        * exact (B.AsanRTFacts.app_not_shadow x (Happq x ltac:(lia)) Hx).
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - intros _ _. split; [|split; [|split; [|split; [|split]]]].
      + apply B.ProgBridge.rng_of_visible, w2b_rv; [unfold B.AsanRT.GOT_CELL_K; lia | unfold B.AsanRT.GOT_CELL_K; lia |].
        intros a Ha. apply Vimg. unfold B.AsanRT.GOT_CELL_K in Ha. lia.
      + apply B.ProgBridge.rng_of_visible, w2b_rv; [unfold B.AsanRT.CELL_K; lia | unfold B.AsanRT.CELL_K; lia |].
        intros a Ha. apply Vimg. unfold B.AsanRT.CELL_K in Ha. lia.
      + apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia |].
        intros a Ha. exact (proj1 (proj1 (Hphipres a ltac:(lia)))).
      + apply B.ProgBridge.rng_of_visible, w2b_rv;
          [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia
          | unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
        intros a Ha. apply (w2b_vis_aview W3 mem3). apply Hphish.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
        apply (w2b_hull 2147450880 phi (B.ACtlCutP.rnb cx 0) (phi + 18) (phi + 18 + 19)); lia.
      + apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vfr; lia].
      + apply B.ProgBridge.rng_of_visible, w2b_rv;
          [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia
          | unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
        intros a Ha. apply Vfrsh. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
        clear - Ha Hfr32. Z.div_mod_to_equations. lia. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms2 md2 PO Hhid2 Hsbm2.
  unfold B.Prog.reac_ports_parse_c.reac_ports_parse_post in PO. rewrite Hok in PO. cbv iota in PO.
  destruct PO as (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E2 & WM & _ & STc &
                  HIc & HOc & H8c & MUc).
  subst ms2.
  rewrite Esp in MUc. unfold B.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME in MUc.
  rewrite ER1, (lib.Lib.MState.ret_pc_even 0x819d0) by first [lia | reflexivity].
  apply w2b_of_MS.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R2 := R) end.
  (* ---- the successor cut C_B819d0_at at turn 0 ---- *)
  set (Wr := [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]) in MUc.
  assert (HoutW : forall x, (x < sp - 16 \/ sp <= x) -> (x < fr + 2528 \/ fr + 2540 <= x) -> lib.Lib.Frame.outside Wr x)
    by (intros x H1 H2; apply w2b_out2_intro; lia).
  assert (HoutSh : forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside Wr x).
  { intros x Hx. apply HoutW.
    - left. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
        B.AsanRT.HIGHMEM_BEG in Hx. lia.
    - destruct (Z_lt_dec x (fr + 2528)) as [Hl|Hl]; [left; exact Hl|].
      destruct (Z_le_dec (fr + 2540) x) as [Hr|Hr]; [right; exact Hr|]. exfalso.
      exact (B.AsanRTFacts.app_not_shadow x (Happq x ltac:(lia)) Hx). }
  assert (HoutImg : forall x, 0x10000 <= x < 0x5fe000 -> lib.Lib.Frame.outside Wr x).
  { intros x Hx. apply HoutW; [left; lia|].
    destruct (Z_lt_dec x (fr + 2528)) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_le_dec (fr + 2540) x) as [Hr|Hr]; [right; exact Hr|]. exfalso. exact (Fnoimg x ltac:(lia) Hx). }
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside Wr x) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs)
    by (intros a bs Hx Hb; exact (B.Prog.RcAsanFPLib.fl_bytes Wr mem3 m' a bs Hb MUc Hx)).
  assert (KS : forall off v, 0 <= off -> off + 8 <= 448 ->
            B.ACtlCutP.spill regs3 mem3 off v -> B.ACtlCutP.spill R2 m' off v).
  { intros off v Ho0 Ho1 Hs.
    exact (B.Prog.Seg.RHelp.rh_spill_keep regs3 R2 mem3 m' Wr A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1 P9 MUc
             (fun x Hx => HoutW x ltac:(lia) ltac:(lia))). }
  assert (HJ2 : AJ cx (own6 cx) ly3 S3 W3 m' md2 k).
  { (* the journal across the two lifted runs *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := m') (mdc' := md2)
      (Wr := fun a => (sp - 16 <= a < sp) \/ (fr + 2528 <= a < fr + 2540)); [exact HJ | | | | |].
    + intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MUc x); [reflexivity|]. apply HoutW; lia.
    + intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Ex; [exact Hx|].
      destruct (B.Prog.Seg.RHelp.rh_out_dec Wr (bv_unsigned x)) as [Ho|Ho]; [rewrite (MUc x Ho); exact Hx|].
      apply w2b_out2 in Ho.
      assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)).
      { rewrite w2b_in_img. intros Hi. destruct Ho as [Ho|Ho]; [lia | exact (Fnoimg (bv_unsigned x) ltac:(lia) Hi)]. }
      assert (Hw0 : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity]. }
      pose proof (WM x Hw0) as Hw. unfold wview in Hw.
      rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
      destruct (m' x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
    + intros x Hx. pose proof (Hhid1 x Hx) as E1. pose proof (Hhid2 x Hx) as E2'.
      cbn [ms_mem lib.Lib.MState.MS] in E1, E2'. rewrite E2'. exact E1.
    + exact (Reusable.YK04.same_but_materialized_trans _ _ _ Hsbm1 Hsbm2).
    + intros a [Ha|Ha]; [left; unfold Reusable.YCfn.LLVMF_STK; lia|].
      right; right; right. exists 6, (B.ACtlCut.c_fpos cx).
      split; [cbn; left; reflexivity|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6. lia. }
  refine (HY cx [Z.of_nat 0] fr k ly3 S3 W3 R2 m' md2 HB HJ2 Hfrs Hfa _ _ (w2b_ctlrt cx (own6 cx) ly3 S3 W3 m' md2 k HB HJ2)).
  - cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B819d0_at]. unfold B.ACtlCutP.ixn. cbn [nth]. lia.
  - unfold B.ACtlCutP.C_B819d0_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
    cbv zeta. change (B.ACtlCutP.ixn 0 [Z.of_nat 0]) with 0%nat.
    exists phi.
    split; [exact Hperm|].
    split.
    { apply (w2b_FRAC_keep cx fr regs3 R2 mem3 m' Wr HFRAC MUc); try assumption.
      - intros A' x HA' HA'r Hx.
        assert (EA : sp <= A').
        { unfold B.ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'. apply (f_equal bv_unsigned) in HA'.
          rewrite !lib.Lib.MState.unsigned_lit_wrap in HA'. rewrite (Z.mod_small A) in HA' by lia.
          change (2 ^ 64) with 18446744073709551616 in HA'. Z.div_mod_to_equations. lia. }
        apply HoutW; lia.
      - intros x Hx. apply HoutW; lia.
      - intros x Hx. apply HoutW.
        + left. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. Z.div_mod_to_equations. lia.
        + unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. clear - Hx Hfrapp Hceil Hfr32. Z.div_mod_to_equations.
          lia.
      - intros x Hx. apply HoutW; lia.
      - intros x Hx. apply HoutW; lia. }
    split; [exact Hn|]. split; [exact Hb6|].
    split; [split; [exact Hphinz | exact (B.Prog.RcAsanFPLib.fl_addressable Wr mem3 m' phi _ HAphi0 MUc HoutSh)]|].
    split; [unfold B.ACtlCut.rgv in *; transitivity (lib.Reusable.YK11.getr regs3 22); [exact P22 | exact H22]|].
    split.
    { unfold B.ACtlCutP.OURb in *. apply (KB _ _); [|exact HOUR].
      rewrite B.Prog.SlotModel.OUR_length. intros x Hx. apply HoutW; lia. }
    split.
    { destruct HCUR as (Hc & Hc23 & Hc25). split; [exact Hc|]. unfold B.ACtlCut.rgv in *.
      split; [transitivity (lib.Reusable.YK11.getr regs3 23); [exact P23 | exact Hc23]
             | transitivity (lib.Reusable.YK11.getr regs3 25); [exact P25 | exact Hc25]]. }
    split; [apply KS; [lia | lia | exact S96]|].
    split.
    { apply (w2b_RBE_keep cx fr regs3 R2 mem3 m' Wr A HRBE MUc Hr9 ltac:(lia) ltac:(lia) P9).
      - intros x Hx. apply HoutW; lia.
      - exact HoutSh.
      - exact HoutImg. }
    split; [unfold B.ACtlCut.rgv in *; transitivity (lib.Reusable.YK11.getr regs3 21); [exact P21 | exact H21]|].
    split; [reflexivity|].
    split.
    { destruct HRFb as (HRB & _ & _ & _). split.
      - apply (w2b_RB_keep cx fr 0 _ _ regs3 R2 mem3 m' Wr HRB MUc
                 (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 0)
                 (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) 0 ltac:(lia)) P22 P23 P25);
          intros x Hx; apply HoutW; lia.
      - split; [exact Hnz|]. split; [unfold B.ACtlCut.rgv in *; transitivity (lib.Reusable.YK11.getr regs3 20);
                                     [exact P20 | exact H20]|].
        apply (KB _ _); [|exact HF]. change (Z.of_nat 0) with 0. rewrite HLF. intros x Hx. apply HoutW; [left; lia|].
        destruct Hsep as [Hs|Hs]; [left | right]; lia. }
    split; [exact P18|].
    split; [reflexivity|].
    split; [exact HIc|].
    split; [replace (fr + 2532) with (fr + 2528 + 4) by lia; exact HOc|].
    split; [apply KS; [lia | lia | exact S120]|].
    split; [apply KS; [lia | lia | exact S24]|].
    split; [apply KS; [lia | lia | exact S16]|].
    unfold B.ACtlCut.rgv in *. transitivity (lib.Reusable.YK11.getr regs3 27); [exact P27 | exact H27].
Qed.

(* ---- S_R18's helpers: the class-6 frame lies above the image; byte facts across MemNorm's normalized memory
   (declaration_of's contract takes mem_inv, which the core's world gives only on MemNorm.normalize, ProgWorld.v:119-128). *)

(* The class-6 frame lies above the image end: the fake stack is disjoint from the image and starts above 0x10000
   (YG0s.frame_facts, layout_ok's lo_img), and no frame byte is an image byte (al_client_img). *)
Lemma w2b_frame_above_img : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  0x5fe000 <= Reusable.YG0f.frame_addr ly 6 pos.
Proof.
  intros ly S W mem md pos HAR Hin.
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ 6 pos (proj1 HAR) Hin)
    as (_ & _ & HFapp & HFimg & _ & HFO & _).
  pose proof (Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR)) as HLO.
  pose proof (Reusable.YG0f.lo_img _ HLO) as (Himg0 & Himg1 & _).
  unfold Reusable.YG0f.in_app in HFapp.
  assert (HlyF : 0x10000 < Reusable.YG0f.ly_F ly).
  { destruct (Z_lt_le_dec 0x10000 (Reusable.YG0f.ly_F ly)) as [H|H]; [exact H|]. exfalso. apply HFimg.
    exists 0x10000. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Himg0.
    unfold Reusable.YG0f.kFakeStackSize, Reusable.YG0f.kImgLo. split; [lia|]. left. lia. }
  assert (Hni : ~ Reusable.YG0d.in_img segs (Reusable.YG0f.frame_addr ly 6 pos)).
  { refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly S W mem md _ HAR _)).
    right. left. exists 6, pos. split; [exact Hin|].
    assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    first [rewrite HFB6; lia | unfold Reusable.YG0n.in_zr; cbn [fst snd]; rewrite HFB6; lia]. }
  rewrite w2b_in_img in Hni. unfold Reusable.YG0f.frame_addr in *.
  unfold Reusable.YG0f.kFakeFramesOff in HFO. lia.
Qed.

(* A non-image address is not read-only. *)
Lemma w2b_ro_false : forall x : word, ~ (0x10000 <= bv_unsigned x < 0x5fe000) ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs x = false.
Proof.
  intros x Hx. unfold lib.Lib.Mem.ro_addr.
  rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x)); [reflexivity|].
  rewrite <- B.ProgBridge.tfibsegs_rsegs, w2b_in_img. exact Hx.
Qed.

Lemma w2b_wmono_rel : forall m m0 m' m0' : word -> option byte,
  B.MemNorm.mem_rel B.Img0.rsegs m m0 -> B.MemNorm.mem_rel B.Img0.rsegs m' m0' ->
  B.MemNorm.ro_same B.Img0.rsegs m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m0 m0' ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m'.
Proof.
  intros m m0 m' m0' HR HR' Ho HW x Hx. destruct (lib.Lib.Mem.ro_addr B.Img0.rsegs x) eqn:E.
  - unfold wview in *. rewrite (Ho x E). exact Hx.
  - rewrite <- (B.MemNorm.wview_rel_rw B.Img0.rsegs m' m0' x HR' E). apply HW.
    rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 x HR E). exact Hx.
Qed.

Lemma w2b_addr_rel : forall (m m0 : word -> option byte) p n, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & Hn & He & HA). split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Happ & bb & Hbb & Hok). split; [exact Happ|]. exists bb.
  split; [|exact Hok]. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ HR). exact Hbb.
Qed.

Lemma w2b_addr_rel' : forall (m m0 : word -> option byte) p n, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.AsanRT.addressable m0 p n -> B.AsanRT.addressable m p n.
Proof.
  intros m m0 p n HR (H0 & Hn & He & HA). split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Happ & bb & Hbb & Hok). split; [exact Happ|]. exists bb.
  split; [|exact Hok]. rewrite (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ HR). exact Hbb.
Qed.

Lemma w2b_stk_rel : forall (m m0 : word -> option byte) lo hi, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> (forall a, lo <= a < hi -> ~ (0x10000 <= a < 0x5fe000)) ->
  lib.Lib.Frame.stk B.Img0.rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H) Hni. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 _ HR); [exact Hw|]. apply w2b_ro_false.
    unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia. exact (Hni a Ha).
  - exists b. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ HR). exact Hb.
Qed.

Lemma w2b_stk_keep : forall W (m m' : word -> option byte) lo hi,
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi -> lib.Lib.Frame.munch W m m' ->
  (forall x, lo <= x < hi -> lib.Lib.Frame.outside W x) -> lib.Lib.Frame.stk B.Img0.rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU HO. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). unfold wview, lib.Lib.Mem.mrd in Hw, Hb |- *.
  rewrite (MU (lib.Lib.Mem.wa a)); [split; [exact Hw | exists b; exact Hb]|].
  unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia. exact (HO a Ha).
Qed.

Lemma w2b_rwc_rel : forall (m m0 : word -> option byte) A cs, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (lib.Lib.Cells.cells_size cs) -> ~ (0x10000 <= a < 0x5fe000)) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m0 A cs.
Proof.
  intros m m0 A cs HR ((Hwf & Hb) & (H0 & H1 & Hw)) Hni.
  split; [split; [exact Hwf | exact (proj1 (B.MemNorm.bytes_at_rel B.Img0.rsegs m m0 _ _ HR) Hb)]|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 _ HR); [exact (Hw i Hi)|]. apply w2b_ro_false.
  unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by lia. apply Hni. lia.
Qed.

Lemma w2b_cells_rel : forall (m m0 : word -> option byte), B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.AsanRT.asan_cells m -> B.AsanRT.asan_cells m0.
Proof.
  intros m m0 HR H.
  pose proof (fun a bs => proj1 (B.MemNorm.bytes_at_rel B.Img0.rsegs m m0 a bs HR)) as K.
  unfold B.AsanRT.asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat (split; [apply K; assumption|]). apply K; assumption.
Qed.

(* B819d0_at b (Inv_B819d0_at SIv:1927) -> B81a50_at b.  S_R18 (Slot.v:95; seg_R18 R18.v:259), b = 0.
   R18F.r18_pre_F_on (R18F.v:114; 0x819d0 -> declaration_of entry, ra = 0x81a50; AC.GT rewritten by w2_gt_img_top;
   source R18.v:115: s1 = A, s10 = ASAN_K (FRAC rgv
   26), a0 = 0 (a0v regs 0: the guard 0x819d0 `beqz a0`, abort jump 0x819d4 refuted), the spill reads [A + 32] = 0
   (RBE spill 32 0: TRAP row 7 0x819e0 refuted), [A + 24] = mrow + 16 and [A + 16] = mrow + 20 (spills 24 / 16), [A +
   120] = q = fr + 2528 (spill 120), the shadow bytes of mrow + 16 / mrow + 20 = 0 (catalogue rows are registered
   globals: V6 / T10), the port words v1 / v2 at q / q + 4 (the body's u32 facts) and at mrow + 16 / mrow + 20 (the
   catalogue row rt_mb: RBE bytes_at mrow rt_mb) equal (the abort jumps 0x81a08 / 0x81a30 after `beq a0,a1` are
   refuted by these equalities: seg_R18's model lemma that the parsed port counts match the matched row),
   rw_cells (s3 + 320) [CB 4] (frame shadow, V5), the decl slot D = fr + 2560 (spill 96, decl_slot), ro_agree
   (ctl_rt)).  Then declaration_of_F_holds_closed_on (a Theorem Labs lane, whole lift by SRr_fevt_hid; declaration_of_contract_F_on,
   declaration_of_c.v:208) -> 0x81a50 = the successor cut.  Post -> C_B81a50_at body: rgv 10 vd with vd <> 0 (the
   declaration_of result, a0 = 1 at R18.v:150), bytes_at (decl_slot fr) (decl rt_mb) (rw_cells D [CB 32 (decl
   row)]), length 32, addressable (decl_slot fr) 32, rgv 18 (phi + 18), RFb and RBE kept. *)
Lemma seg_R18 : forall POST (b : nat), CFb POST C81a50 b -> CFb POST C819d0 b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B819d0_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & Hperm & HFRAC & Hn & Hb6 & HHB & H22 & HOUR & HCUR & Hsp96 & HRBE & H21 & Hb0 & HRFb &
                     H18 & Ha0 & Hu1 & Hu2 & S120 & S24 & S16 & H27).
  subst b.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  assert (Hl392 : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  unfold B.ACtlCutP.Sfr in Hsh, Hr19.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (Hsp0m & _ & Hstklo & Hstklo2 & Hstkhi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hspb : B.ACtlCut.c_sp cx - 4096 < sp /\ sp + 448 <= B.ACtlCut.c_sp cx /\ sp <= A /\
                 A + 448 <= B.ACtlCut.c_sp cx) by lia.
  assert (Hstk : lib.Reusable.YM05.alloc_ceiling + 32768 <= B.ACtlCut.c_sp cx) by lia.
  assert (Hsh_lo : forall a, 0 <= a < 2 ^ 47 -> B.AsanRT.shadow_addr a + 4096 < sp - 8192).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Ha Hceil Hstk Hspb.
    Z.div_mod_to_equations. lia. }
  (* ---- the frame (above the image), its shadow ---- *)
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HfrGT : 0x5fe000 <= fr).
  { rewrite <- EF. exact (w2b_frame_above_img ly3 S3 W3 mem3 md3 (B.ACtlCut.c_fpos cx) HAR Hin6). }
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Pfrsh : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists bb, mem3 (Z_to_bv 64 a) = Some bb).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
    pose proof (proj1 (Hfrsh (a - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
    replace (2147450880 + fr / 8 + (a - (2147450880 + fr / 8))) with a in Hp by lia. exact Hp. }
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfrb a Ha)))).
  assert (Pfr : forall a, fr <= a < fr + 4096 -> exists bb, mem3 (Z_to_bv 64 a) = Some bb)
    by (intros a Ha; exact (proj2 (proj1 (Hfrb a Ha)))).
  assert (Vstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hwin a Ha))).
  assert (Pstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   exists bb, mem3 (Z_to_bv 64 a) = Some bb)
    by (intros a Ha; exact (proj2 (Hwin a Ha))).
  assert (HSb : B.AsanRT.shadow_addr fr + 512 <= B.AsanRT.HIGHMEM_BEG /\ 2147450880 <= B.AsanRT.shadow_addr fr)
    by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG; clear - Hfrce Hceil Hfr4k;
        Z.div_mod_to_equations; lia).
  pose proof (w2b_sfr_apart fr ltac:(lia)) as Hap.
  assert (Happ' : fr + 4096 <= B.AsanRT.LOWMEM_END \/
                  (B.AsanRT.HIGHMEM_BEG <= fr /\ fr + 4096 <= B.AsanRT.APPMEM_END))
    by (unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  specialize (Hap Happ').
  assert (HapS : B.AsanRT.shadow_addr fr + 512 <= fr \/ fr + 4096 <= B.AsanRT.shadow_addr fr)
    by (unfold B.AsanRT.shadow_addr; lia).
  clear Hap. rename HapS into Hap.
  assert (Hshf0 : B.AsanRT.shadow_addr fr + 4096 < sp - 8192) by (apply Hsh_lo; lia).
  pose proof HSb as HSb'. unfold B.AsanRT.HIGHMEM_BEG in HSb'.
  assert (Es3 : bv_unsigned (Sem.reg_get regs3 19) = B.AsanRT.shadow_addr fr).
  { assert (E19 : Sem.reg_get regs3 19 = Z_to_bv 64 (B.AsanRT.shadow_addr fr)) by exact Hr19.
    rewrite E19. apply lib.Lib.MState.unsigned_lit. unfold B.AsanRT.HIGHMEM_BEG in HSb. lia. }
  assert (Esp : bv_unsigned (Sem.reg_get regs3 2) = sp).
  { assert (E2 : Sem.reg_get regs3 2 = Z_to_bv 64 sp) by exact Hr2. rewrite E2.
    apply lib.Lib.MState.unsigned_lit. lia. }
  (* ---- the turn block ---- *)
  assert (Hinb : In (phi, rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR Hinb)
    as (_ & Hphi4k & Hphice & Hphiapp & Hphipres & _).
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hphiapp.
  pose proof (Reusable.YCbq.sep_block_frame _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) 6
                (B.ACtlCut.c_fpos cx) HAR Hinb Hin6) as Hsep.
  pose proof HRFb as (HRB0 & Hnz & H20 & HF).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 0)) with (rnb cx 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  assert (Hreq : Reusable.YG00.req_size (rnb cx 0) = rnb cx 0).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
  rewrite Hreq in Hphice, Hphipres, Hsep, Hphiapp.
  rewrite EF, HFB6 in Hsep. unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  destruct HHB as (Hphinz & HAphi0).
  assert (Hasz : B.ACtlK.a_size (rnb cx 0) = rnb cx 0) by (unfold B.ACtlK.a_size; lia).
  (* ---- the catalogue row ---- *)
  pose proof (B.Prog.Seg.RtmB.rb_mrow_range (B.ACtlCut.c_in cx)) as (Hmr0 & Hmr1 & Hmr8).
  pose proof (B.Prog.Seg.RtmB.rb_mb_len (B.ACtlCut.c_in cx)) as Hmblen.
  unfold B.Prog.SlotModel.CAT in Hmr0, Hmr1.
  pose proof (ctl_cat_addressable ly3 S3 W3 mem3 md3 HAR) as HCA.
  pose proof (ctl_cat_shadow_vis ly3 S3 W3 mem3 md3 HAR) as HCV.
  assert (EL : B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT = 2147532480) by (vm_compute; reflexivity).
  assert (EH : B.Prog.rng_asan.sh_al8_hi B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) =
               2147532896) by (vm_compute; reflexivity).
  rewrite EL, EH in HCV. destruct HCV as (_ & _ & VCs).
  assert (HA16 : B.AsanRT.addressable mem3 (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16) 8).
  { pose proof (B.AsanRTFacts.addressable_sub mem3 B.ACtlCutP.SM.CAT _
                  (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) - B.ACtlCutP.SM.CAT + 16) 8 HCA) as H.
    unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in H.
    replace (652832 + (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) - 652832 + 16))
      with (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16) in H by lia.
    apply H; lia. }
  assert (Hmr8' : (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16) mod 8 = 0)
    by (clear - Hmr8; Z.div_mod_to_equations; lia).
  pose proof (B.Prog.Seg.RHelp.rh_meta0 mem3 _ (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16) HA16 Hmr8'
                ltac:(lia)) as Ksh16.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 mem3 _ (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 20) HA16 Hmr8'
                ltac:(lia)) as Ksh20.
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24' & S16' &
    S96 & S120' & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR' & HTBL & HBOX & HMROW & _).
  assert (M16 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16)
                  (lib.Lib.Mem.le4 (Z_to_bv 64 (4 * B.ACtlCutP.RLF.n_in (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)))))).
  { rewrite <- (B.Prog.Seg.RtmB.rb_row_ic (B.ACtlCut.c_in cx)).
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 _ _ 16 4 HMROW ltac:(rewrite Hmblen; lia)) as Hs.
    replace (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + Z.of_nat 16)
      with (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 16) in Hs by lia. exact Hs. }
  assert (M20 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 20)
                  (lib.Lib.Mem.le4 (Z_to_bv 64 (4 * B.ACtlCutP.RLF.n_out (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)))))).
  { rewrite <- (B.Prog.Seg.RtmB.rb_row_oc (B.ACtlCut.c_in cx)).
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 _ _ 20 4 HMROW ltac:(rewrite Hmblen; lia)) as Hs.
    replace (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + Z.of_nat 20)
      with (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) + 20) in Hs by lia. exact Hs. }
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  pose proof Hrt as (HAC & HSWc & HSWi & HRO).
  (* the spills the run reads *)
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 32 _ S32 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q32.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 24 _ S24 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q24.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 16 _ S16 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q16.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 120 _ S120 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q120.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 272 _ S272 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q272.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 96 _ Hsp96 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q96.
  (* the four frame-shadow cells at S(fr) + 320 *)
  pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 (B.AsanRT.shadow_addr fr) sh 320 4 Hsh ltac:(rewrite Hl392; lia))
    as Hj.
  replace (B.AsanRT.shadow_addr fr + Z.of_nat 320) with (B.AsanRT.shadow_addr fr + 320) in Hj by lia.
  assert (RWsh : lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (B.AsanRT.shadow_addr fr + 320)
                   [lib.Lib.Cells.CB 4 (firstn 4 (skipn 320 sh))]).
  { unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. split; [split|].
    + cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [|exact I].
      rewrite length_firstn, length_skipn, Hl392. reflexivity.
    + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hj.
    + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. unfold B.AsanRT.HIGHMEM_BEG in HSb.
      split; [lia|]. split; [lia|].
      intros i0 Hi0. destruct (proj2 (Pfrsh (B.AsanRT.shadow_addr fr + 320 + i0) ltac:(lia))) as (bb & Hbb).
      unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate. }
  (* declaration_of's shadow region (the row's two memcpy spans, image shadow; the 32-byte output, the frame's) at
     mem3, from ctl_rt_C's img_shadow and cut_shadow (F) conjuncts *)
  assert (HRR : B.ShadowRwOn.shadow_rw_on
                  (B.Prog.declaration_of_c.declaration_of_shadow_R (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx))
                     (B.ACtlCutP.decl_slot fr)) mem3).
  { intros a Hp Ha. destruct Hp as [Hp|[Hp|Hp]];
      unfold B.Prog.sh_word_on.sh_word_on, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in Hp.
    - apply HSWi; [|exact Ha]. exists ((a - Reusable.YG0f.SHADOW_OFF) * 8).
      unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hp. clear - Hp Hmr0 Hmr1. Z.div_mod_to_equations. lia.
    - apply HSWi; [|exact Ha]. exists ((a - Reusable.YG0f.SHADOW_OFF) * 8).
      unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hp. clear - Hp Hmr0 Hmr1. Z.div_mod_to_equations. lia.
    - apply HSWc; [|exact Ha]. left. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite EF, HFB6. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      unfold B.ACtlCutP.decl_slot, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hp. clear - Hp Hfr32. Z.div_mod_to_equations.
      lia. }
  (* ---- the run 0x819d0 -> declaration_of (R18F.r18_pre_F_on), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (R18F.r18_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (A := A) (D := B.ACtlCutP.decl_slot fr) (mr := B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx))
           (q := fr + 2528) (v1 := 4 * B.ACtlCutP.RLF.n_in (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)))
           (v2 := 4 * B.ACtlCutP.RLF.n_out (B.Prog.SlotModel.rt_pbs (B.ACtlCut.c_in cx)))
           (lo := B.ACtlCut.c_sp cx - 32768) (row := B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx))
           (junk := firstn 4 (skipn 320 sh)).
    all: try rewrite Es3; try rewrite Esp.
    - exact Hr9.
    - exact Hr26.
    - exact Ha0.
    - lia.
    - lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - lia.
    - unfold B.Contract.GT. lia.
    - exact Hmr8.
    - unfold B.Contract.GT. lia.
    - lia.
    - lia.
    - lia.
    - unfold B.Contract.GT, B.ACtlCutP.decl_slot. lia.
    - unfold B.ACtlCutP.decl_slot. lia.
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 8 Q32 (lib.Lib.Mem.length_le8 _)).
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 8 Q24 (lib.Lib.Mem.length_le8 _)).
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 8 Q16 (lib.Lib.Mem.length_le8 _)).
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 8 Q120 (lib.Lib.Mem.length_le8 _)).
    - exact Ksh16.
    - exact Ksh20.
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 4 Hu1 (lib.Lib.Mem.length_le4 _)).
    - replace (fr + 2528 + 4) with (fr + 2532) by lia.
      exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 4 Hu2 (lib.Lib.Mem.length_le4 _)).
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 4 M16 (lib.Lib.Mem.length_le4 _)).
    - exact (B.Prog.Seg.RHelp.rh_rdn mem3 _ _ 4 M20 (lib.Lib.Mem.length_le4 _)).
    - exact RWsh.
    - exact HRO.
    - (* what the call needs of the memory after the four shadow stores *)
      intros m1 MU1 WM1 B4.
      assert (HoW1 : forall x, (x < B.AsanRT.shadow_addr fr + 320 \/ B.AsanRT.shadow_addr fr + 324 <= x) ->
                       lib.Lib.Frame.outside [(B.AsanRT.shadow_addr fr + 320, B.AsanRT.shadow_addr fr + 324)] x)
        by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
      assert (Hshf : B.AsanRT.shadow_addr fr + 4096 < sp - 8192) by (apply Hsh_lo; lia).
      split.
      { apply (B.Prog.Seg.RHelp.rh_rdn m1 _ _ 8); [|apply lib.Lib.Mem.length_le8].
        apply (B.Prog.RcAsanFPLib.fl_bytes _ mem3 m1 _ _ Q272 MU1). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply HoW1. right. lia. }
      split.
      { apply (B.Prog.Seg.RHelp.rh_rdn m1 _ _ 8); [|apply lib.Lib.Mem.length_le8].
        apply (B.Prog.RcAsanFPLib.fl_bytes _ mem3 m1 _ _ Q96 MU1). rewrite lib.Lib.Mem.length_le8.
        intros x Hx. apply HoW1. right. lia. }
      split.
      { assert (STK3 : lib.Lib.Frame.stk B.Img0.rsegs mem3 (B.ACtlCut.c_sp cx - 32768) sp).
        { split; [lia|]. split; [lia|]. intros a Ha. destruct (Pstk a ltac:(lia)) as (bb & Hbb).
          unfold lib.Lib.Mem.wa, wview, lib.Lib.Mem.mrd. rewrite Hbb. split; [discriminate | exists bb; reflexivity]. }
        apply (w2b_stk_keep _ mem3 m1 _ _ STK3 MU1). intros x Hx. apply HoW1. right. lia. }
      split.
      { apply (B.Prog.RcAsanFPLib.fl_bytes _ mem3 m1 _ _ HMROW MU1). rewrite Hmblen.
        intros x Hx. apply HoW1. left. lia. }
      split.
      { destruct (B.Prog.Seg.RHelp.rh_bytes_of_present 32 m1 (B.ACtlCutP.decl_slot fr)
                    ltac:(unfold B.ACtlCutP.decl_slot; lia) ltac:(unfold B.ACtlCutP.decl_slot; lia))
          as (ob & Hob & Hobl).
        { intros k0 Hk0. destruct (Pfr (B.ACtlCutP.decl_slot fr + Z.of_nat k0) ltac:(unfold B.ACtlCutP.decl_slot; lia))
            as (bb & Hbb).
          exists bb. unfold lib.Lib.Mem.mrd. rewrite (MU1 _); [unfold lib.Lib.Mem.wa; rewrite Hbb; reflexivity|].
          unfold lib.Lib.Mem.wa. rewrite lib.Lib.MState.unsigned_lit by (unfold B.ACtlCutP.decl_slot; lia).
          apply HoW1. unfold B.ACtlCutP.decl_slot. destruct Hap as [Hap|Hap]; [right | left]; lia. }
        exists ob. rewrite <- Hobl. apply B.Prog.Seg.RHelp.rh_rwc_CB; [exact Hob|]. rewrite Hobl.
        split; [unfold B.ACtlCutP.decl_slot; lia|]. split; [unfold B.ACtlCutP.decl_slot; lia|].
        intros i0 Hi0. apply (WM1 _).
        destruct (Pfr (B.ACtlCutP.decl_slot fr + i0) ltac:(unfold B.ACtlCutP.decl_slot in *; lia)) as (bb & Hbb).
        unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate. }
      split.
      { apply (B.Prog.RcAsanFPLib.fl_asan_cells _ mem3 m1 HAC MU1). intros x Hx. apply HoW1. left.
        unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI in Hx. lia. }
      split.
      { assert (HAm3 : B.AsanRT.addressable mem3 (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)) 296).
        { pose proof (B.AsanRTFacts.addressable_sub mem3 B.ACtlCutP.SM.CAT _
                        (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) - B.ACtlCutP.SM.CAT) 296 HCA) as H.
          unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in H.
          replace (652832 + (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx) - 652832))
            with (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)) in H by lia.
          apply H; lia. }
        apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 _ _ _ HAm3 MU1).
        intros i0 Hi0. apply HoW1. left. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
        clear - Hi0 Hmr1 HfrGT. Z.div_mod_to_equations. lia. }
      apply (B.Prog.Seg.R18.r18_decl_addr m1 fr ltac:(clear - Hfr32; Z.div_mod_to_equations; lia) ltac:(lia)).
      + unfold B.AsanRT.APPMEM_END. lia.
      + intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
      + exact B4.
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia].
    - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia
        | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia |].
      intros a Ha. apply VCs. unfold B.AsanRT.ASAN_K in Ha. clear - Ha Hmr0 Hmr1. Z.div_mod_to_equations. lia.
    - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia
        | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia |].
      intros a Ha. apply VCs. unfold B.AsanRT.ASAN_K in Ha. clear - Ha Hmr0 Hmr1. Z.div_mod_to_equations. lia.
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vimg; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vimg; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vfr; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vfr; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.HIGHMEM_BEG in HSb; lia | unfold B.AsanRT.HIGHMEM_BEG in HSb; lia |].
      intros a Ha. exact (proj1 (Pfrsh a ltac:(lia))). }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & m1 & -> & P1 & P10 & P11 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 &
                  P24 & P25 & P26 & P27 & MU1 & WM1 & B4 & MI1 & HPR & HSRW) Hhid1 Hsbm1.
  rewrite Es3 in MU1, B4. rewrite Esp in HPR.
  destruct HPR as (R272 & R96 & STc & HROW1 & (ob & HOB) & HAC1 & HAmr1 & HAD1).
  set (W1 := [(B.AsanRT.shadow_addr fr + 320, B.AsanRT.shadow_addr fr + 324)]) in MU1.
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m1 MI1) as HMR1.
  assert (Ea0 : bv_unsigned (Sem.reg_get R1 10) = B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)).
  { assert (E : Sem.reg_get R1 10 = Z_to_bv 64 (B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx))) by exact P10.
    rewrite E. apply lib.Lib.MState.unsigned_lit. lia. }
  assert (Ea1 : bv_unsigned (Sem.reg_get R1 11) = B.ACtlCutP.decl_slot fr).
  { assert (E : Sem.reg_get R1 11 = Z_to_bv 64 (B.ACtlCutP.decl_slot fr)) by exact P11.
    rewrite E. apply lib.Lib.MState.unsigned_lit. unfold B.ACtlCutP.decl_slot. lia. }
  assert (Esp1 : bv_unsigned (Sem.reg_get R1 2) = sp).
  { assert (E : Sem.reg_get R1 2 = Z_to_bv 64 sp) by (transitivity (Sem.reg_get regs3 2); [exact P2 | exact Hr2]).
    rewrite E. apply lib.Lib.MState.unsigned_lit. lia. }
  (* ---- declaration_of on MemNorm's normalized memory (mem_inv), back by MemNormF.evtF_normalize_ro ---- *)
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of R1) R1 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv R1))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md1 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    apply B.MemNormF.evtF_normalize_ro; [exact MI1|].
    eapply B.Prog.declaration_of_F_closed.declaration_of_F_holds_closed_on with (lo := B.ACtlCut.c_sp cx - 32768)
      (row := B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) (ob := ob).
    all: try rewrite Ea0; try rewrite Ea1; try rewrite Esp1.
    - apply (w2b_stk_rel m1 _ _ _ HMR1 STc). intros a Ha. lia.
    - unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
    - exact Hmr8.
    - exact Hmblen.
    - exact (proj1 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 _ _ _ HMR1) HROW1).
    - apply (w2b_rwc_rel m1 _ _ _ HMR1 HOB). cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add].
      intros a Ha. unfold B.ACtlCutP.decl_slot in Ha. lia.
    - right. unfold B.ACtlCutP.decl_slot. lia.
    - left. unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
    - left. unfold B.Prog.declaration_of_c.DECLARATION_OF_K, B.ACtlCutP.decl_slot. lia.
    - exact (B.MemNorm.mem_inv_normalize _ m1).
    - exact (w2b_cells_rel m1 _ HMR1 HAC1).
    - exact (B.ShadowRwOnT.shadow_rw_on_normalize _ m1 MI1 (HSRW _ HRR)).
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - exact (w2b_addr_rel m1 _ _ _ HMR1 HAmr1).
    - exact (w2b_addr_rel m1 _ _ _ HMR1 HAD1).
    - unfold B.AsanRT.app_mem, B.ACtlCutP.decl_slot, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG,
        B.AsanRT.APPMEM_END. lia.
    - right. unfold B.AsanRT.RT_HI, B.ACtlCutP.decl_slot. lia.
    - exact (B.ProgBridge.rng_bytes_RNG_W _).
    - exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W3)).
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.Prog.declaration_of_c.DECLARATION_OF_K; lia | unfold B.Prog.declaration_of_c.DECLARATION_OF_K; lia |].
      intros a Ha. apply Vstk. unfold B.Prog.declaration_of_c.DECLARATION_OF_K in Ha. lia.
    - unfold B.Prog.rng_asan.sh_word_rng. right. apply B.ProgBridge.rng_of_visible.
      destruct (WIN_SH_VIS LAWS ly3 S3 W3 mem3 md3 (sp - B.Prog.declaration_of_c.DECLARATION_OF_K)
                  B.Prog.declaration_of_c.DECLARATION_OF_K HAR) as [E0|HV].
      + unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
      + unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
      + unfold B.Prog.declaration_of_c.DECLARATION_OF_K. lia.
      + unfold B.Prog.declaration_of_c.DECLARATION_OF_K in E0. lia.
      + exact HV.
    - exact (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.rt_vis_W W3)).
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vimg; lia].
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia
        | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia |].
      intros a Ha. apply VCs. unfold B.AsanRT.ASAN_K in Ha. clear - Ha Hmr0 Hmr1. Z.div_mod_to_equations. lia.
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.ACtlCutP.decl_slot; lia | unfold B.ACtlCutP.decl_slot; lia |].
      intros a Ha. apply Vfr. unfold B.ACtlCutP.decl_slot in Ha. lia.
    - apply B.ProgBridge.rng_of_visible, w2b_rv;
        [unfold B.AsanRT.ASAN_K, B.ACtlCutP.decl_slot; clear - Hfr4k; Z.div_mod_to_equations; lia
        | unfold B.AsanRT.ASAN_K, B.ACtlCutP.decl_slot; clear - Hfrce Hceil Hfr4k; Z.div_mod_to_equations; lia |].
      intros a Ha.
      assert (Ha' : B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512).
      { unfold B.AsanRT.ASAN_K, B.ACtlCutP.decl_slot in Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
        clear - Ha Hfr32. Z.div_mod_to_equations. lia. }
      exact (proj1 (Pfrsh a Ha')). }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms2 md2 (s0 & HQ & Hrel & Hros) Hhid2 Hsbm2.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'0 & -> &
                  MU2 & WM2 & _ & _ & RW2 & _ & _ & _).
  rewrite Esp1, Ea1 in MU2. rewrite Ea1 in RW2.
  rewrite (B.Prog.Seg.RtmB.rb_rtm_declok (B.ACtlCut.c_in cx)) in RW2. cbv iota in RW2.
  destruct ms2 as [r2 f2 pc2 sv2 rv2 fc2 mem2 rom2].
  destruct Hrel as (Er & Ef & Epc & Esv & Erv & Efc & Erom & HMR2).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem lib.Lib.MState.MS]
    in Er, Ef, Epc, Esv, Erv, Efc, Erom, HMR2, Hros, Hhid2.
  subst r2 f2 pc2 sv2 rv2 fc2 rom2.
  rewrite (B.Prog.Seg.RtmB.rb_rtm_declok (B.ACtlCut.c_in cx)). cbv iota.
  assert (ER1 : Sem.reg_get R1 1 = Z_to_bv 64 0x81a50) by exact P1.
  rewrite ER1, (lib.Lib.MState.ret_pc_even 0x81a50) by first [lia | reflexivity].
  apply w2b_of_MS.
  set (W2 := [(sp - B.Prog.declaration_of_c.DECLARATION_OF_K, sp);
              (B.ACtlCutP.decl_slot fr, B.ACtlCutP.decl_slot fr + 32)]) in MU2.
  pose proof (B.MemNorm.munch_rel B.Img0.rsegs W2 m1 _ mem2 m'0 HMR1 HMR2 Hros MU2) as MU12.
  pose proof (w2b_wmono_rel m1 _ mem2 m'0 HMR1 HMR2 Hros WM2) as WM12.
  (* what lies outside the two write sets *)
  assert (HoW1 : forall x, (x < B.AsanRT.shadow_addr fr + 320 \/ B.AsanRT.shadow_addr fr + 324 <= x) ->
                   lib.Lib.Frame.outside W1 x)
    by (intros x Hx; unfold W1; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HoW2 : forall x, (x < sp - 2256 \/ sp <= x) ->
                   (x < B.ACtlCutP.decl_slot fr \/ B.ACtlCutP.decl_slot fr + 32 <= x) ->
                   lib.Lib.Frame.outside W2 x).
  { intros x H1 H2. unfold W2, B.Prog.declaration_of_c.DECLARATION_OF_K. cbn [lib.Lib.Frame.outside].
    split; [lia | split; [lia | exact I]]. }
  assert (KB : forall a bs,
            (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
  { intros a bs HX Hb.
    apply (B.Prog.RcAsanFPLib.fl_bytes W2 m1 mem2 a bs); [|exact MU12|intros x Hx; exact (proj2 (HX x Hx))].
    apply (B.Prog.RcAsanFPLib.fl_bytes W1 mem3 m1 a bs Hb MU1). intros x Hx. exact (proj1 (HX x Hx)). }
  assert (OStk : forall x, A <= x -> lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x).
  { intros x Hx. split; [apply HoW1; right; lia | apply HoW2; right; unfold B.ACtlCutP.decl_slot; lia]. }
  assert (OImg : forall x, 0 <= x < 0x5fe000 -> lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x).
  { intros x Hx. split; [apply HoW1; left | apply HoW2; [left | left]]; unfold B.ACtlCutP.decl_slot in *; lia. }
  assert (OFrm : forall x, fr <= x < fr + 4096 -> (x < B.ACtlCutP.decl_slot fr \/ B.ACtlCutP.decl_slot fr + 32 <= x) ->
                   lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x).
  { intros x Hx Hd. split; [apply HoW1 | apply HoW2; [left | exact Hd]];
      [destruct Hap as [Hap|Hap]; [right | left]; lia | lia]. }
  assert (OSh : forall x, B.AsanRT.in_shadow x ->
                  (x < B.AsanRT.shadow_addr fr + 320 \/ B.AsanRT.shadow_addr fr + 324 <= x) ->
                  lib.Lib.Frame.outside W1 x /\ lib.Lib.Frame.outside W2 x).
  { intros x Hx Hd. split; [apply HoW1; exact Hd|].
    unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hx.
    apply HoW2; [left | ]; unfold B.ACtlCutP.decl_slot; destruct Happ' as [Hl|Hh];
      unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in *; lia. }
  assert (KA : forall p n, 0 <= n ->
            (forall i, 0 <= i < n -> B.AsanRT.in_shadow (B.AsanRT.shadow_addr (p + i)) /\
               (B.AsanRT.shadow_addr (p + i) < B.AsanRT.shadow_addr fr + 320 \/
                B.AsanRT.shadow_addr fr + 324 <= B.AsanRT.shadow_addr (p + i))) ->
            B.AsanRT.addressable mem3 p n -> B.AsanRT.addressable mem2 p n).
  { intros p n Hn0 HX Ha.
    apply (B.Prog.Seg.RHelp.rh_addr_keep_rng m1 mem2 W2 p n); [|exact MU12|].
    - apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 W1 p n Ha MU1). intros i Hi.
      destruct (HX i Hi) as (_ & Hd). exact (HoW1 _ Hd).
    - intros i Hi. destruct (HX i Hi) as (Hs & Hd). exact (proj2 (OSh _ Hs Hd)). }
  (* the journal across both runs *)
  assert (HJ2 : AJ cx (own6 cx) ly3 S3 W3 mem2 md2 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem2) (mdc' := md2)
      (Wr := fun a => (B.AsanRT.shadow_addr fr + 320 <= a < B.AsanRT.shadow_addr fr + 324) \/
                      (sp - 2256 <= a < sp) \/
                      (B.ACtlCutP.decl_slot fr <= a < B.ACtlCutP.decl_slot fr + 32)); [exact HJ | | | | | ].
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU12 x), (MU1 x); [reflexivity | |].
      + apply HoW1. lia.
      + apply HoW2; lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Ex; [exact Hx|].
      assert (Hw0 : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity]. }
      pose proof (bv_unsigned_in_range 64 x) as Hx64. change (bv_modulus 64) with (2 ^ 64) in Hx64.
      destruct (Z_le_dec 0x10000 (bv_unsigned x)) as [Hl|Hl];
        [destruct (Z_lt_dec (bv_unsigned x) 0x5fe000) as [Hh|Hh]|].
      + rewrite (MU12 x), (MU1 x);
          [exact Hx | apply (proj1 (OImg (bv_unsigned x) ltac:(lia))) | apply (proj2 (OImg (bv_unsigned x) ltac:(lia)))].
      + assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; lia).
        pose proof (WM12 x (WM1 x Hw0)) as Hw. unfold wview in Hw.
        rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
        destruct (mem2 x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
      + assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; lia).
        pose proof (WM12 x (WM1 x Hw0)) as Hw. unfold wview in Hw.
        rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
        destruct (mem2 x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
    - intros x Hx. pose proof (Hhid1 x Hx) as E1. pose proof (Hhid2 x Hx) as E2'.
      cbn [ms_mem lib.Lib.MState.MS] in E1, E2'. rewrite E2'. exact E1.
    - exact (Reusable.YK04.same_but_materialized_trans _ _ _ Hsbm1 Hsbm2).
    - intros a [Ha|[Ha|Ha]].
      + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [cbn; left; reflexivity|].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
      + right; right; right. exists 6, (B.ACtlCut.c_fpos cx). split; [cbn; left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6. unfold B.ACtlCutP.decl_slot in Ha. lia. }
  pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 mem2 md2 k HB HJ2) as Hrt2.
  pose proof Hrt2 as (_ & _ & _ & HRO2).
  (* ---- the successor cut C_B81a50_at at turn 0 ---- *)
  refine (HY cx [Z.of_nat 0] fr k ly3 S3 W3 _ mem2 md2 HB HJ2 Hfrs Hfa _ _ Hrt2).
  - cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B81a50_at]. unfold B.ACtlCutP.ixn. cbn [nth]. lia.
  - unfold B.ACtlCutP.C_B81a50_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
    cbv zeta. change (B.ACtlCutP.ixn 0 [Z.of_nat 0]) with 0%nat.
    match goal with |- context [B.ACtlCutP.FRAC B cx fr fr ?R _] => set (R2 := R) end.
    assert (G2 : lib.Reusable.YK11.getr R2 2 = lib.Reusable.YK11.getr regs3 2) by exact P2.
    assert (G3 : lib.Reusable.YK11.getr R2 3 = lib.Reusable.YK11.getr regs3 3) by exact P3.
    assert (G4 : lib.Reusable.YK11.getr R2 4 = lib.Reusable.YK11.getr regs3 4) by exact P4.
    assert (G8 : lib.Reusable.YK11.getr R2 8 = lib.Reusable.YK11.getr regs3 8) by exact P8.
    assert (G9 : lib.Reusable.YK11.getr R2 9 = lib.Reusable.YK11.getr regs3 9) by exact P9.
    assert (G18 : lib.Reusable.YK11.getr R2 18 = lib.Reusable.YK11.getr regs3 18) by exact P18.
    assert (G19 : lib.Reusable.YK11.getr R2 19 = lib.Reusable.YK11.getr regs3 19) by exact P19.
    assert (G20 : lib.Reusable.YK11.getr R2 20 = lib.Reusable.YK11.getr regs3 20) by exact P20.
    assert (G21 : lib.Reusable.YK11.getr R2 21 = lib.Reusable.YK11.getr regs3 21) by exact P21.
    assert (G22 : lib.Reusable.YK11.getr R2 22 = lib.Reusable.YK11.getr regs3 22) by exact P22.
    assert (G23 : lib.Reusable.YK11.getr R2 23 = lib.Reusable.YK11.getr regs3 23) by exact P23.
    assert (G25 : lib.Reusable.YK11.getr R2 25 = lib.Reusable.YK11.getr regs3 25) by exact P25.
    assert (G26 : lib.Reusable.YK11.getr R2 26 = lib.Reusable.YK11.getr regs3 26) by exact P26.
    assert (G27 : lib.Reusable.YK11.getr R2 27 = lib.Reusable.YK11.getr regs3 27) by exact P27.
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 ->
              B.ACtlCutP.spill regs3 mem3 off v -> B.ACtlCutP.spill R2 mem2 off v).
    { intros off v Ho0 Ho1 Hs.
      pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1) as Hq.
      exists A. split; [unfold B.ACtlCut.rgv in *; rewrite G9; exact Hr9|].
      unfold B.ACtlCutP.q64 in *. apply KB; [|exact Hq]. rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply OStk. lia. }
    exists phi, 1.
    split; [exact Hperm|].
    split.
    { assert (HF1 : B.ACtlCutP.FRAC B cx fr fr regs3 m1).
      { apply (w2b_FRAC_keep_sh cx fr regs3 regs3 mem3 m1 W1 HFRAC MU1); try reflexivity.
        - intros A' x HA' HA'r Hx. apply HoW1. right.
          pose proof (w2b_rg9_ge regs3 A A' Hr9 HA' ltac:(lia) ltac:(lia)) as EA.
          pose proof (Hsh_lo fr ltac:(lia)). lia.
        - intros x Hx. apply HoW1. destruct Hap as [Hap|Hap]; [right | left]; lia.
        - intros x Hx. destruct (B.Prog.Seg.RHelp.rh_out_dec W1 x) as [Ho|Ho]; [left; exact Ho | right].
          assert (Hin : B.AsanRT.shadow_addr fr + 320 <= x < B.AsanRT.shadow_addr fr + 324).
          { destruct (Z_lt_dec x (B.AsanRT.shadow_addr fr + 320)); [exfalso; apply Ho, HoW1; lia|].
            destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 324) x); [exfalso; apply Ho, HoW1; lia|]. lia. }
          destruct B4 as (_ & _ & HB4).
          pose proof (HB4 (Z.to_nat (x - (B.AsanRT.shadow_addr fr + 320))) ltac:(cbn [length]; lia)) as Hb4.
          replace (B.AsanRT.shadow_addr fr + 320 + Z.of_nat (Z.to_nat (x - (B.AsanRT.shadow_addr fr + 320))))
            with x in Hb4 by lia.
          destruct (nth_error _ _) as [b4|] eqn:E4 in Hb4;
            [exists b4; exact Hb4 | apply nth_error_None in E4; cbn [length] in E4; lia].
        - intros x Hx. apply HoW1. right. pose proof (Hsh_lo fr ltac:(lia)). lia.
        - intros x Hx. apply HoW1. destruct Hap as [Hap|Hap]; [right | left]; lia. }
      apply (w2b_FRAC_keep cx fr regs3 R2 m1 mem2 W2 HF1 MU12 G2 G3 G4 G8 G9 G19 G26).
      - intros A' x HA' HA'r Hx.
        pose proof (w2b_rg9_ge regs3 A A' Hr9 HA' ltac:(lia) ltac:(lia)) as EA.
        apply HoW2; right; unfold B.ACtlCutP.decl_slot; lia.
      - intros x Hx. apply HoW2; [left | left]; unfold B.ACtlCutP.decl_slot; lia.
      - intros x Hx. apply HoW2.
        + left. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. clear - Hx Hfrce Hceil Hstk Hspb.
          Z.div_mod_to_equations. lia.
        + unfold B.ACtlCutP.decl_slot. destruct Hap as [Hap|Hap]; [left | right]; lia.
      - intros x Hx. apply HoW2; [right | right]; unfold B.ACtlCutP.decl_slot; lia.
      - intros x Hx. apply HoW2; [left | right]; unfold B.ACtlCutP.decl_slot; lia. }
    split; [exact Hn|].
    split.
    { split.
      - assert (HRB1 : B.ACtlCutP.RB cx fr 0 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 0)
                         (B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) 0) regs3 m1).
        { apply (w2b_RB_keep cx fr 0 _ _ regs3 regs3 mem3 m1 W1 HRB0 MU1
                   (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 0)
                   (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) 0 ltac:(lia)) eq_refl eq_refl eq_refl);
            intros x Hx; apply HoW1; destruct Hap as [Hap|Hap]; [right | left | right | left | right | left]; lia. }
        apply (w2b_RB_keep cx fr 0 _ _ regs3 R2 m1 mem2 W2 HRB1 MU12
                 (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 0)
                 (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) 0 ltac:(lia)) G22 G23 G25);
          intros x Hx; apply HoW2; unfold B.ACtlCutP.decl_slot; lia.
      - split; [exact Hnz|].
        split; [unfold B.ACtlCut.rgv in *; rewrite G20; exact H20|].
        apply KB; [|exact HF]. intros x Hx. change (Z.of_nat 0) with 0 in Hx. rewrite HLF in Hx.
        split; [apply HoW1 | apply HoW2; [left | ]]; unfold B.ACtlCutP.decl_slot.
        + unfold B.AsanRT.HIGHMEM_BEG in HSb. destruct Hphiapp as (_ & [Hl|Hh]); [left | right]; lia.
        + lia.
        + destruct Hsep as [Hs|Hs]; [left | right]; lia. }
    split; [unfold B.ACtlCut.rgv; reflexivity|].
    split; [lia|].
    split; [unfold B.ACtlCut.rgv in *; rewrite G18; exact H18|].
    split; [apply KS; [lia | lia | exact Hsp96]|].
    split.
    { destruct RW2 as ((_ & HRWb) & _).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HRWb. rewrite app_nil_r in HRWb.
      exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs mem2 m'0 _ _ HMR2) HRWb). }
    split.
    { apply (w2b_RBE_transfer cx fr regs3 R2 mem3 mem2 HRBE KS).
      - intros p n Hpn Ha.
        assert (Hb : fr <= p /\ 0 <= n /\ p + n <= fr + 4096 /\
                     (p + n <= fr + 2560 \/ fr + 2592 <= p))
          by (destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; lia).
        apply KA; [lia | | exact Ha]. intros i Hi. split.
        + unfold B.AsanRT.in_shadow, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.LOWMEM_END,
            B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG.
          destruct Happ' as [Hl|Hh]; unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in *;
            [left; clear - Hi Hb Hl Hfr32 HfrGT; Z.div_mod_to_equations; lia
            | right; clear - Hi Hb Hh Hfr32 HfrGT; Z.div_mod_to_equations; lia].
        + unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hi Hb Hfr32. Z.div_mod_to_equations. lia.
      - intros a bs Hr Hb. apply KB; [|exact Hb]. intros x Hx. apply OImg.
        assert (HBA : B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
          by (apply Z.leb_le; vm_compute; reflexivity).
        pose proof Hb as (Hb0 & _).
        unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hr. lia.
      - intros a bs Hr Hb. exact (w2b_ro_bytes mem3 mem2 a bs HRO HRO2 Hr Hb).
      - intros Hh Hr. exact (ctl_names_addressable ly3 S3 W3 mem2 md2 (B.ACtlCut.c_in cx) (proj1 HJ2) Hh Hr). }
    split; [unfold B.ACtlCut.rgv in *; rewrite G21; exact H21|].
    split; [reflexivity|].
    split.
    { split; [exact Hphinz|]. apply KA; [lia | | exact HAphi0]. intros i Hi. rewrite Hasz in Hi. split.
      + unfold B.AsanRT.in_shadow, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG.
        clear - Hi Hphiapp Hphi4k Hceil. Z.div_mod_to_equations. lia.
      + unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hi Hsep Hfr32. Z.div_mod_to_equations. lia. }
    split; [lia|].
    split; [exact (B.Prog.Seg.RtmB.rb_decl_len (B.ACtlCut.c_in cx))|].
    split.
    { apply (B.Prog.Seg.RHelp.rh_addr_keep_rng m1 mem2 W2 _ _ HAD1 MU12). intros i Hi.
      apply HoW2; [left | ]; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.decl_slot.
      + pose proof (Hsh_lo (B.ACtlCutP.decl_slot fr + i) ltac:(unfold B.ACtlCutP.decl_slot; lia)) as Hs.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.decl_slot in Hs. lia.
      + destruct Hap as [Hap|Hap]; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hap; clear - Hi Hap Hfr32;
          Z.div_mod_to_equations; lia. }
    unfold B.ACtlCut.rgv in *. rewrite G27. exact H27.
Qed.

(* B81a50_at b (Inv_B81a50_at SIv:1941) -> B81a68_at b.  S_R19 (Slot.v:97; seg_R19 R19.v:257), b = 0.
   The guard 0x81a50 `bnez a0` (abort jump 0x81a54) is refuted by the body's rgv 10 vd, vd <> 0.  R19F.r19_pre_F
   (R19F.v:39; 0x81a50 -> the bcmp trampoline, ra = 0x81a68; sources R19.v:157 (ro_agree form) / :93 (mem_inv
   form): s1 = A, s2 = phi + 18 (rgv 18), a0 = vd, bytes_at (A + 96) (le8 D) with D = decl_slot fr (spill 96), the
   32 block bytes at phi + 18 and the 32 decl bytes at D), then the bcmp trampoline's contract H_bcmp (journal form aj_bcmp_at,
   YCbq.v:2062: x = phi + 18, y = D, n = 32; src_ok / addressable / shadow hull of both (HB, addressable (decl_slot
   fr) 32, V3 / V4 / V5), both apart from the 2 * ESTACK window (T7), gp / tp (FRAC), ret_ok 0x81a68) -> 0x81a68 =
   the successor cut; the result v = memcmp_model ls rs 32 (R19.v:101 / :165).  Post -> C_B81a68_at body: a0v regs 0 needs
   v = 0, i.e. the block's 32 bytes equal the declaration (SlotModel / RcDecl: rt_g's row block at turn 0 is the
   declaration of rt_mb; seg_R19's model lemma -- the abort jump 0x81a6c after `beqz a0` belongs to S_R20 and is
   refuted by the same a0 = 0); journal unchanged (k).  The raw cut facts after the call come from ctl_post_bcmp
   (H_bcmp's post keeps the view outside [sp - 2 ESTACK, sp), which is below every cut fact).
   No UBSan trap. *)
Lemma seg_R19 : forall POST (b : nat), CFb POST C81a68 b -> CFb POST C81a50 b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B81a50_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & vd & Hperm & HFRAC & Hn & HRFb & H10 & Hvd & H18 & Hsp96 & HDB & HRBE & H21 & Hb0 &
                     HHB & Hvdb & HLD & HAD & H27).
  subst b.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (Hsp0m & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  pose proof HB as ((Hafn & _) & _). pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  assert (Hspb : B.ACtlCut.c_sp cx - 4096 < sp /\ sp + 448 <= B.ACtlCut.c_sp cx /\ sp <= A /\
                 A + 448 <= B.ACtlCut.c_sp cx) by lia.
  assert (Hstk : lib.Reusable.YM05.alloc_ceiling + 32768 <= B.ACtlCut.c_sp cx) by lia.
  assert (Hsh_lo : forall a, 0 <= a < 2 ^ 47 -> B.AsanRT.shadow_addr a + 4096 < sp - 8192).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Ha Hceil Hstk Hspb.
    Z.div_mod_to_equations. lia. }
  (* ---- the frame, its shadow, the turn block ---- *)
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Pfrsh : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists bb, mem3 (Z_to_bv 64 a) = Some bb).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
    pose proof (proj1 (Hfrsh (a - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
    replace (2147450880 + fr / 8 + (a - (2147450880 + fr / 8))) with a in Hp by lia. exact Hp. }
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfrb a Ha)))).
  assert (Vstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hwin a Ha))).
  assert (Hinb : In (phi, rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR Hinb)
    as (_ & Hphi4k & Hphice & _ & Hphipres & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0) HAR Hinb) as (_ & Hphish).
  pose proof HRFb as (HRB0 & Hnz & H20 & HF).
  destruct (B.Prog.Seg.RtmB.rb_rtn (B.ACtlCut.c_in cx) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) (Z.of_nat 0)) with (rnb cx 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  assert (Hreq : Reusable.YG00.req_size (rnb cx 0) = rnb cx 0).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
  rewrite Hreq in Hphice, Hphipres, Hphish.
  pose proof Hphish as Hphish'.
  unfold Reusable.YG0d.shadow_hull_vis, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hphish'.
  assert (Vphi : forall a, phi <= a < phi + rnb cx 0 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hphipres a Ha)))).
  destruct HHB as (Hphinz & HAphi0).
  assert (Hasz : B.ACtlK.a_size (rnb cx 0) = rnb cx 0) by (unfold B.ACtlK.a_size; lia).
  assert (Vsh : forall i, 0 <= i < rnb cx 0 ->
                  Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) = false).
  { intros i Hi. apply (w2b_vis_aview W3 mem3). apply Hphish'.
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    apply (w2b_hull 2147450880 phi (rnb cx 0) (phi + i) (phi + i)); lia. }
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  pose proof Hrt as (HAC & HSWc & HSWi & HRO).
  (* the block's 32 bytes at phi + 18 are the declaration of the catalogue row (RtmB.rb_X0_F) *)
  assert (HLS : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 18)
                  (B.ACtlCutP.RDC.decl (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)))).
  { rewrite <- (B.Prog.Seg.RtmB.rb_X0_F (B.ACtlCut.c_in cx)).
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 phi (B.Prog.SlotModel.rt_F (B.ACtlCut.c_in cx) 0) 18 32 HF
                  ltac:(rewrite HLF; lia)) as Hs.
    replace (phi + Z.of_nat 18) with (phi + 18) in Hs by lia. exact Hs. }
  assert (HDB' : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (B.ACtlCutP.decl_slot fr)
                   (B.ACtlCutP.RDC.decl (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)))) by exact HDB.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A 96 _ Hsp96 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Q96.
  (* ---- the run 0x81a50 -> the bcmp trampoline (R19F.r19_pre_F), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (R19F.r19_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (A := A) (phi := phi) (D := B.ACtlCutP.decl_slot fr) (vd := vd).
    - exact Hr9.
    - exact H18.
    - exact H10.
    - exact Hvd.
    - exact Hvdb.
    - lia.
    - lia.
    - unfold B.ACtlCutP.decl_slot; lia.
    - unfold B.ACtlCutP.decl_slot; lia.
    - exact Q96.
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia]. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & -> & P1 & P10 & P11 & P12 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 &
                  P24 & P25 & P26 & P27) Hhid1 Hsbm1.
  apply w2b_of_MS.
  assert (G2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by exact P2.
  assert (G3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by exact P3.
  assert (G4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by exact P4.
  assert (G8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by exact P8.
  assert (G9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by exact P9.
  assert (G19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by exact P19.
  assert (G20 : lib.Reusable.YK11.getr R1 20 = lib.Reusable.YK11.getr regs3 20) by exact P20.
  assert (G21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by exact P21.
  assert (G22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by exact P22.
  assert (G23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by exact P23.
  assert (G25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by exact P25.
  assert (G26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by exact P26.
  assert (G27 : lib.Reusable.YK11.getr R1 27 = lib.Reusable.YK11.getr regs3 27) by exact P27.
  assert (Esp1 : Reusable.YG0d.spZ R1 = sp) by (unfold Reusable.YG0d.spZ in *; rewrite G2; exact Hspz).
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem3 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem3) (mdc' := md1)
      (Wr := fun _ => False); [exact HJ | | | | | ].
    - intros x _. reflexivity.
    - intros x Hx. exact Hx.
    - intros x _. reflexivity.
    - exact Hsbm1.
    - intros a []. }
  (* ---- the bcmp trampoline (H_bcmp through YCbq.aj_bcmp_at), x = phi + 18, y = decl_slot fr, n = 32 ---- *)
  pose proof H_bcmp as HBC. rewrite B_bcmp_tramp_at in HBC.
  eapply Reusable.YA0n.SRr_bind.
  { apply (Reusable.YCbq.aj_bcmp_at segs B LAWS w2b_segs_low _ HBC W3 R1 mem3 Reusable.YCfn.LLVMF_STK
             (B.ACtlCut.c_sp cx) FP (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx)
             (B.ACtlCut.c_md cx) (own6 cx) ly3 S3 md1 k (phi + 18) (B.ACtlCutP.decl_slot fr) 32
             (sp - B.ACtlCut.c_sp cx) (Z_to_bv 64 0x81a68) HJ1).
    - exact P10.
    - exact P11.
    - exact P12.
    - lia.
    - lia.
    - lia.
    - unfold B.ACtlCutP.decl_slot; lia.
    - unfold B.ACtlCutP.decl_slot; lia.
    - rewrite Esp1; lia.
    - clear - Hsp16 Hsp0m. Z.div_mod_to_equations. lia.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK; lia.
    - rewrite G3, Hr3. exact Hgp0.
    - rewrite G4. exact Hr4.
    - exact P1.
    - apply lib.Reusable.YK0s.ret_ok_even. rewrite lib.Lib.MState.unsigned_lit by lia. reflexivity.
    - intros a Ha. split; [apply w2b_aview_some; exact (proj1 (Hphipres a ltac:(lia)))|].
      rewrite Esp1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold B.ACtlCutP.decl_slot in Ha. split; [apply w2b_aview_some; exact (proj1 (Hfrb a ltac:(lia)))|].
      rewrite Esp1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK, B.ACtlCutP.decl_slot in *. lia.
    - apply (Reusable.YCbq.amem_range_of_block _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0));
        [exact HAR | exact Hinb | lia | rewrite Hreq; lia].
    - apply Reusable.YCbq.amem_range_high; unfold B.ACtlCutP.decl_slot; lia.
    - apply (Reusable.YCbq.range_addressable_of_block _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0));
        [exact HAR | exact Hinb | lia | rewrite Hreq; lia].
    - intros _. apply (Reusable.YCbq.shadow_hull_vis_of_block _ _ LAWS ly3 S3 W3 mem3 md3 phi (rnb cx 0));
        [exact HAR | exact Hinb | lia | rewrite Hreq; lia | lia].
    - apply (w2b_ra_of_addr _ mem3 _ 32 HAD). intros i Hi.
      assert (Hs : B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr (B.ACtlCutP.decl_slot fr + i) <
                   B.AsanRT.shadow_addr fr + 512).
      { unfold B.ACtlCutP.decl_slot, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hi Hfr32.
        Z.div_mod_to_equations. lia. }
      exact (proj1 (Pfrsh _ Hs)).
    - intros _. unfold Reusable.YG0d.shadow_hull_vis. intros s Hs. apply w2b_aview_some.
      assert (Hs' : B.AsanRT.shadow_addr fr <= s < B.AsanRT.shadow_addr fr + 512).
      { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.ACtlCutP.decl_slot in Hs.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hs Hfr32. Z.div_mod_to_equations. lia. }
      exact (Pfrsh s Hs'). }
  cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
  (* ---- the successor cut C_B81a68_at at turn 0 ---- *)
  assert (G : forall r : Z, Reusable.YG0d.acallee_saved r ->
            lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr R1 (Z_to_bv 5 r)) by exact HP.
  assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- G2; apply (G 2); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- G3; apply (G 3); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- G4; apply (G 4); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by (rewrite <- G8; apply (G 8); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite <- G9; apply (G 9); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by (rewrite <- G19; apply (G 19); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F20 : lib.Reusable.YK11.getr regs2 20 = lib.Reusable.YK11.getr regs3 20)
    by (rewrite <- G20; apply (G 20); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F21 : lib.Reusable.YK11.getr regs2 21 = lib.Reusable.YK11.getr regs3 21)
    by (rewrite <- G21; apply (G 21); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by (rewrite <- G22; apply (G 22); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs3 23)
    by (rewrite <- G23; apply (G 23); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by (rewrite <- G25; apply (G 25); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by (rewrite <- G26; apply (G 26); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F27 : lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs3 27)
    by (rewrite <- G27; apply (G 27); unfold Reusable.YG0d.acallee_saved; lia).
  (* the trampoline's post at visible addresses (ctl_post_bcmp) *)
  destruct (ctl_post_bcmp W3 mem3 mem2 sp) as (MV & _).
  { split; [|exact Hpres2]. intros a Ha Ho. apply Hfr; [exact Ha|]. cbn [lib.Lib.Frame.outside] in Ho. lia. }
  assert (HoW : forall x, (x < sp - 8192 \/ sp <= x) ->
                  lib.Lib.Frame.outside [(sp - 2 * Reusable.YG0d.ESTACK, sp)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; unfold Reusable.YG0d.ESTACK; split; [lia | exact I]).
  assert (KB2 : forall a bs,
            (forall x, a <= x < a + Z.of_nat (length bs) ->
               Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ (x < sp - 8192 \/ sp <= x)) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
  { intros a bs HX Hb. apply (w2b_bytes_mv _ _ mem3 mem2 a bs MV); [|exact Hb].
    intros x Hx. destruct (HX x Hx) as (Hv' & Ho). split; [exact Hv' | exact (HoW x Ho)]. }
  pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 mem2 md2 k HB HJ2) as Hrt2.
  pose proof Hrt2 as (_ & _ & _ & HRO2).
  assert (HRB2 : B.ACtlCutP.RB cx fr 0 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 0)
                   (B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) 0) regs2 mem2).
  { apply (w2b_RB_transfer cx fr 0 _ _ regs3 regs2 mem3 mem2 HRB0
             (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 0)
             (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) 0 ltac:(lia)) F22 F23 F25).
    intros a bs Ha0 Ha1 Hb. apply KB2; [|exact Hb]. intros x Hx. split; [apply Vfr; lia | left; lia]. }
  pose proof HRB2 as (Hb6' & HCUR2 & HOUR2 & H22' & _ & _).
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81a68 regs2 mem2 md2) (POST cx)).
  refine (HY cx [Z.of_nat 0] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfrs Hfa _ _ Hrt2).
  - cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B81a68_at]. unfold B.ACtlCutP.ixn. cbn [nth]. lia.
  - unfold B.ACtlCutP.C_B81a68_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
    cbv zeta. change (B.ACtlCutP.ixn 0 [Z.of_nat 0]) with 0%nat.
    exists phi.
    split; [exact Hperm|].
    split.
    { apply (w2b_FRAC_transfer cx fr regs3 regs2 mem3 mem2 HFRAC F2 F3 F4 F8 F9 F19 F26).
      intros a bs HR Hb. apply KB2; [|exact Hb]. intros x Hx.
      destruct (HR x Hx) as [(A' & HA' & HA'r & HA'c & Hx')|[Hx'|[Hx'|Hx']]].
      - assert (EA : A' = A) by (apply (w2b_rg9_eq regs3 A A' Hr9 HA'); lia). subst A'.
        split; [apply Vstk; lia | right; lia].
      - split; [apply Vfr; exact Hx' | left; lia].
      - split; [exact (proj1 (Pfrsh x ltac:(lia)))|]. left.
        pose proof (Hsh_lo fr ltac:(lia)). lia.
      - split; [apply Vstk; lia | right; lia]. }
    split; [exact Hn|].
    split; [exact Hb6'|].
    split.
    { split; [exact Hphinz|]. apply (w2b_addr_mv _ _ mem3 mem2 phi _ MV); [|exact HAphi0].
      intros i Hi. rewrite Hasz in Hi. split; [apply Vsh; lia|]. apply HoW. left.
      pose proof (Hsh_lo (phi + i) ltac:(lia)). lia. }
    split; [exact H22'|].
    split; [exact HOUR2|].
    split; [exact HCUR2|].
    split.
    { apply (w2b_RBE_transfer cx fr regs3 regs2 mem3 mem2 HRBE).
      - intros off v0 Ho0 Ho1 Hs.
        pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A off v0 Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1) as Hq.
        exists A. split; [unfold B.ACtlCut.rgv in *; rewrite F9; exact Hr9|].
        unfold B.ACtlCutP.q64 in *. apply KB2; [|exact Hq]. rewrite lib.Lib.Mem.length_le8.
        intros x Hx. split; [apply Vstk; lia | right; lia].
      - intros p n Hpn Ha. apply (w2b_addr_mv _ _ mem3 mem2 p n MV); [|exact Ha].
        intros i Hi.
        assert (Hb : fr <= p /\ 0 <= n /\ p + n <= fr + 4096)
          by (destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; lia).
        assert (Hs : B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr (p + i) < B.AsanRT.shadow_addr fr + 512)
          by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hi Hb Hfr32; Z.div_mod_to_equations; lia).
        split; [exact (proj1 (Pfrsh _ Hs))|]. apply HoW. left.
        pose proof (Hsh_lo (p + i) ltac:(lia)). lia.
      - intros a bs Hr Hb. apply KB2; [|exact Hb]. intros x Hx.
        assert (HBA : 0x10000 <= B.ACtlCutP.BAC.BA_FR + 72 /\
                      B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
          by (split; apply Z.leb_le; vm_compute; reflexivity).
        assert (Hix : 0x10000 <= x < 0x5fe000).
        { destruct Hr as [Hr|Hr]; [lia|].
          unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hr. lia. }
        split; [apply Vimg; lia | left; lia].
      - intros a bs Hr Hb. exact (w2b_ro_bytes mem3 mem2 a bs HRO HRO2 Hr Hb).
      - intros Hh Hr. exact (ctl_names_addressable ly3 S3 W3 mem2 md2 (B.ACtlCut.c_in cx) (proj1 HJ2) Hh Hr). }
    split; [unfold B.ACtlCut.rgv in *; rewrite F21; exact H21|].
    split; [reflexivity|].
    split.
    { split; [exact HRB2|]. split; [exact Hnz|].
      split; [unfold B.ACtlCut.rgv in *; rewrite F20; exact H20|].
      apply KB2; [|exact HF]. intros x Hx. change (Z.of_nat 0) with 0 in Hx. rewrite HLF in Hx.
      split; [apply Vphi; lia | left; lia]. }
    split.
    { unfold B.ACtlCut.a0v, B.ACtlCut.rgv. rewrite Hv. apply (proj2 Hcmp). intros i Hi.
      rewrite (w2b_aview_vis _ mem3 (phi + 18 + i)) by (apply Vphi; lia).
      rewrite (w2b_aview_vis _ mem3 (B.ACtlCutP.decl_slot fr + i))
        by (apply Vfr; unfold B.ACtlCutP.decl_slot; lia).
      destruct HLS as (_ & _ & HLSb). destruct HDB' as (_ & _ & HDBb).
      replace i with (Z.of_nat (Z.to_nat i)) by lia.
      rewrite (HLSb (Z.to_nat i) ltac:(rewrite HLD; lia)), (HDBb (Z.to_nat i) ltac:(rewrite HLD; lia)).
      reflexivity. }
    unfold B.ACtlCut.rgv in *. rewrite F27. exact H27.
Qed.

(* B81a68_at b (Inv_B81a68_at SIv:1949) -> B81aa0_at b.  S_R20 (Slot.v:99; seg_R20 R20.v:246), b = 0.
   R20F.r20_evt_F (R20F.v:53; 0x81a68 -> the free entry; source R20.v:194: a0 = 0 (a0v regs 0; the guard 0x81a68
   `beqz a0` takes the path, abort jump 0x81a6c refuted), rw_cells (s3 + 316) [CB 8 junk] and stk (s3 + 316)
   (s3 + 324) -- the frame's
   shadow bytes (FRAC: rgv 19 (Sfr fr); V5: fake-frame shadow present and writable); post: ra = 0x81aa0, a0 = s4 =
   phi, munch [(s3 + 316, s3 + 324)]: the journal survives by ajournal_exec, the write set lying in the fake frame's
   shadow (awr_byte: in_frames own6)), then B.ACtlW2a.w2_free_81a9c as for B81914.  Post -> C_B81aa0_at body: RB at
   turn S b from the body's RFb (RB at (RID b) (RFG b)) and SlotModel's RID 1 = RID 0, RFG 1 = RFG 0 (turn 0 writes
   no record); the shadow bytes written are below every body fact's range (they are the frame's shadow, which no cut
   conjunct of C_B81aa0_at reads). *)
Lemma seg_R20 : forall POST (b : nat), CFb POST C81aa0 b -> CFb POST C81a68 b.
Proof.
  intros POST b HY cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B81a68_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (phi & Hperm & HFRAC & Hn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hb0 & HRFb & Ha0 & H27).
  subst b.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  assert (Hl392 : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  unfold B.ACtlCutP.Sfr in Hsh, Hr19.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Pfrsh : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists bb, mem3 (Z_to_bv 64 a) = Some bb).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
    pose proof (proj1 (Hfrsh (a - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
    replace (2147450880 + fr / 8 + (a - (2147450880 + fr / 8))) with a in Hp by lia. exact Hp. }
  assert (Fnoimg : forall a, fr <= a < fr + 4096 -> ~ (0x10000 <= a < 0x5fe000)).
  { intros a Ha Hi. apply w2b_in_img in Hi.
    refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR _) Hi).
    right. left. exists 6, (B.ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite EF, HFB6. exact Ha. }
  assert (HSb : 0 <= B.AsanRT.shadow_addr fr /\ B.AsanRT.shadow_addr fr + 512 <= 2 ^ 64 /\
                0x5fe000 <= B.AsanRT.shadow_addr fr /\ B.AsanRT.shadow_addr fr + 512 <= B.AsanRT.HIGHMEM_BEG)
    by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG; Z.div_mod_to_equations; lia).
  assert (Es3 : bv_unsigned (Sem.reg_get regs3 19) = B.AsanRT.shadow_addr fr).
  { assert (E19 : Sem.reg_get regs3 19 = Z_to_bv 64 (B.AsanRT.shadow_addr fr)) by exact Hr19.
    rewrite E19. apply lib.Lib.MState.unsigned_lit. lia. }
  pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 (B.AsanRT.shadow_addr fr) sh 316 8 Hsh ltac:(rewrite Hl392; lia))
    as Hj.
  replace (B.AsanRT.shadow_addr fr + Z.of_nat 316) with (B.AsanRT.shadow_addr fr + 316) in Hj by lia.
  pose proof HRFb as (HRB0 & Hnz & H20 & HF).
  destruct Hrt as (HAC & HSWc & HSWi & HRO).
  (* ---- the run 0x81a68 -> the free entry (R20F.r20_evt_F: the eight frame-shadow stores), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (R20F.r20_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (junk := firstn 8 (skipn 316 sh)).
    all: try rewrite Es3.
    - exact Ha0.
    - unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. split; [split|].
      + cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [|exact I].
        rewrite length_firstn, length_skipn, Hl392. reflexivity.
      + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hj.
      + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. split; [lia|]. split; [lia|].
        intros i0 Hi0. destruct (proj2 (Pfrsh (B.AsanRT.shadow_addr fr + 316 + i0) ltac:(lia))) as (bb & Hbb).
        unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate.
    - split; [lia|]. split; [lia|]. intros a Ha. destruct (proj2 (Pfrsh a ltac:(lia))) as (bb & Hbb).
      unfold lib.Lib.Mem.wa, wview, lib.Lib.Mem.mrd. rewrite Hbb. split; [discriminate | exists bb; reflexivity].
    - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia |].
      intros a Ha. exact (proj1 (Pfrsh a ltac:(lia))). }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 (R1 & m1 & -> & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 &
                  P25 & P26 & P27 & MU1 & WM1 & ST1) Hhid1 Hsbm1.
  rewrite Es3 in MU1, ST1.
  apply w2b_of_MS.
  set (Wr := [(B.AsanRT.shadow_addr fr + 316, B.AsanRT.shadow_addr fr + 324)]) in MU1.
  assert (HoutW : forall x, (x < B.AsanRT.shadow_addr fr + 316 \/ B.AsanRT.shadow_addr fr + 324 <= x) ->
                    lib.Lib.Frame.outside Wr x)
    by (intros x Hx; unfold Wr; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (G2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by exact P2.
  assert (G3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by exact P3.
  assert (G4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by exact P4.
  assert (G8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by exact P8.
  assert (G9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by exact P9.
  assert (G19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by exact P19.
  assert (G21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by exact P21.
  assert (G22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by exact P22.
  assert (G23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by exact P23.
  assert (G25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by exact P25.
  assert (G26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by exact P26.
  assert (G27 : lib.Reusable.YK11.getr R1 27 = lib.Reusable.YK11.getr regs3 27) by exact P27.
  (* app memory, the image and the stack lie outside the frame-shadow write set *)
  assert (OutApp : forall x, B.AsanRT.app_mem x -> lib.Lib.Frame.outside Wr x).
  { intros x Hx. apply HoutW. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG,
      B.AsanRT.APPMEM_END in Hx. unfold B.AsanRT.HIGHMEM_BEG in HSb.
    destruct Hx as [Hx|Hx]; [|right; lia].
    destruct (Z_lt_dec x (B.AsanRT.shadow_addr fr + 316)); [left; lia | right].
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia. }
  assert (OutFr : forall x, fr <= x < fr + 4096 -> lib.Lib.Frame.outside Wr x).
  { intros x Hx. apply HoutW. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    clear - Hx Hfrapp Hceil Hfr32. Z.div_mod_to_equations. lia. }
  assert (OutImg : forall x, 0 <= x < 0x5fe000 -> lib.Lib.Frame.outside Wr x)
    by (intros x Hx; apply HoutW; left; lia).
  assert (OutHi : forall x, B.AsanRT.HIGHMEM_BEG <= x -> lib.Lib.Frame.outside Wr x)
    by (intros x Hx; apply HoutW; right; lia).
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 m1 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := m1) (mdc' := md1)
      (Wr := fun a => B.AsanRT.shadow_addr fr + 316 <= a < B.AsanRT.shadow_addr fr + 324); [exact HJ | | | | | ].
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1 x); [reflexivity|]. apply HoutW. lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Ex; [exact Hx|].
      destruct (B.Prog.Seg.RHelp.rh_out_dec Wr (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU1 x Ho); exact Hx|].
      assert (Hin : B.AsanRT.shadow_addr fr + 316 <= bv_unsigned x < B.AsanRT.shadow_addr fr + 324).
      { destruct (Z_lt_dec (bv_unsigned x) (B.AsanRT.shadow_addr fr + 316)); [exfalso; apply Ho, HoutW; lia|].
        destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 324) (bv_unsigned x)); [exfalso; apply Ho, HoutW; lia|].
        lia. }
      assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; lia).
      assert (Hw0 : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity]. }
      pose proof (WM1 x Hw0) as Hw. unfold wview in Hw.
      rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
      destruct (m1 x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
    - intros x Hx. pose proof (Hhid1 x Hx) as E1. cbn [ms_mem lib.Lib.MState.MS] in E1. exact E1.
    - exact Hsbm1.
    - intros a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx).
      split; [cbn; left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia. }
  (* turn 0 writes no record: RID / RFG at turn 1 are turn 0's *)
  destruct (B.Prog.Seg.R16.r16_RS_012 (B.ACtlCut.c_in cx) 0 ltac:(lia)) as (ERID & ERFG).
  apply (w2b_free_to_81aa0 POST 0 cx fr k phi ly3 S3 W3 R1 m1 md1 HY HB HJ1 Hfrs Hfa Hk Hb6 Hperm).
  - apply (w2b_FRAC_keep_sh cx fr regs3 R1 mem3 m1 Wr HFRAC MU1 G2 G3 G4 G8 G9 G19 G26).
    + intros A' x HA' HA'r Hx. assert (EA : sp <= A').
      { unfold B.ACtlCut.rgv in HA', Hr9. rewrite Hr9 in HA'. apply (f_equal bv_unsigned) in HA'.
        rewrite !lib.Lib.MState.unsigned_lit_wrap in HA'. rewrite (Z.mod_small A) in HA' by lia.
        change (2 ^ 64) with 18446744073709551616 in HA'. Z.div_mod_to_equations. lia. }
      apply OutHi. unfold B.AsanRT.HIGHMEM_BEG. lia.
    + intros x Hx. apply OutFr. lia.
    + intros x Hx. destruct (B.Prog.Seg.RHelp.rh_out_dec Wr x) as [Ho|Ho]; [left; exact Ho | right].
      destruct ST1 as (_ & _ & HST). apply (HST x).
      destruct (Z_lt_dec x (B.AsanRT.shadow_addr fr + 316)); [exfalso; apply Ho, HoutW; lia|].
      destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 324) x); [exfalso; apply Ho, HoutW; lia|]. lia.
    + intros x Hx. apply OutHi. unfold B.AsanRT.HIGHMEM_BEG. lia.
    + intros x Hx. apply OutFr. lia.
  - exact Hn.
  - unfold B.ACtlCut.rgv in *. rewrite G22. exact H22.
  - unfold B.ACtlCutP.OURb in *. apply (B.Prog.RcAsanFPLib.fl_bytes Wr mem3 m1 _ _ HOUR MU1).
    rewrite B.Prog.SlotModel.OUR_length. intros x Hx. apply OutFr. lia.
  - apply (w2b_RBE_transfer cx fr regs3 R1 mem3 m1 HRBE).
    + intros off v Ho0 Ho1 Hs.
      exact (B.Prog.Seg.RHelp.rh_spill_keep regs3 R1 mem3 m1 Wr A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1 P9 MU1
               (fun x Hx => OutHi x ltac:(unfold B.AsanRT.HIGHMEM_BEG; lia))).
    + intros p n Hpn Ha. apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 Wr p n Ha MU1).
      intros i0 Hi0. apply HoutW. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      clear - Hpn Hi0 Hfr32. destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        Z.div_mod_to_equations; lia.
    + intros a bs Hr Hb. apply (B.Prog.RcAsanFPLib.fl_bytes Wr mem3 m1 a bs Hb MU1). intros x Hx. apply OutImg.
      assert (HBA : B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
        by (apply Z.leb_le; vm_compute; reflexivity).
      pose proof Hb as (Hb0 & _).
      unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hr. lia.
    + intros a bs Hr Hb. apply (B.Prog.RcAsanFPLib.fl_bytes Wr mem3 m1 a bs Hb MU1). intros x Hx.
      pose proof Hb as (Hb0 & Hb1 & _). pose proof (Hr x Hx) as Hro.
      apply OutImg. unfold lib.Lib.Mem.ro_addr in Hro.
      destruct (Z_lt_dec x 0x5fe000) as [Hl|Hl]; [lia|]. exfalso.
      rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned (Z_to_bv 64 x))) in Hro;
        [cbn iota in Hro; discriminate Hro|].
      rewrite lib.Lib.MState.unsigned_lit by lia. rewrite <- B.ProgBridge.tfibsegs_rsegs, w2b_in_img. lia.
    + intros Hh Hr. pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                         _ & _ & _ & HNM & _).
      destruct (HNM (conj Hh Hr)) as (_ & _ & Haddr & _).
      apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 Wr _ _ Haddr MU1).
      intros i0 Hi0. pose proof (w2b_name_img (B.ACtlCut.c_in cx) Hh) as (Hn0 & Hn1).
      destruct (Z_lt_dec (B.AsanRT.shadow_addr (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) + i0))
                  (B.AsanRT.shadow_addr fr + 316)) as [Hl|Hl]; [apply HoutW; left; exact Hl|].
      destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 324)
                  (B.AsanRT.shadow_addr (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) + i0)))
        as [Hr'|Hr']; [apply HoutW; right; exact Hr'|].
      exfalso. apply (Fnoimg (B.ACtlCutP.RS6.rname (B.ACtlCutP.SM.rt_mb (B.ACtlCut.c_in cx)) + i0)).
      * unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hl, Hr'. clear - Hl Hr' Hfr32. Z.div_mod_to_equations. lia.
      * lia.
  - unfold B.ACtlCut.rgv in *. rewrite G21. exact H21.
  - rewrite ERID, ERFG.
    apply (w2b_RB_keep cx fr 0 _ _ regs3 R1 mem3 m1 Wr HRB0 MU1
             (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 0)
             (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) 0 ltac:(lia)) G22 G23 G25);
      intros x Hx; apply OutFr; lia.
  - unfold B.ACtlCut.rgv in *. rewrite G27. exact H27.
  - exact (w2b_ctlrt cx (own6 cx) ly3 S3 W3 m1 md1 k HB HJ1).
  - unfold B.ACtlCut.rgv in *. exact (eq_trans P10 H20).
  - exact P1.
Qed.

(* ---- S_R21 / S_R21_a5c's shared tail: the identity-record check from 0x81b00 (proof-internal) ---- *)

(* A view read inside a visible byte run. *)
Lemma w2b_aview_of_bytes : forall (H : word -> bool) (mem : word -> option byte) p bs a,
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem p bs -> H (Z_to_bv 64 a) = false -> p <= a < p + Z.of_nat (length bs) ->
  Reusable.YG0n.aview segs H mem a = option_map (fun b : byte => bv_unsigned b) (nth_error bs (Z.to_nat (a - p))).
Proof.
  intros H mem p bs a (H0 & H1 & Hb) Hv Ha. rewrite (w2b_aview_vis H mem a Hv).
  rewrite <- (Hb (Z.to_nat (a - p)) ltac:(lia)). replace (p + Z.of_nat (Z.to_nat (a - p))) with a by lia.
  reflexivity.
Qed.

Lemma w2b_aview_of_bytes_some : forall (H : word -> bool) (mem : word -> option byte) p bs a,
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem p bs -> H (Z_to_bv 64 a) = false -> p <= a < p + Z.of_nat (length bs) ->
  Reusable.YG0n.aview segs H mem a <> None.
Proof.
  intros H mem p bs a Hb Hv Ha. rewrite (w2b_aview_of_bytes H mem p bs a Hb Hv Ha).
  destruct (nth_error bs (Z.to_nat (a - p))) eqn:E; [discriminate | apply nth_error_None in E; lia].
Qed.

(* Two visible copies of a NUL-terminated string meet at its NUL (AStrcmpDef.str_meet with c1 = c2 = 0). *)
Lemma w2b_str_meet : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) x y (l : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem x (l ++ [Z_to_bv 8 0]) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem y (l ++ [Z_to_bv 8 0]) ->
  (forall a, x <= a <= x + Z.of_nat (length l) -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  (forall a, y <= a <= y + Z.of_nat (length l) -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  ~ In (Z_to_bv 8 0) l ->
  Reusable.AStrcmpDef.str_meet segs W mem x y (Z.of_nat (length l)) 0 0.
Proof.
  intros W mem x y l Hx Hy Vx Vy Hnz.
  assert (Hlen : Z.of_nat (length (l ++ [Z_to_bv 8 0])) = Z.of_nat (length l) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (Ek : nth_error (l ++ [Z_to_bv 8 0]) (length l) = Some (Z_to_bv 8 0))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  unfold Reusable.AStrcmpDef.str_meet. split; [lia|]. split.
  - intros i Hi.
    destruct (nth_error l (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    exists (bv_unsigned b).
    rewrite (w2b_aview_of_bytes _ mem x _ (x + i) Hx (Vx (x + i) ltac:(lia)) ltac:(lia)).
    rewrite (w2b_aview_of_bytes _ mem y _ (y + i) Hy (Vy (y + i) ltac:(lia)) ltac:(lia)).
    replace (x + i - x) with i by lia. replace (y + i - y) with i by lia.
    rewrite nth_error_app1 by lia. rewrite E. split; [reflexivity|]. split; [reflexivity|].
    intros E0. apply Hnz. replace (Z_to_bv 8 0) with b; [exact (nth_error_In _ _ E)|].
    apply bv_eq. rewrite E0. reflexivity.
  - split; [|split; [|right; reflexivity]].
    + rewrite (w2b_aview_of_bytes _ mem x _ (x + Z.of_nat (length l)) Hx (Vx (x + Z.of_nat (length l)) ltac:(lia))
                ltac:(lia)).
      replace (Z.to_nat (x + Z.of_nat (length l) - x)) with (length l) by lia. rewrite Ek. reflexivity.
    + rewrite (w2b_aview_of_bytes _ mem y _ (y + Z.of_nat (length l)) Hy (Vy (y + Z.of_nat (length l)) ltac:(lia))
                ltac:(lia)).
      replace (Z.to_nat (y + Z.of_nat (length l) - y)) with (length l) by lia. rewrite Ek. reflexivity.
Qed.

(* THE TAIL 0x81b00 (S_R21 and S_R21_a5c at b = 6): R21Fs.r21_tail_pre_Fs (the narrowed tail stretch) lifted; the
   identity record of turn 7 ([A + 144] = fr + 2176, IDBr) and the catalogue row ([A + 272] = mrow, RBE; its granules'
   shadow zero by ctl_cat_addressable, visible by ctl_cat_shadow_vis) refute every abort jump, and [A + 32] = 0 the
   trap row 8.  On h = has_identity_record = 0 the continuation K0 takes the cut at 0x81c60 (memory unchanged,
   a0 = 0).  On h <> 0 H_strcmp compares the record's name at fr + 2179 with the row's name (RBE's bytes / V6, its
   shadow by ctl_names_shadow_vis), both NUL-terminated copies of rt_nb, and returns 0 at 0x81c58 = C_B81c58: the
   facts there by ctl_post_strcmp (only [sp - 2 ESTACK, sp) changes), ctl_rt by w2b_ctlrt, the kind-name table by
   ctl_kind_name_addressable. *)
Lemma w2b_tail_81b00 : forall POST (cx : ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs)
    (regsT : bvmap 5 word) (m : word -> option byte) md3,
  CF POST C81c58 ->
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 m md3 k -> k <= 14 ->
  Reusable.YG01.frames S3 = own6 cx ->
  (forall cid pos, In (cid, pos) (own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx) ->
  B.ACtlCutP.FRAC B cx fr fr regsT m -> B.ACtlCut.c_n cx < 2 ^ 26 ->
  B.ACtlCutP.CUR cx 7 regsT -> B.ACtlCutP.OURb cx fr m ->
  B.ACtlCutP.IDBr cx fr (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7) m -> B.ACtlCutP.RBE cx fr regsT m ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 m ->
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rw32 (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) 56 = 0 ->
   forall (R : bvmap 5 word) md1, AJ cx (own6 cx) ly3 S3 W3 m md1 k ->
     lib.Reusable.YK11.getr R 10 = Z_to_bv 64 0 ->
     lib.Reusable.YK11.getr R 1 = lib.Reusable.YK11.getr regsT 1 ->
     lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regsT 2 ->
     lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regsT 3 ->
     lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regsT 4 ->
     lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regsT 8 ->
     lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regsT 9 ->
     lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regsT 18 ->
     lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regsT 19 ->
     lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regsT 20 ->
     lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regsT 21 ->
     lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regsT 22 ->
     lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regsT 23 ->
     lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regsT 24 ->
     lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regsT 25 ->
     lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regsT 26 ->
     lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regsT 27 ->
     Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81c60 R m md1) (POST cx)) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81b00 regsT m md3) (POST cx).
Proof.
  intros POST cx fr k ly3 S3 W3 regsT m md3 HY HB HJ Hk Hfrs Hfa Hperm HFRAC Hn HCUR HOUR HIDB HRBE Hrt K0.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (Hsp0m & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hstk : lib.Reusable.YM05.alloc_ceiling + 32768 <= B.ACtlCut.c_sp cx) by lia.
  pose proof HB as ((Hafn & _ & _ & _ & _ & Hnlen & _) & _). pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  (* ---- the frame (above the image, below the stack window), its shadow ---- *)
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HfrGT : 0x5fe000 <= fr).
  { rewrite <- EF. exact (w2b_frame_above_img ly3 S3 W3 m md3 (B.ACtlCut.c_fpos cx) HAR Hin6). }
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 m md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 m md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Pfrsh : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists bb, m (Z_to_bv 64 a) = Some bb).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
    pose proof (proj1 (Hfrsh (a - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
    replace (2147450880 + fr / 8 + (a - (2147450880 + fr / 8))) with a in Hp by lia. exact Hp. }
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfrb a Ha)))).
  assert (Vstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hwin a Ha))).
  assert (Hsh_lo : forall a, 0 <= a < 2 ^ 47 -> B.AsanRT.shadow_addr a + 4096 < sp - 8192).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Ha Hceil Hstk HS4096.
    Z.div_mod_to_equations. lia. }
  assert (Hshf0 : B.AsanRT.shadow_addr fr + 4096 < sp - 8192) by (apply Hsh_lo; lia).
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  pose proof Hrt as (HAC & HSWc & HSWi & HRO).
  (* ---- the model facts of the identity-record check ---- *)
  pose proof (B.Prog.Seg.RtmB.rb_istar_range (B.ACtlCut.c_in cx)) as Hi11.
  pose proof (B.Prog.Seg.RtmB.rb_mrow_range (B.ACtlCut.c_in cx)) as (Hmr0 & Hmr1 & Hmr8).
  unfold B.Prog.SlotModel.CAT in Hmr0, Hmr1.
  pose proof (B.Prog.Seg.RtmB.rb_mb_len (B.ACtlCut.c_in cx)) as HROWL.
  pose proof (B.Prog.Seg.RtmB.rb_RID_len (B.ACtlCut.c_in cx) 7) as HIDL.
  destruct (B.Prog.Seg.RtmB.rb_rtm_fw (B.ACtlCut.c_in cx)) as (Ehf & Efw).
  destruct (B.Prog.Seg.RtmB.rb_rtm_ver (B.ACtlCut.c_in cx)) as (Ehv & Emaj & Emin & Epat).
  destruct (B.Prog.Seg.RtmB.rb_row_facts (B.Prog.SlotModel.istar (B.ACtlCut.c_in cx)) Hi11)
    as (Hh32 & Ehid & Hnmf).
  destruct (B.Prog.Seg.RtmB.rb_row_le (B.Prog.SlotModel.istar (B.ACtlCut.c_in cx)) Hi11) as (L56 & L280).
  change (B.Prog.SlotModel.rowb (B.Prog.SlotModel.istar (B.ACtlCut.c_in cx)))
    with (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) in Hh32, Ehid, Hnmf, L56, L280.
  set (mr := B.Prog.SlotModel.mrow (B.ACtlCut.c_in cx)) in *.
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOURa & HTBL & HBOX & HMROW & _).
  (* the spill words the tail loads *)
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regsT m A 144 _ S144 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Q144.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regsT m A 32 _ S32 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q32.
  pose proof (B.Prog.Seg.RHelp.rh_spill_at regsT m A 272 _ S272 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Q272.
  pose proof (B.Prog.Seg.RHelp.rh_rdn m _ _ 8 Q144 (lib.Lib.Mem.length_le8 _)) as R144.
  pose proof (B.Prog.Seg.RHelp.rh_rdn m _ _ 8 Q32 (lib.Lib.Mem.length_le8 _)) as R32.
  pose proof (B.Prog.Seg.RHelp.rh_rdn m _ _ 8 Q272 (lib.Lib.Mem.length_le8 _)) as R272.
  (* the catalogue row's granules have shadow byte 0 *)
  pose proof (ctl_cat_addressable ly3 S3 W3 m md3 HAR) as HCA.
  assert (HADrow : forall p, 652832 <= p -> p + 8 <= 652832 + 3256 -> B.AsanRT.addressable m p 8).
  { intros p Hp1 Hp2.
    pose proof (B.AsanRTFacts.addressable_sub m B.ACtlCutP.SM.CAT _ (p - B.ACtlCutP.SM.CAT) 8 HCA) as H.
    unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in H.
    replace (652832 + (p - 652832)) with p in H by lia. apply H; lia. }
  assert (Hm8 : forall j, (mr + j) mod 8 = j mod 8) by (intros j; clear - Hmr8; Z.div_mod_to_equations; lia).
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 264) (mr + 266) (HADrow (mr + 264) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K266.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 264) (mr + 268) (HADrow (mr + 264) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K268.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 264) (mr + 270) (HADrow (mr + 264) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K270.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 272) (mr + 272) (HADrow (mr + 272) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K272.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 56) (mr + 56) (HADrow (mr + 56) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K56.
  pose proof (B.Prog.Seg.RHelp.rh_meta0 m (mr + 280) (mr + 280) (HADrow (mr + 280) ltac:(lia) ltac:(lia))
                ltac:(rewrite Hm8; reflexivity) ltac:(lia)) as K280.
  (* the identity record's bytes (RID 7) *)
  unfold B.ACtlCutP.IDBr in HIDB.
  pose proof (B.Prog.Seg.R21.r21_rd1 m (fr + 2176) _ 2 HIDB ltac:(rewrite HIDL; lia)) as R2.
  rewrite (B.Prog.Seg.R21.r21_byte1 (nth 2 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehf) in R2.
  pose proof (B.Prog.Seg.R21.r21_rd1 m (fr + 2176) _ 36 HIDB ltac:(rewrite HIDL; lia)) as R36.
  rewrite (B.Prog.Seg.R21.r21_byte1 (nth 36 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehv) in R36.
  pose proof (B.Prog.Seg.R21.r21_rd2 m (fr + 2176) _ 0 HIDB ltac:(rewrite HIDL; lia)) as R0.
  pose proof (B.Prog.Seg.R21.r21_rd2 m (fr + 2176) _ 22 HIDB ltac:(rewrite HIDL; lia)) as R22.
  pose proof (B.Prog.Seg.R21.r21_rd2 m (fr + 2176) _ 24 HIDB ltac:(rewrite HIDL; lia)) as R24.
  pose proof (B.Prog.Seg.R21.r21_rd2 m (fr + 2176) _ 26 HIDB ltac:(rewrite HIDL; lia)) as R26.
  change (fr + 2176 + Z.of_nat 0) with (fr + 2176 + 0) in R0. rewrite Z.add_0_r in R0.
  change (Z.of_nat 2) with 2 in R2. change (Z.of_nat 36) with 36 in R36. change (Z.of_nat 22) with 22 in R22.
  change (Z.of_nat 24) with 24 in R24. change (Z.of_nat 26) with 26 in R26.
  (* the catalogue row's bytes *)
  pose proof (B.Prog.Seg.R21.r21_rd2 m mr _ 266 HMROW ltac:(rewrite HROWL; lia)) as M266.
  pose proof (B.Prog.Seg.R21.r21_rd2 m mr _ 268 HMROW ltac:(rewrite HROWL; lia)) as M268.
  pose proof (B.Prog.Seg.R21.r21_rd2 m mr _ 270 HMROW ltac:(rewrite HROWL; lia)) as M270.
  pose proof (B.Prog.Seg.R21.r21_rd2 m mr _ 272 HMROW ltac:(rewrite HROWL; lia)) as M272.
  pose proof (B.Prog.Seg.R21.r21_rd4 m mr _ 56 HMROW ltac:(rewrite HROWL; lia)) as M56.
  rewrite L56 in M56.
  change (Z.of_nat 266) with 266 in M266. change (Z.of_nat 268) with 268 in M268.
  change (Z.of_nat 270) with 270 in M270. change (Z.of_nat 272) with 272 in M272. change (Z.of_nat 56) with 56 in M56.
  set (h := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rw32 (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) 56)
    in *.
  set (nm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)))
    in *.
  pose proof (ctl_cat_shadow_vis ly3 S3 W3 m md3 HAR) as HCV.
  assert (EL : B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT = 2147532480) by (vm_compute; reflexivity).
  assert (EH : B.Prog.rng_asan.sh_al8_hi B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) =
               2147532896) by (vm_compute; reflexivity).
  rewrite EL, EH in HCV. destruct HCV as (_ & _ & VCs).
  (* ---- the run 0x81b00 -> 0x81c60 / the strcmp trampoline (R21Fs.r21_tail_pre_Fs), lifted ---- *)
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regsT) regsT _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regsT))].
  unfold Lib.Regs6ss.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply B.ProgBridge.fevt_of_evtF.
    eapply (B.Prog.Seg.R21Fs.r21_tail_pre_Fs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (fun ms =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81c60) lib.Reusable.YK11.fp_csr None m
                   (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
            lib.Reusable.YK11.getr R 10 = Z_to_bv 64 0 /\
            lib.Reusable.YK11.getr R 1 = lib.Reusable.YK11.getr regsT 1 /\
            lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regsT 2 /\
            lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regsT 3 /\
            lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regsT 4 /\
            lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regsT 8 /\
            lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regsT 9 /\
            lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regsT 18 /\
            lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regsT 19 /\
            lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regsT 20 /\
            lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regsT 21 /\
            lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regsT 22 /\
            lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regsT 23 /\
            lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regsT 24 /\
            lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regsT 25 /\
            lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regsT 26 /\
            lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regsT 27) \/
         (h <> 0 /\ exists R : bvmap 5 word,
            ms = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 B.Prog.strcmp_wrap_c.STRCMP_WRAP)
                   lib.Reusable.YK11.fp_csr None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
            lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x81c58 /\
            lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (fr + 2176 + 3) /\
            lib.Reusable.YK11.getr R 11 = Z_to_bv 64 nm /\
            lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regsT 2 /\
            lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regsT 3 /\
            lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regsT 4 /\
            lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regsT 8 /\
            lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regsT 9 /\
            lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regsT 19 /\
            lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regsT 21 /\
            lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regsT 22 /\
            lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regsT 23 /\
            lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regsT 24 /\
            lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regsT 25 /\
            lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regsT 26)))
      with (A := A) (S5 := fr + 2176) (mr := mr)
           (fw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.fw_milli
                    (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7))
           (maj := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.major
                     (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7))
           (mnr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.minor
                     (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7))
           (pat := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.patch
                     (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7))
           (h := h) (nm := nm).
    all: try first [ exact Hr9 | exact Hr26 | exact R144 | exact R32 | exact R272 | exact R2 | exact R36
                   | exact K266 | exact K268 | exact K270 | exact K272 | exact K56 | exact K280
                   | (intros _; exact K280)
                   | exact R0 | exact R22 | exact R24 | exact R26 | exact M56
                   | (rewrite Efw; exact M266) | (rewrite Emaj; exact M268) | (rewrite Emin; exact M270)
                   | (rewrite Epat; exact M272) ].
    all: try (match goal with
              | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia
              end).
    all: try (rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
              apply B.ProgBridge.rng_of_visible, w2b_rv;
              [ first [lia | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia]
              | first [lia | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia]
              | intros a Ha;
                first [ apply Vstk; lia | apply Vfr; lia | apply Vimg; lia
                      | apply VCs; unfold B.AsanRT.ASAN_K in Ha |- *; clear - Ha Hmr0 Hmr1;
                        Z.div_mod_to_equations; lia ] ]).
    (* a Theorem Labs lane's weakened form (d91a1b23270): the rows read only on the h <> 0 arm, under the implication *)
    all: try (intros _; split; [|split];
              (rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
               apply B.ProgBridge.rng_of_visible, w2b_rv;
               [ first [lia | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia]
               | first [lia | unfold B.AsanRT.ASAN_K; clear - Hmr0 Hmr1; Z.div_mod_to_equations; lia]
               | intros a Ha;
                 first [ apply Vstk; lia | apply Vfr; lia | apply Vimg; lia
                       | apply VCs; unfold B.AsanRT.ASAN_K in Ha |- *; clear - Ha Hmr0 Hmr1;
                         Z.div_mod_to_equations; lia ] ])).
    - (* h <> 0: the flag byte at S5 + 20, the row's name pointer *)
      intros Hh0.
      assert (Hhid : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.em_hid
                       (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) <> 0)
        by (intros E; apply Hh0; apply Ehid; exact E).
      destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & _).
      assert (Hn6 : B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) 6 <> 0)
        by (apply (proj2 (B.Prog.Seg.RtmB.rb_rtm_hid _)); exact Hhid).
      destruct (B.Prog.Seg.RtmB.rb_rtm_name _ Hn6) as (Ehn & _).
      pose proof (B.Prog.Seg.R21.r21_rd1 m (fr + 2176) _ 20 HIDB ltac:(rewrite HIDL; lia)) as R20.
      rewrite (B.Prog.Seg.R21.r21_byte1 (nth 20 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehn)
        in R20.
      change (Z.of_nat 20) with 20 in R20.
      pose proof (B.Prog.Seg.R21.r21_rd8 m mr _ 280 HMROW ltac:(rewrite HROWL; lia)) as R280.
      rewrite L280 in R280. change (Z.of_nat 280) with 280 in R280.
      split; [exact R20|]. split; [exact R280|]. lia.
    - (* h = 0: the cut 0x81c60 *)
      intros Eh0 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ha0.
      apply Lib.ExecF.evtF_done. left. split; [exact Eh0|].
      eexists. split; [reflexivity|].
      split; [exact Ha0|]. repeat split; reflexivity.
    - (* h <> 0: the strcmp trampoline *)
      intros Hh0 R E1 E10 E11 E2 E3 E4 E8 E9 E19 E21 E22 E23 E24 E25 E26.
      right. split; [exact Hh0|].
      exists R. split; [reflexivity|].
      split; [exact E1|]. split; [exact E10|]. split; [exact E11|].
      repeat split; assumption. }
  { exact (B.ProgBridge.fp_avoids_RNG_W _). }
  intros ms1 md1 HQ Hhid1 Hsbm1.
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 m md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := m) (mdc' := md1)
      (Wr := fun _ => False); [exact HJ | | | | | ].
    - intros x _. reflexivity.
    - intros x Hx. exact Hx.
    - intros x Hx. pose proof (Hhid1 x Hx) as E1. destruct HQ as [(_ & R & -> & _)|(_ & R & -> & _)]; exact E1.
    - exact Hsbm1.
    - intros a []. }
  destruct HQ as [(Eh0 & R & -> & E10 & E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 &
                   E25 & E26 & E27) |
                  (Hh0 & R & -> & E1 & E10 & E11 & E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E23 & E24 & E25 & E26)].
  { (* h = 0 *)
    apply w2b_of_MS. exact (K0 Eh0 R md1 HJ1 E10 E1 E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27). }
  (* ---- h <> 0: H_strcmp on the record's name and the row's name ---- *)
  apply w2b_of_MS. rewrite <- B_strcmp_tramp_at.
  assert (Hhid : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.em_hid
                   (B.Prog.SlotModel.rt_mb (B.ACtlCut.c_in cx)) <> 0)
    by (intros E; apply Hh0; apply Ehid; exact E).
  destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & _).
  assert (Hn6 : B.Prog.SlotModel.rt_n (B.ACtlCut.c_in cx) 6 <> 0)
    by (apply (proj2 (B.Prog.Seg.RtmB.rb_rtm_hid _)); exact Hhid).
  destruct (B.Prog.Seg.RtmB.rb_rtm_name _ Hn6) as (Ehn & Efn & Elast & Hall & Hlen16).
  apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
  assert (Hnm' : nm <> 0) by lia.
  destruct (HNM (conj Hh0 Hnm')) as (_ & HBY & HAY & _).
  set (nb := B.Prog.SlotModel.rt_nb (B.ACtlCut.c_in cx)) in *.
  assert (Hnn : nb <> []) by (intros E; rewrite E in Hl1; cbn [length] in Hl1; lia).
  assert (Enb : nb = removelast nb ++ [Z_to_bv 8 0]).
  { change (last nb (Z_to_bv 8 1) = Z_to_bv 8 0) in Elast.
    pose proof (@app_removelast_last _ nb (Z_to_bv 8 1) Hnn) as X. rewrite Elast in X. exact X. }
  assert (HLsx : (length (removelast nb) + 1 = length nb)%nat)
    by (rewrite Enb at 2; rewrite length_app; cbn [length]; lia).
  assert (HNin : ~ In (Z_to_bv 8 0) (removelast nb)).
  { intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X. vm_compute in X. discriminate X. }
  assert (HBX : lib.Lib.Mem.bytes_at B.Img0.rsegs m (fr + 2176 + 3) (removelast nb ++ [Z_to_bv 8 0])).
  { rewrite <- Enb.
    assert (Es : firstn (length nb) (skipn 3 (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) 7)) = nb).
    { rewrite <- Efn at 2.
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.model_name,
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.get,
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.OFF_NAME,
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.NAME_CAP.
      rewrite firstn_firstn. f_equal. lia. }
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub m (fr + 2176) _ 3 (length nb) HIDB ltac:(rewrite HIDL; lia)) as X.
    rewrite Es in X. change (Z.of_nat 3) with 3 in X. exact X. }
  assert (HBY' : lib.Lib.Mem.bytes_at B.Img0.rsegs m nm (removelast nb ++ [Z_to_bv 8 0])) by (rewrite <- Enb; exact HBY).
  set (kk := Z.of_nat (length (removelast nb))) in *.
  assert (Hkk : kk + 1 = Z.of_nat (length nb)) by (unfold kk; lia).
  assert (HspR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz).
  assert (Hni : 0x10000 <= nm /\ nm + Z.of_nat (length nb) <= 0x5fe000)
    by exact (w2b_name_img (B.ACtlCut.c_in cx) Hh0).
  assert (Vnm : forall a, nm <= a < nm + Z.of_nat (length nb) -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. apply Vimg. lia. }
  assert (Vx : forall a, fr + 2176 + 3 <= a < fr + 2176 + 3 + Z.of_nat (length nb) ->
                 Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. apply Vfr. lia. }
  pose proof (ctl_names_shadow_vis ly3 S3 W3 m md3 (B.ACtlCut.c_in cx) HAR Hh0 ltac:(lia)) as HNV.
  destruct HNV as (_ & _ & VNs).
  assert (VNs' : forall s, B.Prog.rng_asan.sh_al8_lo nm <= s <
                   B.Prog.rng_asan.sh_al8_hi nm (Z.of_nat (length nb)) -> Reusable.YA0n.w_H W3 (Z_to_bv 64 s) = false).
  { intros s Hs. apply VNs. fold nm nb. lia. }
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in VNs'.
  assert (HAX : B.AsanRT.addressable m (fr + 2176 + 3) (Z.of_nat (length nb)))
    by (apply (B.AsanRTFacts.addressable_sub m (fr + 2176) 38 3 (Z.of_nat (length nb)) HA2176); lia).
  assert (HPRE : Reusable.YG0d.ecall_pre segs B ly3 S3 W3 R m md1).
  { eapply Reusable.YCbq.ecall_pre_at with (o := sp - B.ACtlCut.c_sp cx); [exact HJ1 | | | | | | |].
    - rewrite HspR. lia.
    - clear - Hsp16 Hsp0m. Z.div_mod_to_equations. lia.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - rewrite E1. apply lib.Reusable.YK0s.ret_ok_even. rewrite lib.Lib.MState.unsigned_lit by lia. reflexivity.
    - rewrite E3, Hr3. exact Hgp0.
    - rewrite E4. exact Hr4. }
  eapply Reusable.YA0n.SRr_bind.
  { apply (H_strcmp ly3 S3 W3 R m md1 (fr + 2176 + 3) nm kk 0 0 HPRE).
    - pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _). rewrite Eslo, HspR.
      unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - intros a Ha. rewrite HspR in Ha. apply Hwin. unfold Reusable.YG0d.ESTACK in Ha. lia.
    - exact E10.
    - exact E11.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply (w2b_str_meet W3 m _ _ (removelast nb) HBX HBY').
      + intros a Ha. apply Vx. lia.
      + intros a Ha. apply Vnm. lia.
      + exact HNin.
    - intros a Ha. rewrite HspR. split.
      + apply (w2b_aview_of_bytes_some _ m _ _ a HBX (Vx a ltac:(lia))). rewrite length_app. cbn [length]. lia.
      + unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. rewrite HspR. split.
      + apply (w2b_aview_of_bytes_some _ m _ _ a HBY' (Vnm a ltac:(lia))). rewrite length_app. cbn [length]. lia.
      + unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. rewrite HspR. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. rewrite HspR. unfold Reusable.YG0d.ESTACK. lia.
    - apply Reusable.YCbq.amem_range_high; lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd. left. lia.
    - apply (w2b_ra_of_addr (Reusable.YA0n.w_H W3) m (fr + 2176 + 3) (kk + 1) ltac:(rewrite Hkk; exact HAX)).
      intros i Hi.
      apply (proj1 (Pfrsh (B.AsanRT.shadow_addr (fr + 2176 + 3 + i))
                      ltac:(unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hi Hkk Hl2 Hfr32;
                            Z.div_mod_to_equations; lia))).
    - unfold Reusable.YG0d.shadow_hull_vis. intros s Hs. apply w2b_aview_some.
      apply Pfrsh. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hs.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hs Hkk Hl2 Hfr32. Z.div_mod_to_equations. lia.
    - apply (w2b_ra_of_addr (Reusable.YA0n.w_H W3) m nm (kk + 1) ltac:(rewrite Hkk; exact HAY)). intros i Hi.
      apply VNs'.
      unfold B.AsanRT.shadow_addr. clear - Hi Hkk. Z.div_mod_to_equations. lia.
    - unfold Reusable.YG0d.shadow_hull_vis. intros s Hs.
      assert (Hs' : B.AsanRT.shadow_addr nm / 8 * 8 <= s <
                    B.AsanRT.shadow_addr (nm + Z.of_nat (length nb) - 1) / 8 * 8 + 8).
      { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hs. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
        replace (nm + Z.of_nat (length nb) - 1) with (nm + kk) by lia. clear - Hs. Z.div_mod_to_equations. lia. }
      pose proof (VNs' s Hs') as Hv.
      assert (Hsh : B.AsanRT.in_shadow s).
      { unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
          B.AsanRT.HIGHMEM_BEG. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hs'. left.
        clear - Hs' Hni Hkk Hl2. Z.div_mod_to_equations. lia. }
      assert (Himg : B.ACtlRtC.img_shadow s).
      { exists ((s - Reusable.YG0f.SHADOW_OFF) * 8).
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hs'. clear - Hs' Hni Hkk Hl2. Z.div_mod_to_equations. lia. }
      destruct (HSWi s Himg Hsh) as (_ & bb & Hbb).
      rewrite (w2b_aview_vis _ m s Hv). unfold lib.Lib.Mem.wa in *. rewrite Hbb. discriminate. }
  cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm2 & Hv & Hfr & Hpres2).
  assert (Era : Reusable.YG0d.raZ R = 0x81c58)
    by (unfold Reusable.YG0d.raZ; rewrite E1; apply lib.Lib.MState.unsigned_lit; lia).
  rewrite Era.
  pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT1).
  assert (HJ2 : AJ cx (own6 cx) ly3 S3 W3 mem2 md2 k).
  { eapply (Reusable.YCbq.ajournal_after_write segs B LAWS w2b_segs_low) with
      (Wr := fun a => sp - 2 * Reusable.YG0d.ESTACK <= a < sp) (S' := S3) (own2 := own6 cx);
      [exact HJ1 | | | | | | | | | | ].
    - intros a Ha Hna. rewrite HspR in Hfr. apply (Hfr a Ha). exact Hna.
    - exact Hpres2.
    - exact Hsbm2.
    - intros a Ha. left. left. unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK in *. lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs1.
    - exact HQT1. }
  (* the trampoline's post at visible addresses *)
  destruct (ctl_post_strcmp W3 m mem2 sp) as (MV & _).
  { split; [|exact Hpres2]. intros a Ha Ho. rewrite HspR in Hfr. apply Hfr; [exact Ha|].
    cbn [lib.Lib.Frame.outside] in Ho. lia. }
  assert (HoW : forall x, (x < sp - 8192 \/ sp <= x) ->
                  lib.Lib.Frame.outside [(sp - 2 * Reusable.YG0d.ESTACK, sp)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; unfold Reusable.YG0d.ESTACK; split; [lia | exact I]).
  assert (KB2 : forall a bs,
            (forall x, a <= x < a + Z.of_nat (length bs) ->
               Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\ (x < sp - 8192 \/ sp <= x)) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 a bs).
  { intros a bs HX Hb. apply (w2b_bytes_mv _ _ m mem2 a bs MV); [|exact Hb].
    intros x Hx. destruct (HX x Hx) as (Hv' & Ho). split; [exact Hv' | exact (HoW x Ho)]. }
  pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 mem2 md2 k HB HJ2) as Hrt2.
  pose proof Hrt2 as (_ & _ & _ & HRO2).
  assert (G : forall r : Z, Reusable.YG0d.acallee_saved r ->
            lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr R (Z_to_bv 5 r)) by exact HP.
  assert (F2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regsT 2)
    by (rewrite <- E2; apply (G 2); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regsT 3)
    by (rewrite <- E3; apply (G 3); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regsT 4)
    by (rewrite <- E4; apply (G 4); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regsT 8)
    by (rewrite <- E8; apply (G 8); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regsT 9)
    by (rewrite <- E9; apply (G 9); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regsT 19)
    by (rewrite <- E19; apply (G 19); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F23 : lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regsT 23)
    by (rewrite <- E23; apply (G 23); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regsT 25)
    by (rewrite <- E25; apply (G 25); unfold Reusable.YG0d.acallee_saved; lia).
  assert (F26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regsT 26)
    by (rewrite <- E26; apply (G 26); unfold Reusable.YG0d.acallee_saved; lia).
  assert (KS : forall off v, 0 <= off -> off + 8 <= 448 ->
            B.ACtlCutP.spill regsT m off v -> B.ACtlCutP.spill regs2 mem2 off v).
  { intros off v Ho0 Ho1 Hs.
    pose proof (B.Prog.Seg.RHelp.rh_spill_at regsT m A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1) as Hq.
    exists A. split; [unfold B.ACtlCut.rgv in *; rewrite F9; exact Hr9|].
    unfold B.ACtlCutP.q64 in *. apply KB2; [|exact Hq]. rewrite lib.Lib.Mem.length_le8.
    intros x Hx. split; [apply Vstk; lia | right; lia]. }
  assert (HRBE2 : B.ACtlCutP.RBE cx fr regs2 mem2).
  { apply (w2b_RBE_transfer cx fr regsT regs2 m mem2 HRBE KS).
    - intros p n Hpn Ha. apply (w2b_addr_mv _ _ m mem2 p n MV); [|exact Ha].
      intros i Hi.
      assert (Hb : fr <= p /\ 0 <= n /\ p + n <= fr + 4096)
        by (destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; lia).
      assert (Hs : B.AsanRT.shadow_addr fr <= B.AsanRT.shadow_addr (p + i) < B.AsanRT.shadow_addr fr + 512)
        by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hi Hb Hfr32; Z.div_mod_to_equations; lia).
      split; [exact (proj1 (Pfrsh _ Hs))|]. apply HoW. left. lia.
    - intros a bs Hr Hb. apply KB2; [|exact Hb]. intros x Hx.
      assert (HBA : 0x10000 <= B.ACtlCutP.BAC.BA_FR + 72 /\
                    B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
        by (split; apply Z.leb_le; vm_compute; reflexivity).
      assert (Hix : 0x10000 <= x < 0x5fe000).
      { destruct Hr as [Hr|Hr]; [lia|].
        unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hr. lia. }
      split; [apply Vimg; lia | left; lia].
    - intros a bs Hr Hb. exact (w2b_ro_bytes m mem2 a bs HRO HRO2 Hr Hb).
    - intros Hh Hr. exact (ctl_names_addressable ly3 S3 W3 mem2 md2 (B.ACtlCut.c_in cx) (proj1 HJ2) Hh Hr). }
  pose proof HRBE2 as (_ & _ & _ & S264' & _ & _ & S56' & _ & _ & S8' & _ & _ & _ & _ & _ & _ & _ & _ & S176' & S208' &
    S64' & _ & _ & _ & HOURa' & _ & _ & _ & HPRA' & S152' & _ & _ & S160').
  assert (Ec0 : B.Prog.SlotModel.c0 (B.ACtlCut.c_in cx) = 7).
  { destruct HCUR as (Hc0 & _). unfold B.Prog.SlotModel.c0, B.Prog.SlotModel.nlen. lia. }
  refine (HY cx [] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 Hfrs Hfa _ _ Hrt2).
  { cbn [B.ACtlCut.cut_kmax B.ACtlCutP.C_B81c58]. lia. }
  unfold B.ACtlCutP.C_B81c58. cbn [B.ACtlCut.cut_body].
  split; [exact Hperm|].
  split.
  { apply (w2b_FRAC_transfer cx fr regsT regs2 m mem2 HFRAC F2 F3 F4 F8 F9 F19 F26).
    intros a bs HR Hb. apply KB2; [|exact Hb]. intros x Hx.
    destruct (HR x Hx) as [(A' & HA' & HA'r & HA'c & Hx')|[Hx'|[Hx'|Hx']]].
    - assert (EA : A' = A) by (apply (w2b_rg9_eq regsT A A' Hr9 HA'); lia). subst A'.
      split; [apply Vstk; lia | right; lia].
    - split; [apply Vfr; exact Hx' | left; lia].
    - split; [exact (proj1 (Pfrsh x ltac:(lia)))|]. left. lia.
    - split; [apply Vstk; lia | right; lia]. }
  split; [exact Hn|].
  split.
  { unfold B.ACtlCutP.OURb in *. apply KB2; [|exact HOUR]. rewrite B.Prog.SlotModel.OUR_length.
    intros x Hx. split; [apply Vfr; lia | left; lia]. }
  split.
  { unfold B.ACtlCut.a0v, B.ACtlCut.rgv. rewrite Hv. reflexivity. }
  split.
  { unfold B.ACtlCutP.PRO. split; [exact HPRA'|]. split; [exact S152'|]. split; [exact S264'|].
    split; [exact HOURa' | exact S160']. }
  split.
  { exists (B.ACtlCutP.Sfr fr + 68). split; [exact S8'|]. unfold B.ACtlCutP.Sfr. lia. }
  split; [exact S56'|]. split; [exact S176'|]. split; [exact S208'|]. split; [exact S64'|].
  split.
  { rewrite Ec0. destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|]. unfold B.ACtlCut.rgv in *.
    split; [rewrite F23; exact Hc23 | rewrite F25; exact Hc25]. }
  exact (ctl_kind_name_addressable ly3 S3 W3 mem2 md2 (proj1 HJ2)).
Qed.

(* ---- S_R21's helpers (proof-internal) ---- *)

(* FRAC across a visible-only munch that misses the stack from sp up to c_sp and the frame, when every frame-shadow
   byte is present afterwards. *)
Lemma w2b_FRAC_mv_sh : forall cx fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) (H : word -> bool) WR,
  B.ACtlCutP.FRAC B cx fr fr regs m -> munch_vis H WR m m' ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  (forall x, Reusable.YG0d.spZ regs <= x < B.ACtlCut.c_sp cx \/ fr <= x < fr + 4096 ->
     H (Z_to_bv 64 x) = false /\ lib.Lib.Frame.outside WR x) ->
  (forall x, B.AsanRT.shadow_addr fr <= x < B.AsanRT.shadow_addr fr + 392 ->
     exists bb, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some bb) ->
  B.ACtlCutP.FRAC B cx fr fr regs' m'.
Proof.
  intros cx fr regs regs' m m' H WR
    (A & sp & H2 & Hsp & Hspz & H4 & H8 & H9 & H3 & H19 & H26 & Hfr & HA & HAS & HspA & HfrA & HA448 & HS & HSapp &
     Q336 & Q48 & Q40 & Qh & Qe & (sh & Hsh & Hshl) & Hsv & Qtr)
    MV E2 E3 E4 E8 E9 E19 E26 WV WS.
  pose proof HfrA as HfrA'. unfold B.ACtlCutP.FRAME_BYTES in HfrA'.
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) ->
                 Reusable.YG0d.spZ regs <= x < B.ACtlCut.c_sp cx \/ fr <= x < fr + 4096) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs).
  { intros a bs Hx Hb. apply (w2b_bytes_mv H WR m m' a bs MV); [|exact Hb].
    intros x Hx'. exact (WV x (Hx x Hx')). }
  pose proof (lib.Lib.Mem.length_le8) as L8.
  exists A, sp.
  split; [rewrite E2; exact H2|]. split; [exact Hsp|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hspz|].
  split; [rewrite E4; exact H4|].
  unfold B.ACtlCut.rgv in *.
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E3; exact H3|].
  split; [rewrite E19; exact H19|]. split; [rewrite E26; exact H26|].
  do 8 (split; [assumption|]).
  unfold B.ACtlCutP.q64 in *.
  split; [apply KB; [rewrite L8; intros x Hx; left; lia | exact Q336]|].
  split; [apply KB; [rewrite L8; intros x Hx; left; lia | exact Q48]|].
  split; [apply KB; [rewrite L8; intros x Hx; left; lia | exact Q40]|].
  split; [apply KB; [rewrite L8; intros x Hx; right; lia | exact Qh]|].
  split; [apply KB; [rewrite L8; intros x Hx; right; lia | exact Qe]|].
  split.
  { unfold B.ACtlCutP.Sfr, B.ACtlCutP.FRAME_SHADOW, B.ACtlCutP.FRAME_BYTES in *.
    change (Z.to_nat (3136 / 8)) with 392%nat in *.
    pose proof Hsh as (Hs0 & Hs1 & _).
    destruct (B.Prog.Seg.RHelp.rh_bytes_of_present 392 m' (B.AsanRT.shadow_addr fr) ltac:(lia) ltac:(lia))
      as (sh' & Hsh' & Hl').
    { intros k0 Hk0. apply WS. lia. }
    exists sh'. split; [exact Hsh' | exact Hl']. }
  split.
  { apply KB; [|exact Hsv]. intros x Hx. left.
    assert (Hlen : Z.of_nat (length (B.ACtlCutP.saved_bytes cx)) = 104).
    { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !L8. reflexivity. }
    lia. }
  apply KB; [rewrite L8; intros x Hx; right; lia | exact Qtr].
Qed.

(* R6X's facts are RBE's. *)
Lemma w2b_R6X_of_RBE : forall cx b fr (regs : bvmap 5 word) m,
  B.ACtlCutP.RBE cx fr regs m -> B.ACtlCutP.R6X cx b fr regs m.
Proof.
  intros cx b fr regs m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                         HOUT & _ & HNM & HOURa & HTBL & HBOX & HMROW & _).
  split; [exact HOUT|]. split; [exact HOURa|]. split; [exact HTBL|]. split; [exact HBOX|]. split; [exact HMROW|].
  intros (_ & Hc). exact (HNM Hc).
Qed.

(* A non-image byte the write view sees is present. *)
Lemma w2b_present_of_wview : forall (m : word -> option byte) (x : word), ~ (0x10000 <= bv_unsigned x < 0x5fe000) ->
  wview B.Img0.rsegs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x Hni Hw.
  assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; exact Hni).
  unfold wview in Hw. rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
  destruct (m x) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.

(* The facts after the latch's 17 frame-shadow stores [Sfr + 296, Sfr + 313) (S_R21, both arms): the journal, FRAC,
   our[], the turn's records, RBE, CUR and ctl_rt are kept (every other fact lies outside those shadow bytes). *)
Lemma w2b_latch_post : forall (cx : ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs) (regs3 R1 : bvmap 5 word)
    (mem3 m1 : word -> option byte) md3 md1 (b : nat),
  CBASE cx -> AJ cx (own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = own6 cx ->
  (forall cid pos, In (cid, pos) (own6 cx) -> fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) cid pos) ->
  B.ACtlCutP.FRAC B cx fr fr regs3 mem3 -> B.ACtlCutP.RBE cx fr regs3 mem3 ->
  B.ACtlCutP.RB cx fr b (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) (S b))
    (B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) (S b)) regs3 mem3 ->
  B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2 ->
  lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3 ->
  lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4 ->
  lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8 ->
  lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9 ->
  lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19 ->
  lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23 ->
  lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25 ->
  lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26 ->
  lib.Lib.Frame.munch [(B.AsanRT.shadow_addr fr + 296, B.AsanRT.shadow_addr fr + 313)] mem3 m1 ->
  lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 ->
  lib.Lib.Frame.stk B.Img0.rsegs m1 (B.AsanRT.shadow_addr fr + 296) (B.AsanRT.shadow_addr fr + 313) ->
  (forall x, Reusable.YA0n.w_H W3 x = true -> m1 x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md1 ->
  AJ cx (own6 cx) ly3 S3 W3 m1 md1 k /\ B.ACtlCutP.FRAC B cx fr fr R1 m1 /\ B.ACtlCutP.OURb cx fr m1 /\
  B.ACtlCutP.IDBr cx fr (B.Prog.SlotModel.RID (B.ACtlCut.c_in cx) (S b)) m1 /\
  B.ACtlCutP.FGBr cx fr (B.Prog.SlotModel.RFG (B.ACtlCut.c_in cx) (S b)) m1 /\
  B.ACtlCutP.RBE cx fr R1 m1 /\ B.ACtlRtC.ctl_rt_C B ly3 S3 m1 /\ B.ACtlCutP.CUR cx 7 R1.
Proof.
  intros cx fr k ly3 S3 W3 regs3 R1 mem3 m1 md3 md1 b HB HJ Hfrs Hfa HFRAC HRBE HRB Hrt
    P2 P3 P4 P8 P9 P19 P23 P25 P26 MU1 WM1 ST1 Hhid1 Hsbm1.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hstk : lib.Reusable.YM05.alloc_ceiling + 32768 <= B.ACtlCut.c_sp cx) by lia.
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HfrGT : 0x5fe000 <= fr).
  { rewrite <- EF. exact (w2b_frame_above_img ly3 S3 W3 mem3 md3 (B.ACtlCut.c_fpos cx) HAR Hin6). }
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  pose proof (w2b_sfr_apart fr ltac:(lia)) as Hap.
  assert (Happ' : fr + 4096 <= B.AsanRT.LOWMEM_END \/
                  (B.AsanRT.HIGHMEM_BEG <= fr /\ fr + 4096 <= B.AsanRT.APPMEM_END))
    by (unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  specialize (Hap Happ').
  assert (HapS : B.AsanRT.shadow_addr fr + 512 <= fr \/ fr + 4096 <= B.AsanRT.shadow_addr fr)
    by (unfold B.AsanRT.shadow_addr; lia).
  clear Hap. rename HapS into Hap.
  assert (Hsh_lo : forall a, 0 <= a < 2 ^ 47 -> B.AsanRT.shadow_addr a + 4096 < sp - 8192).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Ha Hceil Hstk HS4096.
    Z.div_mod_to_equations. lia. }
  assert (Hshf0 : B.AsanRT.shadow_addr fr + 4096 < sp - 8192) by (apply Hsh_lo; lia).
  assert (HSb : 2147450880 <= B.AsanRT.shadow_addr fr)
    by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hfr4k; Z.div_mod_to_equations; lia).
  set (WL := [(B.AsanRT.shadow_addr fr + 296, B.AsanRT.shadow_addr fr + 313)]) in MU1.
  assert (HoWL : forall x, (x < B.AsanRT.shadow_addr fr + 296 \/ B.AsanRT.shadow_addr fr + 313 <= x) ->
                   lib.Lib.Frame.outside WL x)
    by (intros x Hx; unfold WL; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (OFr : forall x, fr <= x < fr + 4096 -> lib.Lib.Frame.outside WL x).
  { intros x Hx. apply HoWL. destruct Hap as [Hap|Hap]; [right | left]; lia. }
  assert (OStk : forall x, sp <= x -> lib.Lib.Frame.outside WL x) by (intros x Hx; apply HoWL; right; lia).
  assert (OImg : forall x, x < 0x5fe000 -> lib.Lib.Frame.outside WL x) by (intros x Hx; apply HoWL; left; lia).
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> lib.Lib.Frame.outside WL x) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m1 a bs)
    by (intros a bs Hx Hb; exact (B.Prog.RcAsanFPLib.fl_bytes WL mem3 m1 a bs Hb MU1 Hx)).
  (* the journal *)
  assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 m1 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := m1) (mdc' := md1)
      (Wr := fun a => B.AsanRT.shadow_addr fr + 296 <= a < B.AsanRT.shadow_addr fr + 313); [exact HJ | | | | | ].
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1 x); [reflexivity|]. apply HoWL. lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:Ex; [exact Hx|].
      destruct (B.Prog.Seg.RHelp.rh_out_dec WL (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU1 x Ho); exact Hx|].
      assert (Hin : B.AsanRT.shadow_addr fr + 296 <= bv_unsigned x < B.AsanRT.shadow_addr fr + 313).
      { destruct (Z_lt_dec (bv_unsigned x) (B.AsanRT.shadow_addr fr + 296)); [exfalso; apply Ho, HoWL; lia|].
        destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 313) (bv_unsigned x)); [exfalso; apply Ho, HoWL; lia|].
        lia. }
      assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; lia).
      assert (Hw0 : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; apply Hx; reflexivity]. }
      pose proof (WM1 x Hw0) as Hw. unfold wview in Hw.
      rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
      destruct (m1 x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
    - exact Hhid1.
    - exact Hsbm1.
    - intros a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx).
      split; [cbn; left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia. }
  split; [exact HJ1|].
  split.
  { apply (w2b_FRAC_keep_sh cx fr regs3 R1 mem3 m1 WL HFRAC MU1 P2 P3 P4 P8 P9 P19 P26).
    - intros A' x HA' HA'r Hx. pose proof (w2b_rg9_ge regs3 A A' Hr9 HA' ltac:(lia) ltac:(lia)) as EA.
      apply OStk. lia.
    - intros x Hx. apply OFr. lia.
    - intros x Hx. destruct (B.Prog.Seg.RHelp.rh_out_dec WL x) as [Ho|Ho]; [left; exact Ho | right].
      destruct ST1 as (_ & _ & HST). apply (HST x).
      destruct (Z_lt_dec x (B.AsanRT.shadow_addr fr + 296)); [exfalso; apply Ho, HoWL; lia|].
      destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 313) x); [exfalso; apply Ho, HoWL; lia|]. lia.
    - intros x Hx. apply OStk. lia.
    - intros x Hx. apply OFr. lia. }
  pose proof HRB as (_ & HCUR & HOUR & _ & HIDB & HFGB).
  split.
  { unfold B.ACtlCutP.OURb in *. apply KB; [|exact HOUR]. rewrite B.Prog.SlotModel.OUR_length.
    intros x Hx. apply OFr. lia. }
  split.
  { unfold B.ACtlCutP.IDBr in *. apply KB; [|exact HIDB]. rewrite B.Prog.Seg.RtmB.rb_RID_len.
    intros x Hx. apply OFr. lia. }
  split.
  { unfold B.ACtlCutP.FGBr in *. apply KB; [|exact HFGB].
    assert (Hb6 : (b <= 6)%nat) by exact (proj1 HRB).
    rewrite (B.Prog.Seg.RtmB.rb_RFG_len (B.ACtlCut.c_in cx) (S b) ltac:(lia)). intros x Hx. apply OFr. lia. }
  pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 m1 md1 k HB HJ1) as Hrt1.
  pose proof Hrt as (_ & _ & _ & HRO). pose proof Hrt1 as (_ & _ & _ & HRO1).
  split.
  { apply (w2b_RBE_transfer cx fr regs3 R1 mem3 m1 HRBE).
    - intros off v Ho0 Ho1 Hs.
      exact (B.Prog.Seg.RHelp.rh_spill_keep regs3 R1 mem3 m1 WL A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1 P9 MU1
               (fun x Hx => OStk x ltac:(lia))).
    - intros p n Hpn Ha. apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 WL p n Ha MU1).
      intros i0 Hi0. apply HoWL. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      clear - Hpn Hi0 Hfr32. destruct Hpn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        Z.div_mod_to_equations; lia.
    - intros a bs Hr Hb. apply KB; [|exact Hb]. intros x Hx. apply OImg.
      assert (HBA : B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) <= 0x5fe000)
        by (apply Z.leb_le; vm_compute; reflexivity).
      unfold B.ACtlCutP.SM.CAT, B.ACtlCutP.SM.CAT_ROW, B.ACtlCutP.SM.CAT_N in Hr. lia.
    - intros a bs Hr Hb. exact (w2b_ro_bytes mem3 m1 a bs HRO HRO1 Hr Hb).
    - intros Hh Hr. pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                         _ & _ & _ & HNM & _).
      destruct (HNM (conj Hh Hr)) as (_ & _ & Haddr & _).
      apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 WL _ _ Haddr MU1).
      intros i0 Hi0. pose proof (w2b_name_img (B.ACtlCut.c_in cx) Hh) as (Hn0 & Hn1).
      apply HoWL. left. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Hi0 Hn0 Hn1 HfrGT.
      Z.div_mod_to_equations. lia. }
  split; [exact Hrt1|].
  destruct HCUR as (Hc & Hc23 & Hc25). split; [exact Hc|]. unfold B.ACtlCut.rgv in *.
  split; [rewrite P23; exact Hc23 | rewrite P25; exact Hc25].
Qed.

(* B81aa0_at b (Inv_B81aa0_at SIv:1956) -> B816ec_at (S b) (used while b < 6), B81c58, B81ca8.  S_R21 (Slot.v:103; seg_R21
   R21.v:661).  The path first runs 0x81aa0 .. 0x81ac0 (the eight frame-shadow stores at s3 + 296 .. s3 + 312, the
   turn's shadow re-poison) and then the latch at 0x81ac4 (owner's form, Slot.v:101-105):
   - b < 6 (s6 = b, 0 <= b <= 5): R21F.r21_latch_next_F (R21F.v:112; 0x81aa0 -> 0x816ec; source R21.v:221: s6 = b
     (rgv 22 b), rw_cells (s3 + 296) [CB 17 junk] and stk (s3 + 296) (s3 + 313): frame shadow, V5; post s6 = b + 1,
     munch of
     those 17 shadow bytes) -> C_B816ec_at at turn S b: Permutation kept (no allocator event; the journal by
     ajournal_exec over the frame-shadow write set), RS at S b = RB (S b) (RID (S b)) (RFG (S b)) (the body's RB at
     turn S b, b + 1 <= 6, rgv 22 (b + 1)), RBE, rgv 21 36, R6X cx (S b) (R6X's turn enters only through the
     (b = 5 \/ b = 6) guard of the name bytes, which RBE carries unconditionally), rgv 27 32; k <= 2b + 2 = 2 (S b).
   - b = 6: R21F.r21_latch_last_F (R21F.v:146; 0x81aa0 -> 0x81b00; R21.v:253) then R21F.r21_tail_pre_F (R21F.v:342;
     0x81b00 -> strcmp entry, ra = 0x81c58; R21.v:330) on h <> 0, and H_strcmp -> 0x81c58 = C_B81c58, the raw facts
     there by ctl_post_strcmp
     (k <= 14 = 2 * 6 + 2); on h = 0 the tail's arm to 0x81c60, then R21F.r21_p1_pre_F (R21F.v:269; 0x81c60 ->
     set_shadow_f8 entry 0x55144, ra = 0x81ca8; R21.v:557 / :475:
     s1 = A, AC.GT <= s3, s3 + 392 <= A, Q = [A + 8] = Sfr fr + 68 (RBE spill 8), the 19 shadow bytes at s3 + 272,
     stk (s3) (s3 + 392)) and ASF8 (q = Sfr fr + 68, n = 187: inside the fake frame's shadow [Sfr fr, Sfr fr + 3136 /
     8); ecall_pre from the journal) -> 0x81ca8 = C_B81ca8, the raw facts there (the 187 bytes 0xf8 and the rest kept
     at visible addresses) by ctl_post_set_shadow.  The r21_tail_evt premises (R21.v:335-360) come from the
     final identity record at turn 7 ([A + 144] = fr + 2176, IDBr (S 6): its bytes 2, 20, 36 and the version fields)
     and the catalogue row ([A + 272] = mrow, RBE bytes_at mrow rt_mb, its shadow zero: V6), i.e. SlotModel's RID 7
     facts; these refute the abort jumps 0x81b0c, 0x81b48, 0x81b58, 0x81b88, 0x81bb8, 0x81be8, 0x81c1c, and
     [A + 32] = 0 (RBE) refutes TRAP row 8 0x81b18.  The jump 0x81c5c after strcmp's return is S_P1's (W3).
   - b >= 7: the body's (b <= 6)%nat (RB) is false: vacuous (the top supplies the head at 7 by vac_B816ec). *)
Lemma seg_R21 : forall POST (b : nat),
  CFb POST C816ec (S b) -> CF POST C81c58 -> CF POST C81ca8 -> CFb POST C81aa0 b.
Proof.
  intros POST b HY HY58 HYa8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B81aa0_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (Hperm & HFRAC & Hn & Hb6 & H22 & HOUR & HRBE & H21 & HRB & H27).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _ & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  assert (Hl392 : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  unfold B.ACtlCutP.Sfr in Hsh, Hr19.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  pose proof Hastk as (Hsp0m & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2, Hwin.
  assert (Hstk : lib.Reusable.YM05.alloc_ceiling + 32768 <= B.ACtlCut.c_sp cx) by lia.
  pose proof HB as ((Hafn & _ & _ & _ & _ & Hnlen & _) & _). pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  assert (Hin6 : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite Hfrs. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (Efr : fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { apply Hfa. unfold B.ACtlCut.own6. left. reflexivity. }
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF.
    reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HfrGT : 0x5fe000 <= fr).
  { rewrite <- EF. exact (w2b_frame_above_img ly3 S3 W3 mem3 md3 (B.ACtlCut.c_fpos cx) HAR Hin6). }
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  destruct (Reusable.YCbq.frames_bounds _ _ LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4k & Hfrce & Hfrapp).
  rewrite EF in Hfrb, Hfrsh, Hfr4k, Hfrce, Hfrapp. rewrite HFB6 in Hfrb, Hfrsh, Hfrce, Hfrapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfrapp.
  change (4096 / 8) with 512 in Hfrsh.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hfrsh.
  assert (Pfrsh : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
                    Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\ exists bb, mem3 (Z_to_bv 64 a) = Some bb).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
    pose proof (proj1 (Hfrsh (a - (2147450880 + fr / 8)) ltac:(lia))) as Hp.
    replace (2147450880 + fr / 8 + (a - (2147450880 + fr / 8))) with a in Hp by lia. exact Hp. }
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfrb a Ha)))).
  assert (Vstk : forall a, B.ACtlCut.c_sp cx - 32768 <= a < B.ACtlCut.c_sp cx ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Hwin a Ha))).
  pose proof (w2b_sfr_apart fr ltac:(lia)) as Hap.
  assert (Happ' : fr + 4096 <= B.AsanRT.LOWMEM_END \/
                  (B.AsanRT.HIGHMEM_BEG <= fr /\ fr + 4096 <= B.AsanRT.APPMEM_END))
    by (unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia).
  specialize (Hap Happ').
  assert (HapS : B.AsanRT.shadow_addr fr + 512 <= fr \/ fr + 4096 <= B.AsanRT.shadow_addr fr)
    by (unfold B.AsanRT.shadow_addr; lia).
  clear Hap. rename HapS into Hap.
  assert (Hsh_lo : forall a, 0 <= a < 2 ^ 47 -> B.AsanRT.shadow_addr a + 4096 < sp - 8192).
  { intros a Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. clear - Ha Hceil Hstk HS4096.
    Z.div_mod_to_equations. lia. }
  assert (Hshf0 : B.AsanRT.shadow_addr fr + 4096 < sp - 8192) by (apply Hsh_lo; lia).
  assert (HSb : 2147450880 <= B.AsanRT.shadow_addr fr /\ B.AsanRT.shadow_addr fr + 512 <= B.AsanRT.HIGHMEM_BEG)
    by (unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.HIGHMEM_BEG; clear - Hfr4k Hfrce Hceil;
        Z.div_mod_to_equations; lia).
  destruct (img_vis_W W3) as (_ & _ & Vimg).
  assert (Es3 : bv_unsigned (Sem.reg_get regs3 19) = B.AsanRT.shadow_addr fr).
  { assert (E19 : Sem.reg_get regs3 19 = Z_to_bv 64 (B.AsanRT.shadow_addr fr)) by exact Hr19.
    rewrite E19. apply lib.Lib.MState.unsigned_lit. unfold B.AsanRT.HIGHMEM_BEG in HSb. lia. }
  (* the latch's 17 frame-shadow bytes *)
  pose proof (B.Prog.Seg.RHelp.rh_ba_sub mem3 (B.AsanRT.shadow_addr fr) sh 296 17 Hsh ltac:(rewrite Hl392; lia))
    as Hj.
  replace (B.AsanRT.shadow_addr fr + Z.of_nat 296) with (B.AsanRT.shadow_addr fr + 296) in Hj by lia.
  assert (RWL : lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (B.AsanRT.shadow_addr fr + 296)
                  [lib.Lib.Cells.CB 17 (firstn 17 (skipn 296 sh))]).
  { unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. split; [split|].
    + cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [|exact I].
      rewrite length_firstn, length_skipn, Hl392. reflexivity.
    + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hj.
    + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. unfold B.AsanRT.HIGHMEM_BEG in HSb.
      split; [lia|]. split; [lia|].
      intros i0 Hi0. destruct (proj2 (Pfrsh (B.AsanRT.shadow_addr fr + 296 + i0) ltac:(lia))) as (bb & Hbb).
      unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate. }
  assert (STL : lib.Lib.Frame.stk B.Img0.rsegs mem3 (B.AsanRT.shadow_addr fr + 296) (B.AsanRT.shadow_addr fr + 313)).
  { unfold B.AsanRT.HIGHMEM_BEG in HSb. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (proj2 (Pfrsh a ltac:(lia))) as (bb & Hbb).
    unfold lib.Lib.Mem.wa, wview, lib.Lib.Mem.mrd. rewrite Hbb. split; [discriminate | exists bb; reflexivity]. }
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  destruct (le_lt_dec b 5) as [Hb5|Hb5].
  - (* b <= 5: the latch back to the round-trip head at turn S b (R21F.r21_latch_next_F) *)
    eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    { apply B.ProgBridge.fevt_of_evtF.
      eapply (R21F.r21_latch_next_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (bz := Z.of_nat b)
        (junk := firstn 17 (skipn 296 sh)).
      all: try rewrite Es3.
      - exact H22.
      - lia.
      - exact RWL.
      - exact STL.
      - apply B.ProgBridge.rng_of_visible, w2b_rv; [unfold B.AsanRT.HIGHMEM_BEG in HSb; lia
                                                   | unfold B.AsanRT.HIGHMEM_BEG in HSb; lia |].
        intros a Ha. exact (proj1 (Pfrsh a ltac:(lia))). }
    { exact (B.ProgBridge.fp_avoids_RNG_W _). }
    intros ms1 md1 (R1 & m1 & -> & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 &
                    P27 & MU1 & WM1 & ST1) Hhid1 Hsbm1.
    rewrite Es3 in MU1, ST1.
    apply w2b_of_MS.
    destruct (w2b_latch_post cx fr k ly3 S3 W3 regs3 R1 mem3 m1 md3 md1 b HB HJ Hfrs Hfa HFRAC HRBE HRB Hrt
                P2 P3 P4 P8 P9 P19 P23 P25 P26 MU1 WM1 ST1
                ltac:(intros x Hx; pose proof (Hhid1 x Hx) as X; exact X) Hsbm1)
      as (HJ1 & HFRAC1 & HOUR1 & HIDB1 & HFGB1 & HRBE1 & Hrt1 & HCUR1).
    refine (HY cx [Z.of_nat (S b)] fr k ly3 S3 W3 R1 m1 md1 HB HJ1 Hfrs Hfa _ _ Hrt1).
    + cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B816ec_at]. unfold B.ACtlCutP.ixn. cbn [nth].
      rewrite Nat2Z.id. lia.
    + unfold B.ACtlCutP.C_B816ec_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
      cbv zeta.
      assert (Eb' : B.ACtlCutP.ixn 0 [Z.of_nat (S b)] = S b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
      rewrite Eb'.
      split; [exact Hperm|].
      split; [exact HFRAC1|].
      split; [exact Hn|].
      split.
      { unfold B.ACtlCutP.RS, B.ACtlCutP.RB. split; [lia|]. split; [exact HCUR1|]. split; [exact HOUR1|].
        split; [unfold B.ACtlCut.rgv; etransitivity; [exact P22 | f_equal; lia]|].
        split; [exact HIDB1 | exact HFGB1]. }
      split; [exact HRBE1|].
      split; [unfold B.ACtlCut.rgv in *; etransitivity; [exact P21 | exact H21]|].
      split; [exact (w2b_R6X_of_RBE cx (S b) fr R1 m1 HRBE1)|].
      split.
      { pose proof HRBE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & HNM1 & _).
        exact HNM1. }
      unfold B.ACtlCut.rgv in *; etransitivity; [exact P27 | exact H27].
  - (* b = 6: the latch's exit to 0x81b00 (R21F.r21_latch_last_F), then the tail *)
    assert (Eb6 : b = 6%nat) by lia. subst b.
    eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    { apply B.ProgBridge.fevt_of_evtF.
      eapply (R21F.r21_latch_last_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
        (fun ms => exists (R : bvmap 5 word) (m' : word -> option byte),
           ms = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81b00) lib.Reusable.YK11.fp_csr None m'
                  (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
           lib.Reusable.YK11.getr R 1 = lib.Reusable.YK11.getr regs3 1 /\
           lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
           lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
           lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
           lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
           lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
           lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
           lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
           lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
           lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21 /\
           lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
           lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24 /\
           lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
           lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
           lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27 /\
           lib.Lib.Frame.munch [(B.AsanRT.shadow_addr fr + 296, B.AsanRT.shadow_addr fr + 313)] mem3 m' /\
           lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' /\
           lib.Lib.Frame.stk B.Img0.rsegs m' (B.AsanRT.shadow_addr fr + 296) (B.AsanRT.shadow_addr fr + 313))
        ) with (junk := firstn 17 (skipn 296 sh)).
      all: try rewrite Es3.
      - exact H22.
      - exact RWL.
      - exact STL.
      - apply B.ProgBridge.rng_of_visible, w2b_rv; [unfold B.AsanRT.HIGHMEM_BEG in HSb; lia
                                                   | unfold B.AsanRT.HIGHMEM_BEG in HSb; lia |].
        intros a Ha. exact (proj1 (Pfrsh a ltac:(lia))).
      - intros a0' s6' m' MU WM ST. try rewrite Es3 in MU. try rewrite Es3 in ST.
        apply Lib.ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
        do 15 (split; [reflexivity|]). split; [exact MU|]. split; [exact WM | exact ST]. }
    { exact (B.ProgBridge.fp_avoids_RNG_W _). }
    intros ms1 md1 (R1 & m1 & -> & E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E23 & E24 & E25 & E26 & E27 &
                    MU1 & WM1 & ST1) Hhid1 Hsbm1.
    apply w2b_of_MS.
    destruct (w2b_latch_post cx fr k ly3 S3 W3 regs3 R1 mem3 m1 md3 md1 6 HB HJ Hfrs Hfa HFRAC HRBE HRB Hrt
                E2 E3 E4 E8 E9 E19 E23 E25 E26 MU1 WM1 ST1
                ltac:(intros x Hx; pose proof (Hhid1 x Hx) as X; exact X) Hsbm1)
      as (HJ1 & HFRAC1 & HOUR1 & HIDB1 & HFGB1 & HRBE1 & Hrt1 & HCUR1).
    apply (w2b_tail_81b00 POST cx fr k ly3 S3 W3 R1 m1 md1 HY58 HB HJ1 ltac:(lia) Hfrs Hfa Hperm HFRAC1 Hn
             HCUR1 HOUR1 HIDB1 HRBE1 Hrt1).
    (* has_identity_record = 0: 0x81c60 .. set_shadow_f8 (R21F.r21_p1_pre_F on MemNorm.normalize), ASF8 *)
    intros Eh0 R md2 HJ2 F10 F1 F2 F3 F4 F8 F9 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27.
    assert (G2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by (rewrite F2; exact E2).
    assert (G3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by (rewrite F3; exact E3).
    assert (G4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by (rewrite F4; exact E4).
    assert (G8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by (rewrite F8; exact E8).
    assert (G9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite F9; exact E9).
    assert (G19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite F19; exact E19).
    assert (G23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by (rewrite F23; exact E23).
    assert (G25 : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by (rewrite F25; exact E25).
    assert (G26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by (rewrite F26; exact E26).
    assert (Es3R : bv_unsigned (Sem.reg_get R 19) = B.AsanRT.shadow_addr fr).
    { assert (E : Sem.reg_get R 19 = Sem.reg_get regs3 19) by exact G19. rewrite E. exact Es3. }
    pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 m1 md2 k HB HJ2) as Hrt2.
    pose proof Hrt2 as (HAC1 & HSW1c & HSW1i & HRO1).
    pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m1 HRO1) as HMR1.
    set (WL := [(B.AsanRT.shadow_addr fr + 296, B.AsanRT.shadow_addr fr + 313)]) in MU1.
    assert (HoWL : forall x, (x < B.AsanRT.shadow_addr fr + 296 \/ B.AsanRT.shadow_addr fr + 313 <= x) ->
                     lib.Lib.Frame.outside WL x)
      by (intros x Hx; unfold WL; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
    (* the frame shadow at m1, present and writable *)
    assert (Hpm1 : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 392 ->
                     wview B.Img0.rsegs m1 (Z_to_bv 64 a) <> None /\
                     exists bb, lib.Lib.Mem.mrd B.Img0.rsegs m1 (Z_to_bv 64 a) = Some bb).
    { intros a Ha. destruct (proj2 (Pfrsh a ltac:(lia))) as (bb & Hbb).
      assert (Hw3 : wview B.Img0.rsegs mem3 (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hbb; discriminate).
      split; [exact (WM1 _ Hw3)|].
      destruct (B.Prog.Seg.RHelp.rh_out_dec WL a) as [Ho|Ho].
      - exists bb. unfold lib.Lib.Mem.mrd. rewrite (MU1 (Z_to_bv 64 a)); [rewrite Hbb; reflexivity|].
        rewrite lib.Lib.MState.unsigned_lit by (unfold B.AsanRT.HIGHMEM_BEG in HSb; lia). exact Ho.
      - destruct ST1 as (_ & _ & HST).
        assert (Hin : B.AsanRT.shadow_addr fr + 296 <= a < B.AsanRT.shadow_addr fr + 313).
        { destruct (Z_lt_dec a (B.AsanRT.shadow_addr fr + 296)); [exfalso; apply Ho, HoWL; lia|].
          destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 313) a); [exfalso; apply Ho, HoWL; lia|]. lia. }
        exact (proj2 (HST a Hin)). }
    assert (HSbl : B.AsanRT.shadow_addr fr + 512 <= 2 ^ 64) by (unfold B.AsanRT.HIGHMEM_BEG in HSb; lia).
    pose proof HFRAC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                          _ & _ & (sh1 & Hsh1 & Hshl1) & _ & _).
    unfold B.ACtlCutP.Sfr in Hsh1.
    assert (Hl1 : length sh1 = 392%nat) by (rewrite Hshl1; reflexivity).
    pose proof (B.Prog.Seg.RHelp.rh_ba_sub m1 (B.AsanRT.shadow_addr fr) sh1 272 19 Hsh1 ltac:(rewrite Hl1; lia))
      as Hj1.
    replace (B.AsanRT.shadow_addr fr + Z.of_nat 272) with (B.AsanRT.shadow_addr fr + 272) in Hj1 by lia.
    assert (RW19 : lib.Lib.Step.rw_cells B.Img0.rsegs m1 (B.AsanRT.shadow_addr fr + 272)
                     [lib.Lib.Cells.CB 19 (firstn 19 (skipn 272 sh1))]).
    { unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. split; [split|].
      + cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [|exact I].
        rewrite length_firstn, length_skipn, Hl1. reflexivity.
      + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hj1.
      + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. split; [lia|]. split; [lia|].
        intros i0 Hi0. unfold lib.Lib.Mem.wa. exact (proj1 (Hpm1 (B.AsanRT.shadow_addr fr + 272 + i0) ltac:(lia))). }
    assert (STK392 : lib.Lib.Frame.stk B.Img0.rsegs m1 (B.AsanRT.shadow_addr fr) (B.AsanRT.shadow_addr fr + 392)).
    { split; [lia|]. split; [lia|]. intros a Ha. unfold lib.Lib.Mem.wa. exact (Hpm1 a Ha). }
    pose proof HRBE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S8 & _).
    assert (Hr9R : B.ACtlCut.rgv R 9 A) by (unfold B.ACtlCut.rgv in *; rewrite G9; exact Hr9).
    assert (Hr9R1 : B.ACtlCut.rgv R1 9 A) by (unfold B.ACtlCut.rgv in *; rewrite E9; exact Hr9).
    pose proof (B.Prog.Seg.RHelp.rh_spill_at R1 m1 A 8 _ S8 Hr9R1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Q8.
    unfold B.ACtlCutP.q64 in Q8.
    assert (Hnoimg : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 392 ->
                       ~ (0x10000 <= a < 0x5fe000)) by (intros a Ha; lia).
    (* the run 0x81c60 -> set_shadow_f8 (R21F.r21_p1_pre_F) on MemNorm.normalize m1, lifted *)
    apply w2b_to_MS.
    apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of R) R _ _ _ _ _ _ _ _);
      [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv R))].
    unfold Lib.Regs6ss.mkR_of.
    eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md2 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    { apply B.ProgBridge.fevt_of_evtF. apply B.MemNormF.evtF_normalize_ro; [exact HRO1|].
      eapply (R21F.r21_p1_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (A := A) (Q := B.AsanRT.shadow_addr fr + 68) (junk := firstn 19 (skipn 272 sh1)).
      all: try rewrite Es3R.
      - exact Hr9R.
      - unfold B.Contract.GT. lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - intros i Hi. unfold B.AsanRT.in_shadow, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG.
        destruct Happ' as [Hl|Hh]; unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in *;
          [left; clear - Hi Hl Hfr32 HfrGT; Z.div_mod_to_equations; lia
          | right; clear - Hi Hh Hfr32 HfrGT; Z.div_mod_to_equations; lia].
      - apply (w2b_rwc_rel m1 _ _ _ HMR1 RW19). cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add].
        intros a Ha. apply Hnoimg. lia.
      - apply (w2b_stk_rel m1 _ _ _ HMR1 STK392). exact Hnoimg.
      - exact (proj1 (B.MemNorm.bytes_at_rel B.Img0.rsegs m1 _ _ _ HMR1) Q8).
      - exact (B.MemNorm.mem_inv_normalize _ m1).
      - exact (w2b_cells_rel m1 _ HMR1 HAC1).
      - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia |].
        intros a Ha. exact (proj1 (Pfrsh a ltac:(lia))).
      - apply B.ProgBridge.rng_of_visible, w2b_rv; [lia | lia | intros a Ha; apply Vstk; lia]. }
    { exact (B.ProgBridge.fp_avoids_RNG_W _). }
    intros ms3 md3' (s0 & HQ & Hrel & Hros) Hhid3 Hsbm3.
    destruct HQ as (R2 & m2n & junkQ & -> & H1' & H10' & H11' & H2' & H3' & H4' & H8' & H9' & H19' & H23' & H24' &
                    H25' & H26' & MUn & WMn & STn & RWQn & HACn & HMIn).
    destruct ms3 as [r3 f3 pc3 sv3 rv3 fc3 mem2 rom3].
    destruct Hrel as (Er & Ef & Epc & Esv & Erv & Efc & Erom & HMR2).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem lib.Lib.MState.MS]
      in Er, Ef, Epc, Esv, Erv, Efc, Erom, HMR2, Hros, Hhid3.
    subst r3 f3 pc3 sv3 rv3 fc3 rom3.
    rewrite Es3R in MUn, STn.
    apply w2b_of_MS.
    set (WP := [(B.AsanRT.shadow_addr fr, B.AsanRT.shadow_addr fr + 291)]) in MUn.
    pose proof (B.MemNorm.munch_rel B.Img0.rsegs WP m1 _ mem2 m2n HMR1 HMR2 Hros MUn) as MU12.
    pose proof (w2b_wmono_rel m1 _ mem2 m2n HMR1 HMR2 Hros WMn) as WM12.
    assert (HoWP : forall x, (x < B.AsanRT.shadow_addr fr \/ B.AsanRT.shadow_addr fr + 291 <= x) ->
                     lib.Lib.Frame.outside WP x)
      by (intros x Hx; unfold WP; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
    (* the registers at the set_shadow entry *)
    assert (K2 : lib.Reusable.YK11.getr R2 2 = lib.Reusable.YK11.getr regs3 2) by (etransitivity; [exact H2' | exact G2]).
    assert (K3 : lib.Reusable.YK11.getr R2 3 = lib.Reusable.YK11.getr regs3 3) by (etransitivity; [exact H3' | exact G3]).
    assert (K4 : lib.Reusable.YK11.getr R2 4 = lib.Reusable.YK11.getr regs3 4) by (etransitivity; [exact H4' | exact G4]).
    assert (K8 : lib.Reusable.YK11.getr R2 8 = lib.Reusable.YK11.getr regs3 8) by (etransitivity; [exact H8' | exact G8]).
    assert (K9 : lib.Reusable.YK11.getr R2 9 = lib.Reusable.YK11.getr regs3 9) by (etransitivity; [exact H9' | exact G9]).
    assert (K19 : lib.Reusable.YK11.getr R2 19 = lib.Reusable.YK11.getr regs3 19)
      by (etransitivity; [exact H19' | exact G19]).
    assert (K23 : lib.Reusable.YK11.getr R2 23 = lib.Reusable.YK11.getr regs3 23)
      by (etransitivity; [exact H23' | exact G23]).
    assert (K25 : lib.Reusable.YK11.getr R2 25 = lib.Reusable.YK11.getr regs3 25)
      by (etransitivity; [exact H25' | exact G25]).
    assert (K26 : lib.Reusable.YK11.getr R2 26 = lib.Reusable.YK11.getr regs3 26)
      by (etransitivity; [exact H26' | exact G26]).
    assert (K1 : lib.Reusable.YK11.getr R2 1 = Z_to_bv 64 0x81ca8) by exact H1'.
    assert (HspR2 : Reusable.YG0d.spZ R2 = sp) by (unfold Reusable.YG0d.spZ in *; rewrite K2; exact Hspz).
    (* the journal across the P1 suffix *)
    assert (HJ3 : AJ cx (own6 cx) ly3 S3 W3 mem2 md3' k).
    { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem2) (mdc' := md3')
        (Wr := fun a => B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 291); [exact HJ2 | | | | | ].
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU12 x); [reflexivity|]. apply HoWP. lia.
      - intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
        destruct (Reusable.YA0n.w_H W3 x) eqn:Ex; [exact Hx|].
        destruct (B.Prog.Seg.RHelp.rh_out_dec WP (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU12 x Ho); exact Hx|].
        assert (Hin : B.AsanRT.shadow_addr fr <= bv_unsigned x < B.AsanRT.shadow_addr fr + 291).
        { destruct (Z_lt_dec (bv_unsigned x) (B.AsanRT.shadow_addr fr)); [exfalso; apply Ho, HoWP; lia|].
          destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 291) (bv_unsigned x)); [exfalso; apply Ho, HoWP; lia|].
          lia. }
        assert (Hnx : ~ Reusable.YG0d.in_img segs (bv_unsigned x)) by (rewrite w2b_in_img; lia).
        assert (Hw0 : wview B.Img0.rsegs m1 x <> None).
        { unfold wview. destruct (m1 x); [discriminate | exfalso; apply Hx; reflexivity]. }
        pose proof (WM12 x Hw0) as Hw. unfold wview in Hw.
        rewrite (Reusable.YCbq.find_segment_none B.Img0.rsegs (bv_unsigned x) Hnx) in Hw.
        destruct (mem2 x); [intros E; discriminate E | exfalso; apply Hw; reflexivity].
      - intros x Hx. exact (Hhid3 x Hx).
      - exact Hsbm3.
      - intros a Ha. right; right; right. exists 6, (B.ACtlCut.c_fpos cx).
        split; [cbn; left; reflexivity|].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia. }
    (* the frame shadow at mem2, present *)
    assert (Hpm2 : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 392 ->
                     exists bb, lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 a) = Some bb).
    { intros a Ha. destruct STn as (_ & _ & HSTn). destruct (HSTn a Ha) as (_ & bb & Hbb).
      exists bb. rewrite (B.MemNorm.mrd_rel B.Img0.rsegs mem2 m2n _ HMR2). exact Hbb. }
    assert (Apm2 : forall a, B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 392 ->
                     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem2 a).
    { intros a Ha. split; [exact (proj1 (Pfrsh a ltac:(lia)))|].
      destruct STn as (_ & _ & HSTn). destruct (HSTn a Ha) as (Hw & _).
      rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs mem2 m2n _ HMR2) in Hw.
      - apply (w2b_present_of_wview mem2 (Z_to_bv 64 a)); [|exact Hw].
        rewrite lib.Lib.MState.unsigned_lit by lia. apply Hnoimg. exact Ha.
      - apply w2b_ro_false. rewrite lib.Lib.MState.unsigned_lit by lia. apply Hnoimg. exact Ha. }
    (* set_shadow_f8 on [Sfr fr + 68, + 187) (ASF8) *)
    assert (HPRE3 : Reusable.YG0d.ecall_pre segs B ly3 S3 W3 R2 mem2 md3').
    { eapply Reusable.YCbq.ecall_pre_at with (o := sp - B.ACtlCut.c_sp cx); [exact HJ3 | | | | | | |].
      - rewrite HspR2. lia.
      - clear - Hsp16 Hsp0m. Z.div_mod_to_equations. lia.
      - lia.
      - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
      - rewrite K1. apply lib.Reusable.YK0s.ret_ok_even. rewrite lib.Lib.MState.unsigned_lit by lia. reflexivity.
      - rewrite K3, Hr3. exact Hgp0.
      - rewrite K4. exact Hr4. }
    eapply Reusable.YA0n.SRr_bind.
    { apply (ASF8 ly3 S3 W3 R2 mem2 md3' 6 (B.ACtlCut.c_fpos cx) (B.AsanRT.shadow_addr fr + 68) 187 HPRE3 Hin6).
      - exact H10'.
      - exact H11'.
      - lia.
      - rewrite EF. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
        lia.
      - rewrite EF, HFB6. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr,
          B.AsanRT.ASAN_K. change (4096 / 8) with 512. lia. }
    cbv beta. intros W' c' Hwle (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsbm4 & Hval & Hout & Hwin4 & Hpres4).
    assert (Era : Reusable.YG0d.raZ R2 = 0x81ca8)
      by (unfold Reusable.YG0d.raZ; rewrite K1; apply lib.Lib.MState.unsigned_lit; lia).
    rewrite Era.
    pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT3).
    assert (HJ4 : AJ cx (own6 cx) ly3 S3 W3 mem4 md4 k).
    { eapply (Reusable.YCbq.ajournal_after_write segs B LAWS w2b_segs_low) with
        (Wr := fun a => B.AsanRT.shadow_addr fr + 68 <= a < B.AsanRT.shadow_addr fr + 68 + 187) (S' := S3)
        (own2 := own6 cx); [exact HJ3 | | | | | | | | | | ].
      - intros a Ha Hna. apply (Hout a Ha). exact Hna.
      - exact Hpres4.
      - exact Hsbm4.
      - intros a Ha. left. right; right; right. exists 6, (B.ACtlCut.c_fpos cx).
        split; [cbn; left; reflexivity|].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF, HFB6.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512.
        unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
      - exact HAR4.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact Hfrs3.
      - exact HQT3. }
    destruct (ctl_post_set_shadow W3 mem2 mem4 sp (B.AsanRT.shadow_addr fr + 68) 187 0xf8 ltac:(lia) ltac:(lia)
                ltac:(lia)) as (MV4 & _ & _).
    { intros a Ha. apply Apm2. lia. }
    { exact Hval. }
    { split; [|exact Hpres4]. intros a Ha Ho. apply Hout; [exact Ha|]. cbn [lib.Lib.Frame.outside] in Ho. lia. }
    set (WR := [(B.AsanRT.shadow_addr fr + 68, B.AsanRT.shadow_addr fr + 68 + 187);
                (sp - Reusable.YG0d.ESTACK, sp)]) in MV4.
    assert (HoWR : forall x, (x < B.AsanRT.shadow_addr fr + 68 \/ B.AsanRT.shadow_addr fr + 255 <= x) ->
                     (x < sp - 4096 \/ sp <= x) -> lib.Lib.Frame.outside WR x).
    { intros x H1 H2. unfold WR, Reusable.YG0d.ESTACK. cbn [lib.Lib.Frame.outside].
      split; [lia | split; [lia | exact I]]. }
    pose proof (w2b_ctlrt cx (own6 cx) ly3 S3 W3 mem4 md4 k HB HJ4) as Hrt4.
    (* the registers after set_shadow_f8 *)
    assert (GG : forall r : Z, Reusable.YG0d.acallee_saved r ->
              lib.Reusable.YK11.getr regs4 (Z_to_bv 5 r) = lib.Reusable.YK11.getr R2 (Z_to_bv 5 r)) by exact HP4.
    assert (L2 : lib.Reusable.YK11.getr regs4 2 = lib.Reusable.YK11.getr regs3 2)
      by (rewrite <- K2; apply (GG 2); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L3 : lib.Reusable.YK11.getr regs4 3 = lib.Reusable.YK11.getr regs3 3)
      by (rewrite <- K3; apply (GG 3); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L4 : lib.Reusable.YK11.getr regs4 4 = lib.Reusable.YK11.getr regs3 4)
      by (rewrite <- K4; apply (GG 4); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L8 : lib.Reusable.YK11.getr regs4 8 = lib.Reusable.YK11.getr regs3 8)
      by (rewrite <- K8; apply (GG 8); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L9 : lib.Reusable.YK11.getr regs4 9 = lib.Reusable.YK11.getr regs3 9)
      by (rewrite <- K9; apply (GG 9); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L19 : lib.Reusable.YK11.getr regs4 19 = lib.Reusable.YK11.getr regs3 19)
      by (rewrite <- K19; apply (GG 19); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L23 : lib.Reusable.YK11.getr regs4 23 = lib.Reusable.YK11.getr regs3 23)
      by (rewrite <- K23; apply (GG 23); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L25 : lib.Reusable.YK11.getr regs4 25 = lib.Reusable.YK11.getr regs3 25)
      by (rewrite <- K25; apply (GG 25); unfold Reusable.YG0d.acallee_saved; lia).
    assert (L26 : lib.Reusable.YK11.getr regs4 26 = lib.Reusable.YK11.getr regs3 26)
      by (rewrite <- K26; apply (GG 26); unfold Reusable.YG0d.acallee_saved; lia).
    (* bytes from mem3 to mem4 outside every write set *)
    assert (KB4 : forall a bs,
              (forall x, a <= x < a + Z.of_nat (length bs) ->
                 Reusable.YA0n.w_H W3 (Z_to_bv 64 x) = false /\
                 (sp <= x \/ x < B.AsanRT.shadow_addr fr \/ B.AsanRT.shadow_addr fr + 392 <= x) /\
                 (x < sp - 4096 \/ sp <= x)) ->
              lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem4 a bs).
    { intros a bs HX Hb.
      apply (w2b_bytes_mv _ WR mem2 mem4 a bs MV4).
      - intros x Hx. destruct (HX x Hx) as (Hv & Ho1 & Ho2). split; [exact Hv|].
        apply HoWR; [|exact Ho2]. destruct Ho1 as [Ho1|[Ho1|Ho1]]; [right | left | right]; lia.
      - apply (B.Prog.RcAsanFPLib.fl_bytes WP m1 mem2 a bs); [|exact MU12|].
        + apply (B.Prog.RcAsanFPLib.fl_bytes WL mem3 m1 a bs Hb MU1). intros x Hx. apply HoWL.
          destruct (HX x Hx) as (_ & [Ho1|[Ho1|Ho1]] & _); [right | left | right]; lia.
        + intros x Hx. apply HoWP. destruct (HX x Hx) as (_ & [Ho1|[Ho1|Ho1]] & _); [right | left | right]; lia. }
    assert (KS4 : forall off v, 0 <= off -> off + 8 <= 448 ->
              B.ACtlCutP.spill regs3 mem3 off v -> B.ACtlCutP.spill regs4 mem4 off v).
    { intros off v Ho0 Ho1 Hs.
      pose proof (B.Prog.Seg.RHelp.rh_spill_at regs3 mem3 A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho0 Ho1) as Hq.
      exists A. split; [unfold B.ACtlCut.rgv in *; rewrite L9; exact Hr9|].
      unfold B.ACtlCutP.q64 in *. apply KB4; [|exact Hq]. rewrite lib.Lib.Mem.length_le8.
      intros x Hx. split; [apply Vstk; lia|]. split; [left; lia | right; lia]. }
    pose proof HRBE as (_ & _ & _ & S264 & _ & _ & S56 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S176 & S208 &
      S64 & _ & _ & _ & HOURa & _ & _ & _ & HPRA & S152 & _ & _ & S160).
    assert (Ec0 : B.Prog.SlotModel.c0 (B.ACtlCut.c_in cx) = 7).
    { destruct HCUR1 as (Hc0 & _). unfold B.Prog.SlotModel.c0, B.Prog.SlotModel.nlen. lia. }
    refine (HYa8 cx [] fr k ly3 S3 W3 regs4 mem4 md4 HB HJ4 Hfrs Hfa _ _ Hrt4).
    { cbn [B.ACtlCut.cut_kmax B.ACtlCutP.C_B81ca8]. lia. }
    unfold B.ACtlCutP.C_B81ca8. cbn [B.ACtlCut.cut_body].
    split; [exact Hperm|].
    split.
    { (* FRAC: across the P1 suffix (shadow written, present), then across set_shadow_f8 (visible) *)
      assert (HFRAC2 : B.ACtlCutP.FRAC B cx fr fr R2 mem2).
      { apply (w2b_FRAC_keep_sh cx fr R1 R2 m1 mem2 WP HFRAC1 MU12
                 (eq_trans K2 (eq_sym E2)) (eq_trans K3 (eq_sym E3)) (eq_trans K4 (eq_sym E4))
                 (eq_trans K8 (eq_sym E8)) (eq_trans K9 (eq_sym E9)) (eq_trans K19 (eq_sym E19))
                 (eq_trans K26 (eq_sym E26))).
        - intros A' x HA' HA'r Hx. apply HoWP. right.
          assert (HA'1 : B.ACtlCut.rgv R1 9 A') by exact HA'.
          pose proof (w2b_rg9_ge R1 A A' Hr9R1 HA'1 ltac:(lia) ltac:(lia)) as EA. lia.
        - intros x Hx. apply HoWP. destruct Hap as [Hap|Hap]; [right | left]; lia.
        - intros x Hx. right. exact (Hpm2 x ltac:(lia)).
        - intros x Hx. apply HoWP. right. lia.
        - intros x Hx. apply HoWP. destruct Hap as [Hap|Hap]; [right | left]; lia. }
      apply (w2b_FRAC_mv_sh cx fr R2 regs4 mem2 mem4 _ WR HFRAC2 MV4
               (eq_trans L2 (eq_sym K2)) (eq_trans L3 (eq_sym K3)) (eq_trans L4 (eq_sym K4))
               (eq_trans L8 (eq_sym K8)) (eq_trans L9 (eq_sym K9)) (eq_trans L19 (eq_sym K19))
               (eq_trans L26 (eq_sym K26))).
      - intros x Hx. rewrite HspR2 in Hx.
        destruct Hx as [Hx|Hx]; [split; [apply Vstk; lia | apply HoWR; right; lia] |].
        split; [apply Vfr; lia|]. apply HoWR; [destruct Hap as [Hap|Hap]; [right | left]; lia | left; lia].
      - intros x Hx. destruct (Z_lt_dec x (B.AsanRT.shadow_addr fr + 68)) as [Hl|Hl];
          [|destruct (Z_le_dec (B.AsanRT.shadow_addr fr + 255) x) as [Hr|Hr]].
        + destruct (Hpm2 x Hx) as (bb & Hbb). exists bb. unfold lib.Lib.Mem.wa.
          rewrite (MV4 (Z_to_bv 64 x)); [exact Hbb | exact (proj1 (Pfrsh x ltac:(lia)))|].
          rewrite lib.Lib.MState.unsigned_lit by lia. apply HoWR; [left; lia | left; lia].
        + destruct (Hpm2 x Hx) as (bb & Hbb). exists bb. unfold lib.Lib.Mem.wa.
          rewrite (MV4 (Z_to_bv 64 x)); [exact Hbb | exact (proj1 (Pfrsh x ltac:(lia)))|].
          rewrite lib.Lib.MState.unsigned_lit by lia. apply HoWR; [right; lia | left; lia].
        + pose proof (Hval (x - (B.AsanRT.shadow_addr fr + 68)) ltac:(lia)) as Hvx.
          replace (B.AsanRT.shadow_addr fr + 68 + (x - (B.AsanRT.shadow_addr fr + 68))) with x in Hvx by lia.
          rewrite (w2b_aview_vis _ mem4 x (proj1 (Pfrsh x ltac:(lia)))) in Hvx.
          unfold lib.Lib.Mem.wa in *. destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem4 (Z_to_bv 64 x)) as [bb|] eqn:E;
            [exists bb; reflexivity | cbn in Hvx; discriminate Hvx]. }
    split; [exact Hn|].
    split.
    { unfold B.ACtlCutP.OURb in *. apply KB4; [|exact HOUR]. rewrite B.Prog.SlotModel.OUR_length.
      intros x Hx. split; [apply Vfr; lia|]. split; [destruct Hap as [Hap|Hap]; [right; right | right; left]; lia|].
      left; lia. }
    split; [apply KS4; [lia | lia | exact S56]|].
    split.
    { unfold B.ACtlCutP.PRO. split.
      { unfold B.ACtlCutP.PRA in *.
        destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
        do 10 (split; [apply KS4; [lia | lia | assumption]|]). apply KS4; [lia | lia | assumption]. }
      split; [apply KS4; [lia | lia | exact S152]|].
      split; [apply KS4; [lia | lia | exact S264]|].
      split; [|apply KS4; [lia | lia | exact S160]].
      (* our[]'s shadow byte Sfr + 328 is outside every write set *)
      apply (w2b_addr_mv _ WR mem2 mem4 (fr + 2624) 6 MV4).
      - intros i Hi.
        assert (Hs : B.AsanRT.shadow_addr (fr + 2624 + i) = B.AsanRT.shadow_addr fr + 328).
        { unfold B.AsanRT.shadow_addr. clear - Hi Hfr32. Z.div_mod_to_equations. lia. }
        rewrite Hs. split; [exact (proj1 (Pfrsh (B.AsanRT.shadow_addr fr + 328) ltac:(lia)))|].
        apply HoWR; [right; lia | left; lia].
      - apply (B.Prog.Seg.RHelp.rh_addr_keep_rng m1 mem2 WP _ _); [|exact MU12|].
        + apply (B.Prog.Seg.RHelp.rh_addr_keep_rng mem3 m1 WL _ _ HOURa MU1).
          intros i Hi. apply HoWL. right. unfold B.AsanRT.shadow_addr. clear - Hi Hfr32.
          Z.div_mod_to_equations. lia.
        + intros i Hi. apply HoWP. right. unfold B.AsanRT.shadow_addr. clear - Hi Hfr32.
          Z.div_mod_to_equations. lia. }
    split; [apply KS4; [lia | lia | exact S176]|].
    split; [apply KS4; [lia | lia | exact S208]|].
    split; [apply KS4; [lia | lia | exact S64]|].
    split.
    { rewrite Ec0. destruct HCUR1 as (Hc0 & Hc23 & Hc25). split; [exact Hc0|]. unfold B.ACtlCut.rgv in *.
      split; [rewrite L23, <- E23; exact Hc23 | rewrite L25, <- E25; exact Hc25]. }
    exact (ctl_kind_name_addressable ly3 S3 W3 mem4 md4 HAR4).
Qed.

(* B81ac0_at b (Inv_B81ac0_at SIv:1969) -> B816ec_at (S b) (used while b < 6), B81c58, B81c60.  S_R21_a5c (Slot.v:108;
   seg_R21_a5c R21.v:1206); entered only by S_R7's n_b = 0 skip (k <= 2b, no block).
   - b < 6: R21F.r21_a5c_next_F (R21F.v:65; 0x81ac0 -> 0x816ec; R21.v:284: s6 = b, no memory write, m' = m) ->
     C_B816ec_at at S b:
     the body carries IDBr / FGBr at S b, CUR 7, OURb, RBE, R6X cx (S b), rgv 21 36, rgv 27 32 directly, so RS (S b)
     = RB (S b) (RID (S b)) (RFG (S b)) with rgv 22 (b + 1); k <= 2b <= 2 (S b).
   - b = 6: R21F.r21_a5c_last_F (R21F.v:89; 0x81ac0 -> 0x81b00; R21.v:307), then the tail as in B81aa0: h <> 0 ->
     strcmp -> C_B81c58 (raw facts by ctl_post_strcmp)
     (k <= 12 <= 14); h = 0 -> the cut 0x81c60 = C_B81c60 (k <= 12).  Traps / abort jumps as in B81aa0 (row 8 by RBE).
   - b >= 7: vacuous. *)
Lemma seg_R21_a5c : forall POST (b : nat),
  CFb POST C816ec (S b) -> CF POST C81c58 -> CF POST C81c60 -> CFb POST C81ac0 b.
Proof.
  intros POST b HY HY58 HY60 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfrs Hfa Hk Hbody Hrt.
  unfold B.ACtlCutP.C_B81ac0_at in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  cbn [B.ACtlCut.cut_own B.ACtlCut.cut_kmax B.ACtlCut.cut_body B.ACtlCut.cut_pc B.ACtlCut.ix_cut]
    in Hfrs, Hfa, Hk, Hbody, HJ |- *.
  destruct Hbody as [-> Hbody]. cbv zeta in Hbody.
  assert (Eb : B.ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  rewrite Eb in Hk, Hbody.
  destruct Hbody as (Hperm & HFRAC & Hn & Hb6 & H22 & HCUR & HOUR & HIDB & HFGB & HRBE & H21 & HR6X & H27).
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA448 & HS4096 & HSapp & _).
  unfold B.ACtlCutP.FRAME_BYTES in HfrA. unfold B.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstklo2 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Hceil & _).
  unfold Reusable.YCfn.LLVMF_STK in Hstklo2.
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM & _).
  apply w2b_to_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 _ _ _ _ _ _ _ _);
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  destruct (le_lt_dec b 5) as [Hb5|Hb5].
  - (* b <= 5: the latch back to the round-trip head at turn S b, memory unchanged (R21F.r21_a5c_next_F) *)
    eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    { apply B.ProgBridge.fevt_of_evtF.
      eapply (R21F.r21_a5c_next_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (bz := Z.of_nat b);
        [exact H22 | lia]. }
    { exact (B.ProgBridge.fp_avoids_RNG_W _). }
    intros ms1 md1 (R1 & m1 & -> & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 &
                    P27 & ->) Hhid1 Hsbm1.
    apply w2b_of_MS.
    assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem3 md1 k).
    { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem3) (mdc' := md1)
        (Wr := fun _ => False); [exact HJ | | | | | ].
      - intros x _. reflexivity.
      - intros x Hx. exact Hx.
      - intros x _. reflexivity.
      - exact Hsbm1.
      - intros a []. }
    refine (HY cx [Z.of_nat (S b)] fr k ly3 S3 W3 R1 mem3 md1 HB HJ1 Hfrs Hfa _ _ Hrt).
    + cbn [B.ACtlCut.cut_kmax B.ACtlCut.ix_cut B.ACtlCutP.C_B816ec_at]. unfold B.ACtlCutP.ixn. cbn [nth].
      rewrite Nat2Z.id. lia.
    + unfold B.ACtlCutP.C_B816ec_at. cbn [B.ACtlCut.cut_body B.ACtlCut.ix_cut]. split; [reflexivity|].
      cbv zeta.
      assert (Eb' : B.ACtlCutP.ixn 0 [Z.of_nat (S b)] = S b) by (unfold B.ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
      rewrite Eb'.
      split; [exact Hperm|].
      split.
      { apply (w2b_FRAC_keep cx fr regs3 R1 mem3 mem3 [] HFRAC (lib.Lib.Frame.munch_refl [] mem3)
                 P2 P3 P4 P8 P9 P19 P26); intros; exact I. }
      split; [exact Hn|].
      split.
      { unfold B.ACtlCutP.RS, B.ACtlCutP.RB. split; [lia|].
        split; [destruct HCUR as (Hc & Hc23 & Hc25); split; [exact Hc|]; unfold B.ACtlCut.rgv in *;
                split; [etransitivity; [exact P23 | exact Hc23] | etransitivity; [exact P25 | exact Hc25]]|].
        split; [exact HOUR|].
        split; [unfold B.ACtlCut.rgv; etransitivity; [exact P22 | f_equal; lia]|].
        split; [exact HIDB | exact HFGB]. }
      split.
      { apply (w2b_RBE_keep cx fr regs3 R1 mem3 mem3 [] A HRBE (lib.Lib.Frame.munch_refl [] mem3) Hr9
                 ltac:(lia) ltac:(lia) P9); intros; exact I. }
      split; [unfold B.ACtlCut.rgv in *; etransitivity; [exact P21 | exact H21]|].
      split; [exact HR6X|].
      split; [exact HNM|].
      unfold B.ACtlCut.rgv in *; etransitivity; [exact P27 | exact H27].
  - (* b = 6: the latch's exit to 0x81b00 (R21F.r21_a5c_last_F), then the tail *)
    assert (Eb6 : b = 6%nat) by lia. subst b.
    eapply (Reusable.YA0nR.SRr_fevt_hid segs w2b_wx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    { apply B.ProgBridge.fevt_of_evtF.
      eapply (R21F.r21_a5c_last_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
        (fun ms => exists R : bvmap 5 word,
           ms = lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81b00) lib.Reusable.YK11.fp_csr None mem3
                  (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
           lib.Reusable.YK11.getr R 1 = lib.Reusable.YK11.getr regs3 1 /\
           lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2 /\
           lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3 /\
           lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4 /\
           lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8 /\
           lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9 /\
           lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18 /\
           lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19 /\
           lib.Reusable.YK11.getr R 20 = lib.Reusable.YK11.getr regs3 20 /\
           lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21 /\
           lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23 /\
           lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24 /\
           lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25 /\
           lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26 /\
           lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27));
        [exact H22 |].
      intros a0' s6'. apply Lib.ExecF.evtF_done. eexists. split; [reflexivity|].
      repeat split; reflexivity. }
    { exact (B.ProgBridge.fp_avoids_RNG_W _). }
    intros ms1 md1 (R1 & -> & E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E23 & E24 & E25 & E26 & E27)
      Hhid1 Hsbm1.
    apply w2b_of_MS.
    assert (HJ1 : AJ cx (own6 cx) ly3 S3 W3 mem3 md1 k).
    { eapply (Reusable.YCbq.ajournal_exec segs B LAWS w2b_segs_low) with (memc' := mem3) (mdc' := md1)
        (Wr := fun _ => False); [exact HJ | | | | | ].
      - intros x _. reflexivity.
      - intros x Hx. exact Hx.
      - intros x Hx. pose proof (Hhid1 x Hx) as X. exact X.
      - exact Hsbm1.
      - intros a []. }
    assert (HRBE1 : B.ACtlCutP.RBE cx fr R1 mem3).
    { apply (w2b_RBE_keep cx fr regs3 R1 mem3 mem3 [] A HRBE (lib.Lib.Frame.munch_refl [] mem3) Hr9
               ltac:(lia) ltac:(lia) E9); intros; exact I. }
    assert (HFRAC1 : B.ACtlCutP.FRAC B cx fr fr R1 mem3).
    { apply (w2b_FRAC_keep cx fr regs3 R1 mem3 mem3 [] HFRAC (lib.Lib.Frame.munch_refl [] mem3)
               E2 E3 E4 E8 E9 E19 E26); intros; exact I. }
    assert (HCUR1 : B.ACtlCutP.CUR cx 7 R1).
    { destruct HCUR as (Hc & Hc23 & Hc25). split; [exact Hc|]. unfold B.ACtlCut.rgv in *.
      split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    apply (w2b_tail_81b00 POST cx fr k ly3 S3 W3 R1 mem3 md1 HY58 HB HJ1 ltac:(lia) Hfrs Hfa Hperm HFRAC1 Hn
             HCUR1 HOUR HIDB HRBE1 Hrt).
    (* has_identity_record = 0: the cut 0x81c60, memory unchanged, a0 = 0 *)
    intros Eh0 R md2 HJ2 F10 F1 F2 F3 F4 F8 F9 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27.
    assert (HRBE2 : B.ACtlCutP.RBE cx fr R mem3).
    { apply (w2b_RBE_keep cx fr R1 R mem3 mem3 [] A HRBE1 (lib.Lib.Frame.munch_refl [] mem3)
               ltac:(unfold B.ACtlCut.rgv in *; rewrite E9; exact Hr9) ltac:(lia) ltac:(lia) F9); intros; exact I. }
    pose proof HRBE2 as (_ & _ & _ & S264 & _ & _ & S56 & _ & _ & S8 & _ & _ & _ & _ & _ & _ & _ & _ & S176 & S208 &
      S64 & _ & _ & _ & HOURa & _ & _ & _ & HPRA & S152 & _ & _ & S160).
    assert (Ec0 : B.Prog.SlotModel.c0 (B.ACtlCut.c_in cx) = 7).
    { destruct HCUR as (Hc0 & _). pose proof HB as ((_ & _ & _ & _ & _ & Hnlen & _) & _).
      unfold B.Prog.SlotModel.c0, B.Prog.SlotModel.nlen. lia. }
    refine (HY60 cx [] fr k ly3 S3 W3 R mem3 md2 HB HJ2 Hfrs Hfa _ _ Hrt).
    { cbn [B.ACtlCut.cut_kmax B.ACtlCutP.C_B81c60]. lia. }
    unfold B.ACtlCutP.C_B81c60. cbn [B.ACtlCut.cut_body].
    split; [exact Hperm|].
    split.
    { apply (w2b_FRAC_keep cx fr R1 R mem3 mem3 [] HFRAC1 (lib.Lib.Frame.munch_refl [] mem3)
               F2 F3 F4 F8 F9 F19 F26); intros; exact I. }
    split; [exact Hn|].
    split; [exact HOUR|].
    split; [unfold B.ACtlCut.a0v, B.ACtlCut.rgv; exact F10|].
    split.
    { unfold B.ACtlCutP.PRO. split; [exact HPRA|]. split; [exact S152|]. split; [exact S264|].
      split; [exact HOURa | exact S160]. }
    split.
    { exists (B.ACtlCutP.Sfr fr + 68). split; [exact S8|]. unfold B.ACtlCutP.Sfr. lia. }
    split; [exact S56|]. split; [exact S176|]. split; [exact S208|]. split; [exact S64|].
    split.
    { rewrite Ec0. destruct HCUR1 as (Hc0 & Hc23 & Hc25). split; [exact Hc0|]. unfold B.ACtlCut.rgv in *.
      split; [rewrite F23; exact Hc23 | rewrite F25; exact Hc25]. }
    exact (ctl_kind_name_addressable ly3 S3 W3 mem3 md2 (proj1 HJ2)).
Qed.

End W2b.
