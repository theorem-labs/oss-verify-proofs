(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* lib/B/ACtlW4e2.v -- piece W4e2 (S_F24 .. S_F29, cut-table-B.tsv rows 68-73: B82878_at j .. B82aa4_at j) of
   fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.
   One writer: a Theorem Labs lane's glue lane.  rule 24: no function proved (stage glue of a walk; drafting).

   WHAT THIS FILE PROVES (when it builds): one stage lemma per cut of the piece, "the successor cuts hold -> this
   cut holds" (the donor's rt_B / rt_C shape, A/ACf1.v:499, A/ACf2.v:402 at c8557374ad2e), POINTWISE in the frame
   turn j with ACtlCut.ix_cut (as lib/B/ACtlW4e1.v; frame-loop induction in W4g / the top).  Each stage lemma carries
   the NAME of its stage hypothesis in lib/B/ACtl.v (seg_F24 .. seg_F29, ACtl.v:577-595 at 576147dfd46); the top
   cites ACtlW4e2.seg_F24 .. directly after instantiating SK and FP (ACtl.v:171-177).
     B82878_at j (0x82878) --S_F24--> B82888_at j (reac_ports_parse @0x82884)
     B82888_at j (0x82888) --S_F25--> B828a4_at j (reac_ports_unknown @0x828a0, c = fr + 160)
     B828a4_at j (0x828a4) --S_F26--> B828b4_at j (reac_ports_unknown @0x828b0, c = 0)
     B828b4_at j (0x828b4) --S_F27--> B8292c_at j (t_rp j = 0)  |  B82aa4_at j (t_rp j <> 0); silent
     B8292c_at j (0x8292c) --S_F28--> B82aa4_at j (the 12-turn port-slot loop and the tail; silent)
     B82aa4_at j (0x82aa4) --S_F29--> B82abc_at j (three frame-shadow stores and two register moves; silent)
   No allocator site, no fake-stack call, no runtime call: k and the frame list are unchanged on every stage.
   Successor sets: plan llvmf-B-walk-plan.md 2.3 rows 68-73; UB Seg/F24.v-F29.v headers.

   ROUTE, SHELL BINDING, THE FRAME TIE (ctl_from's G1 premise, named HG1 in the plans): as lib/B/ACtlW4e1.v's header.
   BUILD STATE (types only: u19build on a build machine; values are not evidence until the record core lands).
   ROUTE (C) (a working branch: ctl_from's runtime premise is B.ACtlRtC.ctl_rt_C B ly3 S3 mem3, not ACtlCut.ctl_rt mem3):
   all six stage lemmas end in Qed.  The two program callees are taken in their `_on` forms (no shadow_rw
   premise).  The stages carry ctl_rt_C from cut to cut with w4e2k_ctlrtC_run (no stage allocates, so ly3 / S3 do
   not move).
   No Axiom, no Parameter, no Admitted, no admit.

   SECTION HYPOTHESES.  THREE, the siblings' text (lib/B/ACtlW4e1.v / ACtlW4f.v), each discharged once by the top
   (owner ruling a Theorem Labs lane 05:31Z: a stage file does not prove them itself): Hwx (no segment wraps), segs_low (the
   image lies below kLowMemEnd) and LAWS (the core's AR_laws, lib/B/ACtl.v's LAWS).  ctl_block_apart_fs (lib/B/
   ProgWorld.v's ctl_block_apart_fs_stmt B) is no longer a hypothesis: it is CITED, a Theorem Labs lane's proved
   B.ProgWorldBlkApart.ctl_block_apart_fs (94a9bc51607; on a working branch from b12b5ddf699; rule a Theorem Labs lane 13:12Z), used only
   where a stage stores into the owned frame or its shadow while a body conjunct reads the live block (seg_F24,
   seg_F25, seg_F29, through w4e2_block_frame_apart).  tfibsegs_rsegs is cited (ProgBridge.tfibsegs_rsegs, the
   frozen bridge's lemma), and the visibility transports V1 / V3 / V4 / V5 of plan 2.4 are PROVED here from the
   journal and the AR laws, so no fp_avoids / rng fact is assumed.  rt_of_core is not needed (ctl_rt_C carries the
   cells the callees read).  The two program callees are NOT hypotheses: their footprint contracts are PROVED in
   this worktree with no premise, and the stages use the theorems directly:
   - reac_ports_parse (entry 0x883d0): B.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on
     (reac_ports_parseF.v:470) : reac_ports_parse_contract_F_on (reac_ports_parse_c.v:129; route (C): no shadow_rw
     premise; plan F.2 row 34);
   - reac_ports_unknown (entry 0x88628): B.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on
     (reac_ports_unknownF.v:370) : reac_ports_unknown_contract_F_on (reac_ports_unknown_c.v:154; route (C): no
     shadow_rw premise; plan F.2 rows 35-36 (a working note, not in this delivery); files by path from a working branch 076e983605e).
   ITEM 23 (the final ProgWorld form) asks for NO conversion in this piece, and none is stated: S_F24 .. S_F29
   make no runtime call, no world-form call and no allocator call (line 16 above), and the two program callees are
   FOOTPRINT contracts lifted whole, whose posts already give the bytes of the ranges they write in lib/Lib's
   vocabulary over the `_F` run's own memory.  So this file carries no ctl_post_<callee>, no ctl_post_acall_kept
   and no aview_vis_mrd hypothesis (the ported kit cites ProgWorld's proved aview_vis_mrd), and no hypothesis or
   statement of it is a callee post over raw memory; the raw `munch` /
   `rw_cells` words below are the cited `_F` lemmas' own texts, inside the plan comments.
   `_F` RUNS (a Theorem Labs lane's bF-statements/<File>F.md; names per bF-brief.md:36-43 (a working note, not in this delivery) and bseg-runs.tsv rows 117-124 (a working note, not in this delivery)),
   Required QUALIFIED and used directly (glue closure rule, porter 23:38Z): no `_F` text is copied here.
   Every image-B `_F` module is proved on ONE branch, a working branch 12a7ea50807
   (lib/B/Prog/Seg/<File>F.v); the ones cited below are in this tree.
   CITED (proved; none of them mentions AC.GT):
   - B.Prog.Seg.F24F.f24_pre_F       (F24F.md:10-23; 0x82878 -> 0x883d0 = PPC.REAC_PORTS_PARSE, ra = 0x82888)
   - B.Prog.Seg.F25F.f25_pre_F_on    (F25F.v:65, route (C): no shadow_rw premise; 0x82888 -> 0x88628 =
                                      PUC.REAC_PORTS_UNKNOWN, ra = 0x828a4)
   - B.Prog.Seg.F26F.seg_F26_pre_F   (F26F.md:13-22; 0x828a4 -> 0x88628, ra = 0x828b4)
   - B.Prog.Seg.F27F.seg_F27_F       (F27F.md:10-30; the r = 0 arm, 0x828b4 -> 0x8292c)
   - B.Prog.Seg.F27F.seg_F27_rp_F    (F27F.md:38-54; the r <> 0 arm, 0x828b4 -> 0x82aa4)
   - B.Prog.Seg.F28F.f28_loop_F      (F28F.md:11-35, continuation-passing, 0x8292c -> 0x829cc)
   - B.Prog.Seg.F28F.f28_tail_F      (F28F.md:45-72, continuation-passing, 0x829cc -> 0x82aa4)
   - B.Prog.Seg.F29F.f29_evt_ro_F    (F29F.v:128; 0x82aa4 -> 0x82abc; ro_agree in place of mem_inv: ctl_rt_C
                                      carries ro_agree, NOT mem_inv, which the real memory does not satisfy)
   NOT USED: f24_post_F, f25_post_F and seg_F26_post_F (zero-step stretches at the cuts 0x82888 / 0x828a4 /
   0x828b4: the continuation reads the cut body over VISIBLE addresses from the callee post), and f29_evt_F
   (its premise mem_inv cannot be carried).
   CLOSURE (rule (3)-(4)): as lib/B/ACtlW4e1.v's header; the Seg sources at UB 3803efccea0 are F24.v 459ef6164a8,
   F25.v 1da81b404de, F26.v dafb3d337f8, F27.v a0b51aa2c6b, F28.v f6be1c0fd18, F29.v d3a8027a519.
   lib/B/MemNormF.v (blob 99f8b314301, taken by path from dba073859bd; F29F.v Requires it for f29_evt_ro_F) is on
   this branch from this commit; it Requires only lib/B/Reusable/YK11, lib/Lib (PropExec MState Mem Exec Frame
   ExecF) and lib/B (Img0, MemNorm a10a476ffd9).

   PROVENANCE: cut table rows 68-73 (lines 69-74) (a working note, not in this delivery); cut records lib/B/ACtlCutP.v (6d691a975b6); plan 2.3 rows 68-73, F.2 rows 34-36, 6.2, F.4.1 rows 53-64 (a working note, not in this delivery);
   ctrl's runs at a working branch 3803efccea0
   (Seg/F24.v-F29.v; Seg/F24.v is not in this delivery); objdump fuzz_ctrl.objdump.txt L85355-L85499 (a working note, not in this delivery). *)

From Coq Require Import ZArith List Permutation Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YA0o.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG01 Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's image-B bridge (FROZEN 03:17Z): tfibsegs_rsegs, cfg_at_MS, fevt_of_evtF / fsteps_of_mstepsF, RNG_W *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel Prog.RcLeaf Prog.RcPorts Prog.RcPortsLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag B.Prog.Seg.F28.
(* the two callees' proved footprint contracts *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ports_parseF B.Prog.reac_ports_unknownF.
(* a Theorem Labs lane's `_F` modules, Required qualified (glue closure rule, porter 23:38Z) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F24F B.Prog.Seg.F25F B.Prog.Seg.F26F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F27F B.Prog.Seg.F28F B.Prog.Seg.F29F.
(* the unit's copy of YK11: the `_F` posts state their register facts with its getr (same body as the core's) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YK11.
(* the ported body-transport kit's modules (lib/B/ACtlW4e1.v's w4k_ / w4m_ / w4_ helpers) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRTFacts B.Prog.Seg.Tac_ro B.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
(* route (C): ctl_from's runtime premise ctl_rt_C and its region form shadow_rw_on (a working branch) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ShadowRwOn.
(* ctl_block_apart_fs, PROVED (a Theorem Labs lane 94a9bc51607): a live heap block is apart from the fake-stack region *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldBlkApart.
(* frame_facts: a live fake frame lies inside the fake-stack region (seg_F29's block / frame apartness) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec.
Import ListNotations.
Local Open Scope Z_scope.

(* Module aliases.  lib/Lib has two other copies in this closure (lib/B/Bz/Lib, lib/B/Tk/UL), and YK11 two
   (core / unit), so every such name is reached through one of these full paths. *)
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module BK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgBridge.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotModel.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- register vocabulary: the cut's rgv (core getr) against the `_F` runs' maps (unit getr, Sem.reg_get) ---- *)
Lemma w4e2_rgv_reg : forall (regs : bvmap 5 word) (r : bv 5) v,
  bv_eqb r 0 = false -> ACtlCut.rgv regs r v -> Sem.reg_get regs r = Z_to_bv 64 v.
Proof. intros regs r v E H. unfold ACtlCut.rgv, CK11.getr in H. rewrite E in H. exact H. Qed.

Lemma w4e2_rgv_keep : forall (R regs : bvmap 5 word) (r : bv 5) v,
  BK11.getr R r = Sem.reg_get regs r -> ACtlCut.rgv regs r v -> ACtlCut.rgv R r v.
Proof.
  intros R regs r v E H. unfold ACtlCut.rgv, CK11.getr in *. unfold BK11.getr in E.
  destruct (bv_eqb r 0); [exact H | rewrite E; exact H].
Qed.

Lemma w4e2_rgv_set : forall (R : bvmap 5 word) (r : bv 5) v,
  BK11.getr R r = Z_to_bv 64 v -> ACtlCut.rgv R r v.
Proof. intros R r v E. unfold ACtlCut.rgv, CK11.getr. unfold BK11.getr in E. exact E. Qed.

Lemma w4e2_getr_keep : forall (R regs : bvmap 5 word) (r : bv 5),
  BK11.getr R r = Sem.reg_get regs r -> CK11.getr R r = CK11.getr regs r.
Proof.
  intros R regs r E. unfold CK11.getr. unfold BK11.getr in E.
  destruct (bv_eqb r 0); [reflexivity | exact E].
Qed.

(* ---- the ports model at a turn (C5.3): t_rp and t_unk agree on the declaration test of t_pbs ---- *)
Lemma w4e2_rp_unk : forall (inp : list byte) (j : nat),
  (SM.t_rp inp j = 0 /\ 0 <= SM.t_unk inp j <= 48 /\
   SM.t_unk inp j = 4 * Prog.RcPorts.pu_nunk (SM.t_pbs inp j) 12 /\
   Prog.RcLeaf.decl (SM.t_pbs inp j) = true /\
   SM.t_first inp j = Prog.RcPorts.pu_first (SM.t_pbs inp j) 12) \/
  (SM.t_rp inp j = -1 /\ SM.t_unk inp j = -1 /\ Prog.RcLeaf.decl (SM.t_pbs inp j) = false).
Proof.
  intros inp j. unfold SM.t_rp, SM.t_unk, SM.t_first.
  assert (E : Prog.RcPorts.pu_decl (SM.t_pbs inp j) = Prog.RcLeaf.decl (SM.t_pbs inp j)) by reflexivity.
  rewrite E. destruct (Prog.RcLeaf.decl (SM.t_pbs inp j)).
  - left. pose proof (Prog.RcPortsLib.pu_nunk_range (SM.t_pbs inp j) 12) as Hr.
    change (Z.of_nat 12) with 12 in Hr.
    split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; reflexivity.
  - right. split; [reflexivity|]. split; reflexivity.
Qed.

(* ---- bytes / addressable / shadow-hull arithmetic ---- *)
Lemma w4e2_bytes_nth : forall m a (bs : list byte) i,
  LMm.bytes_at B.Img0.rsegs m a bs -> (i < length bs)%nat ->
  LMm.bytes_at B.Img0.rsegs m (a + Z.of_nat i) [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i (H0 & H1 & H) Hi. split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (Ek : k = 0%nat) by lia. subst k.
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite (H i Hi). cbn [nth_error]. apply nth_error_nth'. exact Hi.
Qed.

Lemma w4e2_addr_sub : forall m p n off k, ART.addressable m p n -> 0 <= off -> 0 <= k -> off + k <= n ->
  ART.addressable m (p + off) k.
Proof.
  intros m p n off k (H0 & H1 & H2 & H) Ho Hk Hok. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + off + i) with (p + (off + i)) by lia. apply H. lia.
Qed.

Lemma w4e2_shadow_rng : forall x, 0 <= x < 2 ^ 64 ->
  0 <= Z.shiftr x 3 + ART.ASAN_K /\ Z.shiftr x 3 + ART.ASAN_K + 1 <= 2 ^ 64.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ART.ASAN_K.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4e2_hull : forall p n x, 0 <= p -> p <= x < p + n ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= Z.shiftr x 3 + ART.ASAN_K <
  Reusable.YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8.
Proof.
  intros p n x Hp Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.ASAN_K.
  assert (A1 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : x / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  remember (p / 8) as u. remember (x / 8) as w. remember ((p + n - 1) / 8) as v.
  Z.div_mod_to_equations. lia.
Qed.

(* the turn's block bytes: t_blk is 32 bytes and agrees with the 20 ports bytes t_pbs on their indices *)
Lemma w4e2_blk_len : forall inp j, length (SM.t_blk inp j) = 32%nat.
Proof.
  intros inp j. unfold SM.t_blk, Prog.RcFrag.bsl, SM.t_g, SM.fr50.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
  rewrite length_firstn, length_skipn, length_firstn, length_app, repeat_length. lia.
Qed.

Lemma w4e2_pbs_blk : forall inp j i d, (i < 20)%nat -> nth i (SM.t_pbs inp j) d = nth i (SM.t_blk inp j) d.
Proof.
  intros inp j i d Hi. unfold SM.t_pbs, SM.t_blk, Prog.RcFrag.bsl.
  change (Z.to_nat 20) with 20%nat. change (Z.to_nat 32) with 32%nat.
  change (Z.to_nat 18) with 18%nat.
  set (l := skipn 18 (SM.t_g inp j)).
  assert (Hl : (32 <= length l)%nat).
  { unfold l, SM.t_g, SM.fr50. rewrite length_skipn, length_firstn, length_app, repeat_length. lia. }
  rewrite <- (firstn_skipn 20 (firstn 32 l)).
  rewrite firstn_firstn. change (Init.Nat.min 20 32) with 20%nat.
  rewrite app_nth1; [reflexivity|]. rewrite length_firstn. lia.
Qed.

(* The ports model's three word values in the forms the F28 runs read (by rewriting, never by conversion inside a
   le4 / Z_to_bv: the kernel would unfold the 12-step count there). *)
Lemma w4e2_n_in : forall X, Prog.RcLeaf.n_in X = Prog.RcLeaf.cnt Prog.RcLeaf.is_in X 12.
Proof. reflexivity. Qed.
Lemma w4e2_n_out : forall X, Prog.RcLeaf.n_out X = Prog.RcLeaf.cnt Prog.RcLeaf.is_out X 12.
Proof. reflexivity. Qed.
Lemma w4e2_bt : forall X i, Prog.RcLeaf.bt X i = bv_unsigned (nth i X (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

(* ---- the ports_unknown call (seg_F26): the 20 ports bytes are the first 20 bytes of the turn block, and the
   callee's count is t_unk at a non-null pointer ---- *)
Lemma w4e2_bytes_firstn : forall m a (l : list byte) n, LMm.bytes_at B.Img0.rsegs m a l -> (n <= length l)%nat ->
  LMm.bytes_at B.Img0.rsegs m a (firstn n l).
Proof.
  intros m a l n (H0 & H1 & H) Hn.
  split; [exact H0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. specialize (H i ltac:(lia)).
  rewrite <- (firstn_skipn n l) in H. rewrite nth_error_app1 in H by (rewrite length_firstn; lia). exact H.
Qed.

Lemma w4e2_pbs_blk20 : forall inp j, SM.t_pbs inp j = firstn 20 (SM.t_blk inp j).
Proof.
  intros inp j. unfold SM.t_pbs, SM.t_blk, Prog.RcFrag.bsl. rewrite firstn_firstn. reflexivity.
Qed.

Lemma w4e2_unk_ok : forall p inp j, p <> 0 ->
  (if Prog.RcPorts.pu_ok p (SM.t_pbs inp j) then 4 * Prog.RcPorts.pu_nunk (SM.t_pbs inp j) 12 else -1) =
  SM.t_unk inp j.
Proof.
  intros p inp j Hp. unfold Prog.RcPorts.pu_ok. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity.
Qed.

(* ---- the ports_parse call (seg_F24): the callee's result is t_rp at non-null pointers ---- *)
Lemma w4e2_rp_ok : forall p q inp j, p <> 0 -> q <> 0 ->
  (if Prog.RcLeaf.ports_ok p q (SM.t_pbs inp j) then 0 else -1) = SM.t_rp inp j.
Proof.
  intros p q inp j Hp Hq. unfold Prog.RcLeaf.ports_ok.
  rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq). reflexivity.
Qed.

Lemma w4e2_ports_ok_decl : forall p q bs, p <> 0 -> q <> 0 ->
  Prog.RcLeaf.ports_ok p q bs = Prog.RcLeaf.decl bs.
Proof.
  intros p q bs Hp Hq. unfold Prog.RcLeaf.ports_ok.
  rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq). reflexivity.
Qed.

(* ---- the ports_unknown call with the first-byte cell (seg_F25) ---- *)
Lemma w4e2_first_ok : forall p inp j, p <> 0 ->
  (if Prog.RcPorts.pu_ok p (SM.t_pbs inp j) then Prog.RcPorts.pu_first (SM.t_pbs inp j) 12 else 0) =
  SM.t_first inp j.
Proof.
  intros p inp j Hp. unfold Prog.RcPorts.pu_ok. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity.
Qed.

Section W4e2.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

(* ---- SHELL BINDING (the only lines naming ACtlCut's / ACtlCutP's argument lists) ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ctl_base := (ACtlCut.ctl_base B MT XM_LIB RLO RHI).
(* ctl_from's journal premise, verbatim (ACtlCut.v section 5), as one name for the helpers below. *)
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation ix := ACtlCut.ix_cut.
Local Notation C_B82878_at := (ACtlCutP.C_B82878_at B).
Local Notation C_B82888_at := (ACtlCutP.C_B82888_at B).
Local Notation C_B828a4_at := (ACtlCutP.C_B828a4_at B).
Local Notation C_B828b4_at := (ACtlCutP.C_B828b4_at B).
Local Notation C_B8292c_at := (ACtlCutP.C_B8292c_at B).
Local Notation C_B82aa4_at := (ACtlCutP.C_B82aa4_at B).
Local Notation C_B82abc_at := (ACtlCutP.C_B82abc_at B).

(* ---- Section hypotheses (siblings' text; the top discharges each once, owner ruling a Theorem Labs lane 05:31Z) ----
   Hwx: no loaded segment wraps (YA0nR.SRr_fsteps / fsteps_keeps_hidden take it).  segs_low: the image lies below
   kLowMemEnd (YCbq.ajournal_exec takes it).  LAWS: the core's AR laws (lib/B/ACtl.v's LAWS); ajournal_exec,
   frames_bounds, al_frames, al_blocks and al_shadow are stated under it. *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.

(* ---------------------------------------------------------------------------------------------------------
   The kit (proved here: the W4e1 helpers w4_lift / w4_after_run end in Abort on this base). *)

(* A footprint run grows memory (YI04.step_mem_grows per step). *)
Lemma w4e2_mstepsF_grows : forall RNG ms ms', LX.mstepsF B.Img0.rsegs RNG ms ms' ->
  CK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' H. induction H as [ms | ms ms1 ms2 Hs _ IH].
  - apply CK1b.mem_grows_refl.
  - eapply CK1b.mem_grows_trans; [|exact IH].
    exact (CI04.step_mem_grows _ _ _ (LX.mstepF_step _ _ _ _ Hs)).
Qed.

(* The lift: an `_F` run at the largest footprint the world admits (ProgBridge.RNG_W) is a silent prefix of the
   walk (YA0nR.SRr_fsteps); the continuation gets the run's post, memory growth, the hidden bytes unchanged
   (YA0nR.fsteps_keeps_hidden) and the materialized model -- what YCbq.ajournal_exec takes. *)
Lemma w4e2_lift : forall (W : Reusable.YA0n.world segs) ms md (P : machine_state -> Prop)
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  LX.evtF B.Img0.rsegs (PB.RNG_W (Reusable.YA0n.w_H W)) P ms ->
  (forall ms' md', P ms' -> CK1b.mem_grows (ms_mem ms) (ms_mem ms') ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md P Q (ms' & Hrun & HP) K.
  pose proof (w4e2_mstepsF_grows _ _ _ Hrun) as Hg.
  pose proof (PB.fsteps_of_mstepsF _ _ _ Hrun) as Hfs.
  rewrite <- PB.tfibsegs_rsegs in Hfs.
  pose proof (PB.fp_avoids_RNG_W (Reusable.YA0n.w_H W)) as Hav.
  apply (Reusable.YA0nR.SRr_fsteps segs Hwx W ms ms' md _ Q Hfs Hav).
  intros md' Hs. apply (K ms' md' HP Hg); [|exact Hs].
  exact (Reusable.YA0nR.fsteps_keeps_hidden segs Hwx (Reusable.YA0n.w_H W) _ ms ms'
           (Reusable.YA0n.w_Hoff W) Hfs Hav).
Qed.

(* The world facts of an own6 cut (the visibility transports V1 / V5 of plan 2.4, PROVED here from the journal
   and the AR laws): the frame is the journal's owned class-6 frame (ctl_from's frame law), below the allocation
   ceiling; its 4096 bytes and their 512 shadow bytes are visible; the present stack window is present. *)
Lemma w4e2_world : forall cx fr k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  4096 <= fr /\ fr + 4096 <= CM05.alloc_ceiling /\
  CM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= 2 ^ 47 /\
  0x7fff7f800000 <= CM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) /\
  (forall a, ART.shadow_addr fr <= a < ART.shadow_addr fr + 512 ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) /\
  (forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ HF HL.
  destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hceil & _).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & Hfb & Hfs).
  rewrite Efa in H4096, Hceil, Hfb, Hfs.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in *.
  destruct Hstk as (_ & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof Reusable.YCbq.asan_consts as ((C1 & _) & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (proj1 (proj1 (Hfb a Ha)))|].
  split.
  { intros a Ha. change (4096 / 8) with 512 in Hfs.
    assert (Ea : ART.shadow_addr fr = Reusable.YG0f.shadow_addr fr)
      by (unfold ART.shadow_addr, Reusable.YG0f.shadow_addr, ART.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
    pose proof (Hfs (a - Reusable.YG0f.shadow_addr fr) ltac:(lia)) as Hx.
    replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hx by lia.
    exact (proj1 (proj1 Hx)). }
  exact Hpres.
Qed.

(* A live block (the turn's phi) and its shadow hull are visible (V3 / V4 of plan 2.4, PROVED from the AR block
   and shadow laws; a hidden shadow byte would read as the absent image byte, YA0o.seg_rom_hidden). *)
Lemma w4e2_block : forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 p n,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  4096 <= p /\ p + Reusable.YG00.req_size n <= CM05.alloc_ceiling /\
  (forall a, p <= a < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) /\
  (forall s, Reusable.YG0f.shadow_addr p / 8 * 8 <= s <
             Reusable.YG0f.shadow_addr (p + Reusable.YG00.req_size n - 1) / 8 * 8 + 8 ->
     Reusable.YA0n.w_H W3 (Z_to_bv 64 s) = false).
Proof.
  intros ly3 S3 W3 mem3 md3 p n HAR Hin.
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n HAR Hin)
    as (_ & H4096 & Hceil & _ & Hb & _).
  destruct (Reusable.YG0d.al_shadow segs B LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & Hhull).
  split; [lia|]. split; [lia|]. split; [intros a Ha; exact (proj1 (proj1 (Hb a Ha)))|].
  intros s Hs. specialize (Hhull s Hs).
  destruct (Reusable.YA0n.w_H W3 (Z_to_bv 64 s)) eqn:E; [|reflexivity].
  exfalso. apply Hhull.
  cbv delta [Reusable.YG0n.aview lib.Reusable.YP09.mbyte Reusable.YK04.mrestrict] beta.
  rewrite E.
  rewrite (Reusable.YA0o.seg_rom_hidden segs (Reusable.YA0n.w_H W3) _ (Reusable.YA0n.w_Hoff W3) E).
  reflexivity.
Qed.

(* A spill word is at FRAC's spill base A (register 9 pins it modulo 2^64; A < 2^47). *)
Lemma w4e2_spill : forall (regs : bvmap 5 word) m A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 2 ^ 40 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v R9 HA Hoff (A' & R9' & Hq).
  unfold ACtlCut.rgv in R9, R9'. rewrite R9 in R9'.
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite LMm.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    apply (f_equal (@bv_unsigned 64)) in R9'. rewrite !Z_to_bv_unsigned in R9'. unfold bv_wrap in R9'.
    change (bv_modulus 64) with (2 ^ 64) in R9'.
    Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* The register-reading bundles move along a map that keeps the registers they read. *)
Lemma w4e2_spill_keep : forall (R regs : bvmap 5 word) m off v,
  CK11.getr R 9 = CK11.getr regs 9 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m off v.
Proof. intros R regs m off v E (A' & H9 & Hq). exists A'. split; [|exact Hq]. unfold ACtlCut.rgv in *. rewrite E. exact H9. Qed.

Lemma w4e2_frac_keep : forall cx fr sel (regs R : bvmap 5 word) m,
  ACtlCutP.FRAC B cx fr sel regs m ->
  CK11.getr R 2 = CK11.getr regs 2 -> CK11.getr R 3 = CK11.getr regs 3 -> CK11.getr R 4 = CK11.getr regs 4 ->
  CK11.getr R 8 = CK11.getr regs 8 -> CK11.getr R 9 = CK11.getr regs 9 -> CK11.getr R 19 = CK11.getr regs 19 ->
  CK11.getr R 26 = CK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel R m.
Proof.
  intros cx fr sel regs R m H E2 E3 E4 E8 E9 E19 E26.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

Lemma w4e2_LK_keep : forall cx fr j (regs R : bvmap 5 word) m,
  CK11.getr R 9 = CK11.getr regs 9 -> CK11.getr R 27 = CK11.getr regs 27 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j R m.
Proof.
  intros cx fr j regs R m E9 E27 (Hj & S240 & HO & HFLI).
  split; [exact Hj|]. split; [exact (w4e2_spill_keep R regs m _ _ E9 S240)|]. split; [exact HO|].
  unfold ACtlCutP.FLI in *.
  destruct HFLI as (R27 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
    F17 & F18 & F19 & F20 & F21 & HAd & HStk & HRAD & HKNT & F22 & F23).
  split; [unfold ACtlCut.rgv in *; rewrite E27; exact R27|].
  repeat (split; [first [apply (w4e2_spill_keep R regs m _ _ E9); assumption | assumption]|]).
  apply (w4e2_spill_keep R regs m _ _ E9); assumption.
Qed.

Lemma w4e2_FTL_keep : forall cx j phi fr (regs R : bvmap 5 word) m,
  CK11.getr R 9 = CK11.getr regs 9 -> CK11.getr R 21 = CK11.getr regs 21 -> CK11.getr R 24 = CK11.getr regs 24 ->
  ACtlCutP.FTL cx j phi fr regs m -> ACtlCutP.FTL cx j phi fr R m.
Proof.
  intros cx j phi fr regs R m E9 E21 E24 (R21 & S184 & S272 & R24 & S312).
  unfold ACtlCutP.FTL, ACtlCut.rgv in *. rewrite E21, E24.
  split; [exact R21|]. split; [exact (w4e2_spill_keep R regs m _ _ E9 S184)|].
  split; [exact (w4e2_spill_keep R regs m _ _ E9 S272)|]. split; [exact R24|].
  exact (w4e2_spill_keep R regs m _ _ E9 S312).
Qed.

Lemma w4e2_F27K_keep : forall cx j phi fr (regs R : bvmap 5 word) m,
  CK11.getr R 9 = CK11.getr regs 9 -> CK11.getr R 18 = CK11.getr regs 18 ->
  CK11.getr R 24 = CK11.getr regs 24 -> CK11.getr R 27 = CK11.getr regs 27 ->
  ACtlCutP.F27K cx j phi fr regs m -> ACtlCutP.F27K cx j phi fr R m.
Proof.
  intros cx j phi fr regs R m E9 E18 E24 E27
    (HLK & R18 & R27 & H0 & H50 & Hl & Hb & S312 & S272 & R24 & S104 & S136).
  split; [exact (w4e2_LK_keep cx fr j regs R m E9 E27 HLK)|].
  unfold ACtlCut.rgv in *. rewrite E18, E27, E24.
  split; [exact R18|]. split; [exact R27|]. split; [exact H0|]. split; [exact H50|]. split; [exact Hl|].
  split; [exact Hb|]. split; [exact (w4e2_spill_keep R regs m _ _ E9 S312)|].
  split; [exact (w4e2_spill_keep R regs m _ _ E9 S272)|]. split; [exact R24|].
  split; [exact (w4e2_spill_keep R regs m _ _ E9 S104)|]. exact (w4e2_spill_keep R regs m _ _ E9 S136).
Qed.

Lemma w4e2_FTURN_keep : forall cx j phi (regs R : bvmap 5 word) m,
  CK11.getr R 9 = CK11.getr regs 9 ->
  ACtlCutP.FTURN cx j phi regs m -> ACtlCutP.FTURN cx j phi R m.
Proof.
  intros cx j phi regs R m E9 (S224 & S232 & Hb & Hl).
  split; [exact (w4e2_spill_keep R regs m _ _ E9 S224)|].
  split; [exact (w4e2_spill_keep R regs m _ _ E9 S232)|]. split; [exact Hb | exact Hl].
Qed.

(* The journal across a run that writes no byte (the model is materialized): ajournal_exec, empty write set. *)
Lemma w4e2_aj_same : forall cx ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 md' k own,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  Reusable.YK04.same_but_materialized md3 md' ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx ly3 S3 W3 mem3 md3 md' k own HJ Hs.
  eapply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low) with (Wr := fun _ : Z => False);
    [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
    | exact Hs | intros a Ha; destruct Ha].
Qed.

Local Notation aview_vis_mrd := B.ProgWorld.aview_vis_mrd (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   THE PORTED KIT.  Lines 458-1860 of lib/B/ACtlW4e1.v at a working branch b3cc6232851 (its proved
   helpers, themselves ported from W3a and W4f as the two notes below say), renamed w4_ -> w4e2w_, w4k_ -> w4e2k_,
   w4m_ -> w4e2m_.  Changes: the Section hypothesis tfibsegs_rsegs read as ProgBridge.tfibsegs_rsegs; w4e2w_vis_high
   by YA0o.seg_rom_hidden instead of YF0x.seg_rom_none_high (YF0x is not in this closure); aview_vis_mrd is
   ProgWorld's proved lemma (the notation above); seven lemmas this file does not use are left out (w4_f22_want,
   w4k_mvis, w4m_bcmp_list_eq, w4m_bcmp_cmp, w4_ctlrt, w4_blk01, w4_FM_keep).  Every lemma ends in Qed. *)

(* H1. The core's configuration at a pc is ctrl's MState.MS state under tfibsegs_rsegs: YK11.mkst and MState.MS build the
   same record (FP registers and fcsr from the Section's fx), and YK11.seg_rom / PropExec.seg_rom have the same
   body (the SHADOWED NAMES rule of ACtlCut.v: they are different constants, equal by conversion only). *)
Lemma w4e2w_cfg_MS : forall (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  Reusable.YG0d.cfg_at segs pc regs mem md =
  mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
           (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md.
Proof. intros pc regs mem md. rewrite <- B.ProgBridge.tfibsegs_rsegs. reflexivity. Qed.

(* H2. The kit lift, keeping what the stage's journal step needs: the run's post, the materialized model, and the
   hidden bytes unchanged (YK04R.fsteps_restrict's second conjunct). *)
Lemma w4e2w_lift : forall (W : Reusable.YA0n.world segs) (ms : machine_state) (md : Model)
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
   the run is then one visibility fact (w4e2w_rng_vis below). *)
Lemma w4e2w_lift_F : forall (W : Reusable.YA0n.world segs) (ms : machine_state) (md : Model)
    (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P ms ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md P Q Hevt K.
  apply (w4e2w_lift W ms md (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P Q);
    [| apply B.ProgBridge.fp_avoids_RNG_W | exact K].
  (* segs (= YB1v.tfibsegs) is convertible to B.Img0.rsegs, so fevt_of_evtF's rsegs result closes the goal. *)
  exact (B.ProgBridge.fevt_of_evtF (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) P ms Hevt).
Qed.

(* The visibility fact a run's `rng RNG lo len` premise becomes under RNG_W. *)
Lemma w4e2w_rng_vis : forall (W : Reusable.YA0n.world segs) (lo len : Z),
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
Lemma w4e2w_after_run : forall POST (X : ACtlCut.ctlcut) cx idx (fr k : Z) ly3 S3 (W3 : Reusable.YA0n.world segs)
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
   (Regs6ss.xregs_eqv).  The kit's SRr_xregs_eqv moves the walk across that equivalence, and w4e2w_lift_F lifts the
   run.  The continuation sees the run's end state, the materialized model, and the start's hidden bytes. *)
Lemma w4e2w_seat_F : forall (W : Reusable.YA0n.world segs) (regs R : bvmap 5 word) (pc : Z)
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
  rewrite w4e2w_cfg_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W R regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
           lib.Reusable.YK11.fp_csr None mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs) md Q); [|exact Hxe].
  apply (w4e2w_lift_F W _ md P Q Hevt).
  intros ms' md' HP Hsbm Hhid. exact (K ms' md' HP Hsbm Hhid).
Qed.

(* H5. Visibility above the image.  At or above the image top 0x5fe000 there is no read-only image byte
   (YA0o.seg_rom_hidden: a hidden byte reads as the absent image byte), so a byte the core's view reads there (aview <> None) can only come from
   memory the world does not hide.  This is how a block's SHADOW byte, which AR_shadow_law gives as
   shadow_hull_vis (aview <> None), becomes visible. *)
Lemma w4e2w_vis_high : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
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
  rewrite (Reusable.YA0o.seg_rom_hidden segs (Reusable.YA0n.w_H W) _ (Reusable.YA0n.w_Hoff W) E).
  reflexivity.
Qed.

(* H6. One byte of a byte run (an `_F` run states its per-turn reads one byte at a time). *)
Lemma w4e2w_bytes_at_byte : forall (m : word -> option byte) (a : Z) (bs : list byte) (t : nat) (d : byte),
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
Lemma w4e2w_FRAC_cong : forall cx fr sel (r r' : bvmap 5 word) (m : word -> option byte),
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
(* H9. A live block's bytes are visible (V3): AR_blocks_law states apresent on every byte of a block the
   current state lists, and apresent includes w_H = false.  As an `_F` run's one-byte rng premise under RNG_W. *)
Lemma w4e2w_rng_block : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  p <= x -> x < p + Reusable.YG00.req_size n -> 0 <= x -> x + 1 <= 2 ^ 64 ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) x 1.
Proof.
  intros W mem ly S md p n x HAR Hin Hx1 Hx2 Hx0 Hx3.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpres & _ & _).
  apply w4e2w_rng_vis; [exact Hx0 | exact Hx3 |].
  intros a Ha. destruct (Hpres a ltac:(lia)) as (Hap & _). exact (proj1 Hap).
Qed.

(* H10. A live block's SHADOW bytes are visible (V4): AR_shadow_law gives the shadow hull as
   shadow_hull_vis (aview <> None); a shadow address lies above the image top, where w4e2w_vis_high turns
   aview <> None into w_H = false.  The run states the shadow byte as Z.shiftr x 3 + ASAN_K, which is the core's
   shadow_addr x = SHADOW_OFF + x / 8 for x >= 0. *)
Lemma w4e2w_block_shadow_vis : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
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
  apply (w4e2w_vis_high W mem).
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
Lemma w4e2w_rng_block_shadow : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) ly S md p n x,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= p -> p <= x -> x < p + Reusable.YG00.req_size n -> x < 2 ^ 64 ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) (Z.shiftr x 3 + B.ACtlK.ASAN_K) 1.
Proof.
  intros W mem ly S md p n x HAR Hin Hp Hx1 Hx2 Hx3.
  pose proof (w4e2w_block_shadow_vis W mem ly S md p n x HAR Hin Hp Hx1 Hx2 Hx3) as Hv.
  assert (Hd : Z.shiftr x 3 = x / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : x / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  unfold B.ACtlK.ASAN_K, B.AsanRT.ASAN_K in *.
  apply w4e2w_rng_vis; [rewrite Hd; lia | rewrite Hd; lia |].
  intros a Ha. replace a with (Z.shiftr x 3 + 0x7fff8000) by lia. exact Hv.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   BODY-TRANSPORT TOOLKIT (the w4e2k_ lemmas).  Ported from a Theorem Labs lane's PROVED local helpers (lib/B/ACtlW3a.v,
   lines 273-879 (at head lib/B/ACtlW3a.v:273-879; from a working branch 6365e5d6107); renamed w3a_ -> w4e2k_, `Proof using ..` relaxed to
   `Proof.` because aview_vis_mrd is a proved lemma here, and W3a's turn-0 / PRO-only lemmas left out).  Raw
   memory readers, the journal and ctl_rt_C after a silent run, the own6 cut context from the journal (w4e2k_cut6),
   and the transports of the carried bundles.  Each is proved from the core (YCbq, YG0d's AR laws, the journal),
   lib/Lib and B's ProgBridge; none is a hypothesis.  (If a Theorem Labs lane opens the shared translation file of plan
   section 5, these move there.) *)

Local Notation rsegs := B.Img0.rsegs.

Lemma w4e2k_P64 : 2 ^ 64 = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma w4e2k_outside_dec : forall W x, lib.Lib.Frame.outside W x \/ ~ lib.Lib.Frame.outside W x.
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

Lemma w4e2k_not_outside1 : forall lo hi a, ~ lib.Lib.Frame.outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. cbn [lib.Lib.Frame.outside] in H.
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma w4e2k_raw_mrd : forall (m : word -> option byte) x b, m x = Some b -> lib.Lib.Mem.mrd rsegs m x = Some b.
Proof. intros m x b H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma w4e2k_raw_wview : forall (m : word -> option byte) x b, m x = Some b -> wview rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

Lemma w4e2k_not_img_high : forall a, Reusable.YG0f.kLowMemEnd <= a -> ~ Reusable.YG0d.in_img segs a.
Proof. intros a Ha Hi. pose proof (segs_low a Hi) as H. lia. Qed.

Lemma w4e2k_mrd_raw : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa a) = Some b -> m (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros m a b Ha Hn H. unfold lib.Lib.Mem.mrd in H. destruct (m (lib.Lib.Mem.wa a)) as [b'|] eqn:E; [exact H|].
  exfalso. pose proof (Reusable.YCbq.seg_rom_none segs a Ha Hn) as R.
  assert (H' : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) by exact H.
  rewrite R in H'. discriminate.
Qed.

(* The image hull [0x10000, 0x5fe000) is covered by the segments (ProgBridge.rsegs_spans). *)
Lemma w4e2k_img_hull : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
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

Lemma w4e2k_mrd_munch : forall W (m m' : word -> option byte) x, lib.Lib.Frame.munch W m m' -> 0 <= x < 2 ^ 64 ->
  lib.Lib.Frame.outside W x -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x).
Proof.
  intros W m m' x MU Hx Ho. unfold lib.Lib.Mem.mrd. rewrite (MU (lib.Lib.Mem.wa x)); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho.
Qed.

Lemma w4e2k_bytes_keep : forall (m m' : word -> option byte) a bs,
  lib.Lib.Mem.bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  lib.Lib.Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite K; [exact (H i Hi) | lia].
Qed.

Lemma w4e2k_addr_keep : forall (m m' : word -> option byte) p n, B.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) K. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b.
  split; [rewrite (K i Hi); exact Hb | exact Hk].
Qed.

Lemma w4e2k_stk_raw : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [b Hb].
  split; [exact (w4e2k_raw_wview m _ b Hb) | exists b; exact (w4e2k_raw_mrd m _ b Hb)].
Qed.

Lemma w4e2k_wr_raw : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> exists b, m (lib.Lib.Mem.wa x) = Some b) -> lib.Lib.Mem.wr_at rsegs m a n.
Proof.
  intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (H (a + i) ltac:(lia)) as [b Hb]. exact (w4e2k_raw_wview m _ b Hb).
Qed.

Lemma w4e2k_rw8 : forall m a v, lib.Lib.Mem.bytes_at rsegs m a (lib.Lib.Mem.le8 v) -> lib.Lib.Mem.wr_at rsegs m a 8 ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 v].
Proof.
  intros m a v H Hw. split; [split; [exact (conj I I) | cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]; rewrite app_nil_r; exact H]|].
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. exact Hw.
Qed.

Lemma w4e2k_rw1 : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> m (lib.Lib.Mem.wa a) = Some b ->
  lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C1 b].
Proof.
  intros m a b Ha Hb. split; [split; [exact (conj I I)|] |].
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
    exact (w4e2k_raw_mrd m _ b Hb).
  - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. apply w4e2k_wr_raw; [lia | lia|].
    intros x Hx. replace x with a by lia. exists b. exact Hb.
Qed.

Lemma w4e2k_cb_raw : forall (m : word -> option byte) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, m (lib.Lib.Mem.wa x) = Some b) ->
  exists junk, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n junk].
Proof.
  intros m a n H0 H1 H.
  destruct (lib.Lib.Frame.stk_carve rsegs m a (a + Z.of_nat n) n (w4e2k_stk_raw m a (a + Z.of_nat n) H0 H1 H) ltac:(lia))
    as (_ & junk & Hj).
  replace (a + Z.of_nat n - Z.of_nat n) with a in Hj by lia. exists junk. exact Hj.
Qed.

Lemma w4e2k_bytes_of_mrd : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
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
Lemma w4e2k_spill_A : forall regs m off v A, B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 ->
  0 <= off <= 512 -> B.ACtlCutP.spill regs m off v -> B.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HA HA0 HA1 Hoff (A' & HA' & Hq).
  unfold B.ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
  apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
  change (bv_modulus 64) with (2 ^ 64) in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat Pos.of_succ_nat] in Hq1.
  pose proof w4e2k_P64 as P64. rewrite P64 in HA', HA1, Hq1.
  assert (E : A = A') by (Z.div_mod_to_equations; lia). subst A'. exact Hq.
Qed.

Lemma w4e2k_spill_keep : forall regs R (m m' : word -> option byte) off v A,
  B.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 1024 <= 2 ^ 64 -> 0 <= off <= 512 ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)) ->
  B.ACtlCutP.spill regs m off v -> B.ACtlCutP.spill R m' off v.
Proof.
  intros regs R m m' off v A HA HA0 HA1 Hoff E9 K Hs.
  pose proof (w4e2k_spill_A regs m off v A HA HA0 HA1 Hoff Hs) as Hq.
  exists A. split; [unfold B.ACtlCut.rgv; rewrite E9; exact HA|].
  apply (w4e2k_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

(* shadow_rw_on P after a silent run whose written bytes lie outside the image and are present afterwards: a byte
   outside the write set keeps its value, a written byte is present (the old whole-shadow argument, region P carried). *)
Lemma w4e2k_srwon_run : forall (P : Z -> Prop) (m m' : word -> option byte) Wr,
  B.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.munch Wr m m' -> lib.Lib.Frame.wmono rsegs m m' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a -> ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' Wr HSW MU WM HW a Hp Ha.
  destruct (HSW a Hp Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  pose proof (B.AsanRTFacts.in_shadow_range a Ha) as Hr.
  destruct (w4e2k_outside_dec Wr a) as [H|H].
  - exists b. rewrite (w4e2k_mrd_munch Wr m m' a MU ltac:(lia) H). exact Hb.
  - destruct (HW a H) as (_ & b' & Hb'). exists b'. exact (w4e2k_raw_mrd _ _ _ Hb').
Qed.

(* ctl_rt_C (route (C), ACtlCut.v ctl_from's runtime premise) after a silent run whose written bytes lie outside
   the image and are present afterwards.  No stage of this file allocates or moves a frame, so the successor cut has
   the same ly3 / S3 and the two shadow regions of ctl_rt_C (cut_shadow ly S, img_shadow) are the same sets. *)
Lemma w4e2k_ctlrtC_run : forall ly S (m m' : word -> option byte) Wr,
  B.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch Wr m m' -> lib.Lib.Frame.wmono rsegs m m' ->
  (forall a, ~ lib.Lib.Frame.outside Wr a -> ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b) ->
  B.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S m m' Wr (HAC & HSF & HSI & HRO) MU WM HW.
  assert (KI : forall x, 0 <= x < 2 ^ 64 -> ~ ~ Reusable.YG0d.in_img segs x ->
             lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa x)).
  { intros x Hx Hi. apply (w4e2k_mrd_munch Wr); [exact MU | exact Hx |].
    destruct (w4e2k_outside_dec Wr x) as [H|H]; [exact H|]. exfalso. exact (Hi (proj1 (HW x H))). }
  pose proof w4e2k_P64 as P64.
  split; [|split; [|split]].
  - unfold B.ACtlK.asan_cells_at, B.AsanRT.asan_cells in HAC |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; (eapply w4e2k_bytes_keep; [eassumption|]); intros x Hx;
      (apply KI; [| intros Hn; apply Hn; apply w4e2k_img_hull]);
      rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx;
      unfold B.AsanRT.CELL_K, B.AsanRT.UAR, B.AsanRT.INITED, B.AsanRT.REPLACE, B.AsanRT.CANPOISON,
        B.AsanRT.HIEND, B.AsanRT.MIDBEG, B.AsanRT.MIDEND, B.AsanRT.REAL_MEMCPY, B.AsanRT.REAL_MEMSET,
        B.AsanRT.GOT_CELL_K, B.AsanRT.GOT_UAR, B.AsanRT.GOT_REPLACE, B.AsanRT.GOT_HIEND, B.AsanRT.GOT_MIDBEG,
        B.AsanRT.GOT_MIDEND, B.AsanRT.GOT_REAL_MEMSET in Hx; lia.
  - exact (w4e2k_srwon_run _ m m' Wr HSF MU WM HW).
  - exact (w4e2k_srwon_run _ m m' Wr HSI MU WM HW).
  - unfold B.ACtlK.ro_agree_at in HRO |- *. intros a Ha. rewrite <- (HRO a Ha).
    pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    assert (E : lib.Lib.Mem.wa (bv_unsigned a) = a)
      by (unfold lib.Lib.Mem.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
    rewrite <- E. apply KI; [lia|]. intros Hn. unfold lib.Lib.Mem.ro_addr in Ha.
    assert (Hn' : find_segment rsegs (bv_unsigned a) 1 = None) by exact (Reusable.YCbq.find_segment_none segs _ Hn).
    rewrite Hn' in Ha. discriminate.
Qed.

(* The journal after a silent run (YCbq.ajournal_exec) whose written bytes are journal-writable. *)
Lemma w4e2k_after_run : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k
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
    apply MU. destruct (w4e2k_outside_dec Wr (bv_unsigned x)) as [H|H]; [exact H | exfalso; exact (Hx H)].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (w4e2k_outside_dec Wr (bv_unsigned x)) as [H|H]; [rewrite (MU x H); exact Hx|].
    destruct (HW _ H) as ((b & Hb) & _). unfold lib.Lib.Mem.wa in Hb.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
    rewrite Hb. discriminate.
  - intros a Ha. exact (proj2 (HW a Ha)).
Qed.

Lemma w4e2k_awr_fsh : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
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

Lemma w4e2k_awr_fr : forall (cx : B.ACtlCut.ctlcx) ly3 fr STK sp0 bl0 blc a,
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) -> fr <= a < fr + 4096 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 (B.ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 fr STK sp0 bl0 blc a Efr Ha. right. right. right.
  exists 6, (B.ACtlCut.c_fpos cx). split; [left; reflexivity|]. left. rewrite <- Efr.
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

Lemma w4e2k_awr_stk : forall ly3 own STK sp0 bl0 blc a, sp0 - STK <= a < sp0 ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly3 own a.
Proof. intros ly3 own STK sp0 bl0 blc a Ha. left. exact Ha. Qed.

(* Step C0 for an own6 cut: the frame's placement and presence, the frame shadow's presence, the stack window's
   presence and placement, all from the journal (its AR, YG0d's AR_frames_law, astk_ok, the window clause) and
   the shell's frame law. *)
Lemma w4e2k_cut6 : forall (cx : B.ACtlCut.ctlcx) fr k ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3,
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
    exfalso. apply (Himg (Z.max fr 0x10000)); [lia | apply w4e2k_img_hull; lia]. }
  split; [exact Himg|]. split; [intros a Ha; exact (proj1 (Hfb a Ha))|].
  split.
  { intros a Ha. pose proof (proj1 (Hfsh (a - B.ACtlCutP.Sfr fr) ltac:(lia))) as H.
    replace (Reusable.YG0f.shadow_addr fr + (a - B.ACtlCutP.Sfr fr)) with a in H; [exact H|].
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.ACtlCutP.Sfr, B.AsanRT.shadow_addr,
      B.AsanRT.ASAN_K. lia. }
  split; [exact H16|]. split; [lia|]. split; [lia|]. exact Hpres.
Qed.

Lemma w4e2k_vis : forall (W : Reusable.YA0n.world segs) mem lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W mem lo len H0 H1 H. apply B.ProgBridge.rng_of_visible. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (proj1 (H a Ha)).
Qed.

Lemma w4e2k_sh_off : forall fr off i, fr mod 8 = 0 -> off mod 8 = 0 -> 0 <= i < 8 ->
  B.AsanRT.shadow_addr (fr + off + i) = B.ACtlCutP.Sfr fr + off / 8.
Proof.
  intros fr off i Hf Ho Hi. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. pose proof (Z.div_mod off 8 ltac:(lia)) as E2.
  rewrite Hf in E1. rewrite Ho in E2.
  replace (fr + off + i) with (i + (fr / 8 + off / 8) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small i 8) by lia. lia.
Qed.

Lemma w4e2k_kn_shadow : forall i, 0 <= i < 112 ->
  2147450880 + 81584 <= B.AsanRT.shadow_addr (B.ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597.
Proof.
  intros i Hi. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.ACtlCutP.KNA.KIND_NAME.
  split; Z.div_mod_to_equations; lia.
Qed.

(* The carried bundle FRAC across a memory step that keeps the registers it pins, the stack words above sp and the
   frame header, and leaves the 392 frame-shadow bytes readable. *)
Lemma w4e2k_FRAC_keep : forall (cx : B.ACtlCut.ctlcx) fr sel regs R (m m' : word -> option byte),
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
  pose proof w4e2k_P64 as P64.
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
    { intros a v H1 H2 Hq. apply (w4e2k_bytes_keep m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8.
      intros x Hx. apply KS. lia. }
    refine (conj (HQ _ _ _ _ Hq336) (conj (HQ _ _ _ _ Hq48) (conj (HQ _ _ _ _ Hq40)
      (conj _ (conj _ (conj _ (conj _ _)))))));
      try lia.
    + apply (w4e2k_bytes_keep m m' _ _ Hqh0). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + apply (w4e2k_bytes_keep m m' _ _ Hqh16). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
    + change (Z.to_nat B.ACtlCutP.FRAME_SHADOW) with 392%nat in Hshl |- *.
      destruct Hsh as (Hs0 & Hs1 & _). rewrite Hshl in Hs1.
      destruct (w4e2k_bytes_of_mrd m' 392 (B.ACtlCutP.Sfr fr) Hs0 Hs1 KSh) as (sh' & Hl & Hb).
      exists sh'. split; [exact Hb | exact Hl].
    + assert (Hlen : length (B.ACtlCutP.saved_bytes cx) = 104%nat).
      { unfold B.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
      apply (w4e2k_bytes_keep m m' _ _ Hsaved). rewrite Hlen. intros x Hx. apply KS. lia.
    + apply (w4e2k_bytes_keep m m' _ _ Htr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply KF. lia.
Qed.

Lemma w4e2k_bv_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma w4e2k_signed_nonneg : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of a frame address, by its offset from the 8-aligned frame base. *)
Lemma w4e2k_sh_frame : forall fr x, fr mod 8 = 0 -> fr <= x ->
  B.AsanRT.shadow_addr x = B.ACtlCutP.Sfr fr + (x - fr) / 8 /\
  8 * ((x - fr) / 8) <= x - fr < 8 * ((x - fr) / 8) + 8.
Proof.
  intros fr x Hf Hx. unfold B.ACtlCutP.Sfr, B.AsanRT.shadow_addr.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as E1. rewrite Hf in E1.
  pose proof (Z.div_mod (x - fr) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (x - fr) 8 ltac:(lia)) as E3.
  split; [|lia].
  assert (Ex : x = (x - fr) + (fr / 8) * 8) by lia. rewrite Ex at 1. rewrite Z.div_add by lia. lia.
Qed.

Lemma w4e2k_hull_in : forall x n s, 0 <= x -> 0 < n ->
  Reusable.YG0f.shadow_addr x / 8 * 8 <= s < Reusable.YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8.
Proof.
  intros x n s Hx Hn Hs.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* T5 at a call site: ctrl's addressable (mrd of the shadow bytes) gives the core's range_addressable over the view,
   where the shadow bytes are visible (aview_vis_mrd). *)
Lemma w4e2k_range_addr : forall (W : Reusable.YA0n.world segs) mem p n,
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
    destruct Hk as [Hk|Hk]; [left | right]; rewrite w4e2k_signed_nonneg by lia; lia.
Qed.

Lemma w4e2k_hull_vis : forall (W : Reusable.YA0n.world segs) mem x n, 0 <= x -> 0 < n ->
  (forall s, B.AsanRT.shadow_addr x - 7 <= s < B.AsanRT.shadow_addr (x + n - 1) + 8 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem s) ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x n.
Proof.
  intros W mem x n Hx Hn H s Hs. apply (Reusable.YCbq.aview_some_of_apresent segs). apply H.
  exact (w4e2k_hull_in x n s Hx Hn Hs).
Qed.

(* mrd at a visible address outside the written range, from a munch_vis post. *)
Lemma w4e2k_q64_of_c8 : forall m a v, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.C8 (Z_to_bv 64 v)] ->
  B.ACtlCutP.q64 m a v.
Proof.
  intros m a v ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

Lemma w4e2k_bytes_of_cb : forall m a n bs, lib.Lib.Step.rw_cells rsegs m a [lib.Lib.Cells.CB n bs] ->
  lib.Lib.Mem.bytes_at rsegs m a bs.
Proof.
  intros m a n bs ((_ & H) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in H. rewrite app_nil_r in H.
  exact H.
Qed.

(* The entry's gp (the core's afn_pre inside the lib pre). *)
Lemma w4e2k_gp : forall cx, B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  lib.Reusable.YK11.getr (B.ACtlCut.c_regs cx) 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B).
Proof.
  intros cx ((HAF & _) & _). destruct HAF as (_ & _ & _ & Hgp & _). exact Hgp.
Qed.

Lemma w4e2k_amem_frame : forall fr d n, 4096 <= fr -> fr + 4096 <= lib.Reusable.YM05.alloc_ceiling ->
  (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/ Reusable.YG0f.kHighMemBeg <= fr) ->
  fr <= d -> d + n <= fr + 4096 -> Reusable.YG0d.amem_range d n.
Proof.
  intros fr d n H0 H1 H2 H3 H4. pose proof Reusable.YG0f.ASAN_CEIL_range as (HC & _).
  unfold Reusable.YG0f.ASAN_CEIL in HC. unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd,
    Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd, Reusable.YG0f.kLowShadowBeg in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   CALL-TRANSPORT TOOLKIT (the w4e2m_ lemmas).  Ported from a Theorem Labs lane's PROVED local helpers (lib/B/ACtlW4f.v,
   lines 324-518 and 889-1352 (at head lib/B/ACtlW4f.v:324-518 and :889-1352; from a working branch c8fda648d4e); renamed w4f_ -> w4e2m_
   aview_vis_mrd, a Section hypothesis there on that working branch (in this tree's ACtlW4f.v a Local Notation for the proved B.ProgWorld.aview_vis_mrd), is ProgWorld's proved lemma here (the Local Notation at :530)).  Run seating
   (w4e2m_enter / w4e2m_run / w4e2m_exit), the register transports of the cut bundles (w4e2m_ ... _tr), and the
   transports of FRAC / HB / FTK / FTURN / IFS / LK across a call whose post keeps the raw bytes (MKEPT) of the
   regions they read (w4e2m_bcmp_ ...), with the frame / block / KIND_NAME keeps from a view kept outside a
   window.  Each is proved from the core (YCbq, YG0d's AR laws, the journal), lib/Lib and B's ProgBridge; none is
   a hypothesis. *)

Local Notation getr := lib.Reusable.YK11.getr.

(* A cut state as a footprint run's start state: lib/Lib's MS over the canonical register map (Regs6ss.mkR_of),
   which the walk does not tell apart from the cut's map (YA0nR.SRr_xregs_eqv). *)
Lemma w4e2m_enter : forall (W : Reusable.YA0n.world segs) pc regs mem md Q,
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
Lemma w4e2m_run : forall (W : Reusable.YA0n.world segs) ms md RNG (P : machine_state -> Prop) Q,
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
Lemma w4e2m_exit : forall (W : Reusable.YA0n.world segs) pc R mem md Q,
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R mem md) Q ->
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Reusable.YK11.seg_rom segs)) md) Q.
Proof. intros W pc R mem md Q H. rewrite <- B.ProgBridge.cfg_at_MS. exact H. Qed.

(* The journal across a stretch that writes no memory (YCbq.ajournal_exec, empty write set). *)
Lemma w4e2m_aj_nowrite : forall cx own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ);
    [intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity | exact Hs |
     intros a Ha; destruct Ha].
Qed.

(* A stack range inside the journal's present window [c_sp cx - LLVMF_STK, c_sp cx) is visible. *)
Lemma w4e2m_vis_stack : forall cx own ly3 S3 W3 mem3 md3 k lo len,
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
Lemma w4e2m_frame_at : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HG1.
  pose proof HJ as (_ & Hly & _).
  rewrite (HG1 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
  unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity.
Qed.

Lemma w4e2m_frame_bounds : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof HJ as (HAR & _).
  rewrite (w4e2m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (H1 & H2 & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2. lia.
Qed.

Lemma w4e2m_vis_frame : forall cx ly3 S3 W3 mem3 md3 k fr lo len,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr <= lo -> lo + len <= fr + 4096 -> 0 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo len HJ HF HG1 H1 H2 H3.
  pose proof (w4e2m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (B1 & B2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  pose proof (w4e2m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  split; [lia |]. split; [lia |].
  intros a Ha.
  refine (proj1 (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _))).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

(* A spill slot read at the spill base of FRAC. *)
Lemma w4e2m_spill : forall regs m off v A,
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
Ltac w4e2m_rw_regs :=
  repeat match goal with
  | E : getr ?R ?r = getr ?R0 ?r |- context [getr ?R ?r] => rewrite E
  end.
Ltac w4e2m_tr := intros; w4e2m_rw_regs; assumption.

Lemma w4e2m_rgv_tr : forall R R0 r v, getr R r = getr R0 r -> ACtlCut.rgv R0 r v -> ACtlCut.rgv R r v.
Proof. unfold ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_spill_tr : forall R R0 m off v, getr R 9 = getr R0 9 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m off v.
Proof. unfold ACtlCutP.spill, ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_FRAC_tr : forall cx fr sel R R0 m,
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m.
Proof. unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ. w4e2m_tr. Qed.
Lemma w4e2m_FLI_tr : forall cx fr R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m.
Proof. unfold ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_LK_tr : forall cx fr j R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m.
Proof. unfold ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_FTK_tr : forall cx j fr R R0 m,
  getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 -> getr R 25 = getr R0 25 ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m.
Proof. unfold ACtlCutP.FTK, ACtlCutP.spill, ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_FTURN_tr : forall cx j phi R R0 m, getr R 9 = getr R0 9 ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m.
Proof. unfold ACtlCutP.FTURN, ACtlCutP.spill, ACtlCut.rgv. w4e2m_tr. Qed.
Lemma w4e2m_IFS_tr : forall cx fr j R R0 m, ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m.
Proof. unfold ACtlCutP.IFS, ACtlCutP.FSj, ACtlCutP.FSb. w4e2m_tr. Qed.

(* The raw bytes of [lo, hi) are the same in m and m'. *)
Local Notation MKEPT m m' lo hi :=
  (forall w4e2m_x : Z, lo <= w4e2m_x < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 w4e2m_x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 w4e2m_x)).

(* ---- the one step from a view-level post to a raw fact: a visible address whose view is kept keeps its byte ---- *)
Lemma w4e2m_bcmp_pt : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) a,
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
Lemma w4e2m_bcmp_vis_of_aview : forall (H : word -> bool) (m : word -> option byte) a,
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
Lemma w4e2m_bcmp_bytes : forall (m m' : word -> option byte) a bs,
  MKEPT m m' a (a + Z.of_nat (length bs)) ->
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H). split; [exact H0 |]. split; [exact H1 |].
  intros i Hi. exact (eq_trans (K (a + Z.of_nat i) ltac:(lia)) (H i Hi)).
Qed.

Lemma w4e2m_bcmp_q64 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 8) ->
  ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.q64 in *. apply (w4e2m_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

Lemma w4e2m_bcmp_u32 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 4) ->
  ACtlCutP.u32 m a v -> ACtlCutP.u32 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.u32 in *. apply (w4e2m_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le4. exact K.
Qed.

Lemma w4e2m_bcmp_b8 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 1) ->
  ACtlCutP.b8 m a v -> ACtlCutP.b8 m' a v.
Proof. intros m m' a v K H. unfold ACtlCutP.b8 in *. exact (w4e2m_bcmp_bytes m m' a [Z_to_bv 8 v] K H). Qed.

Lemma w4e2m_bcmp_sp : forall R R0 (m m' : word -> option byte) A csp off v,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> 0 <= off <= 440 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros R R0 m m' A csp off v HA E9 H0 H1 H2 K Hoff Hs.
  pose proof (w4e2m_spill R0 m off v A Hs HA ltac:(lia) ltac:(lia)) as Hq.
  exists A. split; [exact (w4e2m_rgv_tr R R0 9 A E9 HA) |].
  apply (w4e2m_bcmp_q64 m m' (A + off) v); [intros x Hx; apply K; lia | exact Hq].
Qed.

Lemma w4e2m_bcmp_addr : forall (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |].
  exists b. split; [| exact Hok]. exact (eq_trans (K i Hi) Hb).
Qed.

(* A raw-present range stays a stack range (wview / mrd of a present byte). *)
Lemma w4e2m_bcmp_stk : forall (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.stk segs m lo hi -> lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi Hp (H0 & H1 & _). split; [exact H0 |]. split; [exact H1 |].
  intros a Ha. destruct (Hp a Ha) as [b Hb]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* ---- the callee's view-level arguments from raw facts at visible addresses ---- *)
Lemma w4e2m_bcmp_signed : forall b : byte, 0 <= bv_signed b <= 7 -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4e2m_bcmp_range_addr : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) p n,
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
    + left. rewrite (w4e2m_bcmp_signed b ltac:(lia)). exact Hok.
    + right. rewrite (w4e2m_bcmp_signed b ltac:(lia)). lia.
Qed.

(* The byte the view reads at a visible address of a bytes_at fact. *)
Lemma w4e2m_bcmp_aview_at : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) x l k,
  lib.Lib.Mem.bytes_at segs m x l -> (k < length l)%nat ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (x + Z.of_nat k)) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (x + Z.of_nat k) =
  option_map (fun b : byte => bv_unsigned b) (nth_error l k).
Proof.
  intros W m x l k (_ & _ & H) Hk Hv. rewrite (aview_vis_mrd W m _ Hv). f_equal. exact (H k Hk).
Qed.

(* The bcmp result: the view equality of the n compared bytes is the equality of the two byte lists. *)
(* ---- visibility of the walk's owned frame, its shadow and the live blocks ---- *)
Lemma w4e2m_bcmp_frame_present : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4e2m_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  refine (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512. exact Ha.
Qed.

Lemma w4e2m_bcmp_block_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n i,
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
  apply (w4e2m_bcmp_vis_of_aview _ mem).
  - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
  - intros Him. apply segs_low in Him. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.kLowMemEnd in Him.
    Z.div_mod_to_equations. lia.
  - rewrite Hs. discriminate.
Qed.

(* ---- a view kept outside a window [wlo, whi) gives the raw bytes of the frame, its shadow, the spill area and
   KNT's image table (for the walk's cuts: everything the frame-loop bodies read except the live block) ---- *)
Lemma w4e2m_bcmp_frame_kept : forall cx ly3 S3 W3 mem3 md3 k fr (mem2 : word -> option byte) sp,
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
  pose proof (w4e2m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hcl & Hlsp & Hshi & Hshi47 & _). unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  assert (HS : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= lib.Reusable.YM05.alloc_ceiling).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  refine (conj _ (conj _ (conj _ _))).
  - intros a Ha. apply (w4e2m_bcmp_pt W3); [exact (proj1 (Hpres a ltac:(lia))) | apply Hk; lia].
  - intros a Ha. apply (w4e2m_bcmp_pt W3); [| apply Hk; lia].
    exact (proj1 (w4e2m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_introl Ha))).
  - intros a Ha. apply (w4e2m_bcmp_pt W3); [| apply Hk; lia].
    refine (proj1 (w4e2m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_intror _))).
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
      Reusable.YG0f.SHADOW_OFF in *. lia.
  - intros a Ha. unfold ACtlCutP.KNA.KIND_NAME in Ha.
    apply (w4e2m_bcmp_pt W3); [apply Himg; lia | apply Hk; lia].
Qed.

(* The same for a live block and its shadow (the block law gives the bytes present, the shadow law the shadow
   bytes' view, hence their visibility). *)
Lemma w4e2m_bcmp_block_kept : forall ly S (W : Reusable.YA0n.world segs) mem md (mem2 : word -> option byte)
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
  - intros a Ha. apply (w4e2m_bcmp_pt W); [exact (proj1 (proj1 (Hpr a Ha))) | apply Hk; lia].
  - intros i Hi. apply (w4e2m_bcmp_pt W).
    + exact (w4e2m_bcmp_block_shadow_vis ly S W mem md p n i HAR Hin Hi).
    + apply Hk; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- the cut-body predicates across a call that keeps the raw bytes of the regions they read ---- *)
Lemma w4e2m_bcmp_FRAC : forall cx fr sel R R0 (m m' : word -> option byte),
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
  split; [exact (w4e2m_rgv_tr R R0 8 _ E8 Hr8) |].
  split; [exact (w4e2m_rgv_tr R R0 9 _ E9 Hr9) |].
  split; [rewrite E3; exact Hr3 |].
  split; [exact (w4e2m_rgv_tr R R0 19 _ E19 Hr19) |].
  split; [exact (w4e2m_rgv_tr R R0 26 _ E26 Hr26) |].
  do 8 (split; [assumption |]).
  split; [apply (w4e2m_bcmp_q64 m m' (A + 336) fr); [intros x Hx; apply KS; lia | exact Q336] |].
  split; [apply (w4e2m_bcmp_q64 m m' (A + 48) sel); [intros x Hx; apply KS; lia | exact Q48] |].
  split; [apply (w4e2m_bcmp_q64 m m' (A + 40) fr); [intros x Hx; apply KS; lia | exact Q40] |].
  split; [apply (w4e2m_bcmp_q64 m m' fr _); [intros x Hx; apply KF; lia | exact Qhdr] |].
  split; [apply (w4e2m_bcmp_q64 m m' (fr + 16) _); [intros x Hx; apply KF; lia | exact Q16] |].
  split; [exists sh; split; [apply (w4e2m_bcmp_bytes m m' _ sh); [intros x Hx; apply KSH; lia | exact Hsh] |
    exact Lsh] |].
  split; [apply (w4e2m_bcmp_bytes m m' _ _); [intros x Hx; apply KS; rewrite Lsv in Hx; lia | exact Hsav] |].
  apply (w4e2m_bcmp_q64 m m' (fr + 4088) _); [intros x Hx; apply KF; lia | exact Q4088].
Qed.

Lemma w4e2m_bcmp_HB : forall (m m' : word -> option byte) phi len,
  (forall i, 0 <= i < B.ACtlK.a_size len ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof. intros m m' phi len K (H0 & H1). split; [exact H0 | exact (w4e2m_bcmp_addr m m' phi _ K H1)]. Qed.

Lemma w4e2m_bcmp_FTK : forall cx j fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 ->
  getr R 25 = getr R0 25 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m'.
Proof.
  intros cx j fr R R0 m m' A csp HA E9 E22 E24 E25 H0 H1 H2 KS (H184 & H22 & H24 & H272 & H25).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (w4e2m_bcmp_sp R R0 m m' A csp 184 _ HA E9 H0 H1 H2 KS ltac:(lia) H184).
  - exact (w4e2m_rgv_tr R R0 22 _ E22 H22).
  - exact (w4e2m_rgv_tr R R0 24 _ E24 H24).
  - exact (w4e2m_bcmp_sp R R0 m m' A csp 272 _ HA E9 H0 H1 H2 KS ltac:(lia) H272).
  - exact (w4e2m_rgv_tr R R0 25 _ E25 H25).
Qed.

Lemma w4e2m_bcmp_FTURN : forall cx j phi R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> MKEPT m m' phi (phi + ACtlCutP.flen cx j) ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m'.
Proof.
  intros cx j phi R R0 m m' A csp HA E9 H0 H1 H2 KS KB (H224 & H232 & Hphi & Hlen).
  unfold ACtlCutP.flen in KB.
  refine (conj _ (conj _ (conj _ Hlen))).
  - exact (w4e2m_bcmp_sp R R0 m m' A csp 224 _ HA E9 H0 H1 H2 KS ltac:(lia) H224).
  - exact (w4e2m_bcmp_sp R R0 m m' A csp 232 _ HA E9 H0 H1 H2 KS ltac:(lia) H232).
  - apply (w4e2m_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
Qed.

(* IFS, FLI and LK read the frame only at or above fr + 2560 (OUR 2624, ID 2688, FG 2768, FS 2880) and its shadow
   only at or above Sfr fr + 320, so they need the bytes kept there only (changed from W4e1's whole-frame premises:
   the stores of S_F24 / S_F25 / S_F29 hit [fr + 128, fr + 168) and its shadow). *)
Lemma w4e2m_bcmp_IFS : forall cx fr j R R0 (m m' : word -> option byte),
  MKEPT m m' (fr + 2560) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 320) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' KF KSH ((HID & Hidok) & (HFG & Hfgok) & (Hhave & Hnb & Hbody & Had & HFI)).
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LBD.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb in *.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj _ HFI)))))).
  - apply (w4e2m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HID].
  - apply (w4e2m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HFG].
  - apply (w4e2m_bcmp_u32 m m' _ _); [intros x Hx; apply KF; lia | exact Hhave].
  - apply (w4e2m_bcmp_b8 m m' _ _); [intros x Hx; apply KF; lia | exact Hnb].
  - apply (w4e2m_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact Hbody].
  - apply (w4e2m_bcmp_addr m m' _ _); [| exact Had]. intros i Hi. apply KSH.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma w4e2m_bcmp_FLI : forall cx fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' (fr + 2560) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 320) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m'.
Proof.
  intros cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Hs; exact (w4e2m_bcmp_sp R R0 m m' A csp off v HA E9 H0 H1 H2 KS Ho Hs)).
  assert (AD : forall p n, fr + 2560 <= p -> p + n <= fr + 4000 -> 0 <= n ->
                 B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n).
  { intros p n Hp1 Hp2 Hn Hp. apply (w4e2m_bcmp_addr m m' p n); [| exact Hp].
    intros i Hi. apply KSH. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (LKN : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  unfold ACtlCutP.FLI in *.
  destruct HFLI as (H27 & HFLI).
  split; [exact (w4e2m_rgv_tr R R0 27 _ E27 H27) |].
  do 21 (destruct HFLI as (Hsp & HFLI); split; [apply SP; [lia | exact Hsp] | clear Hsp]).
  destruct HFLI as (Had & Hstk & HRAD & HKNT & Hs168 & Hs88).
  split; [apply AD; [lia | lia | lia | exact Had] |].
  split; [exact (w4e2m_bcmp_stk m m' fr _ Hpr Hstk) |].
  split.
  { unfold ACtlCutP.RAD, ACtlCutP.fragb in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
    split; [apply AD; [lia | lia | lia | exact Ra1] |].
    split; [apply AD; [lia | lia | lia | exact Ra2] |].
    apply AD; [lia | lia | lia | exact Ra3]. }
  split.
  { unfold ACtlCutP.KNT in *. destruct HKNT as (Hkb & _). split; [| exact HKA].
    apply (w4e2m_bcmp_bytes m m' _ _); [intros x Hx; apply KK; rewrite LKN in Hx; lia | exact Hkb]. }
  split; [apply SP; [lia | exact Hs168] | apply SP; [lia | exact Hs88]].
Qed.

Lemma w4e2m_bcmp_LK : forall cx fr j R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' (fr + 2560) (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr + 320) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr (Hj & S240 & HOUR & HFLI).
  refine (conj Hj (conj (w4e2m_bcmp_sp R R0 m m' A csp 240 _ HA E9 H0 H1 H2 KS ltac:(lia) S240) (conj _ _))).
  - unfold ACtlCutP.OURb in *. apply (w4e2m_bcmp_bytes m m' _ _); [| exact HOUR].
    rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply KF. lia.
  - exact (w4e2m_bcmp_FLI cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI).
Qed.


(* A live heap block is apart from every live fake frame (B.ProgWorldBlkApart.ctl_block_apart_fs, proved, +
   YG0s.frame_facts: the frame lies inside the fake-stack region [ly_F, ly_F + kFakeStackSize)). *)
Lemma w4e2_block_frame_apart : forall ly S (W : Reusable.YA0n.world segs) mem md p n cid pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  In (cid, pos) (Reusable.YG01.frames S) ->
  p + Reusable.YG00.req_size n <= Reusable.YG0f.frame_addr ly cid pos \/
  Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid <= p.
Proof.
  intros ly S W mem md p n cid pos HAR Hb Hf.
  pose proof (Reusable.YG0s.frame_facts B ly S _ cid pos (proj1 HAR) Hf) as (C0 & _ & _ & _ & _ & F1 & F2 & _).
  assert (Hc : 0 <= cid * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
  unfold Reusable.YG0f.kFakeFramesOff in F1.
  destruct (B.ProgWorldBlkApart.ctl_block_apart_fs B LAWS ly S W mem md p n HAR Hb) as [H|H];
    unfold Reusable.YG0f.frame_addr; [left | right]; lia.
Qed.

(* The bytes of a rw_cells run off the image are raw present. *)
Lemma w4e2_rw_cells_present : forall m a cs x, lib.Lib.Step.rw_cells B.Img0.rsegs m a cs ->
  a <= x < a + Z.of_nat (lib.Lib.Cells.cells_size cs) -> 0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
  exists b, m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m a cs x ((Hwf & (H0 & H1 & H)) & _) Hx Hx64 Hni.
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as Hlen.
  assert (Hi : (Z.to_nat (x - a) < length (lib.Lib.Cells.cells_bytes cs))%nat) by (rewrite Hlen; lia).
  pose proof (H _ Hi) as E. replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  destruct (nth_error (lib.Lib.Cells.cells_bytes cs) (Z.to_nat (x - a))) as [b|] eqn:En.
  - exists b. exact (w4e2k_mrd_raw m x b Hx64 Hni E).
  - apply nth_error_None in En. lia.
Qed.

(* A register moved from another index of the cut's map. *)
Lemma w4e2_rgv_move : forall (R regs : bvmap 5 word) (r r' : bv 5) v,
  BK11.getr R r = Sem.reg_get regs r' -> bv_eqb r 0 = false -> bv_eqb r' 0 = false ->
  ACtlCut.rgv regs r' v -> ACtlCut.rgv R r v.
Proof.
  intros R regs r r' v E Hr Hr' H. unfold ACtlCut.rgv, CK11.getr in *. unfold BK11.getr in E.
  rewrite Hr in *. rewrite Hr' in H. rewrite E. exact H.
Qed.


(* A live fake frame of class 6 lies above the image (YG0s.frame_facts: frame_addr = ly_F + fs_frame_off, with
   ly_F >= 4096 in application memory and fs_frame_off 6 pos >= kFakeFramesOff + 6 * 2^20). *)
Lemma w4e2_frame_high : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  6332416 <= Reusable.YG0f.frame_addr ly 6 pos.
Proof.
  intros ly S W mem md pos HAR Hf.
  pose proof (Reusable.YG0s.frame_facts B ly S _ 6 pos (proj1 HAR) Hf) as (_ & _ & Happ & _ & _ & F1 & _).
  unfold Reusable.YG0f.in_app in Happ. unfold Reusable.YG0f.kFakeFramesOff in F1.
  change (6 * 2 ^ 20) with 6291456 in F1. unfold Reusable.YG0f.frame_addr. lia.
Qed.
(* ---------------------------------------------------------------------------------------------------------
   CALL-STAGE HELPERS (proved here). *)

(* (lib/B/ACtlW4e1.v's w4_ctlrt, ctl_rt from ctlrt_of_AR after a world call, is not ported: no stage of this file
   makes a world call, so ctl_rt_C (route (C)) crosses every program callee and store by w4e2k_ctlrtC_run.) *)
(* A cut register as the run's register word (the runs name lib/Lib's reg_get; the cut's rgv the core's getr). *)
Lemma w4e2w_rgv_reg : forall (regs : bvmap 5 word) (r : bv 5) v,
  bv_eqb r 0 = false -> ACtlCut.rgv regs r v -> LinuxProcessSemantics.Riscv.Sem.reg_get regs r = Z_to_bv 64 v.
Proof. intros regs r v E H. unfold ACtlCut.rgv, lib.Reusable.YK11.getr in H. rewrite E in H. exact H. Qed.

(* The turn's 50-byte record. *)
Lemma w4e2w_tg_len : forall inp jn, length (ACtlCutP.SM.t_g inp jn) = 50%nat.
Proof.
  intros inp jn. unfold ACtlCutP.SM.t_g, ACtlCutP.SM.fr50.
  rewrite length_firstn, length_app, repeat_length. lia.
Qed.

Lemma w4e2w_skipn_cons : forall (l : list byte) (n : nat) (d : byte), (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  induction l as [|x l IH]; intros [|n] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

(* The two record bytes Phi[18], Phi[19] as the first two bytes of the turn block t_blk = bsl g 18 32. *)
(* A sub-range of an addressable range. *)
Lemma w4e2w_addr_sub : forall (m : word -> option byte) p n q k,
  B.AsanRT.addressable m p n -> p <= q -> 0 <= k -> q + k <= p + n -> B.AsanRT.addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hqk.
  split; [lia|]. split; [exact Hk|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* Every shadow byte between the shadow bytes of x and y is the shadow byte of an address between them. *)
Lemma w4e2w_sh_between : forall x y a, 0 <= x <= y ->
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
Lemma w4e2w_munch_kept : forall Wr (m m' : word -> option byte) lo hi,
  lib.Lib.Frame.munch Wr m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> lib.Lib.Frame.outside Wr x) -> MKEPT m m' lo hi.
Proof. intros Wr m m' lo hi MU H0 H1 Ho x Hx. exact (w4e2k_mrd_munch Wr m m' x MU ltac:(lia) (Ho x Hx)). Qed.

(* FM across a call that keeps the spill area. *)
(* A stretch whose post is itself a run (a `_pre_F` lemma with a continuation premise, then the callee's run). *)
Lemma w4e2w_evtF_join : forall RNG (Q : machine_state -> Prop) ms,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG (lib.Lib.ExecF.evtF B.Img0.rsegs RNG Q) ms ->
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG Q ms.
Proof. intros RNG Q ms H. exact (lib.Lib.ExecF.evtF_cut _ _ _ _ _ H (fun _ h => h)). Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82878_at j (0x82878) --S_F24--> B82888_at j.
   0x82878 ld s6,312(s1) (s6 = blk = phi + 18); mv a0,s6; mv a1,s5 (s5 = fr + 128); jal reac_ports_parse
   (entry 0x883d0, ra 0x82888).  No branch, no store, no instrumented check (UB Seg/F24.v:3-11).  The callee reads
   the 20 ports bytes [phi + 18, phi + 38), returns a0 = t_rp j, and writes the three port words at q = fr + 128
   (t_rp j = 0) or only its 16 stack bytes (else).  SINK BRANCHES: none (objdump L85355-L85358). *)
Lemma seg_F24 : forall POST (j : nat),
  ctl_from POST (ix C_B82888_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82878_at [Z.of_nat j]).
Proof.
  intros POST j H888 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  destruct HBODY as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82878_at ACtlCutP.ixn ACtlCutP.fcutp_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & H18 & H20 & HFTURN & HLK & HFTL & H22 & HIFS & HF27K &
    H20' & H23 & S184 & H21 & U0 & U4 & U8 & HAq & HGAP & Hwin).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4e2k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1)
    as (Efr & _ & Hfr4096 & Hfrc & Happ & Himgfr & Hnimg & Hfrpres & Hshpres & _ & Hcspc & Hcsp47 & Hstkpres).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as (Hc1 & Hc2).
  unfold Reusable.YCfn.LLVMF_STK in Hcspc, Hstkpres.
  pose proof HJ as (HAR & _).
  pose proof HRT as (Hcells & _).
  pose proof HF27K as (HLK' & H18' & H27 & Hphi0 & Hphi50 & Hflen & Hblk & S312 & S272 & H24 & S104 & S136).
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & Hpapp & Hbpr & _ & Hnrange).
  assert (Hfin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (w4e2_block_frame_apart ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hin Hfin) as Hapart.
  rewrite <- Efr in Hapart. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hapart.
  assert (Hreq : B.ACtlK.a_size (ACtlCutP.flen cx j) = Reusable.YG00.req_size (ACtlCutP.flen cx j) /\
                 ACtlCutP.flen cx j <= Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hsp2 : bv_unsigned (Sem.reg_get regs3 2) = sp).
  { rewrite (w4e2w_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  pose proof (w4e2_blk_len (ACtlCut.c_in cx) j) as Lblk.
  pose proof (w4e2_spill regs3 mem3 A 312 _ Hr9 ltac:(lia) ltac:(lia) S312) as Q312.
  (* the frame's placement: below the stack window, in application memory, above the image *)
  assert (HSf : ACtlCutP.Sfr fr + 512 <= ART.HIGHMEM_BEG /\ ART.LOWMEM_END <= ACtlCutP.Sfr fr).
  { unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, ART.LOWMEM_END, ART.HIGHMEM_BEG.
    Z.div_mod_to_equations. lia. }
  unfold ART.HIGHMEM_BEG, ART.LOWMEM_END in HSf.
  (* 0x82878 -> 0x883d0 (f24_pre_F) -> the callee -> 0x82888, one lift *)
  apply w4e2m_enter.
  eapply (w4e2_lift W3 _ md3).
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply LX.evtF_cut.
    { eapply (B.Prog.Seg.F24F.f24_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (A := A) (p := phi + 18) (q := fr + 128).
      - exact (w4e2w_rgv_reg _ 9 _ eq_refl Hr9).
      - exact (w4e2w_rgv_reg _ 21 _ eq_refl H21).
      - lia.
      - lia.
      - exact Q312.
      - apply B.ProgBridge.rng_of_visible.
        apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
    intros ms1 Ems1. cbv beta in Ems1. subst ms1.
    eapply (B.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (p := phi + 18) (q := fr + 128) (lo := sp - 16) (bs := SM.t_pbs (ACtlCut.c_in cx) j);
      unfold B.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; rewrite ?Hsp2.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - apply w4e2k_stk_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hstkpres x ltac:(lia))).
    - lia.
    - intros _ _. split; [rewrite w4e2_pbs_blk20, length_firstn, Lblk; reflexivity|].
      rewrite w4e2_pbs_blk20; apply w4e2_bytes_firstn; [exact Hblk | rewrite Lblk; lia].
    - intros _ _. split; [Z.div_mod_to_equations; lia|].
      split; [apply w4e2k_wr_raw; [lia | lia |]; intros x Hx; exact (proj2 (Hfrpres x ltac:(lia)))|].
      split; [destruct Hapart as [Ha|Ha]; destruct Hreq; lia|].
      split; lia.
    - intros _ _. split; [exact Hcells|].
      split; [apply (w4e2w_addr_sub mem3 phi _ (phi + 18) 20 (proj2 HHB)); destruct Hreq; lia | exact HAq].
    - intros _ _ x Hx. cbn [lib.Lib.Frame.outside]. split; [|split; [|exact I]].
      + unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
        lia.
      + unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
          B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
        unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
        lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - intros _ _.
      split; [apply B.ProgBridge.rng_of_visible; unfold B.AsanRT.GOT_CELL_K;
              split; [lia|]; split; [lia|]; intros a Ha; apply Himg; lia|].
      split; [apply B.ProgBridge.rng_of_visible; unfold B.AsanRT.CELL_K;
              split; [lia|]; split; [lia|]; intros a Ha; apply Himg; lia|].
      split.
      { apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. destruct Hreq. exact (proj1 (proj1 (Hbpr a ltac:(lia)))). }
      split.
      { apply B.ProgBridge.rng_of_visible.
        split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        intros a Ha.
        destruct (w4e2w_sh_between (phi + 18) (phi + 37) a ltac:(lia)
                    ltac:(unfold B.AsanRT.shadow_addr in *; lia)) as (z & Hz & <-).
        replace z with (phi + (z - phi)) by lia.
        apply (w4e2m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). destruct Hreq. lia. }
      split.
      { apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hfrpres a ltac:(lia))). }
      apply B.ProgBridge.rng_of_visible.
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
      intros a Ha.
      assert (Hx : ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512)
        by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *;
            Z.div_mod_to_equations; lia).
      exact (proj1 (Hshpres a Hx)). }
  intros ms' md' (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & WM & _ &
    Hstk' & HIF) Hgr Hhid Hsbm.
  unfold B.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME in HIF. rewrite Hsp2 in HIF, Hstk'.
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x82888) = Z_to_bv 64 0x82888) by (apply bv_eq; reflexivity).
  rewrite Eret.
  apply (w4e2m_exit W3 0x82888).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  set (Wr := [(sp - 16, sp); (fr + 128, fr + 128 + 12)]).
  assert (MU : lib.Lib.Frame.munch Wr mem3 m').
  { destruct (Prog.RcLeaf.ports_ok (phi + 18) (fr + 128) (SM.t_pbs (ACtlCut.c_in cx) j)).
    - exact (proj2 (proj2 (proj2 HIF))).
    - eapply lib.Lib.Frame.munch_weaken; [| exact HIF]. intros x Hx. cbn [lib.Lib.Frame.outside Wr] in Hx |- *.
      destruct Hx as (H1 & _). split; [exact H1 | exact I]. }
  assert (Hout : forall x, (x < sp - 16 \/ sp <= x) -> (x < fr + 128 \/ fr + 140 <= x) ->
                   lib.Lib.Frame.outside Wr x)
    by (intros x H1 H2; cbn [lib.Lib.Frame.outside Wr]; split; [lia | split; [lia | exact I]]).
  assert (Hgrow : forall x : word, mem3 x <> None -> m' x <> None) by exact Hgr.
  assert (HW : forall a, ~ lib.Lib.Frame.outside Wr a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha.
    assert (Hr : sp - 16 <= a < sp \/ fr + 128 <= a < fr + 140).
    { destruct (Z_lt_le_dec a (sp - 16)) as [h1|h1]; destruct (Z_lt_le_dec a sp) as [h2|h2];
        destruct (Z_lt_le_dec a (fr + 128)) as [h3|h3]; destruct (Z_lt_le_dec a (fr + 140)) as [h4|h4];
        try (left; lia); try (right; lia); exfalso; apply Ha; apply Hout; lia. }
    assert (Hni : ~ Reusable.YG0d.in_img segs a).
    { destruct Hr as [Hr|Hr]; [apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia|].
      apply Hnimg. lia. }
    split; [exact Hni|].
    assert (Hp : mem3 (lib.Lib.Mem.wa a) <> None).
    { destruct Hr as [Hr|Hr].
      - destruct (Hstkpres a ltac:(lia)) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
        rewrite Hb. discriminate.
      - destruct (Hfrpres a ltac:(lia)) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
        rewrite Hb. discriminate. }
    pose proof (Hgrow _ Hp) as Hp'. destruct (m' (lib.Lib.Mem.wa a)) as [b|]; [exists b; reflexivity | congruence]. }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4e2k_after_run cx ly3 S3 W3 mem3 md3 k m' md' Wr HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    assert (Hr : sp - 16 <= a < sp \/ fr + 128 <= a < fr + 140).
    { destruct (Z_lt_le_dec a (sp - 16)) as [h1|h1]; destruct (Z_lt_le_dec a sp) as [h2|h2];
        destruct (Z_lt_le_dec a (fr + 128)) as [h3|h3]; destruct (Z_lt_le_dec a (fr + 140)) as [h4|h4];
        try (left; lia); try (right; lia); exfalso; apply Ha; apply Hout; lia. }
    destruct Hr as [Hr|Hr].
    - apply w4e2k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia.
    - apply (w4e2k_awr_fr cx ly3 fr _ _ _ _ a Efr). lia. }
  assert (WM' : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m') by exact WM.
  pose proof (w4e2k_ctlrtC_run ly3 S3 mem3 m' Wr HRT MU WM' HW) as HRT'.
  assert (KEPT : forall x, 0 <= x < 2 ^ 64 -> (x < sp - 16 \/ sp <= x) -> (x < fr + 128 \/ fr + 140 <= x) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx H1 H2; exact (w4e2k_mrd_munch Wr mem3 m' x MU Hx (Hout x H1 H2))).
  assert (KSA : forall x : Z, A <= x < ACtlCut.c_sp cx ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KFhi : forall x : Z, fr + 2560 <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KSH : forall x : Z, ACtlCutP.Sfr fr + 320 <= x < ACtlCutP.Sfr fr + 512 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx. apply KEPT; [lia | lia |].
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *. Z.div_mod_to_equations. lia. }
  assert (Hkn : forall i, 0 <= i < 112 ->
             2147450880 + 81584 <= B.AsanRT.shadow_addr (ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597)
    by exact w4e2k_kn_shadow.
  assert (KK : forall x : Z, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { unfold ACtlCutP.KNA.KIND_NAME. intros x Hx. apply KEPT; lia. }
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx j) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. rewrite (proj1 Hreq) in Hi.
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    apply KEPT; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia. }
  assert (KB : forall x : Z, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; [lia | lia | destruct Hapart; lia]).
  assert (KF : forall x : Z, fr <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha. destruct (Hfrpres a ltac:(lia)) as (_ & b & Hb).
    assert (Hp' : m' (Z_to_bv 64 a) <> None) by (apply Hgrow; rewrite Hb; discriminate).
    destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | congruence]. }
  assert (HKA : B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112).
  { pose proof HLK as (_ & _ & _ & HFLI). unfold ACtlCutP.FLI in HFLI.
    destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & (_ & HKA0) & _).
    apply (w4e2m_bcmp_addr mem3 m' _ 112); [| exact HKA0].
    intros i Hi. pose proof (Hkn i Hi) as Hk'. apply KEPT; lia. }
  assert (KShr : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
             exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct (Hshpres x ltac:(lia)) as (_ & b & Hb). exists b.
    change (lib.Lib.Mem.wa x) with (Z_to_bv 64 x).
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    rewrite (KEPT x); [exact (w4e2k_raw_mrd _ _ _ Hb) | lia | |];
      unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *; Z.div_mod_to_equations; lia. }
  assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
  assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
  assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
  assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
  assert (E9 : getr R1 9 = getr regs3 9)
    by (transitivity (Z_to_bv 64 A); [reflexivity | symmetry; exact Hr9]).
  assert (E18 : getr R1 18 = getr regs3 18) by reflexivity.
  assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
  assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
  assert (E21 : getr R1 21 = getr regs3 21)
    by (transitivity (Z_to_bv 64 (fr + 128)); [reflexivity | symmetry; exact H21]).
  assert (E23 : getr R1 23 = getr regs3 23) by reflexivity.
  assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
  assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
  assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R1 m' off v)
    by (intros off v Ho Hs; exact (w4e2m_bcmp_sp R1 regs3 mem3 m' A (ACtlCut.c_sp cx) off v Hr9 E9 ltac:(lia)
                                     ltac:(lia) ltac:(lia) KSA Ho Hs)).
  assert (Hpq : phi + 18 <> 0 /\ fr + 128 <> 0) by lia.
  apply (H888 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82888_at ACtlCutP.ixn
    ACtlCutP.fcutp_body nth].
  split; [reflexivity|]. rewrite Nat2Z.id.
  split.
  { apply (w4e2k_FRAC_keep cx fr fr regs3 R1 mem3 m' HFRAC E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KShr].
    intros x Hx. rewrite HspZ in Hx. apply KEPT; lia. }
  exists phi.
  split; [exact Hperm|]. split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4e2m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  split; [exact (w4e2m_rgv_tr R1 regs3 18 _ E18 H18)|].
  split; [exact (w4e2m_rgv_tr R1 regs3 20 _ E20 H20)|].
  split.
  { apply (w4e2m_bcmp_FTURN cx j phi R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFTURN].
    intros x Hx. apply KB. destruct Hreq. lia. }
  assert (HLK1 : ACtlCutP.LK cx fr j R1 m')
    by exact (w4e2m_bcmp_LK cx fr j R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                ltac:(lia) KSA KFhi KSH KK HKA Hpr HLK).
  split; [exact HLK1|].
  split.
  { destruct HFTL as (T21 & T184 & T272 & T24 & T312).
    split; [exact (w4e2m_rgv_tr R1 regs3 21 _ E21 T21)|].
    split; [exact (SP 184 _ ltac:(lia) T184)|]. split; [exact (SP 272 _ ltac:(lia) T272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 T24)|]. exact (SP 312 _ ltac:(lia) T312). }
  split; [exact (w4e2m_bcmp_IFS cx fr (S j) R1 regs3 mem3 m' KFhi KSH HIFS)|].
  split.
  { (* F27K *)
    split; [exact HLK1|].
    split; [exact (w4e2m_rgv_tr R1 regs3 18 _ E18 H18')|].
    split; [exact (w4e2m_rgv_tr R1 regs3 27 _ E27 H27)|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|].
    split; [apply (w4e2m_bcmp_bytes mem3 m' (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; destruct Hreq; lia | exact Hblk]|].
    split; [exact (SP 312 _ ltac:(lia) S312)|]. split; [exact (SP 272 _ ltac:(lia) S272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 H24)|].
    split; [exact (SP 104 _ ltac:(lia) S104)|]. exact (SP 136 _ ltac:(lia) S136). }
  split.
  { unfold ACtlCut.rgv.
    transitivity (Z_to_bv 64 (if Prog.RcLeaf.ports_ok (phi + 18) (fr + 128) (SM.t_pbs (ACtlCut.c_in cx) j)
                              then 0 else -1)); [reflexivity|].
    rewrite (w4e2_rp_ok (phi + 18) (fr + 128) (ACtlCut.c_in cx) j ltac:(lia) ltac:(lia)). reflexivity. }
  split; [exact (w4e2m_rgv_tr R1 regs3 20 _ E20 H20')|].
  split; [exact (w4e2m_rgv_tr R1 regs3 23 _ E23 H23)|].
  split; [exact (SP 184 _ ltac:(lia) S184)|].
  split; [unfold ACtlCut.rgv; reflexivity|].
  split.
  { (* PORTS: the words the callee wrote (t_rp = 0) or F23's -7 words kept (t_rp <> 0) *)
    unfold ACtlCutP.PORTS, SM.t_rp.
    rewrite (w4e2_ports_ok_decl (phi + 18) (fr + 128) _ ltac:(lia) ltac:(lia)) in HIF.
    destruct (Prog.RcLeaf.decl (SM.t_pbs (ACtlCut.c_in cx) j)).
    - destruct HIF as (B0 & B1 & B2 & _).
      replace (fr + 128 + 4) with (fr + 132) in B1 by lia. replace (fr + 128 + 8) with (fr + 136) in B2 by lia.
      split; [intros _; split; [exact B0|]; split; [exact B1 | exact B2]|].
      intros C. exfalso. apply C. reflexivity.
    - split; [intros C; discriminate C|].
      intros _.
      assert (K1 : forall x, fr + 128 <= x < fr + 140 ->
                 lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
        by (intros x Hx; exact (w4e2k_mrd_munch _ mem3 m' x HIF ltac:(lia)
                                  ltac:(cbn [lib.Lib.Frame.outside]; split; [lia | exact I]))).
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply K1; lia | exact U0]|].
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply K1; lia | exact U4]|].
      apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply K1; lia | exact U8]. }
  split.
  { destruct HGAP as (G0 & G1). split.
    - apply (w4e2m_bcmp_bytes mem3 m' phi _); [| exact G0].
      intros x Hx. apply KB. pose proof HFTURN as (_ & _ & _ & Hl).
      change (SM.t_len (ACtlCut.c_in cx) j) with (ACtlCutP.flen cx j) in Hl. destruct Hreq. lia.
    - intros Hf. apply (w4e2m_bcmp_bytes mem3 m' phi _); [| exact (G1 Hf)].
      intros x Hx. apply KB. rewrite w4e2w_tg_len in Hx. destruct Hreq. lia. }
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
  exact (w4e2m_rgv_tr R1 regs3 21 _ E21 H21).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82888_at j (0x82888) --S_F25--> B828a4_at j.
   0x82888 mv s9,a0 (s9 = t_rp); sb s7,20(s3) (S(fr) + 20 := 1); ld a1,136(s1) (a1 = fr + 160); li a0,-18;
   sb a0,0(a1) ([fr + 160] := 0xee); mv a0,s6 (a0 = blk); jal reac_ports_unknown (entry 0x88628, ra 0x828a4)
   (UB Seg/F25.v:3-19).  The callee reads [phi + 18, phi + 38) and the byte c = fr + 160, returns a0 = t_unk j,
   writes [sp - 16, sp) and c := t_first j.  SINK BRANCHES: none (objdump L85359-L85365). *)
Lemma seg_F25 : forall POST (j : nat),
  ctl_from POST (ix C_B828a4_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82888_at [Z.of_nat j]).
Proof.
  intros POST j H8a4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  destruct HBODY as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82888_at ACtlCutP.ixn ACtlCutP.fcutp_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & H18 & H20 & HFTURN & HLK & HFTL & HIFS & HF27K & H10 &
    H20' & H23 & S184 & H22 & HPORTS & HGAP & Hwin & H21).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4e2k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1)
    as (Efr & _ & Hfr4096 & Hfrc & Happ & Himgfr & Hnimg & Hfrpres & Hshpres & _ & Hcspc & Hcsp47 & Hstkpres).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as (Hc1 & Hc2).
  unfold Reusable.YCfn.LLVMF_STK in Hcspc, Hstkpres.
  pose proof HJ as (HAR & _).
  pose proof HRT as (Hcells & _).
  pose proof HF27K as (HLK' & H18' & H27 & Hphi0 & Hphi50 & Hflen & Hblk & S312 & S272 & H24 & S104 & S136).
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & Hpapp & Hbpr & _ & Hnrange).
  assert (Hfin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (w4e2_block_frame_apart ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hin Hfin) as Hapart.
  pose proof (w4e2_frame_high ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) HAR Hfin) as Hhigh.
  rewrite <- Efr in Hapart, Hhigh. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hapart.
  assert (Hreq : B.ACtlK.a_size (ACtlCutP.flen cx j) = Reusable.YG00.req_size (ACtlCutP.flen cx j) /\
                 ACtlCutP.flen cx j <= Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hsp2 : bv_unsigned (Sem.reg_get regs3 2) = sp).
  { rewrite (w4e2w_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  pose proof (w4e2_blk_len (ACtlCut.c_in cx) j) as Lblk.
  pose proof (w4e2_spill regs3 mem3 A 136 _ Hr9 ltac:(lia) ltac:(lia) S136) as Q136.
  (* the frame shadow's placement *)
  assert (HSf : ART.LOWMEM_END + 512 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= ART.HIGHMEM_BEG /\
                ACtlCutP.Sfr fr + 20 = ART.shadow_addr (fr + 160) /\
                (fr + 4096 <= ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= fr) /\
                2147450880 + 791552 <= ACtlCutP.Sfr fr).
  { unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, ART.LOWMEM_END, ART.HIGHMEM_BEG.
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    Z.div_mod_to_equations. lia. }
  destruct HSf as (HS1 & HS2 & HS3 & HS4 & HS5). unfold ART.LOWMEM_END in HS1. unfold ART.HIGHMEM_BEG in HS2.
  assert (Hshb : forall i, 0 <= i < Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
                   ART.shadow_addr (phi + i) < ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= ART.shadow_addr (phi + i)).
  { intros i Hi. unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *. Z.div_mod_to_equations. lia. }
  set (S3' := ACtlCutP.Sfr fr) in *.
  set (P25 := fun ms' => exists m1 : word -> option byte,
    lib.Lib.Frame.munch (B.Prog.Seg.F25.f25_W S3' (fr + 160) sp) mem3 m1 /\
    lib.Lib.Frame.wmono B.Img0.rsegs mem3 m1 /\
    B.Prog.reac_ports_unknown_c.reac_ports_unknown_post (Z_to_bv 64 0x828a4) (Sem.reg_get regs3 2)
      (Sem.reg_get regs3 3) (Sem.reg_get regs3 4) (Sem.reg_get regs3 8) (Z_to_bv 64 A) (Z_to_bv 64 (fr + 160))
      (Sem.reg_get regs3 18) (Z_to_bv 64 S3') (Sem.reg_get regs3 20) (Sem.reg_get regs3 21)
      (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 1) (Sem.reg_get regs3 24) (Sem.reg_get regs3 10)
      (Sem.reg_get regs3 26) (Sem.reg_get regs3 27) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30)
      (Sem.reg_get regs3 31) CK11.fp_regs CK11.fp_csr m1 (phi + 18) (fr + 160) (sp - 16)
      (SM.t_pbs (ACtlCut.c_in cx) j) ms').
  (* 0x82888 -> 0x88628 (f25_pre_F_on: the two stores) -> the callee -> 0x828a4, one lift *)
  apply w4e2m_enter.
  apply (w4e2_lift W3 _ md3 P25).
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply LX.evtF_cut.
    { eapply (B.Prog.Seg.F25F.f25_pre_F_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (S3 := S3') (A := A) (D := fr + 160) (p := phi + 18) (sp := sp) (lo := sp - 16)
             (bs := SM.t_pbs (ACtlCut.c_in cx) j).
      - exact (w4e2w_rgv_reg _ 19 _ eq_refl Hr19).
      - exact (w4e2w_rgv_reg _ 9 _ eq_refl Hr9).
      - exact (w4e2w_rgv_reg _ 22 _ eq_refl H22).
      - exact (w4e2w_rgv_reg _ 23 _ eq_refl H23).
      - exact Hsp2.
      - unfold ART.LOWMEM_END, ART.HIGHMEM_BEG. lia.
      - symmetry. exact HS3.
      - Z.div_mod_to_equations. lia.
      - unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
        unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ. lia.
      - lia.
      - apply w4e2k_wr_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hshpres x ltac:(lia))).
      - apply w4e2k_wr_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hfrpres x ltac:(lia))).
      - lia.
      - lia.
      - lia.
      - exact Q136.
      - lia.
      - lia.
      - rewrite w4e2_pbs_blk20, length_firstn, Lblk. reflexivity.
      - rewrite w4e2_pbs_blk20. apply w4e2_bytes_firstn; [exact Hblk | rewrite Lblk; lia].
      - apply (w4e2w_addr_sub mem3 phi _ (phi + 18) 20 (proj2 HHB)); destruct Hreq; lia.
      - intros i Hi. destruct (Hshb (18 + i) ltac:(destruct Hreq; lia)) as [Hs|Hs];
          replace (phi + (18 + i)) with (phi + 18 + i) in Hs by lia; lia.
      - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp. lia.
      - destruct Hapart as [Ha|Ha]; destruct Hreq; lia.
      - apply w4e2k_stk_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hstkpres x ltac:(lia))).
      - lia.
      - unfold ART.HIGHMEM_BEG. lia.
      - left. lia.
      - left. lia.
      - exact Hcells.
      - unfold ART.RT_HI. lia.
      - unfold ART.GOT_CELL_K. lia.
      - unfold ART.CELL_K. lia.
      - apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hshpres a ltac:(lia))).
      - apply B.ProgBridge.rng_of_visible.
        apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
      - apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hfrpres a ltac:(lia))). }
    intros ms1 (m1 & Ems1 & MU1 & WM1 & ST1 & B20 & WD & Bp & SR1 & AC1 & AD1 & Ap1). subst ms1.
    eapply LX.evtF_mono.
    { eapply (B.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (p := phi + 18) (c := fr + 160) (lo := sp - 16) (bs := SM.t_pbs (ACtlCut.c_in cx) j);
        unfold B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME; rewrite ?Hsp2.
      - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
      - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
      - exact ST1.
      - lia.
      - intros _. split; [lia|]. split.
        { rewrite w4e2_pbs_blk20, length_firstn, Lblk. reflexivity. }
        split; [exact Bp|]. lia.
      - intros _. split; [exact WD|]. split; [intros _; destruct Hapart as [Ha|Ha]; destruct Hreq; lia|]. lia.
      - exact AC1.
      - intros _. exact AD1.
      - intros _. exact Ap1.
      - intros x Hx. unfold B.Prog.reac_ports_unknown_c.reac_ports_unknown_W,
          B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME.
        rewrite (proj2 (Z.eqb_neq (fr + 160) 0) ltac:(lia)).
        cbn [lib.Lib.Frame.outside]. split; [|split; [|exact I]].
        + unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
            B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx. lia.
        + unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
            B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
          unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ. lia.
      - apply B.ProgBridge.rng_of_visible.
        apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
      - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.GOT_CELL_K.
        split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
      - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.CELL_K.
        split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
      - intros _. split.
        + apply B.ProgBridge.rng_of_visible.
          split; [lia|]. split; [lia|]. intros a Ha. destruct Hreq. exact (proj1 (proj1 (Hbpr a ltac:(lia)))).
        + apply B.ProgBridge.rng_of_visible.
          split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
          split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
          intros a Ha.
          destruct (w4e2w_sh_between (phi + 18) (phi + 37) a ltac:(lia)
                      ltac:(unfold B.AsanRT.shadow_addr in *; lia)) as (z & Hz & <-).
          replace z with (phi + (z - phi)) by lia.
          apply (w4e2m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). destruct Hreq. lia.
      - intros _. split.
        + apply B.ProgBridge.rng_of_visible.
          split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hfrpres a ltac:(lia))).
        + apply B.ProgBridge.rng_of_visible.
          rewrite <- HS3. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hshpres a ltac:(lia))). }
    intros ms' Hpost. exists m1. split; [exact MU1|]. split; [exact WM1|].
    exact Hpost. }
  intros ms' md' (m1 & MU1 & WM1 & (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & -> & MU2 & WM2 &
    Hstk' & _ & Hc)) Hgr Hhid Hsbm.
  unfold B.Prog.reac_ports_unknown_c.reac_ports_unknown_W, B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME in MU2.
  rewrite (proj2 (Z.eqb_neq (fr + 160) 0) ltac:(lia)) in MU2.
  rewrite Hsp2 in MU2, Hstk'.
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x828a4) = Z_to_bv 64 0x828a4) by (apply bv_eq; reflexivity).
  rewrite Eret.
  apply (w4e2m_exit W3 0x828a4).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  set (Wr := B.Prog.Seg.F25.f25_W S3' (fr + 160) sp).
  assert (MU : lib.Lib.Frame.munch Wr mem3 m').
  { apply (lib.Lib.Frame.munch_trans Wr mem3 m1 m' MU1).
    eapply lib.Lib.Frame.munch_weaken; [| exact MU2].
    intros x Hx. unfold Wr, B.Prog.Seg.F25.f25_W in Hx. cbn [lib.Lib.Frame.outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3 & _). repeat split; try exact I; lia. }
  assert (WM : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m') by exact (lib.Lib.Frame.wmono_trans _ _ _ _ WM1 WM2).
  assert (Hout : forall x, (x < S3' + 20 \/ S3' + 21 <= x) -> (x < fr + 160 \/ fr + 161 <= x) ->
                   (x < sp - 16 \/ sp <= x) -> lib.Lib.Frame.outside Wr x)
    by (intros x H1 H2 H3; unfold Wr, B.Prog.Seg.F25.f25_W; cbn [lib.Lib.Frame.outside];
        split; [lia | split; [lia | split; [lia | exact I]]]).
  assert (Hgrow : forall x : word, mem3 x <> None -> m' x <> None) by exact Hgr.
  assert (HrW : forall a, ~ lib.Lib.Frame.outside Wr a ->
                  S3' + 20 <= a < S3' + 21 \/ fr + 160 <= a < fr + 161 \/ sp - 16 <= a < sp).
  { intros a Ha. pose proof (B.Prog.Seg.F25.f25_inW _ _ _ _ Ha) as H. lia. }
  assert (HW : forall a, ~ lib.Lib.Frame.outside Wr a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. pose proof (HrW a Ha) as Hr.
    assert (Hni : ~ Reusable.YG0d.in_img segs a).
    { destruct Hr as [Hr|[Hr|Hr]]; [apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia | |
        apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia].
      apply Hnimg. lia. }
    split; [exact Hni|].
    assert (Hp : mem3 (lib.Lib.Mem.wa a) <> None).
    { destruct Hr as [Hr|[Hr|Hr]].
      - destruct (Hshpres a ltac:(lia)) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
        rewrite Hb. discriminate.
      - destruct (Hfrpres a ltac:(lia)) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
        rewrite Hb. discriminate.
      - destruct (Hstkpres a ltac:(lia)) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
        rewrite Hb. discriminate. }
    pose proof (Hgrow _ Hp) as Hp'. destruct (m' (lib.Lib.Mem.wa a)) as [b|]; [exists b; reflexivity | congruence]. }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4e2k_after_run cx ly3 S3 W3 mem3 md3 k m' md' Wr HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    destruct (HrW a Ha) as [Hr|[Hr|Hr]].
    - apply (w4e2k_awr_fsh cx ly3 fr _ _ _ _ a Efr). lia.
    - apply (w4e2k_awr_fr cx ly3 fr _ _ _ _ a Efr). lia.
    - apply w4e2k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia. }
  pose proof (w4e2k_ctlrtC_run ly3 S3 mem3 m' Wr HRT MU WM HW) as HRT'.
  assert (KEPT : forall x, 0 <= x < 2 ^ 64 -> (x < S3' + 20 \/ S3' + 21 <= x) -> (x < fr + 160 \/ fr + 161 <= x) ->
             (x < sp - 16 \/ sp <= x) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx H1 H2 H3; exact (w4e2k_mrd_munch Wr mem3 m' x MU Hx (Hout x H1 H2 H3))).
  assert (KSA : forall x : Z, A <= x < ACtlCut.c_sp cx ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KFhi : forall x : Z, fr + 2560 <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KSH : forall x : Z, ACtlCutP.Sfr fr + 320 <= x < ACtlCutP.Sfr fr + 512 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (Hkn : forall i, 0 <= i < 112 ->
             2147450880 + 81584 <= B.AsanRT.shadow_addr (ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597)
    by exact w4e2k_kn_shadow.
  assert (KK : forall x : Z, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { unfold ACtlCutP.KNA.KIND_NAME. intros x Hx. apply KEPT; lia. }
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx j) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. rewrite (proj1 Hreq) in Hi. pose proof (Hshb i Hi) as Hs.
    assert (Hb : 2147450880 <= ART.shadow_addr (phi + i) < 17594333495296).
    { unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    change B.AsanRT.shadow_addr with ART.shadow_addr.
    apply KEPT; lia. }
  assert (KB : forall x : Z, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    apply KEPT; [lia | lia | destruct Hapart; lia | lia]. }
  assert (KF : forall x : Z, fr <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha. destruct (Hfrpres a ltac:(lia)) as (_ & b & Hb).
    assert (Hp' : m' (Z_to_bv 64 a) <> None) by (apply Hgrow; rewrite Hb; discriminate).
    destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | congruence]. }
  assert (HKA : B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112).
  { pose proof HLK as (_ & _ & _ & HFLI). unfold ACtlCutP.FLI in HFLI.
    destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & (_ & HKA0) & _).
    apply (w4e2m_bcmp_addr mem3 m' _ 112); [| exact HKA0].
    intros i Hi. pose proof (Hkn i Hi) as Hk'. apply KEPT; lia. }
  assert (KShr : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
             exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct (Hshpres x ltac:(lia)) as (_ & b & Hb).
    assert (Hp' : m' (Z_to_bv 64 x) <> None) by (apply Hgrow; rewrite Hb; discriminate).
    destruct (m' (Z_to_bv 64 x)) as [b'|] eqn:Eb'; [|congruence].
    exists b'. exact (w4e2k_raw_mrd _ _ _ Eb'). }
  assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
  assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
  assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
  assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
  assert (E9 : getr R1 9 = getr regs3 9)
    by (transitivity (Z_to_bv 64 A); [reflexivity | symmetry; exact Hr9]).
  assert (E18 : getr R1 18 = getr regs3 18) by reflexivity.
  assert (E19 : getr R1 19 = getr regs3 19)
    by (transitivity (Z_to_bv 64 S3'); [reflexivity | symmetry; exact Hr19]).
  assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
  assert (E21 : getr R1 21 = getr regs3 21) by reflexivity.
  assert (E22 : getr R1 22 = getr regs3 22)
    by (transitivity (Z_to_bv 64 (phi + 18)); [reflexivity | symmetry; exact H22]).
  assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
  assert (E25 : getr R1 25 = getr regs3 10) by reflexivity.
  assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
  assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R1 m' off v)
    by (intros off v Ho Hs; exact (w4e2m_bcmp_sp R1 regs3 mem3 m' A (ACtlCut.c_sp cx) off v Hr9 E9 ltac:(lia)
                                     ltac:(lia) ltac:(lia) KSA Ho Hs)).
  apply (H8a4 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B828a4_at ACtlCutP.ixn nth].
  split; [reflexivity|]. rewrite Nat2Z.id.
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4e2k_FRAC_keep cx fr fr regs3 R1 mem3 m' HFRAC E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KShr].
    intros x Hx. rewrite HspZ in Hx. apply KEPT; lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4e2m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  assert (HLK1 : ACtlCutP.LK cx fr j R1 m')
    by exact (w4e2m_bcmp_LK cx fr j R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                ltac:(lia) KSA KFhi KSH KK HKA Hpr HLK).
  split.
  { (* F27K *)
    split; [exact HLK1|].
    split; [exact (w4e2m_rgv_tr R1 regs3 18 _ E18 H18')|].
    split; [exact (w4e2m_rgv_tr R1 regs3 27 _ E27 H27)|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|].
    split; [apply (w4e2m_bcmp_bytes mem3 m' (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; destruct Hreq; lia | exact Hblk]|].
    split; [exact (SP 312 _ ltac:(lia) S312)|]. split; [exact (SP 272 _ ltac:(lia) S272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 H24)|].
    split; [exact (SP 104 _ ltac:(lia) S104)|]. exact (SP 136 _ ltac:(lia) S136). }
  split; [exact (w4e2m_rgv_tr R1 regs3 20 _ E20 H20)|].
  split.
  { destruct HFTL as (T21 & T184 & T272 & T24 & T312).
    split; [exact (w4e2m_rgv_tr R1 regs3 21 _ E21 T21)|].
    split; [exact (SP 184 _ ltac:(lia) T184)|]. split; [exact (SP 272 _ ltac:(lia) T272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 T24)|]. exact (SP 312 _ ltac:(lia) T312). }
  split; [unfold ACtlCut.rgv in *; rewrite E25; exact H10|].
  split.
  { unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (if Prog.RcPorts.pu_ok (phi + 18) (SM.t_pbs (ACtlCut.c_in cx) j)
                                                  then 4 * Prog.RcPorts.pu_nunk (SM.t_pbs (ACtlCut.c_in cx) j) 12
                                                  else -1)); [reflexivity|].
    rewrite (w4e2_unk_ok (phi + 18) (ACtlCut.c_in cx) j ltac:(lia)). reflexivity. }
  split; [exact (w4e2m_rgv_tr R1 regs3 22 _ E22 H22)|].
  split.
  { destruct HPORTS as [P0 P1]. split.
    - intros E. destruct (P0 E) as (U0 & U4 & U8).
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U0]|].
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U4]|].
      apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U8].
    - intros E. destruct (P1 E) as (U0 & U4 & U8).
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U0]|].
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U4]|].
      apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KEPT; lia | exact U8]. }
  split.
  { (* FIRSTb: the byte the callee wrote at c = fr + 160 *)
    unfold ACtlCutP.FIRSTb, ACtlCutP.b8.
    pose proof (Hc ltac:(lia)) as Hc'.
    rewrite (w4e2_first_ok (phi + 18) (ACtlCut.c_in cx) j ltac:(lia)) in Hc'. exact Hc'. }
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact Hwin|].
  split.
  { apply (w4e2m_bcmp_FTURN cx j phi R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFTURN].
    intros x Hx. apply KB. destruct Hreq. lia. }
  split; [exact (w4e2m_bcmp_IFS cx fr (S j) R1 regs3 mem3 m' KFhi KSH HIFS)|].
  exact (w4e2m_rgv_tr R1 regs3 21 _ E21 H21).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B828a4_at j (0x828a4) --S_F26--> B828b4_at j.
   0x828a4 mv s7,a0 (s7 = t_unk, the first count); mv a0,s6; li a1,0; jal reac_ports_unknown (entry 0x88628,
   ra 0x828b4) (UB Seg/F26.v:3-12).  The callee with c = 0 reads [phi + 18, phi + 38), returns a0 = t_unk j,
   writes only [sp - 16, sp).  SINK BRANCHES: none (objdump L85366-L85369). *)
Lemma seg_F26 : forall POST (j : nat),
  ctl_from POST (ix C_B828b4_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B828a4_at [Z.of_nat j]).
Proof.
  intros POST j H8b4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  destruct HBODY as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B828a4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hn & Hj & HHB & HF27K & H20 & HFTL & H25 & H10 & H22 & HPORTS & HFIRST &
    Hwin & HFTURN & HIFS & H21).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4e2m_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof HRT as (Hcells & _).
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & _ & Hbpr & _).
  assert (Hsp2 : bv_unsigned (Sem.reg_get regs3 2) = sp).
  { rewrite (w4e2w_rgv_reg regs3 2 sp eq_refl Hr2). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  pose proof HF27K as (HLK & H18 & H27 & Hphi0 & Hphi50 & Hflen & Hblk & S312 & S272 & H24 & S104 & S136).
  assert (Hreq : ACtlCutP.flen cx j <= Reusable.YG00.req_size (ACtlCutP.flen cx j) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx j) = Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  pose proof (w4e2_blk_len (ACtlCut.c_in cx) j) as Lblk.
  (* 0x828a4 -> 0x88628 (seg_F26_pre_F) -> the callee -> 0x828b4, one lift *)
  apply w4e2m_enter.
  eapply w4e2m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply LX.evtF_cut.
    { eapply (B.Prog.Seg.F26F.seg_F26_pre_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (blk := phi + 18).
      exact (w4e2w_rgv_reg _ 22 _ eq_refl H22). }
    intros ms1 Ems1. cbv beta in Ems1. subst ms1.
    eapply (B.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (p := phi + 18) (c := 0) (lo := sp - 16) (bs := SM.t_pbs (ACtlCut.c_in cx) j);
      unfold B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME; rewrite ?Hsp2.
    - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
    - reflexivity.
    - apply w4e2k_stk_raw; [lia | lia |]. intros x Hx. exact (proj2 (Hpres x ltac:(lia))).
    - lia.
    - intros _. split; [lia|]. split.
      { rewrite w4e2_pbs_blk20, length_firstn, Lblk. reflexivity. }
      split; [rewrite w4e2_pbs_blk20; apply w4e2_bytes_firstn; [exact Hblk | rewrite Lblk; lia] | lia].
    - intros C. exfalso. apply C. reflexivity.
    - exact Hcells.
    - intros C. exfalso. apply C. reflexivity.
    - intros _. apply (w4e2w_addr_sub mem3 phi _ (phi + 18) 20 (proj2 HHB)); lia.
    - intros x Hx. unfold B.Prog.reac_ports_unknown_c.reac_ports_unknown_W,
        B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME.
      cbn [Z.eqb lib.Lib.Frame.outside]. split; [|exact I].
      unfold B.AsanRT.in_shadow, B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.LOWMEM_END,
        B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
      lia.
    - apply B.ProgBridge.rng_of_visible.
      apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.GOT_CELL_K.
      split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
    - apply B.ProgBridge.rng_of_visible. unfold B.AsanRT.CELL_K.
      split; [lia|]. split; [lia|]. intros a Ha. apply Himg. lia.
    - intros _. split.
      + apply B.ProgBridge.rng_of_visible.
        split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hbpr a ltac:(lia)))).
      + apply B.ProgBridge.rng_of_visible.
        split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
        intros a Ha.
        destruct (w4e2w_sh_between (phi + 18) (phi + 37) a ltac:(lia)
                    ltac:(unfold B.AsanRT.shadow_addr in *; lia)) as (z & Hz & <-).
        replace z with (phi + (z - phi)) by lia.
        apply (w4e2m_bcmp_block_shadow_vis ly3 S3 W3 mem3 md3 phi _ (z - phi) HAR Hin). lia.
    - intros C. exfalso. apply C. reflexivity. }
  intros ms' md' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & -> & MU & WM & Hstk' & _ & _)
    Hsbm Hhid.
  unfold B.Prog.reac_ports_unknown_c.reac_ports_unknown_W, B.Prog.reac_ports_unknown_c.REAC_PORTS_UNKNOWN_FRAME
    in MU.
  cbn [Z.eqb] in MU. rewrite Hsp2 in MU, Hstk'.
  assert (Eret : lib.Lib.MState.ret_pc (Z_to_bv 64 0x828b4) = Z_to_bv 64 0x828b4) by (apply bv_eq; reflexivity).
  rewrite Eret.
  apply (w4e2m_exit W3 0x828b4).
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  assert (Hout : forall x, 0 <= x < sp - 16 \/ sp <= x -> lib.Lib.Frame.outside [(sp - 16, sp)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HW : forall a, ~ lib.Lib.Frame.outside [(sp - 16, sp)] a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. apply w4e2k_not_outside1 in Ha.
    assert (Hni : ~ Reusable.YG0d.in_img segs a) by (apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
    split; [exact Hni|].
    destruct Hstk' as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as (_ & b & Hb).
    exists b. exact (w4e2k_mrd_raw m' a b ltac:(lia) Hni Hb). }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4e2k_after_run cx ly3 S3 W3 mem3 md3 k m' md' [(sp - 16, sp)] HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    apply w4e2k_not_outside1 in Ha. apply w4e2k_awr_stk. unfold Reusable.YCfn.LLVMF_STK. lia. }
  pose proof (w4e2k_ctlrtC_run ly3 S3 mem3 m' _ HRT MU WM HW) as HRT'.
  assert (KS : forall x : Z, sp <= x < ACtlCut.c_sp cx ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (apply (w4e2w_munch_kept _ mem3 m' sp _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSA : forall x : Z, A <= x < ACtlCut.c_sp cx ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KS; lia).
  assert (KF : forall x : Z, fr <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (apply (w4e2w_munch_kept _ mem3 m' fr _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KSH : forall x : Z, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { apply (w4e2w_munch_kept _ mem3 m' _ _ MU);
      [unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia
      | unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia |].
    intros x Hx. apply Hout.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. Z.div_mod_to_equations. lia. }
  assert (KK : forall x : Z, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { unfold ACtlCutP.KNA.KIND_NAME.
    apply (w4e2w_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]. }
  assert (KB : forall x : Z, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (apply (w4e2w_munch_kept _ mem3 m' _ _ MU); [lia | lia | intros x Hx; apply Hout; lia]).
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx j) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. apply (w4e2k_mrd_munch _ mem3 m' _ MU).
    - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - apply Hout. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    assert (Ha' : fr <= a < fr + 4096 \/
                  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) by (left; lia).
    destruct (proj2 (w4e2m_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha')) as (b & Hb).
    exists b. rewrite (MU (Z_to_bv 64 a)); [exact Hb|].
    change (Z_to_bv 64 a) with (lib.Lib.Mem.wa a). rewrite lib.Lib.Mem.wa_unsigned by lia. apply Hout. lia. }
  (* KIND_NAME's shadow bytes are kept, so the KNT addressable fact moves with them *)
  assert (HKA : B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112).
  { pose proof HLK as (_ & _ & _ & HFLI). unfold ACtlCutP.FLI in HFLI.
    destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & (_ & HKA0) & _).
    apply (w4e2m_bcmp_addr mem3 m' _ 112); [| exact HKA0].
    intros i Hi. pose proof (w4e2k_kn_shadow i Hi) as Hk'.
    apply (w4e2k_mrd_munch _ mem3 m' _ MU); [lia | apply Hout; lia]. }
  assert (E2 : getr R1 2 = getr regs3 2) by reflexivity.
  assert (E3 : getr R1 3 = getr regs3 3) by reflexivity.
  assert (E4 : getr R1 4 = getr regs3 4) by reflexivity.
  assert (E8 : getr R1 8 = getr regs3 8) by reflexivity.
  assert (E9 : getr R1 9 = getr regs3 9) by reflexivity.
  assert (E18 : getr R1 18 = getr regs3 18) by reflexivity.
  assert (E19 : getr R1 19 = getr regs3 19) by reflexivity.
  assert (E20 : getr R1 20 = getr regs3 20) by reflexivity.
  assert (E21 : getr R1 21 = getr regs3 21) by reflexivity.
  assert (E23 : getr R1 23 = getr regs3 10) by reflexivity.
  assert (E24 : getr R1 24 = getr regs3 24) by reflexivity.
  assert (E25 : getr R1 25 = getr regs3 25) by reflexivity.
  assert (E26 : getr R1 26 = getr regs3 26) by reflexivity.
  assert (E27 : getr R1 27 = getr regs3 27) by reflexivity.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R1 m' off v)
    by (intros off v Ho Hs; exact (w4e2m_bcmp_sp R1 regs3 mem3 m' A (ACtlCut.c_sp cx) off v Hr9 E9 ltac:(lia)
                                     ltac:(lia) ltac:(lia) KSA Ho Hs)).
  apply (H8b4 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B828b4_at ACtlCutP.ixn nth].
  split; [reflexivity|]. rewrite Nat2Z.id.
  exists phi.
  split; [exact Hperm|].
  split.
  { apply (w4e2m_bcmp_FRAC cx fr fr R1 regs3 mem3 m' E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. rewrite HspZ in Hx. lia. }
  split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4e2m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  split.
  { (* F27K *)
    split; [exact (w4e2m_bcmp_LK cx fr j R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
                     ltac:(lia) KSA (fun x Hx => KF x ltac:(lia)) (fun x Hx => KSH x ltac:(lia)) KK HKA Hpr HLK)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 18 _ E18 H18)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 27 _ E27 H27)|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|].
    split; [apply (w4e2m_bcmp_bytes mem3 m' (phi + 18) _); [intros x Hx; apply KB; rewrite Lblk in Hx; lia | exact Hblk]|].
    split; [exact (SP 312 _ ltac:(lia) S312)|]. split; [exact (SP 272 _ ltac:(lia) S272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 H24)|].
    split; [exact (SP 104 _ ltac:(lia) S104)|]. exact (SP 136 _ ltac:(lia) S136). }
  split; [exact (w4e2m_rgv_tr R1 regs3 20 _ E20 H20)|].
  split.
  { destruct HFTL as (T21 & T184 & T272 & T24 & T312).
    split; [exact (w4e2m_rgv_tr R1 regs3 21 _ E21 T21)|].
    split; [exact (SP 184 _ ltac:(lia) T184)|]. split; [exact (SP 272 _ ltac:(lia) T272)|].
    split; [exact (w4e2m_rgv_tr R1 regs3 24 _ E24 T24)|]. exact (SP 312 _ ltac:(lia) T312). }
  split; [exact (w4e2m_rgv_tr R1 regs3 25 _ E25 H25)|].
  split; [unfold ACtlCut.rgv in *; rewrite E23; exact H10|].
  split.
  { unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (if Prog.RcPorts.pu_ok (phi + 18) (SM.t_pbs (ACtlCut.c_in cx) j)
                                                  then 4 * Prog.RcPorts.pu_nunk (SM.t_pbs (ACtlCut.c_in cx) j) 12
                                                  else -1)); [reflexivity|].
    rewrite (w4e2_unk_ok (phi + 18) (ACtlCut.c_in cx) j ltac:(lia)). reflexivity. }
  split.
  { destruct HPORTS as [P0 P1]. split.
    - intros E. destruct (P0 E) as (U0 & U4 & U8).
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U0]|].
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U4]|].
      apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U8].
    - intros E. destruct (P1 E) as (U0 & U4 & U8).
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U0]|].
      split; [apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U4]|].
      apply (w4e2m_bcmp_u32 mem3 m' _ _); [intros x Hx; apply KF; lia | exact U8]. }
  split; [apply (w4e2m_bcmp_b8 mem3 m' _ _); [intros x Hx; apply KF; lia | exact HFIRST]|].
  split.
  { apply (w4e2m_bcmp_FTURN cx j phi R1 regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 E9); [lia | lia | lia | exact KSA | |
      exact HFTURN].
    intros x Hx. apply KB. lia. }
  split; [exact (w4e2m_bcmp_IFS cx fr (S j) R1 regs3 mem3 m' (fun x Hx => KF x ltac:(lia)) (fun x Hx => KSH x ltac:(lia)) HIFS)|].
  exact (w4e2m_rgv_tr R1 regs3 21 _ E21 H21).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B828b4_at j (0x828b4) --S_F27--> B8292c_at j (r = 0) | B82aa4_at j (r <> 0).
   The head of the inlined check_ports (UB Seg/F27.v:10-31): no call, no store, no instrumented check.
   r <> 0: 0x828c8-0x828e8 load the three port words through s5 = fr + 128 and compare them with -7, then
   `j 82aa4`.  r = 0: 0x828f0 li t3,12; 0x828f4 ld a0,312(s1); 0x828f8 beqz a0,82fa0; 0x828fc-0x82928 the loop
   registers (a5 = a3 = a1 = a2 = 0, a4 = a0 = phi + 26, a6 = -8 - (phi + 18), a7 = 12); reach 0x8292c.
   SINK BRANCHES (objdump L85370-L85399):
   - 0x828b4 `bne a0,s7,82fa4`: not taken, both counts are t_unk j (C_B828b4_at body rgv 10 (t_unk j) and
     rgv 23 (t_unk j)).
   - 0x828c0 `beq a0,a1,82fa4` (a0 = seqz s9, a1 = slti s7,0): not taken, t_rp j = 0 exactly when 0 <= t_unk j
     (the ports fact C5.3; ctrl's model lemma, Tac_b7 / Seg/F27.v:17-18) with s9 = t_rp j (rgv 25).
   - 0x828d0 / 0x828dc / 0x828e8 `bne _,a1,82fa4` (r <> 0 arm): not taken, PORTS's second arm keeps the three
     words at fr + 128 .. fr + 136 at -7 (C5.4).
   - 0x828f8 `beqz a0,82fa0` (UBSan, plan F.4.1 row 53, T55; r = 0 arm): not taken, a0 = [A + 312] = phi + 18 and
     F27K's 0 < phi /\ phi + 50 <= 2^64 give phi + 18 in [19, 2^64 - 32].
   All are discharged INSIDE seg_F27_F, whose premises carry those conjuncts. *)
Lemma seg_F27 : forall POST (j : nat),
  ctl_from POST (ix C_B8292c_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82aa4_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B828b4_at [Z.of_nat j]).
Proof.
  intros POST j H92c Haa4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* the entry cut at [Z.of_nat j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B828b4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HF27K & R20 & HFTL & R25 & R23 & R10 & HPORTS & HFIRST &
    HFTURN & HIFS & R21).
  pose proof (w4e2_world cx fr k ly3 S3 W3 mem3 md3 HJ HF HL)
    as (Hfr4096 & Hfrc & Hspc & Hsp47 & Hceil & Vfr & Vsh & Vstk).
  pose proof HFRAC as (A & sp & G2 & Hsp16 & Hsp & G4 & R8 & R9 & G3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA448 & Hspc4 & HcAPP & Q336 & Q48 & Q40 & Qhd & Qent & Hsh & Hsaved).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof HF27K as (HLK & R18 & R27 & Hphi0 & Hphi50 & Hlen & Hblk & S312 & S272 & R24 & S104 & S136).
  (* the cut's configuration in the runs' state form, moved to the canonical map mkR_of regs3 *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix C_B828b4_at [Z.of_nat j])) with 0x828b4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRg.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x828b4) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRg.xregs_eqv_sym _ _ (LRg.mkR_of_eqv regs3))].
  destruct (w4e2_rp_unk (ACtlCut.c_in cx) j) as [(Hr0 & Hu & Eu & Hdecl & Efst) | (Hr1 & Hu1 & Hdecl)].
  - (* r = 0: seg_F27_F, 0x828b4 -> 0x8292c; footprint [A + 312, A + 320) in the present stack window *)
    pose proof (w4e2_spill regs3 mem3 A 312 _ R9 ltac:(lia) ltac:(lia) S312) as Q312.
    rewrite Hr0 in R25.
    eapply (w4e2_lift W3 _ md3).
    { unfold LRg.mkR_of.
      eapply (B.Prog.Seg.F27F.seg_F27_F (PB.RNG_W (Reusable.YA0n.w_H W3))) with (A := A) (phi := phi)
        (u := SM.t_unk (ACtlCut.c_in cx) j).
      - exact (w4e2_rgv_reg _ 9 _ eq_refl R9).
      - exact (w4e2_rgv_reg _ 18 _ eq_refl R18).
      - exact (w4e2_rgv_reg _ 27 _ eq_refl R27).
      - exact (w4e2_rgv_reg _ 25 _ eq_refl R25).
      - exact (w4e2_rgv_reg _ 23 _ eq_refl R23).
      - exact (w4e2_rgv_reg _ 10 _ eq_refl R10).
      - exact Hphi0.
      - exact Hphi50.
      - lia.
      - exact Q312.
      - apply PB.rng_RNG_W; [lia | lia |].
        intros a Ha. exact (proj1 (Vstk a ltac:(lia))). }
    intros ms' md' HQ Hgr Hhid Hsbm.
    destruct HQ as (R & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K18 & K23 & K27 & K20 & K21 & K24 & K10 &
      K14 & K16 & K17 & K11 & K12 & K13 & K15 & K28).
    subst ms'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix C_B8292c_at [Z.of_nat j])) R mem3 md') (POST cx)).
    pose proof (w4e2_getr_keep _ _ _ K9) as E9.
    pose proof (w4e2_getr_keep _ _ _ K18) as E18.
    pose proof (w4e2_getr_keep _ _ _ K21) as E21.
    pose proof (w4e2_getr_keep _ _ _ K24) as E24.
    pose proof (w4e2_getr_keep _ _ _ K27) as E27.
    apply (H92c cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + exact (w4e2_aj_same cx ly3 S3 W3 mem3 md3 md' k _ HJ Hsbm).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B8292c_at ACtlCutP.ixn nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split.
      { exact (w4e2_frac_keep cx fr fr regs3 R mem3 HFRAC (w4e2_getr_keep _ _ _ K2) (w4e2_getr_keep _ _ _ K3)
                 (w4e2_getr_keep _ _ _ K4) (w4e2_getr_keep _ _ _ K8) E9 (w4e2_getr_keep _ _ _ K19)
                 (w4e2_getr_keep _ _ _ K26)). }
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4e2_rgv_keep _ _ _ _ K18 R18)|].
      split; [exact (w4e2_rgv_keep _ _ _ _ K20 R20)|].
      split; [exact (w4e2_FTURN_keep _ _ _ _ _ _ E9 HFTURN)|].
      split; [exact (w4e2_LK_keep _ _ _ _ _ _ E9 E27 HLK)|].
      split; [exact (w4e2_FTL_keep _ _ _ _ _ _ _ E9 E21 E24 HFTL)|].
      split; [exact HIFS|].
      split; [exact (w4e2_F27K_keep _ _ _ _ _ _ _ E9 E18 E24 E27 HF27K)|].
      split; [exact Hr0|].
      split; [exact (w4e2_rgv_keep _ _ _ _ K23 R23)|].
      split; [exact HPORTS|]. split; [exact HFIRST|].
      split; [exact (w4e2_rgv_set _ _ _ K10)|]. split; [exact (w4e2_rgv_set _ _ _ K14)|].
      split; [exact (w4e2_rgv_set _ _ _ K16)|]. split; [exact (w4e2_rgv_set _ _ _ K17)|].
      split; [exact (w4e2_rgv_set _ _ _ K11)|]. split; [exact (w4e2_rgv_set _ _ _ K12)|].
      split; [exact (w4e2_rgv_set _ _ _ K13)|]. split; [exact (w4e2_rgv_set _ _ _ K15)|].
      exact (w4e2_rgv_set _ _ _ K28).
    + exact Hrt.
  - (* r <> 0: seg_F27_rp_F, 0x828b4 -> 0x82aa4; footprint the three words [fr + 128, fr + 140) of the frame *)
    rewrite Hr1 in R25. rewrite Hu1 in R23, R10.
    destruct HPORTS as [_ HP7]. destruct (HP7 ltac:(lia)) as (U0 & U4 & U8).
    eapply (w4e2_lift W3 _ md3).
    { unfold LRg.mkR_of.
      eapply (B.Prog.Seg.F27F.seg_F27_rp_F (PB.RNG_W (Reusable.YA0n.w_H W3))) with (fr := fr).
      - exact (w4e2_rgv_reg _ 21 _ eq_refl R21).
      - exact (w4e2_rgv_reg _ 25 _ eq_refl R25).
      - exact (w4e2_rgv_reg _ 23 _ eq_refl R23).
      - exact (w4e2_rgv_reg _ 10 _ eq_refl R10).
      - exact U0.
      - apply LMm.length_le4.
      - reflexivity.
      - exact U4.
      - apply LMm.length_le4.
      - reflexivity.
      - exact U8.
      - apply LMm.length_le4.
      - reflexivity.
      - apply PB.rng_RNG_W; [lia | lia |].
        intros a Ha. exact (Vfr a ltac:(lia)). }
    intros ms' md' HQ Hgr Hhid Hsbm.
    destruct HQ as (R & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K18 & K27 & K20 & K21 & K24).
    subst ms'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix C_B82aa4_at [Z.of_nat j])) R mem3 md') (POST cx)).
    pose proof (w4e2_getr_keep _ _ _ K9) as E9.
    pose proof (w4e2_getr_keep _ _ _ K21) as E21.
    pose proof (w4e2_getr_keep _ _ _ K24) as E24.
    pose proof (w4e2_getr_keep _ _ _ K27) as E27.
    apply (Haa4 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + exact (w4e2_aj_same cx ly3 S3 W3 mem3 md3 md' k _ HJ Hsbm).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82aa4_at ACtlCutP.ixn nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split.
      { exact (w4e2_frac_keep cx fr fr regs3 R mem3 HFRAC (w4e2_getr_keep _ _ _ K2) (w4e2_getr_keep _ _ _ K3)
                 (w4e2_getr_keep _ _ _ K4) (w4e2_getr_keep _ _ _ K8) E9 (w4e2_getr_keep _ _ _ K19)
                 (w4e2_getr_keep _ _ _ K26)). }
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4e2_rgv_keep _ _ _ _ K18 R18)|].
      split; [exact (w4e2_rgv_keep _ _ _ _ K20 R20)|].
      split; [exact (w4e2_FTURN_keep _ _ _ _ _ _ E9 HFTURN)|].
      split; [exact (w4e2_LK_keep _ _ _ _ _ _ E9 E27 HLK)|].
      split; [exact (w4e2_FTL_keep _ _ _ _ _ _ _ E9 E21 E24 HFTL)|].
      exact HIFS.
    + exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B8292c_at j (0x8292c) --S_F28--> B82aa4_at j.
   The port-slot loop (head 0x8292c, latch 0x829b8 `bnez a7`, 12 turns over the codes at phi + 26 + i) and the tail
   0x829cc-0x82aa0 that checks the counts against the port words through s5 = fr + 128 and the first byte at
   [A + 136] = fr + 160 (UB Seg/F28.v:9-44).  No call, no store.
   SINK BRANCHES (objdump L85400-L85493):
   - UBSan traps (plan F.4.1 rows 54-64): 0x82930 `beq t0,t3,82fa0` (T56: t0 = 2^64 - 14 - phi - i >= 25 from
     phi + 50 <= 2^64), 0x8295c / 0x82974 / 0x8298c `bne t1,_,82fa0` (T57-T59: each counter starts at 0 at the
     cut and gains at most 1 per turn, 12 turns), 0x82a00 / 0x82a10 / 0x82a20 / 0x82a34 (T60-T63: the sums of
     in / out / unknown / empty counts stay in [0, 192], PORTS' first arm at t_rp j = 0 and b7_unk_rp0,
     lib/Prog/Seg/Tac_b7.v:255), 0x82a50 / 0x82a68 (n_in, n_out <= 12 < 2^29), 0x82a80 `bltu a0,a1,82fa0`
     (phi + 25 >= 26 from F27K): all not taken from F28GAP (F27K, PORTS, FTL, the pinned loop registers) and the
     loop's own turn bound (seg_F28's induction, SIv:2947-2950; f28_loop's invariant).
   - ASan FAIL branches 0x829d4 / 0x829e4 / 0x829f4 / 0x82a40 / 0x82a58 / 0x82a70 / 0x82aa0 (to 0x82fa4): not
     taken, PORTS and FIRSTb hold exactly the values the loop computed (the words are 4 n_in, 4 n_out, 16 pbs[7];
     the first byte is the first unknown code; 4 (n_in + n_out + nunk + empty) = 48).
   - ASan report paths: the per-turn slow block 0x829c0 (0x829c4 `bge t1,t0,8304c` -> `jal __asan_report_load1`)
     and the tail check 0x82a94 -> 0x82e28 (0x82e2c `bge a3,a2,830cc`): not taken, every code byte lies in the
     live block phi with len >= 50 (HB), so its shadow byte k is 0 or (a mod 8) < k.
   All are discharged INSIDE f28_loop_F / f28_tail_F, whose premises carry those conjuncts. *)
Lemma seg_F28 : forall POST (j : nat),
  ctl_from POST (ix C_B82aa4_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B8292c_at [Z.of_nat j]).
Proof.
  intros POST j Haa4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* the entry cut at [Z.of_nat j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B8292c_at ACtlCutP.ixn ACtlCutP.fcutp_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & R18 & R20 & HFTURN & HLK & HFTL & HIFS & HGAP).
  destruct HGAP as (HF27K & Hrp0 & R23 & HPORTS & HFIRST & G10 & G14 & G16 & G17 & G11 & G12 & G13 & G15 & G28).
  pose proof (w4e2_world cx fr k ly3 S3 W3 mem3 md3 HJ HF HL)
    as (Hfr4096 & Hfrc & Hspc & Hsp47 & Hceil & Vfr & Vsh & Vstk).
  pose proof HFRAC as (A & sp & G2 & Hsp16 & Hsp & G4 & R8 & R9 & G3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA448 & Hspc4 & HcAPP & Q336 & Q48 & Q40 & Qhd & Qent & Hsh & Hsaved).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof HF27K as (_ & _ & _ & Hphi0 & Hphi50 & Hlen & Hblk & S312 & S272 & R24 & S104 & S136).
  pose proof HFTL as (R21 & _).
  (* the ports model at this turn (t_rp j = 0) *)
  destruct (w4e2_rp_unk (ACtlCut.c_in cx) j) as [(_ & Hu & Eu & Hdecl & Efst) | (Hr1 & _)]; [|lia].
  rewrite Eu in R23. unfold ACtlCutP.FIRSTb, ACtlCutP.b8 in HFIRST. rewrite Efst in HFIRST.
  destruct HPORTS as [HP0 _]. destruct (HP0 Hrp0) as (U0 & U4 & U8).
  unfold ACtlCutP.u32 in U0, U4, U8.
  rewrite w4e2_n_in in U0. rewrite w4e2_n_out in U4. rewrite w4e2_bt in U8.
  (* the block phi is live and visible, with its shadow hull *)
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (w4e2_block ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (proj1 HJ) Hin) as (Hp4096 & Hpc & Vb & Vbs).
  assert (Erq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
    by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia).
  rewrite Erq in Vb, Vbs.
  destruct HHB as (_ & HAB). unfold B.ACtlK.a_size in HAB.
  (* the spills the tail reads *)
  pose proof (w4e2_spill regs3 mem3 A 312 _ R9 ltac:(lia) ltac:(lia) S312) as Q312.
  pose proof (w4e2_spill regs3 mem3 A 136 _ R9 ltac:(lia) ltac:(lia) S136) as Q136.
  (* the cut's configuration in the runs' state form, moved to the loop's start map *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix C_B8292c_at [Z.of_nat j])) with 0x8292c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRg.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x8292c) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRg.xregs_eqv_sym _ _ (LRg.mkR_of_eqv regs3))].
  assert (Ereg : LRg.mkR_of regs3 =
    LFr.mkR (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
      (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8) (Z_to_bv 64 A)
      (Z_to_bv 64 (phi + 26 + Z.of_nat 0)) (Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_out (SM.t_pbs (ACtlCut.c_in cx) j) 0))
      (Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_in (SM.t_pbs (ACtlCut.c_in cx) j) 0)) (Z_to_bv 64 (B.Prog.Seg.F28.f28_nemp (SM.t_pbs (ACtlCut.c_in cx) j) 0))
      (Z_to_bv 64 (phi + 26 + Z.of_nat 0)) (Z_to_bv 64 (Prog.RcPorts.pu_first (SM.t_pbs (ACtlCut.c_in cx) j) 0))
      (Z_to_bv 64 (-8 - (phi + 18))) (Z_to_bv 64 (12 - Z.of_nat 0))
      (Sem.reg_get regs3 18) (Sem.reg_get regs3 19) (Sem.reg_get regs3 20) (Z_to_bv 64 (fr + 128))
      (Sem.reg_get regs3 22) (Z_to_bv 64 (4 * Prog.RcPorts.pu_nunk (SM.t_pbs (ACtlCut.c_in cx) j) 12)) (Sem.reg_get regs3 24)
      (Sem.reg_get regs3 25) (Z_to_bv 64 ART.ASAN_K) (Sem.reg_get regs3 27) (Z_to_bv 64 12)
      (Sem.reg_get regs3 29) (Sem.reg_get regs3 30) (Sem.reg_get regs3 31)).
  { unfold LRg.mkR_of. cbn [Z.of_nat Prog.RcLeaf.cnt B.Prog.Seg.F28.f28_nemp Prog.RcPorts.pu_first].
    rewrite Z.add_0_r, Z.sub_0_r.
    f_equal;
      first [ exact (w4e2_rgv_reg _ 9 _ eq_refl R9) | exact (w4e2_rgv_reg _ 10 _ eq_refl G10)
            | exact (w4e2_rgv_reg _ 11 _ eq_refl G11) | exact (w4e2_rgv_reg _ 12 _ eq_refl G12)
            | exact (w4e2_rgv_reg _ 13 _ eq_refl G13) | exact (w4e2_rgv_reg _ 14 _ eq_refl G14)
            | exact (w4e2_rgv_reg _ 15 _ eq_refl G15) | exact (w4e2_rgv_reg _ 16 _ eq_refl G16)
            | exact (w4e2_rgv_reg _ 17 _ eq_refl G17) | exact (w4e2_rgv_reg _ 21 _ eq_refl R21)
            | exact (w4e2_rgv_reg _ 23 _ eq_refl R23) | exact (w4e2_rgv_reg _ 26 _ eq_refl R26)
            | exact (w4e2_rgv_reg _ 28 _ eq_refl G28) ]. }
  rewrite Ereg.
  apply (w4e2_lift W3 _ md3 (fun ms' => exists R : bvmap 5 word,
    ms' = LMS.MS R CK11.fp_regs (Z_to_bv 64 0x82aa4) CK11.fp_csr None mem3 (BK11.seg_rom B.Img0.rsegs) /\
    CK11.getr R 2 = CK11.getr regs3 2 /\ CK11.getr R 3 = CK11.getr regs3 3 /\ CK11.getr R 4 = CK11.getr regs3 4 /\
    CK11.getr R 8 = CK11.getr regs3 8 /\ CK11.getr R 9 = CK11.getr regs3 9 /\
    CK11.getr R 18 = CK11.getr regs3 18 /\ CK11.getr R 19 = CK11.getr regs3 19 /\
    CK11.getr R 20 = CK11.getr regs3 20 /\ CK11.getr R 21 = CK11.getr regs3 21 /\
    CK11.getr R 24 = CK11.getr regs3 24 /\ CK11.getr R 26 = CK11.getr regs3 26 /\
    CK11.getr R 27 = CK11.getr regs3 27)).
  - (* the 12-turn loop, then the tail (continuation-passing) *)
    eapply (B.Prog.Seg.F28F.f28_loop_F (PB.RNG_W (Reusable.YA0n.w_H W3)) 12 0) with (phi := phi) (pbs := (SM.t_pbs (ACtlCut.c_in cx) j)).
    + reflexivity.
    + lia.
    + exact Hphi0.
    + exact Hphi50.
    + intros t Ht.
      pose proof (w4e2_bytes_nth _ _ _ (8 + t) Hblk ltac:(rewrite w4e2_blk_len; lia)) as Hbt.
      rewrite <- (w4e2_pbs_blk (ACtlCut.c_in cx) j (8 + t) (Z_to_bv 8 0) ltac:(lia)) in Hbt.
      replace (phi + 18 + Z.of_nat (8 + t)) with (phi + 26 + Z.of_nat t) in Hbt by lia.
      exact Hbt.
    + intros t Ht. replace (phi + 26 + Z.of_nat t) with (phi + (26 + Z.of_nat t)) by lia.
      apply (w4e2_addr_sub _ _ _ _ _ HAB); lia.
    + intros t Ht. apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. apply Vb. lia.
    + intros t Ht. pose proof (w4e2_hull phi (ACtlCutP.flen cx j) (phi + 26 + Z.of_nat t) ltac:(lia) ltac:(lia)) as Hh.
      destruct (w4e2_shadow_rng (phi + 26 + Z.of_nat t) ltac:(lia)) as [Hs0 Hs1].
      apply PB.rng_RNG_W; [lia | lia |].
      intros a Ha. apply Vbs. lia.
    + intros t1' t2'.
      pose proof (B.Prog.Seg.F28.f28_cnt_bound Prog.RcLeaf.is_in (SM.t_pbs (ACtlCut.c_in cx) j) 12) as Bin.
      pose proof (B.Prog.Seg.F28.f28_cnt_bound Prog.RcLeaf.is_out (SM.t_pbs (ACtlCut.c_in cx) j) 12) as Bout.
      pose proof (B.Prog.Seg.F28.f28_nemp_bound (SM.t_pbs (ACtlCut.c_in cx) j) 12) as Bemp.
      pose proof (Prog.RcPortsLib.pu_nunk_range (SM.t_pbs (ACtlCut.c_in cx) j) 12) as Bunk.
      pose proof (B.Prog.Seg.F28.f28_total (SM.t_pbs (ACtlCut.c_in cx) j) 12) as Btot.
      change (Z.of_nat 12) with 12 in Bin, Bout, Bemp, Bunk, Btot.
      assert (Bfst : 0 <= Prog.RcPorts.pu_first (SM.t_pbs (ACtlCut.c_in cx) j) 12 < 256)
        by (destruct (B.Prog.Seg.F28.f28_first_nunk (SM.t_pbs (ACtlCut.c_in cx) j) 12) as [(_ & E)|(_ & E)]; lia).
      pose proof (w4e2_bytes_nth _ _ _ 7 Hblk ltac:(rewrite w4e2_blk_len; lia)) as Hb7.
      rewrite <- (w4e2_pbs_blk (ACtlCut.c_in cx) j 7 (Z_to_bv 8 0) ltac:(lia)) in Hb7.
      replace (phi + 18 + Z.of_nat 7) with (phi + 25) in Hb7 by lia.
      assert (Hb7' : LMm.bytes_at B.Img0.rsegs mem3 (phi + 25) [Z_to_bv 8 (bv_unsigned (nth 7 (SM.t_pbs (ACtlCut.c_in cx) j) (Z_to_bv 8 0)))])
        by (rewrite Z_to_bv_bv_unsigned; exact Hb7).
      (eapply (B.Prog.Seg.F28F.f28_tail_F (PB.RNG_W (Reusable.YA0n.w_H W3))) with (A := A) (fr := fr)
        (bt7 := bv_unsigned (nth 7 (SM.t_pbs (ACtlCut.c_in cx) j) (Z_to_bv 8 0)))).
      * exact Hphi0.
      * exact Hphi50.
      * exact Bin.
      * exact Bout.
      * exact Bemp.
      * exact Bunk.
      * lia.
      * exact Bfst.
      * exact (B.Prog.Seg.F28.f28_ubyte _).
      * exact (B.Prog.Seg.F27F.f27f_rd8 _ _ _ Q136 (LMm.length_le8 _)).
      * exact (B.Prog.Seg.F27F.f27f_rd8 _ _ _ Q312 (LMm.length_le8 _)).
      * exact (B.Prog.Seg.F27F.f27f_rd4 _ _ _ U0 (LMm.length_le4 _)).
      * exact (B.Prog.Seg.F27F.f27f_rd4 _ _ _ U4 (LMm.length_le4 _)).
      * exact (B.Prog.Seg.F27F.f27f_rd4 _ _ _ U8 (LMm.length_le4 _)).
      * exact (B.Prog.Seg.F28F.f28f_rd1 _ _ _ HFIRST).
      * exact (B.Prog.Seg.F28F.f28f_rd1 _ _ _ Hb7').
      * apply (w4e2_addr_sub _ _ _ _ _ HAB); lia.
      * apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. exact (proj1 (Vstk a ltac:(lia))).
      * apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. exact (proj1 (Vstk a ltac:(lia))).
      * apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. exact (Vfr a ltac:(lia)).
      * apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. exact (Vfr a ltac:(lia)).
      * apply PB.rng_RNG_W; [lia | lia |]. intros a Ha. apply Vb. lia.
      * pose proof (w4e2_hull phi (ACtlCutP.flen cx j) (phi + 25) ltac:(lia) ltac:(lia)) as Hh.
        destruct (w4e2_shadow_rng (phi + 25) ltac:(lia)) as [Hs0 Hs1].
        apply PB.rng_RNG_W; [lia | lia |].
        intros a Ha. apply Vbs. lia.
      * intros a0' a1' a2' a3' a4' a5' a6'.
        eexists. (split; [reflexivity|]).
        (split; [reflexivity|]). (split; [reflexivity|]). split; [reflexivity|]. split; [reflexivity|].
        (split; [transitivity (Z_to_bv 64 A); [reflexivity | symmetry; exact R9]|]).
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [transitivity (Z_to_bv 64 (fr + 128)); [reflexivity | symmetry; exact R21]|].
        split; [reflexivity|].
        split; [transitivity (Z_to_bv 64 ART.ASAN_K); [reflexivity | symmetry; exact R26]|].
        reflexivity.
  - (* the exit cut, B82aa4_at j: same memory, the kept registers *)
    intros ms' md' HQ Hgr Hhid Hsbm.
    destruct HQ as (R & Ems & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E24 & E26 & E27).
    subst ms'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix C_B82aa4_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (Haa4 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + exact (w4e2_aj_same cx ly3 S3 W3 mem3 md3 md' k _ HJ Hsbm).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82aa4_at ACtlCutP.ixn nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact (w4e2_frac_keep cx fr fr regs3 R mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [split; [lia | exact HAB]|].
      split; [unfold ACtlCut.rgv in *; rewrite E18; exact R18|].
      split; [unfold ACtlCut.rgv in *; rewrite E20; exact R20|].
      split; [exact (w4e2_FTURN_keep _ _ _ _ _ _ E9 HFTURN)|].
      split; [exact (w4e2_LK_keep _ _ _ _ _ _ E9 E27 HLK)|].
      split; [exact (w4e2_FTL_keep _ _ _ _ _ _ _ E9 E21 E24 HFTL)|].
      exact HIFS.
    + exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82aa4_at j (0x82aa4) --S_F29--> B82abc_at j.
   0x82aa4 sb s11,16(s3); sb s11,17(s3); sb s11,20(s3) (S(fr) + 16 / 17 / 20 := 0xf8, the ports words and the
   first byte leave scope); addi s6,zero,1; mv s9,s8 (s9 = the sum flag); ld s8,272(s1) (s8 = t_k)
   (UB Seg/F29.v:3-10).  SINK BRANCHES: none (objdump L85494-L85499). *)
Lemma seg_F29 : forall POST (j : nat),
  ctl_from POST (ix C_B82abc_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82aa4_at [Z.of_nat j]).
Proof.
  intros POST j Habc cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  destruct HBODY as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_B82aa4_at ACtlCutP.ixn ACtlCutP.fcutp_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn & Hj & HHB & H18 & H20 & HFTURN & HLK & HFTL & HIFS).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4e2k_cut6 cx fr k ly3 S3 W3 mem3 md3 HJ HF HG1)
    as (Efr & _ & Hfr4096 & Hfrc & Happ & Himgfr & Hnimg & Hfrpres & Hshpres & _ & Hcspc & Hcsp47 & Hstkpres).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as (Hc1 & Hc2).
  unfold Reusable.YCfn.LLVMF_STK in Hcspc.
  pose proof HJ as (HAR & _).
  pose proof HFTL as (T21 & T184 & T272 & T24 & T312).
  pose proof (w4e2k_spill_A regs3 mem3 272 _ A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) T272) as Q272.
  (* the frame shadow's placement: in shadow memory, apart from the frame, the stack, the image's shadow *)
  assert (HS : ART.LOWMEM_END + 512 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= ART.HIGHMEM_BEG /\
               ACtlCutP.Sfr fr + 512 <= A /\ (fr + 4096 <= ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= fr) /\
               (ACtlCutP.Sfr fr + 512 <= 2147450880 + 81584 \/ 2147450880 + 81598 <= ACtlCutP.Sfr fr)).
  { unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, ART.LOWMEM_END, ART.HIGHMEM_BEG.
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
    Z.div_mod_to_equations. lia. }
  destruct HS as (HS1 & HS2 & HS3 & HS4 & HS5).
  unfold ART.LOWMEM_END in HS1. unfold ART.HIGHMEM_BEG in HS2.
  assert (Hcb : exists junk, lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 16)
                               [lib.Lib.Cells.CB 5 junk]).
  { apply w4e2k_cb_raw; [lia | lia |].
    intros x Hx. exact (proj2 (Hshpres x ltac:(cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia))). }
  destruct Hcb as (junk & Hcb).
  assert (HRO : B.MemNorm.ro_agree B.Img0.rsegs mem3) by exact (proj2 (proj2 (proj2 HRT))).
  (* 0x82aa4 -> 0x82abc: the three shadow stores and the t_k load (f29_evt_ro_F), one lift *)
  apply w4e2m_enter.
  eapply w4e2m_run; [| apply B.ProgBridge.fp_avoids_RNG_W |].
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply (B.Prog.Seg.F29F.f29_evt_ro_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
      with (S3 := ACtlCutP.Sfr fr) (A := A) (kv := SM.t_k (ACtlCut.c_in cx) j) (bs := junk).
    - exact (w4e2w_rgv_reg _ 19 _ eq_refl Hr19).
    - exact (w4e2w_rgv_reg _ 9 _ eq_refl Hr9).
    - exact Hcb.
    - exact Q272.
    - exact HRO.
    - unfold ART.LOWMEM_END. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply B.ProgBridge.rng_of_visible.
      split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hshpres a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible.
      apply (w4e2m_vis_stack cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia. }
  intros ms' md' (R & m' & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E26 & E27 & E25 & E22 & E24 &
    MU & WM & _ & cs & Hcs & Hcsl) Hsbm Hhid.
  apply (w4e2m_exit W3 0x82abc).
  set (Wr := [(ACtlCutP.Sfr fr + 16, ACtlCutP.Sfr fr + 21)]).
  assert (Hout : forall x, x < ACtlCutP.Sfr fr + 16 \/ ACtlCutP.Sfr fr + 21 <= x -> lib.Lib.Frame.outside Wr x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside Wr]; split; [lia | exact I]).
  assert (HW : forall a, ~ lib.Lib.Frame.outside Wr a ->
                 ~ Reusable.YG0d.in_img segs a /\ exists b, m' (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. apply w4e2k_not_outside1 in Ha.
    assert (Hni : ~ Reusable.YG0d.in_img segs a)
      by (apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
    split; [exact Hni|].
    apply (w4e2_rw_cells_present m' (ACtlCutP.Sfr fr + 16) cs a Hcs); [rewrite Hcsl; cbn; lia | | exact Hni].
    lia. }
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w4e2k_after_run cx ly3 S3 W3 mem3 md3 k m' md' Wr HJ MU Hhid Hsbm).
    intros a Ha. split; [exact (proj2 (HW a Ha))|].
    apply w4e2k_not_outside1 in Ha. apply (w4e2k_awr_fsh cx ly3 fr _ _ _ _ a Efr). lia. }
  pose proof (w4e2k_ctlrtC_run ly3 S3 mem3 m' Wr HRT MU WM HW) as HRT'.
  assert (KEPT : forall x, 0 <= x < 2 ^ 64 -> (x < ACtlCutP.Sfr fr + 16 \/ ACtlCutP.Sfr fr + 21 <= x) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx H; exact (w4e2k_mrd_munch Wr mem3 m' x MU Hx (Hout x H))).
  assert (KSA : forall x : Z, A <= x < ACtlCut.c_sp cx ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KF : forall x : Z, fr <= x < fr + 4096 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (KSH : forall x : Z, ACtlCutP.Sfr fr + 320 <= x < ACtlCutP.Sfr fr + 512 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x))
    by (intros x Hx; apply KEPT; lia).
  assert (Hkn : forall i, 0 <= i < 112 ->
             2147450880 + 81584 <= B.AsanRT.shadow_addr (ACtlCutP.KNA.KIND_NAME + i) <= 2147450880 + 81597)
    by exact w4e2k_kn_shadow.
  assert (KK : forall x : Z, ACtlCutP.KNA.KIND_NAME <= x < ACtlCutP.KNA.KIND_NAME + 112 ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { unfold ACtlCutP.KNA.KIND_NAME. intros x Hx. apply KEPT; [lia|].
    left. lia. }
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & Hpapp & _ & _ & Hnrange).
  assert (Hfin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (w4e2_block_frame_apart ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hin Hfin) as Hapart.
  rewrite <- Efr in Hapart. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hapart.
  assert (Hreq : B.ACtlK.a_size (ACtlCutP.flen cx j) = Reusable.YG00.req_size (ACtlCutP.flen cx j) /\
                 0 < Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (KBS : forall i, 0 <= i < B.ACtlK.a_size (ACtlCutP.flen cx j) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))).
  { intros i Hi. rewrite (proj1 Hreq) in Hi. apply KEPT.
    - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, ART.shadow_addr, ART.ASAN_K in *.
      Z.div_mod_to_equations. lia. }
  assert (KB : forall x : Z, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 x)).
  { intros x Hx. apply KEPT; [lia|].
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    lia. }
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha. destruct (Hfrpres a ltac:(lia)) as (_ & b & Hb).
    exists b. rewrite (MU (Z_to_bv 64 a)); [exact Hb|].
    change (Z_to_bv 64 a) with (lib.Lib.Mem.wa a). rewrite lib.Lib.Mem.wa_unsigned by lia. apply Hout. lia. }
  assert (HKA : B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112).
  { pose proof HLK as (_ & _ & _ & HFLI). unfold ACtlCutP.FLI in HFLI.
    destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & (_ & HKA0) & _).
    apply (w4e2m_bcmp_addr mem3 m' _ 112); [| exact HKA0].
    intros i Hi. pose proof (Hkn i Hi) as Hk'. apply KEPT; [lia|]. lia. }
  assert (KShr : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
             exists b, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = Some b).
  { intros x Hx.
    assert (Hni : ~ Reusable.YG0d.in_img segs x)
      by (apply w4e2k_not_img_high; unfold Reusable.YG0f.kLowMemEnd; lia).
    destruct (Z_lt_le_dec x (ACtlCutP.Sfr fr + 16)) as [Hlo|Hlo];
      [| destruct (Z_lt_le_dec x (ACtlCutP.Sfr fr + 21)) as [Hmid|Hhi]].
    - destruct (Hshpres x ltac:(lia)) as (_ & b & Hb). exists b.
      change (lib.Lib.Mem.wa x) with (Z_to_bv 64 x). rewrite (KEPT x ltac:(lia) ltac:(lia)).
      exact (w4e2k_raw_mrd _ _ _ Hb).
    - destruct (HW x) as (_ & b & Hb).
      { intros Ho. cbn [lib.Lib.Frame.outside Wr] in Ho. destruct Ho as [Ho _]. lia. }
      exists b. exact (w4e2k_raw_mrd _ _ _ Hb).
    - destruct (Hshpres x ltac:(lia)) as (_ & b & Hb). exists b.
      change (lib.Lib.Mem.wa x) with (Z_to_bv 64 x). rewrite (KEPT x ltac:(lia) ltac:(lia)).
      exact (w4e2k_raw_mrd _ _ _ Hb). }
  pose proof (w4e2_getr_keep _ _ _ E2) as F2. pose proof (w4e2_getr_keep _ _ _ E3) as F3.
  pose proof (w4e2_getr_keep _ _ _ E4) as F4. pose proof (w4e2_getr_keep _ _ _ E8) as F8.
  pose proof (w4e2_getr_keep _ _ _ E9) as F9. pose proof (w4e2_getr_keep _ _ _ E18) as F18.
  pose proof (w4e2_getr_keep _ _ _ E19) as F19. pose proof (w4e2_getr_keep _ _ _ E20) as F20.
  pose proof (w4e2_getr_keep _ _ _ E26) as F26. pose proof (w4e2_getr_keep _ _ _ E27) as F27.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Hs; exact (w4e2m_bcmp_sp R regs3 mem3 m' A (ACtlCut.c_sp cx) off v Hr9 F9 ltac:(lia)
                                     ltac:(lia) ltac:(lia) KSA Ho Hs)).
  apply (Habc cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB HJ' HF HG1 Hk); [| exact HRT'].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_B82abc_at ACtlCutP.ixn
    ACtlCutP.fcutp_body nth].
  split; [reflexivity|]. rewrite Nat2Z.id.
  split.
  { apply (w4e2k_FRAC_keep cx fr fr regs3 R mem3 m' HFRAC F2 F3 F4 F8 F9 F19 F26); [| | exact KShr].
    - intros x Hx. rewrite HspZ in Hx. apply KEPT; lia.
    - intros x Hx. apply KEPT; lia. }
  exists phi.
  split; [exact Hperm|]. split; [exact Hn|]. split; [exact Hj|].
  split; [exact (w4e2m_bcmp_HB mem3 m' phi _ KBS HHB)|].
  split; [exact (w4e2m_rgv_tr R regs3 18 _ F18 H18)|].
  split; [exact (w4e2m_rgv_tr R regs3 20 _ F20 H20)|].
  split.
  { apply (w4e2m_bcmp_FTURN cx j phi R regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 F9); [lia | lia | lia | exact KSA | |
      exact HFTURN].
    intros x Hx. apply KB. destruct Hreq as (Hr1 & Hr2'). unfold Reusable.YG00.req_size in *.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  split.
  { exact (w4e2m_bcmp_LK cx fr j R regs3 mem3 m' A (ACtlCut.c_sp cx) Hr9 F9 F27 ltac:(lia) ltac:(lia) ltac:(lia)
             KSA (fun x Hx => KF x ltac:(lia)) KSH KK HKA Hpr HLK). }
  split.
  { (* FTK *)
    split; [exact (SP 184 _ ltac:(lia) T184)|].
    split; [exact (w4e2_rgv_set _ _ _ E22)|].
    split; [exact (w4e2_rgv_set _ _ _ E24)|].
    split; [exact (SP 272 _ ltac:(lia) T272)|].
    exact (w4e2_rgv_move R regs3 25 24 _ E25 eq_refl eq_refl T24). }
  split; [exact (w4e2m_bcmp_IFS cx fr (S j) R regs3 mem3 m' (fun x Hx => KF x ltac:(lia)) KSH HIFS)|].
  exact (SP 312 _ ltac:(lia) T312).
Qed.

End W4e2.

(* Stage lemmas of this file (seg_F24 .. seg_F29, all six Qed on the route (C) shell;
   [j] = [Z.of_nat j]):
     seg_F24 : forall POST j, ctl_from POST (ix C_B82888_at [j]) -> ctl_from POST (ix C_B82878_at [j])
     seg_F25 : forall POST j, ctl_from POST (ix C_B828a4_at [j]) -> ctl_from POST (ix C_B82888_at [j])
     seg_F26 : forall POST j, ctl_from POST (ix C_B828b4_at [j]) -> ctl_from POST (ix C_B828a4_at [j])
     seg_F27 : forall POST j, ctl_from POST (ix C_B8292c_at [j]) -> ctl_from POST (ix C_B82aa4_at [j]) ->
                               ctl_from POST (ix C_B828b4_at [j])
     seg_F28 : forall POST j, ctl_from POST (ix C_B82aa4_at [j]) -> ctl_from POST (ix C_B8292c_at [j])
     seg_F29 : forall POST j, ctl_from POST (ix C_B82abc_at [j]) -> ctl_from POST (ix C_B82aa4_at [j])
   Trap / sink obligations: S_F27 (0x828b4, 0x828c0, 0x828d0, 0x828dc, 0x828e8 -> 0x82fa4; 0x828f8 -> 0x82fa0, row
   53) and S_F28 (rows 54-64 -> 0x82fa0; seven FAIL branches -> 0x82fa4; two report paths), each discharged inside
   its `_F` stretch from the cut-body conjuncts named at the stage. *)
