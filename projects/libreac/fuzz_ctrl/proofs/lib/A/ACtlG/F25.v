(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e2.v, with its module paths and module names changed; 4090 of its 4391 lines of code are new or changed and 2544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4c.v, with its module names and addresses changed; 578 of its 611 lines of code are new or changed and 4358 lines of the source are left out. *)
(* lib/A/ACtlG/F25.v -- GLUE for stage seg_F25 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:822).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F25 : forall POST (j : nat),
       CF POST (ix_cut C_A825f4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825d4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F25.  Segment F25 is 0x825d4 -> 0x825f4 (Seg/F25.v): the frame shadow byte S(fr) + 20 is set
   to 1 (0x825dc), the spill [A + 120] = fr + 160 is loaded, the frame byte `first` at fr + 160 is cleared
   (0x825e8), and reac_ports_unknown@0x87848 is called at 0x825f0 with c = fr + 160, landing at 0x825f4.

   ROUTE (a) -- NO LIFT, NO SPLIT (a Theorem Labs lane, 2026-10-29 04:10Z).  The run lifted is Seg/F25Fon.v's f25_evt_F_on
   (this lane's route (C) twin of Seg/F25F.v's (not in this delivery) f25_evt_F, with no shadow premise); it takes
   reac_ports_unknown_c.reac_ports_unknown_contract_F_on AS A PREMISE and its run SPANS the call, so this file
   supplies that premise with the PROVED contract (A/Prog/reac_ports_unknownF.v reac_ports_unknown_F_holds_on)
   and lifts the WHOLE run once with Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  It
   cites NO <f>_SRr_at: the caller obligation is the CONTRACT's premises, which f25_evt_F_on states.

   ROUTE (C) (a Theorem Labs lane 1502cba0417 / 1899bed1aee): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The
   run needs no shadow byte from it: its one shadow STORE (0x825dc, S(fr) + 20) is justified by the run's own
   premise wr_at (sfr + 20) 1 (AR_frames_law), and the callee's _on contract dropped its shadow premise.  The exit
   cut has the same state (ly3, S3), so the entry's two regions (cut_shadow B ly3 S3, img_shadow) are carried to it
   by the same per-address argument the old exit used for the universal shadow_rw (lemma KEEPSH below): a byte
   outside W is unchanged (munch), the written byte S(fr) + 20 is present by the run's post, writability by wmono.

   THE PROOF -- the steps of lib/A/ACtlG/F26.v (G1-G5, read its header), with what F25 adds:
   - the write set is W = [S(fr) + 20, S(fr) + 21) ++ [fr + 160, fr + 161) ++ [sp - 16, sp): one SHADOW
     byte, one frame byte, the callee's window.  W is not all app memory, so a kept range must miss W by
     address AND by shadow byte: KEEP p n := disjoint_from W p n /\ every shadow byte of [p, p + n) is
     outside W.  f25_keepi gives KEEP for any app range below the window (or above sp) that misses the
     8-byte granule [fr + 160, fr + 168); B7Cuts.b7_addr_munch is the addressable transport.
   - the frame lies above the image (a Theorem Labs lane's A.ProgWorld.ctl_frame_above_img_stmt, proved premise-free by
     A.ProgWorld_Fs.ctl_frame_above_img) and in app memory (b7g_frame_app); the frame
     shadow byte S(fr) + 20 and the frame byte fr + 160 are present and visible from AR_frames_law.
   - the exit body's three new facts come from the run's post: FIRSTb = the post's b8 at fr + 160,
     addressable (fr + 160) 1 from the post's shadow byte 1 at S(fr) + 20 (fr + 160 is 8-aligned), and
     FRAC's 392 frame shadow bytes become `upd_bytes sh 20 [b1]` (f25_sh_upd).
   - the shadow regions survive the shadow write directly (the written byte is present by the post).
   - the journal's write set is covered by awr_byte's stack disjunct and by in_frames (the frame byte and
     the frame's own shadow byte).

   SECTION HYPOTHESES (exact text in the file; why) -- only LAWS, as F26:
   - LAWS : Reusable.YG0d.AR_laws segs B (ACtl.v:183).
   No other Section hypothesis: the kit's image facts are CITED, A.ACtlG.Kit.kit_wx and
   A.ACtlG.Kit.kit_segs_low (glue base 46eb24cd4b3, Kit.v 7e164a09a73 builds); on the first base (commit
   da4498df513) they were named Section hypotheses with the kit's exact text.  The frame bound is CITED by name,
   A.ProgWorld.ctl_frame_above_img_stmt (proof A.ProgWorld_Fs.ctl_frame_above_img); the TEMPORARY local copy
   A.ACtlG.F26.b7g_frame_GT it replaces is deleted.

   CLOSURE: every Require is qualified; no statement of this file names a frame-route identifier
   (A.Contract, A.Prog.SlotInv and A/Prog/Seg/* are named only inside proofs closed by Qed).  Twin-copy
   modules (core Reusable.YK11 / YK1b / YM05 / YO09 / YI16, Lib.Mem / Frame / PropExec / MState) are
   Required by their FULL path, as F26.v says.

   BUILD STATE: type-checks on a working branch 1899bed1aee (a working branch); its build of
   record (cbrec) is reported by the lane, not here.  No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0n Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.SlotModel A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_unknown_c A.Prog.reac_ports_unknownF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.B7Cuts A.Prog.Seg.F24 A.Prog.Seg.F25Fon.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Contract A.Reusable.YP09 A.MemNorm A.Prog.SlotInv.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.F26.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorld_Fs.

(* The CORE's lib/Reusable modules that have NO second copy, under the short name this file uses; YK11 / YM05 / YO09
   are written lib.Reusable.<X>.<name> (see lib/A/ACtlG/F26.v). *)
Module Reusable.
  Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
  Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
  Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
  Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
  Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
  Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
  Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
  Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
  Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
  Module YG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
  Module YI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
  Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
  Module YK06 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK06.
  Module YK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
End Reusable.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. F25's own helpers. *)

(* A byte of an in_app range is AsanRT app memory. *)
Lemma f25_in_app : forall {rc : lib.Reusable.YM05.RunCeil} lo len a,
  Reusable.YG0f.in_app lo len -> lo <= a < lo + len -> A.AsanRT.app_mem a.
Proof.
  intros rc lo len a Happ Ha.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ.
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
  destruct Happ as (H4096 & [HL | (HH1 & HH2)]); [left | right]; lia.
Qed.

(* The spill [A + off] read through s1 = A. *)
Lemma f25_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (Aa off v : Z),
  lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 Aa -> 0 <= Aa -> Aa + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (Aa + off) v.
Proof.
  intros regs m Aa off v H9 HA0 HA Ho0 Ho (A1 & H9' & Hq).
  unfold ACtlCut.rgv in H9'.
  assert (EA : A1 = Aa).
  { pose proof Hq as Hq'. unfold ACtlCutP.q64 in Hq'. destruct Hq' as (Hb0 & Hb1 & _).
    rewrite Lib.Mem.length_le8 in Hb1.
    assert (Ebv : Z_to_bv 64 Aa = Z_to_bv 64 A1) by (etransitivity; [symmetry; exact H9 | exact H9']).
    apply (f_equal (@bv_unsigned 64)) in Ebv. rewrite !Lib.MState.unsigned_lit_wrap in Ebv.
    change (Z.of_nat 8) with 8 in Hb1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* The kept ranges of F25's write set: an app range below the window (or at or above sp) that misses the
   8-byte granule [fr + 160, fr + 168) misses W by address and by shadow byte. *)
Lemma f25_keepi : forall (fr sp p n : Z),
  0 <= fr -> fr mod 8 = 0 -> A.AsanRT.app_mem (fr + 160) ->
  A.AsanRT.HIGHMEM_BEG <= sp - 16 ->
  0 <= n ->
  (forall x, p <= x < p + n -> A.AsanRT.app_mem x) ->
  (p + n <= fr + 160 \/ fr + 168 <= p) ->
  (p + n <= sp - 16 \/ sp <= p) ->
  Lib.Frame.disjoint_from [(ACtlCutP.Sfr fr + 20, ACtlCutP.Sfr fr + 21); (fr + 160, fr + 161); (sp - 16, sp)] p n /\
  (forall i, 0 <= i < n ->
     Lib.Frame.outside [(ACtlCutP.Sfr fr + 20, ACtlCutP.Sfr fr + 21); (fr + 160, fr + 161); (sp - 16, sp)]
       (A.AsanRT.shadow_addr (p + i))).
Proof.
  intros fr sp p n Hfr0 Hfr8 Happ160 Hsp Hn Happ Hgr Hwin.
  assert (Esh : ACtlCutP.Sfr fr + 20 = A.AsanRT.shadow_addr (fr + 160)).
  { unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hsh : A.AsanRT.in_shadow (ACtlCutP.Sfr fr + 20))
    by (rewrite Esh; exact (A.AsanRTFacts.shadow_of_app _ Happ160)).
  split.
  - cbn [Lib.Frame.disjoint_from]. split; [| split; [| split; [| exact I]]].
    + destruct (Z_le_gt_dec (p + n) (ACtlCutP.Sfr fr + 20)) as [H1 | H1]; [left; exact H1 |].
      destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 21) p) as [H2 | H2]; [right; exact H2 |].
      exfalso. apply (A.AsanRTFacts.app_not_shadow (ACtlCutP.Sfr fr + 20)); [apply Happ; lia | exact Hsh].
    + destruct Hgr; [left | right]; lia.
    + exact Hwin.
  - intros i Hi. cbn [Lib.Frame.outside].
    assert (Hx : A.AsanRT.app_mem (p + i)) by (apply Happ; lia).
    pose proof (A.AsanRTFacts.shadow_of_app _ Hx) as Hs.
    split; [| split; [| split; [| exact I]]].
    + clear Hs Hx Happ Hsh Esh. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
      intros Hc. Z.div_mod_to_equations. lia.
    + intros Hc. apply (A.AsanRTFacts.app_not_shadow (A.AsanRT.shadow_addr (p + i))); [| exact Hs].
      replace (A.AsanRT.shadow_addr (p + i)) with (fr + 160) by lia. exact Happ160.
    + unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

(* A byte list over which a run wrote exactly one byte (index k), the rest outside its write set. *)
Lemma f25_sh_upd : forall (W : list Lib.Frame.ivl) (m m' : word -> option byte) (a : Z) (sh : list byte)
    (k : nat) (b : byte),
  Lib.Mem.bytes_at segs m a sh -> (k < length sh)%nat ->
  Lib.Frame.munch W m m' ->
  (forall i, (i < length sh)%nat -> i <> k -> Lib.Frame.outside W (a + Z.of_nat i)) ->
  Lib.Mem.bytes_at segs m' (a + Z.of_nat k) [b] ->
  Lib.Mem.bytes_at segs m' a (Lib.Mem.upd_bytes sh k [b]).
Proof.
  intros W m m' a sh k b (Ha & Hal & H) Hk MU Hout (_ & _ & Hb).
  assert (Hlen : length (Lib.Mem.upd_bytes sh k [b]) = length sh)
    by (apply Lib.Mem.upd_bytes_length; cbn [length]; lia).
  split; [exact Ha |]. split; [rewrite Hlen; exact Hal |].
  intros i Hi. rewrite Hlen in Hi.
  rewrite Lib.Mem.upd_bytes_nth by (cbn [length]; lia). cbn [length].
  destruct (Nat.leb_spec0 k i) as [Hki | Hki]; destruct (Nat.ltb_spec0 i (k + 1)) as [Hik | Hik];
    cbn [andb].
  - assert (i = k) by lia. subst i. rewrite Nat.sub_diag.
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0.
  - unfold Lib.Mem.mrd in *. rewrite (MU (Lib.Mem.wa (a + Z.of_nat i))); [apply H; exact Hi |].
    rewrite Lib.Mem.wa_unsigned by lia. apply Hout; [exact Hi | lia].
  - unfold Lib.Mem.mrd in *. rewrite (MU (Lib.Mem.wa (a + Z.of_nat i))); [apply H; exact Hi |].
    rewrite Lib.Mem.wa_unsigned by lia. apply Hout; [exact Hi | lia].
  - lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The stage. *)

Section GlueF25.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :295-296), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A825d4_at := (ACtlCutP.C_A825d4_at B).
Local Notation C_A825f4_at := (ACtlCutP.C_A825f4_at B).

(* The core's AR law record (YCbq.v:207, Section a0's hypothesis), as ACtl.v:183 states it. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The kit's image facts are cited by name below: A.ACtlG.Kit.kit_wx and A.ACtlG.Kit.kit_segs_low. *)

Lemma glue_seg_F25 : forall POST (j : nat), CF POST (ix_cut C_A825f4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825d4_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  pose proof A.Prog.SlotInv.FRAME_BYTES_val as HFBv. pose proof A.Prog.SlotInv.FRAME_SHADOW_val as HFSv.
  (* G1: the entry cut at index [Z.of_nat j] (C_A825d4_at, ACtlCutP.v:2622-2630). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825d4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & HBODY).
  destruct HBODY as (phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HB7K & HP).
  cbv beta in HP.
  destruct HP as (R10 & HPORTS & HADq).
  destruct Hrt as (HAC & Hcut & Himgsh & HRO).
  (* G2: the geometry (as F26), plus the frame's own facts. *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkok & _ & _).
  destruct Hstkok as (_ & _ & Hceil & Hstklo & _ & _ & _ & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite HF. cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825d4_at ACtlCut.own6].
    left. reflexivity. }
  assert (Hown6 : In (6, ACtlCut.c_fpos cx) (ACtlCut.cut_own (ix_cut C_A825d4_at [Z.of_nat j]) cx)).
  { cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825d4_at ACtlCut.own6].
    left. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr3 : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) Hown6). unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  rewrite <- Efr3 in Hf4096, Hfceil.
  (* the frame lies above the loaded image: a Theorem Labs lane's statement, cited by name *)
  pose proof ((A.ProgWorld_Fs.ctl_frame_above_img B : A.ProgWorld.ctl_frame_above_img_stmt B)
                ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as HGT.
  rewrite <- Efr3 in HGT.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfrapp & Hfpres & Hfshp).
  rewrite <- Efr3 in Hfrapp, Hfpres, Hfshp.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfrapp, Hfpres, Hfshp.
  change (4096 / 8) with 512 in Hfshp.
  assert (Hfrbyte : forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a)
    by (intros a Ha; exact (f25_in_app fr 4096 a Hfrapp Ha)).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hcmin Hcmax] _].
  (* FRAC's own names. *)
  destruct HFRAC as (Aa & sp & HC).
  pose proof HC as (R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA416 & Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo.
  unfold A.AsanRT.APPMEM_END in HSapp.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hwin : fr + 4096 < sp - 16 /\ A.Prog.ImgBounds.IMG_HI <= sp - 16 /\ sp <= ACtlCut.c_sp cx /\
                 A.AsanRT.HIGHMEM_BEG <= sp - 16).
  { unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.HIGHMEM_BEG. repeat split; lia. }
  destruct Hwin as (Hfrwin & Himg & Hspsp & Hhm).
  assert (Hsp0 : 0 <= sp - 16 /\ sp < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  (* the frame shadow byte S(fr) + 20 *)
  set (sfr := ACtlCutP.Sfr fr) in *.
  assert (Esfr : sfr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (Esh160 : A.AsanRT.shadow_addr (fr + 160) = sfr + 20).
  { rewrite Esfr. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Happ160 : A.AsanRT.app_mem (fr + 160)) by (apply Hfrbyte; lia).
  (* the block of this turn *)
  assert (Hinblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  pose proof HB7K as (_ & _ & _ & Hphi0 & Hphi2 & Hflen & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinblk)
    as (_ & Hphi4096 & Hphiceil & Hphiapp & _).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  rewrite Hreq in Hphiceil, Hphiapp.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) 6
                (ACtlCut.c_fpos cx) HAR Hinblk Hin6) as Hsepb.
  unfold Reusable.YG0f.zdisjoint in Hsepb. cbn [fst snd] in Hsepb. rewrite Hreq, <- Efr3 in Hsepb.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsepb.
  assert (Hphib : forall a, phi <= a < phi + ACtlCutP.flen cx j -> A.AsanRT.app_mem a)
    by (intros a Ha; exact (f25_in_app phi (ACtlCutP.flen cx j) a Hphiapp Ha)).
  (* the input block *)
  pose proof HB as (HBpre & _).
  pose proof HBpre as (_ & _ & _ & _ & Hinp & Hinlen & _).
  assert (Hinlen' : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by lia.
  assert (Hinput : (ACtlCut.c_n cx = 0 /\ ACtlCut.c_p cx = A.ACfn.A_EMPTY) \/
                   (0 < ACtlCut.c_n cx /\ In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))).
  { destruct Hinp as [H0 | (Hn0 & Hinb)]; [left; exact H0 | right; split; [lia |]].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinb. }
  (* the input lies below the window and apart from the frame's granule [fr + 160, fr + 168) *)
  assert (Hinbound : 0 <= ACtlCut.c_p cx /\
                     ACtlCut.c_p cx + ACtlCut.c_n cx <= lib.Reusable.YM05.alloc_ceiling /\
                     (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> A.AsanRT.app_mem x) /\
                     (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr + 160 \/ fr + 168 <= ACtlCut.c_p cx)).
  { destruct Hinput as [(Hn0 & Hp0) | (Hn0 & Hinb)].
    - rewrite Hp0, Hn0. unfold A.ACfn.A_EMPTY.
      split; [lia |]. split; [lia |]. split; [intros x Hx; lia | left; lia].
    - destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR Hinb)
        as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) 6
                    (ACtlCut.c_fpos cx) HAR Hinb Hin6) as Hsepi.
      unfold Reusable.YG0f.zdisjoint in Hsepi. cbn [fst snd] in Hsepi. rewrite <- Efr3 in Hsepi.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsepi.
      assert (Hrq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
      { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
      rewrite Hrq in Hpceil, Hpapp, Hsepi.
      split; [lia |]. split; [lia |].
      split; [intros x Hx; exact (f25_in_app _ _ x Hpapp Hx) |].
      destruct Hsepi; [left | right]; lia. }
  destruct Hinbound as (Hinp0 & Hinceil & Hinapp & Hingr).
  (* G2b: the run's premises *)
  assert (Hstk : Lib.Frame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { split; [lia |]. split; [change (2 ^ 64) with 18446744073709551616; lia |].
    intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hbv).
    assert (Hmrd : Lib.Mem.mrd A.Img0.rsegs mem3 (Lib.Mem.wa a) = Some b)
      by (unfold Lib.Mem.mrd, Lib.Mem.wa; rewrite Hbv; reflexivity).
    split; [| exists b; exact Hmrd].
    assert (Hga : A.Contract.GT <= a) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Himg; lia).
    pose proof (A.Prog.Seg.F24.b7_hi_wr mem3 a Hga ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                  (ex_intro _ b Hmrd)) as HWa.
    unfold A.Reusable.YP09.writable_at in HWa. exact HWa. }
  assert (HADp : A.AsanRT.addressable mem3 (phi + 18) 20).
  { destruct HHB as (_ & Hadphi). unfold A.ACtlK.a_size in Hadphi.
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.flen cx j) 1) 18 20 Hadphi); lia. }
  pose proof HB7K as (_ & _ & R22 & _ & _ & _ & Hblk & _).
  pose proof HFLSI as ((HPRO & _) & _).
  pose proof HPRO as (_ & P120 & _).
  (* the frame's shadow byte S(fr) + 20 and its byte fr + 160: present, so visible and writable *)
  assert (Esfr2 : Reusable.YG0f.shadow_addr fr = sfr) by (rewrite <- A.ACtlG.F26.b7g_sh_eq; reflexivity).
  destruct (Hfshp 20 ltac:(lia)) as ((Hsh20H & bsh & Hsh20) & _).
  rewrite Esfr2 in Hsh20H, Hsh20.
  destruct (Hfpres (fr + 160) ltac:(lia)) as ((H160H & b160 & H160) & _).
  assert (Hsfr0 : 0x7fff8000 <= sfr /\ sfr + 512 <= 0x10007fff8000).
  { rewrite Esfr. Z.div_mod_to_equations. lia. }
  assert (Wsh : Lib.Mem.wr_at A.Img0.rsegs mem3 (sfr + 20) 1).
  { apply (A.ACtlG.F26.b7g_wr1 mem3 (sfr + 20)); [unfold A.Prog.ImgBounds.IMG_HI; lia
      | change (2 ^ 64) with 18446744073709551616; lia | exists bsh; exact Hsh20]. }
  assert (W160 : Lib.Mem.wr_at A.Img0.rsegs mem3 (fr + 160) 1).
  { apply (A.ACtlG.F26.b7g_wr1 mem3 (fr + 160)); [unfold A.Prog.ImgBounds.IMG_HI; lia
      | change (2 ^ 64) with 18446744073709551616; lia | exists b160; exact H160]. }
  assert (Q120 : ACtlCutP.q64 mem3 (Aa + 120) (fr + 160)).
  { apply (f25_spill_at regs3 mem3 Aa 120 (fr + 160) R9); [lia | change (2 ^ 64) with 18446744073709551616; lia
      | lia | lia | exact P120]. }
  (* the block's 20 bytes miss the write set by shadow byte *)
  pose proof (f25_keepi fr sp (phi + 18) 20 ltac:(lia) Hfr8 Happ160 Hhm ltac:(lia)
                ltac:(intros x Hx; apply Hphib; lia)
                ltac:(destruct Hsepb; [left | right]; lia) ltac:(left; lia)) as (_ & KPsh).
  assert (HPSH : forall i, 0 <= i < 20 ->
            Lib.Frame.outside [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] (A.AsanRT.shadow_addr (phi + 18 + i))).
  { intros i Hi. destruct (KPsh i Hi) as (O1 & O2 & _). cbn [Lib.Frame.outside].
    split; [exact O1 | split; [exact O2 | exact I]]. }
  assert (HOUT : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                           A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
                  Lib.Frame.outside [(sp - 16, sp); (fr + 160, fr + 161)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [| split; [| exact I]].
    - unfold A.AsanRT.GOT_CELL_K, A.AsanRT.CELL_K, A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
        A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *.
      unfold A.Prog.ImgBounds.IMG_HI in Himg. lia.
    - intros Hc. destruct Hx as [Hx | [Hx | Hx]].
      + unfold A.AsanRT.GOT_CELL_K in Hx. lia.
      + unfold A.AsanRT.CELL_K in Hx. lia.
      + apply (A.AsanRTFacts.app_not_shadow x); [| exact Hx].
        replace x with (fr + 160) by lia. exact Happ160. }
  (* visibility of the footprint regions *)
  assert (V1 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.cut_own (ix_cut C_A825d4_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (VQ : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (Aa + 120) 8).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.cut_own (ix_cut C_A825d4_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 md3 k (Aa + 120) 8 HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (VSH : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sfr + 20) 1).
  { split; [lia |]. split; [change (2 ^ 64) with 18446744073709551616; lia |].
    intros a Ha. replace a with (sfr + 20) by lia. exact Hsh20H. }
  assert (V160 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (fr + 160) 1).
  { split; [lia |]. split; [change (2 ^ 64) with 18446744073709551616; lia |].
    intros a Ha. replace a with (fr + 160) by lia. exact H160H. }
  assert (VRT : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.RT_LO
                  (A.AsanRT.RT_HI - A.AsanRT.RT_LO)) by exact (A.ProgBridge.rt_vis_W W3).
  assert (V2 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.GOT_CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.GOT_CELL_K; lia. }
  assert (V3 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.CELL_K; lia. }
  assert (V4 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (phi + 18) 20).
  { apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 20
             HAR Hinblk); rewrite ?Hreq; lia. }
  assert (V5 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                 (A.AsanRT.shadow_addr (phi + 18))
                 (A.AsanRT.shadow_addr (phi + 18 + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                (phi + 18) 20 HAR Hinblk ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(lia)) as [Hz | Vsh];
      [lia |].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (phi + 18))
             (A.Prog.rng_asan.sh_al8_hi (phi + 18) 20 - A.Prog.rng_asan.sh_al8_lo (phi + 18)) _ _ Vsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr;
      Z.div_mod_to_equations; lia. }
  (* G3: the cut's configuration in the run's state form, then the walk at the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A825d4_at [Z.of_nat j])) with 0x825d4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x825d4) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run, and the lift at RNG_W. *)
  unfold Lib.Regs6ss.mkR_of.
  pose proof (A.Prog.Seg.F25Fon.f25_evt_F_on (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                A.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on
                (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
                (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
                (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
                (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
                (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
                (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
                (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
                (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
                (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
                (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
                (lib.Reusable.YK11.getr regs3 31)
                lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
                sp phi fr Aa sfr (A.Prog.SlotModel.t_rp (ACtlCut.c_in cx) j) (sp - 16)
                (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)
                R2 R9 R19 R22 R10 Hphi0 Hphi2 ltac:(lia) Hfr32
                ltac:(unfold A.Contract.GT; lia)
                ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                ltac:(unfold A.AsanRT.LOWMEM_END; lia)
                ltac:(rewrite HFSv; lia)
                ltac:(rewrite HFBv; lia)
                ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                HspA
                ltac:(rewrite HFSv; lia)
                Esh160 Happ160
                ltac:(rewrite HFBv, HFSv; rewrite Esfr in *; unfold Reusable.YG0f.in_app,
                        Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hfrapp;
                      Z.div_mod_to_equations; lia)
                ltac:(rewrite HFSv; rewrite Esfr in *; unfold Reusable.YG0f.in_app,
                        Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Hphiapp;
                      Z.div_mod_to_equations; lia)
                ltac:(rewrite HFBv; left; lia)
                ltac:(left; lia)
                ltac:(destruct Hsepb; [right | left]; lia)
                Hstk ltac:(lia) Wsh W160 Q120
                (A.Prog.Seg.F24.b7_pbs_length (ACtlCut.c_in cx) j)
                (A.Prog.Seg.F24.b7_pbs_bytes mem3 (phi + 18) (ACtlCut.c_in cx) j Hblk)
                HAC HADp HPSH HOUT
                (A.ProgBridge.rng_of_visible _ _ _ VSH)
                (A.ProgBridge.rng_of_visible _ _ _ V160)
                (A.ProgBridge.rng_of_visible _ _ _ VQ)
                (A.ProgBridge.rng_of_visible _ _ _ V4)
                (A.ProgBridge.rng_of_visible _ _ _ V5)
                (A.ProgBridge.rng_of_visible _ _ _ V1)
                (A.ProgBridge.rng_of_visible _ _ _ V2)
                (A.ProgBridge.rng_of_visible _ _ _ V3)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
           _ (POST cx) HFS); [exact (A.ProgBridge.fp_avoids_RNG_W _) |].
  (* G5: the continuation. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & b1 & m' & Ems & MU & WM &
    Hb1 & Hb1s & Hfirst).
  subst ms'.
  cbn [ms_mem] in Hhid.
  set (W := [(sfr + 20, sfr + 21); (fr + 160, fr + 161); (sp - 16, sp)] : list Lib.Frame.ivl).
  set (KEEP := fun p n => Lib.Frame.disjoint_from W p n /\
                 (forall i, 0 <= i < n -> Lib.Frame.outside W (A.AsanRT.shadow_addr (p + i)))).
  assert (KEEPI : forall p n, 0 <= n -> (forall x, p <= x < p + n -> A.AsanRT.app_mem x) ->
                    (p + n <= fr + 160 \/ fr + 168 <= p) -> (p + n <= sp - 16 \/ sp <= p) -> KEEP p n).
  { intros p n Hn Happ Hgr Hwn. exact (f25_keepi fr sp p n ltac:(lia) Hfr8 Happ160 Hhm Hn Happ Hgr Hwn). }
  assert (Happ_hi : forall x, sp - 16 <= x < ACtlCut.c_sp cx -> A.AsanRT.app_mem x).
  { intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia. }
  (* the register map of the end state *)
  set (R1 := Lib.Frame.mkR ra' (lib.Reusable.YK11.getr regs3 2)
               (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) t0' t1' t2'
               (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
               (Z_to_bv 64 (if Prog.RcPorts.pu_decl (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)
                            then 4 * Prog.RcPorts.pu_nunk (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) 12
                            else -1))
               a1' a2' a3' a4' a5' a6' a7'
               (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
               (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
               (lib.Reusable.YK11.getr regs3 24)
               (Z_to_bv 64 (A.Prog.SlotModel.t_rp (ACtlCut.c_in cx) j))
               (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28)
               (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  assert (E2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : lib.Reusable.YK11.getr R1 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (E25 : lib.Reusable.YK11.getr R1 25 = Z_to_bv 64 (A.Prog.SlotModel.t_rp (ACtlCut.c_in cx) j))
    by reflexivity.
  assert (E10 : lib.Reusable.YK11.getr R1 10 = Z_to_bv 64 (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j))
    by reflexivity.
  (* the transporter record *)
  assert (TR : A.ACtlG.F26.b7g_tr KEEP mem3 m' regs3 R1).
  { split.
    { intros p n p' n' (HD & HS) Hp Hn Hpn. split; [exact (A.AsanRTFacts.disjoint_from_sub W p n p' n' HD Hp Hpn) |].
      intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HS. lia. }
    split.
    { intros a bs n (HD & _) Hl Hby. apply (Lib.Frame.bytes_at_transport segs W mem3 m' a bs Hby MU).
      rewrite Hl. exact HD. }
    split.
    { intros p n (_ & HS) Had. exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem3 m' p n MU HS Had). }
    intros off v Ho0 Ho Hs.
    apply (A.ACtlG.F26.b7g_spill_keep W mem3 m' regs3 R1 Aa off v R9 ltac:(lia)
             ltac:(change (2 ^ 64) with 18446744073709551616; lia) Ho0 Ho E9 MU); [| exact Hs].
    unfold W. cbn [Lib.Frame.disjoint_from].
    split; [right; lia |]. split; [right; lia |]. split; [right; lia | exact I]. }
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A825f4_at [Z.of_nat j])) R1 m' md')
            (POST cx)).
  (* the exit cut *)
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
  - (* the journal crosses the frame shadow byte, the frame byte and the callee's stack window *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (sfr + 20 <= a < sfr + 21) \/ (fr + 160 <= a < fr + 161) \/ (sp - 16 <= a < sp)).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity |].
      apply (MU x). unfold W. cbn [Lib.Frame.outside].
      split; [intros Hc; apply Hx; left; exact Hc |].
      split; [intros Hc; apply Hx; right; left; exact Hc |].
      split; [intros Hc; apply Hx; right; right; exact Hc | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx |].
      destruct (A.Prog.Seg.F24.b7_out_dec W (bv_unsigned x)) as [Hout | Hout].
      * rewrite (MU x Hout). exact Hx.
      * destruct (A.Prog.Seg.F24.b7_in_cases W (bv_unsigned x) Hout) as (lo & hi & Hin & Hr).
        apply (A.ACtlG.F26.b7g_grow mem3 m' x); [| exact WM | exact Hx].
        unfold W in Hin. cbn [In] in Hin.
        unfold A.Prog.ImgBounds.IMG_HI in *.
        destruct Hin as [E | [E | [E | []]]]; injection E as <- <-; lia.
    + exact Hhid.
    + exact Hsbm.
    + intros a [Ha | [Ha | Ha]].
      * right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hown6 |].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3, Esfr2.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
      * right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hown6 |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      * left. unfold A.ACfn.LLVMF_STK. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A825f4_at (ACtlCutP.v:2634-2644) *)
    split; [reflexivity |].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825f4_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    assert (Hsavlen : Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104).
    { unfold ACtlCutP.saved_bytes. rewrite !length_app, !Lib.Mem.length_le8. reflexivity. }
    (* FRAC, re-established on the end map and the new memory by WALKING its conjuncts (so a conjunct
       appended to FRAC needs no edit here as long as a leaf case closes it): a register or arithmetic fact
       carries over by conversion (R1 keeps registers 2 3 4 8 9 19 26 of regs3); a q64 word or byte list is
       kept by KEEPI (frame bytes and stack bytes miss W by address and by shadow byte); the 392 frame shadow
       bytes take the written byte (f25_sh_upd). *)
    split.
    { exists Aa, sp.
      let keep u :=
        lazymatch goal with
        | |- KEEP fr _ =>
            apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia]
        | |- KEEP (fr + ?o) ?n =>
            let b := eval vm_compute in (Z.leb (o + n) 160) in
            lazymatch b with
            | true => apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia]
            | false => apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | right; lia | left; lia]
            end
        | |- _ => apply KEEPI; [lia | intros x Hx; apply Happ_hi; lia | right; lia | right; lia]
        end in
      let leaf H :=
        lazymatch goal with
        | |- ACtlCutP.q64 _ _ _ => apply (A.ACtlG.F26.b7g_q64 _ _ _ _ _ TR); [keep () | exact H]
        | |- Lib.Mem.bytes_at _ _ _ _ =>
            eapply (A.ACtlG.F26.b7g_by _ _ _ _ _ TR); [| reflexivity | exact H]; rewrite ?Hsavlen; keep ()
        | |- exists _, _ =>
            (let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hshlen := fresh "Hshlen" in
             let Hshl := fresh "Hshl" in
             destruct H as (sh & Hsh & Hshlen);
             assert (Hshl : length sh = 392%nat) by (rewrite Hshlen; reflexivity);
             exists (Lib.Mem.upd_bytes sh 20 [b1]);
             split;
             [ apply (f25_sh_upd W mem3 m' sfr sh 20 b1 Hsh ltac:(rewrite Hshl; lia) MU);
               [ let i := fresh "i" in let Hi := fresh "Hi" in let Hne := fresh "Hne" in
                 let Hapi := fresh "Hapi" in let Esi := fresh "Esi" in let Hsi := fresh "Hsi" in
                 intros i Hi Hne; unfold W; cbn [Lib.Frame.outside];
                 rewrite Hshl in Hi;
                 assert (Hapi : A.AsanRT.app_mem (fr + 8 * Z.of_nat i)) by (apply Hfrbyte; lia);
                 assert (Esi : sfr + Z.of_nat i = A.AsanRT.shadow_addr (fr + 8 * Z.of_nat i))
                   by (rewrite Esfr; unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia);
                 pose proof (A.AsanRTFacts.shadow_of_app _ Hapi) as Hsi; rewrite <- Esi in Hsi;
                 split; [lia |];
                 split; [intros ?; apply (A.AsanRTFacts.app_not_shadow (sfr + Z.of_nat i)); [| exact Hsi];
                         replace (sfr + Z.of_nat i) with (fr + 160) by lia; exact Happ160 |];
                 split; [| exact I];
                 unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
                   A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *; lia
               | change (sfr + Z.of_nat 20) with (sfr + 20); exact Hb1 ]
             | rewrite Lib.Mem.upd_bytes_length; [exact Hshlen | cbn [length]; rewrite Hshl; lia] ])
        | |- _ => exact H
        end in
      let rec walk H :=
        lazymatch type of H with
        | _ /\ _ => let H1 := fresh "Hc" in let H2 := fresh "Hr" in
                    destruct H as [H1 H2]; split; [leaf H1 | walk H2]
        | _ => leaf H
        end in
      walk HC. }
    (* b7_body *)
    exists phi.
    split; [exact HPerm |]. split; [exact Hn26 |]. split; [exact Hj255 |].
    assert (KF : KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624)).
    { unfold ACtlCutP.FRAME_BYTES.
      apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | right; lia | left; lia]. }
    assert (KI : KEEP (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
    { apply KEEPI; [lia | exact Hinapp | exact Hingr | left; lia]. }
    assert (KB : KEEP phi (ACtlCutP.flen cx j)).
    { apply KEEPI; [lia | exact Hphib | destruct Hsepb; [left | right]; lia | left; lia]. }
    split.
    { apply (A.ACtlG.F26.b7g_HB _ _ _ _ _ phi (ACtlCutP.flen cx j) TR); [| exact HHB].
      unfold A.ACtlK.a_size. replace (Z.max (ACtlCutP.flen cx j) 1) with (ACtlCutP.flen cx j) by lia.
      exact KB. }
    split.
    { apply (A.ACtlG.F26.b7g_FLSI _ _ _ _ _ cx j fr TR KF KI Hinlen'); [| exact HFLSI].
      apply (A.Prog.Seg.F24.b7_stk_keep mem3 m' fr (fr + ACtlCutP.FRAME_BYTES));
        [exact (proj1 (proj2 (proj2 (proj1 HFLSI)))) | exact WM
        | unfold A.Contract.GT; lia
        | change (2 ^ 64) with 18446744073709551616; unfold ACtlCutP.FRAME_BYTES; lia]. }
    split; [exact (A.ACtlG.F26.b7g_B7K _ _ _ _ _ cx j phi fr TR KF KB E18 E21 E22 E23 E24 HB7K) |].
    (* the tail of C_A825f4_at *)
    split; [unfold ACtlCut.rgv; exact E25 |].
    split; [unfold ACtlCut.rgv; exact E10 |].
    split.
    { unfold ACtlCutP.PORTS in *. destruct HPORTS as (Hz & Hnz). split; intros E.
      - destruct (Hz E) as (Q0 & Q4 & Q8).
        split; [apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q0] |].
        split; [apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q4]
               | apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q8]].
      - destruct (Hnz E) as (Q0 & Q4 & Q8).
        split; [apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q0] |].
        split; [apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q4]
               | apply (A.ACtlG.F26.b7g_u32 _ _ _ _ _ TR);
                [apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia] | exact Q8]]. }
    split; [unfold ACtlCutP.FIRSTb; exact Hfirst |].
    split.
    { exact (A.ACtlG.F26.b7g_ad _ _ _ _ _ TR (fr + 128) 12
               ltac:(apply KEEPI; [lia | intros x Hx; apply Hfrbyte; lia | left; lia | left; lia]) HADq). }
    (* addressable (fr + 160) 1: the post's shadow byte 1 at S(fr) + 20 = shadow_addr (fr + 160) *)
    split; [lia |]. split; [lia |]. split; [unfold A.AsanRT.APPMEM_END; lia |].
    intros i Hi. replace (fr + 160 + i) with (fr + 160) by lia.
    split; [exact Happ160 |]. exists b1. split.
    + rewrite Esh160. destruct Hb1 as (_ & _ & Hb1). pose proof (Hb1 0%nat ltac:(cbn [length]; lia)) as Hb10.
      rewrite Z.add_0_r in Hb10. exact Hb10.
    + unfold A.AsanRT.shadow_ok. right. rewrite Hb1s. split; [| lia].
      replace ((fr + 160) mod 8) with 0 by (Z.div_mod_to_equations; lia). lia.
  - (* ctl_rt_C at the same state (ly3, S3) *)
    unfold A.ACtlRtC.ctl_rt_C.
    split.
    { unfold A.ACtlK.asan_cells_at in *.
      apply (A.AsanRTFacts.asan_cells_kept W mem3 m' HAC MU).
      unfold W. cbn [Lib.Frame.disjoint_from]. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI.
      unfold A.Prog.ImgBounds.IMG_HI in Himg.
      split; [left; lia |]. split; [left; lia |]. split; [left; lia | exact I]. }
    (* any shadow region carries over: a byte outside W is unchanged, S(fr) + 20 is present by the post *)
    assert (KEEPSH : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m').
    { intros P HP a HPa Ha. destruct (HP a HPa Ha) as [Hw (b & Hb)]. split; [exact (WM _ Hw) |].
      pose proof (A.AsanRTFacts.in_shadow_range a Ha) as Har.
      destruct (Z.eq_dec a (sfr + 20)) as [Ea | Hne].
      - subst a. exists b1. destruct Hb1 as (_ & _ & Hb1). pose proof (Hb1 0%nat ltac:(cbn [length]; lia)) as Hb10.
        rewrite Z.add_0_r in Hb10. exact Hb10.
      - exists b. unfold Lib.Mem.mrd in *. rewrite (MU (Lib.Mem.wa a)); [exact Hb |].
        rewrite Lib.Mem.wa_unsigned by lia. unfold W. cbn [Lib.Frame.outside].
        split; [lia |].
        split; [intros Hc; apply (A.AsanRTFacts.app_not_shadow a); [replace a with (fr + 160) by lia; exact Happ160
                                                                   | exact Ha] |].
        split; [| exact I].
        unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
          A.AsanRT.HIGHMEM_BEG in *. lia. }
    split; [exact (KEEPSH _ Hcut) |].
    split; [exact (KEEPSH _ Himgsh) |].
    apply (A.ACtlG.F26.b7g_ro W mem3 m' HRO MU).
    intros lo hi Hin. unfold W in Hin. cbn [In] in Hin. unfold A.Prog.ImgBounds.IMG_HI in *.
    destruct Hin as [E | [E | [E | []]]]; injection E as <- <-; lia.
Qed.

End GlueF25.

Print Assumptions glue_seg_F25.
