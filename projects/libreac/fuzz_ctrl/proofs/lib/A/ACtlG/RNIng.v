(* lib/A/ACtlG/RNIng.v -- the SHARED part of the glue of stages seg_R11 and seg_R12 of fuzz_ctrl image A's walk of
   LLVMFuzzerTestOneInput (lib/A/ACtl.v (at head lib/A/ACtl.v:686 / :688) (an earlier version, blob c4edf0be7fe, not in this delivery)).  Written by a Theorem Labs lane (tree
   (internal path)).  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_rn_ing : the walk from the entry cut of R11 (pc 0x816c4) or R12 (pc 0x81708), given the cut's facts and the
                   four turn-b facts the caller supplies, reaches ACtl.v's exit cut ix_cut C_A81734_at [Z.of_nat b].
   R11 and R12 differ only in their first two instructions (`li a1,1 ; beq a0,a1,81714`, the pre-run, a parameter
   pc0 + its _F run of the shape rn_pre_run) and in where the ingest payload lies (the heap block phi for R11, the
   fragment record inside the frame for R12, the disjunction of the caller's placement premise).  Both then run the
   shared ingest tail 0x81714 .. 0x81730 and the call of reac_identity_ingest, Seg/RNIng.v rn_ing_evt (:248), as its
   route (C) footprint twin Seg/RNIngFon.v rn_ing_evt_F_on (this lane's beside-file of a Theorem Labs lane's Seg/RNIngF.v (not in this delivery),
   whose rn_ing_evt_F stays byte-identical; its rn_ing_evt_of_F_bounded later changed only in module qualification).  Mirrors Seg/RNIng.v rn_ing_cont (:414), which plays the same role on ctrl's frame
   route.

   ROUTE (C) (a working branch 1502cba0417; recipe L3-recipe.md (a working note, not in this delivery)):
   rn_ing_evt_F_on takes the callee's NARROWED footprint contract reac_identity_ingest_contract_F_on (premise
   shadow_rw DROPPED; LANDED.md rows 24 / 54 (a working note, not in this delivery)) AS A PREMISE and its run spans the call, so this file SUPPLIES that
   premise with the proved A.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on and lifts the WHOLE run
   (pre-run + tail + call) ONCE with Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  No split
   at the call, no lift (reac_identity_ingest_SRr_at is NOT cited: the _F_on carries the contract as its own
   premise, so the caller obligations are the contract's premises, which rn_ing_evt_F_on's premises restate), and
   no _hid placeholder: SRr_fevt_hid's continuation carries ajournal_exec's hidden-bytes premise itself.  The run
   reads no shadow byte through a shadow_rw premise, so the cut's ctl_rt_C feeds it without any shadow region.

   THE PROOF (glue-pattern.md G3-G5; G1 is in R11.v / R12.v)
   G2  every premise of rn_ing_evt_F_on from the cut: sp, s1 = A and s5 = fr + 2176 from FRAC and the body; the three
       spill reads [A + 88] / [A + 80] / [A + 72] from RXS (through register 9); the three argument cells from the
       caller; the identity record from IDBr plus the presence of the frame bytes (AR_frames_law); the callee window
       stk from the journal's presence conjunct over [c_sp - LLVMF_STK, c_sp) (YCbq.v:368).  BOUNDS (auditor
       a Theorem Labs lane, glue-pattern.md section 5 (a working note, not in this delivery)): every bound rn_ing_evt_F_on states (none for A + 88, A + 80,
       A + 72, pa, pp, pn, whose premises are reads and rng only; it bounds spv, lo, id, ad, p and len), and every other one, is proved here from VISIBLE state: FRAC (fr + FRAME_BYTES <= A,
       A + 416 <= c_sp, c_sp - 4096 < sp <= A, c_sp < APPMEM_END), frames_bounds (4096 <= fr,
       fr + 4096 <= alloc_ceiling) with the frame law and layout_le's ly_F, astk_ok (alloc_ceiling <= ly_stk_lo,
       ly_stk_lo + LLVMF_STK <= c_sp), the AR block law for phi, alloc_ceiling's range.  Footprint (rng) premises
       from range_visible facts: the window by ProgWorldVisWin.win_vis, frame bytes and their shadow by
       ProgWorldVisFrame.frame_vis, heap bytes and shadow by ProgWorldVisHeap.heap_vis / heap_sh_vis, GOT_CELL_K
       and CELL_K by ProgBridge.img_vis_W.
   G3  cfg_at_MS, then Reusable.YA0nR.SRr_xregs_eqv from regs3 to Regs6ss.mkR_of regs3.
   G4  the pre-run then rn_ing_evt_F_on, composed by ExecF.evtF_cut, lifted once by SRr_fevt_hid.
   G5  the exit cut at the end map R' (the ingest's post state) and the post memory m': the journal by
       YCbq.ajournal_exec with Wr := [sp - 32, sp) U [fr + 2176, fr + 2214) (awr_byte: the stack window and the
       owned class-6 frame); frames / frame law / k unchanged; the body through the post's munch (bytes kept outside
       the write set), wmono and the kept shadow (AsanRTFacts.munch_meta); ctl_rt_C at the SAME ly3 S3 (the stage
       changes neither): asan_cells by asan_cells_kept, its two shadow_rw_on conjuncts (cut_shadow ly3 S3 and
       img_shadow) by ShadowRwOnT.shadow_rw_on_kept from the entry's ctl_rt_C with meta_kept and wmono, and the
       read-only bytes (all in the image, below 0x5fe000, so outside both written ranges).

   SECTION HYPOTHESES
   - LAWS : the core's AR laws (YCbq Section a0's hypothesis), as A5.v and ACtl.v:237.
   - none other: the kit's helpers are cited by name from lib/A/ACtlG/Kit.v (A.ACtlG.Kit.kit_wx for
     SRr_fevt_hid, A.ACtlG.Kit.kit_segs_low for ajournal_exec and the stack window's not-image bytes).  (On the
     glue base eb89fed7fac, where Kit.v did not compile, they were placeholders with the kit's text: commits
     aa8ed9670fb / 18025d163cd.)

   CLOSURE: every project Require below is qualified; no statement names a frame-route identifier (the Seg/*
   lemmas cited are proof-internal, closed by Qed).  SHADOWED NAMES: getr / seg_rom / FPState / RunCeil are written
   lib.Reusable.YK11.* / lib.Reusable.YM05.* (the core's copies): the Seg/* closure loads the ASan-side
   lib/A/Reusable copies, to which the short names Reusable.YK11 / Reusable.YM05 then resolve.

   BUILD STATE: on a working branch 1502cba0417 (no port_core_refused name in lib/A or lib/Reusable); the Require closure
   reaches no stand-in.  No Axiom, no Parameter, no unproved step. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every project module by its full path (ctrlgate rule (b): a partial `From .. Require` of a twin-family member is
   forbidden; YK11 / YM05 / YO09 / YI16 / YK1j and the lib/Lib modules have image-side twins). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1j OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2y OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingest_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingestF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.RNIng OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.RNIngFon.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Image facts (no Section argument). *)

(* The ASan runtime's data range [RT_LO, RT_HI) = [0x9fad0, 0xa9578) lies in the image's third and fourth
   segments (ProgBridge.rsegs_spans), so each of its bytes is an image byte. *)
Lemma rn_rt_img : forall x, A.AsanRT.RT_LO <= x < A.AsanRT.RT_HI -> Reusable.YG0d.in_img segs x.
Proof.
  intros x Hx. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI in Hx.
  assert (Hin : forall b sz,
    In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) ->
    b <= x < b + sz -> Reusable.YG0d.in_img segs x).
  { intros b sz Hbs Hr. apply in_map_iff in Hbs as (s & Es & Hs). injection Es as <- <-.
    exists s. split; [exact Hs | exact Hr]. }
  rewrite A.ProgBridge.rsegs_spans in Hin.
  destruct (Z_lt_le_dec x 0xa1000) as [H1 | H1].
  - apply (Hin 0x9e000 0x3000); [right; right; left; reflexivity | lia].
  - apply (Hin 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

(* A read-only address lies in a segment, so it is an image byte. *)
Lemma rn_ro_img : forall a : word, lib.Lib.Mem.ro_addr A.Img0.rsegs a = true ->
  Reusable.YG0d.in_img segs (bv_unsigned a).
Proof.
  intros a H. unfold lib.Lib.Mem.ro_addr in H.
  destruct (find_segment A.Img0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  exists s. split.
  - exact (lib.Reusable.YK1j.find_segment_in _ _ _ _ E).
  - pose proof (lib.Reusable.YK1j.find_segment_range _ _ _ _ E) as R. lia.
Qed.

(* A byte that is no image byte has no rom byte (the core's A.AE2y.seg_rom_none, AE2y.v:684, read through `change`:
   its seg_rom over tfibsegs is lib/Lib's over rsegs, the same body over the same image module's loaded_segments),
   so a present read of it is a byte of the memory itself.  The Section only supplies AE2y's Section f contexts in
   case its lemma depends on them; End drops what it does not use. *)
Section RnRom.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Lemma rn_present_of_mrd : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 ->
  ~ Reusable.YG0d.in_img segs a ->
  lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b -> m (lib.Lib.Mem.wa a) <> None.
Proof.
  intros m a b Ha Hn H Hm. unfold lib.Lib.Mem.mrd in H. rewrite Hm in H.
  pose proof (A.AE2y.seg_rom_none a Ha Hn) as E0.
  change (lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a) = None) in E0.
  rewrite E0 in H. discriminate H.
Qed.
End RnRom.

(* The byte-exact shadow span of n > 0 bytes at lo lies in their 8-aligned shadow word cover. *)
Lemma rn_sh_sub : forall H lo len, 0 <= lo -> 0 < len ->
  A.ProgBridge.range_visible H (A.Prog.rng_asan.sh_al8_lo lo)
    (A.Prog.rng_asan.sh_al8_hi lo len - A.Prog.rng_asan.sh_al8_lo lo) ->
  A.ProgBridge.range_visible H (lo / 8 + A.AsanRT.ASAN_K) ((lo + len - 1) / 8 - lo / 8 + 1).
Proof.
  intros H lo len H0 Hl V.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr in V.
  pose proof (Z.div_le_mono lo (lo + len - 1) 8 ltac:(lia) ltac:(lia)) as Dm.
  pose proof (Z.div_mod (lo / 8 + A.AsanRT.ASAN_K) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (lo / 8 + A.AsanRT.ASAN_K) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod ((lo + len - 1) / 8 + A.AsanRT.ASAN_K) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound ((lo + len - 1) / 8 + A.AsanRT.ASAN_K) 8 ltac:(lia)) as M2.
  eapply A.ProgBridge.range_visible_sub; [exact V | lia | lia | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The pre-run's shape: the _F runs of R11 (R11F.r11_evt_F, pc0 = 0x816c4) and R12 (R12F.r12_evt_F,
   pc0 = 0x81708), `li a1,1 ; beq a0,a1,81714` with a0 = 1, only a1 changed.  Their statements, with the start pc a
   parameter (the core's seg_rom in the place of the ASan-side copy, the same body). *)
Definition rn_pre_run (pc0 : Z) : Prop :=
  forall (RNG : lib.Lib.ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 1 ->
    lib.Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists a1' : word,
         ms' = lib.Lib.MState.MS
                 (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                    s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x81714) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs))
      (lib.Lib.MState.MS
         (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
            t4 t5 t6)
         F (Z_to_bv 64 pc0) fc None m (lib.Reusable.YK11.seg_rom A.Img0.rsegs)).

(* The conjunct of the entry bodies C_A816c4_at / C_A81708_at (ACtlCutP.v:1406-1414 / :1428-1436) shared by both
   and by the exit body C_A81734_at (:1450-1458, there unparenthesized), at the index b. *)
Definition rn_common (cx : A.ACtlCut.ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  A.ACtlCut.c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ A.ACtlCutP.HB m phi (A.ACtlCutP.rnb cx b) /\
  A.ACtlCut.rgv regs 23 (Z.of_nat b) /\ A.ACtlCutP.OURb cx fr m /\ A.ACtlCutP.OUTA fr m /\
  A.ACtlCutP.CUR cx 7 regs /\
  A.ACtlCutP.spill regs m 112 (A.Prog.SlotModel.mrow (A.ACtlCut.c_in cx)) /\
  A.ACtlCutP.spill regs m 128 (fr + 544) /\ A.ACtlCutP.PRO cx fr regs m /\
  A.ACtlCutP.spill regs m 104 0x21140 /\ A.ACtlCutP.spill regs m 96 0x1234 /\
  A.ACtlCutP.spill regs m 64 0xe38f0000 /\
  A.ACtlCutP.spill regs m 144 (fr + 2688) /\ A.ACtlCutP.spill regs m 192 (fr + 2768) /\
  (exists idb, lib.Lib.Step.rw_cells segs m (fr + 2688) [lib.Lib.Cells.CB 38 idb]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 2768) [lib.Lib.Cells.CB 72 junk]) /\
  A.ACtlCutP.spill regs m 280 (fr + 3040) /\ A.ACtlCutP.spill regs m 240 (fr + 3056) /\
  (exists jy, lib.Lib.Step.rw_cells segs m (fr + 3040) [lib.Lib.Cells.CB 1 jy]) /\
  (exists junk, lib.Lib.Step.rw_cells segs m (fr + 3056) [lib.Lib.Cells.CB 32 junk]) /\
  A.ACtlCutP.spill regs m 152 (A.ACtlCutP.Sfr fr + 68) /\ A.ACtlCut.rgv regs 21 (fr + 2176) /\
  A.AsanRT.addressable m (fr + 2176) 38.

(* A spill word read at the FRAC base A (the ACtlCutP twin of Seg/RNIng.v rn_spill_ov's first half: spill there is
   SlotInv's). *)
Lemma rn_spill_q : forall (regs : bvmap 5 word) m off v Ab,
  A.ACtlCutP.spill regs m off v -> lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 Ab ->
  0 <= Ab -> Ab + off + 8 <= 2 ^ 64 -> 0 <= off ->
  A.ACtlCutP.q64 m (Ab + off) v.
Proof.
  intros regs m off v Ab (A1 & HA1 & Hq) Hr9 HA0 HAb Hoff.
  unfold A.ACtlCut.rgv in HA1.
  assert (Hc : Z_to_bv 64 Ab = Z_to_bv 64 A1) by (rewrite <- Hr9; exact HA1).
  unfold A.ACtlCutP.q64 in *.
  eapply A.Prog.Seg.RNIng.rn_bytes_cong;
    [apply A.Prog.Seg.RNIng.rn_bv_mod; exact Hc | lia | rewrite lib.Lib.Mem.length_le8; lia | exact Hq].
Qed.

(* A spill kept across a register-map change that keeps register 9 and a memory change that keeps its 8 bytes. *)
Lemma rn_spill_keep : forall (regs regs' : bvmap 5 word) m m' off v Ab W,
  A.ACtlCutP.spill regs m off v -> lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 Ab ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  0 <= Ab -> Ab + off + 8 <= 2 ^ 64 -> 0 <= off ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.disjoint_from W (Ab + off) 8 ->
  A.ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' off v Ab W Hs Hr9 E9 HA0 HAb Hoff MU Hd.
  exists Ab. split; [unfold A.ACtlCut.rgv; rewrite E9; exact Hr9|].
  pose proof (rn_spill_q regs m off v Ab Hs Hr9 HA0 HAb Hoff) as Hq. unfold A.ACtlCutP.q64 in *.
  apply (lib.Lib.Frame.bytes_at_transport segs W m m' (Ab + off) _ Hq MU).
  rewrite lib.Lib.Mem.length_le8. exact Hd.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage part shared by R11 and R12. *)
Section GlueRNIng.

(* ACtl.v's Section shape (ACtl.v:210-214), restricted to what this part uses; the contexts are the core's. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :400), verbatim. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81734_at := (A.ACtlCutP.C_A81734_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:237). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The kit's helpers (A.ACtlG.Kit.kit_wx, kit_segs_low) are cited by name below. *)

Lemma glue_rn_ing : forall (pc0 : Z), rn_pre_run pc0 ->
  forall POST (b : nat) (cx : A.ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (regs3 : bvmap 5 word)
         (mem3 : word -> option byte) md3 (phi ad p len : Z) (pb : list byte),
  CF POST (ix_cut C_A81734_at [Z.of_nat b]) ->
  A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
    (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
    (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (A.ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) cid pos) ->
  k <= 2 * Z.of_nat (A.ACtlCutP.ixn 0 [Z.of_nat b]) + 1 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) ++ [(phi, A.ACtlCutP.rnb cx b)]) ->
  A.ACtlCutP.FRAC B cx fr fr regs3 mem3 ->
  rn_common cx b phi fr regs3 mem3 ->
  A.ACtlCut.a0v regs3 1 ->
  A.ACtlCutP.RXS cx fr regs3 mem3 ->
  A.ACtlCut.rgv regs3 24 phi ->
  A.ACtlCutP.IDBr cx fr (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) mem3 ->
  A.ACtlCutP.FGBr cx fr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) (S b)) mem3 ->
  lib.Lib.Mem.bytes_at segs mem3 (fr + 2448) (lib.Lib.Mem.le2 (Z_to_bv 64 ad)) ->
  lib.Lib.Mem.bytes_at segs mem3 (fr + 2464) (lib.Lib.Mem.le8 (Z_to_bv 64 p)) ->
  lib.Lib.Mem.bytes_at segs mem3 (fr + 2496) (lib.Lib.Mem.le8 (Z_to_bv 64 len)) ->
  0 <= ad < 65536 -> 0 < len -> length pb = Z.to_nat len ->
  lib.Lib.Mem.bytes_at segs mem3 p pb -> A.AsanRT.addressable mem3 p len ->
  ((phi <= p /\ p + len <= phi + A.ACtlCutP.rnb cx b) \/
   (fr + 2214 <= p /\ p + len <= fr + A.ACtlCutP.FRAME_BYTES)) ->
  fst (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) ad pb) = 1 ->
  snd (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) ad pb) =
    A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) (S b) ->
  A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs pc0 regs3 mem3 md3) (POST cx).
Proof.
  intros pc0 PRE POST b cx fr k ly3 S3 W3 regs3 mem3 md3 phi ad p len pb
    HX HB HJ HF HL Hk HPerm HFRAC HCOM Ha0 HRXS Hr24 HIDB HFGB HBa HBp HBn Had Hlen0 Hpblen HPB HAp Hploc
    HING1 HINGs Hrt.
  unfold rn_pre_run in PRE.
  (* ---- G2: names ---- *)
  pose proof HFRAC as (Ab & sp & Hr2 & Hspm & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & HAm & HAS &
    HspA & HfrA & HA416 & HS4 & HSapp & Q304 & Q24 & Q16 & Qhdr & Qent & Hsh & Hsaved & Qtrl).
  pose proof HCOM as (Hcn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & Hs112 & Hs128 & HPRO & Hs104 & Hs96 &
    Hs64 & Hs144 & Hs192 & HRWid & HRWjk & Hs280 & Hs240 & HRWjy & HRWj32 & Hs152 & Hr21 & HAD38).
  pose proof HRXS as (Hs48 & Hs56 & Hs88 & Hs80 & Hs72 & Hs8 & Hs0 & Hs200 & Hs216 & HAD72).
  pose proof Hrt as (HAC & HSWc & HSWi & HRO).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hsp0 & _ & _ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as [[Hc0 Hc1] _].
  unfold A.ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END, A.ACfn.LLVMF_STK in *.
  (* the frame: fr = frame_addr ly3 6 (c_fpos cx), 4096 <= fr, fr + 4096 <= alloc_ceiling, in_app *)
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (A.ACtlCut.c_fpos cx) (or_introl eq_refl)). unfold Reusable.YG0f.frame_addr.
    rewrite EF. reflexivity. }
  assert (Hfs6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite <- Efr in Hf4096, Hfceil, Hfapp. rewrite Hfs6 in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfapp.
  assert (Hfrimg : forall a, fr <= a < fr + 4096 -> ~ Reusable.YG0d.in_img segs a).
  { intros a Ha. apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) a HAR Hin6).
    rewrite <- Efr, Hfs6. exact Ha. }
  assert (Hfrpres : forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha.
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin6)
      as (_ & _ & Hby & _).
    rewrite <- Efr, Hfs6 in Hby. exact (proj1 (Hby a Ha)). }
  (* the heap block phi *)
  assert (Hphi_in : In (phi, A.ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hphi_in)
    as (_ & Hphi4096 & Hphiceil & _ & _ & _ & Hrnbr).
  pose proof (Reusable.YCbq.req_size_pos (A.ACtlCutP.rnb cx b) ltac:(lia)) as Hreq.
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (A.ACtlCut.c_fpos cx)
                HAR Hphi_in Hin6) as Hsepbf.
  rewrite <- Efr, Hfs6 in Hsepbf. unfold Reusable.YG0f.zdisjoint in Hsepbf. cbn [fst snd] in Hsepbf.
  (* the numeric picture *)
  assert (HA0 : 0 <= Ab) by lia.
  assert (Hsp_hi : 0x10007fff8000 <= sp - 32) by lia.
  assert (Hfr_sp : fr + 4096 <= sp - 32) by lia.
  assert (Hspv : 0 <= sp < 2 ^ 64) by lia.
  assert (HAD38app := A.AsanRTFacts.addressable_app mem3 (fr + 2176) 38 HAD38).
  (* the payload: placement, positivity, visibility *)
  assert (HAp0 := HAp). destruct HAp0 as (Hp0 & _ & Hpe & _). unfold A.AsanRT.APPMEM_END in Hpe.
  assert (Hppos : 0 < p) by (destruct Hploc as [[H1 H2] | [H1 H2]]; lia).
  assert (Hpid : p + len <= fr + 2176 \/ fr + 2176 + 38 <= p).
  { destruct Hploc as [[H1 H2] | [H1 H2]]; [destruct Hsepbf as [Hc | Hc]; [left | right] | right]; lia. }
  assert (Hpsp : p + len <= sp - 32) by (destruct Hploc as [[H1 H2] | [H1 H2]]; lia).
  assert (Vfr : forall lo n, fr <= lo -> lo + n <= fr + 4096 ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo n).
  { intros lo n H1 H2.
    refine (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) lo n HAR Hin6
                     _ _)); rewrite <- Efr; [exact H1 | rewrite Hfs6; exact H2]. }
  assert (Vfrsh : forall lo n, 0 < n -> fr <= 64 * (lo / 64) -> 64 * ((lo + n - 1) / 64) + 64 <= fr + 4096 ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
              (lo / 8 + A.AsanRT.ASAN_K) ((lo + n - 1) / 8 - lo / 8 + 1)).
  { intros lo n H0 H1 H2.
    pose proof (Z.div_mod lo 64 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound lo 64 ltac:(lia)) as M1.
    pose proof (Z.div_mod (lo + n - 1) 64 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (lo + n - 1) 64 ltac:(lia)) as M2.
    apply rn_sh_sub; [lia | exact H0 |].
    destruct (proj2 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) lo n HAR Hin6
                       ltac:(rewrite <- Efr; lia) ltac:(rewrite <- Efr, Hfs6; lia))
                ltac:(lia) ltac:(rewrite <- Efr; lia) ltac:(rewrite <- Efr, Hfs6; lia)) as [E0 | V];
      [lia | exact V]. }
  assert (Vwin : forall lo n, A.ACtlCut.c_sp cx - 32768 <= lo -> lo + n <= A.ACtlCut.c_sp cx ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo n).
  { intros lo n H1 H2. exact (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n HJ H1 H2). }
  assert (Vimg : forall lo n, 0x10000 <= lo -> 0 <= n -> lo + n <= 0x5fe000 ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo n).
  { intros lo n H1 H2 H3.
    apply (A.ProgBridge.range_visible_sub _ A.Prog.ImgBounds.IMG_LO
             (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO) lo n (A.ProgBridge.img_vis_W W3));
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  assert (Vp : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) p len).
  { destruct Hploc as [[H1 H2] | [H1 H2]].
    - exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi _ p len HAR Hphi_in H1 ltac:(lia)).
    - apply Vfr; lia. }
  assert (Vps : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                  (p / 8 + A.AsanRT.ASAN_K) ((p + len - 1) / 8 - p / 8 + 1)).
  { destruct Hploc as [[H1 H2] | [H1 H2]].
    - destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi _ p len HAR Hphi_in H1 ltac:(lia)
                  ltac:(lia)) as [E0 | V]; [lia|].
      exact (rn_sh_sub _ p len ltac:(lia) Hlen0 V).
    - pose proof (Z.div_mod p 64 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 64 ltac:(lia)) as M1.
      pose proof (Z.div_mod (p + len - 1) 64 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (p + len - 1) 64 ltac:(lia)) as M2.
      apply Vfrsh; lia. }
  (* the identity record as a writable cell *)
  pose proof (A.Prog.Seg.RNIng.rn_RS_len (A.ACtlCut.c_in cx) b) as (LID & _).
  assert (HRWidr : lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (fr + 2176)
                     [lib.Lib.Cells.CB 38 (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b)]).
  { split; [split|].
    - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [exact LID | exact I].
    - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact HIDB.
    - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. split; [lia|]. split; [lia|].
      intros i Hi. destruct (Hfrpres (fr + 2176 + i) ltac:(lia)) as (_ & bb & Hbb).
      unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate. }
  (* the three spill reads and the three argument cells, as ov reads *)
  assert (R88 : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (Ab + 88)) 8 =
                Some (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 2448)))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (Ab + 88) _ (rn_spill_q regs3 mem3 88 _ Ab Hs88 Hr9 HA0 ltac:(lia)
                                                             ltac:(lia))) as E.
    rewrite lib.Lib.Mem.length_le8 in E. exact E. }
  assert (R80 : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (Ab + 80)) 8 =
                Some (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 2464)))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (Ab + 80) _ (rn_spill_q regs3 mem3 80 _ Ab Hs80 Hr9 HA0 ltac:(lia)
                                                             ltac:(lia))) as E.
    rewrite lib.Lib.Mem.length_le8 in E. exact E. }
  assert (R72 : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (Ab + 72)) 8 =
                Some (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 2496)))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (Ab + 72) _ (rn_spill_q regs3 mem3 72 _ Ab Hs72 Hr9 HA0 ltac:(lia)
                                                             ltac:(lia))) as E.
    rewrite lib.Lib.Mem.length_le8 in E. exact E. }
  assert (RPA : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (fr + 2448)) 2 =
                Some (lib.Lib.Mem.le2 (Z_to_bv 64 ad))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (fr + 2448) _ HBa) as E. rewrite lib.Lib.Mem.length_le2 in E.
    exact E. }
  assert (RPP : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (fr + 2464)) 8 =
                Some (lib.Lib.Mem.le8 (Z_to_bv 64 p))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (fr + 2464) _ HBp) as E. rewrite lib.Lib.Mem.length_le8 in E.
    exact E. }
  assert (RPN : ov_read_bytes A.Img0.rsegs mem3 (lib.Lib.Mem.wa (fr + 2496)) 8 =
                Some (lib.Lib.Mem.le8 (Z_to_bv 64 len))).
  { pose proof (A.Prog.Seg.RNIng.rn_ovr mem3 (fr + 2496) _ HBn) as E. rewrite lib.Lib.Mem.length_le8 in E.
    exact E. }
  (* the callee window [c_sp - LLVMF_STK, sp) *)
  assert (STK3 : lib.Lib.Frame.stk A.Img0.rsegs mem3 (A.ACtlCut.c_sp cx - 32768) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as (_ & bb & Hbb).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hbb; discriminate|].
    exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  (* the callee's outside premise *)
  assert (HOut : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                           A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
            lib.Lib.Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x).
  { intros x Hx. cbn [lib.Lib.Frame.outside]. split; [|split; [|exact I]]; intro Hin.
    - destruct Hx as [HG | [HC | HSh]].
      + unfold A.AsanRT.GOT_CELL_K in HG. lia.
      + unfold A.AsanRT.CELL_K in HC. lia.
      + unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
          A.AsanRT.HIGHMEM_BEG in HSh. lia.
    - destruct Hx as [HG | [HC | HSh]].
      + apply (Hfrimg x ltac:(lia)). apply rn_rt_img.
        unfold A.AsanRT.GOT_CELL_K in HG. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. lia.
      + apply (Hfrimg x ltac:(lia)). apply rn_rt_img.
        unfold A.AsanRT.CELL_K in HC. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. lia.
      + exact (A.AsanRTFacts.app_not_shadow x (HAD38app x Hin) HSh). }
  (* the identity record's shadow span is visible *)
  assert (Vids : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                   ((fr + 2176) / 8 + A.AsanRT.ASAN_K) ((fr + 2176 + 37) / 8 - (fr + 2176) / 8 + 1)).
  { pose proof (Z.div_mod (fr + 2176) 64 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (fr + 2176) 64 ltac:(lia)) as M1.
    pose proof (Z.div_mod (fr + 2176 + 38 - 1) 64 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (fr + 2176 + 38 - 1) 64 ltac:(lia)) as M2.
    replace (fr + 2176 + 37) with (fr + 2176 + 38 - 1) by lia.
    apply Vfrsh; lia. }
  (* ---- G3: the cut's configuration, moved to the canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 pc0) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* ---- G4: the pre-run and the ingest run, composed and lifted once ---- *)
  refine (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
            _ (A.ProgBridge.fp_avoids_RNG_W _) _).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply lib.Lib.ExecF.evtF_cut.
    { apply PRE. exact Ha0. }
    intros ms1 (a1' & ->).
    eapply (A.Prog.Seg.RNIngFon.rn_ing_evt_F_on A.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on)
      with (spv := sp) (A := Ab) (id := fr + 2176) (pa := fr + 2448) (pp := fr + 2464) (pn := fr + 2496)
           (ad := ad) (p := p) (len := len) (lo := A.ACtlCut.c_sp cx - 32768)
           (idb := A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) (pb := pb).
    - exact Hr2.
    - exact Hr9.
    - exact Hr21.
    - exact Hspv.
    - exact Hspm.
    - lia.
    - pose proof (Z.div_mod fr 32 ltac:(lia)) as D. pose proof (Z.div_mod (fr + 2176) 2 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (fr + 2176) 2 ltac:(lia)) as M2. lia.
    - exact Had.
    - lia.
    - lia.
    - exact R88.
    - exact R80.
    - exact R72.
    - exact RPA.
    - exact RPP.
    - exact RPN.
    - exact HRWidr.
    - exact Hpblen.
    - exact HPB.
    - exact Hpid.
    - exact STK3.
    - lia.
    - left. lia.
    - left. exact Hpsp.
    - exact HAC.
    - exact HAD38.
    - exact HAp.
    - exact HOut.
    - apply A.ProgBridge.rng_of_visible. apply Vwin; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vwin; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vwin; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vfr; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vfr; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vfr; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vwin; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vimg; unfold A.AsanRT.GOT_CELL_K; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vimg; unfold A.AsanRT.CELL_K; lia.
    - apply A.ProgBridge.rng_of_visible. apply Vfr; lia.
    - apply A.ProgBridge.rng_of_visible. exact Vids.
    - apply A.ProgBridge.rng_of_visible. exact Vp.
    - apply A.ProgBridge.rng_of_visible. exact Vps. }
  (* ---- G5: the continuation, at the ingest's post state ---- *)
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Ems & MU & WM & STK' & HIc).
  subst ms'.
  assert (Hhid' : forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) by exact Hhid.
  clear Hhid.
  lazymatch goal with
  | |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R' := R)
  end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A81734_at [Z.of_nat b])) R' m' md') (POST cx)).
  (* the end map R' keeps sp gp tp s0 s1 s2 .. s11 *)
  assert (E2 : lib.Reusable.YK11.getr R' 2 = lib.Reusable.YK11.getr regs3 2) by (unfold R'; reflexivity).
  assert (E8 : lib.Reusable.YK11.getr R' 8 = lib.Reusable.YK11.getr regs3 8) by (unfold R'; reflexivity).
  assert (E9 : lib.Reusable.YK11.getr R' 9 = lib.Reusable.YK11.getr regs3 9) by (unfold R'; reflexivity).
  assert (E19 : lib.Reusable.YK11.getr R' 19 = lib.Reusable.YK11.getr regs3 19) by (unfold R'; reflexivity).
  assert (E21 : lib.Reusable.YK11.getr R' 21 = lib.Reusable.YK11.getr regs3 21) by (unfold R'; reflexivity).
  assert (E22 : lib.Reusable.YK11.getr R' 22 = lib.Reusable.YK11.getr regs3 22) by (unfold R'; reflexivity).
  assert (E23 : lib.Reusable.YK11.getr R' 23 = lib.Reusable.YK11.getr regs3 23) by (unfold R'; reflexivity).
  assert (E24 : lib.Reusable.YK11.getr R' 24 = lib.Reusable.YK11.getr regs3 24) by (unfold R'; reflexivity).
  assert (E25 : lib.Reusable.YK11.getr R' 25 = lib.Reusable.YK11.getr regs3 25) by (unfold R'; reflexivity).
  assert (E26 : lib.Reusable.YK11.getr R' 26 = lib.Reusable.YK11.getr regs3 26) by (unfold R'; reflexivity).
  assert (E3 : lib.Reusable.YK11.getr R' 3 = lib.Reusable.YK11.getr regs3 3) by (unfold R'; reflexivity).
  assert (E4 : lib.Reusable.YK11.getr R' 4 = lib.Reusable.YK11.getr regs3 4) by (unfold R'; reflexivity).
  assert (E2a : lib.A.Reusable.YK11.getr R' 2 = lib.A.Reusable.YK11.getr regs3 2) by (unfold R'; reflexivity).
  assert (E3a : lib.A.Reusable.YK11.getr R' 3 = lib.A.Reusable.YK11.getr regs3 3) by (unfold R'; reflexivity).
  assert (E4a : lib.A.Reusable.YK11.getr R' 4 = lib.A.Reusable.YK11.getr regs3 4) by (unfold R'; reflexivity).
  assert (E10 : lib.Reusable.YK11.getr R' 10 = Z_to_bv 64 1).
  { transitivity (Z_to_bv 64 (fst (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) ad pb)));
      [unfold R'; reflexivity | rewrite HING1; reflexivity]. }
  (* the write set and what it leaves alone *)
  set (Wl := [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)]) in MU.
  assert (Hdj : forall a n, (a + n <= sp - 32 \/ sp <= a) -> (a + n <= fr + 2176 \/ fr + 2176 + 38 <= a) ->
            lib.Lib.Frame.disjoint_from Wl a n).
  { intros a n H1 H2. unfold Wl. cbn [lib.Lib.Frame.disjoint_from]. split; [exact H1 | split; [exact H2 | exact I]]. }
  assert (HWapp : A.AsanRTFacts.all_app Wl).
  { unfold Wl. cbn [A.AsanRTFacts.all_app]. split; [|split; [exact HAD38app | exact I]].
    intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. right. lia. }
  pose proof (A.AsanRTFacts.munch_meta Wl mem3 m' MU HWapp) as MK.
  assert (KSP : forall off v, 0 <= off <= 304 -> A.ACtlCutP.spill regs3 mem3 off v ->
                  A.ACtlCutP.spill R' m' off v).
  { intros off v Hoff Hs.
    apply (rn_spill_keep regs3 R' mem3 m' off v Ab Wl Hs Hr9 E9 HA0 ltac:(lia) ltac:(lia) MU).
    apply Hdj; right; lia. }
  assert (KRW : forall a n bs, fr + 2214 <= a -> a + Z.of_nat n <= fr + 3136 ->
                  lib.Lib.Step.rw_cells segs mem3 a [lib.Lib.Cells.CB n bs] ->
                  lib.Lib.Step.rw_cells segs m' a [lib.Lib.Cells.CB n bs]).
  { intros a n bs H1 H2 H. apply (lib.Lib.Frame.rw_cells_transport segs Wl mem3 m' a _ H MU WM).
    cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. apply Hdj; lia. }
  assert (KA : forall q n, A.AsanRT.addressable mem3 q n -> A.AsanRT.addressable m' q n).
  { intros q n H. exact (A.AsanRTFacts.addressable_kept mem3 m' q n H MK). }
  apply (HX cx [Z.of_nat b] fr k ly3 S3 W3 R' m' md' HB).
  - (* the journal: written bytes in the window and the owned frame (YCbq.ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (sp - 32 <= a < sp) \/ (fr + 2176 <= a < fr + 2176 + 38)).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. unfold Wl. cbn [lib.Lib.Frame.outside].
      split; [intro H1; apply Hx; left; exact H1 | split; [intro H1; apply Hx; right; exact H1 | exact I]].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x) eqn:EH; [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      assert (Ex : x = lib.Lib.Mem.wa (bv_unsigned x)) by (unfold lib.Lib.Mem.wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
      destruct (Z_le_gt_dec (sp - 32) (bv_unsigned x)) as [L1 | L1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [L2 | L2] |].
      * (* the callee window: present after the run (stk), and no image byte *)
        destruct STK' as (_ & _ & Hst). destruct (Hst (bv_unsigned x) ltac:(lia)) as (_ & bb & Hbb).
        rewrite Ex. apply (rn_present_of_mrd m' (bv_unsigned x) bb Rx); [|exact Hbb].
        intros Himg. pose proof (A.ACtlG.Kit.kit_segs_low _ Himg) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl. lia.
      * (* above the window: untouched *)
        rewrite (MU x); [exact Hx|]. unfold Wl. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
      * destruct (Z_le_gt_dec (fr + 2176) (bv_unsigned x)) as [L3 | L3];
          [destruct (Z_lt_ge_dec (bv_unsigned x) (fr + 2176 + 38)) as [L4 | L4] |].
        -- (* the identity record: present after the run (rw_cells), and a frame byte, so no image byte *)
           destruct HIc as ((_ & (_ & _ & Hbr)) & _).
           cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hbr. rewrite app_nil_r in Hbr.
           assert (Hl38 : length (snd (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b)
                                         ad pb)) = 38%nat).
           { rewrite HINGs. exact (proj1 (A.Prog.Seg.RNIng.rn_RS_len (A.ACtlCut.c_in cx) (S b))). }
           pose proof (Hbr (Z.to_nat (bv_unsigned x - (fr + 2176))) ltac:(rewrite Hl38; lia)) as Hb1.
           replace (fr + 2176 + Z.of_nat (Z.to_nat (bv_unsigned x - (fr + 2176)))) with (bv_unsigned x)
             in Hb1 by lia.
           destruct (nth_error (snd (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b) ad pb))
                       (Z.to_nat (bv_unsigned x - (fr + 2176)))) as [bb|] eqn:En;
             [| apply nth_error_None in En; rewrite Hl38 in En; lia].
           rewrite Ex. apply (rn_present_of_mrd m' (bv_unsigned x) bb Rx); [|exact Hb1].
           apply Hfrimg. lia.
        -- rewrite (MU x); [exact Hx|]. unfold Wl. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
        -- rewrite (MU x); [exact Hx|]. unfold Wl. cbn [lib.Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
    + exact Hhid'.
    + exact Hsbm.
    + intros a [Ha | Ha].
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * right. right. right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, Hfs6. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 2 b + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81734_at (ACtlCutP.v:1441-1460), at the same index b *)
    cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A81734_at A.ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    exists phi.
    split; [exact HPerm|].
    split.
    { (* FRAC: the registers through R', the memory outside the write set *)
      exists Ab, sp.
      split; [first [rewrite E2a | rewrite E2]; exact Hr2|]. split; [exact Hspm|].
      split; [unfold Reusable.YG0d.spZ in *; first [rewrite E2 | rewrite E2a]; exact Hspz|].
      split; [first [rewrite E4a | rewrite E4]; exact Hr4|].
      split; [unfold A.ACtlCut.rgv in *; rewrite E8; exact Hr8|].
      split; [unfold A.ACtlCut.rgv in *; rewrite E9; exact Hr9|].
      split; [first [rewrite E3a | rewrite E3]; exact Hr3|].
      split; [unfold A.ACtlCut.rgv in *; rewrite E19; exact Hr19|].
      split; [unfold A.ACtlCut.rgv in *; rewrite E26; exact Hr26|].
      split; [exact Hfrm|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact HspA|].
      split; [exact HfrA|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HSapp|].
      unfold A.ACtlCutP.q64 in *.
      split; [apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Q304 MU);
              rewrite lib.Lib.Mem.length_le8; apply Hdj; lia|].
      split; [apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Q24 MU);
              rewrite lib.Lib.Mem.length_le8; apply Hdj; lia|].
      split; [apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Q16 MU);
              rewrite lib.Lib.Mem.length_le8; apply Hdj; lia|].
      split; [apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Qhdr MU);
              rewrite lib.Lib.Mem.length_le8; apply Hdj; lia|].
      split; [apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Qent MU);
              rewrite lib.Lib.Mem.length_le8; apply Hdj; lia|].
      split.
      { destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
        apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Hshb MU).
        rewrite Hshl. unfold A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES, A.ACtlCutP.Sfr,
          A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
        change (Z.of_nat (Z.to_nat (3136 / 8))) with 392.
        pose proof (Z.div_mod fr 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as M8.
        apply Hdj; lia. }
      split.
      { apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Hsaved MU).
        assert (Lsv : length (A.ACtlCutP.saved_bytes cx) = 104%nat).
        { unfold A.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity. }
        rewrite Lsv. apply Hdj; lia. }
      (* the fake-frame trailer word [fr + 4088, fr + 4096) (glue base batch 3): above the identity record and below
         the callee window, so outside the write set *)
      apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Qtrl MU).
      rewrite lib.Lib.Mem.length_le8. apply Hdj; lia. }
    split; [exact Hcn|]. split; [exact Hb6|].
    split; [destruct HHB as (Hphinz & HAphi); split; [exact Hphinz | exact (KA _ _ HAphi)]|].
    split; [unfold A.ACtlCut.rgv in *; rewrite E23; exact Hr23|].
    assert (HOUR' : A.ACtlCutP.OURb cx fr m').
    { unfold A.ACtlCutP.OURb in *. apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ HOUR MU).
      rewrite A.Prog.SlotModel.OUR_length. apply Hdj; lia. }
    split; [exact HOUR'|].
    split; [unfold A.ACtlCutP.OUTA in *; exact (KA _ _ HOUTA)|].
    assert (HCUR' : A.ACtlCutP.CUR cx 7 R').
    { destruct HCUR as (Hc0' & Hc22 & Hc25). unfold A.ACtlCutP.CUR, A.ACtlCut.rgv in *.
      split; [exact Hc0'|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split; [exact HCUR'|].
    split; [exact (KSP 112 _ ltac:(lia) Hs112)|].
    split; [exact (KSP 128 _ ltac:(lia) Hs128)|].
    split.
    { (* PRO: the spills through register 9, the input bytes and the three addressable ranges *)
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
                        P184 & P256 & P264 & P272 & P32).
      split; [exact (KSP 40 _ ltac:(lia) P40)|]. split; [exact (KSP 120 _ ltac:(lia) P120)|].
      split; [exact (KSP 136 _ ltac:(lia) P136)|]. split; [exact (KSP 160 _ ltac:(lia) P160)|].
      split; [exact (KSP 168 _ ltac:(lia) P168)|]. split; [exact (KSP 176 _ ltac:(lia) P176)|].
      split; [exact (KSP 208 _ ltac:(lia) P208)|]. split; [exact (KSP 248 _ ltac:(lia) P248)|].
      split; [exact (KA _ _ Pad)|].
      split.
      { (* the input: [] (A_EMPTY), or a live block of the entry, below alloc_ceiling and apart from the frame *)
        destruct HB as ((_ & _ & _ & _ & Hpn & Hlenin & _) & _).
        destruct Hpn as [(Hn0 & _) | (Hnpos & Hinb)].
        - assert (Ein : A.ACtlCut.c_in cx = []) by (apply length_zero_iff_nil; lia).
          rewrite Ein in Pin |- *.
          destruct Pin as (Pi0 & Pi1 & _). split; [exact Pi0|]. split; [exact Pi1|].
          intros i Hi. cbn [length] in Hi. lia.
        - assert (Hinb3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
          { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinb. }
          destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb3)
            as (_ & Hin4096 & Hinceil & _).
          pose proof (Reusable.YCbq.req_size_pos (A.ACtlCut.c_n cx) ltac:(lia)) as Hreq2.
          pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (A.ACtlCut.c_fpos cx)
                        HAR Hinb3 Hin6) as Hsep2.
          rewrite <- Efr, Hfs6 in Hsep2. unfold Reusable.YG0f.zdisjoint in Hsep2. cbn [fst snd] in Hsep2.
          apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ Pin MU).
          rewrite <- Hlenin. apply Hdj; lia. }
      split; [intros Hn; exact (KA _ _ (Pg Hn))|].
      split; [exact (KSP 184 _ ltac:(lia) P184)|]. split; [exact (KSP 256 _ ltac:(lia) P256)|].
      split; [exact (KSP 264 _ ltac:(lia) P264)|]. split; [exact (KSP 272 _ ltac:(lia) P272)|].
      exact (KSP 32 _ ltac:(lia) P32). }
    split; [exact (KSP 104 _ ltac:(lia) Hs104)|].
    split; [exact (KSP 96 _ ltac:(lia) Hs96)|].
    split; [exact (KSP 64 _ ltac:(lia) Hs64)|].
    split; [exact (KSP 144 _ ltac:(lia) Hs144)|].
    split; [exact (KSP 192 _ ltac:(lia) Hs192)|].
    split; [destruct HRWid as (idb0 & Hx); exists idb0;
            exact (KRW (fr + 2688) 38%nat idb0 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hx)|].
    split; [destruct HRWjk as (junk & Hx); exists junk;
            exact (KRW (fr + 2768) 72%nat junk ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hx)|].
    split; [exact (KSP 280 _ ltac:(lia) Hs280)|].
    split; [exact (KSP 240 _ ltac:(lia) Hs240)|].
    split; [destruct HRWjy as (jy & Hx); exists jy;
            exact (KRW (fr + 3040) 1%nat jy ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hx)|].
    split; [destruct HRWj32 as (junk & Hx); exists junk;
            exact (KRW (fr + 3056) 32%nat junk ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hx)|].
    split; [exact (KSP 152 _ ltac:(lia) Hs152)|].
    split; [unfold A.ACtlCut.rgv in *; rewrite E21; exact Hr21|].
    split; [exact (KA _ _ HAD38)|].
    split.
    { (* RXS *)
      split; [exact (KSP 48 _ ltac:(lia) Hs48)|]. split; [exact (KSP 56 _ ltac:(lia) Hs56)|].
      split; [exact (KSP 88 _ ltac:(lia) Hs88)|]. split; [exact (KSP 80 _ ltac:(lia) Hs80)|].
      split; [exact (KSP 72 _ ltac:(lia) Hs72)|]. split; [exact (KSP 8 _ ltac:(lia) Hs8)|].
      split; [exact (KSP 0 _ ltac:(lia) Hs0)|]. split; [exact (KSP 200 _ ltac:(lia) Hs200)|].
      split; [exact (KSP 216 _ ltac:(lia) Hs216)|].
      exact (KA _ _ HAD72). }
    (* X81734: the ingest result, s8 = phi and the records of turn S b *)
    split; [unfold A.ACtlCut.a0v, A.ACtlCut.rgv; exact E10|].
    split; [unfold A.ACtlCut.rgv in *; rewrite E24; exact Hr24|].
    split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|].
    split; [unfold A.ACtlCut.rgv in *; rewrite E23; exact Hr23|].
    split.
    { unfold A.ACtlCutP.IDBr. destruct HIc as ((_ & Hbb) & _).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hbb. rewrite app_nil_r, HINGs in Hbb. exact Hbb. }
    { unfold A.ACtlCutP.FGBr in *.
      apply (lib.Lib.Frame.bytes_at_transport segs Wl mem3 m' _ _ HFGB MU).
      rewrite (proj2 (A.Prog.Seg.RNIng.rn_RS_len (A.ACtlCut.c_in cx) (S b))). apply Hdj; lia. }
  - (* ctl_rt_C at ly3 S3: the runtime cells and the read-only bytes are image bytes; the two narrowed shadow
       conjuncts are kept (meta_kept, wmono) *)
    split; [|split; [|split]].
    + apply (A.AsanRTFacts.asan_cells_kept Wl mem3 m' HAC MU).
      unfold Wl. cbn [lib.Lib.Frame.disjoint_from]. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI.
      split; [left; lia|]. split; [|exact I].
      destruct (Z_le_gt_dec (0x9fad0 + (0xa9578 - 0x9fad0)) (fr + 2176)) as [H1 | H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (fr + 2176 + 38) 0x9fad0) as [H2 | H2]; [right; exact H2|].
      exfalso. apply (Hfrimg (Z.max (fr + 2176) 0x9fad0) ltac:(lia)).
      apply rn_rt_img. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. lia.
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' HSWc MK WM).
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' HSWi MK WM).
    + intros a Ha. rewrite <- (HRO a Ha). unfold lib.Lib.Mem.mrd. rewrite (MU a); [reflexivity|].
      pose proof (A.Prog.Seg.RNIng.rn_ro_lt a Ha) as Hlt.
      pose proof (rn_ro_img a Ha) as Himg.
      unfold Wl. cbn [lib.Lib.Frame.outside]. split; [lia|]. split; [|exact I].
      intros Hin. exact (Hfrimg (bv_unsigned a) ltac:(lia) Himg).
Qed.

End GlueRNIng.
