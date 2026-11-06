(* lib/A/ACtlG/F22.v -- GLUE for stage seg_F22 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:816) (an earlier version, blob 84ef756918c, not in this delivery)).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F22 : forall POST (j : nat),
       CF POST (ix_cut C_A825a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A82554_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F22, character for character (checked against the base's ACtl.v before the commit).
   Segment F22 is 0x82554 -> 0x825a0: the six record bytes [phi+34, phi+40) are summed by the loop
   (six turns, each one instrumented shadow check and one byte load), then 0x8258c-0x82594 turns the sum into
   s4 = (sum mod 128 = 0 ? 0 : -1) and 0x82598 / 0x8259c call reac_ctrl_headamp_record_verify, which returns
   to 0x825a0 with a0 = s4 = t_want_v.

   THE CHOICE THE TASK ASKS FOR (a) OR (b): THIS FILE TAKES (a), as lib/A/ACtlG/F21.v does and for the same
   measured reason: Seg/F22F.v's `f22_tail_F` (:159) has NO contract premise -- it discharges
   `reac_ctrl_headamp_record_verify_contract_F` outright with the callee's own proof
   `reac_ctrl_headamp_record_verify_F.reac_ctrl_headamp_record_verify_holds_F` (F22F.v:196) -- and its run
   spans the jal at 0x8259c.  The glue composes `f22_loop_F` (:68, CPS at 0x8258c) with `f22_tail_F` into ONE
   `ExecF.evtF` from 0x82554 to 0x825a0 and lifts it ONCE with Reusable.YA0nR.SRr_fevt_hid at
   RNG := A.ProgBridge.RNG_W (w_H W3), paying only the callee's `ExecF.rng` regions from the walk's own
   visibility facts.  Route (b), the ported cgif-form walk pb_ctrl_headamp_record_verify, would need the run
   cut at the jal (F22F.v has no pre/post split), a new stretch lemma, the spec's afn_pre / afobj_any
   obligations and a second lift: strictly more obligations for the same stage statement.  This also matches
   a Theorem Labs lane's 04:10Z route ruling and the 04:01Z split rule (headamp is not one of the eight fake-stack
   callees, and its `_F` IS proved on the base).  NO `<f>_SRr_at` AND NO `_hid` PLACEHOLDER IS CITED.

   THE PROOF (glue-pattern.md section 3, with section 8's loop note: a run-level loop needs no cut construct,
   it is inside the one lifted run)
   G1  unfold the entry cut C_A82554_at (ACtlCutP.v:2582-2592): FRAC and b7_body's seven conjuncts.
   G2  the bounds from VISIBLE state only, exactly as F21.v derives them (frames_bounds + the frame law +
       layout_le's ly_F; the journal's astk_ok; AR_blocks_law for the live block; the core's lib pre for the
       input block; FRAC for the spill base A and sp).
   G3  ProgBridge.cfg_at_MS, the two registers the run pins (sp at x2, s7 = phi at x23) rewritten into the
       canonical map, then Reusable.YA0nR.SRr_xregs_eqv.
   G4  the run: f22_loop_F at n = 6, i = 0 with its continuation instantiated by f22_tail_F, giving one evtF
       from 0x82554 to 0x825a0; then ProgBridge.fevt_of_evtF / tfibsegs_rsegs and ONE SRr_fevt_hid.
   G5  the continuation: the journal across [sp - 16, sp) by Reusable.YCbq.ajournal_exec, ctl_rt_C by
       F21.f21_rt_move, FRAC by kit_frac_move + F21.f21_frac_mem, HB / FLSI / B7K by F21.f21_core_move, then
       the exit cut C_A825a0_at with a0 = s4 = t_want_v (f22_want_hv and f22_hv at the record type bytes 4/3).

   HELPERS SHARED WITH F21: this file Requires A.ACtlG.F21 and cites its six proof-internal helpers
   (f21_bytes_keep, f21_q64_keep, f21_stk_keep, f21_spill_base, f21_frac_mem, f21_core_move, f21_rt_move),
   which are Qed-closed there and take their Section arguments explicitly here.  They are NOT kit helpers and
   are not copied: one writer (this lane) owns both files.

   ROUTE (C), L3 switch (a working branch 1899bed1aee): ctl_from's premise is now
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  ENTRY: only the cells (HAC) are read; the tail run is Seg/F22Fon.v's twin
   f22_tail_F_on (Seg/F22F.v's f22_tail_F only handed its universal `shadow_rw m` on to the record verifier, whose
   route (C) contract _contract_F_on drops it; both LANDED), so no region proof is needed (consumer row F22.v:192,315
   closes with no consumer left).  f22_loop_F has no shadow_rw premise and is cited from F22F.v as it is.  EXIT: the
   state is kept, so ctl_rt_C crosses the window by F21.f21_rt_move (regions kept with A.ShadowRwOnK.fl_shadow_rw_on).
   The stage statement is unchanged.

   SECTION HYPOTHESES: ONE, and it is ACtl.v's own.
   - LAWS: the core's AR law record (YCbq.v:207), ACtl.v:185's own.
   THE KIT IS CITED, NOT RESTATED: on the newer glue base a working branch 46eb24cd4b3
   lib/A/ACtlG/Kit.v (blob 7e164a09a73) BUILDS, so this file's three placeholders are deleted and
   A.ACtlG.Kit.kit_wx / kit_segs_low / kit_frac_move are cited.  NO OTHER HYPOTHESIS IS LEFT.

   CLOSURE and SHADOWED NAMES: as F21.v's header says (qualified Requires only, `lib.<X>` module paths, no
   frame-route identifier in any statement, getr / mkst / seg_rom / cfg_at qualified).

   BUILD STATE (honest): as F21.v's header says - a working branch, interim core
   5da74c9c931 (zero stand-ins) over glue base 46eb24cd4b3, Tk/AW and a Theorem Labs lane's ProgWorld files by path; the same
   406-file closure, none substituted.
   No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0n Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ACtlG.Kit A.ACtlG.F21.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisHeap A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcParse Prog.RcLeaf Prog.RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F22F A.Prog.Seg.F22Fon A.Prog.Seg.F22.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF22.

(* ACtl.v's Section shape (ACtl.v:170-183), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:216-218 and the cut records), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82554_at := (ACtlCutP.C_A82554_at B).
Local Notation C_A825a0_at := (ACtlCutP.C_A825a0_at B).

(* The core's AR laws (YCbq.v:207), ACtl.v:183's LAWS. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F22 : forall POST (j : nat), CF POST (ix_cut C_A825a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A82554_at [Z.of_nat j]).
Proof.
  intros POST j H5a0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (C_A82554_at, ACtlCutP.v:2582-2592). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82554_at ACtlCutP.ixn ACtlCutP.b7_body nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hn26 & Hj255 & HHB & HFLSI & HB7 & Hrec & Hcp18 & Hcp19 &
    R10 & R12 & R13 & R11).
  pose proof HB7 as (HLK & R23 & R22 & Hphi0 & Hphi50 & Hbig & Hblk & S280 & R24 & R18 & S152 & Hgb & Hpb &
    Hpl & HLT & S136 & S120 & S176).
  (* G2: the bounds, from visible state. *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & Hsphi & H47 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (Hac & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : fr = lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite <- Efr3 in Hf4096, Hfceil.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  pose proof HFRAC as (A & sp & Esp & _ & Hspz & _ & _ & R9 & _ & _ & R26 & _ & _ & HAc & HspA & HfrA & HA416 &
    Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo. unfold A.AsanRT.APPMEM_END in HSapp. unfold ACtlCutP.FRAME_BYTES in HfrA.
  unfold ACtlCut.rgv in R10, R11, R12, R13.
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (Hphi16 & Hphi4096 & Hphiceil & _).
  assert (Ereq : lib.Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
    by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia).
  rewrite Ereq in Hphiceil.
  assert (Hinp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  x < sp - 16).
  { pose proof HB as ((HPRE & _ & _ & _ & Hpn & Hnl & _) & _).
    intros x Hx. rewrite <- Hnl in Hx.
    destruct Hpn as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HPRE) Hinp) as (_ & _ & Hpc & _).
    unfold lib.Reusable.YG00.req_size in Hpc. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (Hspr : 0 <= sp < 2 ^ 64) by lia.
  assert (Hhm : A.AsanRT.HIGHMEM_BEG <= sp - 16) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (Hsapp : sp <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  assert (Hfrlo : fr + ACtlCutP.FRAME_BYTES <= sp - 16) by (unfold ACtlCutP.FRAME_BYTES; lia).
  (* the class-6 frame's last byte, for FRAC's trailer word at fr + 4088 (batch 3): frames_bounds gives
     fr + 4096 <= alloc_ceiling, astk_ok gives alloc_ceiling + LLVMF_STK <= c_sp, FRAC gives c_sp - 4096 < sp *)
  assert (Hftlo : fr + 4096 <= sp - 16) by lia.
  assert (Hshlo : ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW <= sp - 16).
  { change ACtlCutP.FRAME_SHADOW with 392. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    pose proof (Z.div_le_upper_bound fr 8 fr ltac:(lia) ltac:(lia)). lia. }
  assert (Hphilo : phi + ACtlCutP.flen cx j <= sp - 16) by lia.
  (* the record's two type bytes, as the run's b0 / b1 *)
  assert (Hdec : exists b0 b1 rest, A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j = b0 :: b1 :: rest).
  { pose proof (A.Prog.Seg.F22.f22_t_blk_len (ACtlCut.c_in cx) j) as L.
    destruct (A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j) as [|x [|y r]]; cbn [length] in L; try lia. eauto. }
  destruct Hdec as (b0 & b1 & rest & Eblk).
  assert (Hblk2 : lib.Lib.Mem.bytes_at segs mem3 (phi + 18) (b0 :: b1 :: rest)) by (rewrite <- Eblk; exact Hblk).
  assert (Hblk18 : lib.Lib.Mem.bytes_at segs mem3 (phi + 18) [b0; b1])
    by exact (A.Prog.Seg.F22.f22_ba_pre2 mem3 (phi + 18) b0 b1 rest Hblk2).
  assert (Ey0 : bv_unsigned b0 = lib.Prog.RcParse.cp_v (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 18).
  { pose proof (A.Prog.Seg.F22.f22_blk_cp (ACtlCut.c_in cx) j 0 ltac:(lia)) as X. rewrite Eblk in X.
    cbn [nth Nat.add] in X. unfold lib.Prog.RcParse.cp_v. rewrite <- X. reflexivity. }
  assert (Ey1 : bv_unsigned b1 = lib.Prog.RcParse.cp_v (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 19).
  { pose proof (A.Prog.Seg.F22.f22_blk_cp (ACtlCut.c_in cx) j 1 ltac:(lia)) as X. rewrite Eblk in X.
    cbn [nth Nat.add] in X. unfold lib.Prog.RcParse.cp_v. rewrite <- X. reflexivity. }
  assert (E18 : bv_unsigned b0 = 4) by (rewrite Ey0; exact Hcp18).
  assert (E19 : bv_unsigned b1 = 3) by (rewrite Ey1; exact Hcp19).
  set (g6 := lib.Prog.RcFrag.bsl (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 34 6) in *.
  assert (Ewant : A.Prog.SlotModel.t_want_v (ACtlCut.c_in cx) j = (if lib.Prog.RcLeaf.hv b0 b1 g6 then 0 else -1))
    by (rewrite A.Prog.Seg.F22.f22_want_hv, Eblk; reflexivity).
  assert (Ehv : lib.Prog.RcLeaf.hv b0 b1 g6 = (lib.Prog.RcModel.psum g6 6 mod 128 =? 0))
    by exact (A.Prog.Seg.F22.f22_hv b0 b1 g6 E18 E19).
  (* the shadow bytes of the six record bytes, and the two addressable ranges *)
  assert (Hal8 : phi mod 8 = 0).
  { pose proof (Z.div_mod phi 16 ltac:(lia)). pose proof (Z.div_mod phi 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound phi 8 ltac:(lia)). lia. }
  pose proof HHB as (_ & Hadr). unfold A.ACtlK.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  assert (HSH : forall i, (i < 6)%nat ->
    ACtlCutP.b8 mem3 (Z.shiftr (phi + 34 + Z.of_nat i) 3 + A.AsanRT.ASAN_K) 0).
  { intros i Hi. replace (phi + 34 + Z.of_nat i) with (phi + (34 + Z.of_nat i)) by lia.
    apply (A.Prog.Seg.F22.f22_sh0 mem3 phi (ACtlCutP.flen cx j)); [exact Hadr | exact Hal8 | lia |].
    assert (E8 : (34 + Z.of_nat i) / 8 = 4)
      by (symmetry; apply (Z.div_unique (34 + Z.of_nat i) 8 4 (34 + Z.of_nat i - 32)); lia).
    rewrite E8. lia. }
  pose proof (A.AsanRTFacts.addressable_sub mem3 phi _ 18 2 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr2.
  pose proof (A.AsanRTFacts.addressable_sub mem3 phi _ 34 6 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr6.
  pose proof Hrt as (HAC & _ & _ & _).
  assert (Hstk : lib.Lib.Frame.stk segs mem3 (sp - 16) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hbb).
    split.
    - unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate.
    - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  (* the footprint (as F21.v: heap_vis / heap_sh_vis, win_vis, rt_vis_W) *)
  set (RNG := A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)).
  (* the re-pointed win_vis states A.ProgWorld.win_vis_stmt B, whose journal's sink head is ProgWorld's own
     instance A.AE2k.tfib_sink_head (ProgWorld.v:77), the one this stage's journal takes *)
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (V18 : lib.Lib.ExecF.rng RNG (phi + 18) 2).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j));
      [exact HAR | exact Hinphi | lia | rewrite Ereq; lia]. }
  assert (V34 : lib.Lib.ExecF.rng RNG (phi + 34) 6).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j));
      [exact HAR | exact Hinphi | lia | rewrite Ereq; lia]. }
  assert (VS18 : lib.Lib.ExecF.rng RNG (A.AsanRT.shadow_addr (phi + 18))
                   (A.AsanRT.shadow_addr (phi + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 2
                HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV]; [lia|].
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      Z.div_mod_to_equations; lia. }
  assert (VS34 : lib.Lib.ExecF.rng RNG (A.AsanRT.shadow_addr (phi + 34))
                   (A.AsanRT.shadow_addr (phi + 39) - A.AsanRT.shadow_addr (phi + 34) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 34) 6
                HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV]; [lia|].
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      Z.div_mod_to_equations; lia. }
  assert (VFr : lib.Lib.ExecF.rng RNG (sp - 16) 16).
  { apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | |]; unfold A.ACfn.LLVMF_STK; lia. }
  assert (VGOT : lib.Lib.ExecF.rng RNG A.AsanRT.GOT_CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.rt_vis_W W3));
      unfold A.AsanRT.GOT_CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  assert (VCK : lib.Lib.ExecF.rng RNG A.AsanRT.CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.rt_vis_W W3));
      unfold A.AsanRT.CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  (* G3 / G4: the composed run, 0x82554 -> 0x8258c (f22_loop_F) -> 0x825a0 (f22_tail_F) *)
  assert (HRUN : lib.Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
       ms' = lib.Lib.MState.MS
         (lib.Lib.Frame.mkR ra' (Z_to_bv 64 sp)
            (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
            (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
            (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
            (lib.Reusable.YK11.getr regs3 9)
            (Z_to_bv 64 (if lib.Prog.RcLeaf.hv b0 b1 g6 then 0 else -1))
            a1' a2' a3' a4' a5' a6' (lib.Reusable.YK11.getr regs3 17)
            (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19)
            (Z_to_bv 64 (if lib.Prog.RcModel.psum g6 6 mod 128 =? 0 then 0 else -1))
            (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (Z_to_bv 64 phi)
            (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
            (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
            (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
            (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31))
         lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x825a0) lib.Reusable.YK11.fp_csr None m'
         (lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
       lib.Lib.Frame.munch [(sp - 16, sp)] mem3 m' /\ lib.Lib.Frame.wmono A.Img0.rsegs mem3 m' /\
       lib.Lib.Frame.stk A.Img0.rsegs m' (sp - 16) sp)
    (lib.Lib.MState.MS
      (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs3 1) (Z_to_bv 64 sp)
         (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
         (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
         (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
         (lib.Reusable.YK11.getr regs3 9) (lib.Reusable.YK11.getr regs3 10)
         (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
         (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14)
         (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16)
         (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
         (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
         (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (Z_to_bv 64 phi)
         (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
         (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
         (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
         (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31))
      lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82554) lib.Reusable.YK11.fp_csr None mem3
      (lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
  { apply (A.Prog.Seg.F22F.f22_loop_F RNG _
      (lib.Reusable.YK11.getr regs3 1) (Z_to_bv 64 sp)
      (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
      (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
      (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
      (lib.Reusable.YK11.getr regs3 9) (lib.Reusable.YK11.getr regs3 15)
      (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17)
      (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19)
      (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
      (lib.Reusable.YK11.getr regs3 22) (Z_to_bv 64 phi)
      (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
      (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
      (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
      (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)
      lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 (phi + 34) g6)
      with (n := 6%nat) (i := 0%nat);
      [ exact R26 | lia | lia | exact (A.Prog.Seg.F22.f22_t_g6_len _ _) | exact Hrec | exact HSH | | | | | |
      | | | ].
    - (* the loop's continuation at 0x8258c: the tail, through the record verifier *)
      intros a0' a2' a3' a4'.
      apply (A.Prog.Seg.F22Fon.f22_tail_F_on RNG
        (lib.Reusable.YK11.getr regs3 1)
        (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
        (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
        (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
        (lib.Reusable.YK11.getr regs3 9) a0' a2' a3' a4'
        (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16)
        (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
        (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
        (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22)
        (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
        (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
        (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
        (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)
        lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 phi (sp - 16) sp b0 b1 g6
        Hspr Hphi0 ltac:(unfold A.AsanRT.APPMEM_END; lia) ltac:(lia) Hhm ltac:(lia)
        Hblk18 (A.Prog.Seg.F22.f22_t_g6_len _ _) Hrec Hstk HAC Hadr2 Hadr6
        V18 V34 VS18 VS34 VFr VGOT VCK).
    - lia.
    - lia.
    - rewrite R10; f_equal; lia.
    - rewrite R12; f_equal; lia.
    - rewrite R13; f_equal; first [reflexivity | lia].
    - rewrite R11; f_equal; first [reflexivity | cbn; lia].
    - exact V34.
    - apply A.ProgBridge.rng_of_visible.
      destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 34) 6
                  HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV]; [lia|].
      apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
        unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
        Z.div_mod_to_equations; lia. }
  (* G3: the cut's configuration, then the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82554_at [Z.of_nat j])) with 0x82554.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82554) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  assert (Esp' : lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp) by exact Esp.
  assert (R23' : lib.Reusable.YK11.getr regs3 23 = Z_to_bv 64 phi) by exact R23.
  assert (Estart : lib.Lib.Regs6ss.mkR_of regs3 =
    lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs3 1) (Z_to_bv 64 sp)
      (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
      (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
      (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
      (lib.Reusable.YK11.getr regs3 9) (lib.Reusable.YK11.getr regs3 10)
      (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
      (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14)
      (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16)
      (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
      (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
      (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (Z_to_bv 64 phi)
      (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25)
      (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
      (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
      (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  { rewrite <- Esp', <- R23'. reflexivity. }
  rewrite Estart.
  (* G4: the lift of the whole run *)
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the continuation *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & Ems & MU & WM & ST').
  subst ms'.
  match goal with |- context [lib.Lib.MState.MS ?R0 _ _ _ _ _ _] => remember R0 as R eqn:ER end.
  assert (G2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by (rewrite ER, Esp'; reflexivity).
  assert (G3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by (rewrite ER; reflexivity).
  assert (G4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by (rewrite ER; reflexivity).
  assert (G8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by (rewrite ER; reflexivity).
  assert (G9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite ER; reflexivity).
  assert (G18 : lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18) by (rewrite ER; reflexivity).
  assert (G19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite ER; reflexivity).
  assert (G21 : lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) by (rewrite ER; reflexivity).
  assert (G22 : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by (rewrite ER; reflexivity).
  assert (G23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by (rewrite ER, R23'; reflexivity).
  assert (G24 : lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24) by (rewrite ER; reflexivity).
  assert (G26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by (rewrite ER; reflexivity).
  assert (HspzR : lib.Reusable.YG0d.spZ R = sp).
  { unfold lib.Reusable.YG0d.spZ in *. rewrite G2. exact Hspz. }
  (* the journal across the record verifier's frame [sp - 16, sp) *)
  assert (HJ' : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => sp - 16 <= a < sp); [exact HJ | | | exact Hhid | exact Hsbm | ].
    - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
      change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 16)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]].
      destruct ST' as (_ & _ & HST). destruct (HST (bv_unsigned x) ltac:(lia)) as (_ & b & Hbb).
      unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in Hbb. rewrite Z_to_bv_bv_unsigned in Hbb.
      assert (Hr0 : lib.Lib.PropExec.seg_rom segs x = None).
      { pose proof (lib.Reusable.YCbq.seg_rom_none segs (bv_unsigned x) Rx
          ltac:(intros Hi; apply A.ACtlG.Kit.kit_segs_low in Hi; unfold lib.Reusable.YG0f.kLowMemEnd in Hi; lia)) as Hz.
        rewrite Z_to_bv_bv_unsigned in Hz. exact Hz. }
      intros Em. rewrite Em, Hr0 in Hbb. discriminate.
    - intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia. }
  assert (Hrt' : A.ACtlRtC.ctl_rt_C B ly3 S3 m')
    by exact (A.ACtlG.F21.f21_rt_move B ly3 S3 mem3 m' (sp - 16) sp Hrt MU WM Hhm Hsapp).
  assert (HFRAC' : ACtlCutP.FRAC B cx fr fr R m').
  { apply (A.ACtlG.F21.f21_frac_mem B cx fr fr R mem3 m' (sp - 16) sp);
      [| exact MU | lia | lia | exact Hftlo | exact Hshlo].
    exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC G2 G3 G4 G8 G9 G19 G26). }
  destruct (A.ACtlG.F21.f21_core_move cx j fr phi regs3 R mem3 m' (sp - 16) sp A HHB HFLSI HB7 MU Hhm Hsapp R9
              ltac:(lia) ltac:(lia) HspA ltac:(lia) Hfrlo Hphilo Hinp G9 G18 G21 G22 G23 G24)
    as (HHB' & HFLSI' & HB7').
  (* the exit cut C_A825a0_at (ACtlCutP.v:2596-2604) *)
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A825a0_at [Z.of_nat j])) R m' md') (POST cx)).
  apply (H5a0 cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB); [exact HJ' | exact HF | exact HL | exact Hk | | exact Hrt'].
  split; [reflexivity|].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825a0_at ACtlCutP.ixn ACtlCutP.b7_body nth].
  rewrite Nat2Z.id.
  split; [exact HFRAC'|].
  exists phi.
  split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
  split; [exact HHB'|]. split; [exact HFLSI'|]. split; [exact HB7'|].
  unfold ACtlCut.rgv. rewrite ER, Ewant, Ehv.
  split; reflexivity.
Qed.

End GlueF22.

Print Assumptions glue_seg_F22.
