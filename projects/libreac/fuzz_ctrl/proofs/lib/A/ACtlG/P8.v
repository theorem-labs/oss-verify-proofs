(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v; 326 of its 355 lines of code are new or changed and 937 lines of the source are left out. *)
(* lib/A/ACtlG/P8.v -- GLUE for stage seg_P8 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:727),
   and the W3-between-loops body lemmas the stages seg_P7, seg_P9 and seg_P10 also use (lib/A/ACtlG/P7.v, P9.v,
   P10.v Require this file qualified).  Written by a Theorem Labs lane's glue lane (piece W3, second part); single
   writer.  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_P8 : forall POST, CF POST C_A81c34 -> CF POST C_A81c20
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P8.  Segment P8 is 0x81c20 -> 0x81c34 (Seg/P8.v:1-8): beq a0,s2 (taken, a0 = s2 = -1); mv a0,s5; li a1,0;
   jal reac_ports_parse.  With q = a1 = 0 the callee fails and writes only its 16-byte frame [sp - 16, sp).

   THE RUN.  a Theorem Labs lane's mechanical v1.9 re-run A.Prog.Seg.P8F.p8_evt_F (Seg/P8F.v:39 (an earlier version, blob a693c87b06bb, not in this delivery)),
   Required, not assumed.  Its one callee premise reac_ports_parse_contract_F is discharged by the PROVED
   A.Prog.reac_ports_parseF.reac_ports_parse_F_holds (reac_ports_parseF.v:436).  The segment is lifted WHOLE (split
   rule of a Theorem Labs lane, 04:01Z: never split at a lifted callee).

   THE PROOF (glue-pattern.md section 3; memory-writing run)
   G1  unfold the entry cut C_A81c20 (ACtlCutP.v:1878-1889): 17 conjuncts.
   G2  the run's premises: a0 = -1 (the body's a0v), s2 = -1 (rgv 18), the callee window [sp - 16, sp) present
       (stk, KitMem.kitmem_stk_of_journal from the journal's presence conjunct) and visible
       (ProgWorldVisWin.win_vis), sp from FRAC.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then YA0nR.SRr_fevt at RNG_W (w_H W3); the run's fsteps is kept in
       the post (w3_fevt_run) so that the journal crosses the run by a Theorem Labs lane's PROVED ProgWorld.ajournal_of_fsteps.
   G5  the exit cut C_A81c34 at the run's end map: journal (ajournal_of_fsteps, the window is the stack case of
       awr_byte), frames / frame law / k unchanged, body by w3_core_keep (every body byte lies outside the window),
       ctl_rt_C by w3_ctlrtC_munch below (route (C): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3; the state
       (ly3, S3) is kept, so its regions are kept across the munch, recipe L3 section 2(d)).

   SECTION HYPOTHESIS (exact text below)
   - LAWS: the core's AR law record (YCbq.v Section a0), as A5.v takes it; ACtl.v:183 has it.
   CITED BY NAME from a Theorem Labs lane's shared lib/A/ACtlG/KitMem.v (a working branch 4a56e997c0f, merged):
     kitmem_stk_of_journal (the window present), kitmem_bytes_munch / kitmem_addr_munch / kitmem_spill_munch /
     kitmem_frac_munch (body bytes outside the write list), kitmem_asan_cells_img / kitmem_ro_agree_img /
     kitmem_outside_dec (inside w3_ctlrtC_munch).  FRAC is
     re-established at the run's end memory by kitmem_frac_munch (BY SHAPE, so it carries the announced trailer
     word q64 m (fr + 4088) ..) and Kit.kit_frac_move, inside w3_core_keep.
   NOT USED: rt_of_core / ctl_rt_C_of_AR (no runtime cell is read by this run; ctl_rt_C is carried across the munch).

   CLOSURE (glue closure rule): every Require is qualified.  The six module names that exist both as the core's
   lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09; a Theorem Labs lane 03:5xZ) are written
   through the fully qualified aliases CK11 / CM05 / CO09 / CI16 below, and lib/Lib's modules through LFrame /
   LMem / LMState / LRegs, so a partial name never resolves to a twin.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only CK11.* / Reusable.YG0d.cfg_at.

   BUILD STATE: see the commit message (type-check on the planning core with the workspace-only substitution of
   port_core_refused_* names; values do not count). *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel Prog.RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_parse_c A.Prog.reac_ports_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P8F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* A footprint run's fsteps, kept next to its post (so that the continuation of SRr_fevt can hand it to
   ProgWorld.ajournal_of_fsteps). *)
Lemma w3_fevt_run : forall (sg : list Segment) RNG ms (P : machine_state -> Prop),
  (exists ms', Reusable.YK04R.fsteps sg RNG ms ms' /\ P ms') ->
  exists ms', Reusable.YK04R.fsteps sg RNG ms ms' /\ (Reusable.YK04R.fsteps sg RNG ms ms' /\ P ms').
Proof. intros sg RNG ms P (ms' & Hr & HP). exists ms'. exact (conj Hr (conj Hr HP)). Qed.

(* The bytes a one- or two-interval write list does not leave alone. *)
Lemma w3_not_outside1 : forall lo hi x, ~ LFrame.outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. cbn [LFrame.outside] in H.
  destruct (Z_lt_le_dec x lo) as [h1|h1]; [exfalso; apply H; split; [lia | exact I]|].
  destruct (Z_lt_le_dec x hi) as [h2|h2]; [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma w3_not_outside2 : forall lo hi lo' hi' x, ~ LFrame.outside [(lo, hi); (lo', hi')] x ->
  (lo <= x < hi) \/ (lo' <= x < hi').
Proof.
  intros lo hi lo' hi' x H. cbn [LFrame.outside] in H.
  destruct (Z_lt_le_dec x lo) as [h1|h1].
  - destruct (Z_lt_le_dec x lo') as [h3|h3]; [exfalso; apply H; split; [lia | split; [lia | exact I]]|].
    destruct (Z_lt_le_dec x hi') as [h4|h4]; [right; lia | exfalso; apply H; split; [lia | split; [lia | exact I]]].
  - destruct (Z_lt_le_dec x hi) as [h2|h2]; [left; lia|].
    destruct (Z_lt_le_dec x lo') as [h3|h3]; [exfalso; apply H; split; [lia | split; [lia | exact I]]|].
    destruct (Z_lt_le_dec x hi') as [h4|h4]; [right; lia | exfalso; apply H; split; [lia | split; [lia | exact I]]].
Qed.

(* Route (C): the cut's carried A.ACtlRtC.ctl_rt_C across a run whose writes are application memory off the image,
   at the same state (ly, S).  The twin of KitMem.kitmem_ctlrt_munch (ACtlCut.ctl_rt) with each of the two shadow
   regions kept by the same per-address argument under its guard: a written byte is application memory, so it is
   no shadow byte (AsanRTFacts.app_not_shadow), so every shadow byte the region names keeps its value.  Used by
   P7.v, P8.v, P9.v and P10.v at their exits. *)
Lemma w3_ctlrtC_munch : forall (B : Reusable.YG0f.asyms) ly S (WR : list LFrame.ivl) (m m' : word -> option byte),
  A.ACtlRtC.ctl_rt_C B ly S m -> LFrame.munch WR m m' ->
  (forall x, ~ LFrame.outside WR x -> A.AsanRT.app_mem x /\ ~ Reusable.YG0d.in_img segs x) ->
  A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros B ly S WR m m' (AC & SC & SI & RO) MU HW.
  assert (HW' : forall x, ~ LFrame.outside WR x -> ~ Reusable.YG0d.in_img segs x) by (intros x Hx; apply HW, Hx).
  assert (Hkeep : forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m').
  { intros P SR a Hp Ha. destruct (SR a Hp Ha) as [Hw (b & Hb)].
    destruct (A.AsanRTFacts.in_shadow_range a Ha) as [R1 R2].
    assert (Ho : LFrame.outside WR a).
    { destruct (A.ACtlG.KitMem.kitmem_outside_dec WR a) as [Ho|Ho]; [exact Ho|].
      exfalso. exact (A.AsanRTFacts.app_not_shadow a (proj1 (HW a Ho)) Ha). }
    assert (E : m' (LMem.wa a) = m (LMem.wa a)) by (apply MU; rewrite LMem.wa_unsigned by lia; exact Ho).
    split.
    - unfold wview in *. rewrite E. exact Hw.
    - exists b. unfold LMem.mrd in *. rewrite E. exact Hb. }
  exact (conj (A.ACtlG.KitMem.kitmem_asan_cells_img WR m m' AC MU HW')
        (conj (Hkeep _ SC) (conj (Hkeep _ SI) (A.ACtlG.KitMem.kitmem_ro_agree_img WR m m' RO MU HW')))).
Qed.

Section GlueP8.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :257-258), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81c20 := (A.ACtlCutP.C_A81c20 B).
Local Notation C_A81c34 := (A.ACtlCutP.C_A81c34 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses. *)

(* The core's AR laws (YCbq.v Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.


(* ---------------------------------------------------------------------------------------------------------
   The W3-between-loops lemmas (also used by P7.v, P9.v, P10.v). *)

(* The conjuncts every cut from C_A81bf8 to C_A81c60 carries (ACtlCutP.v:1863-1934), FRAC at sel = fr. *)
Definition w3_core (cx : ACtlCut.ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  A.ACtlCutP.FRAC B cx fr fr regs m /\ A.ACtlCutP.OURb cx fr m /\
  A.ACtlCutP.CUR cx (A.Prog.SlotModel.c0 (ACtlCut.c_in cx)) regs /\ A.ACtlCutP.PRO cx fr regs m /\
  A.ACtlCutP.spill regs m 144 (fr + 2688) /\ A.AsanRT.addressable m (fr + 2691) 17 /\
  A.ACtlCutP.spill regs m 192 (A.ACtlCutP.fragb fr) /\ A.AsanRT.addressable m (A.ACtlCutP.fragb fr) 72 /\
  A.AsanRT.addressable m (fr + 2688) 38 /\ A.ACtlCutP.IDBe cx fr Prog.RcIdentModel.ID0 m /\
  A.ACtlCutP.FGBe cx fr A.Prog.SlotModel.z72 m /\ A.ACtlCutP.XC fr regs m /\
  A.AsanRT.addressable m (fr + 2880) 35.

(* The bounds every W3 stage reads from visible state: the owned class-6 frame (frames_bounds, AR_frames_law,
   AR_client_img_law at the journal's AR, the frame law and layout_le's ly_F), the journal's stack window
   (astk_ok), and the input block (the lib pre's live block and AR_blocks_law at the entry AR). *)
Lemma w3_bounds : forall cx fr k ly3 S3 W3 mem3 md3,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr /\
  4096 <= fr /\ fr + 4096 <= CM05.alloc_ceiling /\
  (forall i, 0 <= i < 4096 -> A.AsanRT.app_mem (fr + i) /\ ~ Reusable.YG0d.in_img segs (fr + i) /\
     Reusable.YA0n.w_H W3 (Z_to_bv 64 (fr + i)) = false /\ exists b, mem3 (Z_to_bv 64 (fr + i)) = Some b) /\
  (forall i, 0 <= i < 512 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 (Reusable.YG0f.shadow_addr fr + i)) = false) /\
  CM05.alloc_ceiling <= ACtlCut.c_sp cx - A.ACfn.LLVMF_STK /\ ACtlCut.c_sp cx <= 2 ^ 47 /\
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
     x < CM05.alloc_ceiling /\ (x < fr \/ fr + 4096 <= x)).
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HB HJ HF HL HP.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold Reusable.YG0f.frame_addr.
    rewrite EF. reflexivity. }
  assert (EB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hceil & Happ).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & Hpres & Hspres).
  rewrite <- Efr in H4096, Hceil, Happ, Hpres, Hspres. rewrite EB in Hceil, Happ, Hpres, Hspres.
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  destruct Hstk as (_ & _ & Hlo & Hlosp & Hsphi & H47 & _).
  split; [symmetry; exact Efr|].
  split; [exact H4096|]. split; [exact Hceil|].
  split.
  { intros i Hi. split; [|split; [|split]].
    - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL in Happ.
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 (fr + i) HAR _)).
      right; left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite <- Efr, EB. lia.
    - destruct (Hpres (fr + i) ltac:(lia)) as ((Hh & _) & _). exact Hh.
    - destruct (Hpres (fr + i) ltac:(lia)) as ((_ & b & Eb) & _). exists b. exact Eb. }
  split.
  { intros i Hi. assert (E512 : 4096 / 8 = 512) by reflexivity. rewrite E512 in Hspres.
    destruct (Hspres i Hi) as ((Hh & _) & _). exact Hh. }
  split; [unfold A.ACfn.LLVMF_STK in *; lia|].
  split; [change (2 ^ 47) with 140737488355328 in H47 |- *; lia|].
  intros x Hx.
  destruct HB as (Hpre & _). destruct Hpre as (Hafn & _ & _ & _ & Hpn & Hlen & _).
  destruct Hafn as (HAR0 & _).
  destruct Hpn as [(E0 & _) | (Hn0 & Hin0)]; [lia|].
  destruct (Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & _ & Hc & _).
  assert (Rq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
  rewrite Rq in Hc.
  assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin0]).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin)
    as Hsep.
  unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Rq, <- Efr, EB in Hsep.
  split; lia.
Qed.

(* The core conjuncts move to a map R that keeps the registers they read (2 3 4 8 9 19 22 25 26) and to a memory
   m' that agrees with m outside a write list WR leaving alone everything at or above sp, the shadow, the first
   2880 bytes of the frame, its trailer word [fr + 4088, fr + 4096), and the input block. *)
Lemma w3_core_keep : forall cx fr (regs R : bvmap 5 word) (m m' : word -> option byte) (WR : list LFrame.ivl),
  w3_core cx fr regs m ->
  CK11.getr R 2 = CK11.getr regs 2 -> CK11.getr R 3 = CK11.getr regs 3 -> CK11.getr R 4 = CK11.getr regs 4 ->
  CK11.getr R 8 = CK11.getr regs 8 -> CK11.getr R 9 = CK11.getr regs 9 -> CK11.getr R 19 = CK11.getr regs 19 ->
  CK11.getr R 22 = CK11.getr regs 22 -> CK11.getr R 25 = CK11.getr regs 25 ->
  CK11.getr R 26 = CK11.getr regs 26 ->
  LFrame.munch WR m m' ->
  (forall i, 0 <= i < 4096 -> A.AsanRT.app_mem (fr + i)) ->
  (forall x, Reusable.YG0d.spZ regs <= x -> LFrame.outside WR x) ->
  (forall x, A.AsanRT.in_shadow x -> LFrame.outside WR x) ->
  (forall x, (fr <= x < fr + 2880) \/ (fr + 4088 <= x < fr + 4096) -> LFrame.outside WR x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> LFrame.outside WR x) ->
  w3_core cx fr R m'.
Proof.
  intros cx fr regs R m m' WR
    (HFRAC & HOUR & HCUR & HPRO & S144 & A2691 & S192 & Afrag & A2688 & HIDB & HFGB & HXC & A2880)
    K2 K3 K4 K8 K9 K19 K22 K25 K26 HM Hfapp Osp Osh Ofr Oin.
  pose proof HFRAC as (A & sp & F2 & _ & FspZ & _ & _ & F9 & _ & _ & _ & Ffr32 & _ & FAc & FspA & _ & _ & _ &
    Fapp & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- FspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (CK11.getr regs 2)) as Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
    lia. }
  assert (HAb : 0 <= A /\ A + 400 <= 2 ^ 64) by (unfold A.AsanRT.APPMEM_END in Fapp; lia).
  assert (Hsp : forall off v, A.ACtlCutP.spill regs m off v -> 0 <= off <= 304 -> A.ACtlCutP.spill R m' off v).
  { intros off v Hs Hoff. apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs R m m' off v A Hs F9); [lia | lia | lia | exact HM | exact K9 |].
    intros x Hx. apply Osp. rewrite FspZ. lia. }
  assert (Hby : forall a bs, LMem.bytes_at A.Img0.rsegs m a bs ->
                  (forall x, a <= x < a + Z.of_nat (length bs) -> fr <= x < fr + 2880) ->
                  LMem.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Hr. apply (A.ACtlG.KitMem.kitmem_bytes_munch WR m m' a bs Hb HM). intros x Hx. apply Ofr. left. apply Hr, Hx. }
  assert (Had : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H. exact (A.ACtlG.KitMem.kitmem_addr_munch WR m m' p n H HM Osh). }
  split.
  { (* FRAC: memory by KitMem.kitmem_frac_munch, registers by Kit.kit_frac_move *)
    refine (A.ACtlG.Kit.kit_frac_move B cx fr fr regs R m' _ K2 K3 K4 K8 K9 K19 K26).
    apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs m m' WR HFRAC HM Osp).
    - intros x [Hx | Hx]; apply Ofr; [left | right]; lia.
    - intros x Hx. apply Osh.
      change A.ACtlCutP.FRAME_SHADOW with 392 in Hx. unfold A.ACtlCutP.Sfr in Hx.
      set (i := x - A.AsanRT.shadow_addr fr).
      assert (Ex : x = A.AsanRT.shadow_addr (fr + 8 * i)).
      { unfold i. unfold A.AsanRT.shadow_addr in *.
        replace (fr + 8 * (x - (fr / 8 + A.AsanRT.ASAN_K))) with ((x - (fr / 8 + A.AsanRT.ASAN_K)) * 8 + fr) by lia.
        rewrite Z.div_add_l by lia. lia. }
      rewrite Ex. apply A.AsanRTFacts.shadow_of_app. apply Hfapp. unfold i. lia. }
  split.
  { (* OURb: 6 bytes at fr + 2624 *)
    unfold A.ACtlCutP.OURb in *. apply (Hby _ _ HOUR).
    assert (E : length (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat) by reflexivity.
    rewrite E. intros x Hx. lia. }
  split.
  { (* CUR: registers 22 and 25 *)
    unfold A.ACtlCutP.CUR in *. destruct HCUR as (Hc & H22 & H25).
    exact (conj Hc (conj (eq_trans K22 H22) (eq_trans K25 H25))). }
  split.
  { (* PRO *)
    unfold A.ACtlCutP.PRO in *.
    destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 &
      P264 & P272 & P32).
    split; [exact (Hsp _ _ P40 ltac:(lia))|]. split; [exact (Hsp _ _ P120 ltac:(lia))|].
    split; [exact (Hsp _ _ P136 ltac:(lia))|]. split; [exact (Hsp _ _ P160 ltac:(lia))|].
    split; [exact (Hsp _ _ P168 ltac:(lia))|]. split; [exact (Hsp _ _ P176 ltac:(lia))|].
    split; [exact (Hsp _ _ P208 ltac:(lia))|]. split; [exact (Hsp _ _ P248 ltac:(lia))|].
    split; [exact (Had _ _ Pad)|].
    split; [exact (A.ACtlG.KitMem.kitmem_bytes_munch WR m m' _ _ Pin HM Oin)|].
    split; [intros Hn; exact (Had _ _ (Pg Hn))|].
    split; [exact (Hsp _ _ P184 ltac:(lia))|]. split; [exact (Hsp _ _ P256 ltac:(lia))|].
    split; [exact (Hsp _ _ P264 ltac:(lia))|]. split; [exact (Hsp _ _ P272 ltac:(lia))|].
    exact (Hsp _ _ P32 ltac:(lia)). }
  split; [exact (Hsp _ _ S144 ltac:(lia))|].
  split; [exact (Had _ _ A2691)|].
  split; [exact (Hsp _ _ S192 ltac:(lia))|].
  split; [exact (Had _ _ Afrag)|].
  split; [exact (Had _ _ A2688)|].
  split.
  { (* IDBe: 38 bytes at fr + 2688 *)
    unfold A.ACtlCutP.IDBe in *. apply (Hby _ _ HIDB).
    assert (E : length Prog.RcIdentModel.ID0 = 38%nat) by reflexivity.
    rewrite E. intros x Hx. lia. }
  split.
  { (* FGBe: 72 bytes at fr + 2768 *)
    unfold A.ACtlCutP.FGBe in *. apply (Hby _ _ HFGB).
    assert (E : length A.Prog.SlotModel.z72 = 72%nat) by reflexivity.
    rewrite E. intros x Hx. lia. }
  split.
  { (* XC: the spill [s1 + 280] through register 9, the byte's shadow *)
    unfold A.ACtlCutP.XC in *. destruct HXC as (HXq & HXa). split; [|exact (Had _ _ HXa)].
    intros A' HA' HA'r.
    assert (HA'9 : ACtlCut.rgv regs 9 A') by exact (eq_trans (eq_sym K9) HA').
    assert (EA : A' = A).
    { unfold ACtlCut.rgv in HA'9, F9. rewrite F9 in HA'9.
      pose proof (f_equal bv_unsigned HA'9) as E.
      rewrite (LMState.unsigned_lit A) in E by lia. rewrite (LMState.unsigned_lit A') in E by lia.
      lia. }
    subst A'.
    apply (A.ACtlG.KitMem.kitmem_bytes_munch WR m m' _ _ (HXq A HA'9 HA'r) HM).
    intros x Hx. apply Osp. rewrite FspZ. lia. }
  exact (Had _ _ A2880).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P8 : forall POST, CF POST C_A81c34 -> CF POST C_A81c20.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81c20 (ACtlCutP.v:1878-1889). *)
  cbv beta iota zeta delta [ACtlCut.cut_body A.ACtlCutP.C_A81c20] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 & A2691 & S192 & Afrag & A2688 & HIDB & HFGB &
    R10 & R18 & HXC & A2880).
  (* G2: the bounds from visible state. *)
  destruct (w3_bounds cx fr k ly3 S3 W3 mem3 md3 HB HJ HF HL HP)
    as (Efr3 & Hfr4096 & Hfrceil & Hframe & Hfsh & Hceilstk & Hsp47 & Hinput).
  pose proof HFRAC as (A & sp & F2 & _ & FspZ & _ & _ & _ & _ & _ & _ & _ & _ & FAc & FspA & _ & _ & Fsplo &
    Fapp & _).
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hac0 _] _].
  assert (Esp : bv_unsigned (CK11.getr regs3 2) = sp) by exact FspZ.
  assert (Hstk : LFrame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_journal B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) sp HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  assert (Hvis : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { pose proof (A.ProgWorldVisWin.win_vis B) as WV.
    unfold A.ProgWorld.win_vis_stmt in WV.
    apply (WV A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK in *; lia. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81c20) with 0x81c20.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81c20) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4: the run (its callee contract by the proved reac_ports_parse_F_holds) and the lift. *)
  pose proof (A.Prog.Seg.P8F.p8_evt_F A.Prog.reac_ports_parseF.reac_ports_parse_F_holds
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5) (CK11.getr regs3 6)
    (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12)
    (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17)
    (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
    (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
    (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 (sp - 16) R10 R18
    ltac:(rewrite Esp; exact Hstk)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; lia)
    ltac:(rewrite Esp; unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME;
          exact (A.ProgBridge.rng_of_visible _ _ _ Hvis))) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) (w3_fevt_run _ _ _ _ HFS)).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the continuation, at the run's end state. *)
  intros ms' md' [Hrun HQ] Hsbm.
  destruct HQ as (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & HMU & HWM & HST').
  subst ms'.
  rewrite Esp in HMU. unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME in HMU.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81c34) RX m' md') (POST cx)).
  assert (K2 : CK11.getr RX 2 = CK11.getr regs3 2) by reflexivity.
  assert (K3 : CK11.getr RX 3 = CK11.getr regs3 3) by reflexivity.
  assert (K4 : CK11.getr RX 4 = CK11.getr regs3 4) by reflexivity.
  assert (K8 : CK11.getr RX 8 = CK11.getr regs3 8) by reflexivity.
  assert (K9 : CK11.getr RX 9 = CK11.getr regs3 9) by reflexivity.
  assert (K19 : CK11.getr RX 19 = CK11.getr regs3 19) by reflexivity.
  assert (K22 : CK11.getr RX 22 = CK11.getr regs3 22) by reflexivity.
  assert (K25 : CK11.getr RX 25 = CK11.getr regs3 25) by reflexivity.
  assert (K26 : CK11.getr RX 26 = CK11.getr regs3 26) by reflexivity.
  assert (K10 : CK11.getr RX 10 = Z_to_bv 64 (-1)) by reflexivity.
  (* what the window [sp - 16, sp) leaves alone *)
  assert (Hlow : A.AsanRT.HIGHMEM_BEG <= sp - 16)
    by (unfold A.AsanRT.HIGHMEM_BEG, A.ACfn.LLVMF_STK in *; lia).
  assert (Osp : forall x, Reusable.YG0d.spZ regs3 <= x -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. rewrite FspZ in Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
  assert (Osh : forall x, A.AsanRT.in_shadow x -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. cbn [LFrame.outside]. split; [|exact I].
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hx, Hlow. lia. }
  assert (Ofr : forall x, (fr <= x < fr + 2880) \/ (fr + 4088 <= x < fr + 4096) -> LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. assert (Hx' : fr <= x < fr + 4096) by (destruct Hx; lia). cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  assert (Oin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  LFrame.outside [(sp - 16, sp)] x).
  { intros x Hx. destruct (Hinput x Hx) as [Hx1 _]. cbn [LFrame.outside].
    split; [unfold A.ACfn.LLVMF_STK in *; lia | exact I]. }
  refine (HX cx idx fr k ly3 S3 W3 RX m' md' HB _ HF HL Hk _ _).
  - (* the journal across the run: ProgWorld.ajournal_of_fsteps, the window is awr_byte's stack case *)
    match type of Hrun with Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _ _
                HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) HMU Hsbm _) end.
    intros a _ Hno. apply w3_not_outside1 in Hno.
    unfold Reusable.YCbq.awr_byte. left. unfold A.ACfn.LLVMF_STK in *. lia.
  - (* the exit body C_A81c34 (ACtlCutP.v:1893-1904) *)
    cbv beta iota delta [ACtlCut.cut_body A.ACtlCutP.C_A81c34].
    destruct (w3_core_keep cx fr regs3 RX mem3 m' [(sp - 16, sp)]
                (conj HFRAC (conj HOUR (conj HCUR (conj HPRO (conj S144 (conj A2691 (conj S192 (conj Afrag
                  (conj A2688 (conj HIDB (conj HFGB (conj HXC A2880))))))))))))
                K2 K3 K4 K8 K9 K19 K22 K25 K26 HMU (fun i Hi => proj1 (Hframe i Hi)) Osp Osh Ofr Oin)
      as (HFRAC' & HOUR' & HCUR' & HPRO' & S144' & A2691' & S192' & Afrag' & A2688' & HIDB' & HFGB' & HXC' &
          A2880').
    exact (conj HP (conj HFRAC' (conj Hn (conj HOUR' (conj HCUR' (conj HPRO' (conj S144' (conj A2691'
      (conj S192' (conj Afrag' (conj A2688' (conj HIDB' (conj HFGB' (conj K10 (conj HXC' A2880'))))))))))))))).
  - (* ctl_rt_C: the window is high application memory, no image byte; the state's regions are kept *)
    apply (w3_ctlrtC_munch B ly3 S3 [(sp - 16, sp)] mem3 m' Hrt HMU).
    intros x Hx. apply w3_not_outside1 in Hx. split.
    + unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia.
    + intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi) as Hl.
      unfold Reusable.YG0f.kLowMemEnd, A.AsanRT.HIGHMEM_BEG in *. lia.
Qed.

End GlueP8.

Print Assumptions glue_seg_P8.
