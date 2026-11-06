(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v, with its module paths and module names changed; 624 of its 667 lines of code are new or changed and 802 lines of the source are left out. *)
(* lib/A/ACtlG/R9.v -- GLUE for stage seg_R9 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:680).
   Written by a Theorem Labs lane (piece W2a); single writer.  rule 24: no function proved (stage
   glue of a walk; proves no function, kind: segment lemma).  Pattern: (internal path)
   glue-pattern.md (a working note, not in this delivery); piece brief glue-w2a-brief.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_R9 : forall POST (b : nat),
       CF POST (ix_cut C_A81680_at [Z.of_nat b]) -> CF POST (ix_cut C_A81658_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Hypothesis seg_R9.
   Segment R9 (Seg/R9.v seg_R9 :2240) is 0x81658 -> 0x81680 of turn b of the W2 round trip:
     0x81658-0x8166c  r9_st:   four `sb zero` and `li s11,4; sb s11` mark the 36-byte record o = fr + 2368 of the
                               class-6 fake frame addressable (frame-shadow bytes S(fr)+296..300 := 0,0,0,0,4);
     0x81670-0x8167c  r9_call: mv a0,s8 ; mv a1,s2 ; ld a2,56(s1) ; jal reac_ctrl_parse  (f = phi, n = rnb, o);
     the call returns to 0x81680, the exit cut.

   THE PROOF (glue-pattern.md G1-G5, with the split rule (a) at the cgif-form callee reac_ctrl_parse)
   G1  the entry cut C_A81658_at (ACtlCutP.v:1352-1370) at index [b]: its FRAC, its 23 middle conjuncts, RF, RXS.
   G2  bounds from VISIBLE state: the class-6 frame (frames_bounds, the frame law, layout_le's ly_F), FRAC's spill
       base A and sp, the journal's astk_ok and YCbq.asan_consts, the live block (phi, rnb) of the journal's AR
       (al_blocks) through the body's Permutation; visibility from the AR laws (al_frames, al_blocks) and
       ProgWorldVisWin.win_vis.
   G3  the walk moved to the canonical map mkR_of regs3 (YA0nR.SRr_xregs_eqv); s3 := S(fr) by FRAC.
   G4  stretch 1: a Theorem Labs lane's Seg/R9F.r9_st_F at RNG_W (w_H W3) (the five frame-shadow bytes, visible by
       al_frames), lifted by KitMem.kitmem_lift; its journal by ProgWorld.ajournal_of_fsteps (the five bytes are
       awr_byte's in_frames shadow case of the owned class-6 frame).
       stretch 2: Seg/R9Fs.r9_call_pre_Fs (this lane's split, 0x81670 -> reac_ctrl_parse's entry 0x83578 with
       ra = 0x81680) at RNG_W (w_H W3) (the spill cell [A+56], win_vis), lifted the same way; its journal by
       ajournal_of_fsteps with the empty write set.
       the call: a Theorem Labs lane's treac_ctrl_parse_spec (Section hypothesis TPARSE, cited by name from
       lib/A/Prog/C_reac_ctrl_parse.v) through YA0n.SRr_bind, with its caller obligations P1-P13
       (spec-draft.md section 4 (a working note, not in this delivery)): P1 the journal; P2 the read-only
       view, kept from ctl_base by KitMem.kitmem_arodataS_journal; P3 ra = 0x81680; P4 gp / tp by FRAC and the
       pre; P5 a0 = phi (RF), a1 = rnb (RF), a2 = o = fr + 2368 (RXS's spill 56); P7 FRAC's sp; P8 frames = own6
       (no class-1 frame); P9 the block (phi, rnb), rnb >= 124; P10 afobj: o in the class-6 frame, and the 36 bytes
       addressable through the five shadow bytes r9_st wrote (r9g_raddr); P11 awr_byte's in_frames case; P12
       length (rt_g ..) = 50; P13 the 50 frame bytes of the block, from RF's bytes_at phi (rt_F ..).
   G5  the spec's post at the return pc 0x81680 = the exit cut C_A81680_at (ACtlCutP.v:1375-1393): the journal is
       the post's; frames / ablocks unchanged; registers by aregs_preserved (a0 = rt_k by the post, s11 = 4 by
       r9_st); every memory conjunct of the body through ProgWorld.ctl_post_acall_kept (spill area and saved
       registers above alloc_ceiling and above the callee window; the class-6 frame except [o, o+36) and its shadow;
       the live blocks) composed with r9_st's munch; the block-shadow conjuncts (HB, PRO's input block) from the
       post's AR (A.ProgWorldShadow.ctl_block_shadow_of_AR, PROVED); FRAC by r9g_frac_move with the new frame-shadow list
      (R9.r9_shnew); ctl_rt_C by ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED) at the post's AR (route (C)).

   FRAC IS RE-ESTABLISHED at a new memory in ONE place: lemma r9g_frac_move (used once, at the exit).  It walks
   FRAC's conjuncts generically (decompose + one transport tactic per conjunct shape), so the announced trailer
   q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) is carried by the same frame-keep fact: [fr + 4088, fr + 4096)
   is inside the kept class-6 frame and outside the parse output [o, o + 36).

   SECTION HYPOTHESES (exact text below)
   - RELRO_IMG, LAWS, TFIB_SYMS: ACtl.v's own Section hypotheses (ACtl.v:179, :183, :191), same text.
   - TPARSE: ACtl.v's own (ACtl.v:315, same text): a Theorem Labs lane's callee spec treac_ctrl_parse_spec
     (lib/A/Prog/C_reac_ctrl_parse.v:63), the split rule's cgif-form callee contract.
   - Route (C): AR_VIS0 / AR_OWNED_RO are gone (the exit's ctl_rt_C is ProgWorldCtlRtC.ctl_rt_C_of_AR); the one
     frame-shadow read is cut_shadow's (F) disjunct of the owned class-6 frame.
   - (no longer a hypothesis) CTL_BLOCK_SHADOW is a Theorem Labs lane's PROVED A.ProgWorldShadow.ctl_block_shadow_of_AR B,
     named locally by a Let: the heap block's shadow after the callee, which acall_kept does not keep.
   CITED BY NAME: Seg/R9F.r9_st_F, Seg/R9Fs.r9_call_pre_Fs, R9.r9_spill_at / r9_shnew / r9_rtn / r9_RS_len /
   r9_rd8 (Seg/R9.v, proof-internal), ProgBridge, YA0nR, YA0n.SRr_bind, ProgWorld.ajournal_of_fsteps /
   ctl_post_acall_kept / aview_vis_mrd / arodata_okP_of_S, ProgWorldCtlRtC.ctl_rt_C_of_AR, ProgWorldVisWin.win_vis,
   KitMem (kitmem_lift, kitmem_arodataS_journal, kitmem_bytes_at_mrd, kitmem_addressable_mrd, kitmem_rw_cells_mrd),
   Kit (kit_wx, kit_frac_move), YCbq (frames_bounds, sep_block_frame, asan_consts), YG0d (al_frames, al_blocks).

   STAND-IN VALUES: only through ctl_rt_C_of_AR's Tfib_const_abs rows; each checked against the record AF0m
   (a working branch e56483f863b): same address, width and value.  No ts_zsh.  as_gp B is
   passed through symbolically (P4), never read as a value.

   CLOSURE: every Require is qualified; the six twin modules and lib/Lib are named by absolute path; no statement
   names a frame-route identifier (Seg / SlotInv names appear only inside proofs).  Measured (w2a-closure.py):
   420 files, 22 frame-route files (blobs in the commit message), 0 forbidden (no AsanW, no W6, no cut-free file).
   SHADOWED NAMES: getr / seg_rom / cfg_at are OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 /
   Reusable.YG0d-qualified.

   BUILD STATE (honest): TYPE-CHECKS, rc=0, a build machine workspace (internal path) (the log of the
   build of this text before comment-only edits is named in its commit message), with wb-w2a.sh's workspace-only port_core_refused_<hex>
   substitution in A/AE2k AF0m AF0l ACej ACeh (TYPES ONLY, values do not count); no AD2l stand-in.  Print
   Assumptions glue_seg_R9: the Rocq primitives (PrimInt63 / PrimString / PrimArray) and
   functional_extensionality_dep, nothing else.  No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YE01 Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0v.
(* YK0s exists as lib/{,A/,B/,U/}Reusable/YK0s.v: the core's copy, by absolute name (gate finding a Theorem Labs lane 07:36Z) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRt A.ProgWorldVisWin A.ProgWorldShadow.
(* route (C): the narrowed cut conjunct and its producer from AR (no VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.CtrlBase A.Prog.C_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R9 A.Prog.Seg.R9F A.Prog.Seg.R9Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

Module Y11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module YM5 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module YO9 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RPA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module R9S := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R9.
Module R9F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R9F.
Module R9Fs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R9Fs.
Module PRS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parse.
Module KM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Stage-local facts (no Section argument). *)

Lemma r9g_len_le8 : forall w : word, length (LM.le8 w) = 8%nat.
Proof. intros w. apply LM.length_le8. Qed.

(* The first 50 bytes of a frame of at least 50 bytes are its fr50 (SlotModel.fr50 = firstn 50 (bs ++ zeros)). *)
Lemma r9g_nth_fr50 : forall (bs : list byte) (i : nat) d, (i < 50)%nat -> (i < length bs)%nat ->
  nth i (SM.fr50 bs) d = nth i bs d.
Proof.
  intros bs i d Hi Hl. unfold SM.fr50.
  rewrite nth_firstn. destruct (Nat.ltb_spec i 50) as [_|C]; [|lia].
  rewrite app_nth1 by exact Hl. reflexivity.
Qed.

(* The 36 bytes of o = fr + 2368 are addressable in the core's shadow view once the five frame-shadow bytes
   S(fr) + 296 .. S(fr) + 300 read 0, 0, 0, 0, 4 and are visible (P10 of treac_ctrl_parse_spec). *)
Lemma r9g_raddr : forall {fx : Y11.FPState} (W : Reusable.YA0n.world segs) (m : word -> option byte) (fr : Z),
  0 <= fr -> fr mod 32 = 0 ->
  (forall j, 0 <= j < 5 -> Reusable.YA0n.w_H W (Z_to_bv 64 (ACtlCutP.Sfr fr + 296 + j)) = false) ->
  LM.bytes_at A.Img0.rsegs m (ACtlCutP.Sfr fr + 296)
    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m)
    Reusable.YG0f.SHADOW_OFF (fr + 2368) 36.
Proof.
  intros fx W m fr H0 H32 Hvis Hb x Hx.
  set (j := (x - (fr + 2368)) / 8).
  assert (Hj : 0 <= j < 5) by (unfold j; Z.div_mod_to_equations; lia).
  assert (Es : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = ACtlCutP.Sfr fr + 296 + j).
  { unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, j.
    Z.div_mod_to_equations. lia. }
  rewrite Es, (A.ProgWorld.aview_vis_mrd W m _ (Hvis j Hj)).
  destruct Hb as (_ & _ & Hb).
  assert (Hjc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
  destruct Hjc as [Ej|[Ej|[Ej|[Ej|Ej]]]]; rewrite Ej.
  - pose proof (Hb 0%nat ltac:(cbn; lia)) as Hn. cbn [nth_error Z.of_nat] in Hn.
    rewrite Z.add_0_r in Hn. unfold LM.wa in Hn. rewrite Z.add_0_r, Hn.
    eexists; split; [reflexivity | left; reflexivity].
  - pose proof (Hb 1%nat ltac:(cbn; lia)) as Hn. cbn [nth_error] in Hn. change (Z.of_nat 1) with 1 in Hn.
    unfold LM.wa in Hn. rewrite Hn.
    eexists; split; [reflexivity | left; reflexivity].
  - pose proof (Hb 2%nat ltac:(cbn; lia)) as Hn. cbn [nth_error] in Hn. change (Z.of_nat 2) with 2 in Hn.
    unfold LM.wa in Hn. rewrite Hn.
    eexists; split; [reflexivity | left; reflexivity].
  - pose proof (Hb 3%nat ltac:(cbn; lia)) as Hn. cbn [nth_error] in Hn. change (Z.of_nat 3) with 3 in Hn.
    unfold LM.wa in Hn. rewrite Hn.
    eexists; split; [reflexivity | left; reflexivity].
  - pose proof (Hb 4%nat ltac:(cbn; lia)) as Hn. cbn [nth_error] in Hn. change (Z.of_nat 4) with 4 in Hn.
    unfold LM.wa in Hn. rewrite Hn.
    eexists; split; [reflexivity|]. right. change (bv_unsigned (Z_to_bv 8 4)) with 4.
    unfold j in Ej. Z.div_mod_to_equations. lia.
Qed.

(* A spill cell moves to a new register map that keeps s1 and to a new memory that keeps its eight bytes. *)
Lemma r9g_spill_mv : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (A off v : Z),
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= ART.APPMEM_END ->
  0 <= off <= 408 ->
  Y11.getr regs' 9 = Y11.getr regs 9 ->
  (forall i, 0 <= i < 8 -> LM.mrd A.Img0.rsegs m' (LM.wa (A + off + i)) = LM.mrd A.Img0.rsegs m (LM.wa (A + off + i))) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hs HA HA0 HA1 Hoff E9 K.
  pose proof (R9S.r9_spill_at regs A off v m Hs HA HA0 HA1 Hoff) as Hq.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  unfold ACtlCutP.q64. apply (KM.kitmem_bytes_at_mrd m m' (A + off) _ Hq).
  intros i Hi. rewrite r9g_len_le8 in Hi. apply K. lia.
Qed.

Section GlueR9.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : Y11.FPState} {rc : YM5.RunCeil} {LS : YO9.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :236-237), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81658_at := (ACtlCutP.C_A81658_at B).
Local Notation C_A81680_at := (ACtlCutP.C_A81680_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* ACtl.v:179, :183, :191, same text. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* a Theorem Labs lane's cgif-form spec of reac_ctrl_parse (C_reac_ctrl_parse.v:63), the split rule's callee contract. *)
Hypothesis TPARSE : A.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.

(* route (C): AR_VIS0 / AR_OWNED_RO (ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) are GONE: the exit's
   ctl_rt_C comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* ProgWorld.ctl_block_shadow_of_AR_stmt B (ProgWorld.v:849-855), unfolded: no longer a hypothesis, a Theorem Labs lane's PROVED
   A.ProgWorldShadow.ctl_block_shadow_of_AR (on the glue base since 29ddfc3ea99), named locally. *)
Let CTL_BLOCK_SHADOW : Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : Reusable.YA0n.world segs) (m : word -> option byte) md p n lo len,
    Reusable.YG0n.AR segs B ly S W m md ->
    In (p, n) (Reusable.YG0d.ablocks B ly S) ->
    p <= lo -> 0 <= len -> lo + len <= p + Reusable.YG00.req_size n ->
    A.AsanRT.addressable m lo len := A.ProgWorldShadow.ctl_block_shadow_of_AR B.

(* ---------------------------------------------------------------------------------------------------------
   FRAC at a new register map and a new memory (the one place this stage RE-ESTABLISHES FRAC).  The registers move
   by Kit.kit_frac_move; every memory conjunct is walked generically: a q64 / bytes_at conjunct of FRAC moves along
   the pointwise keep K (the spill area [A, A + 416), the frame outside the parse output, the saved registers),
   and the frame-shadow list is the given one.  So the announced trailer q64 m (fr + 4088) (flag_addr ..), inside
   [fr + 2404, fr + 4096), is carried by the same K. *)
Lemma r9g_frac_move : forall cx (fr sel : Z) (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  0 <= fr -> ACtlCutP.FRAC B cx fr sel regs m ->
  Y11.getr regs' 2 = Y11.getr regs 2 -> Y11.getr regs' 3 = Y11.getr regs 3 ->
  Y11.getr regs' 4 = Y11.getr regs 4 -> Y11.getr regs' 8 = Y11.getr regs 8 ->
  Y11.getr regs' 9 = Y11.getr regs 9 -> Y11.getr regs' 19 = Y11.getr regs 19 ->
  Y11.getr regs' 26 = Y11.getr regs 26 ->
  (forall A a, ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= ART.APPMEM_END -> 0 <= a < 2 ^ 64 ->
     (A <= a < A + 416 \/ fr <= a < fr + 2368 \/ fr + 2404 <= a < fr + 4096 \/
      ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx) ->
     LM.mrd A.Img0.rsegs m' (LM.wa a) = LM.mrd A.Img0.rsegs m (LM.wa a)) ->
  (exists sh, LM.bytes_at A.Img0.rsegs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel regs regs' m m' Hfr0 H E2 E3 E4 E8 E9 E19 E26 K HSH.
  pose proof (A.ACtlG.Kit.kit_frac_move B cx fr sel regs regs' m H E2 E3 E4 E8 E9 E19 E26) as H'.
  assert (Hlen8 : forall w : word, Z.of_nat (length (LM.le8 w)) = 8) by (intros w; rewrite r9g_len_le8; reflexivity).
  assert (Hsav : Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !r9g_len_le8. reflexivity. }
  destruct H as (A0 & sp0 & H0). destruct H' as (A & sp & H1).
  destruct H0 as (_ & _ & Hspz0 & _ & _ & HR90 & _ & _ & _ & _ & _ & HAS0 & HspA0 & HfrA0 & HA4160 & _ & HSapp0 & _).
  pose proof H1 as (_ & _ & Hspz & _ & _ & HR9 & _ & _ & _ & Hfrm & HAm & HAS & HspA & HfrA & HA416 & HSsp & HSapp & _).
  assert (Hsp0 : 0 <= sp) by (rewrite <- Hspz; apply R9S.r9_word_range).
  assert (KA : forall a, 0 <= a < 2 ^ 64 ->
     (A <= a < A + 416 \/ fr <= a < fr + 2368 \/ fr + 2404 <= a < fr + 4096 \/
      ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx) ->
     LM.mrd A.Img0.rsegs m' (LM.wa a) = LM.mrd A.Img0.rsegs m (LM.wa a)).
  { intros a Ha Hr. apply (K A a); [| lia | unfold ACtlCutP.FRAME_BYTES, ART.APPMEM_END in *; lia | exact Ha | exact Hr].
    unfold ACtlCut.rgv in *. rewrite <- E9. exact HR9. }
  clear K HR90 HAS0 HspA0 HfrA0 HA4160 HSapp0 Hspz0.
  unfold ACtlCutP.FRAC, ACtlCutP.FRAME_BYTES, ART.APPMEM_END in *.
  decompose [and ex] H1.
  (* every byte conjunct of FRAC (the q64 cells, the saved registers, and any appended q64) moves along KA *)
  repeat match goal with
  | Hq : ACtlCutP.q64 m ?a ?v |- _ =>
      let H' := fresh "Hq'" in
      assert (H' : ACtlCutP.q64 m' a v)
        by (unfold ACtlCutP.q64 in *; apply (KM.kitmem_bytes_at_mrd m m' a _ Hq);
            intros i Hi; rewrite Hlen8 in Hi; apply KA; lia);
      clear Hq
  | Hq : ACtlCutP.MEM.bytes_at segs m (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx) |- _ =>
      let H' := fresh "Hs'" in
      assert (H' : ACtlCutP.MEM.bytes_at segs m' (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx))
        by (apply (KM.kitmem_bytes_at_mrd m m' _ _ Hq); intros i Hi; rewrite Hsav in Hi; apply KA; lia);
      clear Hq
  end.
  exists A, sp.
  repeat match goal with |- _ /\ _ => split end.
  all: first [assumption | exact HSH].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R9 : forall POST (b : nat), CF POST (ix_cut C_A81680_at [Z.of_nat b]) -> CF POST (ix_cut C_A81658_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBASE HJ HF HL Hk Hbody Hrt.
  (* ===== G1: the entry cut at index [b] (ix_cut, ACtlCut.v:232-234; C_A81658_at, ACtlCutP.v:1352-1370) ===== *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81658_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & (Hn26 & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO &
    S104 & S96 & S64 & S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 & S152 & R21 & HA2176) & HRF & HRXS).
  change (ACtlCut.cut_own (ix_cut C_A81658_at [Z.of_nat b]) cx) with (ACtlCut.own6 cx) in HJ, HF, HL.
  (* ===== G2: facts from the shell, the base and the body ===== *)
  pose proof HBASE as ((HPRE & _ & _ & _ & Hinp & Hlen & _ & _ & _ & _ & HROS & _) & _).
  pose proof HPRE as (_ & _ & _ & Hgp & _).
  pose proof HJ as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & _).
  unfold A.ACfn.LLVMF_STK in Hstklo.
  pose proof Reusable.YCbq.asan_consts as (Hac & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr in *; lia).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfpres & Hfshpres).
  rewrite Efa in Hf4096, Hfceil, Hfapp, Hfpres, Hfshpres.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp, Hfpres, Hfshpres.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfapp.
  (* FRAC (ACtlCutP.v:982-996); its last component (the saved registers, and the announced trailer) unnamed *)
  pose proof HFRAC as (A & sp & HR2 & Hspm & Hspz & HR4 & HR8 & HR9 & HR3 & HR19 & HR26 & Hfrm & HAm & HAS &
    HspA & HfrA & HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & Qh0 & Qh16 & (sh & Hsh & Hshl) & _).
  unfold ACtlCutP.FRAME_BYTES, ART.APPMEM_END in HfrA, HSapp.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Hspz; apply R9S.r9_word_range).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* the body's RF (ACtlCutP.v:514) and RXS (:518) *)
  pose proof HRF as (((Hb6r & HCURr & HOURr & R23r & HIDBr & HFGBr) & Hnz & R24 & Hphib) & R18).
  pose proof HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & HA2256).
  pose proof HCUR as (Hc7 & R22 & R25).
  (* the model: rnb is 124 .. 1492 and the frame F_b has rnb bytes (Seg/R9.v r9_rtn) *)
  destruct (R9S.r9_rtn (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (Hrng & HFl).
  assert (Hrnb : 124 <= ACtlCutP.rnb cx b <= 1492) by (unfold ACtlCutP.rnb; lia).
  assert (LRTF : Z.of_nat (length (SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b))) = ACtlCutP.rnb cx b)
    by (rewrite HFl; unfold ACtlCutP.rnb; lia).
  destruct (R9S.r9_RS_len (ACtlCut.c_in cx) b) as (LRID & LRFG).
  assert (LOUR : length (SM.OUR (ACtlCut.c_in cx)) = 6%nat)
    by (unfold SM.OUR; rewrite length_map, length_seq; reflexivity).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.rnb cx b) 0); lia).
  assert (Hbs50 : length (SM.rt_g (ACtlCut.c_in cx) (Z.of_nat b)) = 50%nat)
    by (unfold SM.rt_g; apply SM.fr50_length).
  (* the live block (phi, rnb) of the journal's AR (the body's Permutation) *)
  assert (Hphi_in : In (phi, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) HAR Hphi_in)
    as (_ & Hphi4096 & Hphiceil & Hphiapp & Hphipres & _ & _).
  rewrite Hreq in Hphiceil, Hphiapp, Hphipres.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hphiapp.
  (* every live block lies in application memory below the allocator ceiling, apart from the class-6 frame *)
  assert (Hblk : forall p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
            4096 <= p /\ p + Reusable.YG00.req_size n <= YM5.alloc_ceiling /\
            (p + Reusable.YG00.req_size n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\
            (forall a, p <= a < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false) /\
            (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p)).
  { intros p n Hpn.
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn)
      as (_ & H4 & Hc & Hap & Hpr & _ & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hpn Hin6)
      as Hsep.
    rewrite Efa in Hsep. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
      in Hap.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
    split; [exact H4|]. split; [exact Hc|]. split; [lia|]. split; [|lia].
    intros a Ha. exact (proj1 (proj1 (Hpr a Ha))). }
  (* the input block (c_p, c_n) of the pre is a live block of the journal's AR when c_n > 0 *)
  assert (Hinp_in : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn0. destruct Hinp as [(E0 & _) | (_ & Hin0)]; [lia|].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hin0. }
  (* visibility at W3: the class-6 frame and its shadow (al_frames), the journal's window (win_vis) *)
  assert (Vfr : forall a, fr <= a < fr + 4096 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (proj1 (Hfpres a Ha)))).
  assert (Vsh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha.
    assert (Ei : a = Reusable.YG0f.shadow_addr fr + (a - ACtlCutP.Sfr fr))
      by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; lia).
    rewrite Ei. exact (proj1 (proj1 (Hfshpres (a - ACtlCutP.Sfr fr) ltac:(lia)))). }
  (* win_vis states the record text A.ProgWorld.win_vis_stmt B (ProgWorldVisWin.v re-pointed 05:4xZ), whose journal
     is over ProgWorld's fixed sink head A.AE2k.tfib_sink_head, so it takes no SK argument any more. *)
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (Vwin : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha.
    destruct (WV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 1 HJ ltac:(unfold A.ACfn.LLVMF_STK; lia)
                ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & _ & Hv).
    exact (Hv a ltac:(lia)). }
  (* ctl_rt at the entry *)
  destruct Hrt as (Hcells & Hcut & Himg & Hroag).
  (* the canonical map's s3 and s1, as getr facts *)
  assert (G19 : Y11.getr regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact HR19.
  assert (G9 : Y11.getr regs3 9 = Z_to_bv 64 A) by exact HR9.
  (* ===== G3: the cut's configuration in the run's state form, moved to the canonical map ===== *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81658_at [Z.of_nat b])) with 0x81658.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 Y11.fp_regs
           (Z_to_bv 64 0x81658) Y11.fp_csr None mem3 (Y11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  replace (LR6.mkR_of regs3) with
    (LF.mkR (Y11.getr regs3 1) (Y11.getr regs3 2) (Y11.getr regs3 3) (Y11.getr regs3 4) (Y11.getr regs3 5)
            (Y11.getr regs3 6) (Y11.getr regs3 7) (Y11.getr regs3 8) (Y11.getr regs3 9) (Y11.getr regs3 10)
            (Y11.getr regs3 11) (Y11.getr regs3 12) (Y11.getr regs3 13) (Y11.getr regs3 14) (Y11.getr regs3 15)
            (Y11.getr regs3 16) (Y11.getr regs3 17) (Y11.getr regs3 18) (Z_to_bv 64 (ACtlCutP.Sfr fr))
            (Y11.getr regs3 20) (Y11.getr regs3 21) (Y11.getr regs3 22) (Y11.getr regs3 23) (Y11.getr regs3 24)
            (Y11.getr regs3 25) (Y11.getr regs3 26) (Y11.getr regs3 27) (Y11.getr regs3 28) (Y11.getr regs3 29)
            (Y11.getr regs3 30) (Y11.getr regs3 31))
    by (rewrite <- G19; reflexivity).
  (* ===== G4, stretch 1: r9_st (Seg/R9F.v:62), the five frame-shadow stores ===== *)
  assert (HS0 : 0 <= ACtlCutP.Sfr fr) by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
  assert (HS1 : ACtlCutP.Sfr fr + 301 <= 2 ^ 64)
    by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
  assert (Happ : forall x, fr <= x < fr + 4096 -> ART.app_mem x)
    by (intros x Hx; unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END; lia).
  assert (Wsh : LM.wr_at A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 296) 5).
  { split; [lia|]. split; [lia|]. intros i Hi.
    assert (Ei : ACtlCutP.Sfr fr + 296 + i = ART.shadow_addr (fr + 2368 + 8 * i))
      by (unfold ACtlCutP.Sfr, ART.shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Ei.
    (* route (C): the shadow of a byte of the owned class-6 frame is in cut_shadow's (F) disjunct *)
    assert (HF6 : A.ACtlRtC.cut_shadow B ly3 S3 (ART.shadow_addr (fr + 2368 + 8 * i))).
    { left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K.
      Z.div_mod_to_equations; lia. }
    exact (proj1 (Hcut _ HF6 (A.AsanRTFacts.shadow_of_app _ (Happ (fr + 2368 + 8 * i) ltac:(lia))))). }
  assert (Rsh : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 296) 5).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply Vsh. lia. }
  pose proof (R9F.r9_st_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                (Y11.getr regs3 1) (Y11.getr regs3 2) (Y11.getr regs3 3) (Y11.getr regs3 4) (Y11.getr regs3 5)
                (Y11.getr regs3 6) (Y11.getr regs3 7) (Y11.getr regs3 8) (Y11.getr regs3 9) (Y11.getr regs3 10)
                (Y11.getr regs3 11) (Y11.getr regs3 12) (Y11.getr regs3 13) (Y11.getr regs3 14) (Y11.getr regs3 15)
                (Y11.getr regs3 16) (Y11.getr regs3 17) (Y11.getr regs3 18) (Y11.getr regs3 20) (Y11.getr regs3 21)
                (Y11.getr regs3 22) (Y11.getr regs3 23) (Y11.getr regs3 24) (Y11.getr regs3 25) (Y11.getr regs3 26)
                (Y11.getr regs3 27) (Y11.getr regs3 28) (Y11.getr regs3 29) (Y11.getr regs3 30) (Y11.getr regs3 31)
                Y11.fp_regs Y11.fp_csr mem3 fr HS0 HS1 Wsh Rsh) as HRUN1.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HRUN1.
  apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HRUN1 (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms1 md1 Hrun1 HP1 Hsbm1.
  destruct HP1 as (m2 & Ems1 & MU1 & _ & _ & SH1). subst ms1.
  change (A.Prog.SlotInv.Sfr fr) with (ACtlCutP.Sfr fr) in SH1.
  (* the journal across stretch 1 (ProgWorld.ajournal_of_fsteps): the five bytes are the owned frame's shadow *)
  assert (HJ1 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m2 md1 k).
  { refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (R9S.r9_Wsh fr) _ Hrun1 (A.ProgBridge.fp_avoids_RNG_W _) MU1 Hsbm1 _); [exact HJ|].
    intros a Ha Hno.
    assert (Hr : ACtlCutP.Sfr fr + 296 <= a < ACtlCutP.Sfr fr + 301).
    { destruct (KM.kitmem_not_outside _ _ Hno) as (lo & hi & Hin & Hr).
      unfold R9S.r9_Wsh in Hin. destruct Hin as [E|[]]. injection E as E1 E2. subst lo hi.
      change (A.Prog.SlotInv.Sfr fr) with (ACtlCutP.Sfr fr) in Hr. exact Hr. }
    right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *. lia. }
  (* stretch 1 keeps every byte outside the five shadow bytes *)
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 296 <= a < ACtlCutP.Sfr fr + 301) ->
            LM.mrd A.Img0.rsegs m2 (LM.wa a) = LM.mrd A.Img0.rsegs mem3 (LM.wa a)).
  { intros a Ha Hno. unfold LM.mrd. rewrite (MU1 (LM.wa a)); [reflexivity|].
    rewrite LM.wa_unsigned by exact Ha. unfold R9S.r9_Wsh. cbn [LF.outside]. split; [exact Hno | exact I]. }
  (* ===== G4, stretch 2: r9_call's stretch to the callee entry (Seg/R9Fs.v r9_call_pre_Fs) ===== *)
  assert (Q56 : ACtlCutP.q64 m2 (A + 56) (fr + 2368)).
  { pose proof (R9S.r9_spill_at regs3 A 56 (fr + 2368) mem3 X56 HR9 HA64 ltac:(unfold ART.APPMEM_END; lia)
                  ltac:(lia)) as Hq.
    unfold ACtlCutP.q64. apply (KM.kitmem_bytes_at_mrd mem3 m2 (A + 56) _ Hq).
    intros i Hi. rewrite r9g_len_le8 in Hi. apply KEEP1; [lia|].
    unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
  pose proof (R9S.r9_rd8 m2 (A + 56) _ Q56 (r9g_len_le8 _)) as HRD.
  assert (Rld : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 56) 8).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. apply Vwin. lia. }
  rewrite G9.
  pose proof (R9Fs.r9_call_pre_Fs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                (Y11.getr regs3 1) (Y11.getr regs3 2) (Y11.getr regs3 3) (Y11.getr regs3 4) (Y11.getr regs3 5)
                (Y11.getr regs3 6) (Y11.getr regs3 7) (Y11.getr regs3 8) (Y11.getr regs3 10)
                (Y11.getr regs3 11) (Y11.getr regs3 12) (Y11.getr regs3 13) (Y11.getr regs3 14) (Y11.getr regs3 15)
                (Y11.getr regs3 16) (Y11.getr regs3 17) (Y11.getr regs3 18) (Z_to_bv 64 (ACtlCutP.Sfr fr))
                (Y11.getr regs3 20) (Y11.getr regs3 21)
                (Y11.getr regs3 22) (Y11.getr regs3 23) (Y11.getr regs3 24) (Y11.getr regs3 25) (Y11.getr regs3 26)
                (Z_to_bv 64 4) (Y11.getr regs3 28) (Y11.getr regs3 29) (Y11.getr regs3 30) (Y11.getr regs3 31)
                Y11.fp_regs Y11.fp_csr m2 A (fr + 2368) ltac:(lia) ltac:(lia) HRD Rld) as HRUN2.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HRUN2.
  apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md1 _ _ (POST cx) HRUN2 (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms2 md2 Hrun2 HP2 Hsbm2.
  cbv beta in HP2. subst ms2.
  assert (HJ2 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
  { refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              [] _ Hrun2 (A.ProgBridge.fp_avoids_RNG_W _) (LF.munch_refl _ _) Hsbm2 _); [exact HJ1|].
    intros a _ Hno. exfalso. apply Hno. exact I. }
  (* ===== the call: treac_ctrl_parse_spec at the callee entry, through SRr_bind ===== *)
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMS.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R) end.
  assert (EP : PRS.A_reac_ctrl_parseP = 0x83578) by (vm_compute; reflexivity).
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs PRS.A_reac_ctrl_parseP R1 m2 md2) (POST cx)).
  (* the caller obligations P1-P13 (spec-draft.md section 4) *)
  assert (ESP1 : Reusable.YG0d.spZ R1 = sp) by exact Hspz.
  assert (P2 : Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m2))
    by exact (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ2 HROS).
  assert (P3a : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.ret_ok (Y11.getr R1 1))
    by (vm_compute; reflexivity).
  assert (P3b : 4096 <= Reusable.YG0d.raZ R1).
  { change (Reusable.YG0d.raZ R1) with (bv_unsigned (Z_to_bv 64 0x81680)).
    rewrite LMS.unsigned_lit by lia. lia. }
  assert (P4a : Y11.getr R1 3 = Reusable.YG0d.w64 (Reusable.YG0f.as_gp B)).
  { change (Y11.getr R1 3) with (Y11.getr regs3 3). rewrite HR3. exact Hgp. }
  assert (P4b : Y11.getr R1 4 = Reusable.YG0d.w64 (Reusable.YG0f.as_tp B))
    by (change (Y11.getr R1 4) with (Y11.getr regs3 4); exact HR4).
  assert (P5a : Y11.getr R1 10 = Reusable.YG0d.w64 phi)
    by (change (Y11.getr R1 10) with (Y11.getr regs3 24); exact R24).
  assert (P5b : Y11.getr R1 11 = Reusable.YG0d.w64 (ACtlCutP.rnb cx b))
    by (change (Y11.getr R1 11) with (Y11.getr regs3 18); exact R18).
  assert (P5c : Y11.getr R1 12 = Reusable.YG0d.w64 (fr + 2368)) by reflexivity.
  assert (P8 : Reusable.YG01.count_cid 1 (Reusable.YG01.frames S3) < Reusable.YG00.fs_frames 1)
    by (rewrite HF; vm_compute; reflexivity).
  assert (P9 : 50 <= ACtlCutP.rnb cx b -> exists Lf, In (phi, Lf) (Reusable.YG0d.ablocks B ly3 S3) /\
                 50 <= Reusable.YG00.req_size Lf)
    by (intros _; exists (ACtlCutP.rnb cx b); split; [exact Hphi_in | lia]).
  assert (P10 : fr + 2368 <> 0 -> Reusable.APostBase.afobj segs B ly3 S3 W3 m2 (fr + 2368) 36).
  { intros _. split; [|split].
    - exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efa.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. lia.
    - Z.div_mod_to_equations. lia.
    - apply (r9g_raddr W3 m2 fr ltac:(lia) Hfrm); [|exact SH1].
      intros j Hj. apply Vsh. lia. }
  assert (P11 : fr + 2368 <> 0 -> forall a, fr + 2368 <= a < fr + 2368 + 36 ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3)
              ly3 (ACtlCut.own6 cx) a).
  { intros _ a Ha. right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (P13 : 50 <= ACtlCutP.rnb cx b -> forall i, (i < 50)%nat ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m2 (phi + Z.of_nat i) =
            Some (RPA.cp_v (SM.rt_g (ACtlCut.c_in cx) (Z.of_nat b)) i)).
  { intros _ i Hi.
    destruct (Hblk phi (ACtlCutP.rnb cx b) Hphi_in) as (_ & _ & Hpa & Hpv & Hpf). rewrite Hreq in Hpa, Hpv, Hpf.
    rewrite (A.ProgWorld.aview_vis_mrd W3 m2 _ (Hpv (phi + Z.of_nat i) ltac:(lia))).
    change (Z_to_bv 64 (phi + Z.of_nat i)) with (LM.wa (phi + Z.of_nat i)).
    rewrite KEEP1 by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
    destruct Hphib as (_ & _ & Hpb).
    pose proof (Hpb i ltac:(lia)) as Hpi. change A.AB1v.tfibsegs with A.Img0.rsegs in Hpi.
    rewrite Hpi.
    rewrite (@nth_error_nth' _ (SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b)) i RPA.cp_z ltac:(lia)). cbn [option_map].
    unfold RPA.cp_v, RPA.cp_b, SM.rt_g. rewrite r9g_nth_fr50 by lia. reflexivity. }
  eapply (Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)).
  { exact (TPARSE A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k R1
             phi (ACtlCutP.rnb cx b) (fr + 2368) (SM.rt_g (ACtlCut.c_in cx) (Z.of_nat b))
             HJ2 P2 P3a P3b P4a P4b P5a P5b P5c ltac:(lia)
             ltac:(rewrite ESP1; exact Hspm)
             ltac:(rewrite ESP1; unfold PRS.REAC_CTRL_PARSE_STK, Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK; lia)
             ltac:(rewrite ESP1; lia)
             P8 P9 P10 P11 Hbs50 P13). }
  (* ===== G5: the spec's post at the return pc 0x81680 = the exit cut ===== *)
  intros W2 c2 Hle HPOST.
  destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2' & Ec2 & HJ3 & HPRES & HFR2 & HBL2 & _ & HA0' & _ & HKEPT).
  subst c2.
  change (Reusable.YA0n.SRr segs W2
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81680_at [Z.of_nat b])) regs2 mem2 md2') (POST cx)).
  rewrite ESP1 in HKEPT.
  (* the registers the exit body reads, through aregs_preserved (YG0d.v:22) *)
  assert (E2 : Y11.getr regs2 2 = Y11.getr regs3 2)
    by (exact (HPRES 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E3 : Y11.getr regs2 3 = Y11.getr regs3 3)
    by (exact (HPRES 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E4 : Y11.getr regs2 4 = Y11.getr regs3 4)
    by (exact (HPRES 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E8 : Y11.getr regs2 8 = Y11.getr regs3 8)
    by (exact (HPRES 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E9 : Y11.getr regs2 9 = Y11.getr regs3 9).
  { transitivity (Y11.getr R1 9); [exact (HPRES 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    change (Y11.getr R1 9) with (Z_to_bv 64 A). symmetry. exact HR9. }
  assert (E18 : Y11.getr regs2 18 = Y11.getr regs3 18)
    by (exact (HPRES 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E19' : Y11.getr regs2 19 = Y11.getr regs3 19).
  { transitivity (Y11.getr R1 19); [exact (HPRES 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))|].
    change (Y11.getr R1 19) with (Z_to_bv 64 (ACtlCutP.Sfr fr)). symmetry. exact HR19. }
  assert (E21 : Y11.getr regs2 21 = Y11.getr regs3 21)
    by (exact (HPRES 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E22 : Y11.getr regs2 22 = Y11.getr regs3 22)
    by (exact (HPRES 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E23 : Y11.getr regs2 23 = Y11.getr regs3 23)
    by (exact (HPRES 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E24 : Y11.getr regs2 24 = Y11.getr regs3 24)
    by (exact (HPRES 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E25 : Y11.getr regs2 25 = Y11.getr regs3 25)
    by (exact (HPRES 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E26 : Y11.getr regs2 26 = Y11.getr regs3 26)
    by (exact (HPRES 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (E27 : Y11.getr regs2 27 = Z_to_bv 64 4)
    by (exact (HPRES 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  (* the callee kept every visible byte of the kept classes (ProgWorld.ctl_post_acall_kept) *)
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            A.ProgWorld.kept_class B ly3 S3 (sp - PRS.REAC_CTRL_PARSE_STK) sp
              (fun a => fr + 2368 <= a < fr + 2368 + 36) a ->
            LM.mrd A.Img0.rsegs mem2 (LM.wa a) = LM.mrd A.Img0.rsegs m2 (LM.wa a)).
  { intros a Ha Hv Hkc.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m2 mem2 (sp - PRS.REAC_CTRL_PARSE_STK) sp _ HKEPT Hle
             (LM.wa a));
      [exact Hv | rewrite LM.wa_unsigned by exact Ha; exact Hkc]. }
  (* the bytes the exit body reads are those of the entry body: KEEP2 after KEEP1 *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
            (A <= a < A + 416 \/ ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx \/
             (fr <= a < fr + 4096 /\ ~ (fr + 2368 <= a < fr + 2404)) \/
             (ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 /\ ~ (ACtlCutP.Sfr fr + 296 <= a < ACtlCutP.Sfr fr + 301)) \/
             (exists p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) /\ p <= a < p + Reusable.YG00.req_size n)) ->
            LM.mrd A.Img0.rsegs mem2 (LM.wa a) = LM.mrd A.Img0.rsegs mem3 (LM.wa a)).
  { intros a Ha HD.
    assert (HSfr : ACtlCutP.Sfr fr + 512 <= 0x10007fff8000 /\ 0x7fff8000 <= ACtlCutP.Sfr fr /\
                   (fr + 4096 <= 0x7fff7000 -> ACtlCutP.Sfr fr + 512 <= 0x8fff7000) /\
                   (0x10007fff8000 <= fr -> 0x2008fff7000 <= ACtlCutP.Sfr fr))
      by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
    destruct HD as [Hs | [Hs | [(Hs & Hno) | [(Hs & Hno) | (p & n & Hpn & Hs)]]]].
    - rewrite KEEP2; [apply KEEP1; lia | exact Ha | apply Vwin; lia |].
      left. split; lia.
    - rewrite KEEP2; [apply KEEP1; lia | exact Ha | apply Vwin; lia |].
      left. split; lia.
    - rewrite KEEP2; [apply KEEP1; lia | exact Ha | apply Vfr; lia |].
      right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [|lia].
      left. unfold Reusable.YCbq.frame_rng, Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    - rewrite KEEP2; [apply KEEP1; lia | exact Ha | apply Vsh; lia |].
      right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      split; [|intros HE; unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *; lia].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *. lia.
    - destruct (Hblk p n Hpn) as (Hp4 & Hpc & Hpa & Hpv & Hpf).
      rewrite KEEP2; [apply KEEP1; lia | exact Ha | apply Hpv; lia |].
      right. left. exists p, n, (a - p). split; [exact Hpn|]. split; [lia|]. split; [lia|].
      replace (p + (a - p)) with a by lia. lia. }
  (* presence of the frame bytes at the post (its AR's frames law; frames S2 = frames S3, layout_le) *)
  pose proof HJ3 as (HAR2 & Hly2 & _).
  assert (Hin6' : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite HFR2; exact Hin6).
  assert (Efa2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. exact (KM.kitmem_frame_addr_le _ _ _ 6 (ACtlCut.c_fpos cx) Hly2). }
  destruct (Reusable.YG0d.al_frames segs B LAWS ly2 S2 W2 mem2 md2' 6 (ACtlCut.c_fpos cx) HAR2 Hin6')
    as (_ & _ & Hfpres2 & _).
  rewrite Efa2 in Hfpres2. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfpres2.
  assert (PRES2 : forall a, fr <= a < fr + 4096 -> mem2 (LM.wa a) <> None).
  { intros a Ha. destruct (proj1 (Hfpres2 a Ha)) as (_ & bb & Hbb). unfold LM.wa. rewrite Hbb. discriminate. }
  (* the transport tactics of the exit body *)
  assert (Hlen8 : forall w : word, Z.of_nat (length (LM.le8 w)) = 8) by (intros w; rewrite r9g_len_le8; reflexivity).
  assert (Hspmv : forall off v, 0 <= off <= 408 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hoff Hs. apply (r9g_spill_mv regs3 regs2 mem3 mem2 A off v Hs HR9 HA64
      ltac:(unfold ART.APPMEM_END; lia) Hoff E9).
    intros i Hi. apply KEEP; [lia|]. left. lia. }
  assert (Hbmv : forall a bs, LM.bytes_at A.Img0.rsegs mem3 a bs ->
            fr <= a -> a + Z.of_nat (length bs) <= fr + 2368 -> LM.bytes_at A.Img0.rsegs mem2 a bs).
  { intros a bs Hb Hlo Hhi. apply (KM.kitmem_bytes_at_mrd mem3 mem2 a bs Hb). intros i Hi.
    apply KEEP; [lia|]. right. right. left. split; lia. }
  assert (Hbmv' : forall a bs, LM.bytes_at A.Img0.rsegs mem3 a bs ->
            fr + 2404 <= a -> a + Z.of_nat (length bs) <= fr + 4096 -> LM.bytes_at A.Img0.rsegs mem2 a bs).
  { intros a bs Hb Hlo Hhi. apply (KM.kitmem_bytes_at_mrd mem3 mem2 a bs Hb). intros i Hi.
    apply KEEP; [lia|]. right. right. left. split; lia. }
  assert (Hamv : forall p len, ART.addressable mem3 p len -> fr <= p -> p + len <= fr + 2368 ->
            ART.addressable mem2 p len).
  { intros p len Ha Hlo Hhi. apply (KM.kitmem_addressable_mrd mem3 mem2 p len Ha). intros i Hi.
    apply KEEP; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
    right. right. right. left.
    unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hamv' : forall p len, ART.addressable mem3 p len -> fr + 2408 <= p -> p + len <= fr + 4096 ->
            ART.addressable mem2 p len).
  { intros p len Ha Hlo Hhi. apply (KM.kitmem_addressable_mrd mem3 mem2 p len Ha). intros i Hi.
    apply KEEP; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
    right. right. right. left.
    unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hrwmv : forall a n bs, LST.rw_cells A.Img0.rsegs mem3 a [LC.CB n bs] ->
            fr + 2404 <= a -> a + Z.of_nat n <= fr + 4096 -> LST.rw_cells A.Img0.rsegs mem2 a [LC.CB n bs]).
  { intros a n bs Hrw Hlo Hhi. apply (KM.kitmem_rw_cells_mrd mem3 mem2 a _ Hrw). intros i Hi.
    cbn [LC.cells_size LC.csize] in Hi. rewrite Nat.add_0_r in Hi.
    split; [apply KEEP; [lia|]; right; right; left; split; lia | apply PRES2; lia]. }
  (* the block shadow at the post (CTL_BLOCK_SHADOW at the post's AR; ablocks unchanged) *)
  assert (Hphi_in2 : In (phi, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly2 S2)) by (rewrite HBL2; exact Hphi_in).
  apply (HX cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md2' HBASE).
  - (* journal: the post's *)
    exact HJ3.
  - (* frames: own6, unchanged *)
    rewrite HFR2. exact HF.
  - (* the frame law: own6 *)
    exact HL.
  - (* the event bound: the same k *)
    exact Hk.
  - (* the exit body, C_A81680_at (ACtlCutP.v:1375-1393), at the same turn b *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81680_at ACtlCutP.ixn ACtlCutP.ixz nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [rewrite HBL2; exact HPerm|].
    split.
    { (* FRAC at regs2 / mem2, with the new frame-shadow list (Seg/R9.v r9_shnew) *)
      apply (r9g_frac_move cx fr fr regs3 regs2 mem3 mem2 ltac:(lia) HFRAC E2 E3 E4 E8 E9 E19' E26).
      - intros A' a HR9' HA0 HA1 Ha Hr.
        assert (EA : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A)
            by (unfold ACtlCut.rgv in HR9, HR9'; rewrite <- HR9, <- HR9'; reflexivity).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !LMS.unsigned_lit in E by (unfold ART.APPMEM_END in *; lia). exact E. }
        subst A'. apply KEEP; [exact Ha|].
        destruct Hr as [Hr|[Hr|[Hr|Hr]]]; [left; exact Hr | right; right; left; split; lia
                                         | right; right; left; split; lia | right; left; exact Hr].
      - destruct (R9S.r9_shnew (R9S.r9_Wsh fr) fr mem3 m2 sh
                    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] Hsh Hshl MU1
                    ltac:(intros x Hx; unfold R9S.r9_Wsh; cbn [LF.outside]; split; [lia | exact I])
                    ltac:(intros x Hx; unfold R9S.r9_Wsh; cbn [LF.outside]; split; [lia | exact I])
                    SH1 eq_refl) as (Hsh' & Hshl').
        change (A.Prog.SlotInv.Sfr fr) with (ACtlCutP.Sfr fr) in Hsh'.
        eexists. split; [|exact Hshl'].
        apply (KM.kitmem_bytes_at_mrd m2 mem2 _ _ Hsh'). intros i Hi.
        assert (E392 : Z.of_nat (Z.to_nat A.Prog.SlotInv.FRAME_SHADOW) = 392) by (vm_compute; reflexivity).
        rewrite Hshl', E392 in Hi.
        apply KEEP2; [unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia
                     | apply Vsh; lia |].
        right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
        split; [|intros HE; unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *; Z.div_mod_to_equations; lia].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in *.
        lia. }
    split.
    { split; [exact Hn26|]. split; [exact Hb6|].
      split.
      { (* HB: the block's shadow at the post *)
        split; [exact (proj1 HHB)|].
        apply (CTL_BLOCK_SHADOW LAWS ly2 S2 W2 mem2 md2' phi (ACtlCutP.rnb cx b) phi
                 (A.ACtlK.a_size (ACtlCutP.rnb cx b)) HAR2 Hphi_in2 ltac:(lia)
                 ltac:(unfold A.ACtlK.a_size; lia) ltac:(unfold A.ACtlK.a_size; lia)). }
      split; [unfold ACtlCut.rgv; rewrite E23; exact R23|].
      split; [apply Hbmv'; [exact HOUR | lia | rewrite LOUR; lia]|].
      split; [apply Hamv; [exact HOUTA | lia | lia]|].
      split; [split; [exact Hc7|]; split; [unfold ACtlCut.rgv; rewrite E22; exact R22 | unfold ACtlCut.rgv; rewrite E25; exact R25]|].
      split; [apply Hspmv; [lia | exact S112]|].
      split; [apply Hspmv; [lia | exact S128]|].
      split.
      { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
          P184 & P256 & P264 & P272 & P32).
        split; [apply Hspmv; [lia | exact P40]|]. split; [apply Hspmv; [lia | exact P120]|].
        split; [apply Hspmv; [lia | exact P136]|]. split; [apply Hspmv; [lia | exact P160]|].
        split; [apply Hspmv; [lia | exact P168]|]. split; [apply Hspmv; [lia | exact P176]|].
        split; [apply Hspmv; [lia | exact P208]|]. split; [apply Hspmv; [lia | exact P248]|].
        split; [apply Hamv'; [exact Pad | lia | lia]|].
        split.
        { apply (KM.kitmem_bytes_at_mrd mem3 mem2 _ _ Pin). intros i Hi.
          rewrite <- Hlen in Hi.
          assert (Hn0 : 0 < ACtlCut.c_n cx) by lia.
          assert (Hrq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
            by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia).
          destruct (Hblk _ _ (Hinp_in Hn0)) as (Hp4 & Hc & _). rewrite Hrq in Hc.
          apply KEEP; [lia|].
          right. right. right. right. exists (ACtlCut.c_p cx), (ACtlCut.c_n cx). split; [exact (Hinp_in Hn0)|].
          rewrite Hrq. lia. }
        split.
        { intros Hn0.
          apply (CTL_BLOCK_SHADOW LAWS ly2 S2 W2 mem2 md2' (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_p cx)
                   (ACtlCut.c_n cx) HAR2 ltac:(rewrite HBL2; exact (Hinp_in Hn0)) ltac:(lia) ltac:(lia)
                   ltac:(unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia)). }
        split; [apply Hspmv; [lia | exact P184]|]. split; [apply Hspmv; [lia | exact P256]|].
        split; [apply Hspmv; [lia | exact P264]|]. split; [apply Hspmv; [lia | exact P272]|].
        apply Hspmv; [lia | exact P32]. }
      split; [apply Hspmv; [lia | exact S104]|]. split; [apply Hspmv; [lia | exact S96]|].
      split; [apply Hspmv; [lia | exact S64]|]. split; [apply Hspmv; [lia | exact S144]|].
      split; [apply Hspmv; [lia | exact S192]|].
      split; [destruct Hidb as (idb & Hidb); exists idb; apply Hrwmv; [exact Hidb | lia | lia]|].
      split; [destruct Hjk72 as (junk & Hjk); exists junk; apply Hrwmv; [exact Hjk | lia | lia]|].
      split; [apply Hspmv; [lia | exact S280]|]. split; [apply Hspmv; [lia | exact S240]|].
      split; [destruct Hjy as (jy & Hjy'); exists jy; apply Hrwmv; [exact Hjy' | lia | lia]|].
      split; [destruct Hjk32 as (junk & Hjk); exists junk; apply Hrwmv; [exact Hjk | lia | lia]|].
      split; [apply Hspmv; [lia | exact S152]|].
      split; [unfold ACtlCut.rgv; rewrite E21; exact R21|].
      apply Hamv; [exact HA2176 | lia | lia]. }
    (* X81680: RF, RXS, a0 = rt_k, s11 = 4 *)
    split.
    { split; [split; [|split]|].
      - split; [exact Hb6r|].
        split; [split; [exact Hc7|]; split; [unfold ACtlCut.rgv; rewrite E22; exact R22 | unfold ACtlCut.rgv; rewrite E25; exact R25]|].
        split; [apply Hbmv'; [exact HOURr | lia | rewrite LOUR; lia]|].
        split; [unfold ACtlCut.rgv; rewrite E23; exact R23r|].
        split; [apply Hbmv; [exact HIDBr | lia | rewrite LRID; lia]|].
        apply Hbmv; [exact HFGBr | lia | rewrite LRFG; lia].
      - exact Hnz.
      - split; [unfold ACtlCut.rgv; rewrite E24; exact R24|].
        apply (KM.kitmem_bytes_at_mrd mem3 mem2 _ _ Hphib). intros i Hi. rewrite LRTF in Hi.
        apply KEEP; [lia|]. right. right. right. right. exists phi, (ACtlCutP.rnb cx b).
        split; [exact Hphi_in|]. rewrite Hreq. lia.
      - unfold ACtlCut.rgv; rewrite E18; exact R18. }
    split.
    { split; [apply Hspmv; [lia | exact X48]|]. split; [apply Hspmv; [lia | exact X56]|].
      split; [apply Hspmv; [lia | exact X88]|]. split; [apply Hspmv; [lia | exact X80]|].
      split; [apply Hspmv; [lia | exact X72]|]. split; [apply Hspmv; [lia | exact X8]|].
      split; [apply Hspmv; [lia | exact X0]|]. split; [apply Hspmv; [lia | exact X200]|].
      split; [apply Hspmv; [lia | exact X216]|].
      apply Hamv; [exact HA2256 | lia | lia]. }
    split.
    + unfold ACtlCut.a0v, ACtlCut.rgv. exact HA0'.
    + unfold ACtlCut.rgv. exact E27.
  - (* ctl_rt at the post: ProgWorldCtlRt.ctlrt_of_AR at the post's AR, the read-only view kept from ctl_base *)
    pose proof (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ3 HROS) as HROS2.
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2' HAR2
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS2 (Z.le_refl _) (Z.le_refl _))).
Qed.

End GlueR9.

Print Assumptions glue_seg_R9.

(* Gate check (a Theorem Labs lane 07:18Z): the Section's classes are the CORE copies of the twin modules (lib/Reusable). *)
Locate YM5.RunCeil.
Locate YO9.lib_shape.
Locate Y11.FPState.
(* Gate check (a Theorem Labs lane 07:36Z): ret_ok at P3a is the CORE copy lib.Reusable.YK0s (the one C_reac_ctrl_parse.v
   Imports).  The old partial name resolved first to ctrl's lib.A.Reusable copy (Locate, build
   build 2026-10-29T07:47:16Z); that probe line is removed so no partial YK0s name remains. *)
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.ret_ok.
