(* lib/A/ACtlG/F38.v -- GLUE for stage seg_F38 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   Hypothesis seg_F38).  Written by a Theorem Labs lane after the pattern of lib/A/ACtlG/A5.v
   (glue-pattern.md (a working note, not in this delivery)); single writer.  rule 24: no function proved
   (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F38 : forall POST (j : nat),
       CF POST (ix_cut C_A81d40_at [Z.of_nat (S j)]) -> CF POST C_A82b04 -> CF POST (ix_cut C_A82940_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F38.  The ENTRY is C_A82940_at at turn j (the conclusion); the two EXITS (the premises) are the frame loop's
   head at the NEXT turn, C_A81d40_at [S j] (back edge 0x8295c), and the loop exit C_A82b04 (0x82944 / 0x82960).
   Segment F38 is the frame-loop LATCH 0x82940-0x82960 (Seg/F38.v:9-22): no call, no store, two spill reloads.

   THE THREE RUNS (lib/A/Prog/Seg/F38F.v, this unit's _F re-runs of Seg/F38.v, Required qualified) and the split
   (Seg/F38.v f38_run :381-404, followed here):
     j = 255 (`255 <= j`, with LK's j <= 255)   f38_evt_x_F   0x82940 -> 0x82b04  `li a0,254; bltu a0,s5` taken;
                                                                                  no memory access (empty footprint)
     j <= 254, aa = cc (input exhausted)        f38_evt_e_F   0x82940 -> 0x82b04  falls through `bnez s9` to `j`
     j <= 254, aa <> cc                         f38_evt_b_F   0x82940 -> 0x81d40  back edge
   with aa = t_left j - t_h j (the spill [A + 224], FLSI), bb = c_p + t_body j (the spill [A + 216], FLSI) and
   cc = flen j (register s2 = x18, FLSF).  The b / e runs read [A + 216, +8) and [A + 224, +8) and write nothing.
   Seg/F38.v's f38_run_lib (its Lib-evt -> SR bridge) is NOT used: the glue lifts the _F runs through a Theorem Labs lane's
   bridge (G4) instead, which is that function's role here.

   THE NEXT TURN'S INDEX.  The exit C_A81d40_at is taken at idx := [Z.of_nat (S j)] (ix_cut's `idx = i0` by
   reflexivity; its body's j' = ixn 0 [Z.of_nat (S j)] = S j by Nat2Z.id).  The body's register fact at that index,
   LK's `rgv R 21 (Z.of_nat (S j))` (s5 = the turn counter), is produced by f38_evt_b_F's post: its end map holds
   `Z_to_bv 64 (jv + 1)` in register 21 (`addiw s5,s5,1` at 0x82958), instantiated at jv := Z.of_nat j from the
   entry's LK `rgv regs3 21 (Z.of_nat j)` (the run's premise x21 = Z_to_bv 64 jv), and Z.of_nat j + 1 =
   Z.of_nat (S j).  The other LI facts of turn S j come from the same post: s6 = x22 = bb + cc = c_p + t_c (S j)
   (CUR), s9 = x25 = aa - cc = c_n - t_c (S j) (CUR; and 1 <= t_left (S j) from aa <> cc), with the model's own
   step t_c (S j) = t_body j + t_len j (SlotModel's fc, by reflexivity) and f38_t_facts (Seg/F38.v:91).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index equation, then C_A82940_at's body (ACtlCutP.v, `exists phi`, six
       conjuncts: Permutation, FRAC, c_n bound, LK, FLSF, LT), at j by Nat2Z.id.
   G2  the runs' premises from the body and visible state: the spill base A of FRAC (register 9) with
       416 <= A (fr >= 4096 from frames_bounds and the frame law, as A5; fr + FRAME_BYTES <= A) and
       A + 416 <= 2 ^ 64 (A + 416 <= c_sp <= APPMEM_END); the two spills of FLSI at that A (their own base A0 is A:
       same register, both in [0, 2 ^ 64)), as ro_cells by AsanRTFacts.ro_c8; the value bounds of bb / aa / cc from
       the model (f38_t_facts), f1_IN's addressable (0 <= c_p, c_p + c_n <= APPMEM_END), the body's c_n < 2 ^ 26 and
       the pre's c_n = length c_in (ctl_base); the two rng premises by ProgBridge.rng_of_visible from the journal's
       window-present conjunct (YCbq.v ajournal: every byte of [c_sp - LLVMF_STK, c_sp) is visible in W3), since
       [A + 216, A + 232) lies in [c_sp - 4096, c_sp) by FRAC.  No bound is left as a hypothesis.
   G3  cfg_at_MS, then YA0nR.SRr_xregs_eqv from regs3 to mkR_of regs3 (the runs' explicit mkR start map).
   G4  lift: ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt; the x run at the empty footprint Kit.kit_RNG0, the b / e
       runs at ProgBridge.RNG_W (w_H W3) (fp_avoids by fp_avoids_RNG_W).  The runs write no memory, so SRr_fevt
       (not SRr_fevt_hid) suffices: the journal crosses them with the empty write set.
   G5  the continuation: the end state is MS R .. mem3 .., R the run's own explicit end map (registers kept but
       10, 21, 22, 25); every kept-register fact `getr R r = getr regs3 r` and every written one is by computation.
       Exits: the local EPI (C_A82b04, used by the x and e runs: its OURb is LK's, [A + 144] and the 17 bytes at
       fr + 2691 are FLSH's, the identity bytes are LT's IDj (S j) with byte 19 = 0, as Seg/F38.v f38_epi :287-320
       does it) and the back edge C_A81d40_at [S j] (LI of S j as above, FLSH / f1_IN / [A + 248] / FLC from FLSI
       through register 9).  Journal by ajournal_exec with the empty write set; frames, frame law and ctl_rt_C
       unchanged; k bound: 14 + 2j + 2 = 14 + 2 (S j) on the back edge, and <= 526 = EV_LLVMF on the exit by LK's
       j <= 255.

   ROUTE (C) (L3; shell ACtlCut.v (at head lib/A/ACtlCut.v:243; from a working branch 8ce82d7e310)): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  The latch reads no shadow byte and keeps ly3, S3 and
   the memory on both exits, so each exit passes the entry's Hrt as it is; the Section never had VIS0 / OWNED_RO.

   SECTION HYPOTHESES.  The Section mirrors ACtl.v's Section Ctl at a Theorem Labs lane's Batch3 glue base d36efc6152d (ACtl.v
   blob a3c6b7b35017; its Context, variables and hypotheses, in its order, through KPARSE, including Batch3's
   RELRO_KIND_NAME / RELRO_CAT / RELRO_FRAMES / MO_LE / KREPLY / KPARSE in ACtl.v's exact text and names).  The proof
   uses only LAWS (ajournal_exec, frames_bounds); the rest are unused and do not become arguments: after the Section
   the lemma is `glue_seg_F38 {fx rc} B MT XM_LIB RLO RHI LAWS`, so ACtl.v discharges seg_F38 with
   `exact (glue_seg_F38 B MT XM_LIB RLO RHI LAWS)`.  No _F run is a hypothesis: all three are Required from
   Seg/F38F.v.

   THE FAKE-FRAME TRAILER WORD (Batch3; FRAC's last conjunct, ACtlCutP.v:997, `q64 m (fr + 4088)
   (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))`).  The latch writes no memory, so both exits (C_A81d40_at [S j]
   and C_A82b04) PRODUCE FRAC by A.ACtlG.Kit.kit_frac_move from the entry's whole FRAC at the same memory mem3: the
   trailer word reads memory only and is carried as it stands.  G2 reads FRAC's register 9 and spill-base bounds by
   their TEXT (decompose [and]), not by position, so the appended conjunct moves nothing.

   CITED BY NAME: Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt; A.ProgBridge.fevt_of_evtF, cfg_at_MS, RNG_W,
   fp_avoids_RNG_W, rng_of_visible, range_visible; Reusable.YCbq.ajournal_exec / frames_bounds; Seg/F38F.v's
   f38_evt_x_F / f38_evt_b_F / f38_evt_e_F; Seg/F38.v's model lemmas f38_t_facts, f38_tID_len, f38_id_win (stated
   over SlotModel / RcIdentModel / StrFun only); A.AsanRTFacts.ro_c8.  From the kit (Required, never copied):
   kit_wx, kit_segs_low, kit_frac_move, kit_RNG0.

   CLOSURE: every Require below is qualified; no statement here names a frame-route identifier.  Measured with
   closure_scan.py (sha256 039e7d56edc3..., conservative: an ambiguous
   Require counts all its matches) on a Theorem Labs lane's stand-in-free glue base 29ddfc3ea99 merged: 534 unit files;
   closure-rule-3 files NONE (no lib/AZ/AsanW (not in this delivery), no W6, no SegCF / *_cfw / Cf* file); its lib/AZ files are
   AZ/LibA/AcctCore.v (through Lib/ExecF.v) and AZ/Spec/{AsanCtrl,AsanCtrlProps,STree}.v (through Seg/F38.v).
   Frame-route files, each at its blob on that base: Seg/F38.v 2c3fae322ce, Seg/F38F.v 087d2ca1ecf, Seg/Tac_slot.v
   de02ff45188, Seg/Tac_fs.v 8bd492a660d, Seg/Tac_fsfree.v d76d2012bf8, SlotInv.v 4cf85db229a, SlotModel.v
   04dc7903221, AsanRT.v b67d26f8ec7 (mcs 30), AsanRTInv.v 2a8602e8526, AsanRTFacts.v 1657e654e8c, Contract.v
   fa6fd478d9a, FrameAPI.v f6ffefa9bb4, MemNorm.v cb518fc0304, PContract.v a0c4b1b2aa5, AsanLift.v e92b008d733,
   KindBGlue.v 35e845dad50, BzBridge.v 6ae71886a55, Prog/RcAsanFP.v 4ec9fa6fbdb, Prog/RcAsanFPLib.v e1f4a4f0b5a,
   Prog/RcAsanRT.v 706993599b7, Tk/AW/SmLeaf.v 34b4fe82ea7, Tk/AW/SmLib.v d486737eb6d.

   NAMES: getr / mkst / seg_rom / cfg_at are YK11 / Reusable.YG0d-qualified everywhere, and the modules that exist
   both as the core's lib/Reusable/<X> or lib/Lib/<X> and as a ctrl copy (YK11, YK1b, YM05, YO09; Lib/MState,
   Lib/Mem) are cited by their FULL path and Required from their own directory (porter 04:24Z / 04:33Z rule).
   Check: grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F38.v  -- hits only inside comments.

   BUILD STATE: TYPE-CHECK ON INTERIM 5da74c9c931, CLOSURE REACHES NO STAND-IN.  rc=0 by cb
   on a build machine (a fresh worktree; workspace from the packed base 23b918fe0c2e) with NO port_core_refused
   substitution: on the stand-in-free glue base 29ddfc3ea99 the five planning-core files the type-check workspaces
   used to substitute (lib/A/AE2k.v AF0m.v AF0l.v ACej.v ACeh.v) carry no port_core_refused_ name and compile from
   their own text.  No Axiom, no Parameter, no Admitted, no admit.  Print Assumptions glue_seg_F38: Rocq primitives
   (PrimInt63, PrimString, PrimArray) and functional_extensionality_dep only. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six modules with a ctrl copy (YK11, YK1b, YM05, YO09 here) and lib/Lib's MState / Mem (with lib/A/Bz, lib/AZ
   copies) are Required from their own directory, so the core copy is the one loaded (porter 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.AF0m A.ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel Prog.RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F38 A.Prog.Seg.F38F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF38.

(* ACtl.v's Section Ctl shape (ACtl.v (an earlier version, blob a3c6b7b35017, not in this delivery), a Theorem Labs lane's Batch3 glue base d36efc6152d), in its order,
   through KPARSE.  The Batch3 additions RELRO_KIND_NAME / RELRO_CAT / RELRO_FRAMES / MO_LE / KREPLY / KPARSE are
   ACtl.v's exact text and names (ACtl.v:204-206, :217, :237-238); this stage uses none of them, so none becomes an
   argument of glue_seg_F38. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* ACtl.v's notation block, verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81d40_at := (ACtlCutP.C_A81d40_at B).
Local Notation C_A82940_at := (ACtlCutP.C_A82940_at B).
Local Notation C_A82b04 := (ACtlCutP.C_A82b04 B).

Lemma glue_seg_F38 : forall POST (j : nat),
  CF POST (ix_cut C_A81d40_at [Z.of_nat (S j)]) -> CF POST C_A82b04 -> CF POST (ix_cut C_A82940_at [Z.of_nat j]).
Proof.
  intros POST j HS HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A82940_at). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82940_at ACtlCutP.ixn nth] in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & HLK & HFLSF & HLT).
  rewrite Znat.Nat2Z.id in HLK, HFLSF, HLT.
  cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A82940_at ACtlCutP.ixn nth] in Hk.
  rewrite Znat.Nat2Z.id in Hk.
  pose proof HLK as (Hj255 & H21 & HOUR).
  pose proof HFLSF as (HFLSI & H18 & _ & _ & _ & _ & _ & _).
  pose proof HFLSI as (HFLSH & S216 & S224 & S248 & HIN & HFLC).
  pose proof HIN as ((Hp0 & Hn0 & Hpn & _) & _).
  unfold A.AsanRT.APPMEM_END in Hpn.
  (* G2: the spill base A (FRAC) and its bounds, from visible state.  FRAC's conjuncts are found by their TEXT,
     not by position (decompose + assumption), so a conjunct added to FRAC does not move them. *)
  pose proof HFRAC as (A & sp & HFR).
  assert (HR9 : ACtlCut.rgv regs3 9 A) by (decompose [and] HFR; assumption).
  assert (HAb : sp <= A /\ fr + ACtlCutP.FRAME_BYTES <= A /\ A + 416 <= ACtlCut.c_sp cx /\
                ACtlCut.c_sp cx - 4096 < sp /\ ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END)
    by (decompose [and] HFR; repeat match goal with |- _ /\ _ => split end; assumption).
  clear HFR. destruct HAb as (HspA & HfrA & HA416 & Hsp4096 & HSapp).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Hfr4096 : 4096 <= fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. exact Hf4096. }
  assert (HAlo : 416 <= A) by lia.
  assert (HAhi : A + 416 <= 2 ^ 64) by lia.
  (* the two spill reloads [A + 216] / [A + 224]: each spill's own base A0 is A (the same register 9; A0 within 224
     bytes below the 64-bit range by the spill's bytes_at, A inside it by FRAC) *)
  assert (Ebase : forall A0, ACtlCut.rgv regs3 9 A0 -> -224 <= A0 -> A0 + 224 <= 2 ^ 64 -> A0 = A).
  { intros A0 HA0 Hlo Hhi. unfold ACtlCut.rgv in HA0, HR9. rewrite HR9 in HA0.
    apply (f_equal bv_unsigned) in HA0. rewrite !Z_to_bv_unsigned in HA0. unfold bv_wrap, bv_modulus in HA0.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in HA0.
    rewrite (Z.mod_small A) in HA0 by lia. Z.div_mod_to_equations. lia. }
  destruct S216 as (A1 & HA1 & Q216).
  destruct S224 as (A2 & HA2 & Q224).
  unfold ACtlCutP.q64 in Q216, Q224.
  pose proof Q216 as B216. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_bound in B216.
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in B216.
  pose proof Q224 as B224. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_bound in B224.
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in B224.
  assert (EA1 : A1 = A) by (apply Ebase; [exact HA1 | lia | lia]).
  assert (EA2 : A2 = A) by (apply Ebase; [exact HA2 | lia | lia]).
  subst A1 A2.
  pose proof (A.AsanRTFacts.ro_c8 mem3 (A + 216) _ Q216) as K216.
  pose proof (A.AsanRTFacts.ro_c8 mem3 (A + 224) _ Q224) as K224.
  (* the reloads' footprint: [A + off, +8) inside the journal's present window [c_sp - LLVMF_STK, c_sp) *)
  assert (Hvis : forall off, 0 <= off -> off + 8 <= 416 ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A + off) 8).
  { intros off Ho1 Ho2. split; [lia|]. split; [lia|].
    intros a Ha. unfold A.ACfn.LLVMF_STK in Hwin.
    destruct (Hwin a ltac:(lia)) as [Hh _]. exact Hh. }
  (* the model's turn arithmetic (SlotModel), and c_n = nlen c_in (the pre, ctl_base) *)
  pose proof HB as ((_ & _ & _ & _ & _ & Elen & _) & _).
  assert (Enl : A.Prog.SlotModel.nlen (ACtlCut.c_in cx) = ACtlCut.c_n cx)
    by (unfold A.Prog.SlotModel.nlen; symmetry; exact Elen).
  pose proof (A.Prog.Seg.F38.f38_t_facts (ACtlCut.c_in cx) j) as (Rc & EL & (Hh0 & Hh1) & (Hl0 & Hl1) & Eb).
  pose proof (A.Prog.Seg.F38.f38_t_facts (ACtlCut.c_in cx) (S j)) as (Rc' & EL' & _).
  assert (EcS : A.Prog.SlotModel.t_c (ACtlCut.c_in cx) (S j) =
                A.Prog.SlotModel.t_body (ACtlCut.c_in cx) j + A.Prog.SlotModel.t_len (ACtlCut.c_in cx) j)
    by reflexivity.
  set (bb := ACtlCut.c_p cx + A.Prog.SlotModel.t_body (ACtlCut.c_in cx) j) in *.
  set (aa := A.Prog.SlotModel.t_left (ACtlCut.c_in cx) j - A.Prog.SlotModel.t_h (ACtlCut.c_in cx) j) in *.
  set (cc := ACtlCutP.flen cx j) in *.
  assert (Ebb : bb = ACtlCut.c_p cx + A.Prog.SlotModel.t_body (ACtlCut.c_in cx) j) by reflexivity.
  assert (Eaa : aa = A.Prog.SlotModel.t_left (ACtlCut.c_in cx) j - A.Prog.SlotModel.t_h (ACtlCut.c_in cx) j)
    by reflexivity.
  assert (Ecc : cc = A.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) by reflexivity.
  assert (Hbb : 0 <= bb < 2 ^ 64) by lia.
  assert (Haa : aa < 2 ^ 64) by lia.
  assert (Hcc : 0 <= cc <= aa) by lia.
  (* every spill of the entry map is a spill of a map that keeps register 9 *)
  assert (Hsp : forall Rx : bvmap 5 word,
            OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9 ->
            forall off v, ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill Rx mem3 off v).
  { intros Rx K9 off v (Ab & HAb & Hq). exists Ab. split; [|exact Hq].
    unfold ACtlCut.rgv in *. rewrite K9. exact HAb. }
  (* THE EXIT C_A82b04 from any end map that keeps FRAC's registers, at the entry memory (Seg/F38.v f38_epi). *)
  assert (EPI : forall (Rx : bvmap 5 word) md',
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26 ->
    Reusable.YK04.same_but_materialized md3 md' ->
    Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x82b04 Rx mem3 md') (POST cx)).
  { intros Rx md' K2 K3 K4 K8 K9 K19 K26 Hsbm.
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A82b04) Rx mem3 md') (POST cx)).
    apply (HX cx [] fr k ly3 S3 W3 Rx mem3 md' HB).
    - (* journal: no byte written, the model materialized *)
      eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    - exact HF.
    - exact HL.
    - (* k <= 14 + 2 j + 2 <= 526 = EV_LLVMF, by LK's j <= 255 *)
      cbv beta iota delta [ACtlCut.cut_kmax ACtlCutP.C_A82b04]. unfold A.ACtlK.EV_LLVMF. lia.
    - cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A82b04].
      pose proof HFLSH as (_ & _ & _ & S144 & H2691).
      pose proof HLT as ((HID & HIDok) & _ & _).
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rx mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      split; [exact Hn|]. split; [exact HOUR|].
      split; [exact (Hsp Rx K9 _ _ S144)|].
      split; [|exact H2691].
      (* the identity record of turn S j (LT's IDj): its first 21 bytes, byte 19 = 0 (id_ok) *)
      pose proof (A.Prog.Seg.F38.f38_tID_len (ACtlCut.c_in cx) (S j)) as HLn.
      destruct HIDok as (_ & _ & _ & H19 & _).
      exists (firstn 21 (A.Prog.SlotModel.t_ID (ACtlCut.c_in cx) (S j))).
      split; [|split].
      + unfold ACtlCutP.IDBe in HID.
        rewrite <- (List.firstn_skipn 21 (A.Prog.SlotModel.t_ID (ACtlCut.c_in cx) (S j))) in HID.
        apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_app in HID. exact (proj1 HID).
      + rewrite List.length_firstn, HLn. reflexivity.
      + apply A.Prog.Seg.F38.f38_id_win; [rewrite HLn; unfold Prog.RcIdentModel.ID_SIZE; lia | exact H19].
    - (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
      exact Hrt. }
  (* G3: the cut's configuration in the runs' state form, the walk moved to the runs' canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82940_at [Z.of_nat j])) with 0x82940.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82940) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  destruct (Nat.le_gt_cases 255 j) as [Hx|Hx].
  - (* j = 255: f38_evt_x_F, no memory access; exit C_A82b04 *)
    eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (A.Prog.Seg.F38F.f38_evt_x_F A.ACtlG.Kit.kit_RNG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               _ _ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
               mem3 (Z.of_nat j)); [exact H21 | lia]. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
    match goal with
    | |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] => apply (EPI R md') end;
      [reflexivity .. | exact Hsbm].
  - (* j <= 254: the two spill reloads, then the exit or the back edge *)
    assert (Hjv : 0 <= Z.of_nat j <= 254) by lia.
    destruct (Z.eq_dec aa cc) as [Heq|Hne].
    + (* the input is exhausted (aa = cc): f38_evt_e_F; exit C_A82b04 *)
      eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)).
      { apply A.ProgBridge.fevt_of_evtF.
        apply (A.Prog.Seg.F38F.f38_evt_e_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
                 mem3 A aa bb cc (Z.of_nat j));
          [ exact HR9 | exact H18 | exact H21 | lia | lia | lia | exact K216 | exact K224 | lia | lia | lia
          | exact Heq
          | apply A.ProgBridge.rng_of_visible, Hvis; lia | apply A.ProgBridge.rng_of_visible, Hvis; lia ]. }
      { apply A.ProgBridge.fp_avoids_RNG_W. }
      intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
      match goal with
      | |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] => apply (EPI R md') end;
        [reflexivity .. | exact Hsbm].
    + (* the back edge (aa <> cc): f38_evt_b_F; exit C_A81d40_at at the next turn's index [Z.of_nat (S j)] *)
      eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)).
      { apply A.ProgBridge.fevt_of_evtF.
        apply (A.Prog.Seg.F38F.f38_evt_b_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
                 mem3 A aa bb cc (Z.of_nat j));
          [ exact HR9 | exact H18 | exact H21 | lia | lia | lia | exact K216 | exact K224 | lia | lia | lia
          | exact Hne
          | apply A.ProgBridge.rng_of_visible, Hvis; lia | apply A.ProgBridge.rng_of_visible, Hvis; lia ]. }
      { apply A.ProgBridge.fp_avoids_RNG_W. }
      intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
      match goal with
      | |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (Rb := R) end.
      change (Reusable.YA0n.SRr segs W3
        (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81d40_at [Z.of_nat (S j)])) Rb mem3 md') (POST cx)).
      (* the end map: registers kept but 10 / 21 / 22 / 25; the post's written values *)
      assert (K2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 2 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) by reflexivity.
      assert (K3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 3 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3) by reflexivity.
      assert (K4 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 4 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) by reflexivity.
      assert (K8 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 8 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8) by reflexivity.
      assert (K9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 9 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by reflexivity.
      assert (K19 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 19 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19) by reflexivity.
      assert (K26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 26 =
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26) by reflexivity.
      (* the loop counter s5: the post's `addiw s5,s5,1` value at jv := Z.of_nat j *)
      assert (K21 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 21 =
                    Z_to_bv 64 (Z.of_nat j + 1)) by reflexivity.
      assert (K22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 22 =
                    Z_to_bv 64 (bb + cc)) by reflexivity.
      assert (K25 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rb 25 =
                    Z_to_bv 64 (aa - cc)) by reflexivity.
      apply (HS cx [Z.of_nat (S j)] fr k ly3 S3 W3 Rb mem3 md' HB).
      * (* journal: no byte written, the model materialized *)
        eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
          [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
          | intros x _; reflexivity
          | exact Hsbm | intros a Ha; destruct Ha].
      * exact HF.
      * exact HL.
      * (* k <= 14 + 2 j + 2 = 14 + 2 (S j) *)
        cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A81d40_at ACtlCutP.ixn nth].
        rewrite Znat.Nat2Z.id. lia.
      * (* the head's body at turn S j *)
        cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81d40_at ACtlCutP.ixn nth].
        split; [reflexivity|].
        rewrite Znat.Nat2Z.id.
        split; [exact HP|].
        split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rb mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
        split; [exact Hn|].
        split.
        { (* LI of turn S j *)
          unfold ACtlCutP.LI, ACtlCutP.LK, ACtlCutP.CUR.
          split.
          { split; [lia|]. split; [|exact HOUR].
            unfold ACtlCut.rgv. rewrite K21. f_equal. lia. }
          split.
          { split; [lia|]. split.
            - unfold ACtlCut.rgv. rewrite K22. f_equal. lia.
            - unfold ACtlCut.rgv. rewrite K25. f_equal. lia. }
          split; [lia|].
          (* IFS of turn S j: LT's, its two spills [A + 104] / [A + 112] through register 9 *)
          destruct HLT as (HID & HFG & (Q104 & Q112 & Qbody & Qad & HFI)).
          split; [exact HID|]. split; [exact HFG|].
          split; [exact (Hsp Rb K9 _ _ Q104)|]. split; [exact (Hsp Rb K9 _ _ Q112)|].
          split; [exact Qbody|]. split; [exact Qad | exact HFI]. }
        (* FLSH (its body does not read the turn index): PRO, then the loop part *)
        split.
        { destruct HFLSH as ((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
                              P184 & P256 & P264 & P272 & P32) & P128 & Pstk & P144 & P2691).
          split.
          { exact (conj (Hsp Rb K9 _ _ P40) (conj (Hsp Rb K9 _ _ P120) (conj (Hsp Rb K9 _ _ P136)
              (conj (Hsp Rb K9 _ _ P160) (conj (Hsp Rb K9 _ _ P168) (conj (Hsp Rb K9 _ _ P176)
              (conj (Hsp Rb K9 _ _ P208) (conj (Hsp Rb K9 _ _ P248) (conj Pad (conj Pin (conj Pg
              (conj (Hsp Rb K9 _ _ P184) (conj (Hsp Rb K9 _ _ P256) (conj (Hsp Rb K9 _ _ P264)
              (conj (Hsp Rb K9 _ _ P272) (Hsp Rb K9 _ _ P32)))))))))))))))). }
          split; [exact (Hsp Rb K9 _ _ P128)|]. split; [exact Pstk|].
          split; [exact (Hsp Rb K9 _ _ P144) | exact P2691]. }
        (* the harness block, the [A + 248] spill and FLC: FLSI's, the latch writes no memory *)
        split; [exact HIN|].
        split; [exact (Hsp Rb K9 _ _ S248)|].
        destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Ca72 & Ca38 & C72 & C64 & C56 & C48).
        exact (conj (Hsp Rb K9 _ _ C256) (conj (Hsp Rb K9 _ _ C184) (conj (Hsp Rb K9 _ _ C192)
          (conj (Hsp Rb K9 _ _ C80) (conj (Hsp Rb K9 _ _ C88) (conj (Hsp Rb K9 _ _ C96)
          (conj (Hsp Rb K9 _ _ C272) (conj (Hsp Rb K9 _ _ C264) (conj Ca72 (conj Ca38
          (conj (Hsp Rb K9 _ _ C72) (conj (Hsp Rb K9 _ _ C64) (conj (Hsp Rb K9 _ _ C56)
          (Hsp Rb K9 _ _ C48)))))))))))))).
      * (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
        exact Hrt.
Qed.

End GlueF38.
