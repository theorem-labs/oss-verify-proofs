(* lib/A/ACtlG/R3.v -- GLUE for stage seg_R3 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:664).  Written by a Theorem Labs lane's stage lane for a Theorem Labs lane's walk; single writer.
   rule 24: no function proved (kind: segment lemma; stage glue of a walk).

   WHAT IT PROVES
     glue_seg_R3 : forall POST, CF POST C_A81578 -> CF POST C_A8152c
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R3.  Segment R3 is 0x8152c -> 0x81578 (Seg/R3.v:2-7): two li, fifteen one-byte stores into the frame shadow
   [S(fr) + 254, S(fr) + 291), `mv a0,s5` and `jal reac_identity_init` (0x87100), which zeroes the 38 identity
   bytes at s5 = fr + 2176 through __asan_memset and returns to 0x81578.

   ROUTE (a Theorem Labs lane, 04:0xZ: route (a) of the split rule; route (C) L3 switch 13:0xZ).  The segment's _F run, in its
   route (C) twin A.Prog.Seg.R3Fon.r3_evt_F_on, takes the callee's reac_identity_init_contract_F_on AS ITS OWN
   PREMISE and spans the call, so this stage SUPPLIES that premise with the callee's PROVED contract
   A.Prog.reac_identity_initF.reac_identity_init_F_holds_on_closed and lifts the WHOLE segment run once with
   Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  No split, no lift cited.  SRr_fevt_hid's own
   continuation carries ajournal_exec's hidden-bytes premise, so there is no _hid placeholder.

   THE PROOF (glue-pattern.md G1-G5)
   G1  C_A8152c's 26 body conjuncts (ACtlCutP.v:1208-1224) and FRAC's 24 (ACtlCutP.v:980-994).
   G2  r3_evt_F_on's premises: registers from FRAC / the body; the 37 frame-shadow cells from FRAC's 392 shadow bytes
       and ctl_rt_C's region (F) (the own class-6 frame's shadow, HFR); the id cell, the callee's stack window and their bytes from the journal's AR
       (AR_frames_law, YG0d.v:447-455) and its stack window (YCbq.v:368); every bound from visible state: the frame
       lies above the image (A.ProgWorld_Fs.ctl_frame_above_img, premise-free: 0x5fe000 <= fr), its zone (in_app,
       AR_frames_law) and the stack's place (astk_ok, YCbq.v:333, above alloc_ceiling).  Every footprint range by a
       visibility fact: the frame and its
       shadow (A.ProgWorldVisFrame.frame_vis), the window (A.ProgWorldVisWin.win_vis) and its shadow
       (win_sh_vis), the image and the runtime words (A.ProgBridge.img_vis_W / rt_vis_W).
   G3  ProgBridge.cfg_at_MS, then Reusable.YA0nR.SRr_xregs_eqv onto the canonical map mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and Reusable.YA0nR.SRr_fevt_hid at RNG_W (w_H W3).
   G5  the exit cut C_A81578 (ACtlCutP.v:1228-1246) at the run's end map R and memory m': the journal by
       ajournal_exec over the write set [S(fr)+254, S(fr)+291) u [sp-2224, sp) u [fr+2176, fr+2214) (frame shadow
       and id bytes: in_frames of own6; the callee window: the LLVMF stack window); every kept conjunct by munch
      transport; the new addressable ranges from the stored shadow bytes (Seg/R3.v's r3_addr lemmas); ctl_rt_C at the
       exit from the run's post: its cells and ro_agree, and the cut's two regions carried by the run's forall-P transport.

   CITED, no Section hypothesis for them:
   - the run: A.Prog.Seg.R3Fon.r3_evt_F_on, this lane's route (C) twin of a Theorem Labs lane's R3F.r3_evt_F (R3F.v, not in this delivery, is
     byte-identical); no shadow premise, the post carries `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.  It
     states the run's registers with lib.Lib.PropExec.getr; the continuation restates them over
     lib.Reusable.YK11.getr by `change` (same body).
   - the callee: A.Prog.reac_identity_initF.reac_identity_init_F_holds_on_closed : reac_identity_init_contract_F_on.
   - the frame bound: A.ProgWorld_Fs.ctl_frame_above_img (A.ProgWorld.ctl_frame_above_img_stmt B, a Theorem Labs lane's
     pwglue, premise-free for every frame class) at the live frame (6, c_fpos cx).
   SECTION HYPOTHESES: LAWS only, the core's AR law record (YCbq.v:207), as ACtl.v's Section has it.  VIS0 / OWNED_RO
   were never in this Section.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (Seg/R3.v, Seg/R3Fon.v and
   A.MemNorm are Required, qualified, for helper lemmas and the cited run: closure rule 1).
   NAMES ARE lib.-QUALIFIED: the frame route loads lib/A/Reusable/YK11 and lib/A/Bz/Lib/*, so the partial names
   Reusable.YK11 / Lib.Mem would resolve to those copies; every use here says lib.Reusable.* / lib.Lib.* / lib.A.*.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified everywhere.
   Evidence (builds, closure, Print Assumptions) is in the commit messages, not here. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_initF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R3.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R3Fon.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := lib.A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local helpers (memory facts over lib/Lib's vocabulary; none is a kit helper). *)

(* A range of present bytes is a stk range (every byte is in mem, so both views read it). *)
Lemma glr3_stk_of_present : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk lib.A.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as (_ & b & Hb). unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* Above the image no segment answers, so a byte read through mrd is a byte of the memory itself. *)
Lemma glr3_mrd_hi : forall (m : word -> option byte) (x : word) b,
  6283264 <= bv_unsigned x -> lib.Lib.Mem.mrd lib.A.Img0.rsegs m x = Some b -> m x = Some b.
Proof.
  intros m x b Hx H. unfold lib.Lib.Mem.mrd in H. destruct (m x) as [b'|] eqn:E; [exact H|].
  exfalso. change (lib.Reusable.YK11.seg_rom lib.A.Img0.rsegs x = Some b) in H.
  unfold lib.Reusable.YK11.seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H.
  destruct (find_segment lib.A.Img0.rsegs (bv_unsigned x) 1) as [s|] eqn:Ef; [| cbn in H; discriminate H].
  destruct (lib.A.Prog.Seg.R3.r3_find_below _ _ _ _ _ lib.A.Prog.Seg.R3.r3_rsegs_low Ef ltac:(lia)); lia.
Qed.

(* A q64 cell off the write set is kept. *)
Lemma glr3_q64 : forall W (m m' : word -> option byte) a v,
  lib.A.ACtlCutP.q64 m a v -> lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.disjoint_from W a 8 -> lib.A.ACtlCutP.q64 m' a v.
Proof.
  intros W m m' a v Hq MU HD. unfold lib.A.ACtlCutP.q64 in *.
  eapply lib.Lib.Frame.bytes_at_transport; [exact Hq | exact MU |]. rewrite lib.Lib.Mem.length_le8. exact HD.
Qed.

(* A spill through register 9 (kept by the run) whose cell is off the write set is kept. *)
Lemma glr3_spill : forall W (regs regs' : bvmap 5 word) (m m' : word -> option byte) A off v,
  lib.A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 320 <= 2 ^ 64 -> 0 <= off <= 304 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.disjoint_from W (A + off) 8 ->
  lib.A.ACtlCutP.spill regs m off v -> lib.A.ACtlCutP.spill regs' m' off v.
Proof.
  intros W regs regs' m m' A off v HA HA0 HA1 Hoff E9 MU HD (A0 & HA0' & Hq).
  assert (EA : A0 = A).
  { unfold lib.A.ACtlCut.rgv in HA, HA0'. rewrite HA in HA0'.
    pose proof (f_equal bv_unsigned HA0') as E. rewrite !lib.Lib.MState.unsigned_lit_wrap in E.
    pose proof Hq as Hq'. unfold lib.A.ACtlCutP.q64, lib.Lib.Mem.bytes_at in Hq'. destruct Hq' as (Hq0 & Hq1 & _).
    rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite P64 in *. Z.div_mod_to_equations. lia. }
  subst A0. exists A. split.
  - unfold lib.A.ACtlCut.rgv in *. rewrite E9. exact HA.
  - exact (glr3_q64 W m m' (A + off) v Hq MU HD).
Qed.

(* A rw cell list [CB n l] off the write set is kept. *)
Lemma glr3_cells : forall W (m m' : word -> option byte) a n,
  (exists l, lib.Lib.Step.rw_cells segs m a [lib.Lib.Cells.CB n l]) ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono segs m m' -> lib.Lib.Frame.disjoint_from W a (Z.of_nat n) ->
  exists l, lib.Lib.Step.rw_cells segs m' a [lib.Lib.Cells.CB n l].
Proof.
  intros W m m' a n (l & H) MU WM HD. exists l.
  eapply lib.Lib.Frame.rw_cells_transport; [exact H | exact MU | exact WM |].
  cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. rewrite Nat.add_0_r. exact HD.
Qed.

Section GlueR3.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :230-231), verbatim. *)
Local Notation CF POST X :=
  (lib.A.ACtlCut.ctl_from (SK := lib.A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8152c := (lib.A.ACtlCutP.C_A8152c B).
Local Notation C_A81578 := (lib.A.ACtlCutP.C_A81578 B).

(* The core's AR laws (YCbq.v:207; ACtl.v:185). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

(* Unfold the numeric constants a goal names and close it by linear arithmetic over the context's numeric facts. *)
Local Ltac glr3_unf :=
  unfold lib.A.ACtlCutP.Sfr, lib.A.ACtlCutP.decl_slot, lib.A.Prog.rng_asan.sh_al8_lo, lib.A.Prog.rng_asan.sh_al8_hi,
    lib.A.AsanRT.app_mem, lib.A.AsanRT.in_shadow, lib.A.AsanRT.shadow_addr, lib.Reusable.YG0f.shadow_addr,
    lib.Reusable.YG0n.in_zr, lib.A.AsanRT.RT_HI, lib.A.AsanRT.RT_LO, lib.A.AsanRT.HIGHMEM_BEG,
    lib.A.AsanRT.APPMEM_END, lib.A.AsanRT.LOWMEM_END, lib.A.AsanRT.LOWSHADOW_END, lib.A.AsanRT.HIGHSHADOW_BEG,
    lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_identity_init_c.REAC_IDENTITY_INIT_K, lib.A.Prog.ImgBounds.IMG_LO,
    lib.A.Prog.ImgBounds.IMG_HI, lib.A.ACfn.LLVMF_STK, lib.A.ACfn.A_EMPTY, lib.Reusable.YG0f.SHADOW_OFF in *.
Local Ltac glr3_num :=
  glr3_unf; cbn [fst snd]; lia.

(* An outside / disjoint_from goal over a concrete interval list. *)
Local Ltac glr3_off :=
  first [ cbn [lib.Lib.Frame.outside]; repeat split; glr3_num
        | cbn [lib.Lib.Frame.disjoint_from]; repeat split; glr3_num ].

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R3 : forall POST, CF POST C_A81578 -> CF POST C_A8152c.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A8152c (ACtlCutP.v:1208-1224) and its FRAC (ACtlCutP.v:980-994). *)
  cbv beta iota zeta delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A8152c] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & R21 & HCUR & S48 & Hout & S128 & HPRO & S152 & S144 & S192 &
    Hidr & Hjnk & S280 & S240 & Hjy & Hscr & S56 & S88 & S80 & S72 & S200 & S216 & R18).
  pose proof HFRAC as (A & sp & HFw).
  pose proof HFw as (H2 & Hsp16 & HspZ & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsp4096 & HcAPP & Q304 & Q24 & Q16 & Qh0 & Qh16 & (sh & Hsh & Hshl) & Hsaved & _).
  unfold lib.A.ACtlCutP.FRAME_BYTES in HfrA. unfold lib.A.AsanRT.APPMEM_END in HcAPP.
  pose proof Hrt as (HAC & Hcut & Himg & HRO).
  (* G2: what the journal says about the frame, the stack window and the layout. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ESL & ESH & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & Hstkhi & _).
  destruct (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _]. unfold lib.Reusable.YG0f.ASAN_CEIL in Hce.
  assert (Hin : In (6, lib.A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (lib.A.ACtlCut.c_ly cx) 6 (lib.A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : lib.Reusable.YG0f.frame_addr ly3 6 (lib.A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Efs : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  (* route (C): the own class-6 frame's shadow [S(fr), S(fr) + 512) is region (F) of cut_shadow at the cut's state *)
  assert (HFR : forall a, lib.A.ACtlCutP.Sfr fr <= a < lib.A.ACtlCutP.Sfr fr + 512 ->
                 lib.A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [exact Hin|].
    rewrite Efr3, Efs.
    unfold lib.A.ACtlCutP.Sfr, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF,
      lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K in *.
    lia. }
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (lib.A.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Happ & Hfby & _).
  rewrite Efr3, Efs in Happ, Hfby.
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
    lib.Reusable.YG0f.ASAN_CEIL in Happ.
  (* the frame lies above the image: A.ProgWorld_Fs.ctl_frame_above_img (A.ProgWorld.ctl_frame_above_img_stmt B,
     premise-free, every frame class) at the live frame (6, c_fpos cx) *)
  assert (Hfrlo : 0x5fe000 <= fr).
  { pose proof (lib.A.ProgWorld_Fs.ctl_frame_above_img (rc := rc) B ly3 S3 W3 mem3 md3 6 (lib.A.ACtlCut.c_fpos cx)
                  HAR Hin) as HFA.
    rewrite Efr3 in HFA. exact HFA. }
  (* the numeric facts every arithmetic goal below uses, in unfolded form *)
  assert (Hfz : fr + 4096 <= 0x7fff7000 \/ (0x10007fff8000 <= fr /\ fr + 4096 <= 0x7fffff800000)).
  { destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); [left; exact Hl | right; lia]. }
  assert (Hsplo : 0x7fff7f800000 + 28672 < sp).
  { unfold lib.A.ACfn.LLVMF_STK in Hstklo. unfold lib.A.ACtlCut.c_sp in *. lia. }
  assert (Hspc : sp <= lib.A.ACtlCut.c_sp cx) by lia.
  assert (Hfrsp : fr + 4096 + 28672 < sp).
  { unfold lib.A.ACfn.LLVMF_STK in Hstklo. destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); lia. }
  assert (Hstk3 : lib.Reusable.YG0f.ly_stk_lo ly3 <= sp - 2224 /\ sp <= lib.Reusable.YG0f.ly_stk_hi ly3).
  { rewrite ESL, ESH. unfold lib.A.ACfn.LLVMF_STK in Hstklo. unfold lib.A.ACtlCut.c_sp in *. lia. }
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* the 37 frame-shadow cells the stores hit, read and writable *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (lib.A.Prog.Seg.R3.r3_ba_sub mem3 (lib.A.ACtlCutP.Sfr fr) sh 254 37 Hsh ltac:(lia)) as Hxs.
  replace (lib.A.ACtlCutP.Sfr fr + Z.of_nat 254) with (lib.A.ACtlCutP.Sfr fr + 254) in Hxs by lia.
  assert (Hxl : length (firstn 37 (skipn 254 sh)) = 37%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : lib.Lib.Step.rw_cells lib.A.Img0.rsegs mem3 (lib.A.ACtlCutP.Sfr fr + 254) (map lib.Lib.Cells.C1 (firstn 37 (skipn 254 sh)))).
  { apply lib.A.Prog.Seg.R3.r3_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 37) with 37.
    split; [glr3_num|]. split; [glr3_num|]. intros i Hi.
    refine (proj1 (Hcut _ _ _)); [apply HFR|]; glr3_num. }
  (* the id bytes as one cell, from the frame's present bytes *)
  assert (Hfstk : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3 (fr + 2176) (fr + 2214)).
  { apply (glr3_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. exact (proj1 (Hfby a ltac:(lia))). }
  destruct (lib.Lib.Frame.stk_bytes lib.A.Img0.rsegs mem3 _ _ Hfstk ltac:(lia)) as (idb & Hidl & Hidb).
  assert (Hidl' : length idb = 38%nat) by (rewrite Hidl; replace (fr + 2214 - (fr + 2176)) with 38 by lia;
                                           reflexivity).
  assert (RWid : lib.Lib.Step.rw_cells lib.A.Img0.rsegs mem3 (fr + 2176) [lib.Lib.Cells.CB 38 idb]).
  { rewrite <- Hidl' at 1. apply lib.A.Prog.Seg.R3.r3_rw_CB; [exact Hidb|].
    rewrite Hidl'. replace (Z.of_nat 38) with (fr + 2214 - (fr + 2176)) by lia.
    exact (lib.A.Prog.Seg.R3.r3_wr_stk _ _ _ Hfstk). }
  (* the callee's stack window, present at the cut (the journal's stack window) *)
  assert (Hstkw : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3 (sp - 2224) sp).
  { apply (glr3_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. unfold lib.A.ACfn.LLVMF_STK, lib.A.ACtlCut.c_sp in *. lia. }
  (* visibility of the footprint ranges *)
  assert (FVIS : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
            lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len /\
            (0 <= len -> fr <= 64 * (lo / 64) -> 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096 ->
             len = 0 \/ lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (lib.A.Prog.rng_asan.sh_al8_lo lo)
                          (lib.A.Prog.rng_asan.sh_al8_hi lo len - lib.A.Prog.rng_asan.sh_al8_lo lo))).
  { intros lo len Hv1 Hv2.
    pose proof (lib.A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (lib.A.ACtlCut.c_fpos cx) lo len HAR Hin)
      as V.
    rewrite Efr3, Efs in V. exact (V Hv1 Hv2). }
  destruct (FVIS (fr + 2032) 296 ltac:(lia) ltac:(lia)) as (_ & VSH0).
  destruct (VSH0 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VSH]; [lia|]. clear VSH0.
  destruct (FVIS (fr + 2176) 38 ltac:(lia) ltac:(lia)) as (VID & VIDS0).
  destruct (VIDS0 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VIDS]; [lia|]. clear VIDS0.
  (* the callee window: every byte present in the journal's stack window, so visible (as ProgWorldVisWin.win_vis) *)
  assert (VWIN : lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (sp - 2224) 2224).
  { split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres a ltac:(unfold lib.A.ACfn.LLVMF_STK, lib.A.ACtlCut.c_sp in *; lia))). }
  destruct (lib.A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2224) 2224 HAR
              ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VWSH]; [lia|].
  (* G3: the cut's configuration in the run's state form, moved onto the canonical map mkR_of regs3 *)
  rewrite lib.A.ProgBridge.cfg_at_MS.
  change (lib.A.ACtlCut.cut_pc C_A8152c) with 0x8152c.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8152c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the whole segment run, the callee's contract supplied by its proof, lifted once *)
  eapply (lib.Reusable.YA0nR.SRr_fevt_hid segs lib.A.ACtlG.Kit.kit_wx W3 _ md3
            (lib.A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))).
  - apply lib.A.ProgBridge.fevt_of_evtF.
    eapply (lib.A.Prog.Seg.R3Fon.r3_evt_F_on lib.A.Prog.reac_identity_initF.reac_identity_init_F_holds_on_closed)
      with (spv := sp) (Sh := lib.A.ACtlCutP.Sfr fr) (idp := fr + 2176) (lo := sp - 2224)
           (xs := firstn 37 (skipn 254 sh)) (idb := idb).
    + exact H2.
    + exact H19.
    + exact R21.
    + glr3_num.
    + glr3_num.
    + glr3_num.
    + glr3_num.
    + lia.
    + glr3_num.
    + glr3_num.
    + glr3_num.
    + lia.
    + glr3_num.
    + glr3_num.
    + intros a Ha. glr3_num.
    + lia.
    + exact Hxl.
    + exact CHx.
    + exact RWid.
    + exact HRO.
    + exact Hstkw.
    + exact HAC.
    + apply lib.A.ProgBridge.rng_of_visible.
      eapply lib.A.ProgBridge.range_visible_sub; [exact VSH | glr3_num | lia | glr3_num].
    + exact (lib.A.ProgBridge.rng_bytes_RNG_W _).
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ (lib.A.ProgBridge.img_vis_W W3)).
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ VWIN).
    + right. exact (lib.A.ProgBridge.rng_of_visible _ _ _ VWSH).
    + apply lib.A.ProgBridge.rng_of_visible.
      eapply lib.A.ProgBridge.range_visible_sub; [exact VWSH | glr3_num | glr3_num | glr3_num].
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ (lib.A.ProgBridge.rt_vis_W W3)).
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ VID).
    + apply lib.A.ProgBridge.rng_of_visible.
      eapply lib.A.ProgBridge.range_visible_sub; [exact VIDS | glr3_num | glr3_num | glr3_num].
  - exact (lib.A.ProgBridge.fp_avoids_RNG_W _).
  - (* G5: the continuation at the run's end state *)
    intros ms' md' HQ Hhid Hsbm.
    destruct HQ as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K18 & K21 & MU & WM &
      RO' & ST' & AC' & SWP & RWid' & B0 & B18 & B28).
    subst ms'.
    (* route (C): the run's region transport carries the cut's two regions to m' *)
    pose proof (SWP _ Hcut) as Hcut'. pose proof (SWP _ Himg) as Himg'. clear SWP.
    (* R3F states the run's registers with lib.Lib.PropExec.getr; the cuts read lib.Reusable.YK11.getr (same body) *)
    repeat match goal with H : ?g R ?i = ?v |- _ =>
      lazymatch g with lib.Reusable.YK11.getr => fail | _ => change (lib.Reusable.YK11.getr R i = v) in H end end.
    assert (Hhid' : forall x : word, lib.Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x)
      by (intros x Hx; exact (Hhid x Hx)).
    clear Hhid.
    change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs (lib.A.ACtlCut.cut_pc C_A81578) R m' md') (POST cx)).
    (* every written byte is a byte of m' *)
    assert (RDW : forall x : word,
              ~ lib.Lib.Frame.outside [(lib.A.ACtlCutP.Sfr fr + 254, lib.A.ACtlCutP.Sfr fr + 291); (sp - 2224, sp);
                                    (fr + 2176, fr + 2176 + 38)] (bv_unsigned x) ->
              exists b, m' x = Some b).
    { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      apply lib.A.Prog.Seg.R3.r3_not_out in Hx.
      assert (Hrd : exists b, lib.Lib.Mem.mrd lib.A.Img0.rsegs m' (lib.Lib.Mem.wa (bv_unsigned x)) = Some b).
      { destruct Hx as [Hx | [Hx | Hx]].
        - refine (proj2 (Hcut' (bv_unsigned x) _ _)); [apply HFR|]; glr3_num.
        - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs (bv_unsigned x) ltac:(lia))).
        - exact (lib.A.Prog.Seg.R3.r3_rd_rw m' (fr + 2176) 38 _ (bv_unsigned x) RWid' ltac:(lia)). }
      destruct Hrd as (b & Hb). unfold lib.Lib.Mem.wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb.
      exists b. apply (glr3_mrd_hi m' x b); [glr3_num | exact Hb]. }
    assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
    assert (HA0 : 0 <= A) by lia.
    assert (HA1 : A + 320 <= 2 ^ 64) by lia.
    apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
    + (* the journal across the run: write set = the three ranges of the run's munch *)
      eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS lib.A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a => ~ lib.Lib.Frame.outside
                                 [(lib.A.ACtlCutP.Sfr fr + 254, lib.A.ACtlCutP.Sfr fr + 291); (sp - 2224, sp);
                                  (fr + 2176, fr + 2176 + 38)] a);
        [exact HJ | | | exact Hhid' | exact Hsbm |].
      * intros x Hx. cbv beta in Hx.
        destruct (lib.A.Prog.Seg.R3.r3_out_dec
                    [(lib.A.ACtlCutP.Sfr fr + 254, lib.A.ACtlCutP.Sfr fr + 291); (sp - 2224, sp);
                     (fr + 2176, fr + 2176 + 38)] (bv_unsigned x)) as [Ho | Hno]; [| exfalso; exact (Hx Hno)].
        unfold lib.Reusable.YK04.mrestrict. rewrite (MU x Ho). reflexivity.
      * unfold lib.Reusable.YK1b.mem_grows. intros x. unfold lib.Reusable.YK04.mrestrict.
        destruct (lib.Reusable.YA0n.w_H W3 x); [tauto|].
        intros Hx.
        destruct (lib.A.Prog.Seg.R3.r3_out_dec
                    [(lib.A.ACtlCutP.Sfr fr + 254, lib.A.ACtlCutP.Sfr fr + 291); (sp - 2224, sp);
                     (fr + 2176, fr + 2176 + 38)] (bv_unsigned x)) as [Ho | Hno].
        -- rewrite (MU x Ho). exact Hx.
        -- destruct (RDW x Hno) as (b & Hb). rewrite Hb. discriminate.
      * intros a Ha. cbv beta in Ha. apply lib.A.Prog.Seg.R3.r3_not_out in Ha.
        destruct Ha as [Ha | [Ha | Ha]].
        -- right; right; right. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
           right. rewrite Efr3, Efs. glr3_num.
        -- left. unfold lib.A.ACtlCut.c_sp in *. glr3_num.
        -- right; right; right. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
           left. rewrite Efr3, Efs. glr3_num.
    + (* frames: own6 on both cuts *)
      exact HF.
    + (* the frame law: own6 on both cuts *)
      exact HL.
    + (* the event bound: kmax 0 on both cuts *)
      exact Hk.
    + (* the exit body, C_A81578 (ACtlCutP.v:1228-1246) *)
      cbv beta iota delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A81578].
      split; [exact HP|].
      split.
      { (* FRAC at the new memory, its registers moved by kit_frac_move.  The memory part is walked conjunct by
           conjunct, none named by position, so a conjunct appended to FRAC needs no edit here: a conjunct without
           memory is the cut's own (HFw, decomposed); a q64 word moves by munch off the write set (the frame words,
           the spills, and any word of [fr, fr + 4096) outside the run's writes); the saved registers move the same
           way; the frame shadow is rebuilt from the run's shadow_rw. *)
        apply (lib.A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact K2 | exact K3 | exact K4 | exact K8
                                                                  | exact K9 | exact K19 | exact K26].
        pose proof HFw as HFd. cbv beta in HFd. decompose [and] HFd.
        exists A, sp. cbv beta.
        repeat lazymatch goal with |- _ /\ _ => split end.
        all: first
          [ assumption
          | lazymatch goal with
            | |- context [lib.A.ACtlCutP.saved_bytes] =>
                eapply lib.Lib.Frame.bytes_at_transport; [eassumption | exact MU |];
                replace (Z.of_nat (length (lib.A.ACtlCutP.saved_bytes cx))) with 104
                  by (unfold lib.A.ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity);
                unfold lib.A.ACtlCut.c_sp in *; glr3_off
            | |- exists _, _ =>
                assert (Hst : lib.Lib.Frame.stk lib.A.Img0.rsegs m' (lib.A.ACtlCutP.Sfr fr)
                                (lib.A.ACtlCutP.Sfr fr + 392))
                  by (split; [glr3_num|]; split; [glr3_num|]; intros a Ha;
                      refine (Hcut' a _ _); [apply HFR|]; glr3_num);
                destruct (lib.Lib.Frame.stk_bytes lib.A.Img0.rsegs m' _ _ Hst ltac:(lia)) as (bs & Hl & Hb);
                exists bs; split; [exact Hb|]; rewrite Hl;
                replace (lib.A.ACtlCutP.Sfr fr + 392 - lib.A.ACtlCutP.Sfr fr) with 392 by lia; reflexivity
            | |- _ => eapply (glr3_q64 _ mem3 m'); [eassumption | exact MU | glr3_off]
            end ]. }
      split; [exact Hn|].
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|]. unfold lib.A.ACtlCut.rgv in *.
        split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
      split.
      { unfold lib.A.ACtlCutP.OURb in *. eapply lib.Lib.Frame.bytes_at_transport; [exact HOUR | exact MU |].
        rewrite lib.A.Prog.SlotModel.OUR_length. glr3_off. }
      split.
      { unfold lib.A.ACtlCutP.IDBr.
        change (lib.A.Prog.SlotModel.RID (lib.A.ACtlCut.c_in cx) 0) with (repeat (Z_to_bv 8 0) 38).
        destruct RWid' as ((_ & Hb) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb.
        rewrite app_nil_r in Hb. exact Hb. }
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S48]|].
      (* out[]'s 1488 kept bytes plus the 4 the store S(fr) + 254 = 04 makes addressable *)
      split.
      { apply (lib.A.Prog.Seg.R3.r3_addr_cat m' (fr + 544) 1488 4).
        - apply (lib.A.Prog.Seg.R3.r3_addr_keep _ mem3 m' _ _ Hout MU). intros i Hi. glr3_off.
        - apply (lib.A.Prog.Seg.R3.r3_addr_r m' (fr + 544 + 1488) 4 (Z_to_bv 8 4));
            [lia | glr3_num | lia | reflexivity | glr3_num | intros i Hi; glr3_num |].
          replace (lib.A.AsanRT.shadow_addr (fr + 544 + 1488)) with (lib.A.ACtlCutP.Sfr fr + 254) by glr3_num.
          exact B0. }
      split.
      { (* the 38 id bytes: shadow 00 00 00 00 06 at S(fr) + 272 *)
        apply (lib.A.Prog.Seg.R3.r3_addr_cat m' (fr + 2176) 32 6).
        - apply (lib.A.Prog.Seg.R3.r3_addr_z m' (fr + 2176) 4 32);
            [reflexivity | lia | glr3_num | glr3_num | intros i Hi; glr3_num |].
          replace (lib.A.AsanRT.shadow_addr (fr + 2176)) with (lib.A.ACtlCutP.Sfr fr + 272) by glr3_num.
          pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 0 4 B18 ltac:(cbn [length]; lia)) as H4b.
          cbn [firstn skipn] in H4b. change (Z.of_nat 0) with 0 in H4b. rewrite Z.add_0_r in H4b. exact H4b.
        - apply (lib.A.Prog.Seg.R3.r3_addr_r m' (fr + 2176 + 32) 6 (Z_to_bv 8 6));
            [lia | glr3_num | lia | reflexivity | glr3_num | intros i Hi; glr3_num |].
          replace (lib.A.AsanRT.shadow_addr (fr + 2176 + 32)) with (lib.A.ACtlCutP.Sfr fr + 272 + 4) by glr3_num.
          pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 4 1 B18 ltac:(cbn [length]; lia)) as H6b.
          cbn [firstn skipn] in H6b. change (Z.of_nat 4) with 4 in H6b. exact H6b. }
      split.
      { (* the 72 frag bytes: shadow nine 00 at S(fr) + 282 *)
        apply (lib.A.Prog.Seg.R3.r3_addr_z m' (fr + 2256) 9 72);
          [reflexivity | lia | glr3_num | glr3_num | intros i Hi; glr3_num |].
        replace (lib.A.AsanRT.shadow_addr (fr + 2256)) with (lib.A.ACtlCutP.Sfr fr + 282) by glr3_num. exact B28. }
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S128]|].
      split.
      { (* PRO: its spills, our[]'s 6 bytes, and the input block (off the frame, the stack and the shadow) *)
        destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pnad & P184 & P256 &
          P264 & P272 & P32).
        destruct HB as ((_ & _ & _ & _ & Hpn & Hnl & _) & _).
        assert (Hblk : (lib.A.ACtlCut.c_n cx = 0 /\ lib.A.ACtlCut.c_p cx = lib.A.ACfn.A_EMPTY) \/
                       (0 < lib.A.ACtlCut.c_n cx /\ lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx + 28672 < sp /\
                        4096 <= lib.A.ACtlCut.c_p cx /\
                        (lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx <= 0x7fff7000 \/ 0x10007fff8000 <= lib.A.ACtlCut.c_p cx) /\
                        (lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx <= fr \/ fr + 4096 <= lib.A.ACtlCut.c_p cx))).
        { destruct Hpn as [Hz | (Hn0 & Hinb)]; [left; exact Hz | right].
          assert (Hinb3 : In (lib.A.ACtlCut.c_p cx, lib.A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
            by exact (Permutation_in _ (Permutation_sym HP) Hinb).
          destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb3)
            as (_ & Hb4096 & Hbceil & Hbapp & _).
          pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (lib.A.ACtlCut.c_fpos cx)
                        HAR Hinb3 Hin) as Hsep.
          rewrite Efr3, Efs in Hsep.
          assert (Ereq : lib.Reusable.YG00.req_size (lib.A.ACtlCut.c_n cx) = lib.A.ACtlCut.c_n cx).
          { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (lib.A.ACtlCut.c_n cx) 0); lia. }
          rewrite Ereq in Hbceil, Hbapp, Hsep.
          unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
            lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.zdisjoint in Hbapp, Hsep. cbn [fst snd] in Hsep.
          unfold lib.A.ACfn.LLVMF_STK in Hstklo. lia. }
        assert (Hinl : Z.of_nat (length (lib.A.ACtlCut.c_in cx)) = lib.A.ACtlCut.c_n cx) by lia.
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P40]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P120]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P136]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P160]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P168]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P176]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P208]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P248]|].
        split; [apply (lib.A.Prog.Seg.R3.r3_addr_keep _ mem3 m' _ _ Pad MU); intros i Hi; glr3_off|].
        split.
        { eapply lib.Lib.Frame.bytes_at_transport; [exact Pin | exact MU |]. rewrite Hinl. glr3_off. }
        split.
        { intros Hn0. apply (lib.A.Prog.Seg.R3.r3_addr_keep _ mem3 m' _ _ (Pnad Hn0) MU). intros i Hi. glr3_off. }
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P184]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P256]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P264]|].
        split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                       | glr3_off | exact P272]|].
        eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                 | glr3_off | exact P32]. }
      split; [unfold lib.A.ACtlCut.rgv in *; rewrite K21; exact R21|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S152]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S144]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S192]|].
      split; [apply (glr3_cells _ mem3 m' _ _ Hidr MU WM); glr3_off|].
      split; [apply (glr3_cells _ mem3 m' _ _ Hjnk MU WM); glr3_off|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S280]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S240]|].
      split; [apply (glr3_cells _ mem3 m' _ _ Hjy MU WM); glr3_off|].
      split; [apply (glr3_cells _ mem3 m' _ _ Hscr MU WM); glr3_off|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S56]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S88]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S80]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S72]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S200]|].
      split; [eapply (glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9 | exact MU
                                                     | glr3_off | exact S216]|].
      unfold lib.A.ACtlCut.rgv in *. rewrite K18. exact R18.
    + (* ctl_rt_C at the exit, at the same state ly3 S3: the cells and ro_agree from the run's post, the two regions
         carried by its transport *)
      split; [exact AC' | split; [exact Hcut' | split; [exact Himg' | exact RO']]].
Qed.

End GlueR3.
