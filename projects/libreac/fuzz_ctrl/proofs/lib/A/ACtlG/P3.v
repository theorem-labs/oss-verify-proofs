(* lib/A/ACtlG/P3.v -- GLUE for stage seg_P3 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:717).  Written by a Theorem Labs lane's stage lane for a Theorem Labs lane's walk; single writer.
   rule 24: no function proved (kind: segment lemma; stage glue of a walk).

   WHAT IT PROVES
     glue_seg_P3 : forall POST, CF POST C_A81b80 -> CF POST C_A81b14
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P3.  Segment P3 is 0x81b14 -> 0x81b80 (Seg/P3.v): nineteen one-byte stores into the frame shadow
   [S(fr) + 336, S(fr) + 365), `ld a0,32(s1)` and `jal __asan_memset` (0x81b74: the 35 bytes of first.sroa.7 at
   fr + 2880), `mv a0,s11` and `jal reac_identity_init` (0x81b7c: the 38 identity bytes at fr + 2688), return to
   0x81b80.

   ROUTE (a Theorem Labs lane, 04:0xZ: route (a); route (C) L3 switch 13:5xZ).  The segment's _F run, in a Theorem Labs lane's route (C)
   form Seg/P3F.v p3_evt_ro_F_on, takes BOTH callees' _F_on contracts as its own premises and spans both calls, so this
   stage SUPPLIES them with their PROVED forms -- A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds
   and A.Prog.reac_identity_initF.reac_identity_init_F_holds_on_closed -- and lifts the WHOLE segment run once with
   Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  No split, no lift cited.  The callees' mem_inv
   premises are met inside the run on the normalized memory (MemNormF.evtF_normalize_ro); this stage gives it ro_agree
   from ctl_rt_C's fourth part.  SRr_fevt_hid's continuation carries ajournal_exec's hidden-bytes premise.

   THE PROOF (glue-pattern.md G1-G5)
   G1  C_A81b14's body (ACtlCutP.v:1769-1785) and FRAC (ACtlCutP.v:980-994).
   G2  p3_evt_ro_F_on's premises: registers from FRAC / the body; the 29 frame-shadow cells from FRAC's 392 shadow
       bytes and ctl_rt_C's region (F) (HFR); the run's narrowed region P3.p3_evt_ro_shadow_R id fb from region (F)
       too (both callees' shadow words lie in the own frame's shadow); the identity cell, the spill [A + 32] = fr + 2880 (PRO's position 16) and
       first.sroa.7's 35 bytes from the body / PRO and the frame's present bytes (AR_frames_law); the window from
      the journal; every bound from visible state, as glue lib/A/ACtlG/R3.v does (the frame above the image from
      A.ProgWorld_Fs.ctl_frame_above_img, its zone from in_app, the stack above alloc_ceiling from astk_ok); every footprint
       range by a visibility fact (A.ProgWorldVisFrame.frame_vis, A.ProgWorldVisWin.win_sh_vis, the journal's
       present stack bytes, A.ProgBridge.img_vis_W / rt_vis_W).
   G3  ProgBridge.cfg_at_MS, then Reusable.YA0nR.SRr_xregs_eqv onto mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and Reusable.YA0nR.SRr_fevt_hid at RNG_W (w_H W3).
   G5  the exit cut C_A81b80 (ACtlCutP.v:1789-1820) at the run's end map and memory: the two munch facts of the post
       joined over the write set [S(fr)+336, S(fr)+365) u [sp-2224, sp) u [fr+2688, fr+2726) u [fr+2880, fr+2915);
       the journal by ajournal_exec (frame shadow and frame bytes: in_frames of own6; the callee windows: the LLVMF
      stack window); asan_cells across the write set (AsanRTFacts.asan_cells_kept); ctl_rt_C's two regions across
      the write set by R3Fon.r3on_shadow_rw_on (each shadow byte the run wrote is a stored one); the new addressable
      ranges from the stored shadow bytes; every kept conjunct by munch transport.

   CITED, no Section hypothesis for them:
   - the run: A.Prog.Seg.P3F.p3_evt_ro_F_on (a Theorem Labs lane, P3F.v (at head lib/A/Prog/Seg/P3F.v:702; written on a working branch 2fbeebc6850)): p3_evt_ro_F with the two callees'
     _F_on contracts and `shadow_rw_on (P3.p3_evt_ro_shadow_R id fb) m` in place of `shadow_rw m`.  The
     continuation restates the run's register facts over lib.Reusable.YK11.getr by `change` (same body).
   - the frame bound: A.ProgWorld_Fs.ctl_frame_above_img (A.ProgWorld.ctl_frame_above_img_stmt B, a Theorem Labs lane's
     pwglue, premise-free for every frame class) at the live frame (6, c_fpos cx).
   SECTION HYPOTHESES: LAWS only, the core's AR law record (YCbq.v:207), as ACtl.v's Section has it.  VIS0 / OWNED_RO
   were never in this Section.

   HELPERS: the memory helpers of glue lib/A/ACtlG/R3.v (its glr3_ lemmas), Required qualified; none is a kit helper.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (Seg/P3.v, Seg/P3F.v, Seg/R3.v
   and A.MemNorm are Required, qualified, for helper lemmas and the cited run: closure rule 1).
   NAMES ARE lib.-QUALIFIED: the frame route loads lib/A/Reusable/YK11 and lib/A/Bz/Lib/*, so every use here says
   lib.Reusable.* / lib.Lib.* / lib.A.*.  getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 /
   lib.Reusable.YG0d-qualified everywhere.
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
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_cF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memsetF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memset.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_initF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R3.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.P3.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.P3F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R3Fon.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memsetF_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
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
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.R3.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := lib.A.AB1v.tfibsegs.

(* Two readings of one 64-bit word, both in range, are the same number. *)
Lemma glp3_eq64 : forall (w : word) a b, w = Z_to_bv 64 a -> w = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros w a b Ha Hb Ra Rb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !lib.Lib.MState.unsigned_lit in Hb by lia. exact Hb.
Qed.

(* A spill through register 9 = A is the q64 cell at A + off. *)
Lemma glp3_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) A off v,
  lib.A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 320 <= 2 ^ 64 -> 0 <= off <= 304 ->
  lib.A.ACtlCutP.spill regs m off v -> lib.A.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v HA HA0 HA1 Hoff (A0 & HA0' & Hq).
  assert (EA : A0 = A).
  { unfold lib.A.ACtlCut.rgv in HA, HA0'. rewrite HA in HA0'.
    pose proof (f_equal bv_unsigned HA0') as E. rewrite !lib.Lib.MState.unsigned_lit_wrap in E.
    pose proof Hq as Hq'. unfold lib.A.ACtlCutP.q64, lib.Lib.Mem.bytes_at in Hq'. destruct Hq' as (Hq0 & Hq1 & _).
    rewrite lib.Lib.Mem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite P64 in *. Z.div_mod_to_equations. lia. }
  subst A0. exact Hq.
Qed.

Section GlueP3.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :252-253), verbatim but for the lib. qualification. *)
Local Notation CF POST X :=
  (lib.A.ACtlCut.ctl_from (SK := lib.A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81b14 := (lib.A.ACtlCutP.C_A81b14 B).
Local Notation C_A81b80 := (lib.A.ACtlCutP.C_A81b80 B).

(* The core's AR laws (YCbq.v:207; ACtl.v:185). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

(* Unfold the numeric constants (goal and context) and close by linear arithmetic. *)
Local Ltac glp3_unf :=
  unfold lib.A.ACtlCutP.Sfr, lib.A.ACtlCutP.fragb, lib.A.Prog.rng_asan.sh_al8_lo, lib.A.Prog.rng_asan.sh_al8_hi,
    lib.A.AsanRT.app_mem, lib.A.AsanRT.in_shadow, lib.A.AsanRT.shadow_addr, lib.Reusable.YG0f.shadow_addr,
    lib.Reusable.YG0n.in_zr, lib.A.AsanRT.RT_HI, lib.A.AsanRT.RT_LO, lib.A.AsanRT.HIGHMEM_BEG,
    lib.A.AsanRT.APPMEM_END, lib.A.AsanRT.LOWMEM_END, lib.A.AsanRT.LOWSHADOW_END, lib.A.AsanRT.HIGHSHADOW_BEG,
    lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_identity_init_c.REAC_IDENTITY_INIT_K, lib.A.Prog.asan_memset_c.ASAN_MEMSET_K,
    lib.A.Prog.ImgBounds.IMG_LO, lib.A.Prog.ImgBounds.IMG_HI, lib.A.ACfn.LLVMF_STK, lib.A.ACfn.A_EMPTY,
    lib.Reusable.YG0f.SHADOW_OFF, lib.A.ACtlCutP.FRAME_SHADOW, lib.A.ACtlCutP.FRAME_BYTES in *.
Local Ltac glp3_num := glp3_unf; cbn [fst snd]; lia.

(* An outside / disjoint_from goal over a concrete interval list. *)
Local Ltac glp3_off :=
  first [ cbn [lib.Lib.Frame.outside]; repeat split; glp3_num
        | cbn [lib.Lib.Frame.disjoint_from]; repeat split; glp3_num ].

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P3 : forall POST, CF POST C_A81b80 -> CF POST C_A81b14.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81b14 (ACtlCutP.v:1769-1785) and its FRAC (ACtlCutP.v:980-994). *)
  cbv beta iota zeta delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A81b14] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 &
    (spv0 & A0 & idb & junk & E2' & E9' & R27 & HA0r & Hspvr & RW192 & RWid & RWd & Q280 & Q240 &
     (jy & junk2 & RWjy & RWj2))).
  pose proof HFRAC as (A & sp & HFw).
  pose proof HFw as (H2 & Hsp16 & HspZ & H4 & H8 & H9 & H3 & H19 & H26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsp4096 & HcAPP & Q304 & Q24 & Q16 & Qh0 & Qh16 & (sh & Hsh & Hshl) & Hsaved & _).
  unfold lib.A.ACtlCutP.FRAME_BYTES in HfrA. unfold lib.A.AsanRT.APPMEM_END in HcAPP.
  pose proof Hrt as (HAC & Hcut & Himg & HRO).
  (* G2: what the journal says about the frame, the stack window and the layout (as glue R3.v). *)
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
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 320 <= 2 ^ 64) by lia.
  (* the body's existential s1 is FRAC's A *)
  assert (EA0 : A0 = A).
  { apply (glp3_eq64 (lib.Reusable.YK11.getr regs3 9)); [exact E9' | exact H9 | lia | lia]. }
  subst A0.
  (* the 29 frame-shadow cells the stores hit, read and writable *)
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  pose proof (lib.A.Prog.Seg.R3.r3_ba_sub mem3 (lib.A.ACtlCutP.Sfr fr) sh 336 29 Hsh ltac:(lia)) as Hxs.
  replace (lib.A.ACtlCutP.Sfr fr + Z.of_nat 336) with (lib.A.ACtlCutP.Sfr fr + 336) in Hxs by lia.
  assert (Hxl : length (firstn 29 (skipn 336 sh)) = 29%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : lib.Lib.Step.rw_cells lib.A.Img0.rsegs mem3 (lib.A.ACtlCutP.Sfr fr + 336)
                  (map lib.Lib.Cells.C1 (firstn 29 (skipn 336 sh)))).
  { apply lib.A.Prog.Seg.R3.r3_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 29) with 29.
    split; [glp3_num|]. split; [glp3_num|]. intros i Hi.
    refine (proj1 (Hcut _ _ _)); [apply HFR|]; glp3_num. }
  remember (firstn 29 (skipn 336 sh)) as xs eqn:Exs.
  destruct xs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16
    [|b17 [|b18 [|b19 [|b20 [|b21 [|b22 [|b23 [|b24 [|b25 [|b26 [|b27 [|b28 [|bx xs]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    try (cbn in Hxl; lia).
  cbn [map] in CHx.
  (* the spill [A + 32] = fr + 2880 (PRO's position 16), as a C8 cell of the present stack *)
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P32).
  pose proof (glp3_spill_at regs3 mem3 A 32 (fr + 2880) H9 HA0 HA1 ltac:(lia) P32) as Q32.
  assert (HstA : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3 (A + 32) (A + 40)).
  { apply (lib.A.ACtlG.R3.glr3_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. unfold lib.A.ACfn.LLVMF_STK, lib.A.ACtlCut.c_sp in *. lia. }
  pose proof (lib.A.Prog.Seg.P3.p3_q64_rw1 mem3 (A + 32) (A + 40) (A + 32) (fr + 2880) HstA ltac:(lia) ltac:(lia)
                Q32) as RWA.
  (* first.sroa.7's 35 frame bytes, from the frame's present bytes *)
  assert (Hfstk : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3 fr (fr + 4096)).
  { apply (lib.A.ACtlG.R3.glr3_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. exact (proj1 (Hfby a Ha)). }
  destruct (lib.A.Prog.Seg.P3.p3_cells mem3 fr (fr + 4096) (fr + 2880) 35 Hfstk ltac:(lia)
              ltac:(cbn [Z.of_nat]; lia)) as (fbj & RWF).
  (* the callee window, present at the cut *)
  assert (Hstkw : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3 (sp - 2224) sp).
  { apply (lib.A.ACtlG.R3.glr3_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. unfold lib.A.ACfn.LLVMF_STK, lib.A.ACtlCut.c_sp in *. lia. }
  (* the identity object at fr + 2688 (shadow 00 00 00 00 06 at S(fr) + 336) and first.sroa.7 at fr + 2880
     (shadow 00 00 00 00 03 at S(fr) + 360) are addressable once their shadow bytes read so *)
  assert (HADDR : forall m', lib.Lib.Mem.bytes_at lib.A.Img0.rsegs m' (lib.A.ACtlCutP.Sfr fr + 336)
                    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
                  lib.A.AsanRT.addressable m' (fr + 2688) 38).
  { intros m' HBo. apply (lib.A.Prog.Seg.R3.r3_addr_cat m' (fr + 2688) 32 6).
    - apply (lib.A.Prog.Seg.R3.r3_addr_z m' (fr + 2688) 4 32);
        [reflexivity | lia | glp3_num | glp3_num | intros i Hi; glp3_num |].
      replace (lib.A.AsanRT.shadow_addr (fr + 2688)) with (lib.A.ACtlCutP.Sfr fr + 336) by glp3_num.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 0 4 HBo ltac:(cbn [length]; lia)) as H4b.
      cbn [firstn skipn] in H4b. change (Z.of_nat 0) with 0 in H4b. rewrite Z.add_0_r in H4b. exact H4b.
    - apply (lib.A.Prog.Seg.R3.r3_addr_r m' (fr + 2688 + 32) 6 (Z_to_bv 8 6));
        [lia | glp3_num | lia | reflexivity | glp3_num | intros i Hi; glp3_num |].
      replace (lib.A.AsanRT.shadow_addr (fr + 2688 + 32)) with (lib.A.ACtlCutP.Sfr fr + 336 + 4) by glp3_num.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 4 1 HBo ltac:(cbn [length]; lia)) as H6b.
      cbn [firstn skipn] in H6b. change (Z.of_nat 4) with 4 in H6b. exact H6b. }
  assert (HADDRf : forall m', lib.Lib.Mem.bytes_at lib.A.Img0.rsegs m' (lib.A.ACtlCutP.Sfr fr + 360)
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
                   lib.A.AsanRT.addressable m' (fr + 2880) 35).
  { intros m' HBo. apply (lib.A.Prog.Seg.R3.r3_addr_cat m' (fr + 2880) 32 3).
    - apply (lib.A.Prog.Seg.R3.r3_addr_z m' (fr + 2880) 4 32);
        [reflexivity | lia | glp3_num | glp3_num | intros i Hi; glp3_num |].
      replace (lib.A.AsanRT.shadow_addr (fr + 2880)) with (lib.A.ACtlCutP.Sfr fr + 360) by glp3_num.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 0 4 HBo ltac:(cbn [length]; lia)) as H4b.
      cbn [firstn skipn] in H4b. change (Z.of_nat 0) with 0 in H4b. rewrite Z.add_0_r in H4b. exact H4b.
    - apply (lib.A.Prog.Seg.R3.r3_addr_r m' (fr + 2880 + 32) 3 (Z_to_bv 8 3));
        [lia | glp3_num | lia | reflexivity | glp3_num | intros i Hi; glp3_num |].
      replace (lib.A.AsanRT.shadow_addr (fr + 2880 + 32)) with (lib.A.ACtlCutP.Sfr fr + 360 + 4) by glp3_num.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 4 1 HBo ltac:(cbn [length]; lia)) as H6b.
      cbn [firstn skipn] in H6b. change (Z.of_nat 4) with 4 in H6b. exact H6b. }
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
  destruct (FVIS (fr + 2688) 232 ltac:(lia) ltac:(lia)) as (_ & VSH0).
  destruct (VSH0 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VSH]; [lia|]. clear VSH0.
  destruct (FVIS (fr + 2688) 38 ltac:(lia) ltac:(lia)) as (VID & VIDS0).
  destruct (VIDS0 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VIDS]; [lia|]. clear VIDS0.
  destruct (FVIS (fr + 2880) 35 ltac:(lia) ltac:(lia)) as (VFB & VFBS0).
  destruct (VFBS0 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VFBS]; [lia|]. clear VFBS0.
  (* stack bytes: present in the journal's stack window, so visible (as ProgWorldVisWin.win_vis) *)
  assert (VSTK : forall lo len, lib.A.ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= lib.A.ACtlCut.c_sp cx ->
            0 <= len -> lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len Hv1 Hv2 Hv3. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres a ltac:(unfold lib.A.ACfn.LLVMF_STK; lia))). }
  destruct (lib.A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2224) 2224 HAR
              ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VWSH]; [lia|].
  destruct (lib.A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2208) 2208 HAR
              ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | VWSH2]; [lia|].
  (* G3: the cut's configuration in the run's state form, moved onto the canonical map mkR_of regs3 *)
  rewrite lib.A.ProgBridge.cfg_at_MS.
  change (lib.A.ACtlCut.cut_pc C_A81b14) with 0x81b14.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81b14) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the whole segment run, both callees' contracts supplied by their proofs, lifted once *)
  eapply (lib.Reusable.YA0nR.SRr_fevt_hid segs lib.A.ACtlG.Kit.kit_wx W3 _ md3
            (lib.A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))).
  - apply lib.A.ProgBridge.fevt_of_evtF.
    eapply (lib.A.Prog.Seg.P3F.p3_evt_ro_F_on (lib.A.Prog.asan_memsetF_on.asan_memset_holds_F_on lib.A.Prog.memset.memset_holds)
              lib.A.Prog.reac_identity_initF.reac_identity_init_F_holds_on_closed)
      with (spv := sp) (S := lib.A.ACtlCutP.Sfr fr) (id := fr + 2688) (lo := sp - 2224) (A := A) (fb := fr + 2880)
           (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8)
           (b9 := b9) (b10 := b10) (b11 := b11) (b12 := b12) (b13 := b13) (b14 := b14) (b15 := b15) (b16 := b16)
           (b17 := b17) (b18 := b18) (b19 := b19) (b20 := b20) (b21 := b21) (b22 := b22) (b23 := b23)
           (b24 := b24) (b25 := b25) (b26 := b26) (b27 := b27) (b28 := b28) (idb := idb) (fbj := fbj).
    + exact H2.
    + exact H19.
    + exact R27.
    + exact H9.
    + lia.
    + glp3_num.
    + glp3_num.
    + lia.
    + lia.
    + glp3_num.
    + glp3_num.
    + lia.
    + lia.
    + glp3_num.
    + lia.
    + lia.
    + glp3_num.
    + lia.
    + exact CHx.
    + exact RWid.
    + exact RWA.
    + exact RWF.
    + exact HADDR.
    + exact HADDRf.
    + right. glp3_num.
    + glp3_num.
    + glp3_num.
    + right. glp3_num.
    + glp3_num.
    + glp3_num.
    + glp3_num.
    + exact Hstkw.
    + glp3_num.
    + glp3_num.
    + glp3_num.
    + exact HAC.
    + (* the run's narrowed region P3.p3_evt_ro_shadow_R id fb, both disjuncts in the own class-6 frame's shadow,
         region (F) of cut_shadow (HFR): memset's sh_word_on (fr+2880) 35 lies in [S(fr)+353, S(fr)+372), init's
         sh_word_on (fr+2688) 38 in [S(fr)+329, S(fr)+348) *)
      apply (lib.A.ShadowRwOn.shadow_rw_on_mono (lib.A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
      intros a Ha. apply HFR.
      unfold lib.A.Prog.Seg.P3.p3_evt_ro_shadow_R, lib.A.Prog.Seg.P3.p3_evt_shadow_R,
        lib.A.Prog.asan_memset_c_on.asan_memset_shadow_R,
        lib.A.Prog.reac_identity_init_c.reac_identity_init_shadow_R, lib.A.Prog.sh_word_on.sh_word_on in Ha.
      rewrite !lib.Lib.MState.unsigned_lit in Ha by glp3_num.
      unfold lib.A.Prog.rng_asan.sh_al8_lo, lib.A.Prog.rng_asan.sh_al8_hi in Ha. glp3_unf.
      destruct Ha as [(_ & Hlo & Hhi) | (_ & _ & Hlo & Hhi)]; Z.div_mod_to_equations; lia.
    + exact HRO.
    + apply lib.A.ProgBridge.rng_of_visible.
      eapply lib.A.ProgBridge.range_visible_sub; [exact VSH | glp3_num | lia | glp3_num].
    + apply lib.A.ProgBridge.rng_of_visible. apply VSTK; lia.
    + exact (lib.A.ProgBridge.rng_bytes_RNG_W _).
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ (lib.A.ProgBridge.img_vis_W W3)).
    + apply lib.A.ProgBridge.rng_of_visible. apply VSTK; glp3_num.
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ VFB).
    + right. exact (lib.A.ProgBridge.rng_of_visible _ _ _ VFBS).
    + right. exact (lib.A.ProgBridge.rng_of_visible _ _ _ VWSH2).
    + apply lib.A.ProgBridge.rng_of_visible. apply VSTK; glp3_num.
    + right. exact (lib.A.ProgBridge.rng_of_visible _ _ _ VWSH).
    + apply lib.A.ProgBridge.rng_of_visible.
      eapply lib.A.ProgBridge.range_visible_sub; [exact VWSH | glp3_num | glp3_num | glp3_num].
    + exact (lib.A.ProgBridge.rng_of_visible _ _ _ (lib.A.ProgBridge.rt_vis_W W3)).
    + intros _. split.
      * exact (lib.A.ProgBridge.rng_of_visible _ _ _ VID).
      * apply lib.A.ProgBridge.rng_of_visible.
        eapply lib.A.ProgBridge.range_visible_sub; [exact VIDS | glp3_num | glp3_num | glp3_num].
  - exact (lib.A.ProgBridge.fp_avoids_RNG_W _).
  - (* G5: the continuation at the run's end state *)
    intros ms' md' HQ Hhid Hsbm.
    destruct HQ as (R & msh & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & MU1 & WM1 & RWS1 &
      MU2 & WM2 & RO' & ST' & RWF' & RWI').
    subst ms'.
    (* P3F states the run's registers with the getr it binds; the cuts read lib.Reusable.YK11.getr (same body) *)
    repeat match goal with H : ?g R ?i = ?v |- _ =>
      lazymatch g with lib.Reusable.YK11.getr => fail | _ => change (lib.Reusable.YK11.getr R i = v) in H end end.
    assert (Hhid' : forall x : word, lib.Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x)
      by (intros x Hx; exact (Hhid x Hx)).
    clear Hhid.
    change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs (lib.A.ACtlCut.cut_pc C_A81b80) R m' md')
              (POST cx)).
    (* the run's write set, joined: the 29 frame-shadow bytes, the callee windows, the object, first.sroa.7 *)
    assert (MUall : lib.Lib.Frame.munch
                      [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                       (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem3 m').
    { apply (lib.Lib.Frame.munch_trans _ mem3 msh m').
      - eapply lib.Lib.Frame.munch_weaken; [| exact MU1]. intros x Hx. cbn [lib.Lib.Frame.outside] in *.
        repeat split; glp3_num.
      - eapply lib.Lib.Frame.munch_weaken; [| exact MU2]. intros x Hx. cbn [lib.Lib.Frame.outside] in *.
        repeat split; glp3_num. }
    assert (WMall : lib.Lib.Frame.wmono lib.A.Img0.rsegs mem3 m')
      by (eapply lib.Lib.Frame.wmono_trans; [exact WM1 | exact WM2]).
    assert (E9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
    (* the stored shadow bytes, kept by the two calls *)
    assert (HB29 : lib.Lib.Mem.bytes_at lib.A.Img0.rsegs m' (lib.A.ACtlCutP.Sfr fr + 336)
                     (lib.Lib.Cells.cells_bytes (lib.A.Prog.Seg.P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
    { destruct RWS1 as ((_ & HBs) & _).
      eapply lib.Lib.Frame.bytes_at_transport; [exact HBs | exact MU2 |].
      change (Z.of_nat (length (lib.Lib.Cells.cells_bytes (lib.A.Prog.Seg.P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22
                                                                              b23)))) with 29.
      glp3_off. }
    assert (HB29l : length (lib.Lib.Cells.cells_bytes (lib.A.Prog.Seg.P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))
                    = 29%nat) by reflexivity.
    (* every written byte is a byte of m' *)
    assert (RDW : forall x : word,
              ~ lib.Lib.Frame.outside
                  [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                   (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] (bv_unsigned x) ->
              exists b, m' x = Some b).
    { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      assert (Hhi : 6283264 <= bv_unsigned x).
      { destruct (lib.A.Prog.Seg.P3.p3_in4 (lib.A.ACtlCutP.Sfr fr + 336) (lib.A.ACtlCutP.Sfr fr + 365)
                    (sp - 2224) sp (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) (bv_unsigned x))
          as [Hi | [Hi | [Hi | [Hi | Ho]]]]; [glp3_num | glp3_num | glp3_num | glp3_num | exfalso; exact (Hx Ho)]. }
      assert (Hrd : exists b, lib.Lib.Mem.mrd lib.A.Img0.rsegs m' (lib.Lib.Mem.wa (bv_unsigned x)) = Some b).
      { destruct (lib.A.Prog.Seg.P3.p3_in4 (lib.A.ACtlCutP.Sfr fr + 336) (lib.A.ACtlCutP.Sfr fr + 365)
                    (sp - 2224) sp (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) (bv_unsigned x))
          as [Hi | [Hi | [Hi | [Hi | Ho]]]].
        - exact (lib.A.Prog.Seg.R3.r3_ba_rd m' _ _ (bv_unsigned x) HB29 ltac:(rewrite HB29l; lia)).
        - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs (bv_unsigned x) Hi)).
        - exact (lib.A.Prog.Seg.R3.r3_rd_rw m' (fr + 2688) 38 _ (bv_unsigned x) RWI' ltac:(lia)).
        - exact (lib.A.Prog.Seg.R3.r3_rd_rw m' (fr + 2880) 35 _ (bv_unsigned x) RWF' ltac:(lia)).
        - exfalso. exact (Hx Ho). }
      destruct Hrd as (b & Hb). unfold lib.Lib.Mem.wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb.
      exists b. exact (lib.A.ACtlG.R3.glr3_mrd_hi m' x b Hhi Hb). }
    (* the runtime cells and the shadow across the write set *)
    assert (AC' : lib.A.AsanRT.asan_cells m').
    { apply (lib.A.AsanRTFacts.asan_cells_kept _ mem3 m' HAC MUall). glp3_off. }
    (* route (C): every shadow byte of the run's write set is a stored one; the cut's two regions move to m' *)
    assert (HSTall : forall a, lib.A.AsanRT.in_shadow a ->
              lib.Lib.Frame.outside
                [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                 (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] a \/
              exists b, lib.Lib.Mem.mrd lib.A.Img0.rsegs m' (lib.Lib.Mem.wa a) = Some b).
    { intros a Ha.
      destruct (lib.A.Prog.Seg.P3.p3_in4 (lib.A.ACtlCutP.Sfr fr + 336) (lib.A.ACtlCutP.Sfr fr + 365)
                  (sp - 2224) sp (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) a)
        as [Hi | [Hi | [Hi | [Hi | Ho]]]].
      - right. exact (lib.A.Prog.Seg.R3.r3_ba_rd m' _ _ a HB29 ltac:(rewrite HB29l; lia)).
      - exfalso. glp3_num.
      - exfalso. glp3_num.
      - exfalso. glp3_num.
      - left. exact Ho. }
    pose proof (lib.A.Prog.Seg.R3Fon.r3on_shadow_rw_on _ _ mem3 m' Hcut MUall WMall HSTall) as Hcut'.
    pose proof (lib.A.Prog.Seg.R3Fon.r3on_shadow_rw_on _ _ mem3 m' Himg MUall WMall HSTall) as Himg'.
    apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
    + (* the journal across the run: write set = the four ranges of the joined munch *)
      eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS lib.A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a => ~ lib.Lib.Frame.outside
                                 [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                                  (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] a);
        [exact HJ | | | exact Hhid' | exact Hsbm |].
      * intros x Hx. cbv beta in Hx.
        destruct (lib.A.Prog.Seg.R3.r3_out_dec
                    [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                     (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] (bv_unsigned x)) as [Ho | Hno];
          [| exfalso; exact (Hx Hno)].
        unfold lib.Reusable.YK04.mrestrict. rewrite (MUall x Ho). reflexivity.
      * unfold lib.Reusable.YK1b.mem_grows. intros x. unfold lib.Reusable.YK04.mrestrict.
        destruct (lib.Reusable.YA0n.w_H W3 x); [tauto|].
        intros Hx.
        destruct (lib.A.Prog.Seg.R3.r3_out_dec
                    [(lib.A.ACtlCutP.Sfr fr + 336, lib.A.ACtlCutP.Sfr fr + 365); (sp - 2224, sp);
                     (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] (bv_unsigned x)) as [Ho | Hno].
        -- rewrite (MUall x Ho). exact Hx.
        -- destruct (RDW x Hno) as (b & Hb). rewrite Hb. discriminate.
      * intros a Ha. cbv beta in Ha.
        destruct (lib.A.Prog.Seg.P3.p3_in4 (lib.A.ACtlCutP.Sfr fr + 336) (lib.A.ACtlCutP.Sfr fr + 365)
                    (sp - 2224) sp (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) a)
          as [Hi | [Hi | [Hi | [Hi | Ho]]]].
        -- right; right; right. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
           right. rewrite Efr3, Efs. glp3_num.
        -- left. glp3_num.
        -- right; right; right. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
           left. rewrite Efr3, Efs. glp3_num.
        -- right; right; right. exists 6, (lib.A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
           left. rewrite Efr3, Efs. glp3_num.
        -- exfalso. exact (Ha Ho).
    + (* frames: own6 on both cuts *)
      exact HF.
    + (* the frame law: own6 on both cuts *)
      exact HL.
    + (* the event bound: kmax 14 on both cuts *)
      exact Hk.
    + (* the exit body, C_A81b80 (ACtlCutP.v:1789-1820) *)
      cbv beta iota delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A81b80].
      (* the shadow sub-lists the exit's addressable ranges read *)
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 0 5 HB29 ltac:(rewrite HB29l; lia)) as Bid.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 10 9 HB29 ltac:(rewrite HB29l; lia)) as Bfg.
      pose proof (lib.A.Prog.Seg.R3.r3_ba_sub m' _ _ 24 5 HB29 ltac:(rewrite HB29l; lia)) as Bfb.
      unfold lib.A.Prog.Seg.P3.p3_shc in Bid, Bfg, Bfb.
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app firstn skipn] in Bid, Bfg, Bfb.
      replace (lib.A.ACtlCutP.Sfr fr + 336 + Z.of_nat 0) with (lib.A.ACtlCutP.Sfr fr + 336) in Bid by lia.
      replace (lib.A.ACtlCutP.Sfr fr + 336 + Z.of_nat 10) with (lib.A.ACtlCutP.Sfr fr + 346) in Bfg by lia.
      replace (lib.A.ACtlCutP.Sfr fr + 336 + Z.of_nat 24) with (lib.A.ACtlCutP.Sfr fr + 360) in Bfb by lia.
      pose proof (HADDR m' Bid) as HAD38.
      pose proof (HADDRf m' Bfb) as HAD35.
      assert (HAD72 : lib.A.AsanRT.addressable m' (fr + 2768) 72).
      { apply (lib.A.Prog.Seg.R3.r3_addr_z m' (fr + 2768) 9 72);
          [reflexivity | lia | glp3_num | glp3_num | intros i Hi; glp3_num |].
        replace (lib.A.AsanRT.shadow_addr (fr + 2768)) with (lib.A.ACtlCutP.Sfr fr + 346) by glp3_num. exact Bfg. }
      split; [exact HP|].
      split.
      { (* FRAC at the new memory, walked conjunct by conjunct as glue R3.v does (no conjunct named by position, so
           a conjunct appended to FRAC needs no edit here). *)
        apply (lib.A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact K2 | exact K3 | exact K4 | exact K8
                                                                      | exact K9 | exact K19 | exact K26].
        pose proof HFw as HFd. cbv beta in HFd. decompose [and] HFd.
        exists A, sp. cbv beta.
        repeat lazymatch goal with |- _ /\ _ => split end.
        all: first
          [ assumption
          | lazymatch goal with
            | |- context [lib.A.ACtlCutP.saved_bytes] =>
                eapply lib.Lib.Frame.bytes_at_transport; [eassumption | exact MUall |];
                replace (Z.of_nat (length (lib.A.ACtlCutP.saved_bytes cx))) with 104
                  by (unfold lib.A.ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity);
                glp3_off
            | |- exists _, _ =>
                assert (Hst : lib.Lib.Frame.stk lib.A.Img0.rsegs m' (lib.A.ACtlCutP.Sfr fr)
                                (lib.A.ACtlCutP.Sfr fr + 392))
                  by (split; [glp3_num|]; split; [glp3_num|]; intros a Ha; refine (Hcut' a _ _); [apply HFR|]; glp3_num);
                destruct (lib.Lib.Frame.stk_bytes lib.A.Img0.rsegs m' _ _ Hst ltac:(lia)) as (bs & Hl & Hb);
                exists bs; split; [exact Hb|]; rewrite Hl;
                replace (lib.A.ACtlCutP.Sfr fr + 392 - lib.A.ACtlCutP.Sfr fr) with 392 by lia; reflexivity
            | |- _ => eapply (lib.A.ACtlG.R3.glr3_q64 _ mem3 m'); [eassumption | exact MUall | glp3_off]
            end ]. }
      split; [exact Hn|].
      split.
      { unfold lib.A.ACtlCutP.OURb in *. eapply lib.Lib.Frame.bytes_at_transport; [exact HOUR | exact MUall |].
        rewrite lib.A.Prog.SlotModel.OUR_length. glp3_off. }
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|]. unfold lib.A.ACtlCut.rgv in *.
        split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
      split.
      { (* PRO: its spills, our[]'s 6 bytes, and the input block (off the frame, the stack and the shadow) *)
        destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pnad & P184 & P256 &
          P264 & P272 & _).
        destruct HB as ((_ & _ & _ & _ & Hpn & Hnl & _) & _).
        assert (Hblk : (lib.A.ACtlCut.c_n cx = 0 /\ lib.A.ACtlCut.c_p cx = lib.A.ACfn.A_EMPTY) \/
                       (0 < lib.A.ACtlCut.c_n cx /\ lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx + 28672 < sp /\
                        4096 <= lib.A.ACtlCut.c_p cx /\
                        (lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx <= 0x7fff7000 \/
                         0x10007fff8000 <= lib.A.ACtlCut.c_p cx) /\
                        (lib.A.ACtlCut.c_p cx + lib.A.ACtlCut.c_n cx <= fr \/ fr + 4096 <= lib.A.ACtlCut.c_p cx))).
        { destruct Hpn as [Hz | (Hn0 & Hinb)]; [left; exact Hz | right].
          assert (Hinb3 : In (lib.A.ACtlCut.c_p cx, lib.A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
            by exact (Permutation_in _ (Permutation_sym HP) Hinb).
          destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb3)
            as (_ & Hb4096 & Hbceil & Hbapp & _).
          pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6
                        (lib.A.ACtlCut.c_fpos cx) HAR Hinb3 Hin) as Hsep.
          rewrite Efr3, Efs in Hsep.
          assert (Ereq : lib.Reusable.YG00.req_size (lib.A.ACtlCut.c_n cx) = lib.A.ACtlCut.c_n cx).
          { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (lib.A.ACtlCut.c_n cx) 0); lia. }
          rewrite Ereq in Hbceil, Hbapp, Hsep.
          unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
            lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.zdisjoint in Hbapp, Hsep. cbn [fst snd] in Hsep.
          unfold lib.A.ACfn.LLVMF_STK in Hstklo. lia. }
        assert (Hinl : Z.of_nat (length (lib.A.ACtlCut.c_in cx)) = lib.A.ACtlCut.c_n cx) by lia.
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P40]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P120]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P136]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P160]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P168]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P176]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P208]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P248]|].
        split; [apply (lib.A.Prog.Seg.R3.r3_addr_keep _ mem3 m' _ _ Pad MUall); intros i Hi; glp3_off|].
        split.
        { eapply lib.Lib.Frame.bytes_at_transport; [exact Pin | exact MUall |]. rewrite Hinl. glp3_off. }
        split.
        { intros Hn0. apply (lib.A.Prog.Seg.R3.r3_addr_keep _ mem3 m' _ _ (Pnad Hn0) MUall). intros i Hi. glp3_off. }
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P184]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P256]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P264]|].
        split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                      | exact MUall | glp3_off | exact P272]|].
        eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                | exact MUall | glp3_off | exact P32]. }
      split; [eapply (lib.A.ACtlG.R3.glr3_spill _ regs3 R mem3 m' A); [exact H9 | lia | lia | lia | exact E9
                                                                    | exact MUall | glp3_off | exact S144]|].
      split.
      { replace (fr + 2691) with (fr + 2688 + 3) by lia.
        apply (lib.A.Prog.Seg.P3.p3_addr_sub m' (fr + 2688) 38 3 17 HAD38); lia. }
      split; [unfold lib.A.ACtlCutP.fragb; exact HAD72|].
      split; [exact HAD38|].
      split.
      { unfold lib.A.ACtlCutP.IDBe. destruct RWI' as ((_ & Hb) & _).
        cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
      exists (fr + 2768), sp, A, junk.
      cbv zeta.
      split; [etransitivity; [exact K2 | exact H2]|].
      split; [etransitivity; [exact K9 | exact H9]|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split.
      { eapply lib.Lib.Frame.rw_cells_transport; [exact RW192 | exact MUall | exact WMall |].
        cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. glp3_off. }
      split.
      { eapply lib.Lib.Frame.rw_cells_transport; [exact RWd | exact MUall | exact WMall |].
        cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. glp3_off. }
      split; [exact HAD72|].
      split; [right; glp3_num|].
      split; [glp3_num|].
      split; [glp3_num|].
      split; [glp3_num|].
      split; [intros x Hx; glp3_off|].
      split; [intros x Hx; glp3_off|].
      split.
      { intros A1 HA1' HA1r x Hx.
        assert (EA1 : A1 = A).
        { apply (glp3_eq64 (lib.Reusable.YK11.getr R 9)); [exact HA1' | etransitivity; [exact K9 | exact H9]
                                                        | lia | lia]. }
        subst A1. glp3_off. }
      split.
      { intros A1 HA1' HA1r x Hx.
        assert (EA1 : A1 = A).
        { apply (glp3_eq64 (lib.Reusable.YK11.getr R 9)); [exact HA1' | etransitivity; [exact K9 | exact H9]
                                                        | lia | lia]. }
        subst A1. glp3_off. }
      split; [intros x Hx; glp3_off|].
      split; [intros x Hx; glp3_off|].
      split; [intros x Hx; rewrite lib.A.Prog.SlotModel.OUR_length in Hx; glp3_off|].
      split.
      { cbn [lib.A.AsanRTFacts.all_app]. unfold lib.A.AsanRTFacts.app_ivl.
        repeat split; try (intros a Ha; glp3_num). }
      split.
      { unfold lib.A.ACtlCutP.rt_disjoint.
        unfold lib.A.AsanRT.RT_GOT_AF, lib.A.AsanRT.RT_AF, lib.A.AsanRT.RT_GOT_VERB, lib.A.AsanRT.RT_VERB,
          lib.A.AsanRT.RT_GOT_CF, lib.A.AsanRT.RT_CF, lib.A.AsanRT.RT_TSDI, lib.A.AsanRT.RT_TSDK,
          lib.A.AsanRT.RT_PGSZ, lib.A.AsanRT.RT_TP, lib.A.AsanRT.RT_TSDMAIN, lib.A.AsanRT.RT_REAL_LO,
          lib.A.AsanRT.RT_REAL_HI, lib.A.AsanRT.RT_IMAP, lib.A.AsanRT.RT_IMEM, lib.A.AsanRT.RT_MUG,
          lib.A.AsanRT.RT_AGLOB, lib.A.AsanRT.RT_AGLOB_LEN.
        cbn [lib.Lib.Frame.disjoint_from]. repeat split; glp3_num. }
      split; [reflexivity|].
      split; [apply (lib.A.ACtlG.R3.glr3_q64 _ mem3 m' _ _ Q280 MUall); glp3_off|].
      split; [apply (lib.A.ACtlG.R3.glr3_q64 _ mem3 m' _ _ Q240 MUall); glp3_off|].
      split.
      { exists jy, junk2. split.
        - eapply lib.Lib.Frame.rw_cells_transport; [exact RWjy | exact MUall | exact WMall |].
          cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. glp3_off.
        - eapply lib.Lib.Frame.rw_cells_transport; [exact RWj2 | exact MUall | exact WMall |].
          cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. glp3_off. }
      exact HAD35.
    + (* ctl_rt *)
      split; [exact AC' | split; [exact Hcut' | split; [exact Himg' | exact RO']]].
Qed.

End GlueP3.
