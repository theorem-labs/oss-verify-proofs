(* lib/A/ACtlG/F7.v -- GLUE for stage seg_F7 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:764) (an earlier version, blob c4edf0be7fe, not in this delivery)).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_F7 : forall POST (j : nat), CF POST (ix_cut C_A81f7c_at [Z.of_nat j]) ->
                                          CF POST (ix_cut C_A81f64_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F7.  Segment F7 is 0x81f64 -> 0x81f7c (Seg/F7.v:1-12): two compares not taken, the two
   parse-record loads, and the FIRST reac_ctrl_kind_name call at 0x81f78.

   ROUTE (C) (L3 switch onto a working branch 1899bed1aee; L3 brief L3-brief.md (a working note, not in this delivery),
   recipe a Theorem Labs lane's L3-recipe.md (a working note, not in this delivery)).  The cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 in place of ctl_rt mem3.
   The segment's footprint run is the route (C) twin lib/A/Prog/Seg/F7Fon.v f7_evt_F_on (this lane's beside-file;
   a Theorem Labs lane's F7F.v (not in this delivery) unchanged): the callee premise is reac_ctrl_kind_name_contract_F_on, the run has no
   shadow_rw premise, and the run SPANS the call.  So this file
     - SUPPLIES that premise with the callee's closed theorem A.Prog.reac_ctrl_kind_nameF.reac_ctrl_kind_name_holds_F_on
       (a Theorem Labs lane 330e60af39d, LANDED, a Theorem Labs lane SIGNED 12:04Z), and
     - lifts the WHOLE run ONCE with Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).
   There is NO split at the call and THIS STAGE CITES NO LIFT: an <f>_SRr_at starts at the callee entry and
   takes the callee contract as its own premise, so citing it to discharge that premise would be circular.

   THE PROOF, step by step
   G1  unfold the entry cut: ix_cut's index equation, then C_A81f64_at (ACtlCutP.v), whose body is FRAC and
       b5_body with that cut's P (b5_K, a0 = t_k, IDj, b5_F17, b5_W240, b5_PF).
   G2  the run's premises from the body and from ctl_rt_C's asan cells and ro_agree (its two shadow regions are
       not read: the run needs no shadow byte through a shadow_rw premise); every numeric bound from VISIBLE
       state only: 4096 <= fr and fr + 4096 <= alloc_ceiling from YCbq.frames_bounds on the journal's AR plus
       the shell's frame law and layout_le's ly_F; phi + a_size (flen) <= alloc_ceiling and
       c_p + c_n <= alloc_ceiling from the AR block law on the body's own live list; and
       alloc_ceiling + LLVMF_STK <= c_sp cx from the journal's astk_ok, with
       c_sp cx - 4096 < sp <= A <= c_sp cx - 416 from FRAC.  Together the callee window [sp-16, sp) lies
       strictly above the image, above every frame byte and above every live block, and inside the
       journal's [c_sp cx - LLVMF_STK, c_sp cx) presence window.
   G3  the cut's configuration in the run's state form (ProgBridge.cfg_at_MS), then the walk moved from the
       cut's register map regs3 to the run's canonical one (YA0nR.SRr_xregs_eqv, Regs6ss.mkR_of_eqv).
   G4  the lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then YA0nR.SRr_fevt_hid at
       RNG := ProgBridge.RNG_W (w_H W3); fp_avoids by ProgBridge.fp_avoids_RNG_W and each of the five
       ExecF.rng premises by ProgBridge.rng_of_visible from a range_visible fact; the KIND_NAME shadow range by
       kn_shadow_vis (below), from the core's AR_zshadow_law at the bundle's zero-shadow list.
   G5  the continuation: the run's end map IS the exit cut's map; the journal crosses the callee's window
       write by YCbq.ajournal_exec with Wr := [sp-16, sp) (awr_byte's stack case); every memory conjunct of the
       body moves by the kn_* helpers, which only ever need "this range ends below sp-16"; and ctl_rt_C at the
       exit is kept at the same state ly3 S3 (kn_rt_keep: the two shadow regions by A.ShadowRwOnK.fl_shadow_rw_on).

   SECTION HYPOTHESES (exact text at their declarations; both are ACtl.v's own Section hypotheses)
   - LAWS: the core's AR law record, ACtl.v:237.
   - TFIB_SYMS: the bundle's symbols A.AF0m.CtrlTSyms B, ACtl.v:252.  Its ts_zsh pins as_zero_shadow B to the
     record list A.AF0m.Tfib_zero_shadow, which kn_shadow_vis reads.
   The earlier Section hypothesis KN_SHADOW_VIS (the 14 shadow bytes of the KIND_NAME table are visible in the
   world) is GONE: kn_shadow_vis proves it from LAWS and TFIB_SYMS.  ctl_rt_C's img_shadow / (FA) / (Z) regions do
   not give it: they state that bytes are present in memory, and visibility is a fact about the world's hidden set.

   CITED BY NAME, NOT HYPOTHESES: A.Prog.Seg.F7Fon.f7_evt_F_on (this lane's twin of a Theorem Labs lane's F7F.f7_evt_F, its source not in this delivery);
   A.Prog.reac_ctrl_kind_nameF.reac_ctrl_kind_name_holds_F_on; Reusable.YA0nR.SRr_fevt_hid / SRr_xregs_eqv;
   A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / RNG_W / fp_avoids_RNG_W / rng_of_visible /
   img_vis_W; Reusable.YCbq.ajournal_exec / frames_bounds / asan_consts / find_segment_none;
   Reusable.YG0d.al_blocks / al_frames / AR_zshadow_law; A.AF0m.ts_zsh; A.ProgWorldVisFrame.vis_of_aview;
   A.ShadowRwOnK.fl_shadow_rw_on; the shared kit's A.ACtlG.Kit.kit_wx / kit_segs_low / kit_frac_move; and five
   frame-route-free helpers of lib/A/Prog/Seg/F7.v stated over SlotModel and Lib/Mem only (kn_len, f7_tID_len,
   f7_fsb_len, f7_bytes_firstn, f7_memcmp_firstn).

   SHADOWED NAMES: the two YK11 copies (lib/Reusable/YK11.v and lib/A/Reusable/YK11.v) are BOTH loaded here
   because the run file Requires the ASan-side one, so every core module named below is bound to its full
   path by a Module alias (CK11, CM05, ...).  Nothing writes a bare mkst / getr / seg_rom / cfg_at: check
   `grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F7.v` -- comments only.

   BUILD STATE: type-check on a working branch 1899bed1aee (glue-base line + a Theorem Labs lane's interim core, no stand-in in the
   closure), with the kind_name _on statement / proof files taken by path (reac_ctrl_kind_name_c.v from
   a Theorem Labs lane's 10bfa2d8569, reac_ctrl_kind_nameF.v from a Theorem Labs lane's 330e60af39d).  Every step is proved:
   no unproved step and no assumed constant. *)

From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every project module by its EXACT prefix: lib/A/Reusable, lib/A/Bz/Lib, lib/B/... and lib/AZ/Lib hold twins of
   several of these, so a partial `From ...lib Require Reusable.X` / `Lib.X` could name a twin. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YA0n YA0nR YG0f YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YG0n YG0v YC5d YCbq YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k AF0m Img0 AsanRT ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCut ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnK ACtlRtC ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_kind_name_c reac_ctrl_kind_nameF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F7Fon F7.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core modules, by FULL path: the ASan-side copies lib/A/Reusable/{YK11,YK1b,YM05,YO09,YI16,...} are
   loaded through the _F file, so a short qualid would be ambiguous. *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module CG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module CG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module CG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module CG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module CG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module CG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module CA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module CA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module CC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module CCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module EXF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module R6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module MST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.
Module KNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_nameF.
Module SegF7 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F7.
Module SegF7Fon := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F7Fon.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:165 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   HELPERS.  Each one transports a body conjunct across the callee's window write [lo, hi) = [sp-16, sp),
   which lies strictly above the image, above every frame byte and above every live block.  lib/A/ACtlG/F8.v
   Requires this file qualified and reuses them.  They are not kit material yet: they exist for the two
   kind-name stages, and the shared kit lib/A/ACtlG/Kit.v has a single writer (a Theorem Labs lane), to whom they
   are offered through a Theorem Labs lane if a third stage needs them (P11 calls the same callee). *)
Section KnHelpers.
Context {fx : CK11.FPState} {rc : CM05.RunCeil}.
Variable B : CG0f.asyms.

Lemma kn_bytes : forall (m m' : word -> option byte) (lo hi a : Z) (bs : list byte),
  FRM.munch [(lo, hi)] m m' ->
  (a + Z.of_nat (length bs) <= lo \/ hi <= a) ->
  MEM.bytes_at segs m a bs -> MEM.bytes_at segs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd Hb.
  apply (FRM.bytes_at_transport segs [(lo, hi)] m m' a bs Hb MU).
  cbn [FRM.disjoint_from]. split; [lia | exact I].
Qed.

Lemma kn_q : forall (m m' : word -> option byte) (lo hi a v : Z),
  FRM.munch [(lo, hi)] m m' -> (a + 8 <= lo \/ hi <= a) ->
  ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' lo hi a v MU Hd Hq.
  apply (kn_bytes m m' lo hi a _ MU); [rewrite MEM.length_le8; lia | exact Hq].
Qed.

Lemma kn_u32 : forall (m m' : word -> option byte) (lo hi a v : Z),
  FRM.munch [(lo, hi)] m m' -> (a + 4 <= lo \/ hi <= a) ->
  ACtlCutP.u32 m a v -> ACtlCutP.u32 m' a v.
Proof.
  intros m m' lo hi a v MU Hd Hq.
  apply (kn_bytes m m' lo hi a _ MU); [rewrite MEM.length_le4; lia | exact Hq].
Qed.

Lemma kn_u16 : forall (m m' : word -> option byte) (lo hi a v : Z),
  FRM.munch [(lo, hi)] m m' -> (a + 2 <= lo \/ hi <= a) ->
  ACtlCutP.u16 m a v -> ACtlCutP.u16 m' a v.
Proof.
  intros m m' lo hi a v MU Hd Hq.
  apply (kn_bytes m m' lo hi a _ MU); [rewrite MEM.length_le2; lia | exact Hq].
Qed.

Lemma kn_b8 : forall (m m' : word -> option byte) (lo hi a v : Z),
  FRM.munch [(lo, hi)] m m' -> (a + 1 <= lo \/ hi <= a) ->
  ACtlCutP.b8 m a v -> ACtlCutP.b8 m' a v.
Proof.
  intros m m' lo hi a v MU Hd Hq.
  apply (kn_bytes m m' lo hi a _ MU); [cbn [length]; lia | exact Hq].
Qed.

(* The shadow byte of an address at or below 2 ^ 47 is at or below HIGHMEM_BEG, hence below the window. *)
Lemma kn_sh_lt : forall a, 0 <= a -> a <= 2 ^ 47 -> ART.shadow_addr a <= ART.HIGHMEM_BEG.
Proof.
  intros a H0 H2. unfold ART.shadow_addr, ART.ASAN_K, ART.HIGHMEM_BEG.
  assert (Hd : a / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  change (2 ^ 44) with 17592186044416 in Hd. lia.
Qed.

Lemma kn_sh_nn : forall a, 0 <= a -> 0 <= ART.shadow_addr a.
Proof.
  intros a H0. unfold ART.shadow_addr, ART.ASAN_K.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma kn_shiftr_shadow : forall a, Z.shiftr a 3 + A.ACtlK.ASAN_K = ART.shadow_addr a.
Proof.
  intros a. unfold ART.shadow_addr, A.ACtlK.ASAN_K, ART.ASAN_K.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* addressable survives a window write that lies above every shadow byte of the range. *)
Lemma kn_addr : forall (m m' : word -> option byte) (lo hi p n : Z),
  FRM.munch [(lo, hi)] m m' -> ART.HIGHMEM_BEG + 4096 <= lo ->
  ART.addressable m p n -> ART.addressable m' p n.
Proof.
  intros m m' lo hi p n MU Hlo (Hp & Hn & He & HA).
  split; [exact Hp|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok).
  split; [exact Hap|]. exists b. split; [|exact Hok].
  assert (Hr : 0 <= p + i /\ p + i <= 2 ^ 47).
  { unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Hap.
    change (2 ^ 47) with 140737488355328. lia. }
  pose proof (kn_sh_lt (p + i) (proj1 Hr) (proj2 Hr)) as Hs.
  pose proof (kn_sh_nn (p + i) (proj1 Hr)) as Hs0.
  unfold MEM.mrd in *.
  assert (Em : m' (MEM.wa (ART.shadow_addr (p + i))) = m (MEM.wa (ART.shadow_addr (p + i)))).
  { apply MU. rewrite MEM.wa_unsigned by (unfold ART.HIGHMEM_BEG in Hs; lia).
    cbn [FRM.outside]. split; [lia | exact I]. }
  rewrite Em. exact Hb.
Qed.

(* Register 9 pins its value only mod 2 ^ 64, so two in-range readings agree. *)
Lemma kn_A9 : forall (regs : bvmap 5 word) (A A' : Z),
  ACtlCut.rgv regs 9 A -> ACtlCut.rgv regs 9 A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H H' HA HA'. unfold ACtlCut.rgv in H, H'.
  assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- H'; exact H).
  apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !MST.unsigned_lit in E by lia. exact E.
Qed.

(* The base of a carried `spill` is the cut's own A (Seg/F7.v:74-89, restated over ACtlCutP's names). *)
Lemma kn_spill_base : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA64 Hoff (A' & HA' & Hq').
  pose proof Hq' as Hq2. unfold ACtlCutP.q64, MEM.bytes_at in Hq2. destruct Hq2 as (Hb0 & Hb1 & _).
  rewrite MEM.length_le8 in Hb1. change (Z.of_nat 8) with 8 in Hb1.
  unfold ACtlCut.rgv in HA', H9.
  assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- HA'; exact H9).
  apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in E.
  rewrite (Z.mod_small A (2 ^ 64)) in E by lia.
  pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm.
  rewrite E in Hdm.
  assert (Hq0 : A' / 2 ^ 64 = 0) by lia.
  rewrite Hq0 in Hdm.
  assert (EA : A' = A) by lia.
  subst A'. exact Hq'.
Qed.

Lemma kn_spill : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (lo hi A off v : Z),
  ACtlCut.rgv regs 9 A -> CK11.getr regs' 9 = CK11.getr regs 9 ->
  0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 416 -> hi <= A ->
  FRM.munch [(lo, hi)] m m' ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' lo hi A off v H9 E9 HA0 HA64 Hoff Hhi MU Hs.
  exists A. split.
  - exact (eq_trans E9 H9).
  - apply (kn_q m m' lo hi (A + off) v MU); [right; lia|].
    exact (kn_spill_base regs m A off v H9 HA0 HA64 Hoff Hs).
Qed.

(* mkR_of in the explicit 31-slot form the footprint runs are stated over. *)
Lemma kn_mkR_of : forall regs : bvmap 5 word, R6.mkR_of regs =
  FRM.mkR (CK11.getr regs 1) (CK11.getr regs 2) (CK11.getr regs 3) (CK11.getr regs 4) (CK11.getr regs 5)
    (CK11.getr regs 6) (CK11.getr regs 7) (CK11.getr regs 8) (CK11.getr regs 9) (CK11.getr regs 10)
    (CK11.getr regs 11) (CK11.getr regs 12) (CK11.getr regs 13) (CK11.getr regs 14) (CK11.getr regs 15)
    (CK11.getr regs 16) (CK11.getr regs 17) (CK11.getr regs 18) (CK11.getr regs 19) (CK11.getr regs 20)
    (CK11.getr regs 21) (CK11.getr regs 22) (CK11.getr regs 23) (CK11.getr regs 24) (CK11.getr regs 25)
    (CK11.getr regs 26) (CK11.getr regs 27) (CK11.getr regs 28) (CK11.getr regs 29) (CK11.getr regs 30)
    (CK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* FRAC (ACtlCutP.v:982-996) at a NEW MEMORY, across the window write [lo, hi), which lies above the whole
   class-6 frame slot [fr, fr + 4096) (fs_frame_bytes 6 = 4096), above every shadow byte of an address below
   2 ^ 47, and at or below the cut's own sp.  This RE-ESTABLISHES FRAC (it does not only read it), so the
   step walks FRAC's conjuncts GENERICALLY: it splits the record and dispatches each conjunct on its SHAPE
   (syntactic matching only, so no memory fact is ever compared with another by conversion, which unfolds the
   image's segment list and does not terminate in practice): a q64 word or a byte list moves by the window
   transport kn_q / kn_bytes with an lia side condition, the frame-shadow existential by its own closer, and
   every register or arithmetic conjunct is its own hypothesis.  No conjunct is named, so a conjunct appended
   to FRAC later is handled with no edit when it is one of those shapes: a Theorem Labs lane's FRAC batch trailer
   `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))` is a q64 word with
   fr + 4088 + 8 = fr + 4096 <= lo, so the q64 case keeps it. *)
Lemma kn_frac_mem_keep : forall (cx : ACtlCut.ctlcx) (fr sel lo hi : Z) (regs : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  FRM.munch [(lo, hi)] m m' ->
  fr + 4096 <= lo -> ART.HIGHMEM_BEG + 4096 <= lo -> hi <= CG0d.spZ regs ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel lo hi regs m m' (A & sp & HF) MU Hfr Hhm Hhi.
  exists A, sp.
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         end.
  assert (EFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (EAPP : ART.APPMEM_END = 140737488355328) by reflexivity.
  assert (Hfrnn : 0 <= fr).
  { lazymatch goal with H : ACtlCutP.q64 m fr _ |- _ =>
      pose proof H as Hq; unfold ACtlCutP.q64, MEM.bytes_at in Hq; exact (proj1 Hq) end. }
  assert (Hfr47 : fr <= 2 ^ 47) by (change (2 ^ 47) with 140737488355328; lia).
  assert (Hsh : ART.shadow_addr fr <= ART.HIGHMEM_BEG) by (apply kn_sh_lt; [exact Hfrnn | exact Hfr47]).
  (* one tactic expression, so the closer is internalized while m, m' are in the focused goal's context *)
  (repeat match goal with |- _ /\ _ => split end);
  lazymatch goal with
    | |- ACtlCutP.q64 m' ?a ?v =>
        lazymatch goal with H : ACtlCutP.q64 m a v |- _ =>
          apply (kn_q m m' lo hi a v MU); [lia | exact H] end
    | |- MEM.bytes_at _ m' ?a ?bs =>
        lazymatch goal with H : MEM.bytes_at _ m a bs |- _ =>
          apply (kn_bytes m m' lo hi a bs MU); [lia | exact H] end
    | |- exists _, _ =>
        lazymatch goal with
        | Hl : length ?w = Z.to_nat ACtlCutP.FRAME_SHADOW, H : MEM.bytes_at _ m (ACtlCutP.Sfr fr) ?w |- _ =>
            exists w; split; [|exact Hl];
            apply (kn_bytes m m' lo hi _ w MU); [|exact H];
            left; rewrite Hl; unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW; rewrite EFB;
            change (Z.to_nat (3136 / 8)) with 392%nat; change (Z.of_nat 392) with 392; lia
        end
    | |- _ => match goal with H : ?G |- ?G => exact H end
    end.
Qed.

(* FRAC across the window write AND the run's register map: the memory step above, then the kit's register
   move A.ACtlG.Kit.kit_frac_move (registers 2 3 4 8 9 19 26, which FRAC reads), whose proof rewrites the
   whole record and so is also indifferent to an appended conjunct. *)
Lemma kn_frac_keep : forall (cx : ACtlCut.ctlcx) (fr sel lo hi : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 3 = CK11.getr regs 3 ->
  CK11.getr regs' 4 = CK11.getr regs 4 -> CK11.getr regs' 8 = CK11.getr regs 8 ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 19 = CK11.getr regs 19 ->
  CK11.getr regs' 26 = CK11.getr regs 26 ->
  FRM.munch [(lo, hi)] m m' ->
  fr + 4096 <= lo -> ART.HIGHMEM_BEG + 4096 <= lo -> hi <= CG0d.spZ regs ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros cx fr sel lo hi regs regs' m m' HF E2 E3 E4 E8 E9 E19 E26 MU Hfr Hhm Hhi.
  exact (A.ACtlG.Kit.kit_frac_move B cx fr sel regs regs' m'
           (kn_frac_mem_keep cx fr sel lo hi regs m m' HF MU Hfr Hhm Hhi) E2 E3 E4 E8 E9 E19 E26).
Qed.

(* ctrl's ACtlCutP.flen is SlotModel's t_len; the two facts Seg/F7.v proves over SlotInv's ghost. *)
Lemma kn_8819_big : forall (cx : ACtlCut.ctlcx) (j : nat),
  SM.t_8819 (ACtlCut.c_in cx) j = true -> 50 <= ACtlCutP.flen cx j.
Proof.
  intros cx j H. unfold ACtlCutP.flen. unfold SM.t_8819 in H.
  apply andb_prop in H as (H & _). apply andb_prop in H as (H & _).
  unfold SM.t_big in H. apply Z.leb_le in H. exact H.
Qed.

Lemma kn_tphi_len : forall (cx : ACtlCut.ctlcx) (j : nat),
  (length (SM.t_phi (ACtlCut.c_in cx) j) <= Z.to_nat (ACtlCutP.flen cx j))%nat.
Proof.
  intros cx j. unfold ACtlCutP.flen, SM.t_phi, SM.t_len, SM.f_phi.
  rewrite length_firstn. lia.
Qed.

Lemma kn_tg_len : forall (inp : list byte) (j : nat), length (SM.t_g inp j) = 50%nat.
Proof. intros inp j. unfold SM.t_g. apply SM.fr50_length. Qed.

(* The carried part of the two kind-name cuts' bodies, across the window write. *)
Lemma kn_core_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr lo hi A : Z)
    (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  ACtlCutP.HB m phi (ACtlCutP.flen cx j) /\ ACtlCutP.FLSI cx j fr regs m /\
  ACtlCutP.LK cx fr j regs m /\ ACtlCutP.b5_C cx j phi fr regs m /\
  ACtlCutP.b5_K cx j phi fr regs m /\ ACtlCutP.IDj cx fr j m /\
  ACtlCutP.b5_F17 cx j phi fr regs m /\ ACtlCutP.b5_W240 cx j regs m /\
  ACtlCutP.b5_PF cx j phi fr regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 < 2 ^ 64 ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 20 = CK11.getr regs 20 -> CK11.getr regs' 21 = CK11.getr regs 21 ->
  CK11.getr regs' 22 = CK11.getr regs 22 -> CK11.getr regs' 23 = CK11.getr regs 23 ->
  CK11.getr regs' 24 = CK11.getr regs 24 -> CK11.getr regs' 25 = CK11.getr regs 25 ->
  CG0d.spZ regs' = CG0d.spZ regs ->
  FRM.munch [(lo, hi)] m m' -> FRM.wmono segs m m' ->
  ART.HIGHMEM_BEG + 4096 <= lo -> lo <= 2 ^ 47 -> hi <= A ->
  fr + ACtlCutP.FRAME_BYTES <= lo ->
  phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= lo ->
  ACtlCut.c_p cx + ACtlCut.c_n cx <= lo ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  KNA.KIND_NAME + 112 <= lo ->
  ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\ ACtlCutP.FLSI cx j fr regs' m' /\
  ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.b5_C cx j phi fr regs' m' /\
  ACtlCutP.b5_K cx j phi fr regs' m' /\ ACtlCutP.IDj cx fr j m' /\
  ACtlCutP.b5_F17 cx j phi fr regs' m' /\ ACtlCutP.b5_W240 cx j regs' m' /\
  ACtlCutP.b5_PF cx j phi fr regs' m'.
Proof.
  intros cx j phi fr lo hi A regs regs' m m'
    (HHB & HFLSI & HLK & HbC & HbK & HIDj & HF17 & HW240 & HPF)
    H9 HAb HA416 E9 E18 E20 E21 E22 E23 E24 E25 Esp MU WM Hhm Hlo47 Hhi Hfr Hphi Hin Hinlen Hkn.
  pose proof Hfr as Hfr'. unfold ACtlCutP.FRAME_BYTES in Hfr'.
  assert (Hphi0 : 0 <= phi) by (destruct HHB as (_ & Had); exact (proj1 Had)).
  assert (Ksp : forall off v, ACtlCutP.spill regs m off v -> 0 <= off <= 416 ->
                  ACtlCutP.spill regs' m' off v).
  { intros off v Hs Hoff.
    exact (kn_spill regs regs' m m' lo hi A off v H9 E9 ltac:(lia) HA416 Hoff Hhi MU Hs). }
  assert (Kq : forall off v, ACtlCutP.q64 m (A + off) v -> 0 <= off -> ACtlCutP.q64 m' (A + off) v).
  { intros off v Hq Hoff. apply (kn_q m m' lo hi _ _ MU); [right; lia | exact Hq]. }
  assert (Kad : forall p n, ART.addressable m p n -> ART.addressable m' p n).
  { intros p n Ha. exact (kn_addr m m' lo hi p n MU Hhm Ha). }
  assert (Kfr : forall a bs, MEM.bytes_at segs m a bs -> fr <= a ->
                  a + Z.of_nat (length bs) <= fr + 3136 -> MEM.bytes_at segs m' a bs).
  { intros a bs Hbs Ha Hb. apply (kn_bytes m m' lo hi a bs MU); [left; lia | exact Hbs]. }
  assert (Kph : forall a bs, MEM.bytes_at segs m a bs -> phi <= a ->
                  a + Z.of_nat (length bs) <= phi + A.ACtlK.a_size (ACtlCutP.flen cx j) ->
                  MEM.bytes_at segs m' a bs).
  { intros a bs Hbs Ha Hb. apply (kn_bytes m m' lo hi a bs MU); [left; lia | exact Hbs]. }
  assert (Ksh : forall a, 0 <= a -> a < lo ->
                  ACtlCutP.b8 m (Z.shiftr a 3 + A.ACtlK.ASAN_K) 0 ->
                  ACtlCutP.b8 m' (Z.shiftr a 3 + A.ACtlK.ASAN_K) 0).
  { intros a Ha Hb Hbs. apply (kn_b8 m m' lo hi _ _ MU); [|exact Hbs].
    left. rewrite kn_shiftr_shadow.
    pose proof (kn_sh_lt a Ha ltac:(lia)) as Hs. unfold ART.HIGHMEM_BEG in Hhm, Hs. lia. }
  split.
  { destruct HHB as (Hnz & Had). split; [exact Hnz | exact (Kad _ _ Had)]. }
  split.
  { destruct HFLSI as ((HPRO & S128 & HSTK & S144 & HAD17) & S216 & S224 & S248 & (HINa & HINb) & HFLC).
    destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PAd & PIn & PInb &
      P184 & P256 & P264 & P272 & P32).
    destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CA72 & CA38 & C72 & C64 & C56 & C48).
    split.
    { split.
      { split; [exact (Ksp _ _ P40 ltac:(lia))|].
        split; [exact (Ksp _ _ P120 ltac:(lia))|].
        split; [exact (Ksp _ _ P136 ltac:(lia))|].
        split; [exact (Ksp _ _ P160 ltac:(lia))|].
        split; [exact (Ksp _ _ P168 ltac:(lia))|].
        split; [exact (Ksp _ _ P176 ltac:(lia))|].
        split; [exact (Ksp _ _ P208 ltac:(lia))|].
        split; [exact (Ksp _ _ P248 ltac:(lia))|].
        split; [exact (Kad _ _ PAd)|].
        split.
        { apply (kn_bytes m m' lo hi (ACtlCut.c_p cx) (ACtlCut.c_in cx) MU);
            [left; rewrite Hinlen; lia | exact PIn]. }
        split.
        { intros Hn. exact (Kad _ _ (PInb Hn)). }
        split; [exact (Ksp _ _ P184 ltac:(lia))|].
        split; [exact (Ksp _ _ P256 ltac:(lia))|].
        split; [exact (Ksp _ _ P264 ltac:(lia))|].
        split; [exact (Ksp _ _ P272 ltac:(lia)) | exact (Ksp _ _ P32 ltac:(lia))]. }
      split; [exact (Ksp _ _ S128 ltac:(lia))|].
      split.
      { apply (FRM.stk_transport_disjoint segs [(lo, hi)] m m' fr (fr + ACtlCutP.FRAME_BYTES) HSTK MU WM).
        cbn [FRM.disjoint_from]. split; [unfold ACtlCutP.FRAME_BYTES; lia | exact I]. }
      split; [exact (Ksp _ _ S144 ltac:(lia)) | exact (Kad _ _ HAD17)]. }
    split; [exact (Ksp _ _ S216 ltac:(lia))|].
    split; [exact (Ksp _ _ S224 ltac:(lia))|].
    split; [exact (Ksp _ _ S248 ltac:(lia))|].
    split.
    { split; [exact (Kad _ _ HINa)|].
      apply (kn_bytes m m' lo hi (ACtlCut.c_p cx) (ACtlCut.c_in cx) MU);
        [left; rewrite Hinlen; lia | exact HINb]. }
    split; [exact (Ksp _ _ C256 ltac:(lia))|].
    split; [exact (Ksp _ _ C184 ltac:(lia))|].
    split; [exact (Ksp _ _ C192 ltac:(lia))|].
    split; [exact (Ksp _ _ C80 ltac:(lia))|].
    split; [exact (Ksp _ _ C88 ltac:(lia))|].
    split; [exact (Ksp _ _ C96 ltac:(lia))|].
    split; [exact (Ksp _ _ C272 ltac:(lia))|].
    split; [exact (Ksp _ _ C264 ltac:(lia))|].
    split; [exact (Kad _ _ CA72)|].
    split; [exact (Kad _ _ CA38)|].
    split; [exact (Ksp _ _ C72 ltac:(lia))|].
    split; [exact (Ksp _ _ C64 ltac:(lia))|].
    split; [exact (Ksp _ _ C56 ltac:(lia)) | exact (Ksp _ _ C48 ltac:(lia))]. }
  split.
  { destruct HLK as (Hj & H21 & HOUR). split; [exact Hj|].
    split; [exact (eq_trans E21 H21)|].
    unfold ACtlCutP.OURb in *.
    apply (Kfr (fr + 2624) (SM.OUR (ACtlCut.c_in cx)) HOUR); [lia|].
    rewrite SM.OUR_length. lia. }
  split.
  { destruct HbC as (C23 & C18 & (A1 & H9a & HA1 & HSP & Q232) & HPH & HFR & HKN & HFGj & HFSj).
    rewrite (kn_A9 regs A A1 H9 H9a HAb HA1) in HSP, Q232.
    destruct HSP as (Q248 & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 & Q264).
    split; [exact (eq_trans E23 C23)|].
    split; [exact (eq_trans E18 C18)|].
    split.
    { exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HAb|].
      split.
      { split; [exact (Kq _ _ Q248 ltac:(lia))|].
        split; [exact (Kq _ _ Q256 ltac:(lia))|].
        split; [exact (Kq _ _ Q144 ltac:(lia))|].
        split; [exact (Kq _ _ Q184 ltac:(lia))|].
        split; [exact (Kq _ _ Q192 ltac:(lia))|].
        split; [exact (Kq _ _ Q80 ltac:(lia))|].
        split; [exact (Kq _ _ Q88 ltac:(lia))|].
        split; [exact (Kq _ _ Q96 ltac:(lia))|].
        split; [exact (Kq _ _ Q272 ltac:(lia)) | exact (Kq _ _ Q264 ltac:(lia))]. }
      exact (Kq _ _ Q232 ltac:(lia)). }
    split.
    { destruct HPH as (HPHb & HPHp).
      split.
      { intros Hl. apply (Kph phi (SM.t_g (ACtlCut.c_in cx) j) (HPHb Hl)); [lia|].
        rewrite kn_tg_len. unfold A.ACtlK.a_size. lia. }
      intros Hl. rewrite Esp. exact (HPHp Hl). }
    split.
    { destruct HFR as (FA1 & FA2 & FB & FL).
      split; [exact (Kad _ _ FA1)|].
      split; [exact (Kad _ _ FA2)|].
      split; [|exact FL].
      apply (Kfr (ACtlCutP.fragb fr) (SM.t_FG (ACtlCut.c_in cx) j) FB);
        [unfold ACtlCutP.fragb; lia|].
      rewrite FL. unfold ACtlCutP.fragb. lia. }
    split.
    { destruct HKN as (KB & KA).
      split.
      { apply (kn_bytes m m' lo hi KNA.KIND_NAME KNA.kind_name_bytes MU); [|exact KB].
        left. rewrite SegF7.kn_len. unfold KNA.KIND_NAME in *. lia. }
      exact (Kad _ _ KA). }
    split.
    { destruct HFGj as (FG1 & FG2). split; [|exact FG2].
      unfold ACtlCutP.FGBe in *.
      destruct HFR as (_ & _ & _ & FL).
      apply (Kfr (fr + 2768) (SM.t_FG (ACtlCut.c_in cx) j) FG1); [lia|].
      rewrite FL. lia. }
    { destruct HFSj as (S104 & S112 & FB & FA & FI).
      split; [exact (Ksp _ _ S104 ltac:(lia))|].
      split; [exact (Ksp _ _ S112 ltac:(lia))|].
      split.
      { apply (Kfr (fr + 2880) (SM.fs_body (SM.fst_at (ACtlCut.c_in cx) j)) FB); [lia|].
        pose proof (SegF7.f7_fsb_len (ACtlCut.c_in cx) j) as Hl. lia. }
      split; [exact (Kad _ _ FA) | exact FI]. } }
  split.
  { destruct HbK as (K20 & K22 & K24 & K25 & K280 & KU32 & KR).
    split; [exact (eq_trans E20 K20)|].
    split; [exact (eq_trans E22 K22)|].
    split; [exact (eq_trans E24 K24)|].
    split; [exact (eq_trans E25 K25)|].
    split.
    { destruct K280 as (A1 & H9a & HA1 & Q280).
      rewrite (kn_A9 regs A A1 H9 H9a HAb HA1) in Q280.
      exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HAb|].
      exact (Kq _ _ Q280 ltac:(lia)). }
    split; [|exact KR].
    apply (kn_u32 m m' lo hi _ _ MU); [left; lia | exact KU32]. }
  split.
  { destruct HIDj as (ID1 & ID2). split; [|exact ID2].
    unfold ACtlCutP.IDBe in *.
    apply (Kfr (fr + 2688) (SM.t_ID (ACtlCut.c_in cx) j) ID1); [lia|].
    rewrite SegF7.f7_tID_len. lia. }
  split.
  { destruct HF17 as (A1 & H9a & HA1 & Q200).
    rewrite (kn_A9 regs A A1 H9 H9a HAb HA1) in Q200.
    exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HAb|].
    exact (Kq _ _ Q200 ltac:(lia)). }
  split.
  { destruct HW240 as (A1 & H9a & HA1 & (w & Qw & Hw0 & Hw1 & Hw2)).
    rewrite (kn_A9 regs A A1 H9 H9a HAb HA1) in Qw.
    exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HAb|].
    exists w. split; [exact (Kq _ _ Qw ltac:(lia))|].
    split; [exact Hw0|]. split; [exact Hw1 | exact Hw2]. }
  { destruct HPF as (A1 & H9a & HA1 & Hrec & H88).
    rewrite (kn_A9 regs A A1 H9 H9a HAb HA1) in H88.
    exists A. split; [exact (eq_trans E9 H9)|]. split; [exact HAb|].
    split.
    { intros Hl. destruct (Hrec Hl) as ((rb & Hrb & Hrbl) & Htphi).
      assert (Esz : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
        by (unfold A.ACtlK.a_size; lia).
      split.
      { exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
        apply (Kph phi (firstn 38 rb) (SegF7.f7_bytes_firstn m phi rb 38 Hrb)); [lia|].
        rewrite length_firstn. lia. }
      pose proof (kn_tphi_len cx j) as HL.
      apply (Kph phi (SM.t_phi (ACtlCut.c_in cx) j) Htphi); [lia|]. lia. }
    intros H8819. pose proof (kn_8819_big cx j H8819) as Hbig.
    assert (Esz : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
      by (unfold A.ACtlK.a_size; lia).
    destruct (H88 H8819) as
      ((f16 & v14 & v15 & v16 & v17 & HU16 & B14 & B15 & B16 & B17 & R14 & R15 & R16 & R17 &
        S14 & S15 & S16 & S17 & HF16 & HZZ) &
       (ls & rs & Q72 & Hls & Hlsl & Hrs & Hrsl & Hcmp & HAd186) &
       (ls2 & rs2 & Q64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & HAd180)).
    split.
    { exists f16, v14, v15, v16, v17.
      split; [apply (kn_u16 m m' lo hi _ _ MU); [left; lia | exact HU16]|].
      split; [apply (kn_b8 m m' lo hi _ _ MU); [left; lia | exact B14]|].
      split; [apply (kn_b8 m m' lo hi _ _ MU); [left; lia | exact B15]|].
      split; [apply (kn_b8 m m' lo hi _ _ MU); [left; lia | exact B16]|].
      split; [apply (kn_b8 m m' lo hi _ _ MU); [left; lia | exact B17]|].
      split; [exact R14|]. split; [exact R15|]. split; [exact R16|]. split; [exact R17|].
      split; [exact (Ksh (phi + 14) ltac:(lia) ltac:(lia) S14)|].
      split; [exact (Ksh (phi + 15) ltac:(lia) ltac:(lia) S15)|].
      split; [exact (Ksh (phi + 16) ltac:(lia) ltac:(lia) S16)|].
      split; [exact (Ksh (phi + 17) ltac:(lia) ltac:(lia) S17)|].
      split; [exact HF16 | exact HZZ]. }
    split.
    { exists (firstn 6 ls), (firstn 6 rs).
      split; [exact (Kq 72 _ Q72 ltac:(lia))|].
      split.
      { apply (Kfr (fr + 186) (firstn 6 ls) (SegF7.f7_bytes_firstn m (fr + 186) ls 6 Hls)); [lia|].
        rewrite length_firstn. lia. }
      split; [rewrite length_firstn; lia|].
      split.
      { apply (Kph phi (firstn 6 rs) (SegF7.f7_bytes_firstn m phi rs 6 Hrs)); [lia|].
        rewrite length_firstn. lia. }
      split; [rewrite length_firstn; lia|].
      split; [rewrite SegF7.f7_memcmp_firstn; exact Hcmp|].
      exact (Kad _ _ HAd186). }
    exists (firstn 6 ls2), (firstn 6 rs2).
    split; [exact (Kq 64 _ Q64 ltac:(lia))|].
    split.
    { apply (Kfr (fr + 180) (firstn 6 ls2) (SegF7.f7_bytes_firstn m (fr + 180) ls2 6 Hls2)); [lia|].
      rewrite length_firstn. lia. }
    split; [rewrite length_firstn; lia|].
    split.
    { apply (Kph (phi + 6) (firstn 6 rs2) (SegF7.f7_bytes_firstn m (phi + 6) rs2 6 Hrs2)); [lia|].
      rewrite length_firstn. lia. }
    split; [rewrite length_firstn; lia|].
    split; [rewrite SegF7.f7_memcmp_firstn; exact Hcmp2|].
    exact (Kad _ _ HAd180). }
Qed.

(* A hit of find_segment names a segment of the list that contains the range (the LPS fact ctrl's
   lib/A/Prog/CtrlPaLib.v:28-37 restates as find_segment_hit; restated here so that the PA layer stays out
   of this file's closure). *)
Lemma kn_find_seg : forall (sgs : list Segment) (a n : Z) sg,
  find_segment sgs a n = Some sg ->
  In sg sgs /\ Z.of_N (seg_base sg) <= a /\ a + n <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction sgs as [|s rest IH]; intros a n sg H; [discriminate|]. cbn in H.
  destruct (Z.leb (Z.of_N (seg_base s)) a) eqn:Hlo;
    destruct (Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:Hhi; cbn in H.
  - injection H as <-. split; [left; reflexivity|].
    split; [apply Z.leb_le, Hlo | apply Z.leb_le, Hhi].
  - destruct (IH a n sg H) as [H1 H2]. split; [right; exact H1 | exact H2].
  - destruct (IH a n sg H) as [H1 H2]. split; [right; exact H1 | exact H2].
  - destruct (IH a n sg H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* The carried runtime facts across the window write, route (C) form A.ACtlRtC.ctl_rt_C B ly S (the state ly S
   does not move: the run only writes its callee window).  Every runtime cell and every read-only address lies
   below HIGHMEM_BEG, hence below the window; the two shadow regions (cut_shadow B ly S, img_shadow) are kept by
   A.ShadowRwOnK.fl_shadow_rw_on, because every shadow byte lies below HIGHMEM_BEG too, so outside the window. *)
Lemma kn_rt_keep : forall ly (S : CG00.astate) (m m' : word -> option byte) (lo hi : Z),
  (forall a, CG0d.in_img segs a -> 0 <= a < CG0f.kLowMemEnd) ->
  FRM.munch [(lo, hi)] m m' -> FRM.wmono segs m m' -> ART.HIGHMEM_BEG + 4096 <= lo ->
  A.ACtlRtC.ctl_rt_C B ly S m -> A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S m m' lo hi Hlow MU WM Hhm (HC & HScut & HSimg & HR).
  assert (Kl : forall a bs, MEM.bytes_at A.Img0.rsegs m a bs ->
                 a + Z.of_nat (length bs) <= ART.HIGHMEM_BEG -> MEM.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Hn.
    apply (FRM.bytes_at_transport A.Img0.rsegs [(lo, hi)] m m' a bs Hb MU).
    cbn [FRM.disjoint_from]. split; [lia | exact I]. }
  assert (WMr : FRM.wmono A.Img0.rsegs m m') by (rewrite <- PB.tfibsegs_rsegs; exact WM).
  assert (Hout : forall x, ART.in_shadow x -> FRM.outside [(lo, hi)] x).
  { intros x Hx. cbn [FRM.outside]. split; [|exact I].
    unfold ART.in_shadow in Hx.
    unfold ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in *. lia. }
  split.
  { unfold A.ACtlK.asan_cells_at, ART.asan_cells in *.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
    unfold ART.CELL_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE, ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR,
      ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG, ART.MIDEND, ART.GOT_MIDEND,
      ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET, ART.HIGHMEM_BEG in *.
    split; [apply (Kl _ _ C1); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C2); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C3); cbn [length]; lia|].
    split; [apply (Kl _ _ C4); cbn [length]; lia|].
    split; [apply (Kl _ _ C5); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C6); rewrite MEM.length_le4; lia|].
    split; [apply (Kl _ _ C7); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C8); cbn [length]; lia|].
    split; [apply (Kl _ _ C9); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C10); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C11); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C12); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C13); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C14); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C15); rewrite MEM.length_le8; lia|].
    split; [apply (Kl _ _ C16); rewrite MEM.length_le8; lia|].
    apply (Kl _ _ C17); rewrite MEM.length_le8; lia. }
  split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ [(lo, hi)] m m' HScut MU WMr Hout)|].
  split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ [(lo, hi)] m m' HSimg MU WMr Hout)|].
  { unfold A.ACtlK.ro_agree_at in *.
    intros a Ha.
    assert (Hin : CG0d.in_img A.Img0.rsegs (bv_unsigned a)).
    { unfold MEM.ro_addr in Ha.
      destruct (find_segment A.Img0.rsegs (bv_unsigned a) 1) as [sg|] eqn:E; [|discriminate Ha].
      apply kn_find_seg in E as (Hsin & Hb1 & Hb2).
      exists sg. split; [exact Hsin | lia]. }
    pose proof (Hlow (bv_unsigned a) Hin) as Hb.
    pose proof (bv_unsigned_in_range 64 a) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold CG0f.kLowMemEnd, ART.HIGHMEM_BEG in *.
    assert (Ea : MEM.wa (bv_unsigned a) = a).
    { unfold MEM.wa. apply bv_eq. rewrite Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. reflexivity. }
    assert (Em : m' a = m a).
    { rewrite <- Ea. apply MU. rewrite MEM.wa_unsigned by lia.
      cbn [FRM.outside]. split; [lia | exact I]. }
    unfold MEM.mrd in *. rewrite Em. exact (HR a Ha). }
Qed.

(* The 14 shadow bytes of the KIND_NAME table [0x9e760, 0x9e7d0) are visible in the walk's world.  This is the
   footprint fact the callee's `ExecF.rng RNG (shadow_addr KIND_NAME) 14` asks for, and it is a fact about the
   world's hidden set (w_H W), not about memory: ctl_rt_C's img_shadow / (FA) / (Z) regions say that bytes are
   PRESENT in m, which does not decide w_H W, so they do not give it.  It comes from the core's AR law instead:
   AR_zshadow_law (YG0d.v:435-438) at the bundle's zero-shadow range (0x21aa0, 0x9e7d0 - 0x21aa0), an entry of
   as_zero_shadow B = A.AF0m.Tfib_zero_shadow (CtrlTSyms' ts_zsh; the record fine list of a Theorem Labs lane's start-up
   files, AF0m.v:2955-2964, which keeps KIND_NAME's 14 full granules and excludes its redzone at 0x9e7d0): each of
   those shadow bytes reads Some 0 through the view, and a byte the view reads is visible
   (A.ProgWorldVisFrame.vis_of_aview).  ProgWorld's glob_sh_vis does not apply: it asks for the 64-byte hull
   [0x9e740, 0x9e800), which ends past the range's end 0x9e7d0. *)
Lemma kn_shadow_vis : A.AF0m.CtrlTSyms B -> CG0d.AR_laws segs B ->
  forall ly S (W : CA0n.world segs) mem md,
    CG0n.AR segs B ly S W mem md ->
    PB.range_visible (CA0n.w_H W) (ART.shadow_addr KNA.KIND_NAME) 14.
Proof.
  intros HTS HL ly S W mem md HAR.
  assert (Hzl : CG0d.AR_zshadow_law segs B) by (destruct HL; assumption).
  assert (Hr : In (0x21aa0, 0x9e7d0 - 0x21aa0) (CG0n.zero_shadow_ranges B ly)).
  { unfold CG0n.zero_shadow_ranges. right. rewrite (A.AF0m.ts_zsh _ HTS). unfold A.AF0m.Tfib_zero_shadow.
    repeat (first [left; reflexivity | right]). }
  pose proof (Hzl ly S W mem md _ HAR Hr) as Hz. cbn [fst snd] in Hz.
  unfold PB.range_visible, ART.shadow_addr, ART.ASAN_K, KNA.KIND_NAME.
  split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
  intros a Ha.
  apply (A.ProgWorldVisFrame.vis_of_aview _ W mem).
  assert (Hi : 0 <= a - (CG0f.SHADOW_OFF + 0x21aa0 / 8) < (0x9e7d0 - 0x21aa0) / 8).
  { unfold CG0f.SHADOW_OFF. change (0x21aa0 / 8) with 17236.
    change ((0x9e7d0 - 0x21aa0) / 8) with 63910. change (0x9e760 / 8) with 81132 in Ha. lia. }
  pose proof (Hz _ Hi) as Hzi. unfold CG0v.shadow_of_addr in Hzi.
  replace (CG0f.SHADOW_OFF + 0x21aa0 / 8 + (a - (CG0f.SHADOW_OFF + 0x21aa0 / 8))) with a in Hzi by ring.
  rewrite Hzi. discriminate.
Qed.

(* The journal across the callee's window write: ajournal_exec at Wr := [sp - 16, sp), whose awr_byte case
   is the walk's own stack window (YCbq.v:460-461). *)
Section KnJrnl.
Context {SK : CI16.sink_head}.
Lemma kn_jrnl : forall (cx : ACtlCut.ctlcx) (FP own : list (Z * Z)) ly3 S3 (W3 : CA0n.world segs)
    (mem3 mem' : word -> option byte) md3 md' (k sp : Z),
  CG0d.AR_laws segs B ->
  (forall a, CG0d.in_img segs a -> 0 <= a < CG0f.kLowMemEnd) ->
  CCbq.ajournal (SK := SK) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  FRM.munch [(sp - 16, sp)] mem3 mem' ->
  FRM.wmono segs mem3 mem' ->
  (forall x : word, CA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  CK04.same_but_materialized md3 md' ->
  ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= sp - 16 -> sp <= ACtlCut.c_sp cx ->
  CG0f.kLowMemEnd <= sp - 16 ->
  CCbq.ajournal (SK := SK) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly3 S3 W3 mem' md' k.
Proof.
  intros cx FP own ly3 S3 W3 mem3 mem' md3 md' k sp HLAWS Hlow HJ MU WM Hhid Hsbm Hw1 Hw2 Hhm.
  assert (Hwv : forall (f : word -> option byte) (y : word),
            find_segment segs (bv_unsigned y) 1 = None -> wview segs f y = f y).
  { intros f y Hns. unfold wview. rewrite Hns. destruct (f y); reflexivity. }
  eapply (CCbq.ajournal_exec segs B HLAWS Hlow) with (Wr := fun a => sp - 16 <= a < sp).
  - exact HJ.
  - intros x Hx. unfold CK04.mrestrict. destruct (CA0n.w_H W3 x); [reflexivity|].
    apply MU. cbn [FRM.outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold CK04.mrestrict in *.
    destruct (CA0n.w_H W3 x) eqn:EH; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (sp - 16)) as [Hd|Hd].
    + rewrite (MU x ltac:(cbn [FRM.outside]; split; [lia | exact I])). exact Hx.
    + destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hd2|Hd2].
      * assert (Hni : ~ CG0d.in_img segs (bv_unsigned x)).
        { intros Hi. pose proof (Hlow _ Hi) as Hb2. lia. }
        pose proof (CCbq.find_segment_none segs (bv_unsigned x) Hni) as Hns.
        rewrite <- (Hwv mem' x Hns). apply WM. rewrite (Hwv mem3 x Hns). exact Hx.
      * rewrite (MU x ltac:(cbn [FRM.outside]; split; [lia | exact I])). exact Hx.
  - exact Hhid.
  - exact Hsbm.
  - intros a Ha. unfold CCbq.awr_byte. left. unfold A.ACfn.LLVMF_STK in *. lia.
Qed.
End KnJrnl.

End KnHelpers.

(* ---------------------------------------------------------------------------------------------------------
   THE STAGE. *)
Section GlueF7.

(* ACtl.v's Section shape (ACtl.v:210-214 at blob c4edf0be7fe), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : CG0f.asyms.
Variable MT : CC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :433-434), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81f64_at := (ACtlCutP.C_A81f64_at B).
Local Notation C_A81f7c_at := (ACtlCutP.C_A81f7c_at B).

(* --- Section hypotheses (sources in the header). --- *)

(* ACtl.v:237, exact text. *)
Hypothesis LAWS : CG0d.AR_laws segs B.
(* ACtl.v:252, exact text: the bundle's own symbols.  It pins as_zero_shadow B (ts_zsh), which kn_shadow_vis reads. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

Lemma glue_seg_F7 : forall POST (j : nat),
  CF POST (ix_cut C_A81f7c_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f64_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j]. *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f64_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn26 & Hj255 & HHB & HFLSI & HLK & HbC & HbK & H10 & HIDj & HF17 &
    HW240 & HPF).
  (* route (C): the cut carries ctl_rt_C B ly3 S3 mem3; this stage reads its asan cells and ro_agree only (the run
     reads and stores no shadow byte through a shadow_rw premise, F7Fon.v's header). *)
  pose proof Hrt as (HRTc & _ & _ & HRTr).
  (* G2: the visible-state bounds. *)
  pose proof HJ as HJ0.
  destruct HJ0 as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
  destruct Hstatic as (_ & _ & Hceil & Hstklo & Hsphi & Hhi47 & _ & _ & _).
  pose proof CCbq.asan_consts as (Hac & _ & _ & _ & _).
  (* the frame *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = CG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold CG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite Efr3 in Hf4096, Hfceil.
  change (CG00.fs_frame_bytes 6) with 4096 in Hfceil.
  (* the record block *)
  assert (Hphiin : In (phi, ACtlCutP.flen cx j) (CG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (CG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hphiin)
    as (_ & Hphi4096 & Hphiceil & _ & _ & _ & Hflen0).
  pose proof (CCbq.req_size_pos (ACtlCutP.flen cx j) (proj1 Hflen0)) as (Hrq1 & Hrq2).
  (* the input block *)
  pose proof Hbase as Hbase0.
  destruct Hbase0 as (Hpre & _).
  destruct Hpre as (_ & _ & _ & _ & Hpcase & Hnlen & _).
  assert (Hcpceil : ACtlCut.c_p cx + ACtlCut.c_n cx <= CM05.alloc_ceiling).
  { destruct Hpcase as [(Hn0 & Hp0) | (Hn & Hinb)].
    - rewrite Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hinb3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinb. }
      destruct (CG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR Hinb3)
        as (_ & _ & Hpc & _).
      pose proof (CCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as (_ & Hq2). lia. }
  (* FRAC's own window facts *)
  pose proof HFRAC as HFRAC0.
  destruct HFRAC0 as (A & sp & Hsp & Hsp16 & Hspz & H4r & H8r & H9r & H3r & H19r & H26r &
    Hfr32 & HA32 & HAS & HspA & HfrA & HA416 & Hsp4096 & HSapp & _).
  assert (HSappN : ACtlCut.c_sp cx <= 140737488355328).
  { unfold ART.APPMEM_END in HSapp. exact HSapp. }
  assert (Hspnn : 0 <= sp).
  { rewrite <- Hspz. unfold CG0d.spZ. pose proof (bv_unsigned_in_range 64 (CK11.getr regs3 2)) as Hr. lia. }
  assert (Hsp47 : sp <= 140737488355328) by lia.
  (* the window [sp-16, sp) is above the whole image and above the allocator's ceiling *)
  assert (Hceilsp : CM05.alloc_ceiling + 4096 <= sp - 16).
  { unfold A.ACfn.LLVMF_STK in *. lia. }
  assert (Hspbig : 140735332483072 + 4096 <= sp - 16) by lia.
  assert (HAnn : 0 <= A < 2 ^ 64).
  { split; [lia|]. change (2 ^ 64) with 18446744073709551616. lia. }
  assert (HA416' : A + 416 < 2 ^ 64)
    by (change (2 ^ 64) with 18446744073709551616; lia).
  assert (Hlo : CG0f.kLowMemEnd <= sp - 16) by (unfold CG0f.kLowMemEnd; lia).
  assert (Hhmlo : ART.HIGHMEM_BEG + 4096 <= sp - 16) by (unfold ART.HIGHMEM_BEG; lia).
  assert (Hlo47 : sp - 16 <= 2 ^ 47) by (change (2 ^ 47) with 140737488355328; lia).
  assert (Hfrlo : fr + ACtlCutP.FRAME_BYTES <= sp - 16)
    by (unfold ACtlCutP.FRAME_BYTES; lia).
  (* the whole class-6 frame slot [fr, fr + 4096) is below the window (what kn_frac_keep needs) *)
  assert (Hslotlo : fr + 4096 <= sp - 16) by lia.
  assert (Hphilo : phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= sp - 16).
  { unfold A.ACtlK.a_size, CG00.req_size in *.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hcplo : ACtlCut.c_p cx + ACtlCut.c_n cx <= sp - 16) by lia.
  assert (Hknlo : KNA.KIND_NAME + 112 <= sp - 16) by (unfold KNA.KIND_NAME; lia).
  assert (Hhisp2 : sp <= CG0d.spZ regs3) by (rewrite Hspz; lia).
  assert (Hinlen : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hnlen).
  (* the run's register and memory premises (the cut's own bundles stay intact for kn_core_keep) *)
  pose proof HbK as HbK0.
  destruct HbK0 as (K20 & K22 & K24 & K25 & K280 & KU32 & KR).
  pose proof HbC as HbC0.
  destruct HbC0 as (C23 & C18 & (A1 & H9a & HA1 & HSP & Q232) & HPH & HFR & HKN & HFGj & HFSj).
  rewrite (kn_A9 regs3 A A1 H9r H9a HAnn HA1) in HSP.
  destruct HSP as (Q248 & _).
  destruct HKN as (HKNB & HKNA).
  assert (Hv : 0 <= SM.t_k (ACtlCut.c_in cx) j < 2 ^ 31).
  { pose proof (Prog.RcParse.ctrlparse_kind_range (SM.t_len (ACtlCut.c_in cx) j)
                  (SM.t_g (ACtlCut.c_in cx) j)) as Hk13.
    unfold SM.t_k. change (2 ^ 31) with 2147483648. lia. }
  (* the stack window is present, hence stk *)
  assert (HSTK0 : FRM.stk segs mem3 (sp - 16) sp).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616;
      unfold ART.APPMEM_END in HSapp; lia|].
    intros a Ha.
    destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK in *; lia)) as (HHa & b & Hbb).
    assert (Ea : MEM.wa a = Z_to_bv 64 a) by reflexivity.
    split.
    - rewrite Ea. unfold wview. rewrite Hbb. intros HC; discriminate HC.
    - exists b. unfold MEM.mrd. rewrite Ea, Hbb. reflexivity. }
  (* the five footprint ranges are visible *)
  assert (Hwin : forall a, sp - 16 <= a < sp -> CA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK in *; lia)) as (HHa & _). exact HHa. }
  assert (V248 : PB.range_visible (CA0n.w_H W3) (A + 248) 8).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616;
      unfold ART.APPMEM_END in HSapp; lia|].
    intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK in *; lia)) as (HHa & _). exact HHa. }
  assert (Vkp : PB.range_visible (CA0n.w_H W3) (fr + 176) 4).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros a Ha.
    destruct (CG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
      as (_ & _ & Hfb & _).
    rewrite Efr3 in Hfb. change (CG00.fs_frame_bytes 6) with 4096 in Hfb.
    destruct (Hfb a ltac:(lia)) as ((HHa & _) & _). exact HHa. }
  assert (Vimg : PB.range_visible (CA0n.w_H W3) 0x10000 0x5ee000).
  { pose proof (PB.img_vis_W W3) as Hv0.
    unfold PB.range_visible, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in Hv0 |- *.
    destruct Hv0 as (V1 & V2 & V3). split; [lia|]. split; [lia|]. intros a Ha. apply V3. lia. }
  assert (Vstk : PB.range_visible (CA0n.w_H W3) (sp - KNA.REAC_CTRL_KIND_NAME_FRAME)
                   KNA.REAC_CTRL_KIND_NAME_FRAME).
  { unfold KNA.REAC_CTRL_KIND_NAME_FRAME.
    split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616;
      unfold ART.APPMEM_END in HSapp; lia|].
    intros a Ha. apply Hwin. lia. }
  assert (Vsh : PB.range_visible (CA0n.w_H W3) (ART.shadow_addr KNA.KIND_NAME) 14)
    by exact (kn_shadow_vis B TFIB_SYMS LAWS ly3 S3 W3 mem3 md3 HAR).
  (* the footprint run (the route (C) twin), with the callee's closed _on contract supplied *)
  pose proof (SegF7Fon.f7_evt_F_on KNF.reac_ctrl_kind_name_holds_F_on
                (PB.RNG_W (CA0n.w_H W3))
                (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4)
                (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
                (CK11.getr regs3 9) (CK11.getr regs3 10) (CK11.getr regs3 11) (CK11.getr regs3 12)
                (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16)
                (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
                (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24)
                (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28)
                (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
                CK11.fp_regs CK11.fp_csr mem3
                A (fr + 176) (SM.t_k (ACtlCut.c_in cx) j) (sp - 16)) as HRUN.
  assert (Hspv : bv_unsigned (CK11.getr regs3 2) = sp) by (rewrite <- Hspz; reflexivity).
  rewrite Hspv in HRUN.
  specialize (HRUN H9r H10 K24 Hv Q248 KU32 HKNB
                (SegF7.f7_kn_strings_ro mem3 HRTr) HSTK0 ltac:(unfold KNA.REAC_CTRL_KIND_NAME_FRAME; lia)
                ltac:(unfold KNA.REAC_CTRL_KIND_NAME_FRAME, KNA.KIND_NAME, CG0f.kLowMemEnd in *; lia)
                HRTc HKNA).
  specialize (HRUN ltac:(intros x Hx; cbn [FRM.outside]; split; [|exact I];
                unfold ART.GOT_CELL_K, ART.CELL_K, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
                  ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG, KNA.REAC_CTRL_KIND_NAME_FRAME in *; lia)).
  specialize (HRUN (PB.rng_of_visible _ _ _ V248) (PB.rng_of_visible _ _ _ Vkp)
                (PB.rng_of_visible _ _ _ Vimg) (PB.rng_of_visible _ _ _ Vstk)
                (PB.rng_of_visible _ _ _ Vsh)).
  (* G3: the cut's configuration in the run's state form, then the register move. *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81f64_at [Z.of_nat j])) with 0x81f64.
  apply (CA0nR.SRr_xregs_eqv segs W3 (R6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81f64) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (R6.xregs_eqv_sym _ _ (R6.mkR_of_eqv regs3))].
  rewrite (kn_mkR_of regs3).
  (* G4: the lift. *)
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  apply (CA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (CA0n.w_H W3)) _ (POST cx) HFS).
  { exact (PB.fp_avoids_RNG_W (CA0n.w_H W3)). }
  (* G5: the continuation. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (a1' & a2' & mem' & Ems & MU & WM & MI & ST').
  subst ms'.
  cbn [ms_mem] in Hhid.
  set (R1 := FRM.mkR (Z_to_bv 64 0x81f7c) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4)
         (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8)
         (CK11.getr regs3 9) (Z_to_bv 64 (KNA.kind_name_addr (SM.t_k (ACtlCut.c_in cx) j))) a1' a2'
         (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16)
         (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
         (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24)
         (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28)
         (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)) in *.
  change (CA0n.SRr segs W3
            (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81f7c_at [Z.of_nat j])) R1 mem' md') (POST cx)).
  unfold KNA.REAC_CTRL_KIND_NAME_FRAME in MU, ST'.
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem' md' Hbase).
  - (* the journal across the callee's window write *)
    exact (kn_jrnl B cx [] (ACtlCut.cut_own (ix_cut C_A81f64_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 mem'
             md3 md' k sp LAWS A.ACtlG.Kit.kit_segs_low HJ MU WM Hhid Hsbm
             ltac:(unfold A.ACfn.LLVMF_STK in *; lia) ltac:(lia) Hlo).
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f7c_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split.
    { exact (kn_frac_keep B cx fr fr (sp - 16) sp regs3 R1 mem3 mem' HFRAC
               eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl MU Hslotlo Hhmlo Hhisp2). }
    unfold ACtlCutP.b5_body.
    exists phi.
    split; [exact HPerm|].
    split; [exact Hcn26|].
    split; [exact Hj255|].
    assert (Hcore := kn_core_keep cx j phi fr (sp - 16) sp A regs3 R1 mem3 mem'
      (conj HHB (conj HFLSI (conj HLK (conj HbC (conj HbK
        (conj HIDj (conj HF17 (conj HW240 HPF))))))))
      H9r HAnn HA416' eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      MU WM Hhmlo Hlo47 HspA Hfrlo Hphilo Hcplo Hinlen Hknlo).
    destruct Hcore as (HHB' & HFLSI' & HLK' & HbC' & HbK' & HIDj' & HF17' & HW240' & HPF').
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HbC'|].
    split; [exact HbK'|].
    split; [reflexivity|].
    split; [exact HIDj'|].
    split; [exact HF17'|].
    split; [exact HW240' | exact HPF'].
  - (* ctl_rt_C on the new memory, at the same state ly3 S3 *)
    exact (kn_rt_keep B ly3 S3 mem3 mem' (sp - 16) sp A.ACtlG.Kit.kit_segs_low MU WM Hhmlo Hrt).
Qed.

End GlueF7.
