(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 872 of its 915 lines of code are new or changed and 802 lines of the source are left out. *)
(* lib/A/ACtlG/F2.v -- GLUE for stage seg_F2 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:741-742).  Written by a Theorem Labs lane; re-pointed to the narrowed run
   F2Fs.f2_evt_Fs (BLOCK_RT_HI dropped; F2Fs.v is not in this delivery) by a Theorem Labs lane's sub-lane; route (C) L3 switch by a Theorem Labs lane (the
   len > 0 run is now F2Fs_on.f2_evt_Fs_on); single writer.
   rule 24: no function proved (segment lemma).

   WHAT IT PROVES
     glue_seg_F2 : forall POST (j : nat),
       CF POST (ix_cut C_A81dd0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e54_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A81da4_at [Z.of_nat j])
   with ACtl.v's own CF / ix_cut / C_* notations (ACtl.v:257, :261-262, :305-310; SK := A.AE2k.tfib_sink_head,
   FP := []), i.e. exactly ACtl.v's Section hypothesis seg_F2.  Segment F2 (Seg/F2.v seg_F2 :829, blob
   26e353ed3a9): 0x81da4 mv s7,a0; bnez a0; sltiu s6,s2,50; sd s4,216(s1); sd s6,232(s1); beqz s2,0x81e54;
   then (len > 0) a0 := s7, a1 := s4, a2 := s2 and `jal __asan_memcpy` at 0x81dcc, back at 0x81dd0.

   THE RUNS LIFTED (a Theorem Labs lane's footprint twins, lib/A/Prog/Seg/F2F.v (an earlier version, blob 0ba0d238585, not in this delivery), Required qualified, and
   this lane's narrowed len > 0 stretch in its route (C) form lib/A/Prog/Seg/F2Fs_on.v):
   - len = 0: F2F.f2z_evt_F (F2F.v (at head lib/A/Prog/Seg/F2F.v:229)), 0x81da4 -> 0x81e54, write set the two spill words.
   - len > 0: F2Fs_on.f2_evt_Fs_on, 0x81da4 -> 0x81dd0 WHOLE (the call not split: a Theorem Labs lane's split rule 04:01Z).
     It is F2Fs.f2_evt_Fs (itself F2F.f2_evt_F with F2F.v's (at head lib/A/Prog/Seg/F2F.v:88) `RT_HI <= phi` replaced by
     asan_memcpy_contract_F's own `phi + N <= RT_LO \/ RT_HI <= phi`, asan_memcpy_cF.v (at head lib/A/Prog/asan_memcpy_cF.v:56)) in route (C) form: the
     callee premise is a Theorem Labs lane's asan_memcpy_contract_F_on, DISCHARGED by its PROVED
     A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on; the shadow premise is `shadow_rw_on (f2_evt_Fs_shadow_R phi S N)`
     (the callee's region: the aligned shadow-word spans of the source and of the destination), fed from the cut's
     ctl_rt_C by its (L) disjunct (both spans lie in live blocks' covers, f2g_sh_word_blk).  The run takes
     mem_inv, which the cut does not carry (ctl_rt_C has asan_cells_at / the two shadow regions / ro_agree_at
     only), so it runs on MemNorm.normalize rsegs mem3 (MemNorm.mem_inv_normalize; premises moved forward by
     MemNormTr's asan_cells_normalize / addressable_normalize / stk_normalize_ro / rw_cells_normalize,
     ShadowRwOnT.shadow_rw_on_normalize and MemNorm.bytes_at_normalize) and is moved back to the cut's memory by
     A.ProgWorld.rebase_ro_normalize (= MemNormF.evtF_normalize_ro + the MemNorm transports; its post's facts
     back by MemNormTr.ms_rel_MS / rw_cells_of_rel).  This is the shape of a Theorem Labs lane's calln runs (Seg/F3F.v
     f3_calln_F).
   CLEANER ROUTE (not taken; not this lane's files): a twin of f2_evt whose callee premise is stated on
   ro_agree instead of mem_inv would drop the MemNorm detour.

   THE PROOF (glue-pattern.md G1-G5)
   G1  ix_cut's index equation, then C_A81da4_at's 13 conjuncts (ACtlCutP.v:1966-1977).
   G2  from VISIBLE state only: the journal's AR / layout_le / stack presence / astk_ok; the class-6 frame by
       KitMem.kitmem_own6 (4096 <= fr, fr + 4096 <= alloc_ceiling <= c_sp - LLVMF_STK); FRAC's base A and sp;
       the turn's block (phi, flen) in the live list by the body's Permutation, AR_blocks_law gives its
       placement / presence / NoDup (f2g_nodup), so it is NEW since the entry (f2g_new_block) and apart from
       the input block (sep_blocks) and the frame (sep_block_frame), and off the image (YCbq.blk_img), so it
       misses the runtime words [RT_LO, RT_HI), which lie in the image (KitMem.kitmem_in_img): that is
       f2_evt_Fs's `phi + N <= RT_LO \/ RT_HI <= phi`; the input block from ctl_base's lib pre
       (ACfn.v:38-39).  Footprint RNG := ProgBridge.RNG_W (w_H W3): spill words and callee window by
       KitMem.kitmem_rng_win, the image by ProgBridge.img_vis_W, phi / source by kitmem_rng_heap, their
       8-aligned shadow word spans by ProgWorldVisHeap.heap_sh_vis / ProgWorldVisWin.win_sh_vis.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the canonical map mkR_of regs3; the runs' 31 register
       binders are instantiated with Sem.reg_get regs3 r, so every kept register of the end map is
       CONVERTIBLE to the entry's (body conjuncts carry by `exact`).
   G4  KitMem.kitmem_lift (YA0nR.SRr_fsteps; the continuation gets the fsteps run itself).
   G5  the journal across the run by ProgWorld.ajournal_of_fsteps (write set = the run's munch list; awr_byte:
       the stack window for the spill words and the callee window, in_tmp_block for the block); mem_grows and
       the hidden bytes by ProgWorld.pws_fsteps_mem; FRAC by KitMem.kitmem_frac_keep (by shape, so the
       announced FRAC trailer conjunct at fr + 4088 moves with no edit here); the frame-loop bundles by this
       file's f2g_*_munch lemmas over ACtlCutP's predicates; the exit's ctl_rt_C (route (C)) by f2g_rtC, i.e.
       ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR with the entry's arodata_okS carried by the journal
       (both arms); b5_KN, which F2 PRODUCES (its exits are the first b5_body cuts), by f2g_kn.

   SECTION HYPOTHESES (exact text below; source and why)
   - LAWS, RELRO_IMG, TFIB_SYMS: ACtl.v:244, :226, :259, verbatim (ajournal / frames / blocks laws; the
     read-only span in the image; ts_owned / ts_errno / ts_zsh for the kind-name table; ctl_rt_C_of_AR).
   - RELRO_KIND_NAME: ACtl.v (at head lib/A/ACtl.v:238), verbatim (batch 3, from a working branch d36efc6152d; it replaces this file's earlier KN_RELRO,
     the same fact at KIND_NAME = 0x9e760).  b5_KN's bytes
     come only from ctl_base's arodata_okS RLO RHI (ACfn.v:43) carried by the journal's image clause
     (KitMem.kitmem_arodataS_journal): ro_agree gives nothing there (ro_addr rsegs 0x9e760 = false, measured:
     the RELRO PT_LOAD is writable).  Discharged at the top by relro_kind_name_ctrl (0x9e380 / 0xa07c8).
   - (no BLOCK_RT_HI: the frame route's `RT_HI <= phi`, which the core's AR laws do not give, is no longer
     asked for; f2_evt_Fs asks for the contract's disjunction, paid in G2 from AR's client-image law.)

   ZERO-SHADOW ROW: f2g_kn reads the shadow of [0x9e760, 0x9e7d0) through ts_zsh from AF0m.Tfib_zero_shadow's
   RECORD row (0x21aa0, 0x9e7d0 - 0x21aa0) (AF0m.v:2963 on the interim core 5da74c9c931, merged at glue base
   29ddfc3ea99; the same row as a Theorem Labs lane's record AF0m e56483f863b), found in the list by membership.  The
   planning core's row (0x20ec0, 0xa4380 - 0x20ec0) is gone.  The owned-static and errno side conditions
   (Tfib_owned_static, TFIB_ERRNO = 0x5db76c) hold on it.

   TRANSCRIPTION DIFFERENCES (a Theorem Labs lane 05:5xZ): no Seg/*.v keep lemma is applied to a cut body.  ACtlCutP's f1_IN
   drops SlotInv's `0 < g_n -> In (g_p, g_n) g_H` (SlotInv.v:1826), its b5_C drops b5_FS (SlotInv.v:2128), its
   b5_PH drops `flen = 0 -> ~ a_in_fs ..` and reads YG0d.spZ; the bundles move by f2g_PRO / FLSH / FLC / IFS /
   LK_munch here, stated over ACtlCutP's predicates (single-stage helpers; KitMem has no bundle lemmas).

   CLOSURE (glue closure rule): every project module Required qualified, never Imported (the six doubled
   Reusable modules and lib/Lib by absolute Require).  Measured by a Theorem Labs lane's w2a-closure.py Require scan
   (481 files on glue base 29ddfc3ea99): no lib/AZ/AsanW (not in this delivery), no SegCF / *_cfw / Cf* file; W6 only lib/A/W6/QSlot.v
   (via Seg/Tac_cls); AZ only AZ/Spec/{AsanCtrl, AsanCtrlProps, STree} and AZ/LibA/AcctCore.v (via lib/Lib/ExecF
   only).  Frame-route files at their blob of record (SlotModel 04dc7903221, SlotInv 4cf85db229a, Seg/Tac_slot
   de02ff45188, AsanRT b67d26f8ec7 mcs 30, ...): the full list is in the commit message.  STAND-INS: none; on the
   interim core 5da74c9c931 no file of the closure carries a port_core_refused_<hex> name or an Admitted /
   admit (scripted scan), and A/AD2l.v is not in the closure.

   BUILD STATE: cb build (BASE row 23b918fe0c2e, a build machine), NO
   substitution; the result and its log are in the commit message.
   Every lemma of this file ends in Qed; Print Assumptions glue_seg_F2 is the last line. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
(* the six doubled modules: absolute Require (a `From ...lib Require Reusable.YK11` matches lib.A.Reusable.YK11
   by suffix and cannot disambiguate), and every use below is fully qualified through the aliases. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
(* lib/Lib has twins under lib/A/Bz/Lib: absolute Require and fully qualified use (a Theorem Labs lane 05:0xZ). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0d Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0v Reusable.YCbq Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.AF0m A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.AsanRTFacts A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRt A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC A.Prog.sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.MemNormTr A.MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.ImgBounds A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_kind_name_c A.Prog.asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memcpy_cF_on A.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F2F A.Prog.Seg.F2Fs_on A.Prog.Seg.F2 A.Prog.Seg.F1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* Qualified vocabulary (QFIX: the six doubled modules and every lib/Lib module through an absolute alias). *)
Module CK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CKB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LSP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module CC := A.ACtlCut.
Module CP := A.ACtlCutP.
Module ART := A.AsanRT.
Module SM := A.Prog.SlotModel.
Module KNA := A.Prog.reac_ctrl_kind_name_c.
Module MN := A.MemNorm.
Module MNT := A.MemNormTr.
Module PB := A.ProgBridge.
Module PW := A.ProgWorld.
Module KM := A.ACtlG.KitMem.

Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. Generic helpers (no Section variable).  Everything else this file needs about memory across a run is
   KitMem's (lib/A/ACtlG/KitMem.v, single writer a Theorem Labs lane): kitmem_lift, kitmem_own6, kitmem_frac_keep,
   kitmem_spill_munch, kitmem_bytes_munch, kitmem_q64_munch, kitmem_addr_munch,
   kitmem_arodataS_journal, kitmem_awr_win, kitmem_rng_win / rng_heap / rng_heap_sh_span. *)

(* A register read through the cut's rgv is the run's canonical map entry. *)
Lemma f2g_rg : forall (regs : bvmap 5 word) (r : bv 5) (v : word),
  CK.getr regs r = v -> bv_eqb r 0 = false -> Sem.reg_get regs r = v.
Proof. intros regs r v H E. unfold CK.getr in H. rewrite E in H. exact H. Qed.

(* Two values the same register holds agree modulo 2 ^ 64. *)
Lemma f2g_rgv_mod : forall regs r (v w : Z),
  CC.rgv regs r v -> CC.rgv regs r w -> v mod 2 ^ 64 = w mod 2 ^ 64.
Proof.
  intros regs r v w Hv Hw. unfold CC.rgv in Hv, Hw. rewrite Hv in Hw.
  pose proof (f_equal bv_unsigned Hw) as E.
  rewrite !LMS.unsigned_lit_wrap in E. exact E.
Qed.

(* stk over a window the run does not write. *)
Lemma f2g_stk_munch : forall (WR : list LF.ivl) (m m' : word -> option byte) (lo hi : Z),
  LF.stk A.Img0.rsegs m lo hi -> LF.munch WR m m' ->
  (forall x, lo <= x < hi -> LF.outside WR x) ->
  LF.stk A.Img0.rsegs m' lo hi.
Proof.
  intros WR m m' lo hi (H0 & H1 & H) MU HO. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  assert (E : m' (LM.wa a) = m (LM.wa a))
    by (apply MU; rewrite LM.wa_unsigned by lia; exact (HO a Ha)).
  split.
  - unfold wview in Hv |- *. rewrite E. exact Hv.
  - exists b. unfold LM.mrd in Hb |- *. rewrite E. exact Hb.
Qed.

(* pairwise zdisjoint over non-degenerate ranges has no repeated entry. *)
Lemma f2g_nodup : forall (bl : list (Z * Z)),
  Forall (fun b => 0 <= snd b) bl ->
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint
    (map (fun b : Z * Z => (fst b, Reusable.YG00.req_size (snd b))) bl) ->
  List.NoDup bl.
Proof.
  induction bl as [|x bl IH]; intros HF HP; [constructor|].
  cbn [map Reusable.YG0f.pairwise] in HP. destruct HP as (HFa & HP).
  inversion HF as [|? ? Hx HFt]; subst.
  constructor; [|exact (IH HFt HP)].
  intros Hin.
  pose proof (proj1 (Forall_forall _ _) HFa (fst x, Reusable.YG00.req_size (snd x))
                (in_map (fun b : Z * Z => (fst b, Reusable.YG00.req_size (snd b))) bl x Hin)) as Hd.
  unfold Reusable.YG0f.zdisjoint, Reusable.YG00.req_size in Hd. cbn [fst snd] in Hd.
  destruct (Z.eqb_spec (snd x) 0) as [E|E]; cbn beta iota in Hd; lia.
Qed.

Lemma f2g_new_block : forall (bl L : list (Z * Z)) (x : Z * Z),
  Permutation bl (L ++ [x]) -> List.NoDup bl -> ~ List.In x L.
Proof.
  intros bl L x HP HN.
  assert (HN' : List.NoDup (L ++ [x])) by (apply (Permutation_NoDup HP); exact HN).
  pose proof (List.NoDup_remove_2 L [] x HN') as H2. rewrite app_nil_r in H2. exact H2.
Qed.

(* route (C): the aligned shadow-word span of a sub-range [x, x + N) of [p, hi) lies in the 8-aligned shadow-word
   cover of [p, hi), the form of ACtlRtC.cut_shadow's (L) disjunct (with hi = p + req_size n). *)
Lemma f2g_sh_word_blk : forall p hi x N a, p <= x -> x + N <= hi ->
  A.Prog.sh_word_on.sh_word_on x N a ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= a < Reusable.YG0f.shadow_addr (hi - 1) / 8 * 8 + 8.
Proof.
  intros p hi x N a Hpx Hxh (HN & Hlo & Hhi).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, ART.shadow_addr, ART.ASAN_K in Hlo, Hhi.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  assert (H1 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (H2 : (x + N - 1) / 8 <= (hi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (H3 : (0x7fff8000 + p / 8) / 8 <= (x / 8 + 0x7fff8000) / 8) by (apply Z.div_le_mono; lia).
  assert (H4 : ((x + N - 1) / 8 + 0x7fff8000) / 8 <= (0x7fff8000 + (hi - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The stage. *)

Section GlueF2.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :305-310), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81da4_at := (ACtlCutP.C_A81da4_at B).
Local Notation C_A81dd0_at := (ACtlCutP.C_A81dd0_at B).
Local Notation C_A81e54_at := (ACtlCutP.C_A81e54_at B).

(* ACtl.v:244: the core's AR law record (YCbq Section a0, YCbq.v:207). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* ACtl.v:226: the read-only span lies in the loaded image. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
(* ACtl.v:259: the core's symbol facts for B. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* ACtl.v:238: the kind-name table (KIND_NAME = 0x9e760, 112 bytes) lies in the read-only span. *)
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.

(* the core's application window is ctrl's (kLowShadowBeg < LOWMEM_END, ASAN_CEIL < APPMEM_END). *)
Lemma f2g_app_mem_of : forall a, Reusable.YG0f.app_addr a -> ART.app_mem a.
Proof.
  intros a Ha. pose proof Reusable.YCbq.asan_consts as (Hc & _).
  unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL, ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in *.
  lia.
Qed.

(* ---- the body bundles of the frame loop across a run's write set WR ----
   Each takes: the bundle at the cut's memory, the run's munch, the base register, and the three range facts
   that put the bundle's own bytes outside WR (the spill block [A + 32, A + 304), the class-6 frame
   [fr, fr + 4096) and the input block [c_p, c_p + c_n)).  The shadow bytes they read are covered once, by
   `in_shadow x -> outside WR x` (every write of this stage is application memory). *)

Lemma f2g_PRO_munch : forall cx fr (regs : bvmap 5 word) (m m' : word -> option byte) (Asp : Z)
    (WR : list LF.ivl),
  CP.PRO cx fr regs m -> LF.munch WR m m' -> CC.rgv regs 9 Asp -> 0 <= Asp -> Asp + 416 <= 2 ^ 64 ->
  Z.of_nat (length (CC.c_in cx)) = CC.c_n cx ->
  (forall x, ART.in_shadow x -> LF.outside WR x) ->
  (forall x, Asp + 32 <= x < Asp + 216 \/ Asp + 240 <= x < Asp + 304 -> LF.outside WR x) ->
  (forall x, fr <= x < fr + 4096 -> LF.outside WR x) ->
  (forall x, CC.c_p cx <= x < CC.c_p cx + CC.c_n cx -> LF.outside WR x) ->
  CP.PRO cx fr regs m'.
Proof.
  intros cx fr regs m m' Asp WR HP MU H9 HA0 HA64 Hlen KSH KA KF KI.
  destruct HP as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & HA2624 & HPB & HPG &
                  P184 & P256 & P264 & P272 & P32).
  assert (SPK : forall off v, 32 <= off <= 208 \/ 240 <= off <= 296 ->
            CP.spill regs m off v -> CP.spill regs m' off v).
  { intros off v Hoff Hs.
    exact (KM.kitmem_spill_munch WR regs regs m m' off v Asp Hs H9 HA0 ltac:(lia) ltac:(lia) MU eq_refl
             ltac:(intros x Hx; apply KA; lia)). }
  split; [exact (SPK 40 _ ltac:(lia) S40)|]. split; [exact (SPK 120 _ ltac:(lia) S120)|].
  split; [exact (SPK 136 _ ltac:(lia) S136)|]. split; [exact (SPK 160 _ ltac:(lia) S160)|].
  split; [exact (SPK 168 _ ltac:(lia) S168)|]. split; [exact (SPK 176 _ ltac:(lia) S176)|].
  split; [exact (SPK 208 _ ltac:(lia) S208)|]. split; [exact (SPK 248 _ ltac:(lia) S248)|].
  split; [exact (KM.kitmem_addr_munch WR m m' (fr + 2624) 6 HA2624 MU KSH)|].
  split; [exact (KM.kitmem_bytes_munch WR m m' (CC.c_p cx) (CC.c_in cx) HPB MU
                   ltac:(intros x Hx; apply KI; lia))|].
  split; [intros Hn; exact (KM.kitmem_addr_munch WR m m' (CC.c_p cx) (CC.c_n cx) (HPG Hn) MU KSH)|].
  split; [exact (SPK 184 _ ltac:(lia) P184)|]. split; [exact (SPK 256 _ ltac:(lia) P256)|].
  split; [exact (SPK 264 _ ltac:(lia) P264)|]. split; [exact (SPK 272 _ ltac:(lia) P272)|].
  exact (SPK 32 _ ltac:(lia) P32).
Qed.

Lemma f2g_FLC_munch : forall fr (regs : bvmap 5 word) (m m' : word -> option byte) (Asp : Z)
    (WR : list LF.ivl),
  CP.FLC fr regs m -> LF.munch WR m m' -> CC.rgv regs 9 Asp -> 0 <= Asp -> Asp + 416 <= 2 ^ 64 ->
  (forall x, ART.in_shadow x -> LF.outside WR x) ->
  (forall x, Asp + 32 <= x < Asp + 216 \/ Asp + 240 <= x < Asp + 304 -> LF.outside WR x) ->
  CP.FLC fr regs m'.
Proof.
  intros fr regs m m' Asp WR HC MU H9 HA0 HA64 KSH KA.
  destruct HC as (S256 & S184 & S192 & S80 & S88 & S96 & S272 & S264 & HA72 & HA38 & S72 & S64 & S56 & S48).
  assert (SPK : forall off v, 32 <= off <= 208 \/ 240 <= off <= 296 ->
            CP.spill regs m off v -> CP.spill regs m' off v).
  { intros off v Hoff Hs.
    exact (KM.kitmem_spill_munch WR regs regs m m' off v Asp Hs H9 HA0 ltac:(lia) ltac:(lia) MU eq_refl
             ltac:(intros x Hx; apply KA; lia)). }
  split; [exact (SPK 256 _ ltac:(lia) S256)|]. split; [exact (SPK 184 _ ltac:(lia) S184)|].
  split; [exact (SPK 192 _ ltac:(lia) S192)|]. split; [exact (SPK 80 _ ltac:(lia) S80)|].
  split; [exact (SPK 88 _ ltac:(lia) S88)|]. split; [exact (SPK 96 _ ltac:(lia) S96)|].
  split; [exact (SPK 272 _ ltac:(lia) S272)|]. split; [exact (SPK 264 _ ltac:(lia) S264)|].
  split; [exact (KM.kitmem_addr_munch WR m m' (CP.fragb fr) 72 HA72 MU KSH)|].
  split; [exact (KM.kitmem_addr_munch WR m m' (fr + 2688) 38 HA38 MU KSH)|].
  split; [exact (SPK 72 _ ltac:(lia) S72)|]. split; [exact (SPK 64 _ ltac:(lia) S64)|].
  split; [exact (SPK 56 _ ltac:(lia) S56) | exact (SPK 48 _ ltac:(lia) S48)].
Qed.

Lemma f2g_IFS_munch : forall cx fr (jj : nat) (regs : bvmap 5 word) (m m' : word -> option byte) (Asp : Z)
    (WR : list LF.ivl),
  CP.IFS cx fr jj regs m -> LF.munch WR m m' -> CC.rgv regs 9 Asp -> 0 <= Asp -> Asp + 416 <= 2 ^ 64 ->
  (forall x, ART.in_shadow x -> LF.outside WR x) ->
  (forall x, Asp + 32 <= x < Asp + 216 \/ Asp + 240 <= x < Asp + 304 -> LF.outside WR x) ->
  (forall x, fr <= x < fr + 4096 -> LF.outside WR x) ->
  CP.IFS cx fr jj regs m'.
Proof.
  intros cx fr jj regs m m' Asp WR HI MU H9 HA0 HA64 KSH KA KF.
  destruct HI as ((HID & Hidok) & (HFG & Hfgok) & (S104 & S112 & HBD & HAB & HFI)).
  destruct (A.Prog.Seg.F1.f1_FS_len (CC.c_in cx) jj) as (L1 & L2).
  pose proof (A.Prog.Seg.F1.f1_body_len (CC.c_in cx) jj) as L3.
  assert (SPK : forall off v, 32 <= off <= 208 \/ 240 <= off <= 296 ->
            CP.spill regs m off v -> CP.spill regs m' off v).
  { intros off v Hoff Hs.
    exact (KM.kitmem_spill_munch WR regs regs m m' off v Asp Hs H9 HA0 ltac:(lia) ltac:(lia) MU eq_refl
             ltac:(intros x Hx; apply KA; lia)). }
  split; [split; [|exact Hidok]|split; [split; [|exact Hfgok]|]].
  - unfold CP.IDBe in *.
    apply (KM.kitmem_bytes_munch WR m m' (fr + 2688) _ HID MU). rewrite L1.
    intros x Hx. apply KF. lia.
  - unfold CP.FGBe in *.
    apply (KM.kitmem_bytes_munch WR m m' (fr + 2768) _ HFG MU). rewrite L2.
    intros x Hx. apply KF. lia.
  - split; [exact (SPK 104 _ ltac:(lia) S104)|]. split; [exact (SPK 112 _ ltac:(lia) S112)|].
    split.
    { apply (KM.kitmem_bytes_munch WR m m' (fr + 2880) _ HBD MU).
      intros x Hx. apply KF. lia. }
    split; [|exact HFI].
    exact (KM.kitmem_addr_munch WR m m' (fr + 2880) 35 HAB MU KSH).
Qed.

(* the spill cell of the base register, as the q64 word b5_SPILL names. *)
Lemma f2g_spill_q : forall (regs : bvmap 5 word) (m : word -> option byte) (Asp off v : Z),
  CP.spill regs m off v -> CC.rgv regs 9 Asp -> 0 <= Asp -> 0 <= off -> Asp + off + 8 <= 2 ^ 64 ->
  CP.q64 m (Asp + off) v.
Proof.
  intros regs m Asp off v (A1 & HA1 & Hq) H9 HA0 Hoff Hhi.
  assert (EA : A1 = Asp).
  { unfold CC.rgv in HA1, H9. rewrite H9 in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LM.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

Lemma f2g_FLSH_munch : forall cx (jj : nat) fr (regs : bvmap 5 word) (m m' : word -> option byte) (Asp : Z)
    (WR : list LF.ivl),
  CP.FLSH cx jj fr regs m -> LF.munch WR m m' -> CC.rgv regs 9 Asp -> 0 <= Asp -> Asp + 416 <= 2 ^ 64 ->
  Z.of_nat (length (CC.c_in cx)) = CC.c_n cx ->
  (forall x, ART.in_shadow x -> LF.outside WR x) ->
  (forall x, Asp + 32 <= x < Asp + 216 \/ Asp + 240 <= x < Asp + 304 -> LF.outside WR x) ->
  (forall x, fr <= x < fr + 4096 -> LF.outside WR x) ->
  (forall x, CC.c_p cx <= x < CC.c_p cx + CC.c_n cx -> LF.outside WR x) ->
  CP.FLSH cx jj fr regs m'.
Proof.
  intros cx jj fr regs m m' Asp WR HI MU H9 HA0 HA64 Hlen KSH KA KF KI.
  destruct HI as (HPRO & S128 & HSTK & S144 & HA2691).
  assert (SPK : forall off v, 32 <= off <= 208 \/ 240 <= off <= 296 ->
            CP.spill regs m off v -> CP.spill regs m' off v).
  { intros off v Hoff Hs.
    exact (KM.kitmem_spill_munch WR regs regs m m' off v Asp Hs H9 HA0 ltac:(lia) ltac:(lia) MU eq_refl
             ltac:(intros x Hx; apply KA; lia)). }
  split; [exact (f2g_PRO_munch cx fr regs m m' Asp WR HPRO MU H9 HA0 HA64 Hlen KSH KA KF KI)|].
  split; [exact (SPK 128 _ ltac:(lia) S128)|].
  split.
  { apply (f2g_stk_munch WR m m' fr (fr + CP.FRAME_BYTES) HSTK MU).
    intros x Hx. apply KF. unfold CP.FRAME_BYTES in *. lia. }
  split; [exact (SPK 144 _ ltac:(lia) S144)|].
  exact (KM.kitmem_addr_munch WR m m' (fr + 2691) 17 HA2691 MU KSH).
Qed.

Lemma f2g_LK_munch : forall cx fr (jj : nat) (regs : bvmap 5 word) (m m' : word -> option byte)
    (WR : list LF.ivl),
  CP.LK cx fr jj regs m -> LF.munch WR m m' ->
  (forall x, fr <= x < fr + 4096 -> LF.outside WR x) ->
  CP.LK cx fr jj regs m'.
Proof.
  intros cx fr jj regs m m' WR (Hj & H21 & HOUR) MU KF.
  split; [exact Hj|]. split; [exact H21|].
  unfold CP.OURb in *.
  assert (E6 : Z.of_nat (length (SM.OUR (CC.c_in cx))) = 6)
    by (unfold SM.OUR; rewrite length_map, length_seq; reflexivity).
  apply (KM.kitmem_bytes_munch WR m m' (fr + 2624) _ HOUR MU).
  intros x Hx. apply KF. lia.
Qed.

(* ---- b5_KN at any cut of this walk: the kind-name table's BYTES from the entry's arodata_okS carried by the
   journal's image clause, its SHADOW from the bundle's zero-shadow row. ---- *)
Lemma f2g_kn : forall (cx : CC.ctlcx) ly' S' (W' : Reusable.YA0n.world segs) (m' : word -> option byte) md'
    (own : list (Z * Z)) (k : Z),
  CC.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (CC.c_sp cx) []
    (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx) own ly' S' W' m' md' k ->
  CP.b5_KN m'.
Proof.
  intros cx ly' S' W' m' md' own k HBASE HJ.
  pose proof HBASE as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _).
  pose proof (KM.kitmem_arodataS_journal (SK := A.AE2k.tfib_sink_head) B RLO RHI A.ACfn.LLVMF_STK (CC.c_sp cx)
                (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx) own ly' S' W' m' md' k
                RELRO_IMG HJ Haro) as HA'.
  pose proof HJ as (HAR' & _).
  destruct RELRO_KIND_NAME as [KN1 KN2].
  assert (EKN : KNA.KIND_NAME = 0x9e760) by reflexivity. rewrite <- EKN in KN1, KN2.
  split.
  - (* the 112 bytes *)
    split; [unfold KNA.KIND_NAME; lia|].
    rewrite A.Prog.Seg.F2.f2_kn_len. split; [unfold KNA.KIND_NAME; lia|].
    intros i Hi.
    assert (Hra : RLO <= KNA.KIND_NAME + Z.of_nat i < RHI) by lia.
    assert (Hno : ~ Exists (Reusable.YG0n.in_zr (KNA.KIND_NAME + Z.of_nat i))
                    (Reusable.YG0f.as_owned_static B)).
    { rewrite (A.AF0m.ts_owned B TFIB_SYMS). unfold A.AF0m.Tfib_owned_static.
      rewrite Exists_exists. intros (r & Hr & Hz).
      unfold Reusable.YG0n.in_zr in Hz. unfold KNA.KIND_NAME in Hz. cbn [In] in Hr.
      repeat (destruct Hr as [Hr0 | Hr]; [subst r; cbn [fst snd] in Hz; lia|]). exact Hr. }
    assert (Herr : ~ (Reusable.YG0f.as_errno B <= KNA.KIND_NAME + Z.of_nat i <
                      Reusable.YG0f.as_errno B + 4)).
    { rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO, KNA.KIND_NAME. lia. }
    pose proof (HA' (KNA.KIND_NAME + Z.of_nat i) (or_intror Hra) Hno Herr) as Hv.
    assert (Hrom : CK.seg_rom segs (Z_to_bv 64 (KNA.KIND_NAME + Z.of_nat i)) =
                   nth_error KNA.kind_name_bytes i) by exact (A.Prog.Seg.F2.f2_kn_rom i Hi).
    rewrite Hrom in Hv.
    destruct (nth_error KNA.kind_name_bytes i) as [b|] eqn:Eb;
      [|exfalso; apply nth_error_None in Eb; rewrite A.Prog.Seg.F2.f2_kn_len in Eb; lia].
    cbn [option_map] in Hv.
    pose proof (A.ProgWorldCtlRt.aview_some_vis W' m' (KNA.KIND_NAME + Z.of_nat i) (bv_unsigned b) Hv) as Hvis.
    pose proof (PW.mrd_of_aview_some W' m' (KNA.KIND_NAME + Z.of_nat i) (bv_unsigned b) Hvis Hv) as Hm.
    assert (G : LM.mrd segs m' (LM.wa (KNA.KIND_NAME + Z.of_nat i)) = Some (Z_to_bv 8 (bv_unsigned b)))
      by exact Hm.
    rewrite G. f_equal. apply Z_to_bv_bv_unsigned.
  - (* the 112 shadow bytes: the bundle's zero-shadow row that covers the table, the record row
       (0x21aa0, 0x9e7d0 - 0x21aa0) of AF0m.Tfib_zero_shadow (found by membership, not by position) *)
    split; [unfold KNA.KIND_NAME; lia|]. split; [lia|].
    split; [unfold KNA.KIND_NAME, ART.APPMEM_END; lia|].
    intros i Hi. split; [unfold ART.app_mem, ART.LOWMEM_END, KNA.KIND_NAME; lia|].
    assert (Hrow : In (0x21aa0, 0x9e7d0 - 0x21aa0) (Reusable.YG0n.zero_shadow_ranges B ly')).
    { unfold Reusable.YG0n.zero_shadow_ranges. rewrite (A.AF0m.ts_zsh B TFIB_SYMS).
      unfold A.AF0m.Tfib_zero_shadow. cbn [In].
      repeat (first [left; reflexivity | right]). }
    pose proof (Reusable.YG0d.al_zshadow segs B LAWS ly' S' W' m' md'
                  (0x21aa0, 0x9e7d0 - 0x21aa0) HAR' Hrow) as HZS.
    cbn [fst snd] in HZS. unfold Reusable.YG0v.zero_shadow in HZS.
    assert (Hidx : 0 <= ART.shadow_addr (KNA.KIND_NAME + i) -
                        Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x21aa0 <
                        (0x9e7d0 - 0x21aa0) / 8).
    { unfold ART.shadow_addr, ART.ASAN_K, Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF,
        KNA.KIND_NAME. Z.div_mod_to_equations. lia. }
    pose proof (HZS _ Hidx) as Hz.
    replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x21aa0 +
             (ART.shadow_addr (KNA.KIND_NAME + i) -
              Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x21aa0))
      with (ART.shadow_addr (KNA.KIND_NAME + i)) in Hz by ring.
    pose proof (A.ProgWorldCtlRt.aview_some_vis W' m' (ART.shadow_addr (KNA.KIND_NAME + i)) 0 Hz) as Hvis.
    pose proof (PW.mrd_of_aview_some W' m' (ART.shadow_addr (KNA.KIND_NAME + i)) 0 Hvis Hz) as Hm.
    exists (Z_to_bv 8 0). split; [exact Hm|]. left. reflexivity.
Qed.

(* route (C): ctl_rt_C at any cut of this walk, from the cut journal's AR (a Theorem Labs lane's ctl_rt_C_of_AR: CtrlTSyms +
   AR_laws only) and the entry's arodata_okS carried by the journal's image clause (as f2g_kn). *)
Lemma f2g_rtC : forall (cx : CC.ctlcx) ly' S' (W' : Reusable.YA0n.world segs) (m' : word -> option byte) md'
    (own : list (Z * Z)) (k : Z),
  CC.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (CC.c_sp cx) []
    (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx) own ly' S' W' m' md' k ->
  A.ACtlRtC.ctl_rt_C B ly' S' m'.
Proof.
  intros cx ly' S' W' m' md' own k HBASE HJ.
  pose proof HBASE as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _).
  pose proof (KM.kitmem_arodataS_journal (SK := A.AE2k.tfib_sink_head) B RLO RHI A.ACfn.LLVMF_STK (CC.c_sp cx)
                (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx) own ly' S' W' m' md' k
                RELRO_IMG HJ Haro) as HA'.
  pose proof HJ as (HAR' & _).
  exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly' S' W' m' md' HAR'
           (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HA' (Z.le_refl _) (Z.le_refl _))).
Qed.

Lemma glue_seg_F2 : forall POST (j : nat),
  CF POST (ix_cut C_A81dd0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81da4_at [Z.of_nat j]).
Proof.
  intros POST j HX HZ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* route (C): the cut's ctl_rt_C (ACtlRtC.v:44-46) *)
  destruct Hrt as (Hcells & Hcut & Himg & Hroag).
  (* G1: the entry cut at index [Z.of_nat j] (ACtlCutP.v:1966-1977) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81da4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hn26 & Hj255 & Ha0 & HHB & HLK & HFC & HFLSH & HINb & H248 & HIFS & HFLC).
  (* G2: the numeric and world facts the two runs and the two exit bodies read, all from VISIBLE state. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hceil_lo & Hlo_sp & Hsp_hi & Hhi47 & _).
  change (2 ^ 47) with 140737488355328 in Hhi47.
  destruct (KM.kitmem_own6 (SK := A.AE2k.tfib_sink_head) B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efra & Hfr4096 & Hfr32 & HfrC & HCsp).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfb6 in HfrC. unfold A.ACfn.LLVMF_STK in HCsp, Hlo_sp.
  pose proof Reusable.YCbq.asan_consts as (Hceilv & _).
  pose proof HFRAC as (Asp & sp & E2 & Hsp16 & Hspz & E4 & R8 & R9 & E3 & R19 & R26 & Hfrm32 & HA32 & HAsp &
                       HspA & HfrA & HA416 & Hsp4096 & HSapp & _).
  unfold CP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp.
  assert (HfrAsp : fr + 4096 <= Asp) by lia.
  (* the block the turn allocated *)
  assert (Hinphi : In (phi, CP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (CP.flen cx j) HAR Hinphi)
    as (Hph16 & Hph4096 & HphC & Hphapp & HphAll & Hpw & Hphn).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (CP.flen cx j) 6
                (CC.c_fpos cx) HAR Hinphi Hin6) as Hdjfr.
  rewrite Efra, Hfb6 in Hdjfr. unfold Reusable.YG0f.zdisjoint in Hdjfr. cbn [fst snd] in Hdjfr.
  assert (Hreq : 0 < Reusable.YG00.req_size (CP.flen cx j)).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (CP.flen cx j) 0); lia. }
  (* the block of this turn is new since the entry (the live list has no repeated entry, AR_blocks_law) *)
  assert (Hnd : List.NoDup (Reusable.YG0d.ablocks B ly3 S3)).
  { apply f2g_nodup; [|exact Hpw].
    apply Forall_forall. intros b Hb. destruct b as [p n]. cbn [snd].
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n HAR Hb)
      as (_ & _ & _ & _ & _ & _ & Hn0). lia. }
  pose proof (f2g_new_block (Reusable.YG0d.ablocks B ly3 S3)
                (Reusable.YG0d.ablocks B (CC.c_ly cx) (CC.c_S cx)) (phi, CP.flen cx j) Hperm Hnd) as Hnew.
  (* the entry's lib pre *)
  pose proof HB as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & Hpn & Hnlen & _ & _ & _ & _ & Haro & _).
  assert (Hdjin : CC.c_n cx = 0 \/
                  (In (CC.c_p cx, CC.c_n cx) (Reusable.YG0d.ablocks B ly3 S3) /\
                   (CC.c_p cx + CC.c_n cx <= phi \/
                    phi + Reusable.YG00.req_size (CP.flen cx j) <= CC.c_p cx) /\
                   4096 <= CC.c_p cx /\
                   CC.c_p cx + CC.c_n cx <=
                     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling)).
  { destruct Hpn as [(Hz0 & _) | (Hgt & Hin0)]; [left; exact Hz0 | right].
    assert (Hin : In (CC.c_p cx, CC.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin0).
    assert (Hne : (CC.c_p cx, CC.c_n cx) <> (phi, CP.flen cx j))
      by (intros E; apply Hnew; rewrite <- E; exact Hin0).
    pose proof (Reusable.YCbq.sep_blocks segs B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) phi
                  (CP.flen cx j) HAR Hin Hinphi Hne) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) HAR Hin)
      as (_ & Hp4096 & HpC & _ & _ & _ & _).
    assert (Ereq : Reusable.YG00.req_size (CC.c_n cx) = CC.c_n cx)
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (CC.c_n cx) 0); lia).
    rewrite Ereq in Hd, HpC.
    split; [exact Hin|]. split; [exact Hd|]. split; [exact Hp4096 | exact HpC]. }
  assert (Hinlo : forall x, CC.c_p cx <= x < CC.c_p cx + CC.c_n cx -> x < Asp).
  { intros x Hx. destruct Hdjin as [Hz0|(_ & _ & _ & H2)]; lia. }
  assert (Happin : forall x, CC.c_p cx <= x < CC.c_p cx + CC.c_n cx -> ART.app_mem x).
  { intros x Hx. destruct Hdjin as [Hz0|(Hin & _ & _ & _)]; [lia|].
    apply f2g_app_mem_of.
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) HAR Hin)
      as (_ & _ & _ & Happ & _).
    apply (Reusable.YG0f.in_app_addr _ _ x Happ).
    unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (CC.c_n cx) 0); lia. }
  (* application memory of the frame and of the block *)
  assert (Happfr : forall x, fr <= x < fr + 4096 -> ART.app_mem x).
  { intros x Hx. apply f2g_app_mem_of.
    destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (CC.c_fpos cx) HAR Hin6)
      as (_ & _ & Happ). rewrite Efra, Hfb6 in Happ.
    exact (Reusable.YG0f.in_app_addr fr 4096 x Happ ltac:(lia)). }
  assert (Happph : forall x, phi <= x < phi + Reusable.YG00.req_size (CP.flen cx j) -> ART.app_mem x).
  { intros x Hx. apply f2g_app_mem_of. exact (Reusable.YG0f.in_app_addr _ _ x Hphapp Hx). }
  assert (Happsp : forall x, Asp <= x < Asp + 416 -> ART.app_mem x).
  { intros x Hx. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  assert (Hnimgsp : forall x, Asp <= x < Asp + 416 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. apply KM.kitmem_not_img_hi. unfold A.Prog.ImgBounds.IMG_HI. lia. }
  assert (Hnimgph : forall x, phi <= x < phi + Reusable.YG00.req_size (CP.flen cx j) ->
                    ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. exact (Reusable.YCbq.blk_img segs B LAWS ly3 S3 W3 mem3 md3 phi (CP.flen cx j) x HAR
                          Hinphi Hx). }
  (* the two spill words of the segment are present at the cut *)
  assert (Hrwex : forall a, CC.c_sp cx - 32768 <= a -> a + 8 <= CC.c_sp cx ->
            exists jb, LSP.rw_cells A.Img0.rsegs mem3 a [LC.CB 8 jb]).
  { intros a H1 H2. apply (A.Prog.Seg.F2.f2_rw_ex mem3 a 8 ltac:(lia) ltac:(lia)).
    intros x Hx. destruct (Hpres x ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hh & b & Hb).
    split; [exact (KM.kitmem_wview_some mem3 (Z_to_bv 64 x) b Hb)
           | exists b; exact (KM.kitmem_mrd_some mem3 (Z_to_bv 64 x) b Hb)]. }
  destruct (Hrwex (Asp + 216) ltac:(lia) ltac:(lia)) as (j1 & HR216).
  destruct (Hrwex (Asp + 232) ltac:(lia) ltac:(lia)) as (j2 & HR232).
  (* the footprint and its two segment ranges *)
  pose proof (PB.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)) as HFPA.
  assert (Hrng216 : LEF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (Asp + 216) 8).
  { eapply (KM.kitmem_rng_win (SK := A.AE2k.tfib_sink_head)); [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (Hrng232 : LEF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (Asp + 232) 8).
  { eapply (KM.kitmem_rng_win (SK := A.AE2k.tfib_sink_head)); [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  (* the register facts the two runs take *)
  destruct HFC as (S224 & R20 & R18).
  assert (E9 : Sem.reg_get regs3 9 = Z_to_bv 64 Asp)
    by exact (f2g_rg regs3 9 _ R9 ltac:(vm_compute; reflexivity)).
  assert (E10 : Sem.reg_get regs3 10 = Z_to_bv 64 phi)
    by exact (f2g_rg regs3 10 _ Ha0 ltac:(vm_compute; reflexivity)).
  assert (E20 : Sem.reg_get regs3 20 = Z_to_bv 64 (CC.c_p cx + SM.t_body (CC.c_in cx) j))
    by exact (f2g_rg regs3 20 _ R20 ltac:(vm_compute; reflexivity)).
  (* the entry configuration in the run's form, at the run's canonical register map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (CC.cut_pc (ix_cut C_A81da4_at [Z.of_nat j])) with 531876.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR.mkR_of regs3) regs3 CK.fp_regs
           (Z_to_bv 64 531876) CK.fp_csr None mem3 (CK.seg_rom segs) md3 (POST cx));
    [| exact (LR.xregs_eqv_sym _ _ (LR.mkR_of_eqv regs3))].
  unfold LR.mkR_of.
  destruct (Z.eq_dec (CP.flen cx j) 0) as [Hz | Hnz].
  - (* ================= len = 0: the two spill stores, then 0x81e54 ================= *)
    assert (Hzt : SM.t_len (CC.c_in cx) j = 0) by (unfold CP.flen in Hz; exact Hz).
    assert (E18 : Sem.reg_get regs3 18 = Z_to_bv 64 0).
    { apply (f2g_rg regs3 18); [|vm_compute; reflexivity].
      unfold CC.rgv in R18. rewrite R18, Hzt. reflexivity. }
    pose proof (A.Prog.Seg.F2F.f2z_evt_F (PB.RNG_W (Reusable.YA0n.w_H W3))
        (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
        (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8)
        (Sem.reg_get regs3 9) (Sem.reg_get regs3 10) (Sem.reg_get regs3 11) (Sem.reg_get regs3 12)
        (Sem.reg_get regs3 13) (Sem.reg_get regs3 14) (Sem.reg_get regs3 15) (Sem.reg_get regs3 16)
        (Sem.reg_get regs3 17) (Sem.reg_get regs3 18) (Sem.reg_get regs3 19) (Sem.reg_get regs3 20)
        (Sem.reg_get regs3 21) (Sem.reg_get regs3 22) (Sem.reg_get regs3 23) (Sem.reg_get regs3 24)
        (Sem.reg_get regs3 25) (Sem.reg_get regs3 26) (Sem.reg_get regs3 27) (Sem.reg_get regs3 28)
        (Sem.reg_get regs3 29) (Sem.reg_get regs3 30) (Sem.reg_get regs3 31)
        CK.fp_regs CK.fp_csr mem3 Asp phi (CC.c_p cx + SM.t_body (CC.c_in cx) j) j1 j2
        E9 E10 E18 E20 ltac:(lia) ltac:(lia) ltac:(lia) HR216 HR232 Hrng216 Hrng232) as HRUN.
    apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
             HRUN HFPA).
    intros ms' md' Hrun HP Hsbm.
    pose proof HP as (m' & Ems & MU & WM & Q216 & Q232).
    assert (Emem : ms_mem ms' = m') by (rewrite Ems; reflexivity).
    destruct (PW.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) (PB.RNG_W (Reusable.YA0n.w_H W3)) _ ms'
                Hrun HFPA) as (Hgrow0 & Hhid).
    assert (Hgrow : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows mem3 m')
      by (rewrite <- Emem; exact Hgrow0).
    (* the write set: the two spill words *)
    assert (HOUT : forall x, x < Asp + 216 \/ Asp + 224 <= x < Asp + 232 \/ Asp + 240 <= x ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240)] x).
    { intros x Hx. cbn [LF.outside]. split; [lia|]. split; [lia | exact I]. }
    assert (HIN : forall x, ~ LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240)] x ->
              Asp + 216 <= x < Asp + 240).
    { intros x Hx.
      destruct (KM.kitmem_not_outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240)] x Hx)
        as (lo & hi & Hin & Hr).
      cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
    assert (KSH : forall x, ART.in_shadow x ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240)] x).
    { intros x Hx. apply HOUT.
      pose proof (A.AsanRTFacts.app_not_shadow x) as Hns.
      destruct (Z_lt_le_dec x (Asp + 216)) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (Asp + 240) x) as [H2|H2]; [right; right; exact H2|].
      exfalso. exact (Hns (Happsp x ltac:(lia)) Hx). }
    (* the journal across the two stores *)
    assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                    (CC.c_sp cx) [] (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx)
                    (CC.own6 cx) ly3 S3 W3 m' md' k).
    { rewrite <- Emem.
      eapply (PW.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx).
      2:{ exact Hrun. }
      { exact HJ. }
      { exact HFPA. }
      { rewrite Emem. exact MU. }
      { exact Hsbm. }
      { intros a Ha Ho. apply KM.kitmem_awr_win. pose proof (HIN a Ho) as Hr.
        unfold A.ACfn.LLVMF_STK. lia. } }
    (* the carried runtime facts: ctl_rt_C at the exit journal's AR (route (C)) *)
    pose proof (f2g_rtC cx ly3 S3 W3 m' md' (CC.own6 cx) k HB HJ') as Hrt'.
    (* the exit cut at 0x81e54 *)
    rewrite Ems.
    refine (HZ cx [Z.of_nat j] fr k ly3 S3 W3 _ m' md' HB HJ' HF HL Hk _ Hrt').
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81e54_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    (* the frame's own facts at the run's end memory *)
    assert (HFRAC' : CP.FRAC B cx fr fr regs3 m').
    { apply (KM.kitmem_frac_keep B cx fr fr regs3 mem3 m'
               [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240)] HFRAC MU Hgrow ltac:(lia)).
      - intros A0 HA0 x Hx. pose proof (f2g_rgv_mod regs3 9 A0 Asp HA0 R9) as Emod.
        apply HOUT. revert Emod. Z.div_mod_to_equations. lia.
      - intros x Hx. apply HOUT. lia.
      - intros x Hx. apply HOUT. lia. }
    assert (HFLSH' : CP.FLSH cx j fr regs3 m').
    { apply (f2g_FLSH_munch cx j fr regs3 mem3 m' Asp _ HFLSH MU R9 ltac:(lia) ltac:(lia)
               ltac:(lia) KSH); intros x Hx; apply HOUT; first [lia | pose proof (Hinlo x Hx); lia]. }
    assert (HIFS' : CP.IFS cx fr j regs3 m').
    { apply (f2g_IFS_munch cx fr j regs3 mem3 m' Asp _ HIFS MU R9 ltac:(lia) ltac:(lia) KSH);
        intros x Hx; apply HOUT; lia. }
    assert (HFLC' : CP.FLC fr regs3 m').
    { apply (f2g_FLC_munch fr regs3 mem3 m' Asp _ HFLC MU R9 ltac:(lia) ltac:(lia) KSH).
      intros x Hx. apply HOUT. lia. }
    assert (HLK' : CP.LK cx fr j regs3 m').
    { apply (f2g_LK_munch cx fr j regs3 mem3 m' _ HLK MU). intros x Hx. apply HOUT. lia. }
    assert (HINb' : CP.f1_IN cx m').
    { destruct HINb as (HIN1 & HIN2). split.
      - exact (KM.kitmem_addr_munch _ mem3 m' (CC.c_p cx) (CC.c_n cx) HIN1 MU KSH).
      - apply (KM.kitmem_bytes_munch _ mem3 m' (CC.c_p cx) (CC.c_in cx) HIN2 MU).
        intros x Hx. apply HOUT. rewrite <- Hnlen in Hx. pose proof (Hinlo x Hx). lia. }
    assert (S248' : CP.spill regs3 m' 248 (fr + 176)).
    { exact (KM.kitmem_spill_munch _ regs3 regs3 mem3 m' 248 _ Asp H248 R9 ltac:(lia) ltac:(lia)
               ltac:(lia) MU eq_refl ltac:(intros x Hx; apply HOUT; lia)). }
    assert (S224' : CP.spill regs3 m' 224 (SM.t_left (CC.c_in cx) j - SM.t_h (CC.c_in cx) j)).
    { exact (KM.kitmem_spill_munch _ regs3 regs3 mem3 m' 224 _ Asp S224 R9 ltac:(lia) ltac:(lia)
               ltac:(lia) MU eq_refl ltac:(intros x Hx; apply HOUT; lia)). }
    assert (S216' : CP.spill regs3 m' 216 (CC.c_p cx + SM.t_body (CC.c_in cx) j))
      by (exists Asp; split; [exact R9 | exact Q216]).
    assert (Htb : SM.t_big (CC.c_in cx) j = false)
      by (unfold SM.t_big; rewrite Hzt; reflexivity).
    split; [exact HFRAC'|].
    exists phi.
    split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
    split.
    { destruct HHB as (Hp0 & Had). split; [exact Hp0|].
      exact (KM.kitmem_addr_munch _ mem3 m' phi (A.ACtlK.a_size (CP.flen cx j)) Had MU KSH). }
    split.
    { split; [exact HFLSH'|]. split; [exact S216'|]. split; [exact S224'|].
      split; [exact S248'|]. split; [exact HINb' | exact HFLC']. }
    split; [exact HLK'|].
    split.
    { (* b5_C *)
      split; [reflexivity|].
      split; [unfold CC.rgv; rewrite Hz; reflexivity|].
      split.
      { exists Asp. split; [exact R9|]. split; [lia|]. split.
        - destruct HFLSH' as ((_ & _ & _ & _ & _ & _ & _ & P248 & _ & _ & _ & P184 & P256 & P264 & P272 & _)
                              & _ & _ & P144 & _).
          destruct HFLC' as (_ & _ & P192 & P80 & P88 & P96 & _ & _).
          split; [exact (f2g_spill_q regs3 m' Asp 248 _ P248 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 256 _ P256 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 144 _ P144 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 184 _ P184 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 192 _ P192 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 80 _ P80 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 88 _ P88 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 96 _ P96 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 272 _ P272 R9 ltac:(lia) ltac:(lia) ltac:(lia))
                 | exact (f2g_spill_q regs3 m' Asp 264 _ P264 R9 ltac:(lia) ltac:(lia) ltac:(lia))].
        - rewrite Htb. exact Q232. }
      split; [split; intros Hl; exfalso; lia|].
      split.
      { destruct HFLC' as (_ & _ & _ & _ & _ & _ & _ & _ & HA72 & HA38 & _).
        destruct HIFS' as (_ & (HFG & _) & _).
        split; [exact HA72|]. split; [exact HA38|].
        split; [exact HFG | exact (proj2 (A.Prog.Seg.F1.f1_FS_len (CC.c_in cx) j))]. }
      split; [exact (f2g_kn cx ly3 S3 W3 m' md' (CC.own6 cx) k HB HJ')|].
      destruct HIFS' as (_ & HFGj & HFSj). split; [exact HFGj | exact HFSj]. }
    (* P: the len = 0 arm's own three conjuncts *)
    split; [exact Hz|].
    split.
    { unfold CP.FRAME_BYTES. unfold Reusable.YG00.req_size in Hdjfr.
      destruct (Z.eqb_spec (CP.flen cx j) 0) as [_|Hne]; [|exfalso; exact (Hne Hz)].
      destruct Hdjfr as [H|H]; [left; lia | right; lia]. }
    split; [exact (proj1 HIFS')|].
    exists Asp. split; [exact R9|]. split; [lia|].
    split; [intros Hl; exfalso; lia|].
    intros H8819. exfalso. unfold SM.t_8819 in H8819. rewrite Htb in H8819.
    cbn [andb] in H8819. discriminate H8819.
  - (* ================= len > 0: the two spill stores, the checked memcpy at 0x81dcc, then 0x81dd0 ========== *)
    assert (Efl : CP.flen cx j = SM.t_len (CC.c_in cx) j) by reflexivity.
    pose proof (A.Prog.Seg.F2.f2_len_range (CC.c_in cx) j) as (Hlen0 & Hbody0 & Hbodyn).
    unfold SM.nlen in Hbodyn.
    assert (Hfl : 0 < CP.flen cx j) by lia.
    assert (Ereq : Reusable.YG00.req_size (CP.flen cx j) = CP.flen cx j)
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (CP.flen cx j) 0); lia).
    rewrite Ereq in HphC, Hdjfr, Hdjin, Happph, Hnimgph, HphAll, Hphapp.
    (* the block against the runtime words (f2_evt_Fs's premise, asan_memcpy_contract_F's own form): the block
       lies off the image (Hnimgph, YCbq.blk_img from AR's client-image law) and [RT_LO, RT_HI) lies in it
       (KitMem.kitmem_in_img: [IMG_LO, IMG_HI) = [0x10000, 0x5fe000)), so they do not meet. *)
    assert (HRTphi : phi + CP.flen cx j <= ART.RT_LO \/ ART.RT_HI <= phi).
    { destruct (Z_le_gt_dec (phi + CP.flen cx j) ART.RT_LO) as [Hlo|Hlo]; [left; exact Hlo|].
      destruct (Z_le_gt_dec ART.RT_HI phi) as [Hhi|Hhi]; [right; exact Hhi|].
      exfalso. apply (Hnimgph (Z.max phi ART.RT_LO)); [lia|].
      apply KM.kitmem_in_img.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, ART.RT_LO, ART.RT_HI in *. lia. }
    destruct Hdjin as [Hz0|(HinI & Hdj & Hp4096 & HpC)]; [lia|].
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) HAR HinI)
      as (_ & _ & _ & Hpapp & _ & _ & _).
    assert (Ereqn : Reusable.YG00.req_size (CC.c_n cx) = CC.c_n cx)
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (CC.c_n cx) 0); lia).
    rewrite Ereqn in Hpapp.
    (* an address of a live block, or up to 7 bytes past its end, is application memory *)
    assert (Happ_end : forall p n x, Reusable.YG0f.in_app p n -> p <= x <= p + n + 7 -> ART.app_mem x).
    { intros p n x Hpa Hx. pose proof Reusable.YCbq.asan_consts as (Hc & _).
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.ASAN_CEIL, ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in *.
      lia. }
    assert (HKm : A.Prog.asan_memcpy_c.ASAN_MEMCPY_K = 2224) by reflexivity.
    (* the copy's source: the turn's frame bytes in the input block *)
    destruct HINb as (HIN1 & HIN2).
    assert (Hsrc : LM.bytes_at A.Img0.rsegs mem3 (CC.c_p cx + SM.t_body (CC.c_in cx) j)
                     (SM.t_phi (CC.c_in cx) j)).
    { pose proof (A.Prog.Seg.F2.f2_ba_sub mem3 (CC.c_p cx) (CC.c_in cx) (Z.to_nat (SM.t_body (CC.c_in cx) j))
                    (Z.to_nat (SM.t_len (CC.c_in cx) j)) HIN2 ltac:(lia)) as HH.
      rewrite Z2Nat.id in HH by lia. exact HH. }
    pose proof (A.Prog.Seg.F2.f2_phi_len (CC.c_in cx) j) as Hsrcl.
    (* the copy's destination: the block's bytes are present and writable *)
    destruct (A.Prog.Seg.F2.f2_rw_ex mem3 phi (Z.to_nat (CP.flen cx j)) ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros x Hx; rewrite Z2Nat.id in Hx by lia;
                      destruct (HphAll x ltac:(lia)) as ((Hh & b & Hb) & _);
                      split; [exact (KM.kitmem_wview_some mem3 (Z_to_bv 64 x) b Hb)
                             | exists b; exact (KM.kitmem_mrd_some mem3 (Z_to_bv 64 x) b Hb)]))
      as (junk & HRWd).
    destruct HHB as (Hp0 & Had).
    assert (Easz : A.ACtlK.a_size (CP.flen cx j) = CP.flen cx j) by (unfold A.ACtlK.a_size; lia).
    rewrite Easz in Had.
    (* mem_inv holds of the normalized memory only (MemNorm route, F3F.v f3_calln_F's shape) *)
    assert (Hro : MN.ro_agree A.Img0.rsegs mem3) by exact Hroag.
    assert (HSTK : LF.stk A.Img0.rsegs mem3 (CC.c_sp cx - 32768) sp).
    { eapply (KM.kitmem_stk_of_journal (SK := A.AE2k.tfib_sink_head));
        [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
    assert (N_RWd : LSP.rw_cells A.Img0.rsegs (MN.normalize A.Img0.rsegs mem3) phi
                      [LC.CB (Z.to_nat (CP.flen cx j)) junk]).
    { apply (MNT.rw_cells_normalize mem3 phi _ Hro); [|exact HRWd].
      intros i Hi. cbn [LC.cells_size LC.csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia.
      destruct (LM.ro_addr A.Img0.rsegs (LM.wa (phi + i))) eqn:E; [|reflexivity]. exfalso.
      apply (Hnimgph (phi + i)); [lia|].
      pose proof (KM.kitmem_ro_img _ E) as Hi'. rewrite LM.wa_unsigned in Hi' by lia. exact Hi'. }
    assert (N_R216 : LSP.rw_cells A.Img0.rsegs (MN.normalize A.Img0.rsegs mem3) (Asp + 216) [LC.CB 8 j1]).
    { apply (MNT.rw_cells_normalize mem3 (Asp + 216) _ Hro); [|exact HR216].
      intros i Hi. cbn [LC.cells_size LC.csize] in Hi.
      apply MNT.ro_addr_above_img. unfold A.Prog.ImgBounds.IMG_HI. lia. }
    assert (N_R232 : LSP.rw_cells A.Img0.rsegs (MN.normalize A.Img0.rsegs mem3) (Asp + 232) [LC.CB 8 j2]).
    { apply (MNT.rw_cells_normalize mem3 (Asp + 232) _ Hro); [|exact HR232].
      intros i Hi. cbn [LC.cells_size LC.csize] in Hi.
      apply MNT.ro_addr_above_img. unfold A.Prog.ImgBounds.IMG_HI. lia. }
    (* the footprint of the copy *)
    assert (Hrng_win : LEF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K)
                         A.Prog.asan_memcpy_c.ASAN_MEMCPY_K).
    { eapply (KM.kitmem_rng_win (SK := A.AE2k.tfib_sink_head)); [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
    assert (Hrng_ph : LEF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) phi (CP.flen cx j)).
    { apply (KM.kitmem_rng_heap B LAWS ly3 S3 W3 mem3 md3 phi (CP.flen cx j) phi (CP.flen cx j) HAR Hinphi);
        [lia | rewrite Ereq; lia]. }
    assert (Hrng_S : LEF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (CC.c_p cx + SM.t_body (CC.c_in cx) j)
                       (CP.flen cx j)).
    { apply (KM.kitmem_rng_heap B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) _ _ HAR HinI);
        [lia | rewrite Ereqn; lia]. }
    assert (Hsh_ph : A.Prog.rng_asan.sh_word_rng (PB.RNG_W (Reusable.YA0n.w_H W3)) phi (CP.flen cx j)).
    { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (CP.flen cx j) phi
                  (CP.flen cx j) HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV];
        [left; exact E0 | right; exact (PB.rng_of_visible _ _ _ HV)]. }
    assert (Hsh_S : A.Prog.rng_asan.sh_word_rng (PB.RNG_W (Reusable.YA0n.w_H W3))
                      (CC.c_p cx + SM.t_body (CC.c_in cx) j) (CP.flen cx j)).
    { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx)
                  (CC.c_p cx + SM.t_body (CC.c_in cx) j) (CP.flen cx j) HAR HinI ltac:(lia)
                  ltac:(rewrite Ereqn; lia) ltac:(lia)) as [E0|HV];
        [left; exact E0 | right; exact (PB.rng_of_visible _ _ _ HV)]. }
    assert (Hsh_win : A.Prog.rng_asan.sh_word_rng (PB.RNG_W (Reusable.YA0n.w_H W3))
                        (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K) A.Prog.asan_memcpy_c.ASAN_MEMCPY_K).
    { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
      destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K)
                  A.Prog.asan_memcpy_c.ASAN_MEMCPY_K HAR ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia)
                  ltac:(lia)) as [E0|HV];
        [left; exact E0 | right; exact (PB.rng_of_visible _ _ _ HV)]. }
    (* the register facts of the copy *)
    assert (E2r : Sem.reg_get regs3 2 = Z_to_bv 64 sp)
      by exact (f2g_rg regs3 2 _ E2 ltac:(vm_compute; reflexivity)).
    assert (E18 : Sem.reg_get regs3 18 = Z_to_bv 64 (CP.flen cx j))
      by exact (f2g_rg regs3 18 _ R18 ltac:(vm_compute; reflexivity)).
    (* route (C): the run's shadow region, the source's and the destination's aligned shadow-word spans, lies in
       the cut's own shadow: both ranges are inside live blocks ((L) disjunct of cut_shadow) *)
    assert (HSWR : A.ShadowRwOn.shadow_rw_on
                     (A.Prog.Seg.F2Fs_on.f2_evt_Fs_shadow_R phi (CC.c_p cx + SM.t_body (CC.c_in cx) j) (CP.flen cx j))
                     mem3).
    { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
      intros a Ha. unfold A.Prog.Seg.F2Fs_on.f2_evt_Fs_shadow_R in Ha. unfold A.ACtlRtC.cut_shadow.
      destruct Ha as [Ha|Ha]; right; left.
      - exists (CC.c_p cx), (CC.c_n cx). split; [exact HinI|].
        exact (f2g_sh_word_blk (CC.c_p cx) (CC.c_p cx + Reusable.YG00.req_size (CC.c_n cx))
                 (CC.c_p cx + SM.t_body (CC.c_in cx) j) (CP.flen cx j) a ltac:(lia) ltac:(rewrite Ereqn; lia) Ha).
      - exists phi, (CP.flen cx j). split; [exact Hinphi|].
        exact (f2g_sh_word_blk phi (phi + Reusable.YG00.req_size (CP.flen cx j)) phi (CP.flen cx j) a
                 ltac:(lia) ltac:(rewrite Ereq; lia) Ha). }
    (* the run on the normalized memory (asan_memcpy_contract_F_on discharged by a Theorem Labs lane's proof) *)
    pose proof (A.Prog.Seg.F2Fs_on.f2_evt_Fs_on (PB.RNG_W (Reusable.YA0n.w_H W3))
        A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
        (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
        (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8)
        (Sem.reg_get regs3 9) (Sem.reg_get regs3 10) (Sem.reg_get regs3 11) (Sem.reg_get regs3 12)
        (Sem.reg_get regs3 13) (Sem.reg_get regs3 14) (Sem.reg_get regs3 15) (Sem.reg_get regs3 16)
        (Sem.reg_get regs3 17) (Sem.reg_get regs3 18) (Sem.reg_get regs3 19) (Sem.reg_get regs3 20)
        (Sem.reg_get regs3 21) (Sem.reg_get regs3 22) (Sem.reg_get regs3 23) (Sem.reg_get regs3 24)
        (Sem.reg_get regs3 25) (Sem.reg_get regs3 26) (Sem.reg_get regs3 27) (Sem.reg_get regs3 28)
        (Sem.reg_get regs3 29) (Sem.reg_get regs3 30) (Sem.reg_get regs3 31)
        CK.fp_regs CK.fp_csr (MN.normalize A.Img0.rsegs mem3)
        sp Asp phi (CC.c_p cx + SM.t_body (CC.c_in cx) j) (CP.flen cx j) (CC.c_sp cx - 32768)
        (SM.t_phi (CC.c_in cx) j) junk j1 j2
        E2r E9 E10 E18 E20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HRTphi
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold ART.HIGHMEM_BEG; lia) ltac:(lia) ltac:(lia)
        ltac:(unfold ART.APPMEM_END; lia) ltac:(unfold ART.APPMEM_END; lia) Hsp16
        (MN.bytes_at_normalize A.Img0.rsegs mem3 _ _ Hro Hsrc) Hsrcl N_RWd N_R216 N_R232
        (MNT.addressable_normalize mem3 _ _ Hro
           (A.Prog.Seg.F2.f2_addr_sub mem3 (CC.c_p cx) (CC.c_n cx) (CC.c_p cx + SM.t_body (CC.c_in cx) j)
              (CP.flen cx j) HIN1 ltac:(lia) ltac:(lia) ltac:(lia)))
        (MNT.addressable_normalize mem3 phi (CP.flen cx j) Hro Had)
        (or_intror (Happ_end (CC.c_p cx) (CC.c_n cx)
                      (CC.c_p cx + SM.t_body (CC.c_in cx) j + CP.flen cx j) Hpapp ltac:(lia)))
        (or_intror (Happ_end phi (CP.flen cx j) (phi + CP.flen cx j) Hphapp ltac:(lia)))
        (Happ_end (CC.c_p cx) (CC.c_n cx) (CC.c_p cx + SM.t_body (CC.c_in cx) j + 7) Hpapp ltac:(lia))
        (Happ_end phi (CP.flen cx j) (phi + 7) Hphapp ltac:(lia))
        (MNT.stk_normalize_ro mem3 (CC.c_sp cx - 32768) sp Hro ltac:(unfold A.Prog.ImgBounds.IMG_HI; lia) HSTK)
        (MNT.asan_cells_normalize mem3 Hro Hcells)
        (A.ShadowRwOnT.shadow_rw_on_normalize _ mem3 Hro HSWR)
        (MN.mem_inv_normalize A.Img0.rsegs mem3)
        Hrng216 Hrng232 (PB.rng_bytes_RNG_W _) (PB.rng_of_visible _ _ _ (PB.img_vis_W W3))
        Hrng_win Hrng_ph Hrng_S Hsh_ph Hsh_S Hsh_win) as HRUNn.
    (* the run moved to the real memory (ProgWorld.rebase_ro_normalize = MemNormF.evtF_normalize_ro + the
       MemNorm transports) *)
    pose proof (PW.rebase_ro_normalize _ _ _ _ _ _ _ mem3 _ Hro HRUNn) as HRUN.
    apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
             HRUN HFPA).
    intros ms' md' Hrun HP Hsbm.
    destruct HP as (s0 & HQ & Hrel & HRO' & _ & _ & Hbiff & _ & Hmunch & Hwmono & _).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    Es0 & MU0 & WM0 & ST0 & RW0 & HB0 & AC0 & SW0 & Q2160 & Q2320).
    subst s0.
    destruct (MNT.ms_rel_MS ms' _ _ _ _ _ _ _ Hrel) as (Ems & Hrel').
    remember (ms_mem ms') as m' eqn:Em'.
    pose proof (Hmunch _ MU0) as MU.
    pose proof (Hwmono WM0) as WM.
    pose proof (MNT.rw_cells_of_rel m' m0' phi _ Hrel' RW0) as RW'.
    pose proof (proj2 (Hbiff _ _) Q2160) as Q216.
    pose proof (proj2 (Hbiff _ _) Q2320) as Q232.
    destruct (PW.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) (PB.RNG_W (Reusable.YA0n.w_H W3)) _ ms'
                Hrun HFPA) as (Hgrow0 & Hhid).
    assert (Hgrow : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows mem3 m')
      by (rewrite Em'; exact Hgrow0).
    (* the write set: the two spill words, the block, the callee's stack window *)
    assert (HIN4 : forall x, ~ LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240);
                                           (phi, phi + CP.flen cx j);
                                           (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x ->
              Asp + 216 <= x < Asp + 224 \/ Asp + 232 <= x < Asp + 240 \/ phi <= x < phi + CP.flen cx j \/
              sp - 2224 <= x < sp).
    { intros x Hx. destruct (KM.kitmem_not_outside _ x Hx) as (lo & hi & Hin & Hr).
      cbn [In] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia. }
    assert (HOUT4 : forall x, ~ (Asp + 216 <= x < Asp + 224) -> ~ (Asp + 232 <= x < Asp + 240) ->
              ~ (phi <= x < phi + CP.flen cx j) -> ~ (sp - 2224 <= x < sp) ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                          (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x).
    { intros x H1 H2 H3 H4. cbn [LF.outside]. rewrite HKm.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact I]. }
    assert (KSH : forall x, ART.in_shadow x ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                          (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x).
    { intros x Hx.
      destruct (KM.kitmem_outside_dec [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                                       (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x) as [Ho|Ho];
        [exact Ho|]. exfalso.
      pose proof (A.AsanRTFacts.app_not_shadow x) as Hns.
      destruct (HIN4 x Ho) as [H|[H|[H|H]]].
      - exact (Hns (Happsp x ltac:(lia)) Hx).
      - exact (Hns (Happsp x ltac:(lia)) Hx).
      - exact (Hns (Happph x ltac:(lia)) Hx).
      - exact (Hns ltac:(unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END; right; lia) Hx). }
    (* the journal across the run *)
    assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                    (CC.c_sp cx) [] (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (CC.c_mem cx) (CC.c_md cx)
                    (CC.own6 cx) ly3 S3 W3 m' md' k).
    { rewrite Em'.
      eapply (PW.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx).
      2:{ exact Hrun. }
      { exact HJ. }
      { exact HFPA. }
      { rewrite <- Em'. exact MU. }
      { exact Hsbm. }
      { intros a Ha Ho. destruct (HIN4 a Ho) as [H|[H|[H|H]]].
        - apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia.
        - apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia.
        - right; right; left. exists phi, (CP.flen cx j). split; [exact Hinphi|].
          split; [exact Hnew | rewrite Ereq; lia].
        - apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia. } }
    (* the carried runtime facts: ctl_rt_C at the exit journal's AR (route (C)) *)
    pose proof (f2g_rtC cx ly3 S3 W3 m' md' (CC.own6 cx) k HB HJ') as Hrt'.
    (* the exit cut at 0x81dd0 *)
    rewrite Ems.
    refine (HX cx [Z.of_nat j] fr k ly3 S3 W3 _ m' md' HB HJ' HF HL Hk _ Hrt').
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81dd0_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    assert (HFRAC' : CP.FRAC B cx fr fr regs3 m').
    { apply (KM.kitmem_frac_keep B cx fr fr regs3 mem3 m' _ HFRAC MU Hgrow ltac:(lia)).
      - intros A0 HA0 x Hx. pose proof (f2g_rgv_mod regs3 9 A0 Asp HA0 R9) as Emod.
        apply HOUT4; revert Emod; Z.div_mod_to_equations; lia.
      - intros x Hx. apply HOUT4; lia.
      - intros x Hx. apply HOUT4; lia. }
    assert (KA : forall x, Asp + 32 <= x < Asp + 216 \/ Asp + 240 <= x < Asp + 304 ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                          (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x)
      by (intros x Hx; apply HOUT4; lia).
    assert (KF : forall x, fr <= x < fr + 4096 ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                          (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x)
      by (intros x Hx; apply HOUT4; lia).
    assert (KI : forall x, CC.c_p cx <= x < CC.c_p cx + CC.c_n cx ->
              LF.outside [(Asp + 216, Asp + 224); (Asp + 232, Asp + 240); (phi, phi + CP.flen cx j);
                          (sp - A.Prog.asan_memcpy_c.ASAN_MEMCPY_K, sp)] x)
      by (intros x Hx; apply HOUT4; lia).
    assert (HFLSH' : CP.FLSH cx j fr regs3 m')
      by exact (f2g_FLSH_munch cx j fr regs3 mem3 m' Asp _ HFLSH MU R9 ltac:(lia) ltac:(lia) ltac:(lia)
                  KSH KA KF KI).
    assert (HIFS' : CP.IFS cx fr j regs3 m')
      by exact (f2g_IFS_munch cx fr j regs3 mem3 m' Asp _ HIFS MU R9 ltac:(lia) ltac:(lia) KSH KA KF).
    assert (HFLC' : CP.FLC fr regs3 m')
      by exact (f2g_FLC_munch fr regs3 mem3 m' Asp _ HFLC MU R9 ltac:(lia) ltac:(lia) KSH KA).
    assert (HLK' : CP.LK cx fr j regs3 m') by exact (f2g_LK_munch cx fr j regs3 mem3 m' _ HLK MU KF).
    assert (HINb' : CP.f1_IN cx m').
    { split; [exact (KM.kitmem_addr_munch _ mem3 m' (CC.c_p cx) (CC.c_n cx) HIN1 MU KSH)|].
      apply (KM.kitmem_bytes_munch _ mem3 m' (CC.c_p cx) (CC.c_in cx) HIN2 MU).
      intros x Hx. apply KI. lia. }
    assert (S248' : CP.spill regs3 m' 248 (fr + 176))
      by exact (KM.kitmem_spill_munch _ regs3 regs3 mem3 m' 248 _ Asp H248 R9 ltac:(lia) ltac:(lia)
                  ltac:(lia) MU eq_refl ltac:(intros x Hx; apply KA; lia)).
    assert (S224' : CP.spill regs3 m' 224 (SM.t_left (CC.c_in cx) j - SM.t_h (CC.c_in cx) j))
      by exact (KM.kitmem_spill_munch _ regs3 regs3 mem3 m' 224 _ Asp S224 R9 ltac:(lia) ltac:(lia)
                  ltac:(lia) MU eq_refl ltac:(intros x Hx; apply HOUT4; lia)).
    assert (S216' : CP.spill regs3 m' 216 (CC.c_p cx + SM.t_body (CC.c_in cx) j))
      by (exists Asp; split; [exact R9 | exact Q216]).
    assert (HREC : LM.bytes_at A.Img0.rsegs m' phi (SM.t_phi (CC.c_in cx) j))
      by exact (A.Prog.Seg.F2.f2_c_bytes _ _ _ RW').
    assert (Hb2z : (if SM.t_big (CC.c_in cx) j then 0 else 1) = SM.b2z (CP.flen cx j <? 50)).
    { unfold SM.t_big, SM.b2z. rewrite <- Efl.
      destruct (Z.leb_spec 50 (CP.flen cx j)); destruct (Z.ltb_spec (CP.flen cx j) 50);
        first [reflexivity | lia]. }
    assert (HKF : A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
    assert (HPH : CP.b5_PH cx j phi fr regs3 m').
    { split.
      - intros Hl. unfold SM.t_g. rewrite A.Prog.Seg.F2.f2_fr50 by (rewrite Hsrcl; lia).
        exact (A.Prog.Seg.F2.f2_ba_firstn m' phi _ 50 HREC).
      - intros Hl. split.
        + unfold CP.FRAME_BYTES. destruct Hdjfr as [H|H]; [left; lia | right; lia].
        + left. rewrite Hspz, HKF. lia. }
    split; [exact HFRAC'|].
    exists phi.
    split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
    split.
    { split; [exact Hp0|]. rewrite Easz.
      exact (KM.kitmem_addr_munch _ mem3 m' phi (CP.flen cx j) Had MU KSH). }
    split.
    { split; [exact HFLSH'|]. split; [exact S216'|]. split; [exact S224'|].
      split; [exact S248'|]. split; [exact HINb' | exact HFLC']. }
    split; [exact HLK'|].
    split.
    { (* b5_C *)
      split; [reflexivity|].
      split; [reflexivity|].
      split.
      { exists Asp. split; [exact R9|]. split; [lia|]. split.
        - destruct HFLSH' as ((_ & _ & _ & _ & _ & _ & _ & P248 & _ & _ & _ & P184 & P256 & P264 & P272 & _)
                              & _ & _ & P144 & _).
          destruct HFLC' as (_ & _ & P192 & P80 & P88 & P96 & _ & _).
          split; [exact (f2g_spill_q regs3 m' Asp 248 _ P248 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 256 _ P256 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 144 _ P144 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 184 _ P184 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 192 _ P192 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 80 _ P80 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 88 _ P88 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 96 _ P96 R9 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (f2g_spill_q regs3 m' Asp 272 _ P272 R9 ltac:(lia) ltac:(lia) ltac:(lia))
                 | exact (f2g_spill_q regs3 m' Asp 264 _ P264 R9 ltac:(lia) ltac:(lia) ltac:(lia))].
        - rewrite Hb2z. exact Q232. }
      split; [exact HPH|].
      split.
      { destruct HFLC' as (_ & _ & _ & _ & _ & _ & _ & _ & HA72 & HA38 & _).
        destruct HIFS' as (_ & (HFG & _) & _).
        split; [exact HA72|]. split; [exact HA38|].
        split; [exact HFG | exact (proj2 (A.Prog.Seg.F1.f1_FS_len (CC.c_in cx) j))]. }
      split; [exact (f2g_kn cx ly3 S3 W3 m' md' (CC.own6 cx) k HB HJ')|].
      destruct HIFS' as (_ & HFGj & HFSj). split; [exact HFGj | exact HFSj]. }
    (* P: the len > 0 arm's own four conjuncts *)
    split.
    { split; [exact S224'|]. split; reflexivity. }
    split.
    { intros Hl. unfold CC.rgv.
      transitivity (Z_to_bv 64 (SM.b2z (CP.flen cx j <? 50))); [reflexivity|].
      rewrite (proj2 (Z.ltb_ge _ _) Hl). reflexivity. }
    split; [intros _; exact HREC|].
    exact (proj1 HIFS').
Qed.

End GlueF2.

Print Assumptions glue_seg_F2.
