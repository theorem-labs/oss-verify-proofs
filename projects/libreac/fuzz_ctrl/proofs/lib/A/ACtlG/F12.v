(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* lib/A/ACtlG/F12.v -- GLUE for stage seg_F12 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:778-779) (an earlier version, blob a3c6b7b3501, not in this delivery)).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F12 : forall POST (j : nat),
       CF POST (ix_cut C_A82138_at [Z.of_nat j]) -> CF POST (ix_cut C_A820fc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A820f8_at [Z.of_nat j])
   with ACtl.v's own notation block (CF with SK := A.AE2k.tfib_sink_head and FP := [], ix_cut := ACtlCut.ix_cut,
   C_x := ACtlCutP.C_x B), i.e. exactly ACtl.v's Section hypothesis seg_F12.  Segment F12 is the block
   0x820f8 -> 0x82138 (Seg/F12.v:1-26): 0x820f8 `bltz a0` (not taken), 0x820fc `sd s9,152(s1)`, nine `sb zero` stores
   to the frame's metadata bytes S(fr)+42 .. S(fr)+50, two spill loads and `jal __asan_memcpy` at 0x82134.

   PROVENANCE
   - Brief: <lane notes> glueF12-brief.md (a working note, not in this delivery) (a Theorem Labs lane, 2026-10-29).  Pattern:
     glue-pattern.md sections 1-8 (a working note, not in this delivery).  Template: a Theorem Labs lane's glue_seg_F26 (lib/A/ACtlG/F26.v at 3a0d3ca9bdf).
   - The runs lifted: this lane's lib/A/Prog/Seg/F12F.v (record a working branch 90a63b68e4f, blob
     9c88764ecd4, taken by path): F12F.f12_run_F_on (route (C): the run 0x820fc -> 0x82138, Seg/F12.v:1093-1242, under a
     footprint, premise shadow_rw_on (F12F.f12_run_shadow_R fr), post forall P) and F12F.f12_entry2_F (0x820f8 ->
     0x820fc, register only).  f12_run_F_on's callee premise asan_memcpy_contract_F_on is discharged by a Theorem Labs lane's
     proved closed theorem A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on (a working branch 83ab88c3325,
     asan_memcpy_cF_on.v 95a5333de98 / asan_memcpyF_on.v 7fa6770491b, by path).
   - The order of the steps follows ctrl's own proof of the same segment, Seg/F12.v f12_run (:933-1627, its exit cut
     rebuilt at :1223-1626) and f12_entry2 (:1645-1692).
   - COPIED (allowed by the brief): from a Theorem Labs lane's F26.v (written on a working branch 3a0d3ca9bdf), b7g_frame_app (at head lib/A/ACtlG/F26.v:474-489) as
     g12_frame_app, statement and proof unchanged except the module spelling; the spill transport g12_sp is
     b7g_spill_keep (at head lib/A/ACtlG/F26.v:388-410) with the write set's kept range given as a premise instead of disjoint_from.  From
     lib/A/Prog/Seg/F24.v on this base, b7_segs_below / b7_seg_lt / b7_find_none as g12_segs_below / g12_seg_lt /
     g12_find_none (top IMG_HI = 6283264 instead of AC.GT, the same number), because F24.v is not otherwise in this
     closure.  The earlier copy of F26's b7g_frame_GT (g12_frame_GT) is deleted: the frame bound is now a citation
     of the base's A.ProgWorld.ctl_frame_above_img_stmt through its proof A.ProgWorld_Fs.ctl_frame_above_img
     (premise-free since fec8db0a380, ProgWorld.v (at head lib/A/ProgWorld.v:1248-1252) (an earlier version, blob ab716e7a0e0, not in this delivery)), at cid := 6 (ACtlCut.own6 cx =
     [(6, c_fpos cx)], ACtlCut.v (at head lib/A/ACtlCut.v:188)).

   THE PROOF, step by step (glue-pattern.md section 3, G1-G5)
   g12_at_fc, the shared lemma (the plan's "state AT 0x820fc"): from FRAC + the b5_body conjuncts both entry cuts
       share (b5_K, b5_RC, IDb1, b5_F17, b5_W240, b5_PF: Seg/F12.v's f12_P) and the cut shell at 0x820fc, the walk
       reaches CF POST (ix_cut C_A82138_at [j]).
     G2  geometry from the journal: frames_bounds on the owned frame (6, c_fpos cx) and the frame law (fr + 4096 <=
         alloc_ceiling), astk_ok (alloc_ceiling <= ly_stk_lo <= c_sp cx - 32768), FRAC (c_sp cx - 4096 < sp <= A,
         fr + 3136 <= A, A + 416 <= c_sp cx); so frame < stack window < spill area.  IMG_HI = 0x5fe000 <= fr by
         A.ProgWorld_Fs.ctl_frame_above_img (the statement A.ProgWorld.ctl_frame_above_img_stmt) at cid := 6.
         The run's premises: registers 2 9 19 25 from FRAC and b5_K; memory from b5_C (spills, the fragment record),
         the frame's stk (FLSH) for the 72 destination bytes, the journal's present stack window
         [c_sp cx - 32768, c_sp cx) for wr_at (A+152) and stk lo sp with lo := c_sp cx - LLVMF_STK; the cut's
         ctl_rt_C (route (C), a working branch) for ro_agree / asan_cells and, by shadow_rw_on_mono, the run's region R (the
         nine stored metadata bytes and memcpy's region) inside cut_shadow's (F) region of the owned class-6 frame
         [S(fr), S(fr) + 512) (HRreg).  Footprint premises at RNG := ProgBridge.RNG_W (w_H W3):
         ProgWorldVisWin.win_vis (spill words, callee window), win_sh_vis (its shadow words),
         ProgWorldVisFrame.frame_vis (frame bytes and their shadow word spans; the nine metadata bytes are a
         sub-range of the destination's span), ProgBridge.img_vis_W (image), rng_bytes_RNG_W.
     G3  ProgBridge.cfg_at_MS and Reusable.YA0nR.SRr_xregs_eqv move the walk to the run's mkR_of map.
     G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid at RNG_W (w_H W3).
     G5  the end map R is the exit cut's map.  The journal crosses the write set f12_W A fr sp by
         Reusable.YCbq.ajournal_exec at Wr := g12_Wr (spill word and callee window: awr_byte's stack case; the 72
         frame bytes and their nine metadata bytes: its in_frames case, own6).  Every carried fact moves by one
         disjointness step (g12_out and the O* facts); the frame's 392 shadow bytes are read fresh after the run from
         the run's forall-P post at P := cut_shadow (they are in its (F) region); addressable moves for EVERY range, because a written metadata byte is
         the metadata of [fr+336, fr+408), addressable after the run (the run's post).  FRAC is rebuilt by
         Kit.kit_frac_move (registers) and g12_frac_mem (memory; it walks FRAC's conjuncts generically).  FRAC's
         last conjunct, the fake-frame trailer word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))
         (ACtlCutP.v:997), is proved like every other q64 conjunct: g12_q64 moves it across the run's write set,
         because [fr + 4088, fr + 4096) is inside the owned frame and outside [fr + 336, fr + 408), the only frame
         bytes the run writes (premise Ofrw); kit_frac_move keeps it because it reads memory only.  The exit's
         ctl_rt_C keeps the regions (the state ly3 S3 is the entry's): asan_cells / ro_agree from the run's post, both
         shadow parts by the run's forall-P post at cut_shadow / img_shadow (L3 recipe 2(d)).  The five runtime cells
         of the exit (REAL_BCMP, REAL_MEMCMP, GOT_CF, CF+254, CF+255) come from A.ProgWorldRtC.rt_of_core_C at the
         exit state (FP := []), then F12.f12_got_cf / f12_cf_254 / f12_cf_255.
   glue_seg_F12, first conjunct (C_A820fc_at): G1, drop `ir = false`, the shared lemma (F12.v's f12_entry1).
   glue_seg_F12, second conjunct (C_A820f8_at): G1, G3, f12_entry2_F lifted by SRr_fevt at Kit.kit_RNG0
       (register only), the journal by ajournal_exec with the empty write set (A5.v), FRAC by Kit.kit_frac_move,
       the body by g12_body_regs (registers 2 9 18 20-25 kept), then the shared lemma at the run's end map.

   SECTION HYPOTHESES (exact text below; nothing else is assumed)
   - LAWS : Reusable.YG0d.AR_laws segs B -- ACtl.v's text; frames_bounds, al_blocks, sep_block_frame,
     frame_vis, win_sh_vis, ajournal_exec and rt_of_core_C take it.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- ACtl.v's text; rt_of_core_C's first premise.
   No VIS0 / OWNED_RO (none was ever needed here).
   CITED, NOT ASSUMED: a Theorem Labs lane's A.ProgWorldRtC.rt_of_core_C (the route (C) form of rt_of_core) at FP := [], its
   premises CtrlTSyms B (TFIB_SYMS), AR_laws (LAWS), and the cut's ctl_base / ajournal / ctl_rt_C at the exit state;
   a Theorem Labs lane's asan_memcpy_holds_F_on; a Theorem Labs lane's A.ProgWorld_Fs.ctl_frame_above_img (ProgWorld_Fs.v:498, the
   proof of A.ProgWorld.ctl_frame_above_img_stmt); the kit (A.ACtlG.Kit.kit_wx, kit_segs_low, kit_frac_move,
   kit_RNG0); a Theorem Labs lane's Reusable.YA0nR.SRr_fevt / SRr_fevt_hid / SRr_xregs_eqv; A.ProgBridge;
   A.ProgWorldVisWin / VisFrame; the core's YCbq lemmas; the closed helpers of Seg/F12.v (f12_*, outside its
   Section S).

   CLOSURE: every project Require is qualified (no Import / Export of a project module).  SIX-MODULE SPELLING: the
   copies of YK11 / YK1b / YM05 / YO09 are named only through the alias modules K11c / K11u / K1bc / M05c (full
   paths) or by full path; YI04 / YI16 / YP09 are not named.  No statement names a frame-route identifier.

   BUILD STATE: see the commit message (a working branch 1502cba0417).  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YK04 YG00 YG01 YG0f YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k AF0m Img0 AsanRT AsanRTFacts ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld ProgWorld_Fs ProgWorldVisWin ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan SlotModel asan_memcpy_c sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c_on asan_memcpy_cF_on asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F12 F12F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Step Cells ExecF MState Regs6ss RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* Module aliases, each to a FULL path (the six-module rule for K11c / K11u / K1bc / M05c; the others only to keep
   short names unambiguous next to the _F file's closure). *)
Module K11c := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module K11u := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module K1bc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module M05c := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RPA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module F12S := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F12.
Module F12FS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F12F.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. Closed helpers. *)

(* COPIED from a Theorem Labs lane's F26.v (at head lib/A/ACtlG/F26.v:474-489; written on a working branch 3a0d3ca9bdf) (b7g_frame_app): a byte of an owned frame is app memory. *)
Lemma g12_frame_app : forall {fx : K11c.FPState} {rc : M05c.RunCeil}
    (B : Reusable.YG0f.asyms) ly S (W : Reusable.YA0n.world segs) mem md cid pos a,
  Reusable.YG0d.AR_laws segs B -> Reusable.YG0n.AR segs B ly S W mem md ->
  In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly cid pos <= a <
    Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid ->
  ART.app_mem a.
Proof.
  intros fx rc B ly S W mem md cid pos a LAWS HAR Hin Ha.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _).
  pose proof (@M05c.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
  destruct Happ as (H4096 & [HL | (HH1 & HH2)]); [left | right]; lia.
Qed.

(* COPIED from lib/A/Prog/Seg/F24.v on this base (b7_tops_below / b7_segs_below / b7_seg_lt / b7_find_none), with
   the top IMG_HI = 0x5fe000 = 6283264 (AC.GT there, the same number): no image segment reaches IMG_HI. *)
Definition g12_tops_below (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma g12_segs_below : g12_tops_below A.Img0.rsegs 6283264 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g12_seg_lt : forall x s, find_segment A.Img0.rsegs x 1 = Some s -> x < 6283264.
Proof.
  intros x s H. pose proof g12_segs_below as HB. unfold g12_tops_below in HB.
  revert H HB. generalize A.Img0.rsegs as sg. intros sg. revert x s.
  induction sg as [|s0 r IH]; intros x s H HB; cbn [find_segment] in H; [discriminate H|].
  cbn [forallb] in HB. apply andb_prop in HB as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH x s H Hr).
Qed.

Lemma g12_find_none : forall x, 6283264 <= x -> find_segment A.Img0.rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment A.Img0.rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (g12_seg_lt x s E). lia.
Qed.

(* A present byte is writable (the write view of a present byte is the byte). *)
Lemma g12_wv_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> wview A.Img0.rsegs m x <> None.
Proof. intros m x b E. unfold wview. rewrite E. discriminate. Qed.

(* A byte present at or above the image stays present across a run that keeps writability (F26's b7g_grow, through
   g12_find_none). *)
Lemma g12_grow : forall (m m' : word -> option byte) (x : word),
  6283264 <= bv_unsigned x -> LFr.wmono A.Img0.rsegs m m' -> m x <> None -> m' x <> None.
Proof.
  intros m m' x Hgt WM Hx.
  assert (Hw : wview A.Img0.rsegs m x <> None).
  { destruct (m x) as [b |] eqn:E; [exact (g12_wv_some m x b E) | exfalso; exact (Hx eq_refl)]. }
  pose proof (WM x Hw) as Hw'.
  destruct (m' x) as [b' |] eqn:E'; [discriminate |].
  exfalso. apply Hw'. unfold wview. rewrite E'. rewrite (g12_find_none (bv_unsigned x) Hgt). reflexivity.
Qed.

(* The write set of the run (F12.f12_W) as a predicate, for ajournal_exec's Wr. *)
Definition g12_Wr (A fr sp a : Z) : Prop :=
  (A + 152 <= a < A + 160) \/ (ART.shadow_addr fr + 42 <= a < ART.shadow_addr fr + 51) \/
  (fr + 336 <= a < fr + 408) \/ (sp - 2224 <= a < sp).

(* A byte outside the four intervals of f12_W. *)
Lemma g12_out : forall A fr sp x,
  (x < A + 152 \/ A + 160 <= x) -> ~ (ART.shadow_addr fr + 42 <= x < ART.shadow_addr fr + 51) ->
  (x < fr + 336 \/ fr + 408 <= x) -> (x < sp - 2224 \/ sp <= x) ->
  LFr.outside (F12S.f12_W A fr sp) x.
Proof.
  intros A fr sp x H1 H2 H3 H4. unfold F12S.f12_W. cbn [LFr.outside].
  split; [lia |]. split; [exact H2 |]. split; [lia |]. split; [lia | exact I].
Qed.

Lemma g12_W_cases : forall A fr sp x, LFr.outside (F12S.f12_W A fr sp) x \/ g12_Wr A fr sp x.
Proof.
  intros A fr sp x. unfold g12_Wr.
  assert (D : (A + 152 <= x < A + 160) \/ (ART.shadow_addr fr + 42 <= x < ART.shadow_addr fr + 51) \/
              (fr + 336 <= x < fr + 408) \/ (sp - 2224 <= x < sp) \/
              ((x < A + 152 \/ A + 160 <= x) /\ ~ (ART.shadow_addr fr + 42 <= x < ART.shadow_addr fr + 51) /\
               (x < fr + 336 \/ fr + 408 <= x) /\ (x < sp - 2224 \/ sp <= x))) by lia.
  destruct D as [D | [D | [D | [D | (D1 & D2 & D3 & D4)]]]].
  - right. left. exact D.
  - right. right. left. exact D.
  - right. right. right. left. exact D.
  - right. right. right. right. exact D.
  - left. exact (g12_out A fr sp x D1 D2 D3 D4).
Qed.

(* bytes_at across a run, for a range every byte of which is outside the write set. *)
Lemma g12_by : forall (W : list LFr.ivl) (m m' : word -> option byte) (a : Z) (bs : list byte),
  LMem.bytes_at segs m a bs -> LFr.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> LFr.outside W x) -> LMem.bytes_at segs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) MU HW. split; [exact Ha |]. split; [exact Hl |].
  intros i Hi. unfold LMem.mrd. rewrite MU; [apply H; exact Hi |].
  rewrite LMem.wa_unsigned by lia. apply HW. lia.
Qed.

(* The frame's metadata range: shadow bounds of an app-memory frame (low or high band). *)
Lemma g12_sh_bounds : forall fr, 4096 <= fr ->
  (fr + 4096 <= 0x7fff7000 \/ (0x10007fff8000 <= fr /\ fr + 4096 <= 0x7fffff800000)) ->
  0x7fff8000 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 392 <= 0x10007fff8000.
Proof. intros fr H1 H2. unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* The nine metadata bytes of [fr + 336, fr + 408) lie in that range's 8-aligned shadow word span. *)
Lemma g12_sh42 : forall fr, fr mod 8 = 0 -> 0 <= fr ->
  A.Prog.rng_asan.sh_al8_lo (fr + 336) <= ART.shadow_addr fr + 42 /\
  ART.shadow_addr fr + 42 + 9 <= A.Prog.rng_asan.sh_al8_lo (fr + 336) +
    (A.Prog.rng_asan.sh_al8_hi (fr + 336) 72 - A.Prog.rng_asan.sh_al8_lo (fr + 336)).
Proof.
  intros fr H8 H0. unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, ART.shadow_addr, ART.ASAN_K.
  Z.div_mod_to_equations. lia.
Qed.

(* The 64-byte hull premises of ProgWorldVisFrame.frame_vis for a sub-range of a 4096-byte frame. *)
Lemma g12_hull : forall fr off n, fr mod 32 = 0 -> 0 <= fr -> 63 <= off -> 0 < n -> off + n + 64 <= 4096 ->
  fr <= 64 * ((fr + off) / 64) /\ 64 * ((fr + off + n - 1) / 64) + 64 <= fr + 4096.
Proof. intros fr off n H32 H0 Ho Hn Hon. split; Z.div_mod_to_equations; lia. Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The stage. *)

Section GlueF12.

(* ACtl.v's Section shape (ACtl.v a3c6b7b3501:183-187), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v a3c6b7b3501:257, :261-262, :323-325), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A820f8_at := (ACtlCutP.C_A820f8_at B).
Local Notation C_A820fc_at := (ACtlCutP.C_A820fc_at B).
Local Notation C_A82138_at := (ACtlCutP.C_A82138_at B).

(* The core's AR law record, ACtl.v:210's text. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The core's symbol facts for B, ACtl.v:225's text: rt_of_core's first premise. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---- register and memory transports of the cut bundles ---- *)

Lemma g12_rgv : forall (R regs : bvmap 5 word) (r : bv 5) (v : Z),
  K11c.getr R r = K11c.getr regs r -> ACtlCut.rgv regs r v -> ACtlCut.rgv R r v.
Proof. intros R regs r v E H. unfold ACtlCut.rgv in *. rewrite E. exact H. Qed.

Lemma g12_q64 : forall (W : list LFr.ivl) (m m' : word -> option byte) (a v : Z), LFr.munch W m m' ->
  (forall x, a <= x < a + 8 -> LFr.outside W x) -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros W m m' a v MU HW H. unfold ACtlCutP.q64 in *. apply (g12_by W m m' a _ H MU).
  rewrite LMem.length_le8. exact HW.
Qed.

(* A spill survives a run that keeps s1 and misses the spill word (F26.v:376-398 b7g_spill_keep, kept range as a
   premise). *)
Lemma g12_sp : forall (W : list LFr.ivl) (m m' : word -> option byte) (regs regs' : bvmap 5 word) (Aa off v : Z),
  K11c.getr regs 9 = Z_to_bv 64 Aa -> 0 <= Aa -> Aa + 416 <= 2 ^ 64 ->
  0 <= off -> off + 8 <= 416 ->
  K11c.getr regs' 9 = K11c.getr regs 9 -> LFr.munch W m m' ->
  (forall x, Aa + off <= x < Aa + off + 8 -> LFr.outside W x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros W m m' regs regs' Aa off v H9 HA0 HA Ho0 Ho E9 MU HW (A1 & H9' & Hq).
  unfold ACtlCut.rgv in H9'. unfold ACtlCutP.q64 in Hq.
  assert (EA : A1 = Aa).
  { pose proof Hq as (Hb0 & Hb1 & _). rewrite LMem.length_le8 in Hb1.
    assert (Ebv : Z_to_bv 64 Aa = Z_to_bv 64 A1)
      by (etransitivity; [symmetry; exact H9 | exact H9']).
    apply (f_equal (@bv_unsigned 64)) in Ebv.
    rewrite !LMS.unsigned_lit_wrap in Ebv.
    change (Z.of_nat 8) with 8 in Hb1. Z.div_mod_to_equations. lia. }
  subst A1. exists Aa. split; [unfold ACtlCut.rgv; etransitivity; [exact E9 | exact H9] |].
  unfold ACtlCutP.q64. apply (g12_by W m m' (Aa + off) _ Hq MU).
  rewrite LMem.length_le8. intros x Hx. apply HW. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

(* FRAC across a write set that misses the spill words [A+16, A+32) and [A+304, A+312), the owned frame minus
   [fr+336, fr+408) and the saved registers [c_sp cx - 104, c_sp cx), with the frame's shadow list given at the new
   memory (read fresh from shadow_rw).  It walks FRAC's conjuncts generically: the register / numeric ones are
   unchanged, each q64 word and each byte list moves by the same disjointness step.  FRAC's last conjunct, Batch3's
   fake-frame trailer word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) (ACtlCutP.v:997), is such a q64
   word: [fr + 4088, fr + 4096) is inside the frame and outside [fr+336, fr+408), so the premise on the frame moves it. *)
Lemma g12_frac_mem : forall (cx : ACtlCut.ctlcx) (fr sel : Z) (regs : bvmap 5 word) (m m' : word -> option byte)
    (W : list LFr.ivl) (Aa : Z),
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 Aa -> 0 <= Aa -> Aa < 2 ^ 64 -> LFr.munch W m m' ->
  (forall x, Aa + 16 <= x < Aa + 32 -> LFr.outside W x) ->
  (forall x, Aa + 304 <= x < Aa + 312 -> LFr.outside W x) ->
  (forall x, fr <= x < fr + 4096 -> (x < fr + 336 \/ fr + 408 <= x) -> LFr.outside W x) ->
  (forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> LFr.outside W x) ->
  (exists sh, LMem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' W Aa HF H9 HAa0 HAa1 MU O16 O304 Ofrw Osv Hsh.
  assert (Hsvl : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !LMem.length_le8. reflexivity. }
  destruct HF as (A0 & sp & HF). exists A0, sp.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (HA0 : 0 <= A0 < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 (K11c.getr regs 2)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr.
    assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    unfold Reusable.YG0d.spZ, ART.APPMEM_END in *. lia. }
  assert (EA : A0 = Aa).
  { match goal with H : ACtlCut.rgv regs 9 A0 |- _ => exact (F12S.f12_A_eq regs Aa A0 H9 (conj HAa0 HAa1) H HA0) end. }
  subst A0.
  repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
       | |- ACtlCutP.q64 m' ?a ?v =>
           apply (g12_q64 W m m' a v MU);
             [ intros x Hx; first [ apply O16; lia | apply O304; lia | apply Ofrw; lia | apply Osv; lia ]
             | assumption ]
       | |- LMem.bytes_at _ m' ?a ?bs =>
           eapply (g12_by W m m'); [ eassumption | exact MU | ];
           intros x Hx; rewrite ?Hsvl in Hx; try change (Z.of_nat 104) with 104 in Hx;
           first [ apply O16; lia | apply O304; lia | apply Ofrw; lia | apply Osv; lia ]
       | |- _ => assumption
       end.
Qed.

(* The b5_CUT bundles the entry 0x820f8 carries across a register change that keeps registers 2 9 18 20-25
   (Seg/F12.v's f12_body_regs, here over ACtlCutP's records). *)
Lemma g12_body_regs : forall (cx : ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  K11c.getr regs' 2 = K11c.getr regs 2 -> K11c.getr regs' 9 = K11c.getr regs 9 ->
  K11c.getr regs' 18 = K11c.getr regs 18 -> K11c.getr regs' 20 = K11c.getr regs 20 ->
  K11c.getr regs' 21 = K11c.getr regs 21 -> K11c.getr regs' 22 = K11c.getr regs 22 ->
  K11c.getr regs' 23 = K11c.getr regs 23 -> K11c.getr regs' 24 = K11c.getr regs 24 ->
  K11c.getr regs' 25 = K11c.getr regs 25 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.b5_C cx j phi fr regs m ->
  ACtlCutP.b5_K cx j phi fr regs m -> ACtlCutP.b5_F17 cx j phi fr regs m -> ACtlCutP.b5_W240 cx j regs m ->
  ACtlCutP.b5_PF cx j phi fr regs m ->
  ACtlCutP.FLSI cx j fr regs' m /\ ACtlCutP.LK cx fr j regs' m /\ ACtlCutP.b5_C cx j phi fr regs' m /\
  ACtlCutP.b5_K cx j phi fr regs' m /\ ACtlCutP.b5_F17 cx j phi fr regs' m /\ ACtlCutP.b5_W240 cx j regs' m /\
  ACtlCutP.b5_PF cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E2 E9 E18 E20 E21 E22 E23 E24 E25 H1 H2 H3 H4 H5 H6 H7.
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.LK,
    ACtlCutP.b5_C, ACtlCutP.b5_PH, ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.b5_K, ACtlCutP.b5_sp,
    ACtlCutP.b5_F17, ACtlCutP.b5_W240, ACtlCutP.b5_PF, ACtlCutP.spill, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite ?E2, ?E9, ?E18, ?E20, ?E21, ?E22, ?E23, ?E24, ?E25.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7)))))).
Qed.

(* ---- the shared lemma: the walk from 0x820fc (f12_P on the b5 shell) through the run to the exit cut ---- *)
Lemma g12_at_fc : forall POST (j : nat) (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 (W3 : Reusable.YA0n.world segs)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3 (phi : Z),
  CF POST (ix_cut C_A82138_at [Z.of_nat j]) ->
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 14 + 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat j]) + 1 ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  ACtlCut.c_n cx < 2 ^ 26 -> (j <= 255)%nat ->
  ACtlCutP.HB mem3 phi (ACtlCutP.flen cx j) ->
  ACtlCutP.FLSI cx j fr regs3 mem3 -> ACtlCutP.LK cx fr j regs3 mem3 ->
  ACtlCutP.b5_C cx j phi fr regs3 mem3 ->
  ACtlCutP.b5_K cx j phi fr regs3 mem3 -> ACtlCutP.b5_RC fr mem3 -> ACtlCutP.IDb1 cx fr j mem3 ->
  ACtlCutP.b5_F17 cx j phi fr regs3 mem3 -> ACtlCutP.b5_W240 cx j regs3 mem3 ->
  ACtlCutP.b5_PF cx j phi fr regs3 mem3 ->
  A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x820fc regs3 mem3 md3) (POST cx).
Proof.
  intros POST j cx fr k ly3 S3 W3 regs3 mem3 md3 phi HX HB HJ HF HL Hk HFRAC HPerm Hn26 Hj255 HHB HFLSI HLK
    HC HK HRC HID H17 H240 HPF Hrt.
  assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* ---- G2: the frame, the stack window and the spill area ---- *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkok & _).
  destruct Hstkok as (_ & _ & Hceil & Hstklo & Hsphi & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ESlo & EShi & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite Efr3 in Hf4096, Hfceil, Hfapp.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  pose proof (@M05c.alloc_ceiling_value rc) as [[Hcmin Hcmax] _].
  pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as HGT0.
  rewrite Efr3 in HGT0.
  assert (HGT : IB.IMG_HI <= fr) by (unfold IB.IMG_HI; lia).
  assert (HGTn : 6283264 <= fr) by (unfold IB.IMG_HI in HGT; lia).
  assert (Hfrapp : forall x, fr <= x < fr + 4096 -> ART.app_mem x).
  { intros x Hx. apply (g12_frame_app B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x LAWS HAR Hin6).
    rewrite Efr3. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (Hfrapp' : forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> ART.app_mem x)
    by (intros x Hx; apply Hfrapp; unfold ACtlCutP.FRAME_BYTES in Hx; lia).
  pose proof HFRAC as (Aa & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA416 & Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo. unfold ART.APPMEM_END in HSapp. unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (HAa0 : 0 <= Aa) by lia.
  assert (HAa1 : Aa < 2 ^ 64) by lia.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hfrsp : fr + 4096 <= sp - 2224) by lia.
  assert (Hfrlh : fr + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= fr) by lia.
  destruct (g12_sh_bounds fr ltac:(lia) ltac:(lia)) as (HSHlo & HSHhi).
  (* the bundles, with every spill base equal to FRAC's A *)
  destruct HC as (R23 & R18 & (A5 & H95 & HA5 & HSPILL & Hq232) & HPH & HFR & HKN & HFGj & HFSj).
  pose proof (F12S.f12_A_eq regs3 Aa A5 R9 (conj HAa0 HAa1) H95 HA5) as EA. subst A5.
  destruct HSPILL as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
  destruct HFR as (HfgA & HidA & HFGb & HFGl).
  destruct HK as (R20 & R22 & R24 & R25 & (A280 & H9280 & HA280 & Hq280) & Hu176 & Hargs).
  pose proof (F12S.f12_A_eq regs3 Aa A280 R9 (conj HAa0 HAa1) H9280 HA280) as EA. subst A280.
  destruct HRC as (HADpa & HADpp & HADpn).
  destruct H17 as (A17 & H917 & HA17 & Hq200).
  pose proof (F12S.f12_A_eq regs3 Aa A17 R9 (conj HAa0 HAa1) H917 HA17) as EA. subst A17.
  destruct H240 as (A24 & H924 & HA24 & w240 & Hq240 & Hw0r & Hwt & Hwf).
  pose proof (F12S.f12_A_eq regs3 Aa A24 R9 (conj HAa0 HAa1) H924 HA24) as EA. subst A24.
  destruct HPF as (Ab & H9b & HAb & HL50 & H8819).
  pose proof (F12S.f12_A_eq regs3 Aa Ab R9 (conj HAa0 HAa1) H9b HAb) as EA. subst Ab.
  destruct HPH as (HPHg & _).
  destruct HHB as (Hphinz & HADphi).
  pose proof HADphi as (Hp0 & Hn0 & Hpe & Hall).
  destruct HFLSI as ((HPRO & S128 & Hfrstk & S144 & Had2691) & S216 & S224 & S248 & (HINad & HINby) & HFLC).
  destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
    P272 & P32).
  destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cad1 & Cad2 & C72 & C64 & C56 & C48).
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  (* route (C): the run's region (F12F.f12_run_shadow_R: the nine stored metadata bytes and memcpy's region at its
     call) lies in the owned class-6 frame's shadow [S(fr), S(fr) + 512), cut_shadow's (F) region (L3 recipe 2(c)) *)
  assert (HRreg : forall a, F12FS.f12_run_shadow_R fr a -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6 |].
    rewrite Efr3. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold F12FS.f12_run_shadow_R, A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R, A.Prog.sh_word_on.sh_word_on,
      A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
    rewrite !LMS.unsigned_lit in Ha by (unfold A.Prog.SlotInv.fragb; lia).
    unfold A.Prog.SlotInv.fragb, A.Prog.SlotInv.Sfr, ART.shadow_addr, ART.ASAN_K in Ha.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    clear - Ha Hfr32 Hfr0. Z.div_mod_to_equations. lia. }
  (* the block of this turn and the input block: live, below alloc_ceiling, apart from the frame *)
  assert (Hinblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinblk)
    as (_ & _ & Hphiceil & Hphiapp & _ & _ & Hflen0).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) 6
                (ACtlCut.c_fpos cx) HAR Hinblk Hin6) as Hphisep.
  rewrite Efr3 in Hphisep. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hphisep.
  unfold Reusable.YG0f.zdisjoint in Hphisep. cbn [fst snd] in Hphisep.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hphiapp.
  assert (Hrq : ACtlCutP.flen cx j <= Reusable.YG00.req_size (ACtlCutP.flen cx j))
    by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia).
  pose proof HB as (HBpre & _).
  pose proof HBpre as (_ & _ & _ & _ & Hinp & Hinlen & _).
  (* ---- the run's premises ---- *)
  assert (Hstk_lo : LFr.stk A.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) sp).
  { split; [lia |]. split; [lia |]. intros a Ha.
    destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hb).
    split; [exact (g12_wv_some mem3 _ b Hb) |].
    exists b. unfold LMem.mrd, LMem.wa. rewrite Hb. reflexivity. }
  assert (Hw152 : LMem.wr_at A.Img0.rsegs mem3 (Aa + 152) 8).
  { split; [lia |]. split; [lia |]. intros i Hi.
    destruct (Hpres (Aa + 152 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hb).
    exact (g12_wv_some mem3 _ b Hb). }
  assert (Hw256 : LMem.wr_at A.Img0.rsegs mem3 (Aa + 256) 24).
  { split; [lia |]. split; [lia |]. intros i Hi.
    destruct (Hpres (Aa + 256 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hb).
    exact (g12_wv_some mem3 _ b Hb). }
  destruct (F12S.f12_stk_rwb mem3 (fr + 336) 72 fr (fr + ACtlCutP.FRAME_BYTES) Hfrstk ltac:(lia)
              ltac:(unfold ACtlCutP.FRAME_BYTES; change (Z.of_nat 72) with 72; lia)) as (junk & Hjl & Hjrw).
  assert (HA416' : Aa + 416 <= ART.APPMEM_END) by (unfold ART.APPMEM_END; lia).
  assert (Hsp0 : 0 <= sp) by lia.
  assert (Hsp64 : sp < 2 ^ 64) by lia.
  assert (HspE : sp <= ART.APPMEM_END) by (unfold ART.APPMEM_END; lia).
  assert (Hlo : ART.HIGHMEM_BEG <= ACtlCut.c_sp cx - 32768) by (unfold ART.HIGHMEM_BEG; lia).
  assert (HloK : ACtlCut.c_sp cx - 32768 + A.Prog.asan_memcpy_c.ASAN_MEMCPY_K <= sp)
    by (unfold A.Prog.asan_memcpy_c.ASAN_MEMCPY_K; lia).
  assert (Hfrw2 : fr + ACtlCutP.FRAME_BYTES <= sp - 2224 \/ sp <= fr)
    by (left; unfold ACtlCutP.FRAME_BYTES; lia).
  (* visibility of the footprint regions at the cut's world *)
  assert (Vwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2.
    apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
             (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k lo len HJ); unfold A.ACfn.LLVMF_STK; lia. }
  assert (Vfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
            A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len /\
            (0 <= len -> fr <= 64 * (lo / 64) -> 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096 ->
             len = 0 \/ A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A.Prog.rng_asan.sh_al8_lo lo)
                 (A.Prog.rng_asan.sh_al8_hi lo len - A.Prog.rng_asan.sh_al8_lo lo))).
  { intros lo len H1 H2.
    pose proof (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len HAR Hin6)
      as HV.
    rewrite Efr3 in HV. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in HV. exact (HV H1 H2). }
  pose proof (Vwin (Aa + 152) 8 ltac:(lia) ltac:(lia)) as V152.
  pose proof (Vwin (Aa + 184) 8 ltac:(lia) ltac:(lia)) as V184.
  pose proof (Vwin (Aa + 192) 8 ltac:(lia) ltac:(lia)) as V192.
  pose proof (Vwin (sp - 2224) 2224 ltac:(lia) ltac:(lia)) as Vstk.
  destruct (Vfr (fr + 336) 72 ltac:(lia) ltac:(lia)) as (V336 & Hs336).
  destruct (g12_hull fr 336 72 Hfr32 Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)) as (Hu1 & Hu2).
  destruct (Hs336 ltac:(lia) Hu1 Hu2) as [Hz | Vsh336]; [lia |].
  destruct (Vfr (fr + 2768) 72 ltac:(lia) ltac:(lia)) as (V2768 & Hs2768).
  destruct (g12_hull fr 2768 72 Hfr32 Hfr0 ltac:(lia) ltac:(lia) ltac:(lia)) as (Hu3 & Hu4).
  destruct (Hs2768 ltac:(lia) Hu3 Hu4) as [Hz | Vsh2768]; [lia |].
  assert (V42 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (ART.shadow_addr fr + 42) 9).
  { destruct (g12_sh42 fr Hfr8 Hfr0) as (Hl1 & Hl2).
    exact (A.ProgBridge.range_visible_sub _ _ _ (ART.shadow_addr fr + 42) 9 Vsh336 Hl1 ltac:(lia) Hl2). }
  destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2224) 2224 HAR
              ltac:(rewrite ESlo; lia) ltac:(rewrite EShi; lia) ltac:(lia)) as [Hz | Vshstk]; [lia |].
  pose proof (A.ProgBridge.img_vis_W W3) as Vimg.
  (* ---- the run 0x820fc -> 0x82138 (F12F.f12_run_F), at the unit FPState built from the core's ---- *)
  pose proof (@F12FS.f12_run_F_on (K11u.mkFP K11c.fp_regs K11c.fp_csr)
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
                regs3 mem3 Aa fr sp (ACtlCut.c_sp cx - 32768) (SM.b2z (SM.t_tfill (ACtlCut.c_in cx) j))
                (SM.t_FG (ACtlCut.c_in cx) j) junk
                R2 R9 R19 R25 HGT Hfr8 HfrA HA416' HspA (conj Hsp0 Hsp64) HspE Hlo HloK Hfrw2 Hfrapp'
                Hw152 Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hstk_lo HRO HAC
                (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 HRreg Hcut)
                (A.ProgBridge.rng_of_visible _ _ _ V152) (A.ProgBridge.rng_of_visible _ _ _ V42)
                (A.ProgBridge.rng_of_visible _ _ _ V184) (A.ProgBridge.rng_of_visible _ _ _ V192)
                (A.ProgBridge.rng_bytes_RNG_W _) (A.ProgBridge.rng_of_visible _ _ _ Vimg)
                (A.ProgBridge.rng_of_visible _ _ _ Vstk) (A.ProgBridge.rng_of_visible _ _ _ V336)
                (A.ProgBridge.rng_of_visible _ _ _ V2768)
                (or_intror (A.ProgBridge.rng_of_visible _ _ _ Vsh336))
                (or_intror (A.ProgBridge.rng_of_visible _ _ _ Vsh2768))
                (or_intror (A.ProgBridge.rng_of_visible _ _ _ Vshstk))) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  (* ---- G3: the walk at the run's canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 K11c.fp_regs
           (Z_to_bv 64 0x820fc) K11c.fp_csr None mem3 (K11c.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* ---- G4: the lift ---- *)
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
           _ (POST cx) HFS); [exact (A.ProgBridge.fp_avoids_RNG_W _) |].
  (* ---- G5: the continuation at 0x82138 ---- *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (R & pc' & m' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 &
    K25 & K26 & MU & WM & ROt & STt & Q152 & RWd & BAs & ADd & ACt & SWt).
  subst ms' pc'.
  assert (E2 : K11c.getr R 2 = K11c.getr regs3 2) by exact K2.
  assert (E3 : K11c.getr R 3 = K11c.getr regs3 3) by exact K3.
  assert (E4 : K11c.getr R 4 = K11c.getr regs3 4) by exact K4.
  assert (E8 : K11c.getr R 8 = K11c.getr regs3 8) by exact K8.
  assert (E9 : K11c.getr R 9 = K11c.getr regs3 9) by exact K9.
  assert (E18 : K11c.getr R 18 = K11c.getr regs3 18) by exact K18.
  assert (E19 : K11c.getr R 19 = K11c.getr regs3 19) by exact K19.
  assert (E20 : K11c.getr R 20 = K11c.getr regs3 20) by exact K20.
  assert (E21 : K11c.getr R 21 = K11c.getr regs3 21) by exact K21.
  assert (E22 : K11c.getr R 22 = K11c.getr regs3 22) by exact K22.
  assert (E23 : K11c.getr R 23 = K11c.getr regs3 23) by exact K23.
  assert (E24 : K11c.getr R 24 = K11c.getr regs3 24) by exact K24.
  assert (E25 : K11c.getr R 25 = Z_to_bv 64 (ACtlCutP.fragb fr)) by exact K25.
  assert (E26 : K11c.getr R 26 = K11c.getr regs3 26) by exact K26.
  (* the write set f12_W against every class of carried byte *)
  assert (Osp : forall x, Aa <= x < Aa + 416 -> (x < Aa + 152 \/ Aa + 160 <= x) ->
                  LFr.outside (F12S.f12_W Aa fr sp) x)
    by (intros x Hx Hc; apply g12_out; lia).
  assert (Ofr : forall x, fr <= x < fr + 4096 -> (x < fr + 336 \/ fr + 408 <= x) ->
                  LFr.outside (F12S.f12_W Aa fr sp) x)
    by (intros x Hx Hc; apply g12_out; lia).
  assert (Osv : forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> LFr.outside (F12S.f12_W Aa fr sp) x)
    by (intros x Hx; apply g12_out; lia).
  assert (Ophi : forall x, phi <= x < phi + Reusable.YG00.req_size (ACtlCutP.flen cx j) ->
                   LFr.outside (F12S.f12_W Aa fr sp) x)
    by (intros x Hx; apply g12_out; lia).
  assert (Osh : forall y, ART.app_mem y -> ~ (fr + 336 <= y < fr + 408) ->
                  LFr.outside (F12S.f12_W Aa fr sp) (ART.shadow_addr y)).
  { intros y Hy Hny.
    pose proof (ARF.shadow_of_app y Hy) as Hs. destruct (F12S.f12_sh_lt _ Hs) as (Hs1 & Hs2).
    assert (Hy0 : 0 <= y) by (unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Hy; lia).
    unfold ART.LOWMEM_END, ART.HIGHMEM_BEG in Hs1, Hs2.
    apply g12_out; [lia | exact (F12S.f12_sh_out_fr fr y 42 51 Hfr8 Hfr0 Hy0 ltac:(lia)) | lia | lia]. }
  assert (Oin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
                  LFr.outside (F12S.f12_W Aa fr sp) x).
  { intros x Hx. destruct Hinp as [(Hn00 & _) | (_ & Hinb)]; [lia |].
    assert (Hinb3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hinb).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb3)
      as (_ & _ & Hiceil & Hiapp & _ & _ & Hin0).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx)
                  HAR Hinb3 Hin6) as Hisep.
    rewrite Efr3 in Hisep. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hisep.
    unfold Reusable.YG0f.zdisjoint in Hisep. cbn [fst snd] in Hisep.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Hiapp.
    assert (Hrqi : ACtlCut.c_n cx <= Reusable.YG00.req_size (ACtlCut.c_n cx))
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia).
    apply g12_out; lia. }
  (* the transports *)
  assert (Tq : forall off v, 0 <= off -> off + 8 <= 416 -> (off + 8 <= 152 \/ 160 <= off) ->
                 ACtlCutP.q64 mem3 (Aa + off) v -> ACtlCutP.q64 m' (Aa + off) v).
  { intros off v H0 H1 H2 Hq. apply (g12_q64 _ mem3 m' (Aa + off) v MU); [| exact Hq].
    intros x Hx. apply Osp; lia. }
  assert (Tsp : forall off v, 0 <= off -> off + 8 <= 416 -> (off + 8 <= 152 \/ 160 <= off) ->
                  ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v H0 H1 H2 Hs.
    apply (g12_sp _ mem3 m' regs3 R Aa off v R9 HAa0 ltac:(lia) H0 H1 E9 MU); [| exact Hs].
    intros x Hx. apply Osp; lia. }
  assert (Tfr : forall a bs, LMem.bytes_at segs mem3 a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + 3136 ->
                  (a + Z.of_nat (length bs) <= fr + 336 \/ fr + 408 <= a) -> LMem.bytes_at segs m' a bs).
  { intros a bs Hb H1 H2 H3. apply (g12_by _ mem3 m' a bs Hb MU). intros x Hx. apply Ofr; lia. }
  assert (Tphi : forall a bs, LMem.bytes_at segs mem3 a bs -> phi <= a ->
                   a + Z.of_nat (length bs) <= phi + ACtlCutP.flen cx j -> LMem.bytes_at segs m' a bs).
  { intros a bs Hb H1 H2. apply (g12_by _ mem3 m' a bs Hb MU). intros x Hx. apply Ophi. lia. }
  assert (Tin : LMem.bytes_at segs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
                LMem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { intros Hb. apply (g12_by _ mem3 m' _ _ Hb MU). intros x Hx. apply Oin. lia. }
  assert (Tad : forall p n, ART.addressable mem3 p n -> ART.addressable m' p n).
  { intros p n (Ha1 & Ha2 & Ha3 & Ha). split; [exact Ha1 |]. split; [exact Ha2 |]. split; [exact Ha3 |].
    intros i Hi.
    destruct (Z_lt_le_dec (p + i) (fr + 336)) as [h1 | h1];
      [| destruct (Z_lt_le_dec (p + i) (fr + 408)) as [h2 | h2]].
    - destruct (Ha i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |]. exists b. split; [| exact Hok].
      pose proof (ARF.shadow_of_app (p + i) Happ) as Hs. pose proof (ARF.in_shadow_range _ Hs) as (Hr1 & Hr2).
      unfold LMem.mrd. rewrite MU; [exact Hb |]. rewrite LMem.wa_unsigned by lia. apply Osh; [exact Happ | lia].
    - destruct ADd as (_ & _ & _ & Hd). replace (p + i) with (fr + 336 + (p + i - (fr + 336))) by lia.
      apply Hd. lia.
    - destruct (Ha i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |]. exists b. split; [| exact Hok].
      pose proof (ARF.shadow_of_app (p + i) Happ) as Hs. pose proof (ARF.in_shadow_range _ Hs) as (Hr1 & Hr2).
      unfold LMem.mrd. rewrite MU; [exact Hb |]. rewrite LMem.wa_unsigned by lia. apply Osh; [exact Happ | lia]. }
  assert (Tb8 : forall a v, ACtlCutP.b8 mem3 a v -> phi <= a -> a + 1 <= phi + ACtlCutP.flen cx j ->
                  ACtlCutP.b8 m' a v).
  { intros a v Hb H1 H2. unfold ACtlCutP.b8 in *.
    apply Tphi; [exact Hb | exact H1 | cbn [length]; change (Z.of_nat 1) with 1; exact H2]. }
  assert (Tsh8 : forall y, phi <= y < phi + ACtlCutP.flen cx j ->
                   ACtlCutP.b8 mem3 (Z.shiftr y 3 + A.ACtlK.ASAN_K) 0 ->
                   ACtlCutP.b8 m' (Z.shiftr y 3 + A.ACtlK.ASAN_K) 0).
  { intros y Hy Hb. unfold ACtlCutP.b8 in *.
    assert (Es : Z.shiftr y 3 + A.ACtlK.ASAN_K = ART.shadow_addr y)
      by (rewrite Z.shiftr_div_pow2 by lia; unfold ART.shadow_addr, A.ACtlK.ASAN_K; reflexivity).
    rewrite Es in Hb |- *. apply (g12_by _ mem3 m' _ _ Hb MU). intros x Hx.
    cbn [length] in Hx. change (Z.of_nat 1) with 1 in Hx.
    replace x with (ART.shadow_addr y) by lia. apply Osh; [| lia].
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia. }
  (* the destination's 72 bytes, the frame window and the frame's metadata after the run *)
  assert (TBL : LMem.bytes_at segs m' (fr + 336) (SM.t_FG (ACtlCut.c_in cx) j)).
  { pose proof RWd as ((_ & Hb) & _). cbn [LCells.cells_bytes LCells.cbytes] in Hb.
    rewrite app_nil_r in Hb. exact Hb. }
  assert (Hfrstk' : LFr.stk A.Img0.rsegs m' fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (F12S.f12_stk_after (F12S.f12_W Aa fr sp) mem3 m' fr (fr + ACtlCutP.FRAME_BYTES) Hfrstk MU WM).
    intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
    destruct (Z_lt_le_dec x (fr + 336)) as [h1 | h1]; [left; apply Ofr; lia |].
    destruct (Z_lt_le_dec x (fr + 408)) as [h2 | h2]; [right | left; apply Ofr; lia].
    exact (F12S.f12_bytes_mrd m' (fr + 336) _ x TBL ltac:(rewrite HFGl; change (Z.of_nat 72) with 72; lia)). }
  assert (HFSv : ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (Hshnew : exists sh, LMem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\
                              length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { assert (HshIS : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> ART.in_shadow a)
      by (intros a Ha; exact (F12S.f12_in_shadow_fr fr a Hfrapp' Hfr8 Ha)).
    (* route (C): the frame's 392 shadow bytes lie in cut_shadow's (F) region, carried across the run by its post *)
    assert (HFsh : forall a, F12S.f12_shadow_stk_shadow_R (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW) a ->
                   A.ACtlRtC.cut_shadow B ly3 S3 a).
    { intros a Ha. unfold F12S.f12_shadow_stk_shadow_R in Ha. left. exists 6, (ACtlCut.c_fpos cx).
      split; [exact Hin6 |]. rewrite Efr3. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      rewrite HFSv in Ha. unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in Ha.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    assert (HshStk : LFr.stk A.Img0.rsegs m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW))
      by (apply (F12S.f12_shadow_stk_on m' _ _); [| exact HshIS | unfold ACtlCutP.Sfr; lia | rewrite ?HFSv; unfold ACtlCutP.Sfr; lia];
          exact (A.ShadowRwOn.shadow_rw_on_mono _ _ m' HFsh (SWt _ Hcut))).
    destruct (F12S.f12_bytes_of_stk m' (ACtlCutP.Sfr fr) (Z.to_nat ACtlCutP.FRAME_SHADOW) _ _ HshStk ltac:(lia)
                ltac:(rewrite HFSv; change (Z.of_nat (Z.to_nat 392)) with 392; lia)) as (sh & Hl & Hb).
    exists sh. split; [exact Hb | exact Hl]. }
  assert (HFRAC' : ACtlCutP.FRAC B cx fr fr R m').
  { apply (g12_frac_mem cx fr fr R mem3 m' (F12S.f12_W Aa fr sp) Aa
             (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)
             (g12_rgv R regs3 9 Aa E9 R9) HAa0 HAa1 MU); [ | | exact Ofr | exact Osv | exact Hshnew ].
    - intros x Hx. apply Osp; lia.
    - intros x Hx. apply Osp; lia. }
  (* the bundles at the new memory *)
  assert (HID1l : length (ACtlCutP.ID1 cx j) = 38%nat).
  { unfold ACtlCutP.ID1. rewrite F12S.f12_rpid_len; [reflexivity | apply F12S.f12_tID_len]. }
  assert (TFS : ACtlCutP.FSj cx fr j R m').
  { destruct HFSj as (S104 & S112 & Sbody & Sad & HFI).
    pose proof (F12S.f12_fs_body_len (ACtlCut.c_in cx) j) as Hbl.
    split; [apply Tsp; [lia | lia | lia | exact S104] |].
    split; [apply Tsp; [lia | lia | lia | exact S112] |].
    split; [apply Tfr; [exact Sbody | lia | lia | lia] |].
    split; [apply Tad; exact Sad | exact HFI]. }
  assert (TID : ACtlCutP.IDb1 cx fr j m').
  { destruct HID as (HIDe & HIDok). split; [| exact HIDok]. unfold ACtlCutP.IDBe in *.
    apply Tfr; [exact HIDe | lia | rewrite HID1l; lia | rewrite HID1l; lia]. }
  assert (TFG : ACtlCutP.FGj cx fr j m').
  { destruct HFGj as (_ & Hfok). split; [exact BAs | exact Hfok]. }
  assert (TLK : ACtlCutP.LK cx fr j R m').
  { destruct HLK as (Hj & R21 & HOUR). split; [exact Hj |].
    split; [exact (g12_rgv R regs3 21 _ E21 R21) |].
    unfold ACtlCutP.OURb in *.
    apply Tfr; [exact HOUR | lia | rewrite SM.OUR_length; lia | rewrite SM.OUR_length; lia]. }
  (* the journal across the write set *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := g12_Wr Aa fr sp).
    - exact HJ.
    - intros x Hx. unfold g12_Wr in Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity |].
      apply MU. apply g12_out; lia.
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx |].
      destruct (g12_W_cases Aa fr sp (bv_unsigned x)) as [Hout | Hin].
      + rewrite (MU x Hout). exact Hx.
      + apply (g12_grow mem3 m' x); [| exact WM | exact Hx].
        unfold g12_Wr in Hin. lia.
    - exact Hhid.
    - exact Hsbm.
    - intros a Ha. unfold g12_Wr in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
      + left. unfold A.ACfn.LLVMF_STK. lia.
      + right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
        right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
        unfold ART.shadow_addr, ART.ASAN_K in Ha. lia.
      + right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + left. unfold A.ACfn.LLVMF_STK. lia. }
  (* route (C): the exit's ctl_rt_C keeps the regions (the state ly3 S3 is the entry's), across the run by its
     forall-P post; asan_cells / ro_agree from the run's post (L3 recipe 2(d)) *)
  assert (Hrt' : A.ACtlRtC.ctl_rt_C B ly3 S3 m')
    by (split; [exact ACt | split; [exact (SWt _ Hcut) | split; [exact (SWt _ Himg) | exact ROt]]]).
  (* the five runtime cells of the exit, from A.ProgWorldRtC.rt_of_core_C (FP := []) at the exit state *)
  pose proof (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI [] TFIB_SYMS LAWS cx (ACtlCut.own6 cx) k ly3 S3 W3
                (LMS.MS R K11c.fp_regs (Z_to_bv 64 0x82138) K11c.fp_csr None m' (K11c.seg_rom segs)) md' HB HJ' Hrt')
    as HRT.
  unfold A.ProgWorldRtC.RT_used_C in HRT.
  destruct HRT as (_ & _ & _ & _ & HCF & _ & _ & HREALS).
  assert (HRB : LMem.bytes_at A.Img0.rsegs m' 0xa17f0 (LMem.le8 (LMem.wa 0x97b0c))).
  { assert (Hin : In (0xa17f0, 0x97b0c) ART.RT_REALS)
      by (unfold ART.RT_REALS; repeat (first [left; reflexivity | right])).
    exact (proj1 (Forall_forall _ _) HREALS _ Hin
             ltac:(cbn [fst]; unfold A.ProgWorld.REAL_USED; left; reflexivity)). }
  assert (HRM : LMem.bytes_at A.Img0.rsegs m' 0xa17e8 (LMem.le8 (LMem.wa 0x97bdc))).
  { assert (Hin : In (0xa17e8, 0x97bdc) ART.RT_REALS)
      by (unfold ART.RT_REALS; repeat (first [left; reflexivity | right])).
    exact (proj1 (Forall_forall _ _) HREALS _ Hin
             ltac:(cbn [fst]; unfold A.ProgWorld.REAL_USED; right; left; reflexivity)). }
  (* ProgBridge.cfg_at_MS read backwards (eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82138_at [Z.of_nat j])) R m' md') (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB HJ' HF HL Hk); [| exact Hrt'].
  (* the exit body, C_A82138_at (ACtlCutP.v:2233-2263) *)
  split; [reflexivity |].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82138_at ACtlCutP.ixn nth].
  rewrite Nat2Z.id.
  exists phi.
  split; [exact HPerm |].
  split; [exact HFRAC' |].
  split; [exact Hn26 |].
  split; [exact Hj255 |].
  split; [split; [exact Hphinz | apply Tad; exact HADphi] |].
  split.
  { (* FLSI *)
    split.
    { (* FLSH *)
      split.
      { (* PRO *)
        split; [apply Tsp; [lia | lia | lia | exact P40] |].
        split; [apply Tsp; [lia | lia | lia | exact P120] |].
        split; [apply Tsp; [lia | lia | lia | exact P136] |].
        split; [apply Tsp; [lia | lia | lia | exact P160] |].
        split; [apply Tsp; [lia | lia | lia | exact P168] |].
        split; [apply Tsp; [lia | lia | lia | exact P176] |].
        split; [apply Tsp; [lia | lia | lia | exact P208] |].
        split; [apply Tsp; [lia | lia | lia | exact P248] |].
        split; [apply Tad; exact Pad |].
        split; [apply Tin; exact Pin |].
        split; [intros Hn; apply Tad; exact (Pg Hn) |].
        split; [apply Tsp; [lia | lia | lia | exact P184] |].
        split; [apply Tsp; [lia | lia | lia | exact P256] |].
        split; [apply Tsp; [lia | lia | lia | exact P264] |].
        split; [apply Tsp; [lia | lia | lia | exact P272] |].
        apply Tsp; [lia | lia | lia | exact P32]. }
      split; [apply Tsp; [lia | lia | lia | exact S128] |].
      split; [exact Hfrstk' |].
      split; [apply Tsp; [lia | lia | lia | exact S144] |].
      apply Tad; exact Had2691. }
    split; [apply Tsp; [lia | lia | lia | exact S216] |].
    split; [apply Tsp; [lia | lia | lia | exact S224] |].
    split; [apply Tsp; [lia | lia | lia | exact S248] |].
    split; [split; [apply Tad; exact HINad | apply Tin; exact HINby] |].
    (* FLC *)
    split; [apply Tsp; [lia | lia | lia | exact C256] |].
    split; [apply Tsp; [lia | lia | lia | exact C184] |].
    split; [apply Tsp; [lia | lia | lia | exact C192] |].
    split; [apply Tsp; [lia | lia | lia | exact C80] |].
    split; [apply Tsp; [lia | lia | lia | exact C88] |].
    split; [apply Tsp; [lia | lia | lia | exact C96] |].
    split; [apply Tsp; [lia | lia | lia | exact C272] |].
    split; [apply Tsp; [lia | lia | lia | exact C264] |].
    split; [apply Tad; exact Cad1 |].
    split; [apply Tad; exact Cad2 |].
    split; [apply Tsp; [lia | lia | lia | exact C72] |].
    split; [apply Tsp; [lia | lia | lia | exact C64] |].
    split; [apply Tsp; [lia | lia | lia | exact C56] |].
    apply Tsp; [lia | lia | lia | exact C48]. }
  split; [exact TLK |].
  exists Aa, (SM.b2z (SM.t_sum_ok (ACtlCut.c_in cx) j)).
  split; [exact (g12_rgv R regs3 9 Aa E9 R9) |].
  split; [unfold ACtlCut.rgv; exact E25 |].
  split; [exact (conj HAa0 HAa1) |].
  split; [unfold SM.b2z; destruct (SM.t_sum_ok (ACtlCut.c_in cx) j); lia |].
  split; [reflexivity |].
  split.
  { apply F12S.f12_q64_rw3.
    - apply Tq; [lia | lia | lia | exact Hq256].
    - replace (Aa + 256 + 8) with (Aa + 264) by lia. apply Tq; [lia | lia | lia | exact Hq264].
    - replace (Aa + 256 + 16) with (Aa + 272) by lia. apply Tq; [lia | lia | lia | exact Hq272].
    - exact (LFr.wr_at_transport A.Img0.rsegs mem3 m' (Aa + 256) 24 Hw256 WM). }
  split.
  { apply (F12S.f12_rw_of_bytes m' (ACtlCutP.fragb fr) _ 72); [exact BAs | exact HFGl |].
    apply (F12S.f12_wr_of_stk m' (ACtlCutP.fragb fr) (Z.of_nat 72) fr (fr + ACtlCutP.FRAME_BYTES) Hfrstk');
      unfold ACtlCutP.fragb, ACtlCutP.FRAME_BYTES; try change (Z.of_nat 72) with 72; lia. }
  split; [apply Tad; exact HfgA |].
  split; [apply Tad; exact HADpa |].
  split; [apply Tad; exact HADpp |].
  split; [apply Tad; exact HADpn |].
  split; [exact HRB |].
  split; [exact HRM |].
  split; [exact (F12S.f12_got_cf m' HCF) |].
  split; [exact (F12S.f12_cf_254 m' HCF) |].
  split; [exact (F12S.f12_cf_255 m' HCF) |].
  split; [apply Tq; [lia | lia | lia | exact Hq184] |].
  split; [apply Tq; [lia | lia | lia | exact Hq192] |].
  split; [apply Tq; [lia | lia | lia | exact Hq280] |].
  split; [exact TBL |].
  split; [exact ADd |].
  split; [apply Tq; [lia | lia | lia | exact Hq80] |].
  split; [apply Tq; [lia | lia | lia | exact Hq88] |].
  split; [apply Tq; [lia | lia | lia | exact Hq96] |].
  split; [apply Tq; [lia | lia | lia | exact Hq272] |].
  split; [apply Tq; [lia | lia | lia | exact Hq264] |].
  split.
  { (* F16CARRY *)
    split; [exact (proj2 TFG) |].
    split; [exact TFS |].
    split; [exists (ACtlCutP.ID1 cx j); split; [exact (proj1 TID) | exact HID1l] |].
    split; [apply Tad; exact HidA |].
    split; [apply Tq; [lia | lia | lia | exact Hq144] |].
    (* F17CARRY *)
    split; [exact (g12_rgv R regs3 23 _ E23 R23) |].
    split; [exact (g12_rgv R regs3 22 _ E22 R22) |].
    split; [exact (g12_rgv R regs3 24 _ E24 R24) |].
    split; [exact (g12_rgv R regs3 18 _ E18 R18) |].
    split; [exact (g12_rgv R regs3 20 _ E20 R20) |].
    split; [apply Tq; [lia | lia | lia | exact Hq232] |].
    split; [apply Tq; [lia | lia | lia | exact Hq200] |].
    split; [apply Tq; [lia | lia | lia |
            exact (F12S.f12_spill_q64 regs3 mem3 Aa 136 _ R9 (conj HAa0 HAa1) ltac:(lia) ltac:(lia) P136)] |].
    split; [apply Tq; [lia | lia | lia |
            exact (F12S.f12_spill_q64 regs3 mem3 Aa 120 _ R9 (conj HAa0 HAa1) ltac:(lia) ltac:(lia) P120)] |].
    split; [apply Tq; [lia | lia | lia |
            exact (F12S.f12_spill_q64 regs3 mem3 Aa 176 _ R9 (conj HAa0 HAa1) ltac:(lia) ltac:(lia) P176)] |].
    split; [exists Aa; split; [exact (g12_rgv R regs3 9 Aa E9 R9) | exact Q152] |].
    split.
    { exists w240. split; [apply Tq; [lia | lia | lia | exact Hq240] |].
      split; [exact Hw0r |]. split; [exact Hwt | exact Hwf]. }
    split.
    { intros H50.
      destruct (HL50 H50) as ((rb & Hrb & Hrbl) & Hphib).
      assert (HGl : length (SM.t_g (ACtlCut.c_in cx) j) = 50%nat) by (unfold SM.t_g; apply SM.fr50_length).
      assert (TG : LMem.bytes_at segs m' phi (SM.t_g (ACtlCut.c_in cx) j))
        by (apply Tphi; [exact (HPHg H50) | lia | rewrite HGl; change (Z.of_nat 50) with 50; lia]).
      split.
      { exists (firstn 38 rb). split; [| rewrite length_firstn; lia].
        apply Tphi; [apply F12S.f12_bytes_first; exact Hrb | lia | rewrite length_firstn; lia]. }
      split; [exact TG |].
      split.
      { apply Tphi; [exact Hphib | lia |]. pose proof (F12S.f12_phi_len (ACtlCut.c_in cx) j) as Hpl.
        unfold ACtlCutP.flen in *. lia. }
      (* rec_inv0 *)
      split; [lia |].
      split; [unfold A.ACtlK.a_size, ART.APPMEM_END in Hpe; lia |].
      split; [exact H50 |].
      split; [pose proof (RPA.ctrlparse_kind_range (SM.t_len (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j));
              unfold SM.t_k; lia |].
      split.
      { intros a Ha. destruct (Hall (a - phi) ltac:(unfold A.ACtlK.a_size; lia)) as (Happ & _).
        replace a with (phi + (a - phi)) by lia. exact Happ. }
      split; [apply Tq; [lia | lia | lia | exact Hq200] |].
      split; [unfold SM.t_blk; apply F12S.f12_bytes_bsl;
              [exact TG | lia | lia | rewrite HGl; change (Z.of_nat 50) with 50; lia] |].
      split; [apply F12S.f12_bytes_bsl; [exact TG | lia | lia | rewrite HGl; change (Z.of_nat 50) with 50; lia] |].
      split; [apply Tq; [lia | lia | lia | exact Hq248] | apply Tq; [lia | lia | lia | exact Hq280]]. }
    intros H88.
    assert (Hbig : 50 <= ACtlCutP.flen cx j).
    { pose proof H88 as Hb8. unfold SM.t_8819 in Hb8. apply andb_prop in Hb8 as (Hb8 & _).
      apply andb_prop in Hb8 as (Hb8 & _). unfold SM.t_big in Hb8. apply Z.leb_le in Hb8. exact Hb8. }
    destruct (H8819 H88) as (HPG & (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hmc & Had186) &
                             (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hmc2 & Had180)).
    split.
    { (* rec_parse *)
      destruct HPG as (f16 & v14 & v15 & v16 & v17 & U16 & B14 & B15 & B16 & B17 & r14 & r15 & r16 & r17 &
                       Z14 & Z15 & Z16 & Z17 & Ef & Ek).
      exists f16, v14, v15, v16, v17.
      split; [unfold ACtlCutP.u16 in *; apply Tfr;
              [exact U16 | lia | rewrite LMem.length_le2; change (Z.of_nat 2) with 2; lia
              | rewrite LMem.length_le2; change (Z.of_nat 2) with 2; lia] |].
      split; [apply Tb8; [exact B14 | lia | lia] |].
      split; [apply Tb8; [exact B15 | lia | lia] |].
      split; [apply Tb8; [exact B16 | lia | lia] |].
      split; [apply Tb8; [exact B17 | lia | lia] |].
      split; [exact r14 |]. split; [exact r15 |]. split; [exact r16 |]. split; [exact r17 |].
      split; [apply Tsh8; [lia | exact Z14] |].
      split; [apply Tsh8; [lia | exact Z15] |].
      split; [apply Tsh8; [lia | exact Z16] |].
      split; [apply Tsh8; [lia | exact Z17] |].
      split; [exact Ef | exact Ek]. }
    split.
    { exists (firstn 6 ls), (firstn 6 rs).
      split; [apply Tq; [lia | lia | lia | exact Hq72] |].
      split; [apply Tfr; [apply F12S.f12_bytes_first; exact Hls | lia | rewrite length_firstn; lia
                         | rewrite length_firstn; lia] |].
      split; [rewrite length_firstn; lia |].
      split; [apply Tphi; [apply F12S.f12_bytes_first; exact Hrs | lia | rewrite length_firstn; lia] |].
      split; [rewrite length_firstn; lia |].
      split; [rewrite F12S.f12_mcmp_firstn; exact Hmc |].
      apply Tad; exact Had186. }
    exists (firstn 6 ls2), (firstn 6 rs2).
    split; [apply Tq; [lia | lia | lia | exact Hq64] |].
    split; [apply Tfr; [apply F12S.f12_bytes_first; exact Hls2 | lia | rewrite length_firstn; lia
                       | rewrite length_firstn; lia] |].
    split; [rewrite length_firstn; lia |].
    split; [apply Tphi; [apply F12S.f12_bytes_first; exact Hrs2 | lia | rewrite length_firstn; lia] |].
    split; [rewrite length_firstn; lia |].
    split; [rewrite F12S.f12_mcmp_firstn; exact Hmc2 |].
    apply Tad; exact Had180. }
  (* IFS1 *)
  split; [exact TID |]. split; [exact TFG | exact TFS].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The stage. *)
Lemma glue_seg_F12 : forall POST (j : nat),
  CF POST (ix_cut C_A82138_at [Z.of_nat j]) -> CF POST (ix_cut C_A820fc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A820f8_at [Z.of_nat j]).
Proof.
  intros POST j HX. split.
  - (* C_A820fc_at (ACtlCutP.v:2219-2229): its body minus `ir = false` is the shared lemma's (F12.v's f12_entry1) *)
    intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
    destruct Hbody as [Hidx Hb]. subst idx.
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A820fc_at ACtlCutP.ixn nth] in Hb.
    rewrite Nat2Z.id in Hb.
    destruct Hb as (HFRAC & phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HLK & HC & HP).
    cbv beta in HP.
    destruct HP as (HK & HRC & _ & HID & H17 & H240 & HPF).
    exact (g12_at_fc POST j cx fr k ly3 S3 W3 regs3 mem3 md3 phi HX HB HJ HF HL Hk HFRAC HPerm Hn26 Hj255 HHB
             HFLSI HLK HC HK HRC HID H17 H240 HPF Hrt).
  - (* C_A820f8_at (ACtlCutP.v:2205-2215): `bltz a0` not taken (F12F.f12_entry2_F), then the shared lemma *)
    intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
    destruct Hbody as [Hidx Hb]. subst idx.
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A820f8_at ACtlCutP.ixn nth] in Hb.
    rewrite Nat2Z.id in Hb.
    destruct Hb as (HFRAC & phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HLK & HC & HP).
    cbv beta in HP.
    destruct HP as (HK & HRC & _ & (v & R10 & Hv) & HID & H17 & H240 & HPF).
    (* G3 *)
    rewrite A.ProgBridge.cfg_at_MS.
    change (ACtlCut.cut_pc (ix_cut C_A820f8_at [Z.of_nat j])) with 0x820f8.
    apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 K11c.fp_regs
             (Z_to_bv 64 0x820f8) K11c.fp_csr None mem3 (K11c.seg_rom segs) md3 (POST cx));
      [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
    (* G4: register only, the empty footprint *)
    pose proof (@F12FS.f12_entry2_F (K11u.mkFP K11c.fp_regs K11c.fp_csr) A.ACtlG.Kit.kit_RNG0 regs3 mem3 v R10 Hv)
      as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    (* G5: the state at 0x820fc, same memory, the model materialized *)
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 &
      K23 & K24 & K25 & K26).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x820fc R mem3 md') (POST cx)).
    assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
    { eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply K1bc.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha]. }
    destruct (g12_body_regs cx j phi fr regs3 R mem3 K2 K9 K18 K20 K21 K22 K23 K24 K25 HFLSI HLK HC HK H17 H240 HPF)
      as (HFLSI' & HLK' & HC' & HK' & H17' & H240' & HPF').
    exact (g12_at_fc POST j cx fr k ly3 S3 W3 R mem3 md' phi HX HB HJ' HF HL Hk
             (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)
             HPerm Hn26 Hj255 HHB HFLSI' HLK' HC' HK' HRC HID H17' H240' HPF' Hrt).
Qed.

End GlueF12.

Print Assumptions glue_seg_F12.
