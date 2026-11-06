(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module names changed; 391 of its 424 lines of code are new or changed and 2042 lines of the source are left out. *)
(* lib/A/ACtlG/F5_df0.v -- GLUE for stage seg_F5_df0 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:753), plus the four shared lemmas of the F5 glue lanes that this lane owns (the contract of
   f5-glue-context.md (a working note, not in this delivery)).  Written by a Theorem Labs lane;
   single writer.  rule 24: no function proved (kind: segment lemma) -- a glue stage of image A's entry walk.

   WHAT IT PROVES
     f5g_frac_keep, f5g_ctl_rt_C_keep, f5g_journal, f5g_bounds (the shared lemmas, Section SharedF5 / SharedF5J),
     f5g_frac_base (a helper for f5g_bounds' range premise), and
     glue_seg_F5_df0 : forall POST (j : nat),
       CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e88_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F5_df0.  Segment F5_df0 is 0x81e88 -> 0x81f54, the short-frame arm (flen j < 50):
     0x81e88 bnez s8 (s8 = t_k j = 0, not taken)   0x81e8c li s6,0   0x81e90 li s9,0   0x81e94 sd zero,240(s1)
     0x81e98 sd zero,280(s1)   0x81e9c li s4,1   0x81ea0 j 0x81f54.
   The plain frame-route proof of the same stage is lib/A/Prog/Seg/F5.v:766-925 (seg_F5_df0); it is the map of
   what the exit body needs.

   THE PROOF, step by step (A5.v's G1-G5, glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index equation, then C_A81e88_at (ACtlCutP.v:2037-2046): FRAC and
       b5_body with flen < 50, rgv 24 t_k, u32 [fr+176], IDj, b5_F17, b5_PF; Z.to_nat (Z.of_nat j) = j.
   G2  the run's premises from visible state: t_k j = 0 (Seg/F5.v f5_k, flen < 50), so rgv 24 0; s1 = Asp, the
       spill base of FRAC (f5g_frac_base gives its range); the bounds of f5g_bounds (FRAC + the journal's
       astk_ok + AR's al_blocks over the body's Permutation + the lib pre's input block); the stack window
       [c_sp - LLVMF_STK, c_sp) of the journal is apresent in mem3, which gives stk rsegs mem3 [Asp+240, Asp+288)
       and the two rng (RNG_W (w_H W3)) premises (ProgBridge.rng_of_visible).
   G3  ProgBridge.cfg_at_MS, then the walk moved to the run's canonical map (YA0nR.SRr_xregs_eqv).
   G4  the run Seg/F5F.seg_F5_df0_run_F at fx := A.Reusable.YK11.mkFP fp_regs fp_csr, Asp, RNG_W (w_H W3); lifted by
       ProgBridge.fevt_of_evtF + tfibsegs_rsegs + YA0nR.SRr_fevt_hid (the run writes memory; fp_avoids by
       ProgBridge.fp_avoids_RNG_W).
   G5  the exit cut C_A81f54_at at the run's end map R and mem' = the two 8-byte zero stores; the write set is
       W := [(Asp+240, Asp+248); (Asp+280, Asp+288)] (munch by lib.Lib.Frame.munch_write twice, wmono by
       wmono_write, all_app by Seg/F5.v f5_app_ivl):
         journal  f5g_journal (both cells lie in the stack window);
         frames, frame law, k bound   unchanged (own6, the same kmax on both cuts);
         FRAC     f5g_frac_keep (FRAC's cells lie below Asp + 240 or from Asp + 288 on; the class-6 frame below
                  Asp by f5g_frame_below);
         HB FLSI LK b5_C IDj   A.ACtlG.F5_e10.f5g_keep (a Theorem Labs lane's shared lemma);
         b5_K     R20 = 1, R22 = 0, R25 = 0 (f5_sum / f5_big / f5_tfill, flen < 50), R24 = t_k, the new
                  [Asp+280] = 0 (lib.Lib.Mem.bytes_at_write_same), u32 kept (f5_u32_keep), reply_args by f5_reply
                  (0 < fr: frames_bounds on the journal's AR + the frame law + layout_le's ly_F, as A5.v:167-175);
         b5_F17   kept ([Asp+200] < Asp + 240); b5_W240 the new [Asp+240] = 0 (bytes_at_write_other / _same)
                  with f5_8819; b5_PF vacuous (flen < 50, t_8819 j = false);
         ctl_rt_C f5g_ctl_rt_C_keep at the entry's ly3 S3 (route (C) L3: the state is kept, so the regions are kept;
                  every written byte is above HIGHMEM_BEG <= Asp, so outside the image and the shadow).

   THE SHARED LEMMAS (statements of the contract, with the contract's register reads written
   lib.Reusable.YK11.getr and its frame vocabulary Lib.Frame, a Theorem Labs lane 04:2xZ; binder syntax the owner's)
     f5g_frac_keep   FRAC moves to (regs', m') when the seven FRAC registers are kept and the write set misses
                     [.., A + 240) and [A + 288, ..).  A is any representative of register 9 with
                     HIGHMEM_BEG <= A; FRAC's own base A' is A or A >= 2 ^ 64 (both name the same word).
                     ROBUST TO A FRAC TRAILER (a Theorem Labs lane 05:53Z: an appended `q64 m (fr + 4088) ..` word): the proof
                     reads FRAC's numeric facts by a PREFIX destruct ending in `_`, then walks FRAC's conjuncts
                     generically (register words by the seven register equations, 8-byte cells and byte strings
                     by the frame keeps), so an appended conjunct of either kind needs no edit here.  Its premise
                     `fr + fs_frame_bytes 6 <= A` (the whole class-6 fake frame [fr, fr + 4096) lies below the
                     spill area) is what keeps a word at fr + 4088; f5g_frame_below gives it.
     f5g_frame_below fr + fs_frame_bytes 6 <= A, from the journal's AR (frames_bounds: the frame ends at or below
                     alloc_ceiling), the frame law and layout_le's ly_F, the journal's astk_ok (alloc_ceiling <=
                     ly_stk_lo, ly_stk_lo + LLVMF_STK <= c_sp) and FRAC (c_sp - 4096 < sp <= A).
     f5g_ctl_rt_C_keep  A.ACtlRtC.ctl_rt_C B ly S across a write set above HIGHMEM_BEG, at the same ly S: the asan
                     cells by RcAsanFPLib.fl_bytes (each cell is in the image, below RT_HI < HIGHMEM_BEG); both
                     shadow parts (cut_shadow B ly S and img_shadow) by A.ShadowRwOnK.fl_shadow_rw_on, the write set
                     missing in_shadow (in_shadow x -> x < HIGHMEM_BEG); ro_agree because a read-only address is in
                     the image (the contrapositive of YCbq.find_segment_none, then Kit.kit_segs_low), so below
                     HIGHMEM_BEG.  It replaces f5g_ctlrt_keep (old ctl_rt form, deleted at the route (C) switch).
     f5g_journal     YCbq.ajournal_exec at Wr := fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a, every written
                     byte in the stack window (awr_byte's first arm); modelled on ProgWorld's ajournal_of_fsteps
                     (internal path).
     f5g_bounds      CONTRACT CHANGE (reported to a Theorem Labs lane): one added premise 0 <= A < 2 ^ 64.  Without it the
                     statement is false: rgv regs 9 A pins A only modulo 2 ^ 64, so A = A' - 2 ^ 64 satisfies
                     every other premise and violates HIGHMEM_BEG <= A.  f5g_frac_base supplies such an A.

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (YCbq.v:207), as ACtl.v:183 states it (ajournal_exec and frames_bounds take it).
   - The other ACtl.v Section Ctl entries (RELRO_IMG, TFIB_SYMS, TFIB_LIB, XN_LIB, the REAC_* variables) are
     copied verbatim and vanish at End Section (unused).
   CITED BY NAME: the run A.Prog.Seg.F5F.seg_F5_df0_run_F (F5F.v:82, blob 336a376f81d on the base); the model
   facts A.Prog.Seg.F5.f5_k / f5_big / f5_sum / f5_tfill / f5_8819 / f5_reply / f5_id / f5_app_ivl / f5_q64_keep /
   f5_u32_keep; A.Prog.RcAsanFPLib.fl_bytes; A.ShadowRwOnK.fl_shadow_rw_on; A.AsanRTFacts.all_app; Lib.Frame /
   Lib.Mem's write lemmas; Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt_hid; A.ProgBridge.*; Reusable.YCbq.ajournal_exec /
   frames_bounds / find_segment_none / asan_consts; Reusable.YG0d.al_blocks; A.ACtlG.Kit.kit_wx / kit_segs_low;
   A.ACtlG.F5_e10.f5g_keep.

   CLOSURE: every project Require below is qualified (no Import / Export of a project module); no STATEMENT names a
   frame-route identifier (Seg/F5.v, F5F.v and RcAsanFPLib.v are cited inside proofs only).  The core's twin
   modules are Required from the prefix ...fuzz_ctrl.lib.Reusable and written lib.Reusable.X, ctrl's from
   ...fuzz_ctrl.lib.A.Reusable and written A.Reusable.X (a Theorem Labs lane 04:2xZ and the porter's amendment 04:33Z: the
   unprefixed spelling of a twin resolves to ctrl's copy in a file that Requires ACtlCutP).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / A.Reusable.YK11 / Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F5_df0.v   -- hits only inside comments.

   ROUTE (C) L3 (a Theorem Labs lane, 2026-10-29; recipe L3-recipe.md (a working note, not in this delivery)):
   ctl_from hands the stage Hrt : A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch's shell).  The stage never opens Hrt
   (no destruct, no use of a shadow part): its one use is the exit, which keeps the state (the exit cut is applied
   at the same ly3 S3), so ctl_rt_C B ly3 S3 mem' is kept across the two stores by f5g_ctl_rt_C_keep (both shadow
   parts by A.ShadowRwOnK.fl_shadow_rw_on).  No VIS0 / OWNED_RO / AR_VIS0 / AR_OWNED_RO hypothesis and no
   stage-level ctlrt_of_AR.  The run's contract takes no mem_inv premise.

   BUILD STATE: type-check with cb build --fresh (BASE 23b918fe0c2e) on a working branch 1899bed1aee merged with
   a working branch; the lane report names the cbrec record (.prov), the .vo mtime and Print Assumptions of
   glue_seg_F5_df0, f5g_ctl_rt_C_keep, f5g_frac_keep and f5g_frame_below (Rocq primitives and
   functional_extensionality_dep only).  No Axiom, no Parameter, no Admitted, no admit; LAWS stays a Section
   hypothesis. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.AF0m A.ACeh A.ACtlRtC A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F5 A.Prog.Seg.F5F A.Prog.RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.F5_e10.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The shared lemmas (contract of <lane notes> f5-glue-context.md). *)

(* outside is decidable (a local copy of ProgWorld's pws_outside_dec). *)
Lemma f5g_outside_dec : forall (WR : list lib.Lib.Frame.ivl) x, lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [lib.Lib.Frame.outside]; intros x; [left; exact I|].
  assert (D : (lo <= x < hi) \/ ~ (lo <= x < hi)) by lia.
  destruct D as [D|D]; [right; tauto|]. destruct (IH x) as [H|H]; [left; tauto | right; tauto].
Qed.

Section SharedF5.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.

(* FRAC's spill base is a representative of register 9 in [0, 2 ^ 64). *)
Lemma f5g_frac_base : forall (B : Reusable.YG0f.asyms) (cx : ACtlCut.ctlcx) (fr sel : Z) (regs : bvmap 5 word)
    (m : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m -> exists A, ACtlCut.rgv regs 9 A /\ 0 <= A < 2 ^ 64.
Proof.
  intros B cx fr sel regs m H.
  destruct H as (A' & sp & R2 & Hspm & Hspz & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & _ & _ & _ & HAPP & _).
  exists A'. split; [exact R9|].
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ. exact (proj1 (bv_unsigned_in_range _ _)). }
  unfold A.AsanRT.APPMEM_END in HAPP. lia.
Qed.

Lemma f5g_frac_keep : forall (B : Reusable.YG0f.asyms) (cx : ACtlCut.ctlcx) (fr sel A : Z)
    (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list lib.Lib.Frame.ivl),
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> A.AsanRT.HIGHMEM_BEG <= A ->
  fr + Reusable.YG00.fs_frame_bytes 6 <= A ->
  lib.Lib.Frame.munch W m m' -> (forall x, x < A + 240 -> lib.Lib.Frame.outside W x) ->
  (forall x, A + 288 <= x -> lib.Lib.Frame.outside W x) ->
  lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs 2 ->
  lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs 3 ->
  lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs 4 ->
  lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs 8 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs 19 ->
  lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros B cx fr sel A regs regs' m m' W H H9 HA Hfrm6 MU Hlo Hhi E2 E3 E4 E8 E9 E19 E26.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HF6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite HHBv in HA. rewrite HF6 in Hfrm6.
  destruct H as (A' & sp & H).
  (* FRAC's numeric facts, read by a PREFIX destruct ending in `_` (a conjunct appended to FRAC leaves it valid) *)
  pose proof H as (_ & _ & Hspz & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & HfrA & HA416 & HS4 & HAPP & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ. exact (proj1 (bv_unsigned_in_range _ _)). }
  unfold ACtlCutP.FRAME_BYTES in HfrA. rewrite HAPPv in HAPP.
  (* A and FRAC's A' name the same word: A' is in range, so A = A' or A >= 2 ^ 64 *)
  assert (HAA : A = A' \/ 2 ^ 64 <= A).
  { assert (E : Z_to_bv 64 A = Z_to_bv 64 A')
      by (transitivity (lib.Reusable.YK11.getr regs 9); [symmetry; exact H9 | exact R9]).
    apply (f_equal (@bv_unsigned 64)) in E.
    rewrite !lib.Lib.MState.unsigned_lit_wrap in E.
    rewrite (Z.mod_small A') in E by lia.
    change (2 ^ 64) with 18446744073709551616 in *.
    Z.div_mod_to_equations. lia. }
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> (A = A' -> x < A + 240 \/ A + 288 <= x) -> lib.Lib.Frame.outside W x).
  { intros x Hx Hc. destruct HAA as [EA | HAbig].
    - destruct (Hc EA) as [H1 | H1]; [apply Hlo; exact H1 | apply Hhi; exact H1].
    - apply Hlo. lia. }
  exists A', sp.
  (* Every conjunct of FRAC, walked generically: the register words through the seven register equations (both
     getr copies unfolded to their common body first: FRAC's registers 2 3 4 are ctrl's getr, rgv the core's),
     the 8-byte cells by Seg/F5's f5_q64_keep, the byte strings by RcAsanFPLib.fl_bytes, each cell's range
     outside the write set by lia over FRAC's prefix facts and fr + 4096 <= A (the frame words, an appended
     trailer at fr + 4088 included), the frame shadow below HIGHMEM_BEG, the saved registers above A + 288. *)
  unfold ACtlCut.rgv, Reusable.YG0d.spZ, lib.Reusable.YK11.getr, A.Reusable.YK11.getr
    in H, E2, E3, E4, E8, E9, E19, E26 |- *.
  let side Hx :=
    intros EA;
    try (match goal with Hl : length ?s = _ |- _ => rewrite Hl in Hx end);
    try (unfold ACtlCutP.saved_bytes in Hx; rewrite ?length_app, ?lib.Lib.Mem.length_le8 in Hx);
    try change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392 in Hx;
    try (unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hx);
    first [left; lia | right; lia | left; Z.div_mod_to_equations; lia] in
  let cell Hc :=
    first
      [ exact Hc
      | rewrite ?E2, ?E3, ?E4, ?E8, ?E9, ?E19, ?E26; exact Hc
      | lazymatch type of Hc with
        | ACtlCutP.q64 m ?a ?v =>
            let Hb0 := fresh "Hb" in let Hb1 := fresh "Hb" in
            pose proof Hc as (Hb0 & Hb1 & _); rewrite ?lib.Lib.Mem.length_le8 in Hb1;
            apply (A.Prog.Seg.F5.f5_q64_keep W m m' a v Hc MU);
            let x := fresh "x" in let Hx := fresh "Hx" in
            intros x Hx; apply OUT; [lia | side Hx]
        | lib.Lib.Mem.bytes_at _ m ?a ?bs =>
            let Hb0 := fresh "Hb" in let Hb1 := fresh "Hb" in
            pose proof Hc as (Hb0 & Hb1 & _);
            apply (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hc MU);
            let x := fresh "x" in let Hx := fresh "Hx" in
            intros x Hx; apply OUT; [lia | side Hx]
        end ] in
  let rec walk Hc :=
    lazymatch type of Hc with
    | _ /\ _ =>
        let H1 := fresh "Hc" in let H2 := fresh "Hc" in
        destruct Hc as [H1 H2]; split; [walk H1 | walk H2]
    | ex _ =>
        let w := fresh "w" in let Hw := fresh "Hc" in
        destruct Hc as [w Hw]; exists w; walk Hw
    | _ => cell Hc
    end in
  walk H.
Qed.

Lemma f5g_ctl_rt_C_keep : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) (m m' : word -> option byte)
    (W : list lib.Lib.Frame.ivl),
  A.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  (forall x, x < A.AsanRT.HIGHMEM_BEG -> lib.Lib.Frame.outside W x) -> A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros B ly S m m' W (HAC & HCUT & HIMG & HRO) MU WM Hlow.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (T : forall a bs, lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs ->
                a + Z.of_nat (length bs) <= A.AsanRT.HIGHMEM_BEG -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Hl. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU). intros x Hx. apply Hlow. lia. }
  (* every shadow byte is below HIGHMEM_BEG, so outside the write set *)
  assert (HSW : forall x, A.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x).
  { intros x Hx. apply Hlow.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG in Hx.
    rewrite HHBv in Hx |- *. lia. }
  split; [|split; [|split]].
  - unfold A.ACtlK.asan_cells_at, A.AsanRT.asan_cells in *.
    destruct HAC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
    repeat match goal with |- _ /\ _ => split end;
      (apply T; [eassumption |]);
      rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4; cbn [length];
      rewrite HHBv; unfold A.AsanRT.CELL_K, A.AsanRT.UAR, A.AsanRT.INITED, A.AsanRT.REPLACE, A.AsanRT.CANPOISON,
        A.AsanRT.HIEND, A.AsanRT.MIDBEG, A.AsanRT.MIDEND, A.AsanRT.REAL_MEMCPY, A.AsanRT.REAL_MEMSET,
        A.AsanRT.GOT_CELL_K, A.AsanRT.GOT_UAR, A.AsanRT.GOT_REPLACE, A.AsanRT.GOT_HIEND, A.AsanRT.GOT_MIDBEG,
        A.AsanRT.GOT_MIDEND, A.AsanRT.GOT_REAL_MEMSET; lia.
  - (* (F) / (L) / (Z) / (FA): the regions do not move; the write set misses the shadow *)
    exact (A.ShadowRwOnK.fl_shadow_rw_on _ W m m' HCUT MU WM HSW).
  - (* (I) the image's shadow, the same way *)
    exact (A.ShadowRwOnK.fl_shadow_rw_on _ W m m' HIMG MU WM HSW).
  - intros a Hro. unfold lib.Lib.Mem.mrd. rewrite (MU a).
    + exact (HRO a Hro).
    + apply Hlow.
      destruct (Z_lt_le_dec (bv_unsigned a) A.AsanRT.HIGHMEM_BEG) as [Hl|Hl]; [exact Hl|]. exfalso.
      assert (Hn : ~ Reusable.YG0d.in_img A.Img0.rsegs (bv_unsigned a)).
      { intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low _ Hi) as Hb.
        unfold Reusable.YG0f.kLowMemEnd in Hb. rewrite HHBv in Hl. lia. }
      unfold lib.Lib.Mem.ro_addr in Hro.
      rewrite (Reusable.YCbq.find_segment_none A.Img0.rsegs (bv_unsigned a) Hn) in Hro. discriminate.
Qed.

(* The numeric facts the keeps need, from what ctl_from hands a stage.  CONTRACT CHANGE: the premise
   0 <= A < 2 ^ 64 is added (header). *)
Lemma f5g_bounds : forall (B : Reusable.YG0f.asyms) (MT : Reusable.YC5d.ameter_ops) (XM_LIB : Z -> Z) (RLO RHI : Z)
    (cx : ACtlCut.ctlcx) (own : list (Z * Z)) ly3 S3 W3 (m : word -> option byte) md3 (k fr sel A phi : Z)
    (j : nat) (regs : bvmap 5 word),
  Reusable.YG0d.AR_laws segs B ->
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 m md3 k ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  A.AsanRT.HIGHMEM_BEG <= A /\ A + 416 <= A.AsanRT.APPMEM_END /\ 0 <= fr /\
  fr + ACtlCutP.FRAME_BYTES <= A /\ phi + A.ACtlK.a_size (ACtlCutP.flen cx j) <= A /\
  ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A /\
  ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= A /\ A + 416 <= ACtlCut.c_sp cx.
Proof.
  intros B MT XM_LIB RLO RHI cx own ly3 S3 W3 m md3 k fr sel A phi j regs LAWS HB HJ HFRAC H9 HAr HPerm.
  destruct HFRAC as (A' & sp & _ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    _ & _ & _ & Qhdr & _).
  pose proof Qhdr as (Hfr0 & _).
  destruct HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & _).
  pose proof Reusable.YCbq.asan_consts as (HAC & _).
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HSTKv in Hlo. rewrite HAPPv in HAPP.
  assert (EA : A = A').
  { apply A.Prog.Seg.F5.f5_id; [exact HAr | lia |].
    transitivity (lib.Reusable.YK11.getr regs 9); [symmetry; exact H9 | exact R9]. }
  subst A'.
  (* the live block (phi, flen j) and the entry's input block are AR blocks of (ly3, S3) *)
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md3 _ _ HAR Hin) as (_ & _ & Hpc & _ & _ & _ & Hn).
  assert (Hrq : A.ACtlK.a_size (ACtlCutP.flen cx j) <= Reusable.YG00.req_size (ACtlCutP.flen cx j)).
  { unfold A.ACtlK.a_size, Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (Hinp : ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A).
  { destruct HB as (HPRE & _).
    destruct HPRE as (_ & _ & _ & _ & Hpn & Hlen & _).
    rewrite <- Hlen.
    destruct Hpn as [(Hn0 & Hp0) | (Hnpos & Hinp)].
    - rewrite Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hin2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinp. }
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md3 _ _ HAR Hin2) as (_ & _ & Hpc2 & _).
      unfold Reusable.YG00.req_size in Hpc2.
      rewrite (proj2 (Z.eqb_neq (ACtlCut.c_n cx) 0) ltac:(lia)) in Hpc2. lia. }
  rewrite HHBv, HAPPv, HSTKv.
  split; [lia|]. split; [lia|]. split; [exact Hfr0|]. split; [exact HfrA|].
  split; [lia|]. split; [exact Hinp|]. split; lia.
Qed.

(* The class-6 fake frame [fr, fr + fs_frame_bytes 6) lies below FRAC's spill base A: the frame ends at or below
   alloc_ceiling (frames_bounds on the journal's AR, the frame law, layout_le's ly_F), the journal's astk_ok puts
   the stack above it (alloc_ceiling <= ly_stk_lo, ly_stk_lo + LLVMF_STK <= c_sp), and FRAC puts A above c_sp - 4096.
   It is f5g_frac_keep's frame premise. *)
Lemma f5g_frame_below : forall (B : Reusable.YG0f.asyms) (cx : ACtlCut.ctlcx) (own : list (Z * Z)) ly3 S3 W3
    (m : word -> option byte) md3 (k fr sel A : Z) (regs : bvmap 5 word),
  Reusable.YG0d.AR_laws segs B ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 m md3 k ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) ->
  fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 ->
  fr + Reusable.YG00.fs_frame_bytes 6 <= A.
Proof.
  intros B cx own ly3 S3 W3 m md3 k fr sel A regs LAWS HJ Hin Efr HFRAC H9 HAr.
  destruct HFRAC as (A' & sp & _ & _ & Hspz & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & Hspa & _ & _ & HS4 & HAPP & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ. exact (proj1 (bv_unsigned_in_range _ _)). }
  unfold A.AsanRT.APPMEM_END in HAPP.
  assert (EA : A = A').
  { apply A.Prog.Seg.F5.f5_id; [exact HAr | lia |].
    transitivity (lib.Reusable.YK11.getr regs 9); [symmetry; exact H9 | exact R9]. }
  subst A'.
  destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & _).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 m md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Htop & _).
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  rewrite HSTKv in Hlo.
  rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. lia.
Qed.

End SharedF5.

Section SharedF5J.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.

(* The journal across a run whose writes lie in the stack window (ajournal_exec with Wr := ~ outside WR). *)
Lemma f5g_journal : forall (B : Reusable.YG0f.asyms), Reusable.YG0d.AR_laws segs B ->
  forall (STK sp0 : Z) (FPj : list (Z * Z)) ly S W mem md (own : list (Z * Z)) lyc Sc Wc
    (memc : word -> option byte) mdc (k : Z) (memc' : word -> option byte) mdc' (WR : list lib.Lib.Frame.ivl),
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
  lib.Lib.Frame.munch WR memc memc' -> lib.Reusable.YK1b.mem_grows memc memc' ->
  (forall x : word, Reusable.YA0n.w_H Wc x = true -> memc' x = memc x) ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a -> sp0 - STK <= a < sp0) ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros B LAWS STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' WR HJ MU Hgr Hhid Hsbm Hwin.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc
    memc mdc k memc' mdc' (fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity|].
    destruct (f5g_outside_dec WR (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    split; [exact R | exact Ho].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *.
    destruct (Reusable.YA0n.w_H Wc x); [exact Hx | exact (Hgr x Hx)].
  - exact Hhid.
  - exact Hsbm.
  - intros a (Ha & Ho). left. exact (Hwin a Ha Ho).
Qed.

End SharedF5J.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Section GlueF5df0.

(* ACtl.v's Section Ctl shape (ACtl.v:170-194), verbatim with the core's twins written lib.Reusable.X. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
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

(* ACtl.v's notation block (ACtl.v:213, :217-218, :268, :272), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81e88_at := (ACtlCutP.C_A81e88_at B).
Local Notation C_A81f54_at := (ACtlCutP.C_A81f54_at B).

Lemma glue_seg_F5_df0 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e88_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A81e88_at, ACtlCutP.v:2037-2046). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81e88_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & Hlen50 & R24 & Hu32 & HID & HF17 &
    HPF).
  (* G2: the run's premises and the bounds, from visible state. *)
  pose proof (A.Prog.Seg.F5.f5_k (ACtlCut.c_in cx) j Hlen50) as Hk0.
  destruct (f5g_frac_base B cx fr fr regs3 mem3 HFRAC) as (Asp & R9 & HAspR).
  destruct (f5g_bounds B MT XM_LIB RLO RHI cx _ ly3 S3 W3 mem3 md3 k fr fr Asp phi j regs3 LAWS HB HJ HFRAC R9 HAspR
              HPerm) as (HAh & HAa & Hfr0 & HfrA & HphiA & HinA & HAlo & HAhi).
  assert (HHBv : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  (* 4096 <= fr: the journal's frame (frames_bounds), the frame law and layout_le's ly_F (A5.v:167-175) *)
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Hfr4096 : 4096 <= fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. exact Hf4096. }
  (* the whole class-6 frame lies below the spill base (f5g_frac_keep's frame premise) *)
  pose proof (f5g_frame_below B cx _ ly3 S3 W3 mem3 md3 k fr fr Asp regs3 LAWS HJ Hin Efr HFRAC R9 HAspR) as Hfr6.
  (* the two spill cells lie in the journal's stack window, which is apresent in mem3 *)
  assert (HSTK : lib.Lib.Frame.stk A.Img0.rsegs mem3 (Asp + 240) (Asp + 288)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(rewrite HSTKv in HAlo; lia)) as [_ (b & Hb)].
    change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a). split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity. }
  assert (Hvis : forall lo, Asp + 240 <= lo -> lo + 8 <= Asp + 288 ->
                   lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo 8).
  { intros lo H1 H2. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (Hpres a ltac:(rewrite HSTKv in HAlo; lia))). }
  rewrite Hk0 in R24.
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81e88_at [Z.of_nat j])) with 0x81e88.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81e88) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run and its lift (it writes memory: SRr_fevt_hid at RNG_W (w_H W3)). *)
  pose proof (@A.Prog.Seg.F5F.seg_F5_df0_run_F
                (A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr) regs3 mem3 Asp
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) R24 R9 HSTK
                (Hvis (Asp + 240) ltac:(lia) ltac:(lia)) (Hvis (Asp + 280) ltac:(lia) ltac:(lia))) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS (A.ProgBridge.fp_avoids_RNG_W _)).
  (* G5: the continuation at the run's end state. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K24 & K22 &
    K25 & K20 & Hmem).
  subst ms' pc'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81f54_at [Z.of_nat j]))
            R mem' md') (POST cx)).
  set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]).
  assert (MU1 : lib.Lib.Frame.munch W mem3 (write_to_mem mem3 (lib.Lib.Mem.wa (Asp + 240)) (lib.Lib.Mem.le8 (Z_to_bv 64 0)))).
  { subst W. apply (lib.Lib.Frame.munch_write _ mem3 mem3 (Asp + 240) (lib.Lib.Mem.le8 (Z_to_bv 64 0)));
      [ apply lib.Lib.Frame.munch_refl | lia | rewrite lib.Lib.Mem.length_le8; lia
      | rewrite lib.Lib.Mem.length_le8; cbn [lib.Lib.Frame.inside]; left; lia ]. }
  assert (MU : lib.Lib.Frame.munch W mem3 mem').
  { rewrite Hmem. apply (lib.Lib.Frame.munch_write _ mem3 _ (Asp + 280) (lib.Lib.Mem.le8 (Z_to_bv 64 0)));
      [ exact MU1 | lia | rewrite lib.Lib.Mem.length_le8; lia
      | subst W; rewrite lib.Lib.Mem.length_le8; cbn [lib.Lib.Frame.inside]; right; left; lia ]. }
  assert (WM : lib.Lib.Frame.wmono A.Img0.rsegs mem3 mem').
  { rewrite Hmem. apply lib.Lib.Frame.wmono_write. apply lib.Lib.Frame.wmono_write. apply lib.Lib.Frame.wmono_refl. }
  assert (Hgr : lib.Reusable.YK1b.mem_grows mem3 mem').
  { rewrite Hmem. exact (lib.Reusable.YK1b.mem_grows_trans _ _ _ (lib.Reusable.YK1b.write_to_mem_grows _ mem3 _)
                           (lib.Reusable.YK1b.write_to_mem_grows _ _ _)). }
  assert (HAW : A.AsanRTFacts.all_app W).
  { subst W. cbn [A.AsanRTFacts.all_app].
    split; [apply A.Prog.Seg.F5.f5_app_ivl; lia | split; [apply A.Prog.Seg.F5.f5_app_ivl; lia | exact I]]. }
  assert (Hlo : forall x, x < Asp + 240 -> lib.Lib.Frame.outside W x)
    by (intros x Hx; subst W; cbn [lib.Lib.Frame.outside]; repeat split; try exact I; lia).
  assert (Hmid : forall x, Asp + 248 <= x < Asp + 280 -> lib.Lib.Frame.outside W x)
    by (intros x Hx; subst W; cbn [lib.Lib.Frame.outside]; repeat split; try exact I; lia).
  assert (Hhi : forall x, Asp + 288 <= x -> lib.Lib.Frame.outside W x)
    by (intros x Hx; subst W; cbn [lib.Lib.Frame.outside]; repeat split; try exact I; lia).
  assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside W a ->
                   ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < ACtlCut.c_sp cx).
  { intros a Ha Hno. rewrite HSTKv in HAlo |- *.
    destruct (Z_lt_le_dec a (Asp + 240)) as [H1|H1]; [exfalso; exact (Hno (Hlo a H1))|].
    destruct (Z_lt_le_dec a (Asp + 288)) as [H2|H2]; [lia | exfalso; exact (Hno (Hhi a H2))]. }
  (* the cells the exit body reads after the stores *)
  assert (Hq280 : ACtlCutP.q64 mem' (Asp + 280) 0).
  { rewrite Hmem. unfold ACtlCutP.q64. apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  assert (Hq240 : ACtlCutP.q64 mem' (Asp + 240) 0).
  { rewrite Hmem. unfold ACtlCutP.q64. apply lib.Lib.Mem.bytes_at_write_other;
      [ apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia] | lia
      | rewrite lib.Lib.Mem.length_le8; lia | rewrite !lib.Lib.Mem.length_le8; lia ]. }
  assert (R9' : ACtlCut.rgv R 9 Asp) by exact (eq_trans K9 R9).
  pose proof (A.Prog.Seg.F5.f5_8819 (ACtlCut.c_in cx) j Hlen50) as H8819f.
  destruct (A.ACtlG.F5_e10.f5g_keep cx j phi fr Asp regs3 R mem3 mem' W HHB HFLSI HLK HC HID R9 HAh HAa HfrA HphiA HinA
              MU WM HAW Hlo Hmid K2 K9 K18 K21 K23) as (HHB' & HFLSI' & HLK' & HC' & HID').
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB).
  - (* journal: the two stores lie in the stack window *)
    exact (f5g_journal B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md' W HJ MU Hgr Hhid Hsbm Hwin).
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax on both cuts *)
    exact Hk.
  - (* the exit body, C_A81f54_at (ACtlCutP.v:2095-2104), at the same index *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f54_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split.
    { exact (f5g_frac_keep B cx fr fr Asp regs3 R mem3 mem' W HFRAC R9 HAh Hfr6 MU Hlo Hhi K2 K3 K4 K8 K9 K19 K26). }
    unfold ACtlCutP.b5_body. exists phi. cbv beta.
    split; [exact HPerm|]. split; [exact Hcn|]. split; [exact Hj255|].
    split; [exact HHB'|]. split; [exact HFLSI'|]. split; [exact HLK'|]. split; [exact HC'|].
    split.
    { (* b5_K on the short arm *)
      unfold ACtlCutP.b5_K.
      rewrite (A.Prog.Seg.F5.f5_sum (ACtlCut.c_in cx) j Hlen50), (A.Prog.Seg.F5.f5_big (ACtlCut.c_in cx) j Hlen50),
        (A.Prog.Seg.F5.f5_tfill (ACtlCut.c_in cx) j Hlen50), Hk0.
      change (A.Prog.SlotModel.b2z false) with 0. change (1 - 0) with 1.
      split; [exact K20|]. split; [exact K22|].
      split; [exact (eq_trans K24 R24)|]. split; [exact K25|].
      split.
      { exists Asp. split; [exact R9'|]. split; [exact HAspR | exact Hq280]. }
      split.
      { rewrite <- Hk0. unfold ACtlCutP.FRAME_BYTES in HfrA.
        exact (A.Prog.Seg.F5.f5_u32_keep W mem3 mem' _ _ Hu32 MU ltac:(intros x Hx; apply Hlo; lia)). }
      apply A.Prog.Seg.F5.f5_reply; [exact (proj1 HHB) | lia]. }
    split; [exact HID'|].
    split.
    { (* b5_F17: [Asp + 200] is below the stores *)
      destruct HF17 as (A7 & H97 & HA7 & Hq7).
      assert (EA7 : A7 = Asp).
      { apply A.Prog.Seg.F5.f5_id; [exact HA7 | exact HAspR |].
        transitivity (lib.Reusable.YK11.getr regs3 9); [symmetry; exact H97 | exact R9]. }
      subst A7.
      exists Asp. split; [exact R9'|]. split; [exact HAspR|].
      exact (A.Prog.Seg.F5.f5_q64_keep W mem3 mem' _ _ Hq7 MU ltac:(intros x Hx; apply Hlo; lia)). }
    split.
    { (* b5_W240: the new [Asp + 240] = 0 with t_8819 j = false *)
      exists Asp. split; [exact R9'|]. split; [exact HAspR|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819f in E; discriminate | intros _; reflexivity]. }
    (* b5_PF: both parts are guarded off on the short arm *)
    exists Asp. split; [exact R9'|]. split; [exact HAspR|].
    split; [intros Hl; exfalso; lia | intros E; rewrite H8819f in E; discriminate].
  - (* ctl_rt_C at the same ly3 S3 (regions kept): every written byte is above HIGHMEM_BEG <= Asp *)
    exact (f5g_ctl_rt_C_keep B ly3 S3 mem3 mem' W Hrt MU WM ltac:(intros x Hx; apply Hlo; lia)).
Qed.

End GlueF5df0.
