(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1114 of its 1252 lines of code are new or changed and 873 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F34.v, with its module paths and module names changed; 702 of its 781 lines of code are new or changed and 1173 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F34.v, with its module paths, module names and numbers changed; 516 of its 625 lines of code are new or changed and 672 lines of the source are left out. *)
(* lib/A/ACtlG/F35.v -- GLUE for stage seg_F35 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v (at head lib/A/ACtl.v:850),
   which carries a Theorem Labs lane's Batch3 (from a working branch d36efc6152d; glue base from a working branch 8ee48574229; an earlier ACtl.v from a working branch 524d38bbd10);
   the statement is unchanged).  Written by a Theorem Labs lane (branch
   a working branch), re-fitted to Batch3 by a Theorem Labs lane; single
   writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (G1-G5, G4's memory-writing lift), the template
   this lane's lib/A/ACtlG/F33.v.
   rule 24: no function proved (stage glue of a walk from an already-proved segment run through the proved bridge).

   WHAT IT PROVES
     glue_seg_F35 : forall POST (j i : nat),
       CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i]) ->
       CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): exactly ACtl.v's Section hypothesis
   seg_F35.  ENTRY C_A82888_at [j; i] (pc 0x82888); EXIT C_A8289c_at [j; i] (pc 0x8289c, the return of the bcmp
   wrapper call).  The second exit C_A828a0_at is not reached: the entry body pins a0 = 1, so `beqz a0` is not taken
   (as Seg/F35.v:657 ignores it).  Segment F35 is 0x82888 -> 0x8289c:
     0x82888 beqz a0,828a0 (not taken)  0x8288c li a2,32  0x82890 mv a0,s6  0x82894 mv a1,s9
     0x82898 jal wrapper_bcmp (returns to 0x8289c with a0 = memcmp_model blk (decl_i i) 32).

   THE RUN: lib/A/Prog/Seg/F35F.v f35_call_F_on (route (C): f35_call_F with its shadow premise narrowed to
   shadow_rw_on (f35_call_F_shadow_R L R) and its callee premise bcmp_wrap_F_at_on RNG), Required qualified, lifted
   WHOLE (a Theorem Labs lane: no split at the wrapper).  Its callee premise is discharged by
   `proj1 F35F.F35BWO.bcmp_wrap_F_at_on_owner bcmp_wrap_on.bcmp_wrap_holds_F_on RNG` (bcmp_wrap_holds_F_on is PROVED,
   lib/A/Prog/bcmp_wrap_on.v, a Theorem Labs lane).  The run WRITES memory (the wrapper's stack window [sp - 4560, sp)).

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j; Z.of_nat i]: ix_cut's index equation, then C_A82888_at's conjuncts (phi, the
       live list, FRAC, c_n, j <= 255, HB, FLSI, LK, i <= 10, RL, a0 = 1, the row slot bytes decl_i i at fr + 64 and
       their addressability, LT); ixn 0 / ixn 1 of [Z.of_nat j; Z.of_nat i] are j / i (Nat2Z.id).
   G2  the run's premises.  Registers: a0 = 1 (body), s6 = phi + 18 (FLSX's x22 at t_big = true, from RL's t_rowsel
       through Seg/F35.v's f35_rowsel_big), s9 = fr + 64 (FLSX's x25), sp = spZ regs3 (FRAC).  The block (phi, flen):
       In ablocks by the body's Permutation, then AR_blocks_law (YG0d.al_blocks): 4096 <= phi, phi + flen <=
       alloc_ceiling, in_app.  The frame: YCbq.frames_bounds at fr = frame_addr ly3 6 (c_fpos cx) (F33's Efa).  The
       stack window: the journal's 14th conjunct (apresent on [c_sp - 32768, c_sp)) and its 15th (astk_ok:
       alloc_ceiling + 32768 <= c_sp), with FRAC's c_sp - 4096 < sp <= A, A + 416 <= c_sp: [sp - 4560, sp) lies in
       the engine stack and above alloc_ceiling, so above every block / frame byte and every shadow byte of them.
       Bytes: the block's 32 bytes at phi + 18 from FLSX's guarded part (f35_ba_sub), the row slot from the body;
       memcmp_model_total, f35_mm_spec.  ctl_rt_C gives asan_cells / ro_agree and (route (C)) the wrapper's shadow
       region sh_word_on (phi + 18) 32 \/ sh_word_on (fr + 64) 32 from its cut_shadow conjunct (the block's (L)
       disjunct, the owned frame's (F) disjunct); RT_OF_CORE (below: a Theorem Labs lane's PROVED
       A.ProgWorldRtC.rt_of_core_C) gives the REAL_BCMP / REAL_MEMCMP slots (its REAL_USED Forall) and GOT_CF /
       CF + 254 / CF + 255 (asan_cf_cells).
       Footprint at RNG := ProgBridge.RNG_W (w_H W3): rng_bytes_RNG_W; the image by img_vis_W; the window from the
       journal's apresent bytes; the 32 block bytes and their shadow words by a Theorem Labs lane's ProgWorldVisHeap
       heap_vis / heap_sh_vis; the 32 row-slot bytes and their shadow words by ProgWorldVisFrame.frame_vis.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt_hid (the memory-writing lift; its continuation keeps every hidden
       byte) at RNG_W (w_H W3); fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the run's end state is MS R .. 0x8289c .. mem' with R the run's explicit map (x10 = memcmp result; x2 x3 x4 x8
       x9 x18-x27 are regs3's): the exit cut C_A8289c_at [j; i] is taken there.  Journal: YCbq.ajournal_exec with
       Wr := [spZ regs3 - 4560, spZ regs3) (munch; mem_grows from munch and the post's stk; the hidden bytes from
       SRr_fevt_hid; same_but_materialized; awr_byte's stack case).  frames / frame law / k bound unchanged (own6, the
       same kmax 14 + 2 j + 1 on both cuts).  Body: every memory conjunct is moved across the write by the f35_*_keep
       transports below with the kept set Kp x := ~ (spZ regs3 - 4560 <= x < spZ regs3); every address they read is
       either below alloc_ceiling (block, input block, frame, the shadow of all three) or at or above sp (spills,
       saved registers).  Registers through Kit.kit_frac_move and the kept x9 x18 x20-x25.  The memcmp result:
       f35_lit0, f35_mm_spec, f35_blk (Seg/F35.v's reasoning).  ctl_rt_C (same ly3 S3): asan_cells by
       AsanRTFacts.asan_cells_kept (the window is above [RT_LO, RT_HI)), both shadow regions by the kept set (the
       shadow is below the window), ro_agree from the run's post.

   SECTION HYPOTHESES (ACtl.v's Section Ctl, ACtl.v:183-238, restricted to what this stage uses, in its order):
     LAWS       : Reusable.YG0d.AR_laws segs B       (ACtl.v:210; ajournal_exec, frames_bounds, al_blocks, the
                                                      ProgWorldVis lemmas take it)
     TFIB_SYMS  : A.AF0m.CtrlTSyms B                  (ACtl.v:225; RT_OF_CORE takes it)
   RT_OF_CORE is no longer a Section hypothesis: it is the local notation for A.ProgWorldRtC.rt_of_core_C B MT XM_LIB
   RLO RHI [] (lib/A/ProgWorldRtC.v:76, a Theorem Labs lane, route (C)'s form of A.ProgWorldRt.rt_of_core: premise ctl_rt_C,
   conclusion RT_used_C, whose destruct is one slot longer than RT_used's).

   LOCAL HELPERS, KIT CANDIDATES (general in the kept set Kp; the F34 glue needs the same ones; their exact
   statements go to the kit's writer a Theorem Labs lane through the lane owner): f35_bytes_keep, f35_addr_keep,
   f35_stk_keep, f35_spill_keep, f35_frac_keep, f35_flsi_keep, f35_flsx_keep, f35_lk_keep, f35_lt_keep.  Image
   facts used once: f35_sh_low, f35_mrd_high, f35_hull.

   FRAC AND BATCH3'S TRAILER WORD.  This stage PRODUCES FRAC at its exit C_A8289c_at [j; i] at the run's new memory
   mem', and since Batch3 (a Theorem Labs lane, d36efc6152d) FRAC's last conjunct is the fake-frame trailer word
   `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))` (ACtlCutP.v:997).  FRAC's text is not restated:
   f35_frac_keep moves FRAC's memory conjuncts by a tactic over FRAC's own unfolding (every q64 conjunct inside the
   frame [fr, fr + 4096) or at or above spZ; no conjunct is counted), so it proves the trailer word with no edit: its
   bytes [fr + 4088, fr + 4096) lie in the frame, which the kept set Kp holds (the run writes only the wrapper's
   window [sp - 4560, sp), above alloc_ceiling and so above the frame; the frame LLVMFuzzerTestOneInput writes is
   [fr, fr + 3136), and 3136 < 4088).  The positional read of FRAC is this file's G2 destruct of its first 17
   conjuncts (registers and bounds), which ends in `& _` and so does not count the trailer word.

   CLOSURE (glue closure rule): every project Require below names its FULL directory in the From clause; no
   statement names a frame-route identifier.  The closure reaches the frame route only through Seg/F35F.v ->
   Seg/F35.v (SlotInv, AsanRTInv, Contract, FrameAPI, MemNorm, ...), as closure rule 1 allows.  A.ProgWorld /
   A.ProgWorldRt (for RT_OF_CORE) Require lib/Lib's Mem by its full directory (a Theorem Labs lane's fec8db0a380 form), the
   copy L_Mem names.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are YK11 / YG0d-qualified everywhere; YK11, YK1b, YM05, YO09 (in
   both lib/Reusable and lib/A/Reusable) are named by their FULL path; the lib/Lib modules (15 of which also exist
   under lib/A/Bz/Lib, lib/AZ/Lib, lib/B/Bz/Lib) by full-path module aliases L_*.

   BUILD STATE (2026-10-29): TYPE-CHECK ON INTERIM 5da74c9c931, CLOSURE REACHES NO STAND-IN, not acceptance.  The
   glue base a working branch 121bf608343 carries a Theorem Labs lane's stand-in-free 29ddfc3ea99 (a Theorem Labs lane's interim core
   5da74c9c931 + Batch3 + a Theorem Labs lane's ProgWorld files): the closure's lib/A/AE2k.v (Required here for the sink head),
   lib/A/AF0m.v (Required here for CtrlTSyms) and lib/A/AF0l.v hold no port_core_refused name, and the build
   substitutes nothing.  F35.vo compiles from a fresh clone through cb (BASE 23b918fe0c2e; the lane report
   names the commit, log and .vo mtime); Print Assumptions glue_seg_F35 = Rocq primitives +
   functional_extensionality_dep (LAWS and TFIB_SYMS are its Section-hypothesis arguments).  No Axiom, no Parameter,
   no Admitted.  The Batch3 re-fit itself type-checked first on 8ee48574229 with the stand-ins. *)

From Coq Require Import ZArith List Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG00 YG01 YG0d YG0n YC5d YCbq YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k AF0m ACfn Img0 ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRT AsanRTFacts ProgBridge ProgWorldVisFrame ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorldRt.
(* route (C): the narrowed cut conjunct, rt_of_core_C, and the wrapper's shadow-word region. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on A.Prog.bcmp_wrap_c_on A.Prog.bcmp_wrap_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F35 F35F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame PropExec RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* lib/Lib and the pure model by full-path aliases (a partial Lib.X can bind lib/A/Bz/Lib/X). *)
Module L_Mem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module L_Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module L_ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module L_MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module L_Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module L_PropExec := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module SlM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Memory transports across a write, general in the kept set Kp: a byte x with Kp x is unchanged
   (m' (wa x) = m (wa x)), and each lemma asks Kp of every address its predicate reads. *)

Lemma f35_bytes_keep : forall (Kp : Z -> Prop) (m m' : word -> option byte) (a : Z) (bs : list byte),
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> Kp x) ->
  L_Mem.bytes_at segs m a bs -> L_Mem.bytes_at segs m' a bs.
Proof.
  intros Kp m m' a bs HK HR (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold L_Mem.mrd.
  rewrite (HK (a + Z.of_nat i)); [reflexivity | lia | apply HR; lia].
Qed.

(* addressable reads the shadow byte of each of its bytes. *)
Lemma f35_addr_keep : forall (Kp : Z -> Prop) (m m' : word -> option byte) (p n : Z),
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, p <= x < p + n -> Kp (A.AsanRT.shadow_addr x)) ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros Kp m m' p n HK HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hs). split; [exact Ha|]. exists b. split; [|exact Hs].
  rewrite <- Hb. unfold L_Mem.mrd.
  rewrite (HK (A.AsanRT.shadow_addr (p + i))); [reflexivity | | apply HR; lia].
  unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. unfold A.AsanRT.APPMEM_END in H2.
  change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* Lib.Frame.stk reads the writable view and the byte of each address. *)
Lemma f35_stk_keep : forall (Kp : Z -> Prop) (m m' : word -> option byte) (lo hi : Z),
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, lo <= x < hi -> Kp x) ->
  L_Frame.stk segs m lo hi -> L_Frame.stk segs m' lo hi.
Proof.
  intros Kp m m' lo hi HK HR (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb).
  assert (E : m' (L_Mem.wa a) = m (L_Mem.wa a)) by (apply HK; [lia | apply HR; lia]).
  split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b. unfold L_Mem.mrd in *. rewrite E. exact Hb.
Qed.

(* A spill read at the spill base Ab (pinned by x9), x9 kept. *)
Lemma f35_spill_keep : forall (Kp : Z -> Prop) (regs regs' : bvmap 5 word) (m m' : word -> option byte) (off v Ab : Z),
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab -> Ab + 312 <= 2 ^ 64 -> 0 <= off <= 304 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, Ab <= x < Ab + 312 -> Kp x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros Kp regs regs' m m' off v Ab HA H0 H1 Hoff E HK HR (Ab' & HA' & Hq).
  assert (EA : Ab' = Ab).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite L_Mem.length_le8 in Hq1.
    unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
    apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
    change (bv_modulus 64) with 18446744073709551616 in HA'.
    change (2 ^ 64) with 18446744073709551616 in H1, Hq1.
    rewrite (Z.mod_small Ab) in HA' by lia.
    Z.div_mod_to_equations. lia. }
  subst Ab'. exists Ab. split.
  - unfold ACtlCut.rgv in *. rewrite E. exact HA.
  - unfold ACtlCutP.q64 in *. apply (f35_bytes_keep Kp m m' _ _ HK); [|exact Hq].
    rewrite L_Mem.length_le8. intros x Hx. apply HR. lia.
Qed.

(* FRAC's memory part (ACtlCutP.v FRAC) across a write that keeps the frame [fr, fr + 4096), the frame's shadow
   bytes and [spZ regs, c_sp cx) (the spill area A + 16 .. A + 312 and the saved registers at c_sp - 104).  The
   proof does not count FRAC's conjuncts: it moves every q64 / bytes conjunct whatever their number. *)
Lemma f35_frac_keep : forall (B : Reusable.YG0f.asyms) (Kp : Z -> Prop) (cx : ACtlCut.ctlcx) (fr sel : Z)
    (regs : bvmap 5 word) (m m' : word -> option byte),
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, fr <= x < fr + 4096 -> Kp x) ->
  (forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> Kp x) ->
  (forall x, Reusable.YG0d.spZ regs <= x < ACtlCut.c_sp cx -> Kp x) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros B Kp cx fr sel regs m m' HK HRF HRS HRP H.
  unfold ACtlCutP.FRAC in *.
  destruct H as (Ab & sp & H). exists Ab, sp.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold ACtlCutP.FRAME_BYTES in *.
  (* move every memory conjunct of the hypothesis to m', then the goal is the hypothesis' conjuncts *)
  repeat match goal with
  | Hq : ACtlCutP.q64 m ?a ?v |- _ =>
      let Hq' := fresh "Hq" in
      assert (Hq' : ACtlCutP.q64 m' a v)
        by (apply (f35_bytes_keep Kp m m' a _ HK); [ | exact Hq ];
            rewrite L_Mem.length_le8; intros x Hx; first [ apply HRF; lia | apply HRP; lia ]);
      clear Hq
  | Hb : L_Mem.bytes_at _ m ?a ?bs |- _ =>
      let Hb' := fresh "Hb" in
      assert (Hb' : L_Mem.bytes_at segs m' a bs)
        by (apply (f35_bytes_keep Kp m m' a bs HK); [ | exact Hb ];
            unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?L_Mem.length_le8; intros x Hx; apply HRP; lia);
      clear Hb
  | Hs : exists sh, L_Mem.bytes_at _ m _ sh /\ _ |- _ =>
      let sh := fresh "sh" in let Hb := fresh "Hb" in let Hl := fresh "Hl" in
      destruct Hs as (sh & Hb & Hl);
      assert (exists sh0, L_Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh0 /\
                          length sh0 = Z.to_nat ACtlCutP.FRAME_SHADOW)
        by (exists sh; split; [ | exact Hl ];
            apply (f35_bytes_keep Kp m m' _ _ HK); [ | exact Hb ];
            rewrite Hl; change ACtlCutP.FRAME_SHADOW with 392 in HRS |- *;
            change (Z.of_nat (Z.to_nat 392)) with 392; exact HRS);
      clear Hb
  end.
  repeat match goal with |- _ /\ _ => split end.
  all: assumption.
Qed.

(* FLSI (ACtlCutP.v FLSI = FLSH + spills + f1_IN + FLC): spills at the base Ab (x9 kept), the frame's stk range and
   its in-frame addressable ranges, the input block's bytes and their shadow. *)
Lemma f35_flsi_keep : forall (Kp : Z -> Prop) (cx : ACtlCut.ctlcx) (j : nat) (fr : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (Ab : Z),
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab -> Ab + 312 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, Ab <= x < Ab + 312 -> Kp x) ->
  (forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> Kp x) ->
  (forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> Kp (A.AsanRT.shadow_addr x)) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> Kp x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> Kp (A.AsanRT.shadow_addr x)) ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros Kp cx j fr regs regs' m m' Ab HA H0 H1 E9 HK HRA HRF HRFS HRI HRIS
    (((S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248p & A2624 & BIN & AIN & S184 & S256 & S264 & S272 & S32)
      & S128 & STK & S144 & A2691)
     & S216 & S224 & S248 & (AIN' & BIN') &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & AFG & A2688 & C72 & C64 & C56 & C48)).
  pose proof (fun off v (Hoff : 0 <= off <= 304) =>
    f35_spill_keep Kp regs regs' m m' off v Ab HA H0 H1 Hoff E9 HK HRA) as T.
  assert (TA : forall p n, fr <= p -> p + n <= fr + ACtlCutP.FRAME_BYTES ->
                 A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n Hp Hn Ha. apply (f35_addr_keep Kp m m' p n HK); [|exact Ha].
    intros x Hx. apply HRFS. lia. }
  assert (BIN2 : L_Mem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx))
    by exact (f35_bytes_keep Kp m m' _ _ HK HRI BIN).
  assert (AIN2 : A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx))
    by exact (f35_addr_keep Kp m m' _ _ HK HRIS AIN').
  assert (STK2 : L_Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES))
    by exact (f35_stk_keep Kp m m' _ _ HK HRF STK).
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.f1_IN.
  split.
  { split.
    { split; [exact (T 40 _ ltac:(lia) S40)|]. split; [exact (T 120 _ ltac:(lia) S120)|].
      split; [exact (T 136 _ ltac:(lia) S136)|]. split; [exact (T 160 _ ltac:(lia) S160)|].
      split; [exact (T 168 _ ltac:(lia) S168)|]. split; [exact (T 176 _ ltac:(lia) S176)|].
      split; [exact (T 208 _ ltac:(lia) S208)|]. split; [exact (T 248 _ ltac:(lia) S248p)|].
      split; [apply TA; [lia | unfold ACtlCutP.FRAME_BYTES; lia | exact A2624]|].
      split; [exact BIN2|].
      split; [intros _; exact AIN2|].
      split; [exact (T 184 _ ltac:(lia) S184)|]. split; [exact (T 256 _ ltac:(lia) S256)|].
      split; [exact (T 264 _ ltac:(lia) S264)|].
      split; [exact (T 272 _ ltac:(lia) S272) | exact (T 32 _ ltac:(lia) S32)]. }
    split; [exact (T 128 _ ltac:(lia) S128)|]. split; [exact STK2|].
    split; [exact (T 144 _ ltac:(lia) S144) | apply TA; [lia | unfold ACtlCutP.FRAME_BYTES; lia | exact A2691]]. }
  split; [exact (T 216 _ ltac:(lia) S216)|]. split; [exact (T 224 _ ltac:(lia) S224)|].
  split; [exact (T 248 _ ltac:(lia) S248)|]. split; [split; [exact AIN2 | exact BIN2]|].
  split; [exact (T 256 _ ltac:(lia) C256)|]. split; [exact (T 184 _ ltac:(lia) C184)|].
  split; [exact (T 192 _ ltac:(lia) C192)|]. split; [exact (T 80 _ ltac:(lia) C80)|].
  split; [exact (T 88 _ ltac:(lia) C88)|]. split; [exact (T 96 _ ltac:(lia) C96)|].
  split; [exact (T 272 _ ltac:(lia) C272)|]. split; [exact (T 264 _ ltac:(lia) C264)|].
  split; [apply TA; [unfold ACtlCutP.fragb; lia | unfold ACtlCutP.fragb, ACtlCutP.FRAME_BYTES; lia | exact AFG]|].
  split; [apply TA; [lia | unfold ACtlCutP.FRAME_BYTES; lia | exact A2688]|].
  split; [exact (T 72 _ ltac:(lia) C72)|]. split; [exact (T 64 _ ltac:(lia) C64)|].
  split; [exact (T 56 _ ltac:(lia) C56) | exact (T 48 _ ltac:(lia) C48)].
Qed.

(* FLSX (ACtlCutP.v FLSX): FLSI at the new state, x18 x22 x23 x25 kept, the block's bytes [phi, phi + flen) kept,
   two spills. *)
Lemma f35_flsx_keep : forall (Kp : Z -> Prop) (cx : ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (Ab : Z),
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab -> Ab + 312 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25 ->
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, Ab <= x < Ab + 312 -> Kp x) ->
  (forall x, phi <= x < phi + ACtlCutP.flen cx j -> Kp x) ->
  ACtlCutP.FLSI cx j fr regs' m' -> ACtlCutP.FLSX cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs' m'.
Proof.
  intros Kp cx j phi fr regs regs' m m' Ab HA H0 H1 E9 E18 E22 E23 E25 HK HRA HRp HI'
    (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  unfold ACtlCutP.FLSX.
  split; [exact HI'|].
  split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
  split; [unfold ACtlCut.rgv in *; rewrite E22; exact H22|].
  split; [unfold ACtlCut.rgv in *; rewrite E23; exact H23|].
  split; [unfold ACtlCut.rgv in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hph & Hpl).
    assert (Lg : length (SlM.t_g (ACtlCut.c_in cx) j) = 50%nat).
    { unfold SlM.t_g, SlM.fr50. rewrite length_firstn, length_app, repeat_length. lia. }
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [apply (f35_bytes_keep Kp m m' _ _ HK); [rewrite Lg; intros x Hx; apply HRp; lia | exact Hg]|].
    split; [apply (f35_bytes_keep Kp m m' _ _ HK); [intros x Hx; apply HRp; lia | exact Hph]|].
    exact Hpl. }
  split; [exact (f35_spill_keep Kp regs regs' m m' 152 _ Ab HA H0 H1 ltac:(lia) E9 HK HRA H152)|].
  exact (f35_spill_keep Kp regs regs' m m' 280 _ Ab HA H0 H1 ltac:(lia) E9 HK HRA H280).
Qed.

(* LK (ACtlCutP.v LK): x21 kept, the 6 OUR bytes at fr + 2624 kept. *)
Lemma f35_lk_keep : forall (Kp : Z -> Prop) (cx : ACtlCut.ctlcx) (fr : Z) (j : nat) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 ->
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> Kp x) ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros Kp cx fr j regs regs' m m' E21 HK HR (Hj & H21 & HO).
  split; [exact Hj|]. split; [unfold ACtlCut.rgv in *; rewrite E21; exact H21|].
  unfold ACtlCutP.OURb in *. apply (f35_bytes_keep Kp m m' _ _ HK); [|exact HO].
  unfold SlM.OUR. rewrite length_map, length_seq. intros x Hx. apply HR. lia.
Qed.

(* LT (ACtlCutP.v LT = IFS at S j): the identity record at fr + 2688, the fragment state at fr + 2768, the FIRST
   fragment body at fr + 2880 and its 35 addressable bytes, two spills. *)
Lemma f35_lt_keep : forall (Kp : Z -> Prop) (cx : ACtlCut.ctlcx) (fr : Z) (j : nat) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (Ab : Z),
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab -> Ab + 312 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  (forall x, 0 <= x < 2 ^ 64 -> Kp x -> m' (L_Mem.wa x) = m (L_Mem.wa x)) ->
  (forall x, Ab <= x < Ab + 312 -> Kp x) ->
  (forall x, fr + 2688 <= x < fr + 2688 + Z.of_nat (length (SlM.t_ID (ACtlCut.c_in cx) (S j))) -> Kp x) ->
  (forall x, fr + 2768 <= x < fr + 2768 + Z.of_nat (length (SlM.t_FG (ACtlCut.c_in cx) (S j))) -> Kp x) ->
  (forall x, fr + 2880 <= x < fr + 2880 + Z.of_nat (length (SlM.fs_body (SlM.fst_at (ACtlCut.c_in cx) (S j)))) -> Kp x) ->
  (forall x, fr + 2880 <= x < fr + 2880 + 35 -> Kp (A.AsanRT.shadow_addr x)) ->
  ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros Kp cx fr j regs regs' m m' Ab HA H0 H1 E9 HK HRA HRID HRFG HRB HRBS
    ((HID & Hidok) & (HFG & Hfgok) & (Q104 & Q112 & Qbody & Qad & HFI)).
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.FGj, ACtlCutP.IDb, ACtlCutP.FGb, ACtlCutP.FSj,
    ACtlCutP.FSb, ACtlCutP.IDBe, ACtlCutP.FGBe in *.
  split; [split; [exact (f35_bytes_keep Kp m m' _ _ HK HRID HID) | exact Hidok]|].
  split; [split; [exact (f35_bytes_keep Kp m m' _ _ HK HRFG HFG) | exact Hfgok]|].
  split; [exact (f35_spill_keep Kp regs regs' m m' 104 _ Ab HA H0 H1 ltac:(lia) E9 HK HRA Q104)|].
  split; [exact (f35_spill_keep Kp regs regs' m m' 112 _ Ab HA H0 H1 ltac:(lia) E9 HK HRA Q112)|].
  split; [exact (f35_bytes_keep Kp m m' _ _ HK HRB Qbody)|].
  split; [exact (f35_addr_keep Kp m m' _ _ HK HRBS Qad) | exact HFI].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. Image facts used once. *)

(* The shadow byte of an application byte below APPMEM_END = 2^47 lies below HIGHMEM_BEG. *)
Lemma f35_sh_low : forall y, 0 <= y < 0x800000000000 -> A.AsanRT.shadow_addr y < 0x10007fff8000.
Proof. intros y Hy. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* No segment of the image reaches 0x5fe000 (Seg/F35F.v's f35_find_below / f35_rsegs_top), so a byte read there is
   a memory byte. *)
Lemma f35_mrd_high : forall (m : word -> option byte) (x : word) (b : byte),
  0x5fe000 <= bv_unsigned x -> L_Mem.mrd A.Img0.rsegs m x = Some b -> m x = Some b.
Proof.
  intros m x b Hx H. unfold L_Mem.mrd in H. destruct (m x) as [b'|]; [exact H|].
  exfalso. revert H.
  cbv beta delta [L_PropExec.seg_rom OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom].
  unfold memory_read. try change (Z.of_N 1) with 1.
  destruct (find_segment A.Img0.rsegs (bv_unsigned x) 1) as [s|] eqn:F.
  - destruct (A.Prog.Seg.F35F.f35_find_below A.Img0.rsegs 0x5fe000 (bv_unsigned x) 1 s
                A.Prog.Seg.F35F.f35_rsegs_top F ltac:(lia)) as [Hl|Hl]; intros _; lia.
  - intros Hc. discriminate Hc.
Qed.

(* The 64-byte hull of the row slot [fr + 64, fr + 96) lies in the 4096-byte frame (fr mod 32 = 0). *)
Lemma f35_hull : forall fr, fr mod 32 = 0 ->
  fr <= 64 * ((fr + 64) / 64) /\ 64 * ((fr + 64 + 32 - 1) / 64) + 64 <= fr + 4096.
Proof. intros fr H. Z.div_mod_to_equations. lia. Qed.

Section GlueF35.

(* ACtl.v's Section shape (ACtl.v:183-238), restricted to what this stage uses, in ACtl.v's order. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The core's AR laws (ACtl.v:210; YCbq Section a0's hypothesis, YCbq.v:207). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The core's symbol facts for B (ACtl.v:225); RT_OF_CORE takes them. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* RT_OF_CORE: a Theorem Labs lane's PROVED A.ProgWorldRtC.rt_of_core_C (lib/A/ProgWorldRtC.v:76), route (C)'s form of
   a Theorem Labs lane's A.ProgWorldRt.rt_of_core: its premise is the cut's ctl_rt_C and its conclusion RT_used_C (one slot
   longer than RT_used: two shadow conjuncts).  Here at FP := [] (the walk's), cited by name.  Used once, at the entry
   cut, with ms3 := MS regs3 fp_regs 0 fp_csr None mem3 (seg_rom segs). *)
Local Notation RT_OF_CORE := (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI []).

(* ACtl.v's notation block (ACtl.v:257, :261-262, :351-353), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82888_at := (ACtlCutP.C_A82888_at B).
Local Notation C_A8289c_at := (ACtlCutP.C_A8289c_at B).
Local Notation C_A828a0_at := (ACtlCutP.C_A828a0_at B).

(* An In fact over a concrete list of literals. *)
Local Ltac f35_in := repeat (first [left; reflexivity | right]).

Lemma glue_seg_F35 : forall POST (j i : nat),
  CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i HX _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBASE HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j; i] (ix_cut, ACtlCut.v:234-236; C_A82888_at, ACtlCutP.v:2818-2835). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82888_at ACtlCutP.ixn nth] in Hb.
  rewrite !Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & Hi10 & HRL & R10 & Hrow & Hadr & HLT).
  pose proof HRL as (_ & _ & _ & _ & Hsel & HFLSX).
  pose proof HFLSX as (_ & _ & R22 & _ & R25 & Hrec & _ & _).
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* G2 (a): the core's facts at the cut.  The journal's AR, layout, apresent window (14th) and astk_ok (15th). *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HASTK & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct HASTK as (_ & _ & Hstklo & Hstkhi & _).
  unfold A.ACfn.LLVMF_STK in HPRES, Hstkhi.
  pose proof Reusable.YCbq.asan_consts as (HCE & _).
  pose proof Reusable.YG0f.ASAN_CEIL_range as (HCE2 & _).
  (* FRAC's registers and bounds (its first 17 conjuncts). *)
  pose proof HFRAC as (Asp & spv & F2 & Fsp16 & Fspz & F4 & F8 & F9 & F3 & F19 & F26 & Ffr32 & FA32 & FAc & FspA &
    FfrA & FA416 & Fcsp & FcspE & _).
  subst spv.
  unfold ACtlCutP.FRAME_BYTES in FfrA. unfold A.AsanRT.APPMEM_END in FcspE.
  (* the frame: frame_addr ly3 6 (c_fpos cx) = fr (F33's Efa), and YCbq.frames_bounds *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr.
    first [ rewrite EF; reflexivity | rewrite <- EF; reflexivity ]. }
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr0 & Hfr1 & Hfrapp).
  rewrite Efa in Hfr0, Hfr1, Hfrapp. rewrite E4096 in Hfr1, Hfrapp.
  (* the row path's frame is big (t_rowsel needs kind 9, Seg/F35.v's f35_rowsel_big) *)
  assert (Hbig' : 50 <= SlM.t_len (ACtlCut.c_in cx) j) by exact (A.Prog.Seg.F35.f35_rowsel_big _ _ Hsel).
  assert (Hbig : 50 <= ACtlCutP.flen cx j) by exact Hbig'.
  assert (Hasz : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j) by (unfold A.ACtlK.a_size; lia).
  (* the block (phi, flen): In the cut's ablocks by the body's Permutation, then AR_blocks_law *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinphi)
    as (Hph16 & Hph4096 & Hphce & Hphapp & _).
  assert (Erq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq (ACtlCutP.flen cx j) 0) ltac:(lia)). reflexivity. }
  rewrite Erq in Hphce, Hphapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hphapp, Hfrapp.
  (* the input block (c_p, c_n): below alloc_ceiling when non-empty (the lib pre's In, carried by the Permutation) *)
  pose proof HBASE as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
  assert (HinB : 0 < ACtlCut.c_n cx ->
                 4096 <= ACtlCut.c_p cx /\ ACtlCut.c_p cx + ACtlCut.c_n cx < Reusable.YG0d.spZ regs3 - 4560).
  { intros Hn0. destruct Hpn as [(En & _) | (_ & Hinb)]; [lia|].
    assert (Hin' : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. exact Hinb. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin') as (_ & H4 & Hce & _).
    unfold Reusable.YG00.req_size in Hce.
    rewrite (proj2 (Z.eqb_neq (ACtlCut.c_n cx) 0) ltac:(lia)) in Hce. cbv beta iota in Hce. lia. }
  (* the window [spZ regs3 - 4560, spZ regs3) is above alloc_ceiling and inside the engine stack *)
  assert (Hwin : 0x7fff7f800000 + 20000 < Reusable.YG0d.spZ regs3 - 4560) by lia.
  (* G2 (b): the run's premises. *)
  assert (Htb : SlM.t_big (ACtlCut.c_in cx) j = true) by (unfold SlM.t_big; apply Z.leb_le; exact Hbig').
  assert (R22' : ACtlCut.rgv regs3 22 (phi + 18)) by (rewrite Htb in R22; exact R22).
  destruct (Hrec Hbig) as (_ & _ & _ & Hphi & _).
  assert (Hls : length (firstn 32 (skipn 18 (SlM.t_phi (ACtlCut.c_in cx) j))) = 32%nat)
    by (rewrite length_firstn, length_skipn, A.Prog.Seg.F35.f35_phi_length; lia).
  assert (Hrs : length (SlM.decl_i (Z.of_nat i)) = 32%nat) by (apply A.Prog.Seg.F35.f35_decl_len; lia).
  assert (HLb : L_Mem.bytes_at A.Img0.rsegs mem3 (phi + 18) (firstn 32 (skipn 18 (SlM.t_phi (ACtlCut.c_in cx) j)))).
  { change (phi + 18) with (phi + Z.of_nat 18).
    apply A.Prog.Seg.F35.f35_ba_sub; [exact Hphi | rewrite A.Prog.Seg.F35.f35_phi_length; lia]. }
  destruct (A.Spec.StrFun.memcmp_model_total (firstn 32 (skipn 18 (SlM.t_phi (ACtlCut.c_in cx) j)))
              (SlM.decl_i (Z.of_nat i)) 32 ltac:(lia) ltac:(lia)) as (v & Hv).
  destruct (A.Prog.Seg.F35.f35_mm_spec 32 _ _ v Hls Hrs Hv) as [Hiff Hvr].
  pose proof Hrt as (HAC & Hcut & Himg & HRO).
  (* route (C): the bcmp wrapper's shadow region, sh_word_on (phi + 18) 32 \/ sh_word_on (fr + 64) 32
     (bcmp_wrap_shadow_R L R 32 at L = phi + 18, R = fr + 64), lies in the cut's cut_shadow: the block's words in its
     (L) disjunct (phi + 18 + 32 <= phi + flen, flen >= 50), the row slot's words in the owned frame's (F) disjunct. *)
  assert (Esa : forall x, Reusable.YG0f.shadow_addr x = A.AsanRT.shadow_addr x).
  { intros x. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    lia. }
  assert (Hal8 : forall x y, x <= y -> A.AsanRT.shadow_addr x / 8 * 8 <= A.AsanRT.shadow_addr y / 8 * 8).
  { intros x y Hxy. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    unfold A.AsanRT.shadow_addr. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  assert (HregL : forall a, A.Prog.sh_word_on.sh_word_on (phi + 18) 32 a -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a (_ & Ha1 & Ha2). right; left. exists phi, (ACtlCutP.flen cx j). split; [exact Hinphi|].
    rewrite Erq, !Esa. unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha1, Ha2.
    pose proof (Hal8 phi (phi + 18) ltac:(lia)) as H1.
    pose proof (Hal8 (phi + 18 + 32 - 1) (phi + ACtlCutP.flen cx j - 1) ltac:(lia)) as H2.
    lia. }
  assert (HregR : forall a, A.Prog.sh_word_on.sh_word_on (fr + 64) 32 a -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a (_ & Ha1 & Ha2). left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efa, E4096, !Esa. change (4096 / 8) with 512.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha1, Ha2.
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha1, Ha2 |- *.
    Z.div_mod_to_equations; lia. }
  assert (HSWon : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.F35F.f35_call_F_shadow_R (phi + 18) (fr + 64)) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
    unfold A.Prog.Seg.F35F.f35_call_F_shadow_R, A.Prog.Seg.F35F.f35_evt_F_shadow_R,
      A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R.
    intros a [Ha|Ha]; [exact (HregL a Ha) | exact (HregR a Ha)]. }
  assert (HadL : A.AsanRT.addressable mem3 (phi + 18) 32)
    by exact (A.AsanRTFacts.addressable_sub mem3 phi _ 18 32 (proj2 HHB) ltac:(lia) ltac:(lia)
                ltac:(rewrite Hasz; lia)).
  assert (HaL32 : A.AsanRT.app_mem (phi + 18 + 32)).
  { unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HaL7 : A.AsanRT.app_mem (phi + 18 + 7)).
  { unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HaR32 : A.AsanRT.app_mem (fr + 64 + 32)).
  { unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HaR7 : A.AsanRT.app_mem (fr + 64 + 7)).
  { unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HdjL : phi + 18 + 32 <= Reusable.YG0d.spZ regs3 - 4560 \/ Reusable.YG0d.spZ regs3 <= phi + 18)
    by (left; lia).
  assert (HdjR : fr + 64 + 32 <= Reusable.YG0d.spZ regs3 - 4560 \/ Reusable.YG0d.spZ regs3 <= fr + 64)
    by (left; lia).
  assert (HST : L_Frame.stk A.Img0.rsegs mem3 (Reusable.YG0d.spZ regs3 - 4560) (Reusable.YG0d.spZ regs3)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (HPRES a ltac:(lia)) as (_ & b & Hb).
    split.
    - unfold wview. change (L_Mem.wa a) with (Z_to_bv 64 a). rewrite Hb. discriminate.
    - exists b. unfold L_Mem.mrd. change (L_Mem.wa a) with (Z_to_bv 64 a). rewrite Hb. reflexivity. }
  assert (HloK : Reusable.YG0d.spZ regs3 - 4560 + 4560 <= Reusable.YG0d.spZ regs3) by lia.
  assert (HloH : A.AsanRT.HIGHMEM_BEG <= Reusable.YG0d.spZ regs3 - 4560)
    by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HspA : Reusable.YG0d.spZ regs3 <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  (* the runtime cells, from RT_OF_CORE (A.ProgWorldRtC.rt_of_core_C) at the cut, fed the cut's ctl_rt_C; its
     RT_used_C conclusion destructs as the conjunction (two shadow slots), and REAL_USED is ProgWorld.v's literal list *)
  pose proof (RT_OF_CORE TFIB_SYMS LAWS cx _ k ly3 S3 W3
                (L_MState.MS regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0)
                   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs))
                md3 HBASE HJ Hrt) as (_ & _ & _ & _ & HCF & _ & _ & HREAL).
  destruct HCF as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  unfold A.ProgWorld.REAL_USED in HREAL.
  assert (HRB : L_Mem.bytes_at A.Img0.rsegs mem3 0xa17f0 (L_Mem.le8 (L_Mem.wa 0x97b0c)))
    by exact (proj1 (Forall_forall _ _) HREAL (0xa17f0, 0x97b0c)
                ltac:(unfold A.AsanRT.RT_REALS; f35_in) ltac:(f35_in)).
  assert (HRM : L_Mem.bytes_at A.Img0.rsegs mem3 0xa17e8 (L_Mem.le8 (L_Mem.wa 0x97bdc)))
    by exact (proj1 (Forall_forall _ _) HREAL (0xa17e8, 0x97bdc)
                ltac:(unfold A.AsanRT.RT_REALS; f35_in) ltac:(f35_in)).
  assert (HC254 : L_Mem.bytes_at A.Img0.rsegs mem3 (0x13a3a8 + 254) [Z_to_bv 8 1]).
  { pose proof (A.Prog.Seg.F35.f35_ba_sub _ _ _ 14 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 14) with (0x13a3a8 + 254) in Hs by (unfold A.AsanRT.RT_CF; lia).
    exact Hs. }
  assert (HC255 : L_Mem.bytes_at A.Img0.rsegs mem3 (0x13a3a8 + 255) [Z_to_bv 8 1]).
  { pose proof (A.Prog.Seg.F35.f35_ba_sub _ _ _ 15 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 15) with (0x13a3a8 + 255) in Hs by (unfold A.AsanRT.RT_CF; lia).
    exact Hs. }
  (* the footprint at RNG_W (w_H W3) *)
  assert (HWV : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (Reusable.YG0d.spZ regs3 - 4560) 4560).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (HPRES a ltac:(lia))). }
  pose proof (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 32 HAR
                Hinphi ltac:(lia) ltac:(rewrite Erq; lia)) as HLV.
  destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 32 HAR
              Hinphi ltac:(lia) ltac:(rewrite Erq; lia) ltac:(lia)) as [HLz|HLshv]; [lia|].
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 64) 32 HAR Hin6
              ltac:(lia) ltac:(lia)) as (HRV & HRsh0).
  destruct (f35_hull fr Ffr32) as (H64a & H64b).
  destruct (HRsh0 ltac:(lia) ltac:(rewrite Efa; exact H64a) ltac:(rewrite Efa, E4096; exact H64b))
    as [HRz|HRshv]; [lia|].
  assert (HLs : L_ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                  (8 * (A.AsanRT.shadow_addr (phi + 18) / 8))
                  (8 * (A.AsanRT.shadow_addr (phi + 18 + 31) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (phi + 18) / 8))).
  { apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HLshv.
    replace (phi + 18 + 32 - 1) with (phi + 18 + 31) in HLshv by lia.
    rewrite !(Z.mul_comm 8). exact HLshv. }
  assert (HRs : L_ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                  (8 * (A.AsanRT.shadow_addr (fr + 64) / 8))
                  (8 * (A.AsanRT.shadow_addr (fr + 64 + 31) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (fr + 64) / 8))).
  { apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HRshv.
    replace (fr + 64 + 32 - 1) with (fr + 64 + 31) in HRshv by lia.
    rewrite !(Z.mul_comm 8). exact HRshv. }
  (* G3: the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl), then the walk moved from
     the cut's register map regs3 to the run's canonical one, mkR_of regs3 (YA0nR.SRr_xregs_eqv). *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i])) with 0x82888.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (L_Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82888) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (L_Regs6ss.xregs_eqv_sym _ _ (L_Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run f35_call_F, lifted whole with SRr_fevt_hid at RNG_W (w_H W3) (the run is over Img0.rsegs, the cut
     over tfibsegs: ProgBridge.tfibsegs_rsegs). *)
  eassert (HRUN : L_ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
                    (L_MState.MS (L_Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
                       (Z_to_bv 64 0x82888) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
                       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
  { unfold L_Regs6ss.mkR_of.
    eapply A.Prog.Seg.F35F.f35_call_F_on with (L := phi + 18) (R := fr + 64)
      (ls := firstn 32 (skipn 18 (SlM.t_phi (ACtlCut.c_in cx) j))) (rs := SlM.decl_i (Z.of_nat i)) (v := v)
      (lo := Reusable.YG0d.spZ regs3 - 4560).
    - exact R10.
    - exact R22'.
    - exact R25.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HLb.
    - exact Hrow.
    - exact Hv.
    - exact HRO.
    - exact HadL.
    - exact Hadr.
    - exact HaL32.
    - exact HaR32.
    - exact HaL7.
    - exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact HloK.
    - exact HloH.
    - exact HspA.
    - exact HAC.
    - exact HSWon.
    - exact HRB.
    - exact HRM.
    - exact HGOTCF.
    - exact HC254.
    - exact HC255.
    - exact (A.ProgBridge.rng_bytes_RNG_W _).
    - exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
    - exact (A.ProgBridge.rng_of_visible _ _ _ HWV).
    - exact (A.ProgBridge.rng_of_visible _ _ _ HLV).
    - exact HLs.
    - exact (A.ProgBridge.rng_of_visible _ _ _ HRV).
    - exact HRs.
    - exact (proj1 A.Prog.Seg.F35F.F35BWO.bcmp_wrap_F_at_on_owner A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on _). }
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the continuation, at the run's end state MS R .. 0x8289c .. mem': R is the run's own end map, so the exit
     cut is taken at regs := R. *)
  intros ms' md' HQ0 Hhid Hsbm.
  cbv beta in HQ0.
  destruct HQ0 as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & mem' &
                   Ems & MU & WM & RO' & ST').
  subst ms'.
  match goal with |- context [L_MState.MS ?R0 _ _ _ _ _ _] => set (R := R0) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i])) R mem' md')
            (POST cx)).
  assert (MU3 : L_Frame.munch [(Reusable.YG0d.spZ regs3 - 4560, Reusable.YG0d.spZ regs3)] mem3 mem') by exact MU.
  assert (ST3 : L_Frame.stk segs mem' (Reusable.YG0d.spZ regs3 - 4560) (Reusable.YG0d.spZ regs3)) by exact ST'.
  (* the kept set: every byte outside the wrapper's window *)
  pose (Kp := fun x : Z => ~ (Reusable.YG0d.spZ regs3 - 4560 <= x < Reusable.YG0d.spZ regs3)).
  assert (HK : forall x, 0 <= x < 2 ^ 64 -> Kp x -> mem' (L_Mem.wa x) = mem3 (L_Mem.wa x)).
  { intros x Hx HKx. apply MU3. rewrite L_Mem.wa_unsigned by lia. cbn [L_Frame.outside]. split; [exact HKx | exact I]. }
  (* the registers of R: x2 x3 x4 x8 x9 x18-x27 are regs3's, x10 the compare result *)
  assert (E2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E20 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 20 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 20) by reflexivity.
  assert (E21 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E24 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 24 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E25 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (E26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (K10 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 v) by reflexivity.
  (* the exit body's memory conjuncts across the write *)
  assert (HA0 : 0 <= Asp) by lia.
  assert (HA1 : Asp + 312 <= 2 ^ 64) by lia.
  assert (HRA : forall x, Asp <= x < Asp + 312 -> Kp x) by (intros x Hx; unfold Kp; lia).
  assert (HFRACm : ACtlCutP.FRAC B cx fr fr regs3 mem').
  { apply (f35_frac_keep B Kp cx fr fr regs3 mem3 mem' HK); [ | | | exact HFRAC].
    - intros x Hx. unfold Kp. lia.
    - intros x Hx. unfold Kp. unfold ACtlCutP.Sfr in Hx. change ACtlCutP.FRAME_SHADOW with 392 in Hx.
      pose proof (f35_sh_low fr ltac:(lia)). lia.
    - intros x Hx. unfold Kp. lia. }
  pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem' HFRACm E2 E3 E4 E8 E9 E19 E26) as HFRAC'.
  assert (HHB' : ACtlCutP.HB mem' phi (ACtlCutP.flen cx j)).
  { destruct HHB as (Hphi0 & Hadd). split; [exact Hphi0|].
    apply (f35_addr_keep Kp mem3 mem' _ _ HK); [|exact Hadd].
    intros x Hx. rewrite Hasz in Hx. unfold Kp. pose proof (f35_sh_low x ltac:(lia)). lia. }
  pose proof (f35_flsi_keep Kp cx j fr regs3 R mem3 mem' Asp F9 HA0 HA1 E9 HK HRA
                ltac:(intros x Hx; unfold Kp; unfold ACtlCutP.FRAME_BYTES in Hx; lia)
                ltac:(intros x Hx; unfold Kp; unfold ACtlCutP.FRAME_BYTES in Hx;
                      pose proof (f35_sh_low x ltac:(lia)); lia)
                ltac:(intros x Hx; unfold Kp; rewrite <- Hlen in Hx;
                      destruct (Z_lt_le_dec 0 (ACtlCut.c_n cx)) as [Hn0|Hn0]; [pose proof (HinB Hn0)|]; lia)
                ltac:(intros x Hx; unfold Kp;
                      destruct (Z_lt_le_dec 0 (ACtlCut.c_n cx)) as [Hn0|Hn0]; [|lia];
                      pose proof (HinB Hn0); pose proof (f35_sh_low x ltac:(lia)); lia)
                HFLSI) as HFLSI'.
  pose proof (f35_lk_keep Kp cx fr j regs3 R mem3 mem' E21 HK ltac:(intros x Hx; unfold Kp; lia) HLK) as HLK'.
  pose proof (f35_flsx_keep Kp cx j phi fr regs3 R mem3 mem' Asp F9 HA0 HA1 E9 E18 E22 E23 E25 HK HRA
                ltac:(intros x Hx; unfold Kp; lia) HFLSI' HFLSX) as HFLSX'.
  assert (HRL' : ACtlCutP.RL cx j i phi fr R mem').
  { destruct HRL as (Hi10' & H20 & H24 & Hprev' & Hsel' & _).
    split; [exact Hi10'|].
    split; [unfold ACtlCut.rgv in H20 |- *; rewrite E20; exact H20|].
    split; [unfold ACtlCut.rgv in H24 |- *; rewrite E24; exact H24|].
    split; [exact Hprev'|]. split; [exact Hsel' | exact HFLSX']. }
  assert (Hiff' : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 0 <->
                  SlM.t_blk (ACtlCut.c_in cx) j = SlM.decl_i (Z.of_nat i)).
  { rewrite K10, (A.Prog.Seg.F35.f35_lit0 v Hvr), (A.Prog.Seg.F35.f35_blk (ACtlCut.c_in cx) j Hbig'). exact Hiff. }
  assert (Hrow' : L_Mem.bytes_at segs mem' (fr + 64) (SlM.decl_i (Z.of_nat i))).
  { apply (f35_bytes_keep Kp mem3 mem' _ _ HK); [|exact Hrow].
    rewrite Hrs. intros x Hx. unfold Kp. lia. }
  assert (Hadr' : A.AsanRT.addressable mem' (fr + 64) 32).
  { apply (f35_addr_keep Kp mem3 mem' _ _ HK); [|exact Hadr].
    intros x Hx. unfold Kp. pose proof (f35_sh_low x ltac:(lia)). lia. }
  assert (LID : length (SlM.t_ID (ACtlCut.c_in cx) (S j)) = 38%nat)
    by exact (A.Prog.Seg.F35.f35_tID_length _ _).
  pose proof (A.Prog.Seg.F35.f35_FG_len (ACtlCut.c_in cx) (S j)) as LFG.
  pose proof (A.Prog.Seg.F35.f35_fs_body_len (ACtlCut.c_in cx) (S j)) as LBD.
  pose proof (f35_lt_keep Kp cx fr j regs3 R mem3 mem' Asp F9 HA0 HA1 E9 HK HRA
                ltac:(intros x Hx; unfold Kp; lia)
                ltac:(intros x Hx; unfold Kp; lia)
                ltac:(intros x Hx; unfold Kp; lia)
                ltac:(intros x Hx; unfold Kp; pose proof (f35_sh_low x ltac:(lia)); lia)
                HLT) as HLT'.
  apply (HX cx [Z.of_nat j; Z.of_nat i] fr k ly3 S3 W3 R mem' md' HBASE).
  - (* journal: the window written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => Reusable.YG0d.spZ regs3 - 4560 <= a < Reusable.YG0d.spZ regs3).
    + exact HJ.
    + intros x Hx. cbv beta in Hx. unfold Reusable.YK04.mrestrict. rewrite (MU3 x); [reflexivity|].
      cbn [L_Frame.outside]. split; [exact Hx | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *. revert Hx.
      destruct (Reusable.YA0n.w_H W3 x); intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (Reusable.YG0d.spZ regs3 - 4560)) as [L1|L1];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (Reusable.YG0d.spZ regs3)) as [L2|L2]].
      * rewrite (MU3 x); [exact Hx|]. cbn [L_Frame.outside]. split; [lia | exact I].
      * destruct ST3 as (_ & _ & Hst). destruct (Hst (bv_unsigned x) (conj L1 L2)) as (_ & b & Hb).
        unfold L_Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
        rewrite (f35_mrd_high mem' x b ltac:(lia) Hb). discriminate.
      * rewrite (MU3 x); [exact Hx|]. cbn [L_Frame.outside]. split; [lia | exact I].
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
    + intros a Ha. cbv beta in Ha. left. unfold A.ACfn.LLVMF_STK. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A8289c_at [j; i] (ACtlCutP.v) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8289c_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite !Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split; [exact HFRAC'|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HRL'|].
    split; [exact Hiff'|].
    split; [exact Hrow'|].
    split; [exact Hadr' | exact HLT'].
  - (* ctl_rt_C at the same ly3 S3: asan_cells kept (the window is above [RT_LO, RT_HI)), both shadow regions kept
       (every shadow byte is below the window), ro_agree from the run's post *)
    assert (HKsh : forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P mem').
    { intros P HSP a HPa Ha. destruct (HSP a HPa Ha) as (Hw & b & Hb).
      assert (Ea : mem' (L_Mem.wa a) = mem3 (L_Mem.wa a)).
      { unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
          A.AsanRT.HIGHMEM_BEG in Ha.
        apply HK; [lia | unfold Kp; lia]. }
      split; [unfold wview in *; rewrite Ea; exact Hw | exists b; unfold L_Mem.mrd in *; rewrite Ea; exact Hb]. }
    split; [|split; [|split]].
    + refine (A.AsanRTFacts.asan_cells_kept _ mem3 mem' HAC MU3 _).
      cbn [L_Frame.disjoint_from]. split; [left; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia | exact I].
    + exact (HKsh _ Hcut).
    + exact (HKsh _ Himg).
    + exact RO'.
Qed.

End GlueF35.

Print Assumptions glue_seg_F35.
