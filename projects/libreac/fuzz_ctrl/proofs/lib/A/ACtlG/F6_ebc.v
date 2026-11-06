(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v, with its numbers changed; 2171 of its 2324 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R10.v, with its module paths changed; 645 of its 706 lines of code are new or changed and 2263 lines of the source are left out. *)
(* lib/A/ACtlG/F6_ebc.v -- GLUE for stage seg_F6_ebc of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v seg_F6_ebc, W piece W4b): the frame turn's reac_ctrl_parse call at 0x81f60.  Written by a Theorem Labs lane
   (brief stage-parse-sites.md (a working note, not in this delivery)); single writer.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F6_ebc : forall POST (j : nat),
       CF POST (ix_cut C_A81f64_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f54_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F6_ebc.  Segment F6_ebc is 0x81f54 -> 0x81f64 (Seg/F6.v:11): mv a0,s7 ; mv a1,s2 ; li a2,0 ;
   jal reac_ctrl_parse (0x81f60, return 0x81f64).  The return point IS the exit cut C_A81f64_at.

   THE ROUTE (a Theorem Labs lane 03:56Z): the walk applies a Theorem Labs lane's cgif-form treac_ctrl_parse_spec at the jal, cited
   as the named Section hypothesis TPARSE; the run before the call is the narrowed pre stretch f6_ebc_pre_Fs of
   lib/A/Prog/Seg/F6Fs.v (this lane's split of F6.f6_ebc_evt, granted by a Theorem Labs lane 04:01Z: four register-only
   steps, so it is lifted at the empty footprint); there is no stretch after the call, so the exit cut is applied
   to TPARSE's post (glue-pattern.md section 8 (a working note, not in this delivery), "ra is the exit cut").  reac_ctrl_parse_contract_F is NOT used.

   THE PROOF
   G1  unfold the entry cut: ix_cut's index equation, then C_A81f54_at's FRAC and b5_body (b5_K, IDj, b5_F17,
       b5_W240, b5_PF), one name per conjunct.
   G2  numeric facts from visible state: the frame law and layout_le's ly_F give frame_addr ly3 6 pos = fr; FRAC
       gives sp, A and their bounds; astk_ok (the journal) puts the stack above alloc_ceiling.
   G3  the cut's configuration as MS (ProgBridge.cfg_at_MS), the walk moved to the run's canonical map
       (YA0nR.SRr_xregs_eqv), and mkR_of regs3 written with the run's three literal registers (sp, s2 = flen,
       s7 = phi).
   G4  lift f6_ebc_pre_Fs (ProgBridge.fevt_of_evtF, tfibsegs_rsegs, YA0nR.SRr_fevt at Kit.kit_RNG0): the walk is at
       reac_ctrl_parse's entry 0x83578 with ra = 0x81f64, a0 = phi, a1 = flen, a2 = 0, memory mem3, model md'.
   P   TPARSE at that state (YA0n.SRr_bind), at STK := LLVMF_STK, sp0 := c_sp cx, FP := [], the entry context,
       own := own6, lyc / Sc / W / memc := ly3 / S3 / W3 / mem3, f := phi, n := flen, o := 0,
       fr := SlotModel.t_g (c_in cx) j.  Its caller duties (spec-draft section 4, P6 dropped by R5): P1 the journal
       across the model materialization (YCbq.ajournal_exec, empty write set); P2 arodata_okS kept by the journal
       (f6g_aro_journal, FP = []); P3 ra = 0x81f64; P4 gp / tp from the entry and FRAC; P5 the argument registers;
       P7 the stack (FRAC); P8 no class-1 frame (frames S3 = own6); P9 / P12 / P13 the record block (the body's live
       list, F6.f6_tg_len, b5_PH, AR_blocks_law's visibility, ProgWorld.aview_vis_mrd); P10 / P11 vacuous (o = 0).
   G5  TPARSE's post at the return point is the exit cut's configuration (getr Rc 1 = 0x81f64); the exit's
       ctl_from at the same cx, fr, k and the post's ly2 S2 W2 regs2 mem2 md2:
         journal  the post's own (same own6, same k);
         frames   frames S2 = frames S3 = own6; frame law and k bound unchanged;
         body     registers: aregs_preserved keeps every callee-saved register the body reads, a0 is
                  fst (ctrlparse flen (t_g ..)) = SlotModel.t_k by definition; memory: every byte the body reads is
                  of a class TPARSE's acall_kept keeps (ProgWorld.ctl_post_acall_kept): the stack above the
                  callee's window [sp - 8800, sp) (the spills at A, the saved registers at c_sp - 104), the live
                  class-6 frame and its shadow, live heap blocks (the record at phi, the input at c_p), the
                  non-owned image bytes (KIND_NAME); the live blocks' shadow bytes come from AR_shadow_law at both
                  ends (f6g_blk_sh_keep) or ProgWorldShadow.ctl_block_shadow_of_AR at the post, KIND_NAME's shadow from
                  ProgWorldShadow.ctl_zshadow_of_AR, the frame's presence (FRM.stk) from AR_frames_law at the post;
                  the existential byte lists of b5_PF of unbounded length are cut to the bytes they are used for;
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR (the call writes runtime cells and the post's
                  state is not the entry's), with the post's arodata view (f6g_aro_journal from the entry); route (C),
                  L3-recipe.md section 2(d) (a working note, not in this delivery).

   SECTION HYPOTHESES (exact text below)
   - ACtl.v's own: RELRO_IMG, LAWS, TFIB_SYMS (same names and texts as ACtl.v's Section Ctl).
   - TPARSE: a Theorem Labs lane's parse spec of record (a working branch 621a4ba64dc,
     lib/A/Prog/C_reac_ctrl_parse.v, REAC_CTRL_PARSE_STK = 8800), the route's named callee hypothesis.
   - none for the exit's runtime conjunct: route (C) (L3-recipe.md (a working note, not in this delivery)) takes ctl_rt_C from the post's AR by
     A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither A.ProgWorld.AR_states_vis0_shadow nor
     AR_states_owned_ro, so the former Section hypotheses VIS0 / OWNED_RO are gone.

   SIX TWIN MODULES (porter a Theorem Labs lane 04:24Z / 04:33Z): YI04 / YI16 / YK11 / YK1b / YM05 / YO09 are named only
   through the aliases CK11 / CK1b / CM05 / CO09 of their core copies' full paths; their Require lines name full
   paths.  The closure also reaches ctrl's lib/A/Reusable copies (through Seg/F6Fs.v and Seg/F6.v); no content of
   those copies is named here.

   CLOSURE (glue closure rule): every project Require is qualified; the _F file Seg/F6Fs.v brings Seg/F6.v and the
   frame route of record into the closure (rule 1), named in the commit message with blobs (rule 5).

   BUILD STATE: type-check on the stand-in-free image-A glue base a working branch 29ddfc3ea99
   (interim core 5da74c9c931; its lib/A/AF0m.v and AF0l.v are ctrl's record blobs, the same as
   a working branch e56483f863b).  This proof reads the bundle's start-up tables in two steps
   only (KKN, b5_KN): KIND_NAME's 112 bytes avoid Tfib_owned_static and lie in a Tfib_zero_shadow row.  Both are
   decided by a boolean search (forallb / existsb, vm_compute), so they do not depend on the tables' order (record
   AF0m.v:2963 row (0x21aa0, 0x9e7d0 - 0x21aa0); the first owned row past KIND_NAME, (0x9e7d0, 0x30) at :2979, starts
   at KIND_NAME + 112).  TFIB_ERRNO = 0x5db76c.  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG00 YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRt A.ProgWorldShadow.
(* route (C): the narrowed cut conjunct and its producer from AR (no VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.C_reac_ctrl_parse A.Prog.CtrlImg A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F6 A.Prog.Seg.F6Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Spec.StrFun Prog.RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Byte-level helpers of this stage (no frame-route name): bytes and addressability move along a memory that
   reads the same on the bytes they name; a cut prefix of a byte list; memcmp_model reads n bytes. *)

Lemma f6g_bytes_keep_in : forall (m m' : word -> option byte) a bs lo hi,
  (forall x, lo <= x < hi -> Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Lib.Mem.mrd segs m (Lib.Mem.wa x)) ->
  lo <= a -> a + Z.of_nat (length bs) <= hi ->
  Lib.Mem.bytes_at segs m a bs -> Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs lo hi K Hlo Hhi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite K by lia. exact (H i Hi).
Qed.

Lemma f6g_addr_keep : forall (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n ->
     Lib.Mem.mrd A.Img0.rsegs m' (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
     Lib.Mem.mrd A.Img0.rsegs m (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hs). split; [exact Ha|].
  exists b. rewrite (K i Hi). split; [exact Hb | exact Hs].
Qed.

Lemma f6g_bytes_firstn : forall (m : word -> option byte) a bs k,
  Lib.Mem.bytes_at segs m a bs -> Lib.Mem.bytes_at segs m a (firstn k bs).
Proof.
  intros m a bs k H. rewrite <- (firstn_skipn k bs) in H.
  exact (proj1 (proj1 (Lib.Mem.bytes_at_app segs m a (firstn k bs) (skipn k bs)) H)).
Qed.

Lemma f6g_memcmp_firstn : forall n l r,
  A.Spec.StrFun.memcmp_model (firstn n l) (firstn n r) n = A.Spec.StrFun.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn [firstn A.Spec.StrFun.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A range of present visible bytes is ctrl's stk (the frame's presence). *)
Lemma f6g_stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) ->
  Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as [_ (b & Hb)]. unfold Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* mkR_of regs is the explicit 31-slot register map of the core's register reads (F6.f6_mkR_expand over the core's
   YK11; both reads unfold to reg_get at a nonzero index). *)
Lemma f6g_mkR_expand : forall regs, Lib.Regs6ss.mkR_of regs =
  Lib.Frame.mkR (CK11.getr regs 1) (CK11.getr regs 2) (CK11.getr regs 3) (CK11.getr regs 4) (CK11.getr regs 5)
    (CK11.getr regs 6) (CK11.getr regs 7) (CK11.getr regs 8) (CK11.getr regs 9) (CK11.getr regs 10)
    (CK11.getr regs 11) (CK11.getr regs 12) (CK11.getr regs 13) (CK11.getr regs 14) (CK11.getr regs 15)
    (CK11.getr regs 16) (CK11.getr regs 17) (CK11.getr regs 18) (CK11.getr regs 19) (CK11.getr regs 20)
    (CK11.getr regs 21) (CK11.getr regs 22) (CK11.getr regs 23) (CK11.getr regs 24) (CK11.getr regs 25)
    (CK11.getr regs 26) (CK11.getr regs 27) (CK11.getr regs 28) (CK11.getr regs 29) (CK11.getr regs 30)
    (CK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A register that pins a 64-bit address pins one integer in a window of 2^64: a spill base read back through
   register 9 at an in-range offset is the FRAC base. *)
Lemma f6g_A_eq : forall A A' off,
  Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A -> A + off < 2 ^ 64 -> 0 <= off ->
  0 <= A' + off -> A' + off < 2 ^ 64 -> A' = A.
Proof.
  intros A A' off E HA HAo Hoff H0 H1.
  pose proof (f_equal (@bv_unsigned 64) E) as E'. rewrite !Z_to_bv_unsigned in E'.
  unfold bv_wrap in E'. change (bv_modulus 64) with (2 ^ 64) in E'.
  rewrite (Z.mod_small A) in E' by lia.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueF6ebc.

(* ACtl.v's Section shape (ACtl.v Section Ctl), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img segs a.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81f54_at := (ACtlCutP.C_A81f54_at B).
Local Notation C_A81f64_at := (ACtlCutP.C_A81f64_at B).

(* The cgif-form parse spec of record, at the call (the route of a Theorem Labs lane 03:56Z). *)
Hypothesis TPARSE : A.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
(* route (C): VIS0 / OWNED_RO (ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) are GONE: the exit's ctl_rt_C
   comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* arodata_okS is kept by a journal whose freed-block list is empty (APostBase.arodata_ok_journalP's proof, with
   FP = [] in place of the ro_below_ofl instance). *)
Lemma f6g_aro_journal : forall STK sp0 ly S (W : lib.Reusable.YA0n.world segs) mem md own ly' S'
    (W' : lib.Reusable.YA0n.world segs) mem' md' k,
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  lib.Reusable.YE01.arodata_okS segs B RLO RHI (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem) ->
  lib.Reusable.YE01.arodata_okS segs B RLO RHI (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W') mem').
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | ].
  - destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] |].
    exact (RELRO_IMG a Hgot).
  - apply (lib.Reusable.YCbq.fp_spares_closed (SK := A.AE2k.tfib_sink_head)).
    intros Hop. exact (lib.Reusable.YCbq.sink_closed_nil Hop).
Qed.

(* A live block's shadow bytes read the same at any two states whose AR both list it (AR_shadow_law gives their
   values, the view reads them, so they are visible). *)
Lemma f6g_blk_sh_keep : forall ly S (W : lib.Reusable.YA0n.world segs) m md ly' S'
    (W' : lib.Reusable.YA0n.world segs) m' md' p n i,
  lib.Reusable.YG0n.AR segs B ly S W m md -> lib.Reusable.YG0n.AR segs B ly' S' W' m' md' ->
  In (p, n) (lib.Reusable.YG0d.ablocks B ly S) -> In (p, n) (lib.Reusable.YG0d.ablocks B ly' S') ->
  0 <= i < (lib.Reusable.YG00.req_size n + 7) / 8 ->
  Lib.Mem.mrd A.Img0.rsegs m'
    (Lib.Mem.wa (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF p + i)) =
  Lib.Mem.mrd A.Img0.rsegs m
    (Lib.Mem.wa (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF p + i)).
Proof.
  intros ly S W m md ly' S' W' m' md' p n i HAR HAR' Hin Hin' Hi.
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly S W m md p n HAR Hin) as ((_ & _ & Hc) & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly' S' W' m' md' p n HAR' Hin') as ((_ & _ & Hc') & _).
  pose proof (Hc i Hi) as E. pose proof (Hc' i Hi) as E'.
  set (a := lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF p + i) in *.
  set (v := if i <? lib.Reusable.YG00.req_size n / 8 then 0 else lib.Reusable.YG00.req_size n mod 8) in *.
  assert (Hv : lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false)
    by (apply (A.ProgWorldVisFrame.vis_of_aview segs W m a); rewrite E; discriminate).
  assert (Hv' : lib.Reusable.YA0n.w_H W' (Z_to_bv 64 a) = false)
    by (apply (A.ProgWorldVisFrame.vis_of_aview segs W' m' a); rewrite E'; discriminate).
  unfold Lib.Mem.wa.
  rewrite (A.ProgWorld.mrd_of_aview_some W m a v Hv E), (A.ProgWorld.mrd_of_aview_some W' m' a v Hv' E').
  reflexivity.
Qed.

(* A spill of register 9's base moves along a register map that keeps register 9 and a memory that keeps the
   spill area [A, A + 416). *)
Lemma f6g_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  CK11.getr regs' 9 = CK11.getr regs 9 ->
  (forall x, A <= x < A + 416 -> Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Lib.Mem.mrd segs m (Lib.Mem.wa x)) ->
  0 <= off -> off + 8 <= 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v RA HA HA416 E9 K Hoff Hoff8 (A' & RA' & Hq).
  unfold ACtlCut.rgv in RA, RA'. unfold ACtlCutP.q64 in Hq.
  pose proof (Lib.Mem.bytes_at_bound segs _ _ _ Hq) as (Hq0 & Hq1). rewrite Lib.Mem.length_le8 in Hq1.
  assert (EA : A' = A) by (apply (f6g_A_eq A A' off); [rewrite <- RA', <- RA; reflexivity | lia..]).
  subst A'. exists A. split; [unfold ACtlCut.rgv; rewrite E9; exact RA|].
  unfold ACtlCutP.q64. apply (f6g_bytes_keep_in m m' (A + off) _ A (A + 416) K); [lia | | exact Hq].
  rewrite Lib.Mem.length_le8. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F6_ebc : forall POST (j : nat),
  CF POST (ix_cut C_A81f64_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f54_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  assert (Ej : ACtlCutP.ixn 0 [Z.of_nat j] = j) by exact (Nat2Z.id j).
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81f54_at] in Hb.
  rewrite Ej in Hb. unfold ACtlCutP.b5_body in Hb. cbv beta in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & HK & HIDj & HF17 & HW240 & HPF).
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsp4096 & Happ & QA304 & QA24 & QA16 & Qhdr & Qent & Hsh & Hsaved).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in Happ.
  pose proof HC as (R23 & R18 & (A1 & R9c & HA1 & HSPILL & Q232) & HPH & HFR & HKN & HFG & HFS).
  pose proof HK as (R20 & R22 & R24 & R25 & SP280 & U176 & Hra).
  (* the entry facts *)
  pose proof HB as ((HAFN & _ & _ & _ & Hpn & Hlen & _ & _ & _ & _ & HARO & _) & _).
  pose proof HAFN as (_ & _ & _ & Hgp0 & _ & _ & _ & _ & _).
  (* the journal at the cut *)
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hastk3 & _).
  pose proof Hastk3 as (_ & _ & Hstklo & Hstk & Hsp0hi & Hstkhi & _).
  unfold A.ACfn.LLVMF_STK in Hstk.
  (* G2: the frame *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (EF3 : lib.Reusable.YG0f.ly_F ly3 = lib.Reusable.YG0f.ly_F (ACtlCut.c_ly cx)).
  { destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). first [exact EF | exact (eq_sym EF)]. }
  assert (Efa3 : lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF3. reflexivity. }
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (Hfr4096 & Hfrceil & _).
  rewrite Efa3 in Hfr4096, Hfrceil.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfrceil.
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & _ & HFb3 & HFs3).
  rewrite Efa3 in HFb3, HFs3. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in HFb3, HFs3.
  (* the record block *)
  assert (Hinphi3 : In (phi, ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR3 Hinphi3)
    as (Hphi16 & Hphi4096 & Hphiceil & _ & Hphipres & _ & Hflen0).
  (* sp, A *)
  assert (Hsp0 : 0 <= sp) by (rewrite <- HspZ; apply bv_unsigned_in_range).
  assert (HAeq : A1 = A).
  { apply (f6g_A_eq A A1 0); [rewrite <- R9c, <- R9; reflexivity | lia | lia | lia | lia | lia]. }
  subst A1.
  (* G3: the cut's configuration in the run's state form, the walk at the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81f54_at [Z.of_nat j])) with 0x81f54.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81f54) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  rewrite f6g_mkR_expand, R2, R18, R23.
  (* G4: the narrowed pre stretch, lifted at the empty footprint *)
  pose proof (A.Prog.Seg.F6Fs.f6_ebc_pre_Fs A.ACtlG.Kit.kit_RNG0
    (CK11.getr regs3 1) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5) (CK11.getr regs3 6)
    (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10) (CK11.getr regs3 11)
    (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15) (CK11.getr regs3 16)
    (CK11.getr regs3 17) (CK11.getr regs3 19) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22)
    (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27)
    (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 phi (ACtlCutP.flen cx j) sp) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS0.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS0.
  apply (lib.Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS0).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  intros ms' md' HQ0 Hsbm. subst ms'.
  set (Rc := Lib.Frame.mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 sp) (CK11.getr regs3 3) (CK11.getr regs3 4)
    (CK11.getr regs3 5) (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9)
    (Z_to_bv 64 phi) (Z_to_bv 64 (ACtlCutP.flen cx j)) (Z_to_bv 64 0) (CK11.getr regs3 13) (CK11.getr regs3 14)
    (CK11.getr regs3 15) (CK11.getr regs3 16) (CK11.getr regs3 17) (Z_to_bv 64 (ACtlCutP.flen cx j))
    (CK11.getr regs3 19) (CK11.getr regs3 20) (CK11.getr regs3 21) (CK11.getr regs3 22) (Z_to_bv 64 phi)
    (CK11.getr regs3 24) (CK11.getr regs3 25) (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28)
    (CK11.getr regs3 29) (CK11.getr regs3 30) (CK11.getr regs3 31)).
  assert (ESR : lib.Reusable.YG0d.spZ Rc = sp).
  { unfold lib.Reusable.YG0d.spZ. change (CK11.getr Rc 2) with (Z_to_bv 64 sp).
    exact (Lib.Mem.wa_unsigned sp ltac:(lia)). }
  (* P1: the journal across the model materialization *)
  assert (HJ' : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  (* P: the call, on a Theorem Labs lane's spec *)
  assert (EPA : A.Prog.C_reac_ctrl_parse.A_reac_ctrl_parseP = 0x83578) by (vm_compute; reflexivity).
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs A.Prog.C_reac_ctrl_parse.A_reac_ctrl_parseP Rc mem3 md') (POST cx)).
  eapply (lib.Reusable.YA0n.SRr_bind segs).
  { apply (TPARSE A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
             (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k Rc phi
             (ACtlCutP.flen cx j) 0 (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)).
    - (* P1 *) exact HJ'.
    - (* P2 *) exact (f6g_aro_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    - (* P3 *) change (CK11.getr Rc 1) with (Z_to_bv 64 0x81f64). vm_compute. reflexivity.
    - unfold lib.Reusable.YG0d.raZ. change (bv_unsigned (CK11.getr Rc 1)) with 532324. lia.
    - (* P4 *) change (CK11.getr Rc 3) with (CK11.getr regs3 3). rewrite R3. exact Hgp0.
    - change (CK11.getr Rc 4) with (CK11.getr regs3 4). exact R4.
    - (* P5 *) reflexivity.
    - reflexivity.
    - reflexivity.
    - pose proof Hflen0 as (Hf0 & Hfm). unfold lib.Reusable.YG00.MALLOC_MAX in Hfm. lia.
    - (* P7 *) rewrite ESR. exact Hsp16.
    - rewrite ESR. unfold A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK, lib.Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK.
      lia.
    - rewrite ESR. lia.
    - (* P8 *) rewrite HF. vm_compute. reflexivity.
    - (* P9 *) intros Hn. exists (ACtlCutP.flen cx j). split; [exact Hinphi3|].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia.
    - (* P10 *) intros Ho. exfalso. apply Ho. reflexivity.
    - (* P11 *) intros Ho. exfalso. apply Ho. reflexivity.
    - (* P12 *) exact (A.Prog.Seg.F6.f6_tg_len (ACtlCut.c_in cx) j).
    - (* P13 *) intros Hn i Hi.
      destruct HPH as (HPHb & _). pose proof (HPHb Hn) as (_ & _ & Hg).
      assert (Hil : (i < length (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))%nat)
        by (rewrite (A.Prog.Seg.F6.f6_tg_len (ACtlCut.c_in cx) j); exact Hi).
      assert (Hvis : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (phi + Z.of_nat i)) = false).
      { destruct (Hphipres (phi + Z.of_nat i)) as ((Hv & _) & _); [|exact Hv].
        unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
      rewrite (A.ProgWorld.aview_vis_mrd W3 mem3 (phi + Z.of_nat i) Hvis).
      pose proof (Hg i Hil) as Hgi. unfold Lib.Mem.wa in Hgi. rewrite A.ProgBridge.tfibsegs_rsegs in Hgi.
      rewrite Hgi.
      rewrite (nth_error_nth' _ lib.Prog.RcParse.cp_z Hil). reflexivity. }
  (* G5: after the call, at the return point = the exit cut *)
  intros W2 c2 Hle HPOST.
  destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & HF2 & Hbl2 & _ & HR10 & _ & Hkept).
  subst c2. rewrite ESR in Hkept.
  change (lib.Reusable.YA0n.SRr segs W2
            (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81f64_at [Z.of_nat j])) regs2 mem2 md2)
            (POST cx)).
  pose proof HJ2 as (HAR2 & Hly2 & _).
  (* the registers the exit body reads: kept by the call (aregs_preserved), as at the entry *)
  assert (KR : forall r : Z, lib.Reusable.YG0d.acallee_saved r ->
                 CK11.getr regs2 (Z_to_bv 5 r) = CK11.getr Rc (Z_to_bv 5 r)) by exact Hpres.
  assert (K2 : CK11.getr regs2 2 = CK11.getr regs3 2).
  { transitivity (CK11.getr Rc 2); [exact (KR 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK11.getr Rc 2) with (Z_to_bv 64 sp). symmetry. exact R2. }
  assert (K3 : CK11.getr regs2 3 = CK11.getr regs3 3)
    by exact (KR 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K4 : CK11.getr regs2 4 = CK11.getr regs3 4)
    by exact (KR 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K8 : CK11.getr regs2 8 = CK11.getr regs3 8)
    by exact (KR 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K9 : CK11.getr regs2 9 = CK11.getr regs3 9)
    by exact (KR 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K18 : CK11.getr regs2 18 = CK11.getr regs3 18).
  { transitivity (CK11.getr Rc 18); [exact (KR 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK11.getr Rc 18) with (Z_to_bv 64 (ACtlCutP.flen cx j)). symmetry. exact R18. }
  assert (K19 : CK11.getr regs2 19 = CK11.getr regs3 19)
    by exact (KR 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K20 : CK11.getr regs2 20 = CK11.getr regs3 20)
    by exact (KR 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K21 : CK11.getr regs2 21 = CK11.getr regs3 21)
    by exact (KR 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K22 : CK11.getr regs2 22 = CK11.getr regs3 22)
    by exact (KR 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K23 : CK11.getr regs2 23 = CK11.getr regs3 23).
  { transitivity (CK11.getr Rc 23); [exact (KR 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK11.getr Rc 23) with (Z_to_bv 64 phi). symmetry. exact R23. }
  assert (K24 : CK11.getr regs2 24 = CK11.getr regs3 24)
    by exact (KR 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K25 : CK11.getr regs2 25 = CK11.getr regs3 25)
    by exact (KR 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K26 : CK11.getr regs2 26 = CK11.getr regs3 26)
    by exact (KR 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  (* the memory the exit body reads: the classes TPARSE's acall_kept keeps (ctl_post_acall_kept) *)
  pose proof (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ Hkept Hle) as KC.
  assert (KS : forall a, sp <= a < ACtlCut.c_sp cx ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a)).
  { intros a Ha. apply KC.
    - assert (Hr : ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < ACtlCut.c_sp cx) by (unfold A.ACfn.LLVMF_STK; lia).
      destruct (Hpres3 a Hr) as [Hv _]. exact Hv.
    - rewrite (Lib.Mem.wa_unsigned a ltac:(lia)). left. split; [lia|]. lia. }
  assert (KSA : forall a, A <= a < A + 416 ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a))
    by (intros a Ha; apply KS; lia).
  assert (KF : forall a, fr <= a < fr + 4096 ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a)).
  { intros a Ha. apply KC.
    - destruct (HFb3 a Ha) as ((Hv & _) & _). exact Hv.
    - rewrite (Lib.Mem.wa_unsigned a ltac:(lia)). right. right. right.
      exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [|lia].
      left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efa3.
      change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (ESfr : ACtlCutP.Sfr fr = lib.Reusable.YG0f.shadow_addr fr)
    by (unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
          lib.Reusable.YG0f.SHADOW_OFF; lia).
  assert (KFS : forall a, lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 512 ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a)).
  { intros a Ha.
    assert (Hsa : 0 <= lib.Reusable.YG0f.shadow_addr fr)
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
    assert (Hsa' : lib.Reusable.YG0f.shadow_addr fr + 512 <= 2 ^ 64)
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
    apply KC.
    - destruct (HFs3 (a - lib.Reusable.YG0f.shadow_addr fr) ltac:(lia)) as ((Hv & _) & _).
      replace (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) with a in Hv by lia.
      exact Hv.
    - rewrite (Lib.Mem.wa_unsigned a ltac:(lia)). right. right. right.
      exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      + right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa3.
        change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
      + unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Ha. lia. }
  (* a frame byte's shadow lies in the frame's shadow *)
  assert (KFA : forall p n, fr <= p -> p + n <= fr + 4096 -> 0 <= n -> forall i, 0 <= i < n ->
            Lib.Mem.mrd A.Img0.rsegs mem2 (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
            Lib.Mem.mrd A.Img0.rsegs mem3 (Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))).
  { intros p n Hp Hpn' Hn i Hi. apply KFS.
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia. }
  assert (KB : forall p n a, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) ->
            p <= a < p + lib.Reusable.YG00.req_size n ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a)).
  { intros p n a Hin Ha.
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR3 Hin)
      as (_ & Hp4096 & Hpceil & _ & Hppres & _ & _).
    apply KC.
    - destruct (Hppres a Ha) as ((Hv & _) & _). exact Hv.
    - rewrite (Lib.Mem.wa_unsigned a ltac:(lia)). right. left.
      exists p, n, (a - p). split; [exact Hin|]. split; [lia|]. split; [lia|]. lia. }
  assert (Hinphi2 : In (phi, ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly2 S2))
    by (rewrite Hbl2; exact Hinphi3).
  assert (Ereq : lib.Reusable.YG00.req_size (ACtlCutP.flen cx j) = A.ACtlK.a_size (ACtlCutP.flen cx j)).
  { unfold lib.Reusable.YG00.req_size, A.ACtlK.a_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  (* the transports the exit body uses, by class *)
  assert (HA0 : 0 <= A) by lia.
  assert (HA64 : A + 416 <= 2 ^ 64) by lia.
  assert (AEQ : forall A', ACtlCut.rgv regs3 9 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' RA' HA'. pose proof R9 as R9'. unfold ACtlCut.rgv in RA', R9'.
    apply (f6g_A_eq A A' 0); [rewrite <- RA', <- R9'; reflexivity | lia..]. }
  assert (SPK : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v)
    by (intros off v H0 H1 Hs; exact (f6g_spill_keep regs3 regs2 mem3 mem2 A off v R9 HA0 HA64 K9 KSA H0 H1 Hs)).
  assert (QK : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.q64 mem3 (A + off) v -> ACtlCutP.q64 mem2 (A + off) v).
  { intros off v H0 H1 Hq. unfold ACtlCutP.q64 in *.
    apply (f6g_bytes_keep_in mem3 mem2 _ _ A (A + 416) KSA); [lia | rewrite Lib.Mem.length_le8; lia | exact Hq]. }
  assert (FK : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            Lib.Mem.bytes_at segs mem3 a bs -> Lib.Mem.bytes_at segs mem2 a bs)
    by (intros a bs H0 H1 Hb; exact (f6g_bytes_keep_in mem3 mem2 a bs fr (fr + 4096) KF H0 H1 Hb)).
  assert (FA : forall p n, fr <= p -> p + n <= fr + 4096 -> 0 <= n ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable mem2 p n)
    by (intros p n H0 H1 H2 Ha; exact (f6g_addr_keep mem3 mem2 p n (KFA p n H0 H1 H2) Ha)).
  assert (RK : forall a bs, phi <= a -> a + Z.of_nat (length bs) <= phi + ACtlCutP.flen cx j ->
            Lib.Mem.bytes_at segs mem3 a bs -> Lib.Mem.bytes_at segs mem2 a bs).
  { intros a bs H0 H1 Hb. apply (f6g_bytes_keep_in mem3 mem2 a bs phi (phi + ACtlCutP.flen cx j)); [|lia|lia|exact Hb].
    intros x Hx. apply (KB phi (ACtlCutP.flen cx j) x Hinphi3).
    unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  assert (RSK : forall i, 0 <= i < 3 ->
            Lib.Mem.mrd A.Img0.rsegs mem2
              (Lib.Mem.wa (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + i)) =
            Lib.Mem.mrd A.Img0.rsegs mem3
              (Lib.Mem.wa (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + i))
            \/ ACtlCutP.flen cx j < 50).
  { intros i Hi. destruct (Z_lt_le_dec (ACtlCutP.flen cx j) 50) as [Hlt|Hge]; [right; exact Hlt|left].
    apply (f6g_blk_sh_keep ly3 S3 W3 mem3 md3 ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) i HAR3 HAR2
             Hinphi3 Hinphi2).
    unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); [lia|].
    split; [lia|].
    assert (3 <= (ACtlCutP.flen cx j + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (HinIN3 : 0 < ACtlCut.c_n cx ->
            In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn. destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hin. }
  assert (INK : Lib.Mem.bytes_at segs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
                Lib.Mem.bytes_at segs mem2 (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { intros Hb.
    apply (f6g_bytes_keep_in mem3 mem2 _ _ (ACtlCut.c_p cx) (ACtlCut.c_p cx + ACtlCut.c_n cx)); [|lia|lia|exact Hb].
    intros x Hx. assert (Hn : 0 < ACtlCut.c_n cx) by lia.
    apply (KB _ _ x (HinIN3 Hn)).
    unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (INA : A.AsanRT.addressable mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
                A.AsanRT.addressable mem2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Ha. destruct (Z.eq_dec (ACtlCut.c_n cx) 0) as [E0|Hn].
    - apply (f6g_addr_keep mem3 mem2); [intros i Hi; lia | exact Ha].
    - destruct Ha as (Hp0 & Hn0 & _).
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
               (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR2); [rewrite Hbl2; apply HinIN3; lia | lia | lia |].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  (* KIND_NAME's 112 bytes (KIND_NAME = 0x9e760): a non-owned image range.  Not-owned is decided by a boolean
     search over the bundle's owned-static table (true on the planning core and on the record AF0m.v), so the step
     does not depend on the table's order or shape. *)
  assert (HKNl : (length A.Prog.reac_ctrl_kind_name_c.kind_name_bytes <= 112)%nat) by (vm_compute; lia).
  assert (KKN : forall a, A.Prog.reac_ctrl_kind_name_c.KIND_NAME <= a < A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 ->
            Lib.Mem.mrd segs mem2 (Lib.Mem.wa a) = Lib.Mem.mrd segs mem3 (Lib.Mem.wa a)).
  { intros a Ha.
    assert (Hown : forallb (fun r : Z * Z => (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 <=? fst r) ||
                                             (fst r + snd r <=? A.Prog.reac_ctrl_kind_name_c.KIND_NAME))
                     A.AF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
    unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME in Ha, Hown.
    assert (Himg : lib.Reusable.YG0d.in_img segs a) by (apply A.Prog.CtrlImg.ctrl_relro_img; lia).
    apply KC.
    - destruct (A.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia.
    - rewrite (Lib.Mem.wa_unsigned a ltac:(lia)). right. right. left. split; [exact Himg|]. split.
      + rewrite (A.AF0m.ts_owned _ TFIB_SYMS). intros Hex. apply Exists_exists in Hex.
        destruct Hex as (r & Hr & Hz). rewrite forallb_forall in Hown. specialize (Hown r Hr).
        unfold lib.Reusable.YG0n.in_zr in Hz.
        apply orb_prop in Hown as [Ho|Ho]; apply Z.leb_le in Ho; lia.
      + rewrite (A.AF0m.ts_errno _ TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO. lia. }
  (* the bytes the exit body reads, by class: the stack above the callee's window, the frame, the frame's shadow *)
  assert (BK : forall a bs, Lib.Mem.bytes_at segs mem3 a bs ->
            (sp <= a /\ a + Z.of_nat (length bs) <= ACtlCut.c_sp cx) \/
            (fr <= a /\ a + Z.of_nat (length bs) <= fr + 4096) \/
            (lib.Reusable.YG0f.shadow_addr fr <= a /\
             a + Z.of_nat (length bs) <= lib.Reusable.YG0f.shadow_addr fr + 512) ->
            Lib.Mem.bytes_at segs mem2 a bs).
  { intros a bs Hb [Hc|[Hc|Hc]].
    - apply (f6g_bytes_keep_in mem3 mem2 a bs sp (ACtlCut.c_sp cx) KS); [lia | lia | exact Hb].
    - apply (f6g_bytes_keep_in mem3 mem2 a bs fr (fr + 4096) KF); [lia | lia | exact Hb].
    - apply (f6g_bytes_keep_in mem3 mem2 a bs (lib.Reusable.YG0f.shadow_addr fr)
               (lib.Reusable.YG0f.shadow_addr fr + 512) KFS); [lia | lia | exact Hb]. }
  (* the exit cut *)
  apply (HX cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - (* journal: the post's own *)
    exact HJ2.
  - (* frames *)
    rewrite HF2. exact HF.
  - (* frame law *)
    exact HL.
  - (* event bound *)
    exact Hk.
  - (* the exit body, C_A81f64_at at [j] *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81f64_at].
    split; [reflexivity|]. rewrite Ej.
    split.
    { (* FRAC at the exit's map and memory: each conjunct of the entry's FRAC moved generically, whatever the
         number of conjuncts (registers through the K equalities, memory bytes through the kept classes BK), so an
         appended frame-word conjunct (e.g. a trailer word at fr + 4088, inside the frame) moves the same way *)
      pose proof HFRAC as HF0. unfold ACtlCutP.FRAC in HF0 |- *.
      destruct HF0 as (A0 & sp0 & HF0). exists A0, sp0.
      repeat match type of HF0 with _ /\ _ => let Hh := fresh "Hf" in destruct HF0 as [Hh HF0] end.
      unfold ACtlCutP.q64 in *.
      repeat match goal with |- _ /\ _ => split end;
        first
          [ assumption
          | (rewrite ?K2, ?K3, ?K4, ?K8, ?K9, ?K19, ?K26; assumption)
          | (unfold lib.Reusable.YG0d.spZ; rewrite K2; assumption)
          | (unfold ACtlCut.rgv; rewrite ?K2, ?K3, ?K4, ?K8, ?K9, ?K19, ?K26; assumption)
          | (eapply BK; [eassumption | rewrite ?Lib.Mem.length_le8, ?Lib.Mem.length_le4, ?Lib.Mem.length_le2; lia])
          | (eapply BK; [eassumption | unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?Lib.Mem.length_le8;
                                      cbn [length Nat.add]; lia])
          | (match goal with
             | H : exists sh, Lib.Mem.bytes_at _ mem3 ?a sh /\ _ |- exists sh, Lib.Mem.bytes_at _ mem2 ?a sh /\ _ =>
                 let s := fresh "sh" in let Hs1 := fresh "Hs" in let Hs2 := fresh "Hs" in
                 destruct H as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
                 eapply BK; [exact Hs1 | rewrite Hs2, ESfr; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES; lia]
             end)
          | lia ]. }
    unfold ACtlCutP.b5_body. exists phi. cbv beta.
    split; [rewrite Hbl2; exact HPerm|].
    split; [exact Hcn|]. split; [exact Hj255|].
    split.
    { (* HB: the record block's shadow, from the post's AR *)
      destruct HHB as (Hphi0 & _). split; [exact Hphi0|]. rewrite <- Ereq.
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 phi (ACtlCutP.flen cx j) phi
               (lib.Reusable.YG00.req_size (ACtlCutP.flen cx j)) HAR2 Hinphi2); [lia | | lia].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
    split.
    { (* FLSI *)
      destruct HFLSI as ((HPRO & S128 & HSTK & S144 & HAD2691) & S216 & S224 & S248 & (HINa & HINb) & HFLC).
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & HAD2624 & HINb' & HINa' &
        P184 & P256 & P264 & P272 & P32).
      destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & HADfg & HAD2688 & C72 & C64 & C56 &
        C48).
      split; [split; [|split; [|split; [|split]]]|].
      - (* PRO *)
        split; [refine (SPK _ _ _ _ P40); lia|].
        split; [refine (SPK _ _ _ _ P120); lia|].
        split; [refine (SPK _ _ _ _ P136); lia|].
        split; [refine (SPK _ _ _ _ P160); lia|].
        split; [refine (SPK _ _ _ _ P168); lia|].
        split; [refine (SPK _ _ _ _ P176); lia|].
        split; [refine (SPK _ _ _ _ P208); lia|].
        split; [refine (SPK _ _ _ _ P248); lia|].
        split; [refine (FA _ _ _ _ _ HAD2624); lia|].
        split; [exact (INK HINb')|].
        split; [intros Hn; exact (INA (HINa' Hn))|].
        split; [refine (SPK _ _ _ _ P184); lia|].
        split; [refine (SPK _ _ _ _ P256); lia|].
        split; [refine (SPK _ _ _ _ P264); lia|].
        split; [refine (SPK _ _ _ _ P272); lia|].
        refine (SPK _ _ _ _ P32); lia.
      - refine (SPK _ _ _ _ S128); lia.
      - (* the frame's presence, from the post's AR *)
        destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2
                    ltac:(rewrite HF2; exact Hin6)) as (_ & _ & HFb2 & _).
        assert (Efa2 : lib.Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr).
        { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr.
          destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). first [rewrite EF | rewrite <- EF]; reflexivity. }
        rewrite Efa2 in HFb2. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in HFb2.
        unfold ACtlCutP.FRAME_BYTES.
        apply (f6g_stk_of_present (lib.Reusable.YA0n.w_H W2) mem2 fr (fr + 3136)); [lia | lia |].
        intros a Ha. exact (proj1 (HFb2 a ltac:(lia))).
      - refine (SPK _ _ _ _ S144); lia.
      - refine (FA _ _ _ _ _ HAD2691); lia.
      - split; [refine (SPK _ _ _ _ S216); lia|].
        split; [refine (SPK _ _ _ _ S224); lia|].
        split; [refine (SPK _ _ _ _ S248); lia|].
        split; [split; [exact (INA HINa) | exact (INK HINb)]|].
        unfold ACtlCutP.fragb in *.
        split; [refine (SPK _ _ _ _ C256); lia|].
        split; [refine (SPK _ _ _ _ C184); lia|].
        split; [refine (SPK _ _ _ _ C192); lia|].
        split; [refine (SPK _ _ _ _ C80); lia|].
        split; [refine (SPK _ _ _ _ C88); lia|].
        split; [refine (SPK _ _ _ _ C96); lia|].
        split; [refine (SPK _ _ _ _ C272); lia|].
        split; [refine (SPK _ _ _ _ C264); lia|].
        split; [refine (FA _ _ _ _ _ HADfg); lia|].
        split; [refine (FA _ _ _ _ _ HAD2688); lia|].
        split; [refine (SPK _ _ _ _ C72); lia|].
        split; [refine (SPK _ _ _ _ C64); lia|].
        split; [refine (SPK _ _ _ _ C56); lia|].
        refine (SPK _ _ _ _ C48); lia. }
    split.
    { (* LK *)
      destruct HLK as (HjL & R21 & HOUR). split; [exact HjL|].
      split; [unfold ACtlCut.rgv in *; rewrite K21; exact R21|].
      unfold ACtlCutP.OURb in *. refine (FK _ _ _ _ HOUR); [lia|].
      rewrite A.Prog.SlotModel.OUR_length. cbn. lia. }
    split.
    { (* b5_C *)
      split; [unfold ACtlCut.rgv in *; rewrite K23; exact R23|].
      split; [unfold ACtlCut.rgv in *; rewrite K18; exact R18|].
      split.
      { exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [exact HA1|].
        destruct HSPILL as (Q248 & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 & Q264).
        split; [|refine (QK _ _ _ _ Q232); lia].
        split; [refine (QK _ _ _ _ Q248); lia|].
        split; [refine (QK _ _ _ _ Q256); lia|].
        split; [refine (QK _ _ _ _ Q144); lia|].
        split; [refine (QK _ _ _ _ Q184); lia|].
        split; [refine (QK _ _ _ _ Q192); lia|].
        split; [refine (QK _ _ _ _ Q80); lia|].
        split; [refine (QK _ _ _ _ Q88); lia|].
        split; [refine (QK _ _ _ _ Q96); lia|].
        split; [refine (QK _ _ _ _ Q272); lia|].
        refine (QK _ _ _ _ Q264); lia. }
      split.
      { (* b5_PH *)
        destruct HPH as (HPHb & HPHp). split.
        - intros Hn. refine (RK _ _ _ _ (HPHb Hn)); [lia|].
          rewrite (A.Prog.Seg.F6.f6_tg_len (ACtlCut.c_in cx) j). cbn. lia.
        - intros Hn. unfold lib.Reusable.YG0d.spZ. rewrite K2. exact (HPHp Hn). }
      split.
      { (* b5_FR *)
        destruct HFR as (HFRa1 & HFRa2 & HFRb & HFRl). unfold ACtlCutP.fragb in *.
        split; [refine (FA _ _ _ _ _ HFRa1); lia|].
        split; [refine (FA _ _ _ _ _ HFRa2); lia|].
        split; [refine (FK _ _ _ _ HFRb); [lia | rewrite HFRl; cbn; lia]|].
        exact HFRl. }
      split.
      { (* b5_KN: KIND_NAME's bytes (a non-owned image range) and its shadow (a zero-shadow global row of the
           bundle, found by value: a boolean search true on the planning core and on the record AF0m.v) *)
        destruct HKN as (HKNb & HKNa). split.
        - apply (f6g_bytes_keep_in mem3 mem2 _ _ A.Prog.reac_ctrl_kind_name_c.KIND_NAME
                   (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112) KKN); [lia | lia | exact HKNb].
        - assert (Hzs : existsb (fun r : Z * Z => (fst r <=? A.Prog.reac_ctrl_kind_name_c.KIND_NAME) &&
                                   (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 <=? fst r + 8 * (snd r / 8)))
                          A.AF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
          apply existsb_exists in Hzs as (r & Hr & Hb). apply andb_prop in Hb as (Hb1 & Hb2).
          apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
          apply (A.ProgWorldShadow.ctl_zshadow_of_AR B LAWS ly2 S2 W2 mem2 md2 r A.Prog.reac_ctrl_kind_name_c.KIND_NAME
                   112 HAR2); [rewrite (A.AF0m.ts_zsh _ TFIB_SYMS); exact Hr | exact Hb1 | lia | exact Hb2]. }
      split.
      { (* FGj *)
        destruct HFG as (HFGb & HFGo). split; [|exact HFGo]. unfold ACtlCutP.FGBe in *.
        pose proof HFR as (_ & _ & _ & HFRl).
        refine (FK _ _ _ _ HFGb); [lia | rewrite HFRl; cbn; lia]. }
      (* FSj *)
      destruct HFS as (F104 & F112 & HFSb & HFSa & HFSI).
      split; [refine (SPK _ _ _ _ F104); lia|].
      split; [refine (SPK _ _ _ _ F112); lia|].
      split; [refine (FK _ _ _ _ HFSb); [lia|]|].
      { pose proof (A.Prog.Seg.F6.f6_fs_body_len (ACtlCut.c_in cx) j) as Hl. lia. }
      split; [refine (FA _ _ _ _ _ HFSa); lia | exact HFSI]. }
    (* the stage's own conjuncts *)
    split.
    { (* b5_K *)
      split; [unfold ACtlCut.rgv in *; rewrite K20; exact R20|].
      split; [unfold ACtlCut.rgv in *; rewrite K22; exact R22|].
      split; [unfold ACtlCut.rgv in *; rewrite K24; exact R24|].
      split; [unfold ACtlCut.rgv in *; rewrite K25; exact R25|].
      split.
      { destruct SP280 as (A2 & R9b & HA2 & Q280). rewrite (AEQ A2 R9b HA2) in Q280.
        exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [lia|].
        refine (QK _ _ _ _ Q280); lia. }
      split; [|exact Hra].
      unfold ACtlCutP.u32 in *. refine (FK _ _ _ _ U176); [lia | rewrite Lib.Mem.length_le4; lia]. }
    split.
    { (* a0 = the parse result: SlotModel.t_k is fst (ctrlparse flen (t_g ..)) by definition *)
      unfold ACtlCut.rgv. exact HR10. }
    split.
    { (* IDj *)
      destruct HIDj as (HIDb & HIDo). split; [|exact HIDo]. unfold ACtlCutP.IDBe in *.
      refine (FK _ _ _ _ HIDb); [lia | rewrite A.Prog.Seg.F6.f6_tID_len; cbn; lia]. }
    split.
    { (* b5_F17 *)
      destruct HF17 as (A2 & R9b & HA2 & Q200). rewrite (AEQ A2 R9b HA2) in Q200.
      exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [lia|].
      refine (QK _ _ _ _ Q200); lia. }
    split.
    { (* b5_W240 *)
      destruct HW240 as (A2 & R9b & HA2 & (w240 & Q240 & Hw)). rewrite (AEQ A2 R9b HA2) in Q240.
      exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [lia|].
      exists w240. split; [refine (QK _ _ _ _ Q240); lia | exact Hw]. }
    (* b5_PF: the byte lists of unbounded length are cut to the bytes they name *)
    destruct HPF as (A2 & R9b & HA2 & HPFa & HPFb). pose proof (AEQ A2 R9b HA2) as EA2. subst A2.
    exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [lia|].
    assert (Htphi : (length (A.Prog.SlotModel.t_phi (ACtlCut.c_in cx) j) <= Z.to_nat (ACtlCutP.flen cx j))%nat).
    { unfold ACtlCutP.flen, A.Prog.SlotModel.t_phi, A.Prog.SlotModel.t_len, A.Prog.SlotModel.f_phi.
      rewrite length_firstn. lia. }
    split.
    { intros Hn. destruct (HPFa Hn) as ((rb & Hrb & Hrbl) & Hphb). split.
      - exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
        refine (RK _ _ _ _ (f6g_bytes_firstn _ _ _ _ Hrb)); [lia | rewrite length_firstn; lia].
      - refine (RK _ _ _ _ Hphb); lia. }
    intros H8819.
    assert (Hbig : 50 <= ACtlCutP.flen cx j).
    { unfold A.Prog.SlotModel.t_8819, A.Prog.SlotModel.t_big in H8819.
      apply andb_prop in H8819 as (H8819 & _). apply andb_prop in H8819 as (H8819 & _).
      apply Z.leb_le in H8819. exact H8819. }
    destruct (HPFb H8819) as ((f16 & v14 & v15 & v16 & v17 & U196 & B14 & B15 & B16 & B17 & Hv14 & Hv15 & Hv16 &
      Hv17 & S14 & S15 & S16 & S17 & Hf16 & Hk1) & (ls & rs & Q72 & Hls & Hlsl & Hrs & Hrsl & Hcmp & HAD186) &
      (ls2 & rs2 & Q64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & HAD180)).
    assert (Hphi8 : phi mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (SHK : forall d, 14 <= d < 18 ->
              ACtlCutP.b8 mem3 (Z.shiftr (phi + d) 3 + A.ACtlK.ASAN_K) 0 ->
              ACtlCutP.b8 mem2 (Z.shiftr (phi + d) 3 + A.ACtlK.ASAN_K) 0).
    { intros d Hd Hb. unfold ACtlCutP.b8 in *.
      rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *.
      assert (Ei : (phi + d) / 8 + A.ACtlK.ASAN_K =
                   lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + (d / 8)).
      { unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, A.ACtlK.ASAN_K, A.AsanRT.ASAN_K.
        Z.div_mod_to_equations. lia. }
      rewrite Ei in Hb |- *.
      apply (f6g_bytes_keep_in mem3 mem2 _ _ (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + d / 8)
               (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + d / 8 + 1)); [|lia|cbn; lia|exact Hb].
      intros x Hx. replace x with (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF phi + d / 8) by lia.
      destruct (RSK (d / 8) ltac:(Z.div_mod_to_equations; lia)) as [E|E]; [exact E | lia]. }
    split.
    { exists f16, v14, v15, v16, v17.
      unfold ACtlCutP.u16, ACtlCutP.b8 in U196, B14, B15, B16, B17 |- *.
      split; [refine (FK _ _ _ _ U196); [lia | rewrite Lib.Mem.length_le2; lia]|].
      split; [refine (RK _ _ _ _ B14); [lia | cbn; lia]|].
      split; [refine (RK _ _ _ _ B15); [lia | cbn; lia]|].
      split; [refine (RK _ _ _ _ B16); [lia | cbn; lia]|].
      split; [refine (RK _ _ _ _ B17); [lia | cbn; lia]|].
      do 4 (split; [assumption|]).
      split; [exact (SHK 14 ltac:(lia) S14)|].
      split; [exact (SHK 15 ltac:(lia) S15)|].
      split; [exact (SHK 16 ltac:(lia) S16)|].
      split; [exact (SHK 17 ltac:(lia) S17)|].
      split; [exact Hf16 | exact Hk1]. }
    split.
    { exists (firstn 6 ls), (firstn 6 rs).
      split; [refine (QK _ _ _ _ Q72); lia|].
      split; [refine (FK _ _ _ _ (f6g_bytes_firstn _ _ _ _ Hls)); [lia | rewrite length_firstn; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [refine (RK _ _ _ _ (f6g_bytes_firstn _ _ _ _ Hrs)); [lia | rewrite length_firstn; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f6g_memcmp_firstn; exact Hcmp|].
      refine (FA _ _ _ _ _ HAD186); lia. }
    exists (firstn 6 ls2), (firstn 6 rs2).
    split; [refine (QK _ _ _ _ Q64); lia|].
    split; [refine (FK _ _ _ _ (f6g_bytes_firstn _ _ _ _ Hls2)); [lia | rewrite length_firstn; lia]|].
    split; [rewrite length_firstn; lia|].
    split; [refine (RK _ _ _ _ (f6g_bytes_firstn _ _ _ _ Hrs2)); [lia | rewrite length_firstn; lia]|].
    split; [rewrite length_firstn; lia|].
    split; [rewrite f6g_memcmp_firstn; exact Hcmp2|].
    refine (FA _ _ _ _ _ HAD180); lia.
  - (* ctl_rt_C: from the post's AR (the call writes runtime cells) *)
    apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2).
    apply (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI); [| lia | lia].
    exact (f6g_aro_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HARO).
Qed.

End GlueF6ebc.
