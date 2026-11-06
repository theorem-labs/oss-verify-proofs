(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v, with its numbers changed; 2171 of its 2324 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R10.v, with its module paths changed; 731 of its 781 lines of code are new or changed and 2274 lines of the source are left out. *)
(* lib/A/ACtlG/F3.v -- GLUE for stage seg_F3 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v seg_F3, W piece W4a): the frame turn's first reac_ctrl_parse call, at 0x81df8.  Written by
   a Theorem Labs lane (brief stage-parse-sites.md (a working note, not in this delivery)); single writer.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_F3 : forall POST (j : nat),
       CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dd0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F3 (ACtl.v blob 84ef756918c).  Segment F3 is 0x81dd0 -> 0x81dfc (Seg/F3.v:1-11): addi s9,s7,18 and the five
   frame-shadow stores sb 22..26(s3) (0 0 0 0 4: the 36 output cells [fr + 176, fr + 212) become addressable),
   mv a0,s7 ; mv a1,s2 ; ld a2,248(s1) (a2 = o = fr + 176) ; jal reac_ctrl_parse; return point 0x81dfc = the exit cut.

   THE ROUTE (a Theorem Labs lane 03:56Z): the walk applies a Theorem Labs lane's cgif-form treac_ctrl_parse_spec at the jal, cited as
   the named Section hypothesis TPARSE (a working branch 621a4ba64dc, REAC_CTRL_PARSE_STK = 8800:
   the walk's 32768-byte LLVMF_STK window holds the callee's 8800 below sp).  Before the call, two lifted
   runs: F3F.f3_st_F (a Theorem Labs lane's _F, 0x81dd0 -> 0x81dec, writes the five shadow bytes) and this lane's narrowed
   pre stretch F3Fs.f3_calln_pre_Fs (0x81dec -> the callee entry 0x83578 with ra = 0x81dfc; reads [A + 248, A + 256)),
   the split of F3.f3_calln granted by a Theorem Labs lane 04:01Z (F3Fs.v, commit c210c16fa5d).  There is no stretch after
   the call: TPARSE's post at the return point is the exit cut's configuration.  reac_ctrl_parse_contract(_F) is NOT
   used.

   THE PROOF
   G1  unfold the entry cut C_A81dd0_at: FRAC and b5_body (HB, FLSI, LK, b5_C, FC, the 22 / t_phi facts, IDj).
   G2  the owned frame (frame law + layout_le's ly_F: frame_addr ly3 6 pos = fr; AR_frames_law: frame bytes and the
       frame shadow present and visible; frames_bounds), the record block (Permutation of the live list,
       AR_blocks_law), the stack (FRAC; astk_ok puts the window above alloc_ceiling), the spill base A.
   G3  ProgBridge.cfg_at_MS, the walk moved to f3_st_F's explicit start map (YA0nR.SRr_xregs_eqv,
       Regs6ss.mkR_eqv_of with FRAC's sp / A / s3 and b5_C's s2 / s7).
   G4  lift f3_st_F at RNG_W (w_H W3) with SRr_fevt_hid (its rng premise and wr_at from the frame shadow's presence),
       the journal across it by ProgWorld.ajournal_of_fsteps (its five writes are frame-shadow bytes of the owned
       frame: awr_byte's in_frames case); then lift f3_calln_pre_Fs (its read [A + 248] from FLSI's spill 248, kept
       by f3_st_F's munch, through F3Fs.f3s_q64_ov; rng from the journal's stack presence), the journal across it
       (no write).
   P   TPARSE at the callee entry (YA0n.SRr_bind): STK := LLVMF_STK, sp0 := c_sp cx, FP := [], own := own6,
       lyc / Sc / W / memc := ly3 / S3 / W3 / m1, f := phi, n := flen, o := fr + 176, fr := SlotModel.t_g.  Its caller
       duties (spec-draft section 4, P6 dropped by R5): P1 the journal (G4); P2 arodata_okS kept by the journal
       (F6_ebc.f6g_aro_journal, FP = []); P3 ra = 0x81dfc; P4 gp from the entry, tp from FRAC; P5 the argument
       registers; P7 the stack (FRAC); P8 no class-1 frame (frames S3 = own6); P9 the record block in the live list;
       P10 the output cells inside the owned frame, 8-aligned, addressable in the view from the five shadow bytes
       (f3g_raddr_out); P11 the output cells are owned-frame bytes (awr_byte's in_frames case); P12 / P13 the record
       frame t_g at phi (b5_PH, untouched by f3_st_F, read through ProgWorld.aview_vis_mrd).
   G5  TPARSE's post, the exit cut's ctl_from at the same cx, fr, k:
         journal  the post's own (same own6, same k); frames S2 = frames S3 = own6; frame law and k bound unchanged;
         body     registers: aregs_preserved keeps every callee-saved register the body reads (s9 = phi + 18 from
                  f3_st_F); a0 = fst (ctrlparse flen (t_g ..)) = SlotModel.t_k by definition; memory: every byte the
                  body reads is of a class TPARSE's acall_kept keeps (ProgWorld.ctl_post_acall_kept), composed with
                  f3_st_F's munch (the stack above the callee window, the owned frame off [fr + 176, fr + 212) and
                  its shadow, live heap blocks, the non-owned image bytes of KIND_NAME); the frame shadow's existential
                  list and the frame's presence from the post's AR_frames_law; FRAC's last conjunct (batch 3), the
                  fake-frame trailer word q64 at fr + 4088, from the owned-frame class; the live blocks' shadow from the
                  post's AR (ProgWorldShadow.ctl_block_shadow_of_AR), KIND_NAME's shadow from its zero-shadow row
                  (ProgWorldShadow.ctl_zshadow_of_AR); the new facts from the parse output: the u32 kind at
                  fr + 176 (F3.f3_c7 over the 36 output bytes read through mrd_of_aview_some) and b5_PF
                  (F3.f3_pf_fields / F3.f3_pf_cmp over the output, the record frame at phi, and the output cells'
                  addressability F3.f3_addr_o from the five shadow bytes, kept by the call);
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR (the call writes runtime cells and the post's
                  state is not the entry's), with the post's arodata view (f6g_aro_journal from the entry); route (C),
                  L3-recipe.md section 2(d) (a working note, not in this delivery).
   TABLE VALUES (a Theorem Labs lane 05:52Z): two steps read the start-up tables, and neither picks a list position: KIND_NAME's
   112 bytes avoid Tfib_owned_static (OWB, a forallb decided by vm_compute) and lie in a Tfib_zero_shadow row (ZSB,
   an existsb decided by vm_compute).  Both booleans are true on the planning core this file type-checks against and
   on the RECORD AF0m (a working branch e56483f863b, lines 2955-2981: the covering row is
   (0x21aa0, 0x9e7d0 - 0x21aa0), and the owned row (0x9e7d0, 0x30) starts at KIND_NAME + 112), checked by a script.

   SECTION HYPOTHESES (exact text below)
   - ACtl.v's own: RELRO_IMG, LAWS, TFIB_SYMS (same names and texts as ACtl.v's Section Ctl).
   - TPARSE: a Theorem Labs lane's parse spec of record, the route's named callee hypothesis.
   - none for the exit's runtime conjunct: route (C) (L3-recipe.md (a working note, not in this delivery)) takes ctl_rt_C from the post's AR by
     A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither A.ProgWorld.AR_states_vis0_shadow nor
     AR_states_owned_ro, so the former Section hypotheses VIS0 / OWNED_RO are gone.

   HELPERS: this file's f3g_* lemmas are stage-local; the generic ones are a Theorem Labs lane's, Required from
   lib/A/ACtlG/F6_ebc.v (a working branch 072e322f65a) and cited as A.ACtlG.F6_ebc.f6g_* until they move
   to the kit (a Theorem Labs lane's instruction); none is copied.

   SIX TWIN MODULES (porter a Theorem Labs lane 04:24Z / 04:33Z): YI04 / YI16 / YK11 / YK1b / YM05 / YO09 are named only
   through the aliases CK / CM / CO of their core copies' full paths; their Require lines name full paths.

   CLOSURE (glue closure rule): every project Require is qualified; the _F files Seg/F3F.v and Seg/F3Fs.v bring
   Seg/F3.v and the frame route of record into the closure (rule 1).

   BUILD STATE (honest): on the glue base (planning core) a TYPE-CHECK WITH STAND-INS on the cb packed base
   23b918fe0c2e (the closure reaches the planning core's lib/A/AE2k.v, AF0m.v, AF0l.v, whose undefined
   port_core_refused_<hex> names the build workspace replaces by the hex literal, never on the branch); on
   a working branch (this branch merged with the interim core 5da74c9c931, which has none) a type-check
   whose closure reaches no stand-in.  No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG00 YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YE01 YK04 YK04R YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRt A.ProgWorldShadow.
(* route (C): the narrowed cut conjunct and its producer from AR (no VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.C_reac_ctrl_parse A.Prog.CtrlImg A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F3 A.Prog.Seg.F3F A.Prog.Seg.F3Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Spec.StrFun Prog.RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.F6_ebc.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Import ListNotations.
Local Open Scope Z_scope.

Module CK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module PS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parse.

Local Notation segs := A.AB1v.tfibsegs.

Section GlueF3.
Context {fx : CK.FPState} {rc : CM.RunCeil} {LS : CO.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v's own Section hypotheses (ACtl.v Section Ctl), same names and texts. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img segs a.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81dd0_at := (A.ACtlCutP.C_A81dd0_at B).
Local Notation C_A81dfc_at := (A.ACtlCutP.C_A81dfc_at B).

(* The cgif-form parse spec of record, at the call (the route of a Theorem Labs lane 03:56Z). *)
Hypothesis TPARSE : PS.treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
(* route (C): VIS0 / OWNED_RO (ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) are GONE: the exit's ctl_rt_C
   comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* The 36 output cells [fr + 176, fr + 212) are addressable in the core's view once the five frame-shadow bytes
   Sfr fr + 22 .. 26 hold 0 0 0 0 4 (f3_st_F's post) and are visible: P10 of the parse spec. *)
Lemma f3g_raddr_out : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) fr,
  0 <= fr -> fr mod 32 = 0 ->
  A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (A.Prog.SlotInv.Sfr fr + 22) 5 ->
  LMe.bytes_at A.Img0.rsegs m (A.Prog.SlotInv.Sfr fr + 22)
    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF (fr + 176) 36.
Proof.
  intros W m fr Hfr0 Hfr32 (_ & _ & Hvis) (_ & _ & Hb) x Hx.
  assert (Ek : lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x =
               A.Prog.SlotInv.Sfr fr + 22 + ((x - fr) / 8 - 22)).
  { unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, A.Prog.SlotInv.Sfr,
      A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (Hk : 0 <= (x - fr) / 8 - 22 < 5) by (Z.div_mod_to_equations; lia).
  rewrite Ek.
  set (y := A.Prog.SlotInv.Sfr fr + 22 + ((x - fr) / 8 - 22)).
  assert (Hy : A.Prog.SlotInv.Sfr fr + 22 <= y < A.Prog.SlotInv.Sfr fr + 22 + 5) by (unfold y; lia).
  rewrite (A.ProgWorld.aview_vis_mrd W m y (Hvis y Hy)).
  pose proof (Hb (Z.to_nat ((x - fr) / 8 - 22)) ltac:(cbn [length]; lia)) as Hbk.
  rewrite Z2Nat.id in Hbk by lia. unfold LMe.wa in Hbk. fold y in Hbk.
  rewrite Hbk.
  assert (Hc : (x - fr) / 8 - 22 = 0 \/ (x - fr) / 8 - 22 = 1 \/ (x - fr) / 8 - 22 = 2 \/
               (x - fr) / 8 - 22 = 3 \/ (x - fr) / 8 - 22 = 4) by lia.
  destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn [Z.to_nat Pos.to_nat nth_error option_map];
    eexists; (split; [reflexivity|]); unfold lib.Reusable.YG0v.saddr_ok.
  1-4: left; reflexivity.
  right. change (bv_unsigned (Z_to_bv 8 4)) with 4. Z.div_mod_to_equations. lia.
Qed.


(* Present bytes are visible and writable (the frame shadow f3_st_F writes, from the AR frame law). *)
Lemma f3g_pres_wr_vis : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) lo n,
  0 <= lo -> lo + n <= 2 ^ 64 ->
  (forall a, lo <= a < lo + n -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a) ->
  A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo n /\ LMe.wr_at A.Img0.rsegs m lo n.
Proof.
  intros W m lo n Hlo Hhi Hp. split.
  - split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha. exact (proj1 (Hp a Ha)).
  - split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    destruct (Hp (lo + i) ltac:(lia)) as [_ [b Hb]].
    unfold LMe.wa. unfold wview. rewrite Hb. discriminate.
Qed.

(* Bytes outside a run's write list are the same after the run (Lib.Frame.munch). *)
Lemma f3g_bytes_munch : forall W (m m' : word -> option byte) a (bs : list byte),
  LMe.bytes_at A.Img0.rsegs m a bs -> LFr.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> LFr.outside W x) -> LMe.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) MU HO. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  rewrite <- (H i Hi). unfold LMe.mrd. rewrite (MU (LMe.wa (a + Z.of_nat i))); [reflexivity|].
  rewrite LMe.wa_unsigned by lia. apply HO. lia.
Qed.

(* A range of k present bytes holds some byte list of length k (the frame shadow's existential in FRAC). *)
Lemma f3g_bytes_of_present : forall (m : word -> option byte) a (k : nat),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, (i < k)%nat -> exists b, LMe.mrd A.Img0.rsegs m (LMe.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, LMe.bytes_at A.Img0.rsegs m a bs /\ length bs = k.
Proof.
  intros m a k Ha Hk Hp.
  exists (map (fun i => match LMe.mrd A.Img0.rsegs m (LMe.wa (a + Z.of_nat i)) with
                        | Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  split; [|rewrite length_map, length_seq; reflexivity].
  split; [exact Ha|]. split; [rewrite length_map, length_seq; exact Hk|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  assert (E : nth_error (seq 0 k) i = Some i).
  { rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. reflexivity. }
  rewrite (map_nth_error _ _ _ E). destruct (Hp i Hi) as (b & Hb). rewrite Hb. reflexivity.
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma f3g_addr_sub : forall (m : word -> option byte) p n q k,
  A.AsanRT.addressable m p n -> p <= q -> 0 <= k -> q + k <= p + n -> A.AsanRT.addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hqk. split; [lia|]. split; [exact Hk|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

Lemma glue_seg_F3 : forall POST (j : nat),
  CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dd0_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1 *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81dd0_at A.ACtlCutP.ixn nth A.ACtlCutP.b5_body] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HLK & HB5C & HFC & H22 & HPHI & HIDj).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hspc & HcAPP & Q304 & Q24 & Q16 & Qhdr & Qent & Hsh & Hsaved).
  pose proof HB5C as (R23 & R18 & _).
  pose proof HFLSI as (HFLSH & S216 & S224 & S248 & HIN & HFLC).
  (* G2: the journal's AR, the owned frame, the bounds *)
  pose proof HJ as (HAR & Hly & Hsecs & Hwle0 & Hio & Hfrs & Hnev & Hk0 & J1 & J2 & J3 & J4 & J5 & Hpres & Hastk &
    J6 & Hqt).
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfa32 & Hfapp & HfB & HfS).
  rewrite <- Efr3 in Hfa32, Hfapp, HfB, HfS.
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  rewrite <- Efr3 in Hf4096, Hfceil.
  assert (Efb6 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efb6 in HfB, HfS, Hfceil.
  assert (Hphiin : In (phi, A.ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.flen cx j) HAR Hphiin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & HpB & Hpdisj & Hpn).
  pose proof lib.Reusable.YCbq.asan_consts as ((Hceil1 & Hceil2) & _).
  assert (Hphi : 0 <= phi < 2 ^ 64).
  { unfold lib.Reusable.YG00.req_size in Hpceil.
    destruct (A.ACtlCutP.flen cx j =? 0); lia. }
  assert (ESfr : A.Prog.SlotInv.Sfr fr = lib.Reusable.YG0f.shadow_addr fr).
  { unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSfr0 : 0 <= A.Prog.SlotInv.Sfr fr).
  { unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (HSfr27 : A.Prog.SlotInv.Sfr fr + 27 <= 2 ^ 64).
  { unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  pose (RNG := A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)).
  destruct (f3g_pres_wr_vis W3 mem3 (A.Prog.SlotInv.Sfr fr + 22) 5 ltac:(lia) ltac:(lia)) as (Vsh & Wsh).
  { intros a Ha. rewrite ESfr in Ha.
    replace a with (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) by lia.
    apply (HfS (a - lib.Reusable.YG0f.shadow_addr fr)). lia. }
  pose proof (A.ProgBridge.rng_of_visible _ _ _ Vsh) as Rsh.
  (* the stack: [alloc_ceiling + LLVMF_STK, 2 ^ 47) holds c_sp (astk_ok), so every spill cell is high memory *)
  pose proof Hastk as (Hs16 & HSTK0 & Hsc1 & Hsc2 & Hsc3 & Hsc4 & _).
  pose proof (EspZ) as EspZ'. unfold lib.Reusable.YG0d.spZ in EspZ'.
  pose proof (bv_unsigned_in_range 64 (CK.getr regs3 2)) as Hsprng. rewrite EspZ' in Hsprng.
  change (bv_modulus 64) with (2 ^ 64) in Hsprng.
  unfold A.ACfn.LLVMF_STK in Hsc2. unfold A.AsanRT.APPMEM_END in HcAPP.
  unfold A.ACtlCutP.FRAME_BYTES in HfrA.
  (* the spill base of FLSI's spill 248 is FRAC's A *)
  destruct S248 as (A' & R9' & Q248).
  assert (EA' : A' = A).
  { pose proof Q248 as (HQa & HQb & _). unfold A.ACtlCut.rgv in R9, R9'. rewrite R9 in R9'.
    apply (f_equal (@bv_unsigned 64)) in R9'. rewrite !Z_to_bv_unsigned in R9'. unfold bv_wrap in R9'.
    change (bv_modulus 64) with (2 ^ 64) in R9'. rewrite (Z.mod_small A) in R9' by lia.
    Z.div_mod_to_equations. lia. }
  subst A'.
  (* G3: the cut's configuration, moved to the explicit start map of f3_st_F *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc (ix_cut C_A81dd0_at [Z.of_nat j])) with 0x81dd0.
  pose (R0 := LFr.mkR (CK.getr regs3 1) (Z_to_bv 64 sp) (CK.getr regs3 3) (CK.getr regs3 4) (CK.getr regs3 5)
                (CK.getr regs3 6) (CK.getr regs3 7) (CK.getr regs3 8) (Z_to_bv 64 A) (CK.getr regs3 10)
                (CK.getr regs3 11) (CK.getr regs3 12) (CK.getr regs3 13) (CK.getr regs3 14) (CK.getr regs3 15)
                (CK.getr regs3 16) (CK.getr regs3 17) (Z_to_bv 64 (A.ACtlCutP.flen cx j))
                (Z_to_bv 64 (A.Prog.SlotInv.Sfr fr)) (CK.getr regs3 20) (CK.getr regs3 21) (CK.getr regs3 22)
                (Z_to_bv 64 phi) (CK.getr regs3 24) (CK.getr regs3 25) (CK.getr regs3 26) (CK.getr regs3 27)
                (CK.getr regs3 28) (CK.getr regs3 29) (CK.getr regs3 30) (CK.getr regs3 31)).
  assert (HXE : LR6.xregs_eqv R0 regs3).
  { apply LR6.xregs_eqv_sym. unfold R0. apply LR6.mkR_eqv_of;
      first [ exact Esp | exact R9 | exact R18 | exact R19 | exact R23 | reflexivity ]. }
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 R0 regs3 CK.fp_regs (Z_to_bv 64 0x81dd0) CK.fp_csr None mem3
           (CK.seg_rom segs) md3 (POST cx)); [| exact HXE].
  (* G4a: f3_st_F, 0x81dd0 .. 0x81dec (s9 = phi + 18 and the five frame-shadow bytes of the 36 output cells) *)
  pose proof (A.Prog.Seg.F3F.f3_st_F RNG (CK.getr regs3 1) (Z_to_bv 64 sp) (CK.getr regs3 3) (CK.getr regs3 4)
      (CK.getr regs3 5) (CK.getr regs3 6) (CK.getr regs3 7) (CK.getr regs3 8) (Z_to_bv 64 A) (CK.getr regs3 10)
      (CK.getr regs3 11) (CK.getr regs3 12) (CK.getr regs3 13) (CK.getr regs3 14) (CK.getr regs3 15)
      (CK.getr regs3 16) (CK.getr regs3 17) (Z_to_bv 64 (A.ACtlCutP.flen cx j)) (CK.getr regs3 20)
      (CK.getr regs3 21) (CK.getr regs3 22) (CK.getr regs3 24) (CK.getr regs3 25) (CK.getr regs3 26)
      (CK.getr regs3 27) (CK.getr regs3 28) (CK.getr regs3 29) (CK.getr regs3 30) (CK.getr regs3 31)
      CK.fp_regs CK.fp_csr mem3 fr phi Hfr0 HSfr0 Hphi HSfr27 Wsh Rsh) as HRUN1.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN1) as (ms1 & Hrun1 & HP1).
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG (fun ms => ms = ms1) (POST cx)
           (ex_intro _ ms1 (conj Hrun1 eq_refl))).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms1' md1 Ems1' Hhid1 Hsbm1. subst ms1'.
  destruct HP1 as (m1 & a0' & Ems1 & MU1u & WM1 & STK1 & SB1). subst ms1.
  (* f3_st_F states its munch over lib/A/Tk/UL/Frame.v (F3.v's `Frame.`), the journal lemma over lib/Lib/Frame.v:
     the same definition, and on the concrete one-interval list both outside's reduce to the same term *)
  assert (MU1 : LFr.munch (A.Prog.Seg.F3.f3_Wsh fr) mem3 m1) by (intros x Hx; apply MU1u; exact Hx).
  (* the journal across f3_st_F: its five writes are bytes of the owned frame's shadow *)
  assert (HJ1 : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx)
                  [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx)
                  (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k).
  { lazymatch type of Hrun1 with ?F _ _ ?s0 ?s1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 _ _ _ RNG
                (A.Prog.Seg.F3.f3_Wsh fr) HJ Hrun1 (A.ProgBridge.fp_avoids_RNG_W _) MU1 Hsbm1 _) end.
    intros a Ha Hout. unfold A.Prog.Seg.F3.f3_Wsh in Hout. cbn [LFr.outside] in Hout.
    right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3, Efb6, <- ESfr. lia. }
  (* the prologue spill [A + 248, A + 256) still holds o = fr + 176: f3_st wrote frame-shadow bytes only, and the
     whole shadow of the frame lies below the stack *)
  assert (Hsh_hi : lib.Reusable.YG0f.shadow_addr fr + 4096 / 8 <= A).
  { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
  assert (Q248m1 : LMe.bytes_at A.Img0.rsegs m1 (A + 248) (LMe.le8 (Z_to_bv 64 (fr + 176)))).
  { apply (f3g_bytes_munch _ mem3 m1 _ _ Q248 MU1). intros x Hx.
    pose proof (LMe.length_le8 (Z_to_bv 64 (fr + 176))) as L8. rewrite L8 in Hx.
    unfold A.Prog.Seg.F3.f3_Wsh. cbn [LFr.outside]. rewrite ESfr. split; [lia | exact I]. }
  pose proof (A.Prog.Seg.F3Fs.f3s_q64_ov m1 (A + 248) (fr + 176) Q248m1) as HRD.
  destruct (f3g_pres_wr_vis W3 mem3 (A + 248) 8 ltac:(lia) ltac:(lia)) as (V248 & _).
  { intros a Ha. apply Hpres. unfold A.ACfn.LLVMF_STK. lia. }
  pose proof (A.ProgBridge.rng_of_visible _ _ _ V248) as R248.
  (* G4b: f3_calln_pre_Fs, 0x81dec .. the jal: a0 = phi, a1 = flen, a2 = o, ra = 0x81dfc, pc = 0x83578 *)
  pose proof (A.Prog.Seg.F3Fs.f3_calln_pre_Fs RNG (CK.getr regs3 1) (CK.getr regs3 3) (CK.getr regs3 4)
      (CK.getr regs3 5) (CK.getr regs3 6) (CK.getr regs3 7) (CK.getr regs3 8) a0' (CK.getr regs3 11)
      (CK.getr regs3 12) (CK.getr regs3 13) (CK.getr regs3 14) (CK.getr regs3 15) (CK.getr regs3 16)
      (CK.getr regs3 17) (Z_to_bv 64 (A.Prog.SlotInv.Sfr fr)) (CK.getr regs3 20) (CK.getr regs3 21)
      (CK.getr regs3 22) (CK.getr regs3 24) (Z_to_bv 64 (phi + 18)) (CK.getr regs3 26) (CK.getr regs3 27)
      (CK.getr regs3 28) (CK.getr regs3 29) (CK.getr regs3 30) (CK.getr regs3 31) CK.fp_regs CK.fp_csr m1
      A phi (A.ACtlCutP.flen cx j) (fr + 176) sp ltac:(lia) ltac:(lia) HRD R248) as HRUN2.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN2) as (ms2 & Hrun2 & HP2).
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md1 RNG (fun ms => ms = ms2) (POST cx)
           (ex_intro _ ms2 (conj Hrun2 eq_refl))).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms2' md2 Ems2' Hhid2 Hsbm2. subst ms2'. subst ms2.
  (* the journal across the four instructions: they write nothing, the model may materialize *)
  assert (HJ2 : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx)
                  [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx)
                  (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 m1 md2 k).
  { lazymatch type of Hrun2 with ?F _ _ ?s0 ?s1 =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 _ _ _ RNG
                [] HJ1 Hrun2 (A.ProgBridge.fp_avoids_RNG_W _) _ Hsbm2 _) end.
    - apply LFr.munch_refl.
    - intros a _ Hout. exfalso. apply Hout. exact I. }
  (* the callee: a Theorem Labs lane's cgif-form parse spec at its entry (A_reac_ctrl_parseP = 0x83578) *)
  assert (EPC : Z_to_bv 64 A.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE = Z_to_bv 64 PS.A_reac_ctrl_parseP)
    by (f_equal; vm_compute; reflexivity).
  rewrite EPC.
  pose (Rc := LFr.mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 sp) (CK.getr regs3 3) (CK.getr regs3 4) (CK.getr regs3 5)
          (CK.getr regs3 6) (CK.getr regs3 7) (CK.getr regs3 8) (Z_to_bv 64 A) (Z_to_bv 64 phi)
          (Z_to_bv 64 (A.ACtlCutP.flen cx j)) (Z_to_bv 64 (fr + 176)) (CK.getr regs3 13) (CK.getr regs3 14)
          (CK.getr regs3 15) (CK.getr regs3 16) (CK.getr regs3 17) (Z_to_bv 64 (A.ACtlCutP.flen cx j))
          (Z_to_bv 64 (A.Prog.SlotInv.Sfr fr)) (CK.getr regs3 20) (CK.getr regs3 21) (CK.getr regs3 22)
          (Z_to_bv 64 phi) (CK.getr regs3 24) (Z_to_bv 64 (phi + 18)) (CK.getr regs3 26) (CK.getr regs3 27)
          (CK.getr regs3 28) (CK.getr regs3 29) (CK.getr regs3 30) (CK.getr regs3 31)).
  change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs PS.A_reac_ctrl_parseP Rc m1 md2) (POST cx)).
  assert (ERc1 : CK.getr Rc 1 = Z_to_bv 64 0x81dfc) by reflexivity.
  assert (ERc2 : CK.getr Rc 2 = Z_to_bv 64 sp) by reflexivity.
  assert (ERc3 : CK.getr Rc 3 = CK.getr regs3 3) by reflexivity.
  assert (ERc4 : CK.getr Rc 4 = CK.getr regs3 4) by reflexivity.
  assert (ESpRc : lib.Reusable.YG0d.spZ Rc = sp).
  { unfold lib.Reusable.YG0d.spZ. rewrite ERc2, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pose proof HB as ((HAF & _ & _ & _ & HpnIN & HlenIN & _ & _ & _ & _ & HRO0 & _) & _).
  pose proof HAF as (_ & _ & _ & Hgp & _).
  pose proof HB5C as (_ & _ & _ & HPH & _).
  (* geometry: app bytes (frame, blocks) never fall in the five written shadow bytes; the frame's shadow is not a
     frame byte; the stack lies above the frame's shadow *)
  assert (APPSH : forall lo len a, lib.Reusable.YG0f.in_app lo len -> lo <= a < lo + len ->
            a < A.Prog.SlotInv.Sfr fr + 22 \/ A.Prog.SlotInv.Sfr fr + 27 <= a).
  { intros lo len a Hap Ha. unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg,
      lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in Hap.
    unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (SHFR : forall a, lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 512 ->
            ~ (fr <= a < fr + 4096)).
  { intros a Ha Hb. unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg,
      lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in Hfapp.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Ha. Z.div_mod_to_equations. lia. }
  assert (Hsh_sp : lib.Reusable.YG0f.shadow_addr fr + 512 <= sp).
  { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
  (* f3_st_F changed only the five frame-shadow bytes *)
  assert (MUK : forall a, 0 <= a < 2 ^ 64 -> (a < A.Prog.SlotInv.Sfr fr + 22 \/ A.Prog.SlotInv.Sfr fr + 27 <= a) ->
            LMe.mrd segs m1 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros a Ha Hn. unfold LMe.mrd. rewrite (MU1 (LMe.wa a)); [reflexivity|].
    rewrite LMe.wa_unsigned by lia. unfold A.Prog.Seg.F3.f3_Wsh. cbn [LFr.outside]. split; [lia | exact I]. }
  assert (Hreq : lib.Reusable.YG00.req_size (A.ACtlCutP.flen cx j) = A.ACtlK.a_size (A.ACtlCutP.flen cx j)).
  { unfold lib.Reusable.YG00.req_size, A.ACtlK.a_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
  eapply lib.Reusable.YA0n.SRr_bind.
  { refine (TPARSE A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx)
              (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 m1 md2 k
              Rc phi (A.ACtlCutP.flen cx j) (fr + 176) (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j)
              HJ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - (* P2: the entry's read-only view, kept by the journal (FP = []) *)
      exact (A.ACtlG.F6_ebc.f6g_aro_journal B RLO RHI RELRO_IMG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO0).
    - (* P3: ra is the return point *) rewrite ERc1. vm_compute. reflexivity.
    - unfold lib.Reusable.YG0d.raZ. rewrite ERc1, Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
    - (* P4 *) rewrite ERc3. exact (eq_trans R3 Hgp).
    - rewrite ERc4. exact R4.
    - (* P5 *) reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold lib.Reusable.YG00.req_size in Hpceil. destruct (A.ACtlCutP.flen cx j =? 0) eqn:E0;
        [apply Z.eqb_eq in E0; lia | lia].
    - (* P7 *) rewrite ESpRc. exact Hsp16.
    - rewrite ESpRc. unfold PS.REAC_CTRL_PARSE_STK, lib.Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK. lia.
    - rewrite ESpRc. lia.
    - (* P8 *) rewrite HF. vm_compute. reflexivity.
    - (* P9 *) intros H50. exists (A.ACtlCutP.flen cx j). split; [exact Hphiin|].
      unfold lib.Reusable.YG00.req_size. destruct (A.ACtlCutP.flen cx j =? 0) eqn:E50;
        [apply Z.eqb_eq in E50; lia | lia].
    - (* P10: the output cells lie in the owned class-6 frame, marked addressable by f3_st_F's shadow bytes *)
      intros _. split; [|split].
      + exists 6, (A.ACtlCut.c_fpos cx). rewrite <- Efr3, Efb6. split; [exact Hin6|].
        Z.div_mod_to_equations. lia.
      + Z.div_mod_to_equations. lia.
      + exact (f3g_raddr_out W3 m1 fr Hfr0 Hfr32 Vsh SB1).
    - (* P11: the output cells are bytes of the owned frame *)
      intros _ a Ha. right; right; right. exists 6, (A.ACtlCut.c_fpos cx).
      split; [left; reflexivity|]. left. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd].
      rewrite <- Efr3, Efb6. lia.
    - (* P12 *) exact (A.Prog.Seg.F6.f6_tg_len _ _).
    - (* P13: the record frame at phi (b5_PH), untouched by f3_st_F, read through the view *)
      intros Hn i Hi.
      destruct HPH as (HPHb & _). pose proof (HPHb Hn) as (_ & _ & Hg).
      assert (Hil : (i < length (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j))%nat)
        by (rewrite (A.Prog.Seg.F6.f6_tg_len (A.ACtlCut.c_in cx) j); exact Hi).
      assert (Hia : phi <= phi + Z.of_nat i < phi + lib.Reusable.YG00.req_size (A.ACtlCutP.flen cx j)).
      { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
      assert (Hvis : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (phi + Z.of_nat i)) = false).
      { destruct (HpB (phi + Z.of_nat i) Hia) as ((Hv & _) & _). exact Hv. }
      rewrite (A.ProgWorld.aview_vis_mrd W3 m1 (phi + Z.of_nat i) Hvis).
      pose proof (MUK (phi + Z.of_nat i) ltac:(lia) (APPSH _ _ _ Hpapp Hia)) as E1.
      unfold LMe.wa in E1. rewrite A.ProgBridge.tfibsegs_rsegs in E1. rewrite E1.
      pose proof (Hg i Hil) as Hgi. unfold LMe.wa in Hgi. rewrite A.ProgBridge.tfibsegs_rsegs in Hgi.
      rewrite Hgi. rewrite (nth_error_nth' _ lib.Prog.RcParse.cp_z Hil). reflexivity. }
  (* G5: TPARSE's post, back at the return point 0x81dfc = the exit cut *)
  intros W2 c2 Hle2 (ly2 & S2 & regs2 & mem2 & md2' & Ec2 & HJ3 & Hpres2 & Hfr2 & Hab2 & Hff & Ha0 & Hout & Hkept).
  subst c2. rewrite ESpRc in Hkept.
  change (lib.Reusable.YA0n.SRr segs W2 (lib.Reusable.YG0d.cfg_at segs
            (A.ACtlCut.cut_pc (ix_cut C_A81dfc_at [Z.of_nat j])) regs2 mem2 md2') (POST cx)).
  pose proof HJ3 as (HAR2 & Hly2 & _).
  (* the registers the exit body reads: callee-saved, kept by the call (aregs_preserved) *)
  assert (KR : forall r : Z, lib.Reusable.YG0d.acallee_saved r ->
                 CK.getr regs2 (Z_to_bv 5 r) = CK.getr Rc (Z_to_bv 5 r)) by exact Hpres2.
  assert (K2 : CK.getr regs2 2 = CK.getr regs3 2).
  { transitivity (CK.getr Rc 2); [exact (KR 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    rewrite ERc2. symmetry. exact Esp. }
  assert (K3 : CK.getr regs2 3 = CK.getr regs3 3)
    by exact (KR 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K4 : CK.getr regs2 4 = CK.getr regs3 4)
    by exact (KR 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K8 : CK.getr regs2 8 = CK.getr regs3 8)
    by exact (KR 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K9 : CK.getr regs2 9 = CK.getr regs3 9).
  { transitivity (CK.getr Rc 9); [exact (KR 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK.getr Rc 9) with (Z_to_bv 64 A). symmetry. exact R9. }
  assert (K18 : CK.getr regs2 18 = CK.getr regs3 18).
  { transitivity (CK.getr Rc 18); [exact (KR 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK.getr Rc 18) with (Z_to_bv 64 (A.ACtlCutP.flen cx j)). symmetry. exact R18. }
  assert (K19 : CK.getr regs2 19 = CK.getr regs3 19).
  { transitivity (CK.getr Rc 19); [exact (KR 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK.getr Rc 19) with (Z_to_bv 64 (A.Prog.SlotInv.Sfr fr)). symmetry. exact R19. }
  assert (K20 : CK.getr regs2 20 = CK.getr regs3 20)
    by exact (KR 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K21 : CK.getr regs2 21 = CK.getr regs3 21)
    by exact (KR 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K22 : CK.getr regs2 22 = CK.getr regs3 22)
    by exact (KR 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K23 : CK.getr regs2 23 = CK.getr regs3 23).
  { transitivity (CK.getr Rc 23); [exact (KR 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
    change (CK.getr Rc 23) with (Z_to_bv 64 phi). symmetry. exact R23. }
  assert (K25 : CK.getr regs2 25 = Z_to_bv 64 (phi + 18))
    by exact (KR 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K26 : CK.getr regs2 26 = CK.getr regs3 26)
    by exact (KR 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  (* the memory the exit body reads: the classes TPARSE's acall_kept keeps (ProgWorld.ctl_post_acall_kept), each
     composed with f3_st_F's munch *)
  pose proof (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 m1 mem2 _ _ _ Hkept Hle2) as KC.
  assert (KS : forall a, sp <= a < A.ACtlCut.c_sp cx ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros a Ha. rewrite <- (MUK a ltac:(lia) ltac:(right; rewrite ESfr; lia)). apply KC.
    - assert (Hr : A.ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < A.ACtlCut.c_sp cx)
        by (unfold A.ACfn.LLVMF_STK; lia).
      destruct (Hpres a Hr) as [Hv _]. exact Hv.
    - rewrite (LMe.wa_unsigned a ltac:(lia)). left. split; [lia|].
      unfold PS.REAC_CTRL_PARSE_STK, lib.Reusable.YG0d.ESTACK. lia. }
  assert (KSA : forall a, A <= a < A + 416 ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a))
    by (intros a Ha; apply KS; lia).
  assert (KF : forall a, fr <= a < fr + 4096 -> ~ (fr + 176 <= a < fr + 176 + 36) ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros a Ha HE. rewrite <- (MUK a ltac:(lia) (APPSH _ _ _ Hfapp Ha)). apply KC.
    - destruct (HfB a Ha) as ((Hv & _) & _). exact Hv.
    - rewrite (LMe.wa_unsigned a ltac:(lia)). right. right. right.
      exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hin6|]. split; [|exact HE].
      left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr3, Efb6. lia. }
  assert (KFS1 : forall a, lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 512 ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs m1 (LMe.wa a)).
  { intros a Ha.
    assert (Hsa : 0 <= lib.Reusable.YG0f.shadow_addr fr)
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
    apply KC.
    - change (4096 / 8) with 512 in HfS.
      destruct (HfS (a - lib.Reusable.YG0f.shadow_addr fr) ltac:(lia)) as ((Hv & _) & _).
      replace (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) with a in Hv by lia.
      exact Hv.
    - rewrite (LMe.wa_unsigned a ltac:(lia)). right. right. right.
      exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      + right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3, Efb6.
        change (4096 / 8) with 512. lia.
      + intros HE. apply (SHFR a Ha). lia. }
  assert (KFS : forall a, lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 512 ->
            (a < A.Prog.SlotInv.Sfr fr + 22 \/ A.Prog.SlotInv.Sfr fr + 27 <= a) ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros a Ha Hn. rewrite (KFS1 a Ha). apply MUK; [|exact Hn].
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Ha. Z.div_mod_to_equations. lia. }
  assert (KB : forall p n a, In (p, n) (lib.Reusable.YG0d.ablocks B ly3 S3) ->
            p <= a < p + lib.Reusable.YG00.req_size n ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros p n a Hin Ha.
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin)
      as (_ & Hp4096' & Hpceil' & Hpapp' & Hppres & _ & _).
    pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (A.ACtlCut.c_fpos cx)
                  HAR Hin Hin6) as Hsep.
    unfold lib.Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- Efr3, Efb6 in Hsep.
    rewrite <- (MUK a ltac:(lia) (APPSH _ _ _ Hpapp' Ha)). apply KC.
    - destruct (Hppres a Ha) as ((Hv & _) & _). exact Hv.
    - rewrite (LMe.wa_unsigned a ltac:(lia)). right. left.
      exists p, n, (a - p). split; [exact Hin|]. split; [lia|]. split; [lia|]. lia. }
  (* the post's own frame facts (presence of the frame and of its shadow at mem2, visible in W2) *)
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2' 6 (A.ACtlCut.c_fpos cx) HAR2
              ltac:(rewrite Hfr2; exact Hin6)) as (_ & _ & HFb2 & HFs2).
  assert (Efa2 : lib.Reusable.YG0f.frame_addr ly2 6 (A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr.
    destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _). first [rewrite EF2 | rewrite <- EF2]; reflexivity. }
  rewrite Efa2, Efb6 in HFb2, HFs2. change (4096 / 8) with 512 in HFs2.
  (* the transports the exit body uses, by class *)
  assert (HA0 : 0 <= A) by lia.
  assert (HA64 : A + 416 <= 2 ^ 64) by lia.
  assert (AEQ : forall A', A.ACtlCut.rgv regs3 9 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A'' RAy HAy. pose proof R9 as R9y. unfold A.ACtlCut.rgv in RAy, R9y.
    apply (A.ACtlG.F6_ebc.f6g_A_eq A A'' 0); [rewrite <- RAy, <- R9y; reflexivity | lia..]. }
  assert (SPK : forall off v, 0 <= off -> off + 8 <= 416 ->
            A.ACtlCutP.spill regs3 mem3 off v -> A.ACtlCutP.spill regs2 mem2 off v)
    by (intros off v H0 H1 Hs;
        exact (A.ACtlG.F6_ebc.f6g_spill_keep regs3 regs2 mem3 mem2 A off v R9 HA0 HA64 K9 KSA H0 H1 Hs)).
  assert (QK : forall off v, 0 <= off -> off + 8 <= 416 ->
            A.ACtlCutP.q64 mem3 (A + off) v -> A.ACtlCutP.q64 mem2 (A + off) v).
  { intros off v H0 H1 Hq. unfold A.ACtlCutP.q64 in *.
    apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 _ _ A (A + 416) KSA);
      [lia | rewrite LMe.length_le8; lia | exact Hq]. }
  (* frame bytes off the output cells: [fr, fr + 176) and [fr + 216, fr + 4096) *)
  assert (FK : forall a bs, (fr <= a /\ a + Z.of_nat (length bs) <= fr + 176) \/
                            (fr + 216 <= a /\ a + Z.of_nat (length bs) <= fr + 4096) ->
            LMe.bytes_at segs mem3 a bs -> LMe.bytes_at segs mem2 a bs).
  { intros a bs Hr Hb. destruct Hr as [Hr | Hr].
    - apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 a bs fr (fr + 176)); [|lia|lia|exact Hb].
      intros x Hx. apply KF; lia.
    - apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 a bs (fr + 216) (fr + 4096)); [|lia|lia|exact Hb].
      intros x Hx. apply KF; lia. }
  (* addressability of frame ranges from fr + 216 on: their shadow is the frame shadow from byte 27 on *)
  assert (FA : forall p n, fr + 216 <= p -> p + n <= fr + 4096 -> 0 <= n ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable mem2 p n).
  { intros p n H0 H1 H2 Ha. apply (A.ACtlG.F6_ebc.f6g_addr_keep mem3 mem2 p n); [|exact Ha].
    intros i Hi. apply KFS.
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - right. unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (RK : forall a bs, phi <= a -> a + Z.of_nat (length bs) <= phi + A.ACtlCutP.flen cx j ->
            LMe.bytes_at segs mem3 a bs -> LMe.bytes_at segs mem2 a bs).
  { intros a bs H0 H1 Hb.
    apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 a bs phi (phi + A.ACtlCutP.flen cx j)); [|lia|lia|exact Hb].
    intros x Hx. apply (KB phi (A.ACtlCutP.flen cx j) x Hphiin).
    unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
  assert (Hinphi2 : In (phi, A.ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly2 S2))
    by (rewrite Hab2; exact Hphiin).
  assert (HinIN3 : 0 < A.ACtlCut.c_n cx ->
            In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn. destruct HpnIN as [(Hn0 & _) | (_ & Hin)]; [lia|].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hin. }
  assert (INK : LMe.bytes_at segs mem3 (A.ACtlCut.c_p cx) (A.ACtlCut.c_in cx) ->
                LMe.bytes_at segs mem2 (A.ACtlCut.c_p cx) (A.ACtlCut.c_in cx)).
  { intros Hb.
    apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 _ _ (A.ACtlCut.c_p cx)
             (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx)); [|lia|lia|exact Hb].
    intros x Hx. assert (Hn : 0 < A.ACtlCut.c_n cx) by lia.
    apply (KB _ _ x (HinIN3 Hn)).
    unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia. }
  assert (INA : A.AsanRT.addressable mem3 (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) ->
                A.AsanRT.addressable mem2 (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx)).
  { intros Ha. destruct (Z.eq_dec (A.ACtlCut.c_n cx) 0) as [E0|Hn].
    - apply (A.ACtlG.F6_ebc.f6g_addr_keep mem3 mem2); [intros i Hi; lia | exact Ha].
    - destruct Ha as (Hp0 & Hn0 & _).
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2' (A.ACtlCut.c_p cx)
               (A.ACtlCut.c_n cx) (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx) HAR2);
        [rewrite Hab2; apply HinIN3; lia | lia | lia |].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia. }
  (* KIND_NAME (0x9e760, 112 bytes): a non-owned image range, decided by search on the bundle's table (no list
     position is used, so the step holds on the planning core and on the record AF0m alike) *)
  assert (OWB : forallb (fun r : Z * Z => (fst r + snd r <=? A.Prog.reac_ctrl_kind_name_c.KIND_NAME) ||
                           (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 <=? fst r)) A.AF0m.Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  assert (KKN : forall a, A.Prog.reac_ctrl_kind_name_c.KIND_NAME <= a <
                          A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 ->
            LMe.mrd segs mem2 (LMe.wa a) = LMe.mrd segs mem3 (LMe.wa a)).
  { intros a Ha. unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME in Ha.
    assert (Himg : lib.Reusable.YG0d.in_img segs a) by (apply A.Prog.CtrlImg.ctrl_relro_img; lia).
    rewrite <- (MUK a ltac:(lia) ltac:(left; unfold A.Prog.SlotInv.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
                                    Z.div_mod_to_equations; lia)).
    apply KC.
    - destruct (A.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia.
    - rewrite (LMe.wa_unsigned a ltac:(lia)). right. right. left. split; [exact Himg|]. split.
      + rewrite (A.AF0m.ts_owned _ TFIB_SYMS). intros Hex. apply Exists_exists in Hex.
        destruct Hex as (r & Hr & Hz). pose proof (proj1 (forallb_forall _ _) OWB r Hr) as Hrb.
        apply orb_true_iff in Hrb. unfold lib.Reusable.YG0n.in_zr in Hz.
        unfold A.Prog.reac_ctrl_kind_name_c.KIND_NAME in Hrb.
        destruct Hrb as [Hrb | Hrb]; apply Z.leb_le in Hrb; lia.
      + rewrite (A.AF0m.ts_errno _ TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO. lia. }
  (* the five frame-shadow bytes at mem2 (written by f3_st_F, kept by the call) and the output cells' addressing *)
  assert (SB2 : LMe.bytes_at A.Img0.rsegs mem2 (A.Prog.SlotInv.Sfr fr + 22)
                  [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4]).
  { apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in m1 mem2 _ _ (lib.Reusable.YG0f.shadow_addr fr)
             (lib.Reusable.YG0f.shadow_addr fr + 512) KFS1); [rewrite ESfr; lia | cbn [length]; rewrite ESfr; lia |].
    exact SB1. }
  assert (HAPPf : forall a, fr <= a < fr + A.ACtlCutP.FRAME_BYTES -> A.AsanRT.app_mem a).
  { intros a Ha. unfold A.ACtlCutP.FRAME_BYTES in Ha. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END,
      A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
      lib.Reusable.YG0f.ASAN_CEIL in Hfapp. lia. }
  assert (HADo : A.AsanRT.addressable mem2 (fr + 176) 36).
  { apply (A.Prog.Seg.F3.f3_addr_o mem2 fr Hfr0 Hfr32 HAPPf); [unfold A.AsanRT.APPMEM_END; lia | exact SB2]. }
  (* the 36 output cells at mem2: parse's output B = snd (ctrlparse flen (t_g ..)) *)
  assert (HOUT : LMe.bytes_at A.Img0.rsegs mem2 (fr + 176)
                   (snd (lib.Prog.RcParse.ctrlparse (A.ACtlCutP.flen cx j)
                          (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j)))).
  { pose proof (lib.Prog.RcParse.ctrlparse_length (A.ACtlCutP.flen cx j)
                  (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j)) as HL36.
    split; [lia|]. split; [rewrite HL36; lia|]. intros i Hi. rewrite HL36 in Hi.
    assert (Hvis : lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 (fr + 176 + Z.of_nat i)) = false).
    { destruct (HFb2 (fr + 176 + Z.of_nat i) ltac:(lia)) as ((Hv & _) & _). exact Hv. }
    pose proof (Hout ltac:(lia) i Hi) as Hoi.
    pose proof (A.ProgWorld.mrd_of_aview_some W2 mem2 _ _ Hvis Hoi) as Hm.
    unfold LMe.wa. rewrite Hm, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
    rewrite (nth_error_nth' _ lib.Prog.RcParse.cp_z) by lia. reflexivity. }
  (* the exit cut's six premises *)
  apply (HX cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2' HB HJ3).
  - rewrite Hfr2. exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A81dfc_at at [j] *)
    cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A81dfc_at A.ACtlCutP.ixn nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    split.
    { (* FRAC *)
      exists A, sp.
      split; [rewrite K2; exact Esp|]. split; [exact Hsp16|].
      split; [unfold lib.Reusable.YG0d.spZ; rewrite K2; exact EspZ|].
      split; [rewrite K4; exact R4|].
      split; [unfold A.ACtlCut.rgv; rewrite K8; exact R8|].
      split; [unfold A.ACtlCut.rgv; rewrite K9; exact R9|].
      split; [rewrite K3; exact R3|].
      split; [unfold A.ACtlCut.rgv; rewrite K19; exact R19|].
      split; [unfold A.ACtlCut.rgv; rewrite K26; exact R26|].
      do 8 (split; [assumption|]).
      split; [refine (QK _ _ _ _ Q304); lia|].
      split; [refine (QK _ _ _ _ Q24); lia|].
      split; [refine (QK _ _ _ _ Q16); lia|].
      split; [unfold A.ACtlCutP.q64 in *; refine (FK _ _ _ Qhdr); left; rewrite LMe.length_le8; lia|].
      split; [unfold A.ACtlCutP.q64 in *; refine (FK _ _ _ Qent); left; rewrite LMe.length_le8; lia|].
      split.
      { (* the frame shadow, rewritten in bytes 22 .. 26 by f3_st_F: present at mem2 (the post's frame law) *)
        destruct (f3g_bytes_of_present mem2 (A.ACtlCutP.Sfr fr) (Z.to_nat A.ACtlCutP.FRAME_SHADOW))
          as (sh2 & Hsh2 & Hsh2l).
        - unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
        - unfold A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES, A.ACtlCutP.Sfr, A.AsanRT.shadow_addr,
            A.AsanRT.ASAN_K. cbn [Z.to_nat]. Z.div_mod_to_equations. lia.
        - intros i Hi. unfold A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES in Hi. cbn in Hi.
          destruct (HFs2 (Z.of_nat i) ltac:(lia)) as ((_ & b & Hb) & _). exists b.
          unfold LMe.mrd, LMe.wa. replace (A.ACtlCutP.Sfr fr + Z.of_nat i)
            with (lib.Reusable.YG0f.shadow_addr fr + Z.of_nat i)
            by (unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
                  lib.Reusable.YG0f.SHADOW_OFF; lia).
          rewrite Hb. reflexivity.
        - exists sh2. split; [exact Hsh2 | exact Hsh2l]. }
      split.
      { apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 _ _ sp (A.ACtlCut.c_sp cx) KS);
          [lia | | exact (proj1 Hsaved)].
        unfold A.ACtlCutP.saved_bytes; rewrite !length_app, !LMe.length_le8; cbn; lia. }
      (* the fake-frame trailer word (batch 3, FRAC's last conjunct): q64 at fr + 4088, a frame byte range past the
         output cells, kept by the call (FK, the owned-frame class of acall_kept) and by f3_st_F's munch *)
      unfold A.ACtlCutP.q64 in *; refine (FK _ _ _ (proj2 Hsaved)); right; rewrite LMe.length_le8; lia. }
    unfold A.ACtlCutP.b5_body. exists phi. cbv beta.
    split; [rewrite Hab2; exact HPerm|].
    split; [exact Hn26|]. split; [exact Hj255|].
    split.
    { (* HB: the record block's shadow, from the post's AR *)
      destruct HHB as (Hphi0 & _). split; [exact Hphi0|]. rewrite <- Hreq.
      apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2' phi (A.ACtlCutP.flen cx j) phi
               (lib.Reusable.YG00.req_size (A.ACtlCutP.flen cx j)) HAR2 Hinphi2); [lia | | lia].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
    split.
    { (* FLSI *)
      destruct HFLSI as ((HPRO & S128 & HSTK & S144 & HAD2691) & S216' & S224' & S248' & (HINa & HINb) & HFLC').
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & HAD2624 & HINb' & HINa' &
        P184 & P256 & P264 & P272 & P32).
      destruct HFLC' as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & HADfg & HAD2688 & C72 & C64 & C56 &
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
        unfold A.ACtlCutP.FRAME_BYTES.
        apply (A.ACtlG.F6_ebc.f6g_stk_of_present (lib.Reusable.YA0n.w_H W2) mem2 fr (fr + 3136)); [lia | lia |].
        intros a Ha. exact (proj1 (HFb2 a ltac:(lia))).
      - refine (SPK _ _ _ _ S144); lia.
      - refine (FA _ _ _ _ _ HAD2691); lia.
      - split; [refine (SPK _ _ _ _ S216'); lia|].
        split; [refine (SPK _ _ _ _ S224'); lia|].
        split; [refine (SPK _ _ _ _ S248'); lia|].
        split; [split; [exact (INA HINa) | exact (INK HINb)]|].
        unfold A.ACtlCutP.fragb in *.
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
      split; [unfold A.ACtlCut.rgv in *; rewrite K21; exact R21|].
      unfold A.ACtlCutP.OURb in *. refine (FK _ _ _ HOUR). right.
      rewrite A.Prog.SlotModel.OUR_length. cbn. lia. }
    split.
    { (* b5_C *)
      destruct HB5C as (_ & _ & (A1 & R9c & HA1 & HSPILL & Q232) & HPH' & HFR & HKN & HFG & HFS).
      pose proof (AEQ A1 R9c HA1) as EA1. subst A1.
      split; [unfold A.ACtlCut.rgv in *; rewrite K23; exact R23|].
      split; [unfold A.ACtlCut.rgv in *; rewrite K18; exact R18|].
      split.
      { exists A. split; [unfold A.ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [exact HA1|].
        destruct HSPILL as (Q248' & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 & Q264).
        split; [|refine (QK _ _ _ _ Q232); lia].
        split; [refine (QK _ _ _ _ Q248'); lia|].
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
        destruct HPH' as (HPHb & HPHp). split.
        - intros Hn. refine (RK _ _ _ _ (HPHb Hn)); [lia|].
          rewrite (A.Prog.Seg.F6.f6_tg_len (A.ACtlCut.c_in cx) j). cbn. lia.
        - intros Hn. unfold lib.Reusable.YG0d.spZ. rewrite K2. exact (HPHp Hn). }
      split.
      { (* b5_FR *)
        destruct HFR as (HFRa1 & HFRa2 & HFRb & HFRl). unfold A.ACtlCutP.fragb in *.
        split; [refine (FA _ _ _ _ _ HFRa1); lia|].
        split; [refine (FA _ _ _ _ _ HFRa2); lia|].
        split; [refine (FK _ _ _ HFRb); right; rewrite HFRl; cbn; lia|].
        exact HFRl. }
      split.
      { (* b5_KN: KIND_NAME's bytes (non-owned image) and its shadow (a zero-shadow global, found by search) *)
        destruct HKN as (HKNb & HKNa). split.
        - apply (A.ACtlG.F6_ebc.f6g_bytes_keep_in mem3 mem2 _ _ A.Prog.reac_ctrl_kind_name_c.KIND_NAME
                   (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112) KKN); [lia | | exact HKNb].
          assert (Hknl : (length A.Prog.reac_ctrl_kind_name_c.kind_name_bytes <= 112)%nat) by (vm_compute; lia).
          lia.
        - assert (ZSB : existsb (fun r : Z * Z => (fst r <=? A.Prog.reac_ctrl_kind_name_c.KIND_NAME) &&
                           (A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 112 <=? fst r + 8 * (snd r / 8)))
                           A.AF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
          apply existsb_exists in ZSB. destruct ZSB as (r & Hr & Hrb).
          apply andb_true_iff in Hrb. destruct Hrb as (Hr1 & Hr2). apply Z.leb_le in Hr1, Hr2.
          apply (A.ProgWorldShadow.ctl_zshadow_of_AR B LAWS ly2 S2 W2 mem2 md2' r
                   A.Prog.reac_ctrl_kind_name_c.KIND_NAME 112 HAR2); [| exact Hr1 | lia | exact Hr2].
          rewrite (A.AF0m.ts_zsh _ TFIB_SYMS). exact Hr. }
      split.
      { (* FGj *)
        destruct HFG as (HFGb & HFGo). split; [|exact HFGo]. unfold A.ACtlCutP.FGBe in *.
        pose proof HFR as (_ & _ & _ & HFRl).
        refine (FK _ _ _ HFGb). right. unfold A.ACtlCutP.fragb. rewrite HFRl. cbn. lia. }
      (* FSj *)
      destruct HFS as (F104 & F112 & HFSb & HFSa & HFSI).
      split; [refine (SPK _ _ _ _ F104); lia|].
      split; [refine (SPK _ _ _ _ F112); lia|].
      split; [refine (FK _ _ _ HFSb); right|].
      { pose proof (A.Prog.Seg.F6.f6_fs_body_len (A.ACtlCut.c_in cx) j) as Hl. lia. }
      split; [refine (FA _ _ _ _ _ HFSa); lia | exact HFSI]. }
    (* the stage's own conjuncts *)
    split.
    { (* FC *)
      destruct HFC as (C224 & R20 & R18f). split; [refine (SPK _ _ _ _ C224); lia|].
      split; [unfold A.ACtlCut.rgv in *; rewrite K20; exact R20|].
      unfold A.ACtlCut.rgv in *; rewrite K18; exact R18f. }
    split.
    { (* a0 = the parse result: SlotModel.t_k is fst (ctrlparse flen (t_g ..)) by definition *)
      unfold A.ACtlCut.rgv. exact Ha0. }
    split.
    { (* s9 = phi + 18 (f3_st_F's addi, kept by the call) *)
      unfold A.ACtlCut.rgv. exact K25. }
    split.
    { intros Hn. unfold A.ACtlCut.rgv in *. rewrite K22. exact (H22 Hn). }
    split.
    { (* u32 at fr + 176: the kind word of the output cells (F3.f3_c7) *)
      apply A.Prog.Seg.F3.f3_c7.
      apply (A.ProgWorld.rw_cells_CB_of_present mem2 (fr + 176) 36
               (snd (lib.Prog.RcParse.ctrlparse (A.ACtlCutP.flen cx j) (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j))));
        [exact (lib.Prog.RcParse.ctrlparse_length _ _) | lia | lia | |].
      - intros i Hi. pose proof HOUT as (_ & _ & Ho). exact (Ho i ltac:(rewrite lib.Prog.RcParse.ctrlparse_length; lia)).
      - intros i Hi. destruct (HFb2 (fr + 176 + i) ltac:(lia)) as ((_ & b & Hb) & _). rewrite Hb. discriminate. }
    split.
    { (* IDj *)
      destruct HIDj as (HIDb & HIDo). split; [|exact HIDo]. unfold A.ACtlCutP.IDBe in *.
      refine (FK _ _ _ HIDb). right. rewrite A.Prog.Seg.F6.f6_tID_len. cbn. lia. }
    (* b5_PF: made by the parse output (F3.f3_pf_fields / f3_pf_cmp) and the record frame at phi *)
    pose proof HFLC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C72 & C64 & _).
    destruct C72 as (A72 & R72 & Q72). destruct C64 as (A64 & R64 & Q64).
    assert (EA72 : A72 = A).
    { pose proof Q72 as (Hq0 & Hq1 & _). rewrite LMe.length_le8 in Hq1.
      pose proof R9 as R9z. unfold A.ACtlCut.rgv in R72, R9z.
      apply (A.ACtlG.F6_ebc.f6g_A_eq A A72 72); [rewrite <- R72, <- R9z; reflexivity | lia..]. }
    assert (EA64 : A64 = A).
    { pose proof Q64 as (Hq0 & Hq1 & _). rewrite LMe.length_le8 in Hq1.
      pose proof R9 as R9z. unfold A.ACtlCut.rgv in R64, R9z.
      apply (A.ACtlG.F6_ebc.f6g_A_eq A A64 64); [rewrite <- R64, <- R9z; reflexivity | lia..]. }
    subst A72 A64.
    exists A. split; [unfold A.ACtlCut.rgv in *; rewrite K9; exact R9|]. split; [lia|].
    pose proof HPH as (HPHb & _).
    split.
    { intros Hn. split.
      - exists (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j). split.
        + refine (RK _ _ _ _ (HPHb Hn)); [lia|]. rewrite (A.Prog.Seg.F6.f6_tg_len (A.ACtlCut.c_in cx) j). cbn. lia.
        + rewrite (A.Prog.Seg.F6.f6_tg_len (A.ACtlCut.c_in cx) j). lia.
      - assert (Htphi : (length (A.Prog.SlotModel.t_phi (A.ACtlCut.c_in cx) j) <=
                         Z.to_nat (A.ACtlCutP.flen cx j))%nat).
        { unfold A.ACtlCutP.flen, A.Prog.SlotModel.t_phi, A.Prog.SlotModel.t_len, A.Prog.SlotModel.f_phi.
          rewrite length_firstn. lia. }
        refine (RK _ _ _ _ (HPHI Hn)); lia. }
    intros H8819.
    assert (Hh : lib.Prog.RcParse.cp_hdr (A.ACtlCutP.flen cx j) (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j) = true)
      by exact H8819.
    assert (Hbig : 50 <= A.ACtlCutP.flen cx j).
    { apply lib.Prog.RcParse.cp_hdr_spec in Hh. lia. }
    assert (Hg2 : LMe.bytes_at A.Img0.rsegs mem2 phi (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j)).
    { refine (RK _ _ _ _ (HPHb Hbig)); [lia|]. rewrite (A.Prog.Seg.F6.f6_tg_len (A.ACtlCut.c_in cx) j). cbn. lia. }
    assert (HA50 : A.AsanRT.addressable mem2 phi 50).
    { apply (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2' phi (A.ACtlCutP.flen cx j) phi 50
               HAR2 Hinphi2); [lia | lia |].
      unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
    pose proof (A.Prog.Seg.F3.f3_pf_fields mem2 (fr + 176) phi (A.ACtlCutP.flen cx j)
                  (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j) (A.Prog.Seg.F6.f6_tg_len _ _) Hh HOUT Hg2 HA50
                  ltac:(exact Hp16)) as HPF1.
    destruct (A.Prog.Seg.F3.f3_pf_cmp mem2 (fr + 176) phi (A.ACtlCutP.flen cx j)
                (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j) (A.Prog.Seg.F6.f6_tg_len _ _) Hh HOUT Hg2)
      as ((ls & rs & Hls & Hlsl & Hrs & Hrsl & Hcmp) & (ls2 & rs2 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2)).
    replace (fr + 176 + 10) with (fr + 186) in Hls by lia.
    replace (fr + 176 + 4) with (fr + 180) in Hls2 by lia.
    split; [exact HPF1|].
    split.
    { exists ls, rs. split; [refine (QK _ _ _ _ Q72); lia|].
      split; [exact Hls|]. split; [exact Hlsl|]. split; [exact Hrs|]. split; [exact Hrsl|].
      split; [exact Hcmp|]. exact (f3g_addr_sub mem2 (fr + 176) 36 (fr + 186) 6 HADo ltac:(lia) ltac:(lia) ltac:(lia)). }
    exists ls2, rs2. split; [refine (QK _ _ _ _ Q64); lia|].
    split; [exact Hls2|]. split; [exact Hls2l|]. split; [exact Hrs2|]. split; [exact Hrs2l|].
    split; [exact Hcmp2|]. exact (f3g_addr_sub mem2 (fr + 176) 36 (fr + 180) 6 HADo ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* ctl_rt_C: from the post's AR (the call writes runtime cells) *)
    apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2' HAR2).
    apply (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI); [| lia | lia].
    exact (A.ACtlG.F6_ebc.f6g_aro_journal B RLO RHI RELRO_IMG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HRO0).
Qed.

End GlueF3.
