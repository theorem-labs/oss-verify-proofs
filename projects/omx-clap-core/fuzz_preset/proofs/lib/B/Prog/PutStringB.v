(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), this
   file: the ASSEMBLY of put_string's walk (B' listing slot 7473, 232 instructions) into the kit's #102 text
   tput_string_specX (the kit: lib/A/PRH_FnWriter.v (sha256 1b338cb8e926; internal record), PRH_Base.v (sha256 da55cb740765; internal record)), generic in the image
   facts and the allocator relation ARx; the instance is PutStringB_Inst.v. KIT CUT REBIND (2026-10-30): the same walk
   PutStringB_Inst.v. The batch kit's REBIND (2026-10-30): the same walk at the batch kit's text (the cut 
   PRH_FnWriter.v (sha256 bc9a9128f55a; internal record), PRH_Base.v (sha256 2ca8a3d631bd; internal record)): no DW, the consumer window prh_cons_from and the per-event
   the per-event live room prh_live_evs at entry, prh_granted in the post (PutStringB_Model.v's batch-kit note).
   rule 24: proves function put_string. proof-index (17:58Z): `proof-index: end; put_string: 14 named, 15 by
   address, 4 related, 8 released lemma(s), delivery: 2 named and 21 name(s) holding it, 6 UNRELEASED file(s) in the
   lemma index, 0 UNRELEASED hit(s) on live working heads`; census-1 sweep (18:01Z, 806 lib/B trees, positive
   control hit): 0 hits; second-agent check: CONFIRM.
   THE WALK'S PARTS (each lemma at its Section's CURRENT float state fx, its post ps_Qfin fe X at the ENTRY float state
   fe): PutStringB_A.v ps_seg_a (entry .. the opening-quote put .. the first byte), PutStringB_L.v psl_head_step (the
   byte test, the run put before an escape) and psl_next_step (the next byte), PutStringB_E.v ps_esc_run / pe_tail (the
   escape: __asan_memcpy or __wrap_snprintf, __wrap_strlen, the escape's put), PutStringB_T.v ps_tail_run (the last
   run's put, the closing quote, the release, the return). __wrap_snprintf returns at SOME float state (its row's post),
   so every continuation is over every float state with the two float facts the walk carries (frm_zero,
   fregs_kept_x fe; PutStringB_Base.v psK_head / psK_next / psK_esc / psK_tail), and the loop is a descending
   induction over the byte index.
   THE ENTRY ROUNDING MODE: the kit's fpre ends in FRM0-ENTRY (`frm_zero (@fp_csr fx)`; the 2026-10-29 ruling on the
   counterexample bs = [0x61] at fcsr = 0x20, where no snprintf runs and the exit float state is the entry's). The
   walk reads it off the text's fpre at the entry (HFRM0 below) and carries it as the CURRENT state's frm_zero through
   every continuation; ps_pre states the rest of fpre at YK11.fx0 (float-free).
   THE RE-HIDING MOVE: put reallocs when it grows (a crossing call) and its text concludes SRr' SEGS RZ_cf, so every
   continuation after the opening-quote put is the R form of its contract at wle' SEGS RZ_cf (psK_headR / psK_nextR /
   psK_escR / psK_tailR beside the kept psK_head .. psK_tail), the loop steps conclude SRr', and the text's post is
   fpostWFmR at wle' SEGS RZ_cf; the text's hull premise (length rp_os <= 4) is ps_pre's last conjunct. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr' with its mono) and the fixed
   zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_CallerJ PutStringB_S7bKit PutStringB_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_Model PutStringB_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_A PutStringB_L PutStringB_E PutStringB_T.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* NO Context {fx}: every float state here is a named binder, and every lemma of a segment file is applied with its
   float state given explicitly (fx := ..), never left to instance resolution *)
Section d. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Context {RL : PrhRoomLive}.
Section f.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* ---- the image facts and the allocator's laws: the segment files' Section hypotheses, verbatim (see
   PutStringB_A.v Section h for each one's comment and owner; PutStringB_Inst.v witnesses them at the instance) ---- *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
Hypothesis Hent : SIGMA AS_put_string = BASE + AF_put_string.
Hypothesis Huar : as_got_uar B = VAL (A_OBJ 1).
Hypothesis Hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Hypothesis HOBJ : ps_objs_disj.
Hypothesis HUARC : ps_uar_ok B.
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env SEGS B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Hypothesis Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0.
Hypothesis HW : prh_head_wide.
Hypothesis ASO : asyms_ok B.
Hypothesis HIMGSH : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
Hypothesis HPAB : 4096 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= kLowShadowBeg.
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
Hypothesis HLIT18 : ps_lit_fact B ARx 65 [34].
Hypothesis HLIT85 : ps_lit_fact B ARx 85 [92; 116; 0].
Hypothesis HLIT87 : ps_lit_fact B ARx 87 [92; 110; 0].
Hypothesis HLIT91 : ps_lit_fact B ARx 91 [92; 114; 0].
Hypothesis HLIT93 : ps_lit_fact B ARx 93 [92; 37; 99; 0].
Hypothesis HLIT89 : ps_lit_fact B ARx 89 [92; 117; 37; 48; 52; 120; 0].
(* the release's three frame laws (PutStringB_T.v; YGcallSx.v's) and the flag-cell presence
   STAND-IN FPRX (AR_laws_x field 23; at ARcfx YG0scf.AR_flag_law_ok_cf) *)
Hypothesis ASFX : forall ly S Hp (W : world SEGS) mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Hypothesis FPRX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Variable CTX0 : list (list Z).
(* ---- THE CALLEE TEXTS, at EVERY float state (each segment lemma is applied at the float state it starts at) ---- *)
(* put: the #102 tput_specX (PutB.v's walk) *)
Hypothesis PUT : forall fz : YK11.FPState, tput_specX (fx := fz) (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* __asan_stack_malloc_0: the m-form row (YGcallMxmn astack_malloc_realizes_xm, owner R4); used at the
   entry state only *)
Hypothesis ASM0 : forall fz : YK11.FPState, astack_malloc_realizes_xm (fx := fz) SEGS B ARx 0.
(* __asan_memcpy: the m-form intrinsic row (YGcallMxmn aintrin_realizes_xm OCpy; owner R2) *)
Hypothesis AMCPY : forall fz : YK11.FPState,
  aintrin_realizes_xm (fx := fz) SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
(* __wrap_strlen: the read-only row with the keep (YGcallMxmn astrlen_realizes_xrom; PROVED at the
   instance: AU/PSstrRo.v ps_strlen_xrom_xs_B, PutStringB_Wit.v psw_strlen) *)
Hypothesis ASTRLEN : forall fz : YK11.FPState,
  astrlen_realizes_xrom (fx := fz) SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).
(* __wrap_snprintf: the row's TEXT (YGcallSnp asnprintf_realizes_xrom at the escape family YGcallSnpCk.FF_esc lo hi),
   with its instance parameters, K <= Kp, and the ONE condition the walk reads of them
   (PutStringB_E.v ps_snp_inst); the walk uses the row through YGcallSnpCk.snp_esc_of_xrom (post at SOME float state) *)
Variables (K Kp lo hi gcan can img_lo img_hi : Z) (cr : list (Z * Z)).
Hypothesis HKK : K <= Kp.
Hypothesis HSNPI : PutStringB_E.ps_snp_inst B ARx Kp lo hi gcan can img_lo img_hi cr.
Hypothesis ASNP : forall fz : YK11.FPState,
  asnprintf_realizes_xrom (fx := fz) SEGS B ARx pa_relro_lo pa_relro_hi (YGcallSnpCk.FF_esc lo hi) K gcan can img_lo
    img_hi cr (SIGMA AS___wrap_snprintf).

Section pm.
(* the walk's memory invariant; the assembly takes it as the memnorm keep from the entry *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* the tail join, at every float state the walk carries (the contract's R form at wle' SEGS RZ_cf) *)
Lemma ps_tailK : forall fe X ch, ps_pre B ARx CTX0 X ch -> ps_s0 X -> psK_tailR B ARx Pm (wle' SEGS RZ_cf) fe X.
Proof.
intros fe X ch Hpre HS0 fz Hfrm Hfk pos j P lyc Sc Hpc Wc regsc memc mdc kc HT.
exact (@PutStringB_T.ps_tail_run fz _ _ _ _ _ _ B ARx LAWS segs_low HW ASO HIMGSH HPAB PST_ok HPSTRO Pm PLAW PCALL
  CTX0 (PUT fz) HLIT18 ASFX FFLX SFX FPRX fe Hfrm Hfk X ch Hpre HS0 pos j P lyc Sc Hpc Wc regsc memc mdc kc HT).
Qed.

(* ---- THE LOOP, as a descending induction over the byte index, from the three loop steps at EVERY float state
   (the head step, the next-byte step, and the escape as a map from the next-join continuation to the escape-join
   continuation): ps_HSTEP / ps_NSTEP / ps_ESTEP state them in the exact shapes of PutStringB_L.v / PutStringB_E.v's
   lemmas at fx := fz; ps_steps below proves them from those lemmas. Every step runs after the opening-quote put, so
   each concludes SRr' SEGS RZ_cf and the contracts are their R forms at wle' SEGS RZ_cf ---- *)
Definition ps_HSTEP : Prop := forall (fz fe : YK11.FPState) X ch, frm_zero (@fp_csr fz) ->
  ps_pre B ARx CTX0 X ch -> ps_s0 X -> forall i,
  (forall pos P lyc Sc Hpc Wc regsc memc mdc kc, ps_esc B ARx Pm X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 456))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin B ARx Pm fe X)) ->
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_next B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 636))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin B ARx Pm fe X)) ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_head B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin B ARx Pm fe X).
Definition ps_NSTEP : Prop := forall (fz fe : YK11.FPState) X ch, ps_pre B ARx CTX0 X ch -> ps_s0 X -> forall i,
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_head B ARx Pm X pos (S i) j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin B ARx Pm fe X)) ->
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_tail B ARx Pm X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin B ARx Pm fe X)) ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_next B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 636))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin B ARx Pm fe X).
Definition ps_ESTEP : Prop := forall (fe : YK11.FPState) X ch, ps_pre B ARx CTX0 X ch -> ps_s0 X -> forall i,
  psK_nextR B ARx Pm (wle' SEGS RZ_cf) fe X i -> psK_escR B ARx Pm (wle' SEGS RZ_cf) fe X i.

Section ind.
Hypothesis HSTEP : ps_HSTEP.
Hypothesis NSTEP : ps_NSTEP.
Hypothesis ESTEP : ps_ESTEP.

Lemma ps_loopK : forall (fe : YK11.FPState) X ch, ps_pre B ARx CTX0 X ch -> ps_s0 X ->
  forall k i, (i + k = length (x_bs X))%nat ->
  psK_headR B ARx Pm (wle' SEGS RZ_cf) fe X i /\ psK_nextR B ARx Pm (wle' SEGS RZ_cf) fe X i.
Proof.
intros fe X ch Hpre HS0 k. induction k as [|k IH]; intros i Hik.
- (* i = n: no head and no next join (both need i < n) *)
  split.
  + intros fz _ _ pos j P lyc Sc Hpc Wc regsc memc mdc kc HH. exfalso.
    destruct HH as (_ & (_ & Hlt) & _). clear - Hik Hlt. lia.
  + intros fz _ _ pos j P lyc Sc Hpc Wc regsc memc mdc kc HN. exfalso.
    destruct HN as (_ & _ & Hlt & _). clear - Hik Hlt. lia.
- destruct (IH (S i) ltac:(clear - Hik; lia)) as [IHh _].
  assert (KN : psK_nextR B ARx Pm (wle' SEGS RZ_cf) fe X i).
  { intros fz Hfrm Hfk pos j P lyc Sc Hpc Wc regsc memc mdc kc HN.
    refine (NSTEP fz fe X ch Hpre HS0 i _ _ pos j P lyc Sc Hpc Wc regsc memc mdc kc HN).
    - intros pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HH.
      exact (IHh fz Hfrm Hfk pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HH).
    - intros pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HT.
      exact (ps_tailK fe X ch Hpre HS0 fz Hfrm Hfk pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HT). }
  split; [|exact KN].
  intros fz Hfrm Hfk pos j P lyc Sc Hpc Wc regsc memc mdc kc HH.
  refine (HSTEP fz fe X ch Hfrm Hpre HS0 i _ _ pos j P lyc Sc Hpc Wc regsc memc mdc kc HH).
  + intros pos' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HE.
    exact (ESTEP fe X ch Hpre HS0 i KN fz Hfrm Hfk pos' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HE).
  + intros pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HN.
    exact (KN fz Hfrm Hfk pos' j' P' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HN).
Qed.

(* every head join, at every byte index *)
Lemma ps_headK : forall (fe : YK11.FPState) X ch, ps_pre B ARx CTX0 X ch -> ps_s0 X ->
  forall i, psK_headR B ARx Pm (wle' SEGS RZ_cf) fe X i.
Proof.
intros fe X ch Hpre HS0 i.
destruct (Nat.le_gt_cases i (length (x_bs X))) as [Hle | Hgt].
- exact (proj1 (ps_loopK fe X ch Hpre HS0 (length (x_bs X) - i) i ltac:(clear - Hle; lia))).
- intros fz _ _ pos j P lyc Sc Hpc Wc regsc memc mdc kc HH. exfalso.
  destruct HH as (_ & (_ & Hlt) & _). clear - Hgt Hlt. lia.
Qed.
End ind.

End pm.

(* the head step and the next-byte step, at every float state: PutStringB_L.v's lemmas at fx := fz *)
Lemma ps_hstep : forall Pm, srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm -> ps_HSTEP Pm.
Proof.
intros Pm PLAW PCALL fz fe X ch Hfrm Hpre HS0 i KE KN pos j P lyc Sc Hpc Wc regsc memc mdc kc HH.
exact (@PutStringB_L.psl_head_step fz _ _ _ _ _ _ B ARx LAWS segs_low HW ASO HIMGSH HPAB PST_ok HPSTRO Pm PLAW PCALL
  CTX0 (PUT fz) Hfrm fe X ch Hpre HS0 i KE KN pos j P lyc Sc Hpc Wc regsc memc mdc kc HH).
Qed.
Lemma ps_nstep : forall Pm, srr_inv_laws SEGS Pm -> ps_NSTEP Pm.
Proof.
intros Pm PLAW fz fe X ch Hpre HS0 i KH KT pos j P lyc Sc Hpc Wc regsc memc mdc kc HN.
exact (@PutStringB_L.psl_next_step fz _ _ _ _ _ _ B ARx LAWS segs_low HW ASO HIMGSH HPAB PST_ok HPSTRO Pm PLAW
  CTX0 fe X ch Hpre HS0 i KH KT pos j P lyc Sc Hpc Wc regsc memc mdc kc HN).
Qed.

(* the escape, at every float state: PutStringB_E.v's ps_esc_run at fx := fz; its post-snprintf continuation (at the
   float state snprintf returns) is pe_tail at that state, and both next-join continuations are the loop's *)
Lemma ps_estep : forall Pm, srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm -> ps_ESTEP Pm.
Proof.
intros Pm PLAW PCALL fe X ch Hpre HS0 i KN fz Hfrm Hfk pos P lyc Sc Hpc Wc regsc memc mdc kc HE.
assert (HKp : ESTACK <= Kp) by (destruct HSNPI as ((HK1 & _) & _); exact HK1).
refine (@PutStringB_E.ps_esc_run fz _ _ _ _ _ _ B ARx LAWS segs_low HW HFHULL HPAB PST_ok HPSTRO Pm PLAW PCALL
  CTX0 (PUT fz) Hfrm HLIT85 HLIT87 HLIT91 HLIT93 HLIT89 (AMCPY fz) (ASTRLEN fz) Kp lo hi gcan can img_lo img_hi cr
  HSNPI (@YGcallSnpCk.snp_esc_of_xrom fz SEGS B ARx _ _ lo hi K Kp gcan can img_lo img_hi cr _ HKK HKp (ASNP fz))
  fe X ch Hpre HS0 Hfrm Hfk pos i P _ _ lyc Sc Hpc Wc regsc memc mdc kc HE).
- intros lyn Sn Hpn Wn regsn memn mdn kn HN.
  exact (KN fz Hfrm Hfk pos (S i) _ lyn Sn Hpn Wn regsn memn mdn kn HN).
- intros fz' Hfrm' Hfk' lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc' HWR.
  refine (@PutStringB_E.pe_tail fz' _ _ _ _ _ _ B ARx LAWS segs_low HW HFHULL HPAB PST_ok HPSTRO Pm PLAW PCALL
    CTX0 (PUT fz') Hfrm' (ASTRLEN fz') fe X ch Hpre HS0 592 pos i P lyc' Sc' Hpc' Wc' regsc' memc' mdc' kc'
    (or_intror eq_refl) HWR _).
  intros lyn Sn Hpn Wn regsn memn mdn kn HN.
  exact (KN fz' Hfrm' Hfk' pos (S i) _ lyn Sn Hpn Wn regsn memn mdn kn HN).
Qed.

(* the kit's tput_string_specX after the re-hiding move (PRH_FnWriter.v :778: SRr' SEGS RZ_cf, its post fpostWFmR at
   wle' SEGS RZ_cf, the hull premise length rp_os <= 4; the kit's fpre carries FRM0-ENTRY, the rounding mode 0 at
   entry) at the instance's names: the walk from the entry (ps_seg_a at fe), the loop (ps_headK), the tail
   (ps_tailK), and the post ps_Qfin read as the text's fpostWFmR at the memnorm keep from the entry *)
Theorem put_string_holds : forall fe : YK11.FPState,
  tput_string_specX (fx := fe) (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Proof.
intros fe. unfold tput_string_specX.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s d buf st bs Lam peak ran
  HFPRE Hroom Hrp Huniv Hlen4 Hcons H10 H11 Hocase Hoch Hs0 Hwin Ho1 Ho2 Hout Hled Hcstr Hkept Hevs Hdisj Hfr Hwmax
  Hhead Hlive.
set (X := mkPSX d ly S Hp W regs mem md o s bs buf st Lam peak ran most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist).
set (Pm := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS Pm) by exact (srr_inv_laws_imp SEGS _ mem (srr_inv_laws_memnorm_k SEGS)).
assert (PCALL : srr_inv_call SEGS Pm) by exact (srr_inv_call_imp SEGS mem).
pose proof (ps_hstep Pm PLAW PCALL) as HS. pose proof (ps_nstep Pm PLAW) as NS.
pose proof (ps_estep Pm PLAW PCALL) as ES.
(* the text's fpre at fe is ps_pre's float-free fpre (at YK11.fx0) plus the entry rounding mode HFRM0 *)
destruct HFPRE as (HAFN & HRO & HTOP & HRAC & HFRM0).
assert (Hpre : ps_pre B ARx CTX0 X ch).
{ exact (conj (conj HAFN (conj HRO (conj HTOP (conj HRAC fp_frm_zero_fx0)))) (conj Hroom (conj Hrp (conj Huniv
    (conj H10 (conj H11 (conj Hocase (conj Hoch (conj Hwin (conj Ho1 (conj Ho2 (conj Hout (conj Hled (conj Hcstr
    (conj Hkept (conj Hdisj (conj Hfr (conj Hwmax (conj Hhead (conj Hlive (conj Hevs (conj Hcons Hlen4)))))))))))))))))))))). }
assert (HS0 : ps_s0 X) by exact Hs0.
(* the entry float state's two float facts: frm_zero (FRM0-ENTRY, from fpre); its f registers are its own *)
assert (HFK0 : fregs_kept_x fe fe) by (intros r _; reflexivity).
assert (KH : forall pos i j P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_head B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fe regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin B ARx Pm fe X)).
{ intros pos i j P lyc Sc Hpc Wc regsc memc mdc kc HH.
  exact (ps_headK Pm PLAW PCALL HS NS ES fe X ch Hpre HS0 i fe HFRM0 HFK0 pos j P lyc Sc Hpc Wc regsc memc mdc kc HH). }
assert (KT : forall pos j P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_tail B ARx Pm X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fe regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin B ARx Pm fe X)).
{ intros pos j P lyc Sc Hpc Wc regsc memc mdc kc HT.
  exact (ps_tailK Pm PLAW PCALL fe X ch Hpre HS0 fe HFRM0 HFK0 pos j P lyc Sc Hpc Wc regsc memc mdc kc HT). }
eapply (SRr'_mono SEGS RZ_cf).
{ exact (PutStringB_A.ps_seg_a (fx := fe) B ARx LAWS TL Hent Huar Hobj HOBJ HUARC segs_low errno_low OWNLOW SMX
    (ASM0 fe) Hsm0 HW ASO HIMGSH HPAB PST_ok HPSTRO Pm PLAW PCALL CTX0 (PUT fe) HFRM0 HLIT18 HLIT85 HLIT87 HLIT91
    HLIT93 HLIT89 X ch Hpre HS0 (fun H => H) KH KT). }
(* ps_Qfin at the memnorm keep is the text's fpostWFmR at wle' SEGS RZ_cf: the keep is the inner Q's last conjunct *)
cbv beta. intros W' c' _ [HQ HPm].
destruct HQ as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hfrm & Hfk & HJ & Hwin' & Hpres & HQin).
subst c'. cbn [cfg_ms mkst ms_mem] in HPm.
unfold fpostWFmR, fpostWFR. exists fx', ly', S', Hp', regs', mem', md', k.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact HJ|]. split; [exact Hwin'|].
split; [exact Hpres|]. split; [exact HQin | exact HPm].
Qed.
End h.
End f.
End d.
