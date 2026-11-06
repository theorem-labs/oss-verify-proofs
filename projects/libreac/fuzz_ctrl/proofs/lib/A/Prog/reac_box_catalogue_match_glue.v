(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_catalogue_match (0x84498 = BASE + AF_reac_box_catalogue_match) of fuzz_ctrl's ASan build
   (image A, libreac v1.9.0): the WALK of the cgif-form contract stated in C_reac_box_catalogue_match.v
   (`treac_box_catalogue_match_spec`, statement only). This file glues the lifted footprint stretches
   reac_box_catalogue_match_F<n>.v with cgif's runtime / callee rules at the events between them; the
   world-to-machine facts it cannot prove on this base are named Section hypotheses (see the report).
   Rule 24: `proof-index reac_box_catalogue_match` = 0 named / 0 by address / 0 related (a Theorem Labs lane,
   2026-10-28 21:05Z), a Theorem Labs lane CONFIRM: no released proof is reused. At ossv/recipes c5e779efe8c (2026-10-31), reac_box_catalogue_match has no released proof outside this unit. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist both in the core (lib/Reusable) and in ctrl's lib/A/Reusable (YI04 YI16 YK11 YK1b YM05
   YO09) are Required from the core's directory and named `lib.Reusable.X.n` (porter a Theorem Labs lane 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlImg CtrlFrame CtrlRo.
(* `apost_base` comes from the Reusable copy, never from a private one (brief, 2026-10-28); imported last so that
   it wins over the PA layer's copy of the same cgif text. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import APostBase.
(* ctrl's plain files: Required QUALIFIED only, never Imported (glue closure rule, porter 23:38Z; a Theorem Labs lane Q6). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_lib.
(* The two callees' specs of record, Required QUALIFIED: reac_ctrl_parse (a working branch
   55301a93133) and reac_box_model_block (a Theorem Labs lane, statement-only file, a working branch
   2249a9686c1). The walk uses the caller-journal shapes and the model they name. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
(* The walk's glue: the bridge, ctrl's machine vocabulary and the MemNorm route, the proved visibility lemmas, and
   the stretch lemmas. All Required QUALIFIED (lib/Lib shadows getr / mkst / seg_rom of lib.Reusable.YK11: never
   Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame ExecF MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ACtlK A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.MemNormF A.MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap A.ProgWorldVisFrame.
(* a Theorem Labs lane's ProgWorld and its proof files (see "a Theorem Labs lane's ProgWorld facts" below). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ProgWorld A.ProgWorld_Fs
  A.ProgWorldAstack A.ProgWorldShadow A.ProgWorldBlkApart A.ProgWorldTlsApart.
(* Route (C) L3 (L3-recipe.md (a working note, not in this delivery), a Theorem Labs lane 09:20Z): the cut's runtime facts in the stage-variable form, without
   AR_states_vis0_shadow: A.ACtlRtC.ctl_rt_C / cut_shadow / img_shadow (a Theorem Labs lane's cform), ctl_rt_C_of_AR and
   RT_used_of_AR_C (a Theorem Labs lane's ProgWorldCtlRtC / ProgWorldRtC), the region form A.ShadowRwOn / ShadowRwOnT. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC A.ProgWorldCtlRtC
  A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0nR YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss PropExec StepF Cells Step RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatchLib RcBoxLib RcSynthLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_c reac_box_catalogue_match
  reac_box_catalogue_match_F1 reac_box_catalogue_match_F3 reac_box_catalogue_match_F4
  reac_box_catalogue_match_F6 reac_box_catalogue_match_F7 reac_box_catalogue_match_F2.
(* The `_on` forms of the run (route (C)): the narrowed invariant and stretches, F5's new file, and the bcmp wrapper's
   F-form `_on` proof (a Theorem Labs lane's bcmp_wrap_on.v). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on reac_box_catalogue_match_F5_on
  rng_asan sh_word_on asan_stack_malloc_c_on bcmp_wrap_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import C_reac_box_catalogue_match.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The FP state, the run ceiling and the sink head are the core's (lib.Reusable.YK11, lib.Reusable.YM05,
   lib.Reusable.YI16), the ones PI_ctrl, afn_pre and apost_base take. Written fully qualified: their short names also
   name lib/A/Reusable/ and lib/B/Reusable/ modules, and with the Requires above on a Theorem Labs lane's PA head they did not
   resolve to the core's (type-checks 02:33Z / 03:00Z: "?rc: Cannot infer this placeholder of type RunCeil" at the
   line of A_catalogue_matchP, then "?fx: Cannot infer the implicit parameter fx of apost_base" at the post). The
   meaning is the one intended. *)
Section b. Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
Section d.
(* The concrete image instance: no `Context {PI : PAImg ctrl_listing}` (two Theorem Labs lanes, 23:49Z). *)
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).


(* ---- a Theorem Labs lane's ProgWorld facts the walk takes ---------------------------------------------------------------
   lib/A/ProgWorld.v (blob d63a6e41b51) and its proof files ProgWorld_Fs.v (9209c78fc84), ProgWorldAstack.v
   (d98becdc45d), ProgWorldShadow.v (a10a774a57e), with A.AF0m (44930bfd861), lib/A/ProgWorldBlkApart.v (22f3e61fbe0)
   and lib/A/ProgWorldTlsApart.v (1f4f062c65a) (both by path from 87fcd8d0b28), and for route (C) L3 (a working branch
   1899bed1aee) lib/A/ProgWorldCtlRtC.v (9bde20fbe52) and ProgWorldRtC.v (a0e814a689c) over a Theorem Labs lane's
   lib/A/ACtlRtC.v (50a0bf66916). Section h cites the PROVED lemmas and keeps as a Section hypothesis only what
   ProgWorld states without a proof (CtrlTSyms). *)
#[local] Notation segs := A.AB1v.tfibsegs (only parsing).
#[local] Notation ctl_fs_geom := A.ProgWorld.ctl_fs_geom (only parsing).

Section h.
Variable B : asyms.
(* The read-only window, as a Theorem Labs lane's `ctl_base` carries it (two Theorem Labs lanes, 23:37Z): Section variables right
   after B, so callers write `treac_box_catalogue_match_spec (SK := SK) B RLO RHI GLOBS`. *)
Variables RLO RHI : Z.
(* The read-only window lies in the image: what `arodata_ok_journalP` needs to carry the RO fact across each call
   (cgif lib/YC20.v:56, used at :60-68; here with SEGS = tfibsegs). The composer discharges it from PI_ctrl's
   `pa_relro_lo` / `pa_relro_hi` / `pa_relro_img` (a Theorem Labs lane via a Theorem Labs lane, 00:14Z); RLO / RHI stay Variables, so
   no relro range is written into this statement. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img tfibsegs a.
(* The runtime's table of registered globals. *)
Variable GLOBS : list (Z * Z).
(* The statement's post and spec at this section's variables (C_reac_box_catalogue_match.v, the statement file). *)
#[local] Notation treac_box_catalogue_match_post :=
  (C_reac_box_catalogue_match.treac_box_catalogue_match_post (SK := SK) B) (only parsing).
#[local] Notation treac_box_catalogue_match_spec :=
  (C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := SK) B RLO RHI GLOBS) (only parsing).


(* ---- Section context the walk uses ---------------------------------------------------------------------- *)
(* The runtime laws, with cgif's names and types (cgif A/AChf.v:49-57, A/ACfj.v:99-104, A/ACfi.v:88-91);
   `abcmp_realizes` is NOT one of them: the bcmp call sits inside a lifted stretch (bcmp_wrap_contract_F). *)
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : astack_malloc_realizes tfibsegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
(* The image's library facts: objects 0 = GOT_UAR, 1 = GOT_CELL_K, 30 = CELL_K, 31 = UAR (a Theorem Labs lane, Q8 21:29Z).
   `palf_sm2` (CtrlFrame.v:100) is what the class-2 stack-malloc call needs. *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* The registered globals (CtrlRo.v:44-46). *)
Hypothesis HGM : globs_marked tfibsegs B GLOBS.
(* The read-only window lies below the sink's overflow head (CtrlBase.v:23-24 / APostBase.v:27-28). *)
Context {RO : ro_below_ofl tfibsegs RLO RHI}.
(* The two callees, at the call sites 0x84684 (parse(f, len, F + 32)) and 0x846c8 (model_block(row_i, 0, F + 112)),
   both in the caller-journal form with this walk's journal (own = [(2, pos)]), in their owners' citation form
   (CONVENTIONS sec. 2): REAC_CTRL_PARSE_STK = 8800 (C_reac_ctrl_parse.v:46), REAC_BOX_MODEL_BLOCK_STK = 4320
   (C_reac_box_model_block.v:102). *)
Hypothesis TPARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) B RLO RHI.
Hypothesis TMB : C_reac_box_model_block.treac_box_model_block_spec (SK := SK) B GLOBS
  (BASE + AF_reac_box_model_block) RLO RHI.
(* The world-to-machine facts, from a Theorem Labs lane's ProgWorld (see "a Theorem Labs lane's ProgWorld facts" above). PROVED there
   and cited: ctl_rt_C_of_AR (ProgWorldCtlRtC.v:37; route (C) L3, no AR_states_vis0_shadow, no
   AR_states_owned_ro), ctl_fp_of_AR (ProgWorld_Fs.v:385), RT_used_of_AR_C (ProgWorldRtC.v:43), ajournal_of_fsteps
   (ProgWorld.v:1091), ctl_fs_of_astack and ctl_release_of_free_law (ProgWorldAstack.v:225, :333),
   ctl_block_shadow_of_AR and ctl_stack_shadow_of_AR (ProgWorldShadow.v:63, :113), as_tp_RT_TP and as_tsd_TSD
   (ProgWorld.v:876, :1192), and ctl_block_apart_fs (ProgWorldBlkApart.v:23) and fp_tls_apart
   (ProgWorldTlsApart.v:159), from 87fcd8d0b28. The one Section hypothesis left: the composer's symbol facts
   A.AF0m.CtrlTSyms B. AR_states_vis0_shadow (false at AR) is gone with the universal shadow_rw it fed. *)
Hypothesis CTS : A.AF0m.CtrlTSyms B.
Let TLSAP : A.ProgWorld.fp_tls_apart_stmt B := A.ProgWorldTlsApart.fp_tls_apart B.
Let BLKFS : A.ProgWorld.ctl_block_apart_fs_stmt B := A.ProgWorldBlkApart.ctl_block_apart_fs B.
Let CTLRT : A.ProgWorldCtlRtC.ctl_rt_C_of_AR_stmt B := A.ProgWorldCtlRtC.ctl_rt_C_of_AR B.
Let FPAR : A.ProgWorld.ctl_fp_of_AR_stmt B := A.ProgWorld_Fs.ctl_fp_of_AR B.
Let RTAR : A.ProgWorldRtC.RT_used_of_AR_C_stmt B := A.ProgWorldRtC.RT_used_of_AR_C B.
Let AJF : A.ProgWorld.ajournal_of_fsteps_stmt (SK := SK) B := A.ProgWorld.ajournal_of_fsteps B.
Let FSAS : A.ProgWorld.ctl_fs_of_astack_stmt B 2 := A.ProgWorldAstack.ctl_fs_of_astack B 2.
Let RELF : A.ProgWorld.ctl_release_of_free_law_stmt (SK := SK) B 2 := A.ProgWorldAstack.ctl_release_of_free_law B 2.
Let BLKSH : A.ProgWorld.ctl_block_shadow_of_AR_stmt B := A.ProgWorldShadow.ctl_block_shadow_of_AR B.
Let STKSH : A.ProgWorld.ctl_stack_shadow_of_AR_stmt B := A.ProgWorldShadow.ctl_stack_shadow_of_AR B.
(* The bundle's thread pointer is ctrl's TP cell, so the stretches' `bv_unsigned tp` is ProgWorld's A.AsanRT.RT_TP. *)
Let TP_RT : as_tp B = A.AsanRT.RT_TP := A.ProgWorld.as_tp_RT_TP B CTS.
Let TSD_TSD : A.AF0m.CtrlTSyms B -> as_tsd B = 0x5fcbb8 := A.ProgWorld.as_tsd_TSD B.

(* lia without the euclidean-division equations, Local to this file (a Theorem Labs lane rule 3): the walk's proofs were written
   while the PA files' global setting of this flag to false leaked into this file; with the leak gone the flag is
   the one this file's Require closure leaves (true: ZifyNat and stdpp's bitvector.definitions set it, a Theorem Labs lane 09:40Z /
   09:46Z), and cm_stage_s5 takes 23.5 s instead of 8.2 s, cm_base 5.6 s instead of 3.1 s (rocq compile -time,
   a build machine, 2026-10-29 09:47Z). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The stack window is visible at every state of the journal: its presence clause (D YCbq.v ajournal, `apresent`
   on [sp0 - STK, sp0)). Stated here for any sink head: ProgWorldVisWin.win_vis on the glue base fixes the journal's
   sink head to A.AE2k.tfib_sink_head, and this file's statement is generic in SK. *)
Lemma cm_win_vis : forall sp0 ly0 S00 W0 mem0 md0 own lyc Sc Wc mr mdc k lo n,
  ajournal tfibsegs B CM_STK sp0 [] ly0 S00 W0 mem0 md0 own lyc Sc Wc mr mdc k ->
  0 <= lo -> sp0 - CM_STK <= lo -> lo + n <= sp0 -> sp0 <= 2 ^ 64 -> A.ProgBridge.range_visible (w_H Wc) lo n.
Proof.
  intros sp0 ly0 S00 W0 mem0 md0 own lyc Sc Wc mr mdc k lo n J H0 Hlo Hhi Hsp.
  pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  split; [exact H0|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* ==== The walk, part 1: the generic glue ======================================================================
   G1. A footprint run lifted to the world, handing the run itself to the continuation (for the journal). *)
Lemma cm_SRr_frun : forall (W : world tfibsegs) (ms : machine_state) (model : Model) (RNG : Z -> nat -> Prop)
    (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  (exists ms', lib.Reusable.YK04R.fsteps tfibsegs RNG ms ms' /\ P ms') ->
  lib.Reusable.YK04R.fp_avoids (w_H W) RNG ->
  (forall ms' model', P ms' -> lib.Reusable.YK04R.fsteps tfibsegs RNG ms ms' ->
     same_but_materialized model model' -> SRr tfibsegs W (mkCfg ms' model') Q) ->
  SRr tfibsegs W (mkCfg ms model) Q.
Proof.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (lib.Reusable.YA0nR.SRr_fsteps tfibsegs ctrl_wx W ms ms' model RNG Q Hrun Hfp
           (fun model' Hs => Hk ms' model' HP Hrun Hs)).
Qed.

(* G2. The footprint of one lift: the visible bytes of its ranges R and every byte of a segment. Every other byte is
   hidden from the run, so the run keeps it (YA0nR.fsteps_keeps_hidden). *)
Definition cm_inR (R : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? snd r)) R.
Definition cm_inseg (x : word) : bool :=
  match find_segment tfibsegs (bv_unsigned x) 1 with Some _ => true | None => false end.
Definition cm_Hk (H : word -> bool) (R : list (Z * Z)) : word -> bool :=
  fun x => H x || (negb (cm_inseg x) && negb (cm_inR R (bv_unsigned x))).

Lemma cm_Hk_off : forall (W : world tfibsegs) R, H_off_segments tfibsegs (cm_Hk (w_H W) R).
Proof.
  intros W R a Ha. unfold cm_Hk in Ha. destruct (w_H W a) eqn:E.
  - exact (w_Hoff W a E).
  - cbn [orb] in Ha. apply andb_prop in Ha as [Ha _]. unfold cm_inseg in Ha.
    destruct (find_segment tfibsegs (bv_unsigned a) 1); [discriminate Ha | reflexivity].
Qed.

Lemma cm_fp_avoids_Hk : forall (H : word -> bool) R, lib.Reusable.YK04R.fp_avoids H (A.ProgBridge.RNG_W (cm_Hk H R)).
Proof.
  intros H R a n Hr k Hkn. pose proof (A.ProgBridge.fp_avoids_RNG_W (cm_Hk H R) a n Hr k Hkn) as E.
  unfold cm_Hk in E. destruct (H (woff a k)); [discriminate E | reflexivity].
Qed.

Lemma cm_rng_Hk : forall (H : word -> bool) R lo len,
  (forall a, lo <= a < lo + len -> cm_inR R a = true) -> A.ProgBridge.range_visible H lo len ->
  lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk H R)) lo len.
Proof.
  intros H R lo len HR (Hlo & Hhi & Hv). apply A.ProgBridge.rng_RNG_W; [exact Hlo | exact Hhi |].
  intros a Ha. unfold cm_Hk. rewrite (Hv a Ha). cbn [orb].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  rewrite (HR a Ha). cbn [negb]. apply andb_false_r.
Qed.

Lemma cm_keep_Hk : forall (W : world tfibsegs) R ms ms',
  lib.Reusable.YK04R.fsteps tfibsegs (A.ProgBridge.RNG_W (cm_Hk (w_H W) R)) ms ms' ->
  forall x, cm_Hk (w_H W) R x = true -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros W R ms ms' Hrun.
  exact (lib.Reusable.YA0nR.fsteps_keeps_hidden tfibsegs ctrl_wx (cm_Hk (w_H W) R) _ ms ms' (cm_Hk_off W R) Hrun
           (A.ProgBridge.fp_avoids_RNG_W (cm_Hk (w_H W) R))).
Qed.

Lemma cm_outside_dec : forall (WR : list lib.Lib.Frame.ivl) x, lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [lib.Lib.Frame.outside]; intros x; [left; exact I|].
  assert (D : (lo <= x < hi) \/ ~ (lo <= x < hi)) by lia.
  destruct D as [D|D]; [right; tauto|]. destruct (IH x) as [H|H]; [left; tauto | right; tauto].
Qed.

(* G3. The writes of a lift: outside a coarse write set A nothing changes (the stretch's own munch), and inside A
   only the footprint's bytes can change; so the run writes only WR when every footprint byte of A is in WR and A
   holds no segment byte. *)
Lemma cm_munch_of_keep : forall (W : world tfibsegs) R (A WR : list lib.Lib.Frame.ivl) (m m' : word -> option byte),
  (forall x, cm_Hk (w_H W) R x = true -> m' x = m x) ->
  lib.Lib.Frame.munch A m m' ->
  (forall a, cm_inR R a = true -> ~ lib.Lib.Frame.outside A a -> ~ lib.Lib.Frame.outside WR a) ->
  (forall x : word, ~ lib.Lib.Frame.outside A (bv_unsigned x) -> cm_inseg x = false) ->
  lib.Lib.Frame.munch WR m m'.
Proof.
  intros W R A WR m m' HK MU HRA HAS x Hx.
  destruct (cm_outside_dec A (bv_unsigned x)) as [Ho | Hi]; [exact (MU x Ho)|].
  apply HK. unfold cm_Hk. rewrite (HAS x Hi). cbn [negb].
  destruct (cm_inR R (bv_unsigned x)) eqn:E.
  - exfalso. exact (HRA _ E Hi Hx).
  - cbn [negb andb]. apply orb_true_r.
Qed.

(* G4. One re-based lift: the stretch runs on `normalize mr` (its base; MemNorm.mem_inv_normalize), the run moves to
   the real memory mr by MemNormF.evtF_normalize_ro (premise ro_agree), and the world step is cm_SRr_frun at the
   footprint cm_Hk (w_H W) R. The continuation gets the real end state ms', the stretch's end state s0 (ms_rel), the
   read-only bytes kept, the run, and every byte off the footprint kept. *)
Lemma cm_lift_base : forall (W : world tfibsegs) (R0 F : bvmap 5 word) (pc : word) (fc : bv 32)
    (mr : word -> option byte) (model : Model) (R : list (Z * Z)) (P : machine_state -> Prop)
    (Q : world tfibsegs -> config -> Prop),
  A.MemNorm.ro_agree A.Img0.rsegs mr ->
  lib.Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (cm_Hk (w_H W) R)) P
    (lib.Lib.MState.MS R0 F pc fc None (A.MemNorm.normalize A.Img0.rsegs mr) (seg_rom tfibsegs)) ->
  (forall (ms' s0 : machine_state) (model' : Model), P s0 -> A.MemNorm.ms_rel A.Img0.rsegs ms' s0 ->
     A.MemNorm.ro_same A.Img0.rsegs mr (ms_mem ms') ->
     lib.Reusable.YK04R.fsteps tfibsegs (A.ProgBridge.RNG_W (cm_Hk (w_H W) R))
       (lib.Lib.MState.MS R0 F pc fc None mr (seg_rom tfibsegs)) ms' ->
     (forall x, cm_Hk (w_H W) R x = true -> ms_mem ms' x = mr x) ->
     same_but_materialized model model' -> SRr tfibsegs W (mkCfg ms' model') Q) ->
  SRr tfibsegs W (mkCfg (lib.Lib.MState.MS R0 F pc fc None mr (seg_rom tfibsegs)) model) Q.
Proof.
  intros W R0 F pc fc mr model R P Q Hro Hrun K.
  pose proof (A.MemNormF.evtF_normalize_ro _ P R0 F pc fc None mr (seg_rom tfibsegs) Hro Hrun) as Hreal.
  apply (cm_SRr_frun W _ model (A.ProgBridge.RNG_W (cm_Hk (w_H W) R))
           (fun s => exists s0, P s0 /\ A.MemNorm.ms_rel A.Img0.rsegs s s0 /\
                       A.MemNorm.ro_same A.Img0.rsegs mr (ms_mem s))).
  - exact (A.ProgBridge.fevt_of_evtF _ _ _ Hreal).
  - exact (cm_fp_avoids_Hk (w_H W) R).
  - intros ms' model' (s0 & HP & Hrel & Hsame) Hfs Hsbm.
    exact (K ms' s0 model' HP Hrel Hsame Hfs (cm_keep_Hk W R _ ms' Hfs) Hsbm).
Qed.

(* ==== The walk, part 2: the entry and stretch S1 =============================================================== *)
Lemma cm_inR_In : forall R lo hi a, In (lo, hi) R -> lo <= a < hi -> cm_inR R a = true.
Proof.
  intros R lo hi a Hin Ha. unfold cm_inR. apply existsb_exists. exists (lo, hi). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma cm_rt_vis : forall (W : world tfibsegs) lo n,
  A.AsanRT.RT_LO <= lo -> 0 <= n -> lo + n <= A.AsanRT.RT_HI -> A.ProgBridge.range_visible (w_H W) lo n.
Proof.
  intros W lo n H1 H2 H3.
  apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO));
    [exact (A.ProgBridge.rt_vis_W W) | lia | lia | lia].
Qed.

(* A range of present bytes is a stk range (wview reads the byte the memory holds). *)
Lemma cm_stk_present : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent H m a) -> lib.Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as (_ & b & Hb). change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
  split.
  - unfold RiscvSemantics.wview. rewrite Hb. cbn. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* The read-only premise of ProgWorldCtlRtC's ctl_rt_C_of_AR from the spec's (ProgWorld.v:376-382
   arodata_okP_of_S, at the same window). *)
Lemma cm_arodataP : forall rd, arodata_okS tfibsegs B RLO RHI rd -> A.Prog.CtrlBase.arodata_okP segs RLO RHI B rd.
Proof. intros rd H a Ha. apply H. destruct Ha as [Ha|Ha]; [left; exact Ha | right; lia]. Qed.

Lemma cm_pc_entry : A_catalogue_matchP = reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH.
Proof. vm_compute. reflexivity. Qed.

(* S1's footprint: the stack window and the four runtime cells it loads (F1.md). *)
Definition cm_R1 (S : Z) : list (Z * Z) :=
  [(S - 9136, S); (A.AsanRT.GOT_CELL_K, A.AsanRT.GOT_CELL_K + 8); (A.AsanRT.CELL_K, A.AsanRT.CELL_K + 8);
   (A.AsanRT.GOT_UAR, A.AsanRT.GOT_UAR + 8); (A.AsanRT.UAR, A.AsanRT.UAR + 4)].

Lemma cm_spZ : forall regs, spZ regs = bv_unsigned (reg_get regs 2).
Proof. reflexivity. Qed.
Lemma cm_getr10 : forall regs, lib.Reusable.YK11.getr regs 10 = reg_get regs 10.
Proof. reflexivity. Qed.
Lemma cm_getr11 : forall regs, lib.Reusable.YK11.getr regs 11 = reg_get regs 11.
Proof. reflexivity. Qed.

Definition cm_rg (regs : bvmap 5 word) (r : Z) : word := reg_get regs (Z_to_bv 5 r).

(* The register file S1's run starts from: the entry registers, with sp / a0 / a1 written by their values. *)
Definition cm_R0 (regs : bvmap 5 word) (S f len : Z) : bvmap 5 word :=
  lib.Lib.Frame.mkR (cm_rg regs 1) (Z_to_bv 64 S) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 5) (cm_rg regs 6)
    (cm_rg regs 7) (cm_rg regs 8) (cm_rg regs 9) (Z_to_bv 64 f) (Z_to_bv 64 len) (cm_rg regs 12) (cm_rg regs 13)
    (cm_rg regs 14) (cm_rg regs 15) (cm_rg regs 16) (cm_rg regs 17) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20)
    (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27)
    (cm_rg regs 28) (cm_rg regs 29) (cm_rg regs 30) (cm_rg regs 31).

Lemma cm_R0_eqv : forall regs f len, lib.Reusable.YK11.getr regs 10 = w64 f -> lib.Reusable.YK11.getr regs 11 = w64 len ->
  lib.Lib.Regs6ss.xregs_eqv regs (cm_R0 regs (spZ regs) f len).
Proof.
  intros regs f len H10 H11. unfold cm_R0, cm_rg. apply lib.Lib.Regs6ss.mkR_eqv_of; try reflexivity.
  - unfold spZ. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
  - transitivity (lib.Reusable.YK11.getr regs 10); [reflexivity | exact H10].
  - transitivity (lib.Reusable.YK11.getr regs 11); [reflexivity | exact H11].
Qed.

(* The register file at the `jal __asan_stack_malloc_2` (0x84504): cmS1K's state (F1.v:74-82). *)
Definition cm_R1st (regs : bvmap 5 word) (S f len : Z) : bvmap 5 word :=
  lib.Lib.Frame.mkR (cm_rg regs 1) (Z_to_bv 64 (reac_box_catalogue_match_F1.CA S)) (cm_rg regs 3) (cm_rg regs 4)
    (cm_rg regs 5) (cm_rg regs 6) (cm_rg regs 7) (Z_to_bv 64 S) (Z_to_bv 64 (reac_box_catalogue_match_F1.CA S))
    (Z_to_bv 64 192) (lib.Lib.Mem.wa A.AsanRT.CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (cm_rg regs 13) (cm_rg regs 14)
    (cm_rg regs 15) (cm_rg regs 16) (cm_rg regs 17) (cm_rg regs 18) (Z_to_bv 64 f) (Z_to_bv 64 len)
    (lib.Lib.Mem.wa A.AsanRT.ASAN_K) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26)
    (cm_rg regs 27) (cm_rg regs 28) (cm_rg regs 29) (cm_rg regs 30) (cm_rg regs 31).

(* The same registers after the `jal __asan_stack_malloc_2` (ra = 0x84508), at the allocator's entry 0x3d8bc. *)
Definition cm_R1j (regs : bvmap 5 word) (S f len : Z) : bvmap 5 word :=
  lib.Lib.Frame.mkR (Z_to_bv 64 0x84508) (Z_to_bv 64 (reac_box_catalogue_match_F1.CA S)) (cm_rg regs 3) (cm_rg regs 4)
    (cm_rg regs 5) (cm_rg regs 6) (cm_rg regs 7) (Z_to_bv 64 S) (Z_to_bv 64 (reac_box_catalogue_match_F1.CA S))
    (Z_to_bv 64 192) (lib.Lib.Mem.wa A.AsanRT.CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (cm_rg regs 13) (cm_rg regs 14)
    (cm_rg regs 15) (cm_rg regs 16) (cm_rg regs 17) (cm_rg regs 18) (Z_to_bv 64 f) (Z_to_bv 64 len)
    (lib.Lib.Mem.wa A.AsanRT.ASAN_K) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26)
    (cm_rg regs 27) (cm_rg regs 28) (cm_rg regs 29) (cm_rg regs 30) (cm_rg regs 31).

(* The entry saves (F1.v:65-66 at the entry registers ra s0 .. s10). *)
Definition cm_saves (regs : bvmap 5 word) :=
  reac_box_catalogue_match_F1.cmSAVES (cm_rg regs 1) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19)
    (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26).

(* The one discharge of the stretches' `mem_inv rsegs m` premise (a Theorem Labs lane wave rule 13:49Z: contracts and stretches keep
   mem_inv, met at a cut by the MemNorm normalize route): each stretch runs on `normalize rsegs mr`, where mem_inv holds
   outright (MemNorm.mem_inv_normalize); the run moves back to mr across mem_rel_normalize, whose ro_agree is ctl_rt_C's
   4th part at that cut (cm_S1, cm_base, cm_cut_base). Swap this lemma if the route changes. *)
Lemma cm_mem_inv_norm : forall m : word -> option byte,
  lib.Lib.Mem.mem_inv A.Img0.rsegs (A.MemNorm.normalize A.Img0.rsegs m).
Proof. exact (A.MemNorm.mem_inv_normalize A.Img0.rsegs). Qed.

(* ---- Route (C): the run's shadow premise from the cut's regions ----
   reac_box_catalogue_match_shadow_R f len S FS (a Theorem Labs lane's R, reac_box_catalogue_match_c.v) lies inside
   ctl_rt_C's regions at any journal state with the window in the stack, FS = ly_F ly and f's block live: the window
   in the stack's zero-shadow range (Z), the class blocks 0-2 in the fake-stack frames area (FA), the input's words
   in its live block's cover (L), the catalogue's and BC's words in the image's shadow (I). *)
Lemma cm_R_cut : forall (ly : alayout) (S0 : astate) (f len S Lf a : Z),
  lib.Reusable.YG0f.ly_stk_lo ly <= S - 9136 -> S <= lib.Reusable.YG0f.ly_stk_hi ly ->
  lib.Reusable.YG0f.ly_stk_lo ly mod 8 = 0 -> lib.Reusable.YG0f.ly_F ly mod 8 = 0 ->
  (50 <= len -> In (f, Lf) (lib.Reusable.YG0d.ablocks B ly S0) /\ 50 <= lib.Reusable.YG00.req_size Lf) ->
  reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R f len S (lib.Reusable.YG0f.ly_F ly) a ->
  A.ACtlRtC.cut_shadow B ly S0 a \/ A.ACtlRtC.img_shadow a.
Proof.
  intros ly S0 f len S Lf a Hlo Hhi Hlo8 HF8 Hblk Ha.
  unfold reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R in Ha.
  destruct Ha as [Ha|[(c & Hc & Ha)|(L & [Ha|[Ha|Ha]])]].
  - left. right; right; left.
    exists (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly).
    split; [left; reflexivity|]. cbn [fst snd].
    unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K,
      reac_box_catalogue_match_c.CM_K in *.
    Z.div_mod_to_equations. lia.
  - left. right; right; right.
    unfold A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R, A.Prog.asan_stack_malloc_c.fs_frame,
      A.Prog.asan_stack_malloc_c.fs_B, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF,
      lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
    destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; try lia; Z.div_mod_to_equations; lia.
  - left. right; left. destruct (Hblk L) as (Hin & Hreq). exists f, Lf. split; [exact Hin|].
    destruct Ha as (_ & Ha).
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
    Z.div_mod_to_equations. lia.
  - right. exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)). destruct Ha as (_ & Ha).
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K,
      reac_box_catalogue_match_c.CM_T, A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in *.
    split; [unfold lib.Reusable.YG0f.SHADOW_OFF in *; Z.div_mod_to_equations; lia|].
    unfold lib.Reusable.YG0f.shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  - right. exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)). destruct Ha as (_ & Ha).
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K,
      A.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE_BC, A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in *.
    split; [unfold lib.Reusable.YG0f.SHADOW_OFF in *; Z.div_mod_to_equations; lia|].
    unfold lib.Reusable.YG0f.shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow premise at the normalized memory of a journal state, from ctl_rt_C there (its cut and image
   regions), the layout's alignments (layout_ok: lo_top's page_aligned stack bottom, lo_F_al) and cm_R_cut. *)
Lemma cm_srw_C : forall (ly : alayout) (S0 : astate) (W : world tfibsegs) (m : word -> option byte) (md : Model)
    (f len S Lf : Z),
  AR tfibsegs B ly S0 W m md -> A.ACtlRtC.ctl_rt_C B ly S0 m ->
  lib.Reusable.YG0f.ly_stk_lo ly <= S - 9136 -> S <= lib.Reusable.YG0f.ly_stk_hi ly ->
  (50 <= len -> In (f, Lf) (lib.Reusable.YG0d.ablocks B ly S0) /\ 50 <= lib.Reusable.YG00.req_size Lf) ->
  A.ShadowRwOn.shadow_rw_on
    (reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R f len S (lib.Reusable.YG0f.ly_F ly))
    (A.MemNorm.normalize A.Img0.rsegs m).
Proof.
  intros ly S0 W m md f len S Lf HAR (_ & HCUT & HIMG & HROA) Hlo Hhi Hblk.
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as HLO.
  destruct HLO as [_ _ _ _ _ HFal _ _ _ _ _ _ _ _ Hltop _ _ _ _ _ _].
  destruct Hltop as (_ & _ & _ & _ & Hloal & _).
  unfold lib.Reusable.YG0f.page_aligned in HFal, Hloal.
  assert (A8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
  { intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q Hq]. rewrite Hq.
    replace (q * 4096) with ((q * 512) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (A8 _ Hloal) as H8lo. pose proof (A8 _ HFal) as H8F.
  apply A.ShadowRwOnT.shadow_rw_on_normalize; [exact HROA|].
  apply (A.ShadowRwOn.shadow_rw_on_mono _ _ m (fun a Ha => cm_R_cut ly S0 f len S Lf a Hlo Hhi H8lo H8F Hblk Ha)).
  exact (A.ShadowRwOn.shadow_rw_on_union _ _ m HCUT HIMG).
Qed.

(* S1 as a world step: from the spec's precondition at the entry through the `jal __asan_stack_malloc_2` (0x84504)
   to the allocator's entry 0x3d8bc, with the journal at the reached memory (the run wrote only the window
   [S - 9136, S), the stack window of CM_STK) and the twelve entry saves at [S - 96, S). *)
Lemma cm_S1 : forall ly S0 W regs mem md ch f len Lf (Q : world tfibsegs -> config -> Prop),
  afn_pre tfibsegs B CM_STK ly S0 W regs mem md ch ->
  arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem) ->
  lib.Reusable.YK11.getr regs 10 = w64 f -> lib.Reusable.YK11.getr regs 11 = w64 len -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  (50 <= len -> In (f, Lf) (ablocks B ly S0) /\ 50 <= req_size Lf) ->
  (forall (mc : word -> option byte) (model' : Model),
     ajournal tfibsegs B CM_STK (spZ regs) [] ly S0 W mem md [] ly S0 W mc model' 0 ->
     lib.Lib.Step.rw_cells A.Img0.rsegs mc (spZ regs - 96) (cm_saves regs) ->
     SRr tfibsegs W (mkCfg (lib.Lib.MState.MS (cm_R1j regs (spZ regs) f len) fp_regs
       (Z_to_bv 64 0x3d8bc) fp_csr None mc (seg_rom tfibsegs)) model') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_catalogue_matchP regs mem md) Q.
Proof.
  intros ly S0 W regs mem md ch f len Lf Q HPRE HRO H10 H11 Rf Rlen HBLK K.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (S16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold CM_STK in Hslo, Hpres.
  assert (HS64 : spZ regs < 2 ^ 64) by lia.
  assert (HK : 9136 <= spZ regs) by lia.
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= spZ regs - 9136) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HAE : spZ regs <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  pose proof (CTLRT CTS LAWS RLO RHI ly S0 W mem md HAR (cm_arodataP _ HRO)) as CRT.
  pose proof CRT as (ACm & _ & _ & ROm).
  assert (HRm : A.MemNorm.ro_agree A.Img0.rsegs mem) by exact ROm.
  assert (STm : lib.Lib.Frame.stk A.Img0.rsegs mem (spZ regs - 9136) (spZ regs)).
  { apply (cm_stk_present (w_H W)); [lia | lia | intros a Ha; apply Hpres; lia]. }
  assert (HIMG : A.Prog.ImgBounds.IMG_HI <= spZ regs - 9136).
  { unfold A.Prog.ImgBounds.IMG_HI. pose proof HHM as HHM'. unfold A.AsanRT.HIGHMEM_BEG in HHM'. lia. }
  pose proof (ajournal_init tfibsegs B CM_STK [] ly S0 W regs mem md ch HPRE) as J0.
  rewrite A.ProgBridge.cfg_at_MS, cm_pc_entry.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv tfibsegs W (cm_R0 regs (spZ regs) f len) regs fp_regs
           (Z_to_bv 64 reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH) fp_csr None mem (seg_rom tfibsegs) md Q);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (cm_R0_eqv regs f len H10 H11))].
  apply (cm_lift_base W (cm_R0 regs (spZ regs) f len) fp_regs
           (Z_to_bv 64 reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH) fp_csr mem md (cm_R1 (spZ regs))
           (fun s => exists mc, s = lib.Lib.MState.MS (cm_R1j regs (spZ regs) f len) fp_regs
                                  (Z_to_bv 64 0x3d8bc) fp_csr None mc
                                  (seg_rom tfibsegs) /\
                      lib.Lib.Frame.munch [(spZ regs - 9136, spZ regs)] (A.MemNorm.normalize A.Img0.rsegs mem) mc /\
                      lib.Lib.Step.rw_cells A.Img0.rsegs mc (spZ regs - 96) (cm_saves regs))
           Q HRm).
  - eapply lib.Lib.ExecF.evtF_cut with
      (P := fun s => exists mc, s = lib.Lib.MState.MS (cm_R1st regs (spZ regs) f len) fp_regs
                                     (Z_to_bv 64 reac_box_catalogue_match_F1.CM_STACK_MALLOC_CALL) fp_csr None mc
                                     (seg_rom tfibsegs) /\
                         lib.Lib.Frame.munch [(spZ regs - 9136, spZ regs)] (A.MemNorm.normalize A.Img0.rsegs mem) mc /\
                         lib.Lib.Step.rw_cells A.Img0.rsegs mc (spZ regs - 96) (cm_saves regs)).
    2: { intros ms1 (mc & -> & MU & SAV). unfold cm_R1st, reac_box_catalogue_match_F1.CM_STACK_MALLOC_CALL.
         change (seg_rom tfibsegs) with (lib.Lib.PropExec.seg_rom A.Img0.rsegs).
         apply reac_box_catalogue_match_F2.cm_jal_sm2_F.
         exists mc. split; [reflexivity|]. split; [exact MU | exact SAV]. }
    refine (reac_box_catalogue_match_F1.cm_entry_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
              (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
              (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
              (A.MemNorm.normalize A.Img0.rsegs mem) f len (spZ regs) (ly_F ly) Rf Rlen HS64 S16 HK
              (A.MemNormTr.stk_normalize_ro mem _ _ HRm HIMG STm)
              (cm_mem_inv_norm mem)
              (A.MemNormTr.asan_cells_normalize mem HRm ACm)
              (cm_srw_C ly S0 W mem md f len (spZ regs) Lf HAR CRT ltac:(lia) ltac:(lia) HBLK) HHM HAE
              _ _ (cm_rg regs 5) (cm_rg regs 6) (cm_rg regs 7) (cm_rg regs 12) (cm_rg regs 13) (cm_rg regs 14)
              (cm_rg regs 15) (cm_rg regs 16) (cm_rg regs 17) (cm_rg regs 28) (cm_rg regs 29) (cm_rg regs 30)
              (cm_rg regs 31) _ _ _ _ _ _).
    + intros mc MU _ _ _ _ _ _ SAV. exists mc. split; [reflexivity|]. split; [exact MU | exact SAV].
    + apply cm_rng_Hk; [intros a Ha; apply (cm_inR_In _ (spZ regs - 9136) (spZ regs)); [left; reflexivity | lia]|].
      exact (cm_win_vis (spZ regs) ly S0 W mem md [] ly S0 W mem md 0 (spZ regs - 9136) 9136 J0
               ltac:(lia) ltac:(unfold CM_STK; lia) ltac:(lia) ltac:(lia)).
    + apply cm_rng_Hk; [intros a Ha; apply (cm_inR_In _ A.AsanRT.GOT_CELL_K (A.AsanRT.GOT_CELL_K + 8));
                        [right; left; reflexivity | lia]|].
      apply cm_rt_vis; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.GOT_CELL_K; lia.
    + apply cm_rng_Hk; [intros a Ha; apply (cm_inR_In _ A.AsanRT.CELL_K (A.AsanRT.CELL_K + 8));
                        [right; right; left; reflexivity | lia]|].
      apply cm_rt_vis; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.CELL_K; lia.
    + apply cm_rng_Hk; [intros a Ha; apply (cm_inR_In _ A.AsanRT.GOT_UAR (A.AsanRT.GOT_UAR + 8));
                        [right; right; right; left; reflexivity | lia]|].
      apply cm_rt_vis; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.GOT_UAR; lia.
    + apply cm_rng_Hk; [intros a Ha; apply (cm_inR_In _ A.AsanRT.UAR (A.AsanRT.UAR + 4));
                        [right; right; right; right; left; reflexivity | lia]|].
      apply cm_rt_vis; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.UAR; lia.
  - intros ms' s0 model' (mc & -> & MU & SAV) Hrel Hsame Hfs _ Hsbm.
    destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as (Ems & REL). rewrite Ems.
    apply K.
    + refine (AJF LAWS ctrl_wx CM_STK (spZ regs) [] ly S0 W mem md [] ly S0 W
                (lib.Lib.MState.MS (cm_R0 regs (spZ regs) f len) fp_regs
                   (Z_to_bv 64 reac_box_catalogue_match_c.REAC_BOX_CATALOGUE_MATCH) fp_csr None mem (seg_rom tfibsegs))
                ms' md model' 0 _ [(spZ regs - 9136, spZ regs)] J0 Hfs (cm_fp_avoids_Hk (w_H W) _) _ Hsbm _).
      * exact (A.MemNorm.munch_rel A.Img0.rsegs _ mem (A.MemNorm.normalize A.Img0.rsegs mem) (ms_mem ms') mc
                 (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem HRm) REL Hsame MU).
      * intros a Ha Hin.
        assert (Hw : spZ regs - 9136 <= a < spZ regs).
        { destruct (Z_le_gt_dec (spZ regs - 9136) a); destruct (Z_lt_ge_dec a (spZ regs)); try lia;
            exfalso; apply Hin; cbn [lib.Lib.Frame.outside]; (split; [lia | exact I]). }
        left. unfold CM_STK. lia.
    + exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ REL SAV).
Qed.

(* ==== The walk, part 3: the class-2 fake-stack site (`jal __asan_stack_malloc_2` at 0x84504) =================
   The one local lemma of this walk that touches the allocator (brief). It is YC85.aj_stack_malloc_atS
   (lib/A/Prog/YC85.v:291-353) at cid = 2, its proof text with this file's names (segs := tfibsegs, ASM := ASM2,
   errno_low := PALib's pal_env, stack_malloc_progress := SMP, segs_low := ctrl_segs_low), with four more conjuncts
   in the post: the call's ecall_pre and the pieces of astack_malloc_realizes' post (YG0d.v:290-300) that
   ProgWorld's ctl_fs_of_astack takes (AR at the new state, the kept non-owned bytes, the window's presence). *)
Lemma cm_sm2_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  lib.Reusable.YK11.getr regsT 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regsT 4 = w64 (as_tp B) ->
  lib.Reusable.YK11.getr regsT 1 = raw -> lib.Reusable.YK0s.ret_ok raw ->
  count_cid 2 (frames Sc) < fs_frames 2 ->
  SRr tfibsegs W (mkCfg (lib.Reusable.YK11.mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) 2)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
     c2 = mkCfg (lib.Reusable.YK11.mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md ((2, pos) :: own) lyc S2 W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ lib.Reusable.YK11.getr regs2 10 = w64 (frame_addr lyc 2 pos) /\
     ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (2, pos) :: frames Sc /\ ~ In (2, pos) (frames Sc) /\
     st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
     zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc 2 pos) (fs_frame_bytes 2) /\
     rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc 2 pos + fs_frame_bytes 2 - 8) = Some (flag_addr lyc 2 pos) /\
     acall_kept tfibsegs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
     ajournal tfibsegs B ESTACK (sp0 + o) [] lyc Sc W memT mdc [(2, pos)] lyc S2 W mem2 md2 0 /\
     (exists f, S2 = set_fs f Sc) /\
     ecall_pre tfibsegs B lyc Sc W regsT memT mdc /\ AR tfibsegs B lyc S2 W mem2 md2 /\
     (forall a, frame_addr lyc 2 pos <= a < frame_addr lyc 2 pos + fs_frame_bytes 2 -> apresent (w_H W) mem2 a) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a ->
        ~ (spZ regsT - ESTACK <= a < spZ regsT) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
     (forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
assert (errno_low : api_env tfibsegs B) by (destruct TL; assumption).
assert (Hcid : 0 <= 2 <= 10) by lia.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (SMP Sc 2 HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc 2 HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake 2 pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM2 lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : lib.Reusable.YG01.blocks S2 = lib.Reusable.YG01.blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal tfibsegs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(2, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal tfibsegs B LAWS ctrl_segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2
          (fun _ => False) [] [(2, pos)] 0);
[exact HAR2 | apply lib.Reusable.YG0f.layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((2, pos) :: own) with ([(2, pos)] ++ own).
eapply (ajournal_sub tfibsegs B LAWS ctrl_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
pose proof HJ1 as HJ1s. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exists f; exact ES2|]]].
- eapply (acall_kept_of_journal tfibsegs B ctrl_segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
  intros b m i Hb Hi _. rewrite Eab2. exact Hb.
- split; [exact HPRE|]. split; [exact HAR2|]. split; [exact Hfpres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ==== The walk, part 4: the base bundle =========================================================================
   Each stretch runs on `normalize mr`, mr the real memory at its start (the entry, or a call's return). cmBB is the
   source's Section hypotheses (reac_box_catalogue_match.v:115-141) at that memory; cm_base derives them from the
   journal state at mr (AR, the window's presence, the static stack bounds) and the spec's premises. *)

(* At a visible address the core's view is ctrl's mrd (ProgWorld.v:559-567, proof text verbatim). *)
Lemma cm_aview_vis_mrd : forall (W : world tfibsegs) (mem : word -> option byte) (a : Z),
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd A.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Hh.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, lib.Lib.Mem.mrd.
  rewrite Hh. reflexivity.
Qed.

(* A byte the view shows is a byte ctrl's mrd returns (ProgWorldShadow.v:34-47, proof text verbatim). *)
Lemma cm_view_mrd : forall (W : world tfibsegs) (m : word -> option byte) (s v : Z),
  aview tfibsegs (w_H W) m s = Some v ->
  exists b, lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 s) = Some b /\ bv_unsigned b = v.
Proof.
  intros W m s v Hv.
  destruct (w_H W (Z_to_bv 64 s)) eqn:Hh.
  - exfalso. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    rewrite Hh in Hv. unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (lib.Reusable.YK04.memory_read1_hidden tfibsegs _ (w_Hoff W) _ Hh) in Hv.
    discriminate Hv.
  - rewrite (cm_aview_vis_mrd W m s Hh) in Hv.
    destruct (lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 s)) as [b|]; [|discriminate Hv].
    exists b. split; [reflexivity|]. injection Hv as Hv. exact Hv.
Qed.

(* The return address is even (A/KindBGlue.v:49-69, proof text verbatim). *)
Lemma cm_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma cm_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.
Lemma cm_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> lib.Lib.MState.ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, cm_mod2_land; apply cm_land_m2).
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Lemma cm_u64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Hx.
Qed.

(* No segment of rsegs reaches IMG_HI (MemNormTr.v:33-39). *)
Lemma cm_seg_none : forall a, A.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 -> find_segment A.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment A.Img0.rsegs a 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (A.BzBridge.find_segment_below A.Img0.rsegs A.Prog.ImgBounds.IMG_HI a 1 s A.MemNormTr.rsegs_below_img E
              ltac:(lia)) as [L|L]; lia.
Qed.
Lemma cm_seg_rom_none : forall a, A.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a) = None.
Proof.
  intros a Ha. apply A.MemNorm.seg_rom_unmapped.
  rewrite (lib.Lib.Mem.wa_unsigned a ltac:(unfold A.Prog.ImgBounds.IMG_HI in Ha; lia)). apply cm_seg_none. exact Ha.
Qed.

(* The thread cells, moved along any map of byte facts (both directions of MemNorm.bytes_at_rel). *)
Lemma cm_tls_map : forall (m m' : word -> option byte),
  (forall a bs, lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs) ->
  forall TP DT TS C T DB k, A.Prog.asan_stack_malloc_c.asan_tls_cells m TP DT TS C T DB k ->
  A.Prog.asan_stack_malloc_c.asan_tls_cells m' TP DT TS C T DB k.
Proof.
  intros m m' BR TP DT TS C T DB k
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  exact (conj (BR _ _ H1) (conj (BR _ _ H2) (conj (BR _ _ H3) (conj (BR _ _ H4) (conj (BR _ _ H5) (conj H6
    (conj (BR _ _ H7) (conj (BR _ _ H8) (conj (BR _ _ H9) (conj (BR _ _ H10)
    (conj (ex_intro _ tb (ex_intro _ te (BR _ _ H11))) (conj (BR _ _ H12) (conj (BR _ _ H13) (conj (BR _ _ H14)
    (conj (BR _ _ H15) (conj (BR _ _ H16) (conj (BR _ _ H17) (conj H18 (BR _ _ H19))))))))))))))))))).
Qed.

(* fp moves to the normalized memory: its byte facts by bytes_at_rel, its side-stack range (above IMG_HI) by
   stk_normalize_ro. *)
Lemma cm_fp_normalize : forall cs m TP FS lo hi Wr D, A.MemNorm.ro_agree A.Img0.rsegs m ->
  A.Prog.RcAsanFP.fp cs m TP FS lo hi Wr D ->
  A.Prog.RcAsanFP.fp cs (A.MemNorm.normalize A.Img0.rsegs m) TP FS lo hi Wr D.
Proof.
  intros cs m TP FS lo hi Wr D HRO (DT & TS & C & T & DB & k & HC & HTP & HPL & H88 & H96 & HCL & HREST).
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs m HRO) as REL.
  pose proof (fun a bs => proj1 (A.MemNorm.bytes_at_rel A.Img0.rsegs m (A.MemNorm.normalize A.Img0.rsegs m) a bs REL))
    as BF.
  exists DT, TS, C, T, DB, k.
  refine (conj (cm_tls_map _ _ BF _ _ _ _ _ _ _ HC) (conj (BF _ _ HTP) (conj _ (conj (BF _ _ H88) (conj (BF _ _ H96)
    (conj _ HREST)))))).
  - destruct HPL as (P1 & P2 & P3 & P4 & P5). refine (conj P1 (conj P2 (conj P3 (conj P4 _)))).
    apply A.MemNormTr.stk_normalize_ro; [exact HRO | | exact P5].
    unfold A.Prog.ImgBounds.IMG_HI. unfold A.Prog.asan_stack_malloc_c.ASAN_GT in P3. lia.
  - eapply Forall_impl; [|exact HCL]. intros c (Hc & h & flags & B1 & B2 & B3 & B4).
    split; [exact Hc|]. exists h, flags. exact (conj (BF _ _ B1) (conj (BF _ _ B2) (conj B3 B4))).
Qed.

(* A byte view of a range gives ctrl's bytes_at. *)
Lemma cm_bytes_of_view : forall (W : world tfibsegs) (m : word -> option byte) (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat ->
     aview tfibsegs (w_H W) m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs.
Proof.
  intros W m a bs H0 H1 Hv. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (cm_view_mrd W m _ _ (Hv i Hi)) as (b & Hb & Hbu). unfold lib.Lib.Mem.wa. rewrite Hb.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Hbu.
Qed.

(* One byte of a bytes_at. *)
Lemma cm_bytes_sub1 : forall (m : word -> option byte) a bs (i : nat) b,
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs -> nth_error bs i = Some b ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|]. intros j Hj. cbn [length] in Hj.
  assert (j = 0%nat) as -> by lia. cbn [nth_error]. rewrite Z.add_0_r. rewrite <- Hn. exact (H i Hi).
Qed.

(* The view's shadow value at a granule of an 8-aligned base (ProgWorldShadow.v:27-56, proof text verbatim). *)
Lemma cm_byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia.
Qed.
Lemma cm_shadow_eq : forall q a, q mod 8 = 0 ->
  lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF q + (a - q) / 8 = A.AsanRT.shadow_addr a.
Proof.
  intros q a Hq. rewrite <- (lib.Reusable.YG0v.shadow_of_addr_aligned_off _ q (a - q) Hq).
  replace (q + (a - q)) with a by lia.
  unfold lib.Reusable.YG0v.shadow_of_addr, A.AsanRT.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K. lia.
Qed.

(* A registered global's bytes are addressable: globs_marked gives block_shadow for (q, sz); the rest is
   ctl_block_shadow_of_AR's proof (ProgWorldShadow.v:58-82) with AR_shadow_law replaced by globs_marked. *)
Lemma cm_glob_addr : forall ly S W m md q sz lo len,
  AR tfibsegs B ly S W m md -> In (q, sz) GLOBS -> 0 <= lo -> q <= lo -> 0 <= len -> lo + len <= q + sz ->
  lo + len <= A.AsanRT.LOWMEM_END ->
  A.AsanRT.addressable m lo len.
Proof.
  intros ly S W m md q sz lo len HAR Hin H0 Hlo Hlen Hhi Hlow.
  pose proof (HGM ly S W m md q sz Hin HAR) as (Hq8 & Hrs & Hsh).
  unfold A.AsanRT.addressable. split; [exact H0|]. split; [exact Hlen|]. split.
  { unfold A.AsanRT.APPMEM_END, A.AsanRT.LOWMEM_END in *. lia. }
  intros i Hi. unfold A.AsanRT.addr_byte. split.
  - unfold A.AsanRT.app_mem. left. lia.
  - assert (Hj : 0 <= (lo + i - q) / 8 < (sz + 7) / 8) by (Z.div_mod_to_equations; lia).
    specialize (Hsh _ Hj). rewrite (cm_shadow_eq q (lo + i) Hq8) in Hsh.
    destruct (cm_view_mrd W m _ _ Hsh) as (b & Hb & Hbu).
    exists b. split; [exact Hb|].
    assert (Hsm : bv_unsigned b < 128).
    { rewrite Hbu. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). destruct (_ <? _); lia. }
    unfold A.AsanRT.shadow_ok. rewrite (cm_byte_signed_small b Hsm), Hbu.
    destruct (Z.ltb_spec ((lo + i - q) / 8) (sz / 8)) as [Hl | Hl].
    + left. reflexivity.
    + right. clear -Hl Hq8 Hlo Hhi Hi Hrs. Z.div_mod_to_equations. lia.
Qed.

Lemma cm_tbl_eq : A_CM_TBL = reac_box_catalogue_match_c.CM_T.
Proof. vm_compute. reflexivity. Qed.

(* The table bytes: the read-only view equals the rom byte. *)
Lemma cm_HT_of_view : forall (W : world tfibsegs) mr a,
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mr a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)) ->
  lib.Lib.Mem.mrd A.Img0.rsegs mr (lib.Lib.Mem.wa a) = lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a).
Proof.
  intros W mr a Hh Hv. rewrite (cm_aview_vis_mrd W mr a Hh) in Hv.
  change (lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a)) with (seg_rom tfibsegs (Z_to_bv 64 a)).
  change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a).
  destruct (lib.Lib.Mem.mrd A.Img0.rsegs mr (Z_to_bv 64 a)) as [b|];
    destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [c|]; cbn [option_map] in Hv; try discriminate Hv; [|reflexivity].
  injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

Lemma cm_arodataS : forall rd, A.Prog.CtrlBase.arodata_okP segs RLO RHI B rd -> arodata_okS tfibsegs B RLO RHI rd.
Proof. intros rd H a Ha. apply H. destruct Ha as [Ha|Ha]; [left; exact Ha | right; lia]. Qed.

(* The class-0/1/2 side-stack ranges of fp_w lie in [F, F + 3182592) or in its shadow. *)
Lemma cm_fpw_in : forall F d, In d (A.Prog.RcAsanFP.fp_w [0%nat; 1%nat; 2%nat] F) -> 0 <= F ->
  (F <= fst d /\ snd d <= F + 3182592) \/
  (A.AsanRT.shadow_addr F <= fst d /\ snd d <= A.AsanRT.shadow_addr (F + 3182592)).
Proof.
  intros F d Hd HF. unfold A.Prog.RcAsanFP.fp_w, A.Prog.RcAsanFP.fp_w1 in Hd. cbn [flat_map app] in Hd.
  unfold A.Prog.asan_stack_malloc_c.fs_hint, A.Prog.asan_stack_malloc_c.fs_flag, A.Prog.asan_stack_malloc_c.fs_frame,
    A.Prog.asan_stack_malloc_c.fs_M, A.Prog.asan_stack_malloc_c.fs_B in Hd.
  cbn [Z.of_nat Pos.of_succ_nat] in Hd.
  repeat match type of Hd with context [2 ^ ?e] =>
    let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v in Hd end.
  unfold A.AsanRT.shadow_addr in *.
  repeat (destruct Hd as [<-|Hd];
    [cbn [fst snd]; first [left; split; lia | right; split; (apply Z.add_le_mono_r; apply Z.div_le_mono; lia)] |]).
  destruct Hd.
Qed.

(* fp_dj from a pointwise separation. *)
Lemma cm_fp_dj_sep : forall (Wr D : list lib.Lib.Frame.ivl),
  (forall w, In w Wr -> forall d, In d D -> snd w <= fst d \/ snd d <= fst w) -> A.Prog.RcAsanFP.fp_dj Wr D.
Proof.
  intros Wr D H. unfold A.Prog.RcAsanFP.fp_dj. apply Forall_forall. intros w Hw. apply Forall_forall.
  intros d Hd. exact (H w Hw d Hd).
Qed.

Definition cmBB (m : word -> option byte) (tp : word) (S f len FS : Z) (fb : list byte) : Prop :=
  S < 2 ^ 64 /\ S mod 16 = 0 /\ 9136 <= S /\ A.AsanRT.HIGHMEM_BEG <= S - 9136 /\ S <= A.AsanRT.APPMEM_END /\
  lib.Lib.Frame.stk A.Img0.rsegs m (S - 9136) S /\
  (forall a, S - 9136 <= a < S -> lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a) = None) /\
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at A.Img0.rsegs m f fb /\
     (f + 50 <= S - 9136 \/ S <= f)) /\
  (forall a, reac_box_catalogue_match_c.CM_T <= a < reac_box_catalogue_match_c.CM_T + 3256 ->
     lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a)) /\
  lib.Lib.Mem.mem_inv A.Img0.rsegs m /\ A.AsanRT.asan_cells m /\
  A.ShadowRwOn.shadow_rw_on (reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R f len S FS) m /\
  A.AsanRT.addressable m (S - 9136) 9136 /\
  (50 <= len -> A.AsanRT.addressable m f 50 /\ A.AsanRT.app_mem (f + 50)) /\
  A.AsanRT.addressable m reac_box_catalogue_match_c.CM_T 3256 /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m A.Prog.bcmp_wrap_c.REAL_BCMP
    (lib.Lib.Mem.le8 (lib.Lib.Mem.wa A.Prog.bcmp_wrap_c.BCMP)) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m A.Prog.bcmp_wrap_c.REAL_MEMCMP
    (lib.Lib.Mem.le8 (lib.Lib.Mem.wa A.Prog.memcmp_c.MEMCMP)) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m A.Prog.bcmp_wrap_c.GOT_CF (lib.Lib.Mem.le8 (lib.Lib.Mem.wa A.Prog.bcmp_wrap_c.CF)) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (A.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1] /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (A.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1] /\
  A.Prog.RcAsanFP.fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
    (reac_box_catalogue_match_c.reac_box_catalogue_match_W S) (reac_box_catalogue_match_c.reac_box_catalogue_match_D f len) /\
  reac_box_catalogue_match_c.reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

Lemma cm_base : forall ly S0 W mem md own lyc Sc Wc mr mdc k S f len fb Lf (tp : word),
  ajournal tfibsegs B CM_STK S [] ly S0 W mem md own lyc Sc Wc mr mdc k ->
  arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem) ->
  bv_unsigned tp = A.AsanRT.RT_TP ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  (50 <= len -> In (f, Lf) (ablocks B lyc Sc) /\ 50 <= req_size Lf /\
     forall i, (i < 50)%nat -> aview tfibsegs (w_H Wc) mr (f + Z.of_nat i) = Some (bv_unsigned (nth i fb (Z_to_bv 8 0)))) ->
  (forall a, A_CM_TBL <= a < A_CM_TBL + CM_ROWS ->
     in_roP tfibsegs RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  In (A_CM_TBL, CM_ROWS) GLOBS ->
  cmBB (A.MemNorm.normalize A.Img0.rsegs mr) tp S f len (ly_F lyc) fb.
Proof.
  intros ly S0 W mem md own lyc Sc Wc mr mdc k S f len fb Lf tp J HRO0 Htp Rf Rlen Hfb HREC HTBL HGL.
  pose proof J as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
  pose proof Hstatic as (S16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  pose proof Hly as (_ & _ & _ & ET & EC & EF & _ & _ & _ & Eslo & Eshi & Etsd & _ & _ & ED & _ & _).
  unfold CM_STK in *.
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as HLO.
  destruct HLO as [_ _ _ _ _ _ _ _ _ _ _ Happ _ _ Hltop _ _ _ _ _ Hstkceil].
  pose proof (proj1 (Forall_forall _ _) Happ) as Happ'. unfold owned_extents in Happ'.
  pose proof (Happ' (ly_T lyc, kThreadObjSize) ltac:(right; right; left; reflexivity)) as HappT.
  pose proof (Happ' (ly_F lyc, kFakeStackSize) ltac:(right; right; right; left; reflexivity)) as HappF.
  pose proof (Happ' (ly_C lyc, 256) ltac:(do 6 right; left; reflexivity)) as HappC.
  pose proof (Happ' (ly_D lyc, 4096) ltac:(do 7 right; left; reflexivity)) as HappD.
  cbn [fst snd] in HappT, HappF, HappC, HappD. unfold in_app in HappT, HappF, HappC, HappD.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (am_tsd _ _ _ _ (proj1 HAR)) as Htsd. pose proof (TSD_TSD CTS) as Htsd'.
  unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kFakeStackSize in *.
  destruct Hltop as (_ & _ & _ & _ & _ & _ & Hhm).
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= S - 9136) by (unfold A.AsanRT.HIGHMEM_BEG, kHighMemBeg in *; lia).
  assert (HAE : S <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  assert (HIMG : A.Prog.ImgBounds.IMG_HI <= S - 9136) by (unfold A.Prog.ImgBounds.IMG_HI; lia).
  pose proof (arodata_ok_journalP tfibsegs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J (cm_arodataP _ HRO0))
    as HROc.
  pose proof (CTLRT CTS LAWS RLO RHI lyc Sc Wc mr mdc HAR HROc) as CRT.
  pose proof CRT as (ACm & _ & _ & ROm).
  assert (HRm : A.MemNorm.ro_agree A.Img0.rsegs mr) by exact ROm.
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mr HRm) as REL.
  pose proof (fun a bs => proj1 (A.MemNorm.bytes_at_rel A.Img0.rsegs mr _ a bs REL)) as BF.
  destruct (RTAR CTS LAWS lyc Sc Wc mr mdc HAR) as (_ & _ & _ & _ & HCF & _ & _ & HREAL).
  destruct HCF as (HCF1 & _ & _ & _ & _ & _ & HCF7 & _).
  pose proof (proj1 (Forall_forall _ _) HREAL) as HREAL'.
  assert (Hu : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x) by exact cm_u64.
  unfold cmBB. split; [lia|]. split; [exact S16|]. split; [lia|]. split; [exact HHM|]. split; [exact HAE|].
  split.
  { apply A.MemNormTr.stk_normalize_ro; [exact HRm | exact HIMG |].
    apply (cm_stk_present (w_H Wc)); [lia | lia | intros a Ha; apply Hpres; lia]. }
  split.
  { intros a Ha. apply cm_seg_rom_none. lia. }
  split.
  { intros H50. destruct (HREC H50) as (Hin & Hreq & Hv).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc Wc mr mdc f Lf HAR Hin) as (_ & H4096 & Hceilb & _).
    split; [lia|]. split; [lia|]. split.
    - apply BF. apply (cm_bytes_of_view Wc); [lia | rewrite Hfb; lia |]. intros i Hi. rewrite Hfb in Hi. exact (Hv i Hi).
    - left. lia. }
  split.
  { intros a Ha. rewrite <- cm_tbl_eq in Ha. destruct (HTBL a ltac:(unfold CM_ROWS; lia)) as (Hro & Hno & Hne).
    rewrite <- (A.MemNorm.mrd_rel A.Img0.rsegs mr _ (lib.Lib.Mem.wa a) REL).
    apply (cm_HT_of_view Wc).
    - destruct (A.ProgBridge.img_vis_W Wc) as (_ & _ & Hv). apply Hv.
      pose proof cm_tbl_eq as Et. unfold reac_box_catalogue_match_c.CM_T in Et. rewrite Et in Ha.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia.
    - exact (HROc a Hro Hno Hne). }
  split; [exact (cm_mem_inv_norm mr)|].
  split; [exact (A.MemNormTr.asan_cells_normalize mr HRm ACm)|].
  split; [exact (cm_srw_C lyc Sc Wc mr mdc f len S Lf HAR CRT ltac:(lia) ltac:(lia)
                  (fun H => conj (proj1 (HREC H)) (proj1 (proj2 (HREC H)))))|].
  split.
  { apply A.MemNormTr.addressable_normalize; [exact HRm|].
    exact (STKSH LAWS lyc Sc Wc mr mdc (S - 9136) 9136 HAR ltac:(lia) ltac:(lia) ltac:(lia)). }
  split.
  { intros H50. destruct (HREC H50) as (Hin & Hreq & _).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc Wc mr mdc f Lf HAR Hin) as (_ & H4096 & Hceilb & Happb & _).
    split.
    - apply A.MemNormTr.addressable_normalize; [exact HRm|].
      exact (BLKSH LAWS lyc Sc Wc mr mdc f Lf f 50 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happb.
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
      destruct Happb as (_ & [Hl | (Hh1 & Hh2)]); [left | right]; lia. }
  split.
  { apply A.MemNormTr.addressable_normalize; [exact HRm|].
    pose proof cm_tbl_eq as Et. unfold reac_box_catalogue_match_c.CM_T in Et. rewrite <- cm_tbl_eq.
    apply (cm_glob_addr lyc Sc Wc mr mdc A_CM_TBL CM_ROWS);
      [exact HAR | exact HGL | rewrite Et; lia | lia | lia | unfold CM_ROWS; lia |
       rewrite Et; unfold A.AsanRT.LOWMEM_END; lia]. }
  split.
  { apply BF. apply (HREAL' (0xa17f0, 0x97b0c)); [unfold A.AsanRT.RT_REALS; repeat (first [left; reflexivity | right])|].
    cbn [fst]. left. reflexivity. }
  split.
  { apply BF. apply (HREAL' (0xa17e8, 0x97bdc)); [unfold A.AsanRT.RT_REALS; repeat (first [left; reflexivity | right])|].
    cbn [fst]. right. left. reflexivity. }
  split; [exact (BF _ _ HCF1)|].
  split.
  { pose proof (cm_bytes_sub1 _ _ _ 14 _ (BF _ _ HCF7) eq_refl) as H.
    replace (A.Prog.bcmp_wrap_c.CF + 254) with (A.AsanRT.RT_CF + 240 + Z.of_nat 14) by reflexivity. exact H. }
  split.
  { pose proof (cm_bytes_sub1 _ _ _ 15 _ (BF _ _ HCF7) eq_refl) as H.
    replace (A.Prog.bcmp_wrap_c.CF + 255) with (A.AsanRT.RT_CF + 240 + Z.of_nat 15) by reflexivity. exact H. }
  assert (Hbnd : 0 <= ly_tsd lyc < 2 ^ 64 /\ 0 <= ly_C lyc < 2 ^ 64 /\ 0 <= ly_T lyc < 2 ^ 64 /\
                 0 <= ly_D lyc < 2 ^ 64 /\ 0 <= A.AsanRT.RT_TP + 32 < 2 ^ 64).
  { rewrite Htsd, Htsd'. unfold A.AsanRT.RT_TP. lia. }
  split.
  { rewrite Htp. apply cm_fp_normalize; [exact HRm|].
    apply (FPAR CTS LAWS lyc Sc Wc mr mdc); [exact HAR | repeat constructor | | | |].
    - unfold A.Prog.asan_stack_malloc_c.FS_SIZE. lia.
    - intros a Ha. unfold A.AsanRT.app_mem. right. lia.
    - apply cm_fp_dj_sep. intros w Hw d Hd.
      unfold reac_box_catalogue_match_c.reac_box_catalogue_match_W, reac_box_catalogue_match_c.CM_K in Hw.
      destruct Hw as [<-|[]]. cbn [fst snd].
      unfold A.Prog.RcAsanFP.fp_tls in Hd. cbn [app] in Hd.
      rewrite !Hu in Hd by lia. rewrite Htsd, Htsd' in Hd.
      unfold A.Prog.asan_stack_malloc_c.TLS_INDEX, A.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR,
        A.Prog.asan_stack_malloc_c.TSD_KEY_INITED, A.Prog.asan_stack_malloc_c.TSD_KEY,
        A.Prog.asan_stack_malloc_c.GOT_CF, A.Prog.asan_stack_malloc_c.CF, A.Prog.asan_stack_malloc_c.GOT_VERBOSITY,
        A.Prog.asan_stack_malloc_c.VERBOSITY, A.Prog.asan_stack_malloc_c.DTLS_TPOFF, A.AsanRT.RT_TP,
        A.Prog.asan_stack_malloc_c.fs_frame, A.Prog.asan_stack_malloc_c.fs_B in Hd.
      cbn [Z.of_nat] in Hd.
      repeat (destruct Hd as [<-|Hd]; [cbn [fst snd]; right; lia|]). destruct Hd.
    - unfold reac_box_catalogue_match_c.reac_box_catalogue_match_D. destruct (Z.ltb_spec len 50) as [E50|E50].
      + unfold A.Prog.RcAsanFP.fp_dj. constructor.
      + destruct (HREC E50) as (Hin & Hreq & _).
        destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc Wc mr mdc f Lf HAR Hin) as (_ & H4096 & Hceilb & Happb & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happb.
        pose proof (BLKFS LAWS lyc Sc Wc mr mdc f Lf HAR Hin) as HB. unfold kFakeStackSize in HB.
        apply cm_fp_dj_sep. intros w Hw d Hd. destruct Hw as [<-|[]]. cbn [fst snd].
        destruct (cm_fpw_in (ly_F lyc) d Hd ltac:(lia)) as [(D1 & D2) | (D1 & D2)]; [lia|].
        unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in D1, D2.
        assert (Q1 : 0 <= ly_F lyc / 8) by (apply Z.div_pos; lia).
        assert (Q2 : (ly_F lyc + 3182592) / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
        lia. }
  { rewrite Htp. intros DT TS C T DB kk Hc.
    apply (TLSAP CTS LAWS lyc Sc Wc mr mdc [0%nat; 1%nat; 2%nat] (S - 9136) S HAR ltac:(repeat constructor)
             ltac:(lia) ltac:(lia)).
    exact (cm_tls_map _ _ (fun a bs => proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs mr _ a bs REL)) _ _ _ _ _ _ _ Hc). }
Qed.

(* ==== The walk, part 5: the exit run (stretch level) ============================================================
   From the exit cut 0x84724: S6 (cm_exit_rel_F, F6) to the release store 0x847bc and the store itself
   (cm_release_store_F, F7), ending just after the store (0x847c0), where the flag byte reads 0; S7
   (cm_exit_rel_after_store_F, F7) is lifted on its own from there. *)
Definition cmPS (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S FS fr sp2 jj r : Z)
    (mc : word -> option byte) (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word)
    : machine_state -> Prop :=
  fun s => exists mcur : word -> option byte,
    s = lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S)
          (Z_to_bv 64 (reac_box_catalogue_match.CA S)) (lib.Lib.Mem.wa (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj))
          y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (A.AsanRT.shadow_addr fr))
          (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None
        (write_to_mem mcur (lib.Lib.Mem.wa (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj))
           (lib.Lib.Mem.le1 (Z_to_bv 64 0))) (lib.Lib.PropExec.seg_rom A.Img0.rsegs) /\
    lib.Lib.Frame.munch [(fr, fr + 8); (A.AsanRT.shadow_addr fr, A.AsanRT.shadow_addr fr + 32);
           (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj, A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj + 1)] mc mcur /\
    lib.Lib.Frame.wmono A.Img0.rsegs mc mcur /\ lib.Lib.Mem.mem_inv A.Img0.rsegs mcur /\
    (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P mcur) /\
    lib.Lib.Frame.stk A.Img0.rsegs mcur (S - 9136) S /\
    lib.Lib.Frame.stk A.Img0.rsegs mcur FS (FS + A.Prog.asan_stack_malloc_c.FS_SIZE) /\
    store_ok A.Img0.rsegs mcur (lib.Lib.Mem.wa (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj)) 1 = true.

Lemma cm_exitA_F : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len S FS : Z) (fb : list byte),
  cmBB m tp S f len FS fb -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  forall (RNG : lib.Lib.ExecF.footprint) (fr sp2 jj : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  lib.Lib.ExecF.rng RNG fr 8 -> lib.Lib.ExecF.rng RNG (fr + 248) 8 ->
  lib.Lib.ExecF.rng RNG (A.AsanRT.shadow_addr fr) 32 ->
  lib.Lib.ExecF.rng RNG (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj) 1 ->
  r = RcMatch.want reac_box_catalogue_match_c.CM_T len fb ->
  reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj 1 mc ->
  lib.Lib.ExecF.evtF A.Img0.rsegs RNG
    (cmPS gp tp s11 F fc m S FS fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S)
       (Z_to_bv 64 (reac_box_catalogue_match.CA S)) y0 y1 y2 y3 y4 y5 y6 y7
       (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (A.AsanRT.shadow_addr fr))
       (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
       F (Z_to_bv 64 0x84724) fc None mc (lib.Lib.PropExec.seg_rom A.Img0.rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb BB Rf Rlen Hfb
    RNG fr sp2 jj mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 R1 R2 R3 R4 Hr INV.
  destruct BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP & HMEMCMP &
    HGOT & HCF254 & HCF255 & FP0 & TLS0).
  eapply lib.Lib.ExecF.evtF_cut.
  { exact (reac_box_catalogue_match_F6.cm_exit_rel_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS
             fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 RNG fr sp2 jj 1 mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7
             z4 z5 z8 z9 z10 u3 u4 u5 u6 R1 R2 R3 eq_refl Hr INV). }
  intros ms' (mcur & -> & MU & WM & MI' & SR' & ST1 & ST2 & SOK).
  apply (reac_box_catalogue_match_F7.cm_release_store_F gp tp s11 F fc f len S FS fb Rf Rlen Hfb RNG fr sp2 jj r mc
           mcur x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 _ R4 SOK).
  apply lib.Lib.ExecF.evtF_done. exists mcur. split; [reflexivity|].
  exact (conj MU (conj WM (conj MI' (conj SR' (conj ST1 (conj ST2 SOK)))))).
Qed.

(* ==== The walk, part 6: helpers of the world-level stages ======================================================= *)
Lemma cm_view_of_garr8 : forall (H : word -> bool) (m : word -> option byte) base (zs : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H m) base zs -> (j < length zs)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j zs 0).
Proof.
  intros H m base zs j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
  change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
  unfold lib.Reusable.YG0n.aview. rewrite Hv. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8.
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. unfold bv_wrap.
  change (bv_modulus 8) with 256. repeat rewrite (Z.mod_small _ _ Hr). reflexivity.
Qed.

(* The record's bytes at a journal state: the journal keeps a block that lives at both ends (FP = []). *)
Lemma cm_rec_view : forall ly S0 W mem md own lyc Sc Wc mr mdc k S f fb Lf,
  ajournal tfibsegs B CM_STK S [] ly S0 W mem md own lyc Sc Wc mr mdc k ->
  In (f, Lf) (ablocks B ly S0) -> In (f, Lf) (ablocks B lyc Sc) -> 50 <= req_size Lf -> length fb = 50%nat ->
  garr8 tfibsegs (mrestrict (w_H W) mem) f (map (fun b : byte => bv_unsigned b) fb) ->
  forall i, (i < 50)%nat ->
    aview tfibsegs (w_H Wc) mr (f + Z.of_nat i) = Some (bv_unsigned (nth i fb (Z_to_bv 8 0))).
Proof.
  intros ly S0 W mem md own lyc Sc Wc mr mdc k S f fb Lf J H1 H2 Hreq Hfb Hg i Hi.
  pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 f Lf (Z.of_nat i) H1 H2 ltac:(lia) ltac:(intros (r & Hr & _); destruct Hr)).
  rewrite (cm_view_of_garr8 _ _ _ _ i Hg ltac:(rewrite map_length; lia)).
  f_equal. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite map_length; lia).
  apply map_nth.
Qed.

(* cmInv at a base, with the base itself as the current memory (cm_mk_inv, source :793, at Wm = []). *)
Lemma cm_inv_base : forall (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m : word -> option byte)
    (f len S FS : Z) (fb : list byte) (jj : Z),
  cmBB m tp S f len FS fb -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  0 <= jj < A.Prog.asan_stack_malloc_c.fs_M 2 ->
  lib.Lib.Step.rw_cells A.Img0.rsegs m (S - 96) (reac_box_catalogue_match.cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (A.Prog.asan_stack_malloc_c.fs_frame FS 2 jj + 248)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (A.Prog.asan_stack_malloc_c.fs_flag FS 2 jj))) ->
  reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS
    (A.Prog.asan_stack_malloc_c.fs_frame FS 2 jj) (reac_box_catalogue_match.CA S) jj 1 m.
Proof.
  intros ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb jj BB Rf Rlen Hfb Hjj HSAV HFW.
  destruct BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP & HMEMCMP &
    HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & HCL & _).
  apply (reac_box_catalogue_match_on.cm_mk_inv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST
           Hfb AC SR HHM HAE AW FP0 TLS0 _ _ _ _ m []).
  - unfold reac_box_catalogue_match.cmFK. right. split; [exact Hjj|]. split; [reflexivity|]. split; reflexivity.
  - intros x _. reflexivity.
  - apply lib.Lib.Frame.wmono_refl.
  - apply A.Prog.MemMono.rd_mono_refl.
  - exact MI.
  - intros x _. exact I.
  - intros y _ _. exact I.
  - intros c Hc. destruct (proj1 (Forall_forall _ _) HCL c Hc) as (_ & h & flags & B1 & B2 & B3 & B4).
    split; [exists h; exact B1 | exists flags; split; [exact B2 | split; [exact B3 | exact B4]]].
  - exact HSAV.
  - intros _. exact HFW.
Qed.

(* A footprint run from a stretch-level state that ms_rel relates to the real one (MemNormF.evtF_rel_ro). *)
Lemma cm_lift_rel : forall (W : world tfibsegs) (ms s0 : machine_state) (model : Model) (R : list (Z * Z))
    (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  A.MemNorm.ms_rel A.Img0.rsegs ms s0 ->
  lib.Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (cm_Hk (w_H W) R)) P s0 ->
  (forall (ms' s1 : machine_state) (model' : Model), P s1 -> A.MemNorm.ms_rel A.Img0.rsegs ms' s1 ->
     A.MemNorm.ro_same A.Img0.rsegs (ms_mem ms) (ms_mem ms') ->
     lib.Reusable.YK04R.fsteps tfibsegs (A.ProgBridge.RNG_W (cm_Hk (w_H W) R)) ms ms' ->
     (forall x, cm_Hk (w_H W) R x = true -> ms_mem ms' x = ms_mem ms x) ->
     same_but_materialized model model' -> SRr tfibsegs W (mkCfg ms' model') Q) ->
  SRr tfibsegs W (mkCfg ms model) Q.
Proof.
  intros W ms s0 model R P Q Hrel Hrun K.
  pose proof (A.MemNormF.evtF_rel_ro _ P ms s0 Hrel Hrun) as Hreal.
  apply (cm_SRr_frun W ms model (A.ProgBridge.RNG_W (cm_Hk (w_H W) R))
           (fun s => exists s1, P s1 /\ A.MemNorm.ms_rel A.Img0.rsegs s s1 /\
                       A.MemNorm.ro_same A.Img0.rsegs (ms_mem ms) (ms_mem s))).
  - exact (A.ProgBridge.fevt_of_evtF _ _ _ Hreal).
  - exact (cm_fp_avoids_Hk (w_H W) R).
  - intros ms' model' (s1 & HP & Hrel' & Hsame) Hfs Hsbm.
    exact (K ms' s1 model' HP Hrel' Hsame Hfs (cm_keep_Hk W R ms ms' Hfs) Hsbm).
Qed.

Lemma cm_munch_join : forall (A : list lib.Lib.Frame.ivl) (b x y : word -> option byte),
  lib.Lib.Frame.munch A b x -> lib.Lib.Frame.munch A b y -> lib.Lib.Frame.munch A x y.
Proof. intros A b x y Hx Hy z Hz. rewrite (Hy z Hz), (Hx z Hz). reflexivity. Qed.

Lemma cm_not_outside : forall (L : list lib.Lib.Frame.ivl) a,
  ~ lib.Lib.Frame.outside L a -> exists r, In r L /\ fst r <= a < snd r.
Proof.
  induction L as [|[lo hi] L IH]; cbn [lib.Lib.Frame.outside]; intros a H; [exfalso; exact (H I)|].
  assert (D : lo <= a < hi \/ ~ (lo <= a < hi)) by lia.
  destruct D as [D|D]; [exists (lo, hi); split; [left; reflexivity | exact D]|].
  destruct (IH a) as (r & Hr & Hra); [intros Ho; exact (H (conj D Ho))|].
  exists r. split; [right; exact Hr | exact Hra].
Qed.

Lemma cm_in_not_outside : forall (L : list lib.Lib.Frame.ivl) lo hi a,
  In (lo, hi) L -> lo <= a < hi -> ~ lib.Lib.Frame.outside L a.
Proof.
  induction L as [|[l h] L IH]; cbn [lib.Lib.Frame.outside In]; intros lo hi a Hin Ha; [destruct Hin|].
  intros (Hn & Ho). destruct Hin as [E|Hin]; [injection E as -> ->; exact (Hn Ha) | exact (IH lo hi a Hin Ha Ho)].
Qed.

(* The bytes of aWc lie above every segment, so cm_Hk never hides them for being a segment byte. *)
Lemma cm_aWc_noseg : forall S FS, A.AsanRT.HIGHMEM_BEG <= S - 9136 -> A.Prog.asan_stack_malloc_c.ASAN_GT <= FS ->
  forall x : word, ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc S FS) (bv_unsigned x) -> cm_inseg x = false.
Proof.
  intros S FS HS HF x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  destruct (cm_not_outside _ _ Hx) as (r & Hr & Hra).
  assert (Hlo : A.Prog.ImgBounds.IMG_HI <= bv_unsigned x).
  { unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs in Hr. destruct Hr as [<-|Hr].
    - cbn [fst snd] in Hra. unfold A.AsanRT.HIGHMEM_BEG, A.Prog.ImgBounds.IMG_HI in *. lia.
    - apply in_app_or in Hr as [Hr|[<-|[]]].
      + unfold A.Prog.asan_stack_malloc_c.ASAN_GT in HF.
        destruct (cm_fpw_in FS r Hr ltac:(lia)) as [(D1 & D2) | (D1 & D2)];
          unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.Prog.ImgBounds.IMG_HI in *.
        * lia.
        * assert (0 <= FS / 8) by (apply Z.div_pos; lia). lia.
      + cbn [fst snd] in Hra. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.Prog.ImgBounds.IMG_HI in *.
        assert (0 <= (S - 9136) / 8) by (apply Z.div_pos; unfold A.AsanRT.HIGHMEM_BEG in HS; lia). lia. }
  unfold cm_inseg. destruct (find_segment tfibsegs (bv_unsigned x) 1) eqn:E; [|reflexivity].
  exfalso. pose proof (cm_seg_none (bv_unsigned x) (conj Hlo (proj2 Rx))) as E0.
  change (find_segment A.Img0.rsegs (bv_unsigned x) 1) with (find_segment tfibsegs (bv_unsigned x) 1) in E0.
  rewrite E in E0. discriminate E0.
Qed.

(* The callee-saved registers of the final state are the entry's. *)
Lemma cm_preserved : forall (regs : bvmap 5 word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  aregs_preserved regs
    (lib.Lib.Frame.mkR (cm_rg regs 1) (Z_to_bv 64 (spZ regs)) (cm_rg regs 3) (cm_rg regs 4) t0 t1 t2 (cm_rg regs 8)
       (cm_rg regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21)
       (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) t3 t4 t5 t6).
Proof.
  intros regs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - transitivity (Z_to_bv 64 (spZ regs)); [reflexivity|]. unfold spZ.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Lemma cm_wtm_here : forall (m : word -> option byte) (a : Z) (b : byte), 0 <= a < 2 ^ 64 ->
  write_to_mem m (lib.Lib.Mem.wa a) [b] (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros m a b Ha.
  rewrite (lib.Lib.Mem.write_to_mem_spec [b] m a (lib.Lib.Mem.wa a) ltac:(lia) ltac:(cbn [length]; lia)).
  rewrite (lib.Lib.Mem.wa_unsigned a Ha). cbn [length].
  rewrite (proj2 (Z.leb_le a a) (Z.le_refl a)), (proj2 (Z.ltb_lt a (a + Z.of_nat 1)) ltac:(lia)). cbn [andb].
  replace (a - a) with 0 by lia. reflexivity.
Qed.

Lemma cm_inR_not_outside : forall R a, cm_inR R a = true -> ~ lib.Lib.Frame.outside R a.
Proof.
  intros R a H. unfold cm_inR in H. apply existsb_exists in H as ([lo hi] & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in H1, H2.
  exact (cm_in_not_outside R lo hi a Hin (conj H1 H2)).
Qed.

Lemma cm_vis_of_present : forall (H : word -> bool) (m : word -> option byte) lo n,
  0 <= lo -> lo + n <= 2 ^ 64 -> (forall a, lo <= a < lo + n -> apresent H m a) -> A.ProgBridge.range_visible H lo n.
Proof.
  intros H m lo n H0 H1 Hp. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (Hp a Ha) as (Hh & _).
  exact Hh.
Qed.

Lemma cm_fs2 : forall F pos, A.Prog.asan_stack_malloc_c.fs_frame F 2 pos = F + 2134016 + 256 * pos /\
  A.Prog.asan_stack_malloc_c.fs_flag F 2 pos = F + 28672 + pos /\ A.Prog.asan_stack_malloc_c.fs_M 2 = 4096.
Proof.
  intros F pos. unfold A.Prog.asan_stack_malloc_c.fs_frame, A.Prog.asan_stack_malloc_c.fs_flag,
    A.Prog.asan_stack_malloc_c.fs_M, A.Prog.asan_stack_malloc_c.fs_B. cbn. lia.
Qed.

(* ==== The walk, part 7: the world-level stages ===================================================================
   The spec's binders and premises are this section's variables and hypotheses; pb_reac_box_catalogue_match
   instantiates them. Lf is the record block's request size (any value when len < 50). *)
Section walk.
Variables (ly : alayout) (S0 : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (f len : Z) (fb : list byte) (Lf : Z).
Hypothesis HPRE : afn_pre tfibsegs B CM_STK ly S0 W regs mem md ch.
Hypothesis HRO0 : arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem).
Hypothesis H10 : lib.Reusable.YK11.getr regs 10 = w64 f.
Hypothesis H11 : lib.Reusable.YK11.getr regs 11 = w64 len.
Hypothesis Rf : 0 <= f < 2 ^ 64.
Hypothesis Rlen : 0 <= len < 2 ^ 64.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HBLK : 50 <= len -> In (f, Lf) (ablocks B ly S0) /\ 50 <= req_size Lf.
Hypothesis HG : 50 <= len -> garr8 tfibsegs (mrestrict (w_H W) mem) f (map (fun b : byte => bv_unsigned b) fb).
Hypothesis HTG : garr8 tfibsegs (mrestrict (w_H W) mem) A_CM_TBL CM_TBLZ.
Hypothesis HGL : In (A_CM_TBL, CM_ROWS) GLOBS.
Hypothesis HIMG1 : IMG_LO + 64 <= A_CM_TBL.
Hypothesis HIMG2 : A_CM_TBL + CM_ROWS + 64 <= IMG_HI.
Hypothesis HTBL : forall a, A_CM_TBL <= a < A_CM_TBL + CM_ROWS ->
  in_roP tfibsegs RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HC2 : count_cid 2 (frames S0) < fs_frames 2.
Hypothesis HC1 : count_cid 1 (frames S0) < fs_frames 1.
Hypothesis HC0 : count_cid 0 (frames S0) < fs_frames 0.

Local Notation SP := (spZ regs).
Local Notation FS := (ly_F ly).
Local Notation FRp pos := (A.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 2 pos).
Local Notation FLp pos := (A.Prog.asan_stack_malloc_c.fs_flag (ly_F ly) 2 pos).

Lemma cm_htp : bv_unsigned (cm_rg regs 4) = A.AsanRT.RT_TP.
Proof.
  pose proof HPRE as (_ & _ & _ & _ & Htp & _).
  change (cm_rg regs 4) with (lib.Reusable.YK11.getr regs 4). rewrite Htp. unfold w64. rewrite TP_RT.
  apply cm_u64. unfold A.AsanRT.RT_TP. lia.
Qed.

(* The state of the walk at a cut after the class-2 frame is taken: the journal (own = [(2, pos)]), the blocks
   unchanged, the frame index, the entry saves at [SP - 96, SP), the frame's flag word. *)
Definition cmCut (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world tfibsegs) (mr : word -> option byte)
    (mdc : Model) : Prop :=
  ajournal tfibsegs B CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 /\
  ablocks B lyc Sc = ablocks B ly S0 /\ 0 <= pos < A.Prog.asan_stack_malloc_c.fs_M 2 /\
  lib.Lib.Step.rw_cells A.Img0.rsegs mr (SP - 96) (cm_saves regs) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs mr (FRp pos + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (FLp pos))).

Lemma cm_cut_base : forall pos lyc Sc Wc mr mdc, cmCut pos lyc Sc Wc mr mdc ->
  ly_F lyc = FS /\ In (2, pos) (frames Sc) /\ A.MemNorm.ro_agree A.Img0.rsegs mr /\
  AR tfibsegs B lyc Sc Wc mr mdc /\
  cmBB (A.MemNorm.normalize A.Img0.rsegs mr) (cm_rg regs 4) SP f len FS fb /\
  reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
    (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25)
    (cm_rg regs 26) (A.MemNorm.normalize A.Img0.rsegs mr) f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP)
    pos 1 (A.MemNorm.normalize A.Img0.rsegs mr).
Proof.
  intros pos lyc Sc Wc mr mdc (J & Eab & Hpos & HSAV & HFW).
  pose proof J as (HAR & Hly & _ & _ & _ & Hfrs & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (2, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  assert (HRm : A.MemNorm.ro_agree A.Img0.rsegs mr).
  { pose proof (arodata_ok_journalP tfibsegs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J (cm_arodataP _ HRO0))
      as HROc.
    destruct (CTLRT CTS LAWS RLO RHI lyc Sc Wc mr mdc HAR HROc) as (_ & _ & _ & ROm). exact ROm. }
  assert (HREC : 50 <= len -> In (f, Lf) (ablocks B lyc Sc) /\ 50 <= req_size Lf /\
     forall i, (i < 50)%nat ->
       aview tfibsegs (w_H Wc) mr (f + Z.of_nat i) = Some (bv_unsigned (nth i fb (Z_to_bv 8 0)))).
  { intros H50. destruct (HBLK H50) as (Hb & Hreq).
    assert (Hb' : In (f, Lf) (ablocks B lyc Sc)) by (rewrite Eab; exact Hb).
    split; [exact Hb'|]. split; [exact Hreq|].
    exact (cm_rec_view ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 SP f fb Lf J Hb Hb' Hreq Hfb (HG H50)). }
  pose proof (cm_base ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 SP f len fb Lf (cm_rg regs 4) J HRO0 cm_htp Rf Rlen
                Hfb HREC HTBL HGL) as BB.
  rewrite EF in BB.
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mr HRm) as REL.
  split; [exact EF|]. split; [exact Hin|]. split; [exact HRm|]. split; [exact HAR|]. split; [exact BB|].
  pose proof BB as (_ & _ & _ & HHM & HAE & _).
  apply (cm_inv_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ f len SP FS fb pos BB Rf Rlen Hfb Hpos).
  - apply A.MemNormTr.rw_cells_normalize; [exact HRm | | exact HSAV].
    intros i Hi. unfold cm_saves, reac_box_catalogue_match_F1.cmSAVES in Hi. cbn in Hi.
    apply A.MemNormTr.ro_addr_above_img.
    unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia.
  - exact (proj1 (A.MemNorm.bytes_at_rel A.Img0.rsegs mr _ _ _ REL) HFW).
Qed.

(* The exit stage: from the exit cut 0x84724 with the cut invariant to the spec's post. Lift 1 runs S6 and the
   release store at the footprint {window, frame, frame shadow, flag byte}; ProgWorld's release law gives the journal
   with own = [] and the frame freed (stack_free_state). Lift 2 runs S7 (the epilogue) at the window; the journal
   of it and the restored registers give apost_base. *)
Lemma cm_stage_exit : forall pos lyc Sc Wc mr mdc
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  cmCut pos lyc Sc Wc mr mdc ->
  SRr tfibsegs Wc (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      (cm_rg regs 3) (cm_rg regs 4) u0 u1 u2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      y0 y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 (FRp pos))
      (Z_to_bv 64 (RcMatch.want reac_box_catalogue_match_c.CM_T len fb))
      z4 z5 (Z_to_bv 64 (A.AsanRT.shadow_addr (FRp pos))) (Z_to_bv 64 (FRp pos)) z8 z9 z10 (cm_rg regs 27) u3 u4 u5 u6)
      fp_regs (Z_to_bv 64 0x84724) fp_csr None mr (seg_rom tfibsegs)) mdc)
    (treac_box_catalogue_match_post regs ly S0 W mem md len fb).
Proof.
  intros pos lyc Sc Wc mr mdc x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 HC.
  pose proof HC as (J & Eab & Hpos & HSAV & HFW).
  destruct (cm_cut_base pos lyc Sc Wc mr mdc HC) as (EF & Hin & HRm & HAR & BB & INV).
  pose proof BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP &
    HMEMCMP & HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold A.AsanRT.APPMEM_END in HAE'. unfold A.AsanRT.HIGHMEM_BEG in HHM'.
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSlo & _).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (G1 & G2 & G3 & G4 & _ & _ & G7).
  change (Z.to_nat 2) with 2%nat in G1, G2, G3, G4.
  destruct (cm_fs2 FS pos) as (E1 & E2 & E3).
  destruct (cm_fs2 FS 0) as (E10 & E20 & _).
  pose proof (proj1 (cm_fs2 FS 4096)) as E1M.
  assert (EB2 : lib.Reusable.YG00.fs_frame_bytes 2 = 256) by (rewrite <- G2; reflexivity).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  assert (EFA : frame_addr lyc 2 pos = FRp pos) by (unfold frame_addr; rewrite EF, G3; reflexivity).
  assert (EFL : flag_addr lyc 2 pos = FLp pos) by (unfold flag_addr; rewrite EF, G4; reflexivity).
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mr HRm) as REL0.
  unfold A.Prog.asan_stack_malloc_c.FS_SIZE, A.Prog.asan_stack_malloc_c.ASAN_GT in *.
  (* visibility of the frame, its shadow and the flag byte *)
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc Wc mr mdc 2 pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite EFA, EB2 in HFb. rewrite EFA, EB28 in HFsh.
  assert (VF : A.ProgBridge.range_visible (w_H Wc) (FRp pos) 256).
  { apply (cm_vis_of_present _ mr); [lia | lia | intros a Ha; exact (proj1 (HFb a Ha))]. }
  assert (VS : A.ProgBridge.range_visible (w_H Wc) (A.AsanRT.shadow_addr (FRp pos)) 32).
  { apply (cm_vis_of_present _ mr).
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. assert (0 <= FRp pos / 8) by (apply Z.div_pos; lia). lia.
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. assert (FRp pos / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia).
      lia.
    - intros a Ha. rewrite G7 in Ha.
      replace a with (lib.Reusable.YG0f.shadow_addr (FRp pos) + (a - lib.Reusable.YG0f.shadow_addr (FRp pos))) by lia.
      exact (proj1 (HFsh (a - lib.Reusable.YG0f.shadow_addr (FRp pos)) ltac:(lia))). }
  assert (VL : A.ProgBridge.range_visible (w_H Wc) (FLp pos) 1).
  { split; [lia|]. split; [lia|]. intros a Ha. replace a with (FLp pos) by lia.
    apply (A.ProgWorldVisFrame.vis_of_aview tfibsegs Wc mr). rewrite <- EFL.
    pose proof (am_flags _ _ _ _ (proj1 HAR)) as HFL.
    rewrite (HFL 2 pos ltac:(lia) ltac:(rewrite <- G1; lia)). discriminate. }
  assert (VW : forall lo n, SP - 9136 <= lo -> lo + n <= SP -> A.ProgBridge.range_visible (w_H Wc) lo n).
  { intros lo n Hlo Hhi.
    exact (cm_win_vis SP ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 lo n J ltac:(lia) ltac:(unfold CM_STK; lia) Hhi
             ltac:(lia)). }
  (* the sub-ranges of aWc the run writes, and aWc above every segment *)
  assert (HnoA := cm_aWc_noseg SP FS HHM P3).
  assert (HinA : forall lo hi z, In (lo, hi) (reac_box_catalogue_match.aWc SP FS) -> lo <= z < hi ->
                   ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) z) by exact (cm_in_not_outside _).
  assert (Hfrm : In (A.Prog.asan_stack_malloc_c.fs_frame FS 2 0,
                     A.Prog.asan_stack_malloc_c.fs_frame FS 2 (A.Prog.asan_stack_malloc_c.fs_M 2))
                    (reac_box_catalogue_match.aWc SP FS)).
  { unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs, A.Prog.RcAsanFP.fp_w,
      A.Prog.RcAsanFP.fp_w1. cbn [flat_map app]. do 11 right. left. reflexivity. }
  assert (Hshm : In (A.AsanRT.shadow_addr (A.Prog.asan_stack_malloc_c.fs_frame FS 2 0),
                     A.AsanRT.shadow_addr (A.Prog.asan_stack_malloc_c.fs_frame FS 2 (A.Prog.asan_stack_malloc_c.fs_M 2)))
                    (reac_box_catalogue_match.aWc SP FS)).
  { unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs, A.Prog.RcAsanFP.fp_w,
      A.Prog.RcAsanFP.fp_w1. cbn [flat_map app]. do 12 right. left. reflexivity. }
  assert (Hflm : In (A.Prog.asan_stack_malloc_c.fs_flag FS 2 0,
                     A.Prog.asan_stack_malloc_c.fs_flag FS 2 0 + A.Prog.asan_stack_malloc_c.fs_M 2)
                    (reac_box_catalogue_match.aWc SP FS)).
  { unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs, A.Prog.RcAsanFP.fp_w,
      A.Prog.RcAsanFP.fp_w1. cbn [flat_map app]. do 10 right. left. reflexivity. }
  assert (HSH8 : (FRp pos + 256) / 8 = FRp pos / 8 + 32).
  { replace (FRp pos + 256) with (FRp pos + 32 * 8) by lia. apply Z.div_add. lia. }
  assert (HSHlo : A.AsanRT.shadow_addr (A.Prog.asan_stack_malloc_c.fs_frame FS 2 0) <= A.AsanRT.shadow_addr (FRp pos)).
  { unfold A.AsanRT.shadow_addr. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  assert (HSHhi : A.AsanRT.shadow_addr (FRp pos) + 32 <=
                  A.AsanRT.shadow_addr (A.Prog.asan_stack_malloc_c.fs_frame FS 2 (A.Prog.asan_stack_malloc_c.fs_M 2))).
  { unfold A.AsanRT.shadow_addr. rewrite E3, E1M.
    assert ((FRp pos + 256) / 8 <= (FS + 2134016 + 256 * 4096) / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (HsubA : forall z, lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) z ->
                    lib.Lib.Frame.outside [(FRp pos, FRp pos + 8); (A.AsanRT.shadow_addr (FRp pos),
                       A.AsanRT.shadow_addr (FRp pos) + 32); (FLp pos, FLp pos + 1)] z).
  { intros z Hz. cbn [lib.Lib.Frame.outside]. split; [|split; [|split; [|exact I]]]; intros Hzr.
    - exact (HinA _ _ z Hfrm ltac:(rewrite E3; lia) Hz).
    - exact (HinA _ _ z Hshm ltac:(lia) Hz).
    - exact (HinA _ _ z Hflm ltac:(rewrite E3; lia) Hz). }
  (* lift 1: S6 and the release store *)
  pose (RX := [(SP - 9136, SP); (FRp pos, FRp pos + 256);
               (A.AsanRT.shadow_addr (FRp pos), A.AsanRT.shadow_addr (FRp pos) + 32); (FLp pos, FLp pos + 1)]).
  assert (RX1 : forall lo n, FRp pos <= lo -> 0 <= n -> lo + n <= FRp pos + 256 ->
                  lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk (w_H Wc) RX)) lo n).
  { intros lo n Hlo Hn Hhi. apply cm_rng_Hk.
    - intros a Ha. apply (cm_inR_In RX (FRp pos) (FRp pos + 256)); [unfold RX; right; left; reflexivity | lia].
    - apply (A.ProgBridge.range_visible_sub _ (FRp pos) 256); [exact VF | lia | lia | lia]. }
  assert (RX3 : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk (w_H Wc) RX)) (A.AsanRT.shadow_addr (FRp pos)) 32).
  { apply cm_rng_Hk; [|exact VS]. intros a Ha.
    apply (cm_inR_In RX (A.AsanRT.shadow_addr (FRp pos)) (A.AsanRT.shadow_addr (FRp pos) + 32));
      [unfold RX; right; right; left; reflexivity | lia]. }
  assert (RX4 : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk (w_H Wc) RX)) (FLp pos) 1).
  { apply cm_rng_Hk; [|exact VL]. intros a Ha.
    apply (cm_inR_In RX (FLp pos) (FLp pos + 1)); [unfold RX; right; right; right; left; reflexivity | lia]. }
  eapply (cm_lift_base Wc _ fp_regs (Z_to_bv 64 0x84724) fp_csr mr mdc RX _ _ HRm).
  { exact (cm_exitA_F (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
             (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
             (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr (A.MemNorm.normalize A.Img0.rsegs mr)
             f len SP FS fb BB Rf Rlen Hfb _ (FRp pos) (reac_box_catalogue_match.CA SP) pos
             (A.MemNorm.normalize A.Img0.rsegs mr) _ x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
             (RX1 (FRp pos) 8 ltac:(lia) ltac:(lia) ltac:(lia))
             (RX1 (FRp pos + 248) 8 ltac:(lia) ltac:(lia) ltac:(lia)) RX3 RX4
             eq_refl INV). }
  intros ms1 s1 md1 HP1 Hrel1 Hsame1 Hfs1 Hkeep1 Hsbm1.
  destruct HP1 as (mcur & Es1 & MU & WM & MI' & SR' & ST1 & ST2 & SOK). subst s1.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel1) as (Ems1 & REL1).
  assert (Hle1 : lib.Lib.Mem.le1 (Z_to_bv 64 0) = [Z_to_bv 8 0]) by exact (lib.Lib.StepF.le1_lit_byte 0).
  assert (MUs : lib.Lib.Frame.munch (reac_box_catalogue_match.aWc SP FS) (A.MemNorm.normalize A.Img0.rsegs mr)
                  (write_to_mem mcur (lib.Lib.Mem.wa (FLp pos)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))).
  { intros z Hz. rewrite Hle1. rewrite lib.Lib.Mem.write_to_mem_spec by (cbn [length]; lia).
    pose proof (HsubA _ Hz) as Hz'. cbn [lib.Lib.Frame.outside] in Hz'. destruct Hz' as (_ & _ & Hzf & _).
    cbn [length]. destruct ((FLp pos <=? bv_unsigned z) && (bv_unsigned z <? FLp pos + Z.of_nat 1))%bool eqn:Ez.
    - exfalso. apply andb_prop in Ez as [Ez1 Ez2]. apply Z.leb_le in Ez1. apply Z.ltb_lt in Ez2. apply Hzf. lia.
    - apply MU. exact (HsubA _ Hz). }
  pose proof (A.MemNorm.munch_rel A.Img0.rsegs _ mr _ (ms_mem ms1) _ REL0 REL1 Hsame1 MUs) as MUa.
  assert (MU1 := cm_munch_of_keep Wc _ _ _ mr (ms_mem ms1) Hkeep1 MUa
                   (fun a Hr _ => cm_inR_not_outside _ a Hr) HnoA).
  assert (HFLrng : A.Prog.ImgBounds.IMG_HI <= FLp pos < 2 ^ 64).
  { unfold A.Prog.ImgBounds.IMG_HI. lia. }
  assert (HFLAG : lib.Reusable.YP09.mbyte tfibsegs (ms_mem ms1) (flag_addr lyc 2 pos) = Some (Z_to_bv 8 0)).
  { rewrite EFL. unfold lib.Reusable.YP09.mbyte.
    pose proof (proj1 REL1 (lib.Lib.Mem.wa (FLp pos))) as E. unfold A.MemNorm.normalize in E.
    rewrite (A.MemNormTr.ro_addr_above_img (FLp pos) HFLrng) in E.
    rewrite Hle1 in E. rewrite (cm_wtm_here mcur (FLp pos) (Z_to_bv 8 0) ltac:(lia)) in E.
    unfold lib.Lib.Mem.wa in E. rewrite <- E. reflexivity. }
  assert (HWR1 : forall a, 0 <= a < 2 ^ 64 ->
     ~ lib.Lib.Frame.outside [(SP - 9136, SP); (FRp pos, FRp pos + 256);
         (A.AsanRT.shadow_addr (FRp pos), A.AsanRT.shadow_addr (FRp pos) + 32); (FLp pos, FLp pos + 1)] a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B lyc Sc) lyc [(2, pos)] a \/ a = flag_addr lyc 2 pos).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & Hr & Hra).
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hra.
    - left. left. unfold CM_STK. lia.
    - left. right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB2. lia.
    - left. right. right. right. exists 2, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB28, <- G7. lia.
    - right. rewrite EFL. lia. }
  match type of Hfs1 with lib.Reusable.YK04R.fsteps _ _ ?st0 _ =>
    pose proof (RELF LAWS ASF ctrl_wx ltac:(lia) CM_STK SP [] ly S0 W mem md [] lyc Sc Wc st0 ms1 mdc md1 0 pos _ _ J
                  Hfs1 (cm_fp_avoids_Hk (w_H Wc) _) MU1 Hsbm1 HWR1 HFLAG) as J1
  end.
  (* lift 2: the epilogue S7 *)
  assert (RW7 : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk (w_H Wc) [(SP - 9136, SP)])) (SP - 96) 96).
  { apply cm_rng_Hk; [|exact (VW (SP - 96) 96 ltac:(lia) ltac:(lia))]. intros a Ha.
    apply (cm_inR_In _ (SP - 9136) SP); [left; reflexivity | lia]. }
  eapply (cm_lift_rel Wc ms1 _ md1 [(SP - 9136, SP)] _ _ Hrel1).
  { exact (reac_box_catalogue_match_F7.cm_exit_rel_after_store_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4)
             (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
             (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
             (A.MemNorm.normalize A.Img0.rsegs mr) f len SP FS fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 _
             (FRp pos) (reac_box_catalogue_match.CA SP) pos _ (A.MemNorm.normalize A.Img0.rsegs mr) mcur x1
             (lib.Lib.Mem.wa (FLp pos)) u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 eq_refl INV MU WM MI'
             SR' ST1 ST2 SOK RW7). }
  intros ms2 s2 md2 HP2 Hrel2 Hsame2 Hfs2 Hkeep2 Hsbm2.
  destruct HP2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Es2 &
                   MU' & _).
  subst s2. destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel2) as (Ems2 & REL2).
  pose proof (A.MemNorm.munch_rel A.Img0.rsegs (reac_box_catalogue_match.aWc SP FS) (ms_mem ms1) _ (ms_mem ms2) m'
                REL1 REL2 Hsame2 (cm_munch_join _ (A.MemNorm.normalize A.Img0.rsegs mr) _ m' MUs MU')) as MUb.
  assert (MU2 := cm_munch_of_keep Wc [(SP - 9136, SP)] _ [(SP - 9136, SP)] (ms_mem ms1) (ms_mem ms2) Hkeep2 MUb
                   (fun a Hr _ => cm_inR_not_outside _ a Hr) HnoA).
  assert (HWR2 : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside [(SP - 9136, SP)] a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B lyc (stack_free_state 2 pos Sc)) lyc [] a).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & [<-|[]] & Hra). cbn [fst snd] in Hra.
    left. unfold CM_STK. lia. }
  pose proof (AJF LAWS ctrl_wx CM_STK SP [] ly S0 W mem md [] lyc (stack_free_state 2 pos Sc) Wc ms1 ms2 md1 md2 0 _ _
                J1 Hfs2 (cm_fp_avoids_Hk (w_H Wc) _) MU2 Hsbm2 HWR2) as J2.
  apply SRr_ret. unfold C_reac_box_catalogue_match.treac_box_catalogue_match_post, apost_base.
  pose proof HPRE as (_ & Hraok & _).
  exists lyc, (stack_free_state 2 pos Sc),
    (lib.Lib.Frame.mkR (cm_rg regs 1) (Z_to_bv 64 SP) (cm_rg regs 3) (cm_rg regs 4) t0' t1' t2' (cm_rg regs 8)
       (cm_rg regs 9) (Z_to_bv 64 (RcMatch.want reac_box_catalogue_match_c.CM_T len fb)) a1' a2' a3' a4' a5' a6' a7'
       (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
       (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) t3' t4' t5' t6'), (ms_mem ms2), md2.
  split; [rewrite Ems2; rewrite (cm_ret_pc (cm_rg regs 1) Hraok); reflexivity|].
  split; [exact J2|]. split; [apply cm_preserved|]. split.
  - rewrite cm_tbl_eq. reflexivity.
  - change (ablocks B lyc (stack_free_state 2 pos Sc)) with (ablocks B lyc Sc). rewrite Eab. apply Permutation_refl.
Qed.

(* ---- the premises a caller-journal callee takes about the 32 bytes it writes in our frame ---- *)
Lemma cm_frame_facts_J : forall pos lyc Sc Wc mr mdc,
  ajournal tfibsegs B CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 ->
  0 <= pos < A.Prog.asan_stack_malloc_c.fs_M 2 ->
  (forall a, FRp pos <= a < FRp pos + 256 -> apresent (w_H Wc) mr a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 32 -> apresent (w_H Wc) mr (A.AsanRT.shadow_addr (FRp pos) + i) /\
              ~ aowned B lyc Sc (A.AsanRT.shadow_addr (FRp pos) + i)) /\
  frame_addr lyc 2 pos = FRp pos /\ lib.Reusable.YG00.fs_frame_bytes 2 = 256 /\
  FS + 2134016 <= FRp pos /\ FRp pos + 256 <= FS + 11571200 /\ In (2, pos) (frames Sc).
Proof.
  intros pos lyc Sc Wc mr mdc J Hpos.
  pose proof J as (HAR & Hly & _ & _ & _ & Hfrs & _). pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (2, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (G1 & G2 & G3 & G4 & _ & _ & G7).
  change (Z.to_nat 2) with 2%nat in G1, G2, G3.
  destruct (cm_fs2 FS pos) as (E1 & _ & E3).
  assert (EB2 : lib.Reusable.YG00.fs_frame_bytes 2 = 256) by (rewrite <- G2; reflexivity).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  assert (EFA : frame_addr lyc 2 pos = FRp pos) by (unfold frame_addr; rewrite EF, G3; reflexivity).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc Wc mr mdc 2 pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite EFA, EB2 in HFb. rewrite EFA, EB28 in HFsh.
  split; [exact HFb|]. split.
  - intros i Hi. rewrite G7. exact (HFsh i Hi).
  - split; [exact EFA|]. split; [exact EB2|]. split; [lia|]. split; [lia | exact Hin].
Qed.

Lemma cm_frame_facts : forall pos lyc Sc Wc mr mdc, cmCut pos lyc Sc Wc mr mdc ->
  (forall a, FRp pos <= a < FRp pos + 256 -> apresent (w_H Wc) mr a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 32 -> apresent (w_H Wc) mr (A.AsanRT.shadow_addr (FRp pos) + i) /\
              ~ aowned B lyc Sc (A.AsanRT.shadow_addr (FRp pos) + i)) /\
  frame_addr lyc 2 pos = FRp pos /\ lib.Reusable.YG00.fs_frame_bytes 2 = 256 /\
  FS + 2134016 <= FRp pos /\ FRp pos + 256 <= FS + 11571200 /\ In (2, pos) (frames Sc).
Proof. intros pos lyc Sc Wc mr mdc (J & _ & Hpos & _ & _). exact (cm_frame_facts_J pos lyc Sc Wc mr mdc J Hpos). Qed.

(* Byte facts across a call: the views agree at visible bytes in both worlds. *)
Lemma cm_bytes_of_view2 : forall (Wa Wb : world tfibsegs) (m m' : word -> option byte) (A : Z) (bs : list byte),
  (forall i, (i < length bs)%nat ->
     aview tfibsegs (w_H Wb) m' (A + Z.of_nat i) = aview tfibsegs (w_H Wa) m (A + Z.of_nat i) /\
     w_H Wa (Z_to_bv 64 (A + Z.of_nat i)) = false /\ w_H Wb (Z_to_bv 64 (A + Z.of_nat i)) = false) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m A bs -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' A bs.
Proof.
  intros Wa Wb m m' A bs HV (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HV i Hi) as (Hvw & Ha & Hb).
  rewrite (cm_aview_vis_mrd Wb m' (A + Z.of_nat i) Hb), (cm_aview_vis_mrd Wa m (A + Z.of_nat i) Ha) in Hvw.
  rewrite <- (HB i Hi). unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd A.Img0.rsegs m' (Z_to_bv 64 (A + Z.of_nat i))) as [b'|];
    destruct (lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 (A + Z.of_nat i))) as [b|];
    cbn [option_map] in Hvw; try discriminate Hvw; [|reflexivity].
  injection Hvw as Hvw. f_equal. apply bv_eq. exact Hvw.
Qed.

Lemma cm_rw_of_view2 : forall (Wa Wb : world tfibsegs) (m m' : word -> option byte) (A : Z)
    (cs : list lib.Lib.Cells.cell),
  (forall a, A <= a < A + Z.of_nat (lib.Lib.Cells.cells_size cs) ->
     aview tfibsegs (w_H Wb) m' a = aview tfibsegs (w_H Wa) m a /\ w_H Wa (Z_to_bv 64 a) = false /\
     apresent (w_H Wb) m' a) ->
  lib.Lib.Step.rw_cells A.Img0.rsegs m A cs -> lib.Lib.Step.rw_cells A.Img0.rsegs m' A cs.
Proof.
  intros Wa Wb m m' A cs HV ((Hwf & HBT) & HWR).
  pose proof HBT as (H0 & H1 & _).
  split; [split; [exact Hwf|]|].
  - apply (cm_bytes_of_view2 Wa Wb m m' A _); [|exact HBT].
    intros i Hi. rewrite (lib.Lib.Cells.cells_bytes_length cs Hwf) in Hi.
    destruct (HV (A + Z.of_nat i) ltac:(lia)) as (Hvw & Ha & (Hb & _)). split; [exact Hvw|]. split; [exact Ha | exact Hb].
  - pose proof HWR as (W0 & W1 & _). split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (HV (A + i) ltac:(lia)) as (_ & _ & (_ & b & Hb)).
    unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
Qed.

Lemma cm_addressable_of_rel : forall m m0 p n, A.MemNorm.mem_rel A.Img0.rsegs m m0 ->
  A.AsanRT.addressable m0 p n -> A.AsanRT.addressable m p n.
Proof.
  intros m m0 p n REL (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b.
  rewrite (A.MemNorm.mrd_rel A.Img0.rsegs m m0 _ REL). split; [exact Hb | exact Hok].
Qed.

Lemma cm_addressable_view : forall (Wa Wb : world tfibsegs) (ma mb : word -> option byte) p n,
  (forall i, 0 <= i < n ->
     aview tfibsegs (w_H Wb) mb (A.AsanRT.shadow_addr (p + i)) =
       aview tfibsegs (w_H Wa) ma (A.AsanRT.shadow_addr (p + i)) /\
     w_H Wa (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i))) = false /\
     w_H Wb (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i))) = false) ->
  A.AsanRT.addressable ma p n -> A.AsanRT.addressable mb p n.
Proof.
  intros Wa Wb ma mb p n HV (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b.
  destruct (HV i Hi) as (Hv & Ha' & Hb').
  rewrite (cm_aview_vis_mrd Wb mb _ Hb'), (cm_aview_vis_mrd Wa ma _ Ha') in Hv.
  change (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) with (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i))) in Hb |- *.
  rewrite Hb in Hv.
  destruct (lib.Lib.Mem.mrd A.Img0.rsegs mb (Z_to_bv 64 (A.AsanRT.shadow_addr (p + i)))) as [b'|];
    cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as Hv. assert (Eb : b' = b) by (apply bv_eq; exact Hv). subst b'. split; [reflexivity | exact Hok].
Qed.

(* A byte view of a row gives the core's garr8 of its values. *)
Lemma cm_garr8_of_view : forall (H : word -> bool) (m : word -> option byte) base (bs : list byte),
  (forall j, (j < length bs)%nat ->
     aview tfibsegs H m (base + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0)))) ->
  garr8 tfibsegs (mrestrict H m) base (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros H m base bs Hv j Hj. rewrite length_map in Hj.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Rb.
  change (bv_modulus 8) with 256 in Rb.
  split; [|lia].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  specialize (Hv j Hj). unfold lib.Reusable.YG0n.aview in Hv.
  destruct (lib.Reusable.YP09.mbyte tfibsegs (mrestrict H m) (base + Z.of_nat j)) as [b|];
    cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as Hv. f_equal.
  assert (Le : lib.Reusable.YO0f.le_byte (bv_unsigned (nth j bs (Z_to_bv 8 0))) 1 0 =
               bv_unsigned (nth j bs (Z_to_bv 8 0))).
  { unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Rb. }
  rewrite Le, <- Hv. symmetry. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma cm_not_img : forall x, A.Prog.ImgBounds.IMG_HI <= x -> ~ lib.Reusable.YG0d.in_img tfibsegs x.
Proof.
  intros x Hx (sg & Hin & Hr).
  apply (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s)))) in Hin.
  change tfibsegs with A.Img0.rsegs in Hin. rewrite A.ProgBridge.rsegs_spans in Hin.
  unfold A.Prog.ImgBounds.IMG_HI in Hx.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma cm_signed_small : forall b : byte, 0 <= bv_signed b <= 7 -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap in *. change (bv_half_modulus 8) with 128 in *.
  change (bv_modulus 8) with 256 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cm_CA : forall S, reac_box_catalogue_match.CA S mod 32 = 0 /\
  S - 160 <= reac_box_catalogue_match.CA S <= S - 128.
Proof. intros S. unfold reac_box_catalogue_match.CA. Z.div_mod_to_equations. lia. Qed.

Lemma cm_pc_mb : Z_to_bv 64 0x85b44 = lib.Reusable.YG0d.w64 (BASE + AF_reac_box_model_block).
Proof. unfold lib.Reusable.YG0d.w64. f_equal; vm_compute; reflexivity. Qed.

Lemma cm_retok_mb : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x846cc).
Proof. vm_compute. reflexivity. Qed.

(* The row's bytes at a cut: the table is read-only image data, so the view is the image (arodata), and the image
   bytes are CM_TBL's (reac_box_catalogue_match_lib.CM_TBL_eq). *)
Lemma cm_row_view : forall pos lyc Sc Wc mr mdc (i : nat), cmCut pos lyc Sc Wc mr mdc -> (i < 11)%nat ->
  forall j, (j < length (reac_box_catalogue_match_lib.cm_row i))%nat ->
    aview tfibsegs (w_H Wc) mr (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i + Z.of_nat j) =
    Some (bv_unsigned (nth j (reac_box_catalogue_match_lib.cm_row i) (Z_to_bv 8 0))).
Proof.
  intros pos lyc Sc Wc mr mdc i (J & _) Hi j Hj.
  rewrite (reac_box_catalogue_match_lib.cm_row_len i Hi) in Hj.
  pose proof (arodata_ok_journalP tfibsegs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J (cm_arodataP _ HRO0))
    as HROc.
  pose proof cm_tbl_eq as Et. unfold reac_box_catalogue_match_c.CM_T in Et.
  assert (HTa : forall a, reac_box_catalogue_match_c.CM_T <= a < reac_box_catalogue_match_c.CM_T + Z.of_nat 3256 ->
            lib.Lib.Mem.mrd A.Img0.rsegs mr (lib.Lib.Mem.wa a) =
            lib.Lib.PropExec.seg_rom A.Img0.rsegs (lib.Lib.Mem.wa a)).
  { intros a Ha. change (Z.of_nat 3256) with 3256 in Ha. unfold reac_box_catalogue_match_c.CM_T in Ha.
    destruct (HTBL a ltac:(unfold A_CM_TBL in *; rewrite Et; unfold CM_ROWS; lia)) as (Hro & Hno & Hne).
    apply (cm_HT_of_view Wc).
    - destruct (A.ProgBridge.img_vis_W Wc) as (_ & _ & Hv). apply Hv.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia.
    - exact (HROc a Hro Hno Hne). }
  pose proof (lib.Prog.RcMatchLib.cm_bytes_img A.Img0.rsegs mr reac_box_catalogue_match_c.CM_T 3256
                reac_box_catalogue_match_lib.CM_TBL reac_box_catalogue_match_lib.CM_TBL_eq
                ltac:(unfold reac_box_catalogue_match_c.CM_T; lia) ltac:(unfold reac_box_catalogue_match_c.CM_T; lia) HTa)
    as BT.
  pose proof (lib.Prog.RcBoxLib.bytes_at_sub A.Img0.rsegs mr reac_box_catalogue_match_c.CM_T
                reac_box_catalogue_match_lib.CM_TBL (296 * i) 296 BT
                ltac:(rewrite reac_box_catalogue_match_lib.CM_TBL_len; lia)) as BR.
  fold (reac_box_catalogue_match_lib.cm_row i) in BR.
  destruct BR as (B0 & B1 & BB).
  assert (Hj' : (j < length (reac_box_catalogue_match_lib.cm_row i))%nat)
    by (rewrite (reac_box_catalogue_match_lib.cm_row_len i Hi); exact Hj).
  pose proof (BB j Hj') as Hm.
  rewrite (nth_error_nth' _ (Z_to_bv 8 0) Hj') in Hm.
  assert (Ea : reac_box_catalogue_match_c.CM_T + Z.of_nat (296 * i) + Z.of_nat j =
               reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i + Z.of_nat j) by lia.
  rewrite Ea in Hm.
  assert (Hvis : w_H Wc (Z_to_bv 64 (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i + Z.of_nat j)) = false).
  { destruct (A.ProgBridge.img_vis_W Wc) as (_ & _ & Hv). apply Hv.
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, reac_box_catalogue_match_c.CM_T. lia. }
  rewrite (cm_aview_vis_mrd Wc mr _ Hvis). unfold lib.Lib.Mem.wa in Hm. rewrite Hm. reflexivity.
Qed.

(* ---- the model_block call (0x846c8), entered from the loop head of row i ---- *)
Definition cmLHst (i : nat) (pos : Z) (mr : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word) : machine_state :=
  lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) (cm_rg regs 3) (cm_rg regs 4)
      rt0 rt1 rt2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i))
      (Z_to_bv 64 (FRp pos + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (A.AsanRT.shadow_addr (FRp pos)))
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) (cm_rg regs 27)
      rt3 rt4 rt5 rt6)
    fp_regs (Z_to_bv 64 0x846ac) fp_csr None mr (seg_rom tfibsegs).

(* The registers at the callee entry 0x85b44 (ra = 0x846cc). *)
Definition cmMBR (i : nat) (pos : Z) (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word) : bvmap 5 word :=
  lib.Lib.Frame.mkR (Z_to_bv 64 0x846cc) (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) (cm_rg regs 3) (cm_rg regs 4)
      rt0 rt1 rt2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      (Z_to_bv 64 (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (FRp pos + 112))
      ra3 ra4 ra5 ra6 ra7
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i))
      (Z_to_bv 64 (FRp pos + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (A.AsanRT.shadow_addr (FRp pos)))
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) (cm_rg regs 27)
      rt3 rt4 rt5 rt6.

(* The end of the S4 lift: at the callee entry 0x85b44, with S4's invariant at the stretch memory mc. *)
Definition cmP4 (i : nat) (pos : Z) (mb : word -> option byte) : machine_state -> Prop :=
  fun s => exists (mc : word -> option byte) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word),
    s = lib.Lib.MState.MS (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11) fp_regs (Z_to_bv 64 0x85b44) fp_csr None
          mc (lib.Lib.PropExec.seg_rom A.Img0.rsegs) /\
    reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
      (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25)
      (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc /\
    A.AsanRT.addressable mc (FRp pos + 112) 32.

(* The model_block stage: from the loop head of row i (cut invariant at mr) through S4 (one lift, footprint the
   frame's shadow), the jal, and reac_box_model_block (TMB) at p = CM_T + 296 i, b = 0, o = F + 112, to the return
   0x846cc, where the continuation gets the cut invariant again, a0, the 32 bytes the call wrote, and their shadow. *)
Lemma cm_stage_mb : forall (i : nat) pos lyc Sc Wc mr mdc (Q : world tfibsegs -> config -> Prop)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (i < 11)%nat -> lib.Prog.RcMatch.cm_gate len fb = true ->
  (forall j, (j < i)%nat -> nth j lib.Prog.RcMatch.DECLS [] <> lib.Prog.RcMatch.cm_blk fb) ->
  cmCut pos lyc Sc Wc mr mdc ->
  (forall (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) ly2 S2 W2 mem2 md2 (regs2 : bvmap 5 word),
     cmCut pos ly2 S2 W2 mem2 md2 ->
     aregs_preserved (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11) regs2 ->
     lib.Reusable.YK11.getr regs2 10 = w64 (lib.Prog.RcSynth.rc (reac_box_catalogue_match_lib.cm_row i) 0) ->
     lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (FRp pos + 112)
       (lib.Prog.RcSynth.synth (reac_box_catalogue_match_lib.cm_row i) 0 []) ->
     A.AsanRT.addressable mem2 (FRp pos + 112) 32 ->
     SRr tfibsegs W2 (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x846cc) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs Wc (mkCfg (cmLHst i pos mr rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6) mdc) Q.
Proof.
  intros i pos lyc Sc Wc mr mdc Q rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hi Hgate Hno HC K.
  pose proof HC as (J & Eab & Hpos & HSAV & HFW).
  destruct (cm_cut_base pos lyc Sc Wc mr mdc HC) as (EF & Hin & HRm & HAR & BB & INV).
  destruct (cm_frame_facts pos lyc Sc Wc mr mdc HC) as (HFb & HFsh & EFA & EB2 & HFlo & HFhi & _).
  pose proof BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP &
    HMEMCMP & HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSlo & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold A.AsanRT.APPMEM_END in HAE'. unfold A.AsanRT.HIGHMEM_BEG in HHM'.
  destruct (cm_CA SP) as (HCA32 & HCAlo & HCAhi).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & _ & _ & _ & _ & G7).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  destruct (cm_fs2 FS pos) as (E1 & _ & E3).
  pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _). unfold CM_STK in Hslo.
  unfold A.Prog.asan_stack_malloc_c.FS_SIZE, A.Prog.asan_stack_malloc_c.ASAN_GT in *.
  assert (HFR64 : FRp pos mod 64 = 0) by (rewrite E1; Z.div_mod_to_equations; lia).
  set (sF := A.AsanRT.shadow_addr (FRp pos)).
  assert (VS : A.ProgBridge.range_visible (w_H Wc) sF 32).
  { split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; assert (0 <= FRp pos / 8) by (apply Z.div_pos; lia); lia|].
    split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            assert (FRp pos / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia); lia|].
    intros a Ha. replace a with (sF + (a - sF)) by lia. exact (proj1 (proj1 (HFsh (a - sF) ltac:(lia)))). }
  assert (R4sh : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (cm_Hk (w_H Wc) [(sF, sF + 32)])) sF 24).
  { apply cm_rng_Hk.
    - intros a Ha. apply (cm_inR_In [(sF, sF + 32)] sF (sF + 32)); [left; reflexivity | lia].
    - apply (A.ProgBridge.range_visible_sub _ sF 32); [exact VS | lia | lia | lia]. }
  (* lift: S4 to the callee entry *)
  unfold cmLHst.
  apply (cm_lift_base Wc _ fp_regs (Z_to_bv 64 0x846ac) fp_csr mr mdc [(sF, sF + 32)]
           (cmP4 i pos (A.MemNorm.normalize A.Img0.rsegs mr)) Q HRm).
  { refine (reac_box_catalogue_match_F4.cm_model_S4_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
              (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
              (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
              (A.MemNorm.normalize A.Img0.rsegs mr) f len SP FS fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0
              _ i _ (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 Hi _
              (A.MemNorm.normalize A.Img0.rsegs mr) rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
              Hgate Hno INV R4sh).
    intros mc q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 _ _ _ INV' AD'.
    apply reac_box_catalogue_match_F4.cm_jal_mb_F.
    exists mc, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12. split; [reflexivity|]. split; [exact INV' | exact AD']. }
  intros ms1 s1 md1 HP1 Hrel1 Hsame1 Hfs1 Hkeep1 Hsbm1.
  destruct HP1 as (mc & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & Es1 & INV1 & AD1). subst s1.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel1) as (Ems1 & REL1).
  pose proof INV1 as (_ & MU1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAV1 & FW1).
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mr HRm) as REL0.
  pose proof (A.MemNorm.munch_rel A.Img0.rsegs _ mr (A.MemNorm.normalize A.Img0.rsegs mr) (ms_mem ms1) mc
                REL0 REL1 Hsame1 MU1) as MUa.
  pose proof (cm_munch_of_keep Wc _ _ [(sF, sF + 32)] mr (ms_mem ms1) Hkeep1 MUa
                (fun a Hr _ => cm_inR_not_outside _ a Hr) (cm_aWc_noseg SP FS HHM P3)) as MU4.
  assert (HWR4 : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside [(sF, sF + 32)] a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B lyc Sc) lyc [(2, pos)] a).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & [<-|[]] & Hra). cbn [fst snd] in Hra.
    right. right. right. exists 2, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA, EB28, <- G7. fold sF. lia. }
  match type of Hfs1 with lib.Reusable.YK04R.fsteps _ _ ?st0 _ =>
    pose proof (AJF LAWS ctrl_wx CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc st0 ms1 mdc md1 0 _ _ J Hfs1
                  (cm_fp_avoids_Hk (w_H Wc) _) MU4 Hsbm1 HWR4) as J1
  end.
  assert (HCt1 : cmCut pos lyc Sc Wc (ms_mem ms1) md1).
  { split; [exact J1|]. split; [exact Eab|]. split; [exact Hpos|]. split.
    - exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ REL1 SAV1).
    - exact (proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs _ _ _ _ REL1) (FW1 eq_refl)). }
  pose proof (cm_addressable_of_rel _ _ _ _ REL1 AD1) as AD1'.
  destruct (cm_frame_facts pos lyc Sc Wc (ms_mem ms1) md1 HCt1) as (HFb1 & HFsh1 & _).
  pose proof J1 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  assert (HRO1 : arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H Wc) (ms_mem ms1))).
  { apply cm_arodataS.
    exact (arodata_ok_journalP tfibsegs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 (cm_arodataP _ HRO0)). }
  assert (Esp : spZ (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11) = reac_box_catalogue_match.CA SP).
  { change (spZ (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11))
      with (bv_unsigned (Z_to_bv 64 (reac_box_catalogue_match.CA SP))).
    apply cm_u64. lia. }
  assert (Hra1 : lib.Reusable.YK11.getr (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11) 1 = Z_to_bv 64 0x846cc)
    by reflexivity.
  rewrite Ems1, cm_pc_mb.
  eapply SRr_bind.
  { refine (TMB CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc (ms_mem ms1) md1 0
              (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11)
              (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i) 0 (FRp pos + 112)
              (reac_box_catalogue_match_lib.cm_row i) [] J1 HRO1 _ _ Hgp0 Htp0 eq_refl eq_refl eq_refl
              _ _ _ _ _ _ _ _ _ _).
    - rewrite Hra1. exact cm_retok_mb.
    - unfold raZ. rewrite Hra1, cm_u64 by lia. lia.
    - unfold reac_box_catalogue_match_c.CM_T. lia.
    - lia.
    - lia.
    - rewrite Esp. Z.div_mod_to_equations. lia.
    - rewrite Esp. unfold CM_STK, C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK,
        C_reac_box_model_block.BUILD_DT1_SINGLE_STK, ESTACK. lia.
    - rewrite Esp. lia.
    - rewrite Hfrs. change (count_cid 0 ((2, pos) :: frames S0)) with (count_cid 0 (frames S0)). exact HC0.
    - intros _. pose proof cm_tbl_eq as Et.
      split; [unfold reac_box_catalogue_match_c.CM_T; Z.div_mod_to_equations; lia|].
      split; [exact (reac_box_catalogue_match_lib.cm_row_len i Hi)|].
      split.
      { apply cm_garr8_of_view. intros j Hj. exact (cm_row_view pos lyc Sc Wc (ms_mem ms1) md1 i HCt1 Hi j Hj). }
      split; [exists A_CM_TBL, CM_ROWS; split; [exact HGL|]; rewrite cm_tbl_eq; unfold CM_ROWS; lia|].
      split; [apply (Z.le_trans _ A_CM_TBL); [exact HIMG1 | rewrite cm_tbl_eq; lia]|].
      split; [apply (Z.le_trans _ (A_CM_TBL + CM_ROWS + 64)); [rewrite cm_tbl_eq; unfold CM_ROWS; lia | exact HIMG2]|].
      split; [intros x Hx; apply HTBL; rewrite cm_tbl_eq; unfold CM_ROWS; lia|].
      right. right. unfold reac_box_catalogue_match_c.CM_T. lia.
    - intros _ [E5|E5]; discriminate E5.
    - intros _. split; [|split; [|split; [|split]]].
      + left. exists 2, pos. split; [exact Hin|]. split; [discriminate|].
        intros x Hx. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, EB2. lia.
      + intros x Hx. apply cm_not_img. unfold A.Prog.ImgBounds.IMG_HI. lia.
      + intros a Ha. split; [|split; [|split]].
        * right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
          unfold in_zr. cbn [fst snd]. rewrite EFA, EB2. lia.
        * exact (proj1 (HFb1 a ltac:(lia))).
        * exact (proj2 (HFb1 a ltac:(lia))).
        * rewrite Esp. unfold ESTACK. lia.
      + split; [|split; [|split; [|split; [|split]]]].
        * intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
          destruct (HFb1 a ltac:(lia)) as ((Hh & b & Hb) & _).
          rewrite (cm_aview_vis_mrd Wc _ a Hh). unfold lib.Lib.Mem.mrd. rewrite Hb. cbn [option_map]. discriminate.
        * intros x Hx.
          destruct (proj2 (proj2 (proj2 AD1')) (x - (FRp pos + 112)) ltac:(lia)) as (Happ & b & Hb & Hok).
          replace (FRp pos + 112 + (x - (FRp pos + 112))) with x in Happ, Hb, Hok by lia.
          exists (bv_unsigned b).
          assert (Esh : lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x = A.AsanRT.shadow_addr x)
            by (unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr,
                  A.AsanRT.ASAN_K; lia).
          assert (Exs : A.AsanRT.shadow_addr x = sF + (x - FRp pos) / 8).
          { clear - HFR64. unfold sF, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
          assert (Hix : 0 <= (x - FRp pos) / 8 < 32) by (clear - Hx; Z.div_mod_to_equations; lia).
          destruct (HFsh1 ((x - FRp pos) / 8) Hix) as ((Hh & _) & _).
          fold sF in Hh. rewrite <- Exs in Hh.
          split.
          -- rewrite Esh, (cm_aview_vis_mrd Wc _ _ Hh).
             change (lib.Lib.Mem.wa (A.AsanRT.shadow_addr x)) with (Z_to_bv 64 (A.AsanRT.shadow_addr x)) in Hb.
             rewrite Hb. reflexivity.
          -- destruct Hok as [Hz|(Hlt & Hle)].
             ++ left. rewrite (cm_signed_small b ltac:(lia)). exact Hz.
             ++ right. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm8.
                rewrite (cm_signed_small b ltac:(lia)). lia.
        * intros s Hs. rewrite <- !G7 in Hs.
          assert (Hs' : sF + 8 <= s < sF + 24).
          { clear - Hs HFR64. unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *. Z.div_mod_to_equations. lia. }
          destruct (HFsh1 (s - sF) ltac:(lia)) as ((Hh & b & Hb) & _).
          fold sF in Hh, Hb. replace (sF + (s - sF)) with s in Hh, Hb by lia.
          rewrite (cm_aview_vis_mrd Wc _ s Hh). unfold lib.Lib.Mem.mrd. rewrite Hb. cbn [option_map]. discriminate.
        * pose proof (P4 (FRp pos + 112) ltac:(lia)) as Ap1. pose proof (P4 (FRp pos + 144) ltac:(lia)) as Ap2.
          unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Ap1, Ap2.
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
        * lia.
        * lia.
      + right. rewrite Esp. unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK,
          C_reac_box_model_block.BUILD_DT1_SINGLE_STK, ESTACK. lia. }
  (* the return of reac_box_model_block *)
  intros W2 c2 Hle2 (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & HP2 & Hfr2 & Hab2 & Hbr). subst c2.
  assert (E0 : ((reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i =? 0) || (FRp pos + 112 =? 0))%bool = false).
  { apply orb_false_iff. split; apply Z.eqb_neq; unfold reac_box_catalogue_match_c.CM_T; lia. }
  rewrite E0 in Hbr. destruct Hbr as (Ha0 & Hg2 & HK2). rewrite Esp in HK2.
  destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  change (0 + C_reac_box_model_block.EV_BMB) with 0 in J2.
  destruct (cm_frame_facts_J pos ly2 S2 W2 mem2 md2 J2 Hpos) as (HFb2 & HFsh2 & _).
  pose proof HCt1 as (_ & _ & _ & SAV1' & FW1').
  assert (HCt2 : cmCut pos ly2 S2 W2 mem2 md2).
  { split; [exact J2|]. split; [rewrite Hab2; exact Eab|]. split; [exact Hpos|]. split.
    - apply (cm_rw_of_view2 Wc W2 (ms_mem ms1) mem2 (SP - 96) (cm_saves regs)); [|exact SAV1'].
      assert (Csz : Z.of_nat (lib.Lib.Cells.cells_size (cm_saves regs)) = 96) by reflexivity.
      intros a Ha. rewrite Csz in Ha.
      assert (Hac : lib.Reusable.YM05.alloc_ceiling <= SP - 9136) by (clear - Hceil Hslo; lia).
      assert (Ka : lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64) by (clear - Hac RS Ha; lia).
      assert (Na : ~ (reac_box_catalogue_match.CA SP - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK <= a <
                      reac_box_catalogue_match.CA SP)) by lia.
      assert (Ea : ~ (FRp pos + 112 <= a < FRp pos + 112 + 32)) by lia.
      pose proof (Hpres1 a ltac:(unfold CM_STK; lia)) as Hp1.
      split; [exact (K1 a Ka Na Ea)|]. split; [exact (proj1 Hp1)|]. exact (K5 a Ka Na Hp1).
    - apply (cm_bytes_of_view2 Wc W2 (ms_mem ms1) mem2 (FRp pos + 248) _); [|exact FW1'].
      intros j Hj. rewrite lib.Lib.Mem.length_le8 in Hj.
      split; [|split].
      + apply (K4 2 pos); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, EB2; lia |
                           cbv beta; lia].
      + exact (proj1 (proj1 (HFb1 (FRp pos + 248 + Z.of_nat j) ltac:(lia)))).
      + exact (proj1 (proj1 (HFb2 (FRp pos + 248 + Z.of_nat j) ltac:(lia)))). }
  pose proof (lib.Prog.RcSynthLib.rs_synth_len (reac_box_catalogue_match_lib.cm_row i) 0 []
                (reac_box_catalogue_match_lib.cm_row_len i Hi)) as SL.
  assert (BY2 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (FRp pos + 112)
                  (lib.Prog.RcSynth.synth (reac_box_catalogue_match_lib.cm_row i) 0 [])).
  { apply (cm_bytes_of_view W2); [lia | rewrite SL; lia |].
    intros j Hj. rewrite (cm_view_of_garr8 _ _ _ _ j Hg2 ltac:(unfold C_reac_box_model_block.bmb_z; rewrite length_map; exact Hj)).
    f_equal. unfold C_reac_box_model_block.bmb_z.
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    apply (map_nth (fun x : byte => bv_unsigned x)). }
  assert (AD2 : A.AsanRT.addressable mem2 (FRp pos + 112) 32).
  { apply (cm_addressable_view Wc W2 (ms_mem ms1) mem2); [|exact AD1'].
    intros j Hj.
    assert (Exs : A.AsanRT.shadow_addr (FRp pos + 112 + j) = sF + (112 + j) / 8).
    { clear - HFR64. unfold sF, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
    assert (Hk : 14 <= (112 + j) / 8 < 18) by (clear - Hj; Z.div_mod_to_equations; lia).
    rewrite Exs.
    split; [|split].
    - apply (K4 2 pos); [exact Hin | right; unfold in_zr; cbn [fst snd]; rewrite EFA, EB28, <- G7; fold sF; lia |].
      pose proof (P4 (FRp pos + 112) ltac:(lia)) as Ap1. pose proof (P4 (FRp pos + 143) ltac:(lia)) as Ap2.
      cbv beta. clear - Ap1 Ap2 Hk HFR64.
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Ap1, Ap2.
      unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
    - exact (proj1 (proj1 (HFsh1 ((112 + j) / 8) ltac:(lia)))).
    - exact (proj1 (proj1 (HFsh2 ((112 + j) / 8) ltac:(lia)))). }
  exact (K q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ly2 S2 W2 mem2 md2 regs2 HCt2 HP2 Ha0 BY2 AD2).
Qed.

(* ---- shadow-interval arithmetic for the S5 footprint ---- *)
Lemma cm_sa_mono : forall x y, x <= y -> A.AsanRT.shadow_addr x <= A.AsanRT.shadow_addr y.
Proof. intros x y H. unfold A.AsanRT.shadow_addr. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma cm_sa_ge_lo : forall x, 0 <= x -> A.AsanRT.LOWMEM_END <= A.AsanRT.shadow_addr x.
Proof.
  intros x Hx. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.LOWMEM_END.
  assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma cm_sa_le_hi : forall x, 0 <= x <= A.AsanRT.APPMEM_END -> A.AsanRT.shadow_addr x <= A.AsanRT.HIGHMEM_BEG.
Proof.
  intros x Hx. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cm_cover_lo : forall x, 0 <= x -> A.AsanRT.LOWMEM_END <= 8 * (A.AsanRT.shadow_addr x / 8).
Proof.
  intros x Hx. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.LOWMEM_END. Z.div_mod_to_equations. lia.
Qed.

Lemma cm_cover_le : forall x y, 0 <= x < y -> y mod 64 = 0 ->
  8 * (A.AsanRT.shadow_addr x / 8) + 8 <= A.AsanRT.shadow_addr y.
Proof. intros x y Hx Hy. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma cm_cover_ge : forall x y, 0 <= y <= x -> y mod 64 = 0 ->
  A.AsanRT.shadow_addr y <= 8 * (A.AsanRT.shadow_addr x / 8).
Proof. intros x y Hx Hy. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma cm_aWc_cases : forall S1 F1 a, ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc S1 F1) a ->
  (S1 - 9136 <= a < S1) \/ (A.AsanRT.shadow_addr (S1 - 9136) <= a < A.AsanRT.shadow_addr S1) \/
  (exists d, In d (A.Prog.RcAsanFP.fp_w [0%nat; 1%nat; 2%nat] F1) /\ fst d <= a < snd d).
Proof.
  intros S1 F1 a H. destruct (cm_not_outside _ _ H) as (r & Hr & Hra).
  unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs in Hr.
  destruct Hr as [<-|Hr]; [left; exact Hra|].
  apply in_app_or in Hr as [Hr|[<-|[]]].
  - right. right. exists r. split; [exact Hr | exact Hra].
  - right. left. exact Hra.
Qed.

Lemma cm_aWc_hi : forall S1 F1 a, A.AsanRT.HIGHMEM_BEG <= S1 - 9136 -> A.Prog.asan_stack_malloc_c.ASAN_GT <= F1 ->
  ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc S1 F1) a -> A.Prog.ImgBounds.IMG_HI <= a.
Proof.
  intros S1 F1 a HS HF Hx. destruct (cm_aWc_cases S1 F1 a Hx) as [Hw | [Hws | (d & Hd & Hda)]].
  - unfold A.AsanRT.HIGHMEM_BEG, A.Prog.ImgBounds.IMG_HI in *. lia.
  - pose proof (cm_sa_ge_lo (S1 - 9136) ltac:(unfold A.AsanRT.HIGHMEM_BEG in HS; lia)) as L.
    unfold A.AsanRT.LOWMEM_END, A.Prog.ImgBounds.IMG_HI in *. lia.
  - unfold A.Prog.asan_stack_malloc_c.ASAN_GT in HF.
    destruct (cm_fpw_in F1 d Hd ltac:(lia)) as [(D1 & D2) | (D1 & D2)].
    + unfold A.Prog.ImgBounds.IMG_HI. lia.
    + pose proof (cm_sa_ge_lo F1 ltac:(lia)) as L. unfold A.AsanRT.LOWMEM_END, A.Prog.ImgBounds.IMG_HI in *. lia.
Qed.

(* The record's bytes and their aligned shadow cover lie outside aWc (they are read-only for the run). *)
Lemma cm_rec_out : forall a,
  0 <= f -> f + 50 <= lib.Reusable.YM05.alloc_ceiling ->
  (f + 50 <= A.AsanRT.LOWMEM_END \/ A.AsanRT.HIGHMEM_BEG <= f) ->
  (f + 50 <= FS \/ FS + 11571200 <= f) ->
  FS mod 4096 = 0 -> 0 < FS -> FS + 11571200 <= SP - 9136 ->
  (forall b, FS <= b < FS + 11571200 -> A.AsanRT.app_mem b) ->
  lib.Reusable.YM05.alloc_ceiling <= SP - 9136 -> A.AsanRT.HIGHMEM_BEG <= SP - 9136 -> SP <= A.AsanRT.APPMEM_END ->
  (f + 18 <= a < f + 50 \/
   8 * (A.AsanRT.shadow_addr (f + 18) / 8) <= a < 8 * (A.AsanRT.shadow_addr (f + 18 + 32 - 1) / 8) + 8) ->
  lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) a.
Proof.
  intros a H0 Hac Happ HBF HF64 HF0 HFS HPF HacSP HHM HAE Ha.
  destruct (cm_outside_dec (reac_box_catalogue_match.aWc SP FS) a) as [Ho|Hin]; [exact Ho|]. exfalso.
  pose proof lib.Reusable.YM05.alloc_ceiling_value as (Hmn & Hm4).
  assert (Hac64 : lib.Reusable.YM05.alloc_ceiling mod 64 = 0) by (clear - Hm4; Z.div_mod_to_equations; lia).
  assert (HFS64 : FS mod 64 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  assert (HFS64' : (FS + 11571200) mod 64 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  pose proof (cm_cover_lo (f + 18) ltac:(lia)) as CL.
  pose proof (cm_cover_le (f + 18 + 32 - 1) lib.Reusable.YM05.alloc_ceiling ltac:(lia) Hac64) as CH.
  pose proof (cm_sa_mono lib.Reusable.YM05.alloc_ceiling (SP - 9136) HacSP) as M1.
  pose proof (cm_sa_le_hi SP ltac:(unfold A.AsanRT.HIGHMEM_BEG in HHM; lia)) as M2.
  pose proof (cm_sa_le_hi lib.Reusable.YM05.alloc_ceiling ltac:(unfold A.AsanRT.APPMEM_END in *; lia)) as M3.
  pose proof (cm_sa_ge_lo (SP - 9136) ltac:(unfold A.AsanRT.HIGHMEM_BEG in HHM; lia)) as M4.
  destruct (cm_aWc_cases SP FS a Hin) as [Hw | [Hws | (d & Hd & Hda)]].
  - unfold A.AsanRT.HIGHMEM_BEG in *. lia.
  - destruct Ha as [Ha|Ha]; unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG in *; lia.
  - pose proof (cm_sa_ge_lo FS ltac:(lia)) as M5.
    pose proof (cm_sa_le_hi (FS + 3182592) ltac:(unfold A.AsanRT.HIGHMEM_BEG in *; lia)) as M6.
    destruct (cm_fpw_in FS d Hd ltac:(lia)) as [(D1 & D2) | (D1 & D2)]; destruct Ha as [Ha|Ha].
    + lia.
    + pose proof (HPF a ltac:(lia)) as Ap. unfold A.AsanRT.app_mem in Ap.
      unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia.
    + unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG in *. lia.
    + destruct HBF as [HB|HB].
      * pose proof (cm_cover_le (f + 18 + 32 - 1) FS ltac:(lia) HFS64). lia.
      * pose proof (cm_cover_ge (f + 18) (FS + 11571200) ltac:(lia) HFS64').
        pose proof (cm_sa_mono (FS + 3182592) (FS + 11571200) ltac:(lia)). lia.
Qed.

Lemma cm_pres_get : forall (R R2 : bvmap 5 word) (k : Z), aregs_preserved R R2 -> acallee_saved k ->
  reg_get R2 (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k).
Proof.
  intros R R2 k H Hk. pose proof (H k Hk) as E. unfold acallee_saved in Hk.
  destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [exact E|exact E|exact E|exact E|exact E|].
  assert (Hk' : k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27)
    by lia.
  destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; exact E.
Qed.

(* The exit cut 0x84724 with a0 = want. *)
Definition cmXCst (pos : Z) (mr : word -> option byte)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) : machine_state :=
  lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) (cm_rg regs 3) (cm_rg regs 4)
      u0 u1 u2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) y0 y1 y2 y3 y4 y5 y6 y7
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (lib.Prog.RcMatch.want reac_box_catalogue_match_c.CM_T len fb))
      z4 z5 (Z_to_bv 64 (A.AsanRT.shadow_addr (FRp pos))) (Z_to_bv 64 (FRp pos)) z8 z9 z10 (cm_rg regs 27) u3 u4 u5 u6)
    fp_regs (Z_to_bv 64 0x84724) fp_csr None mr (seg_rom tfibsegs).

(* The end of the S5 lift: the loop head of row i + 1, or the exit cut. *)
Definition cmP5 (i : nat) (pos : Z) (mb : word -> option byte) : machine_state -> Prop :=
  fun s =>
    (exists (mc : word -> option byte) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
       s = cmLHst (i + 1) pos mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 /\
       (i + 1 < 11)%nat /\
       (forall j, (j < i + 1)%nat -> nth j lib.Prog.RcMatch.DECLS [] <> lib.Prog.RcMatch.cm_blk fb) /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc) \/
    (exists (mc : word -> option byte) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
       s = cmXCst pos mc x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc).

(* The S5 stage: from the return of reac_box_model_block (0x846cc, row i) through the bcmp wrapper (inside the
   lift, by its footprint contract) to the loop head of row i + 1 or the exit cut 0x84724; one lift, footprint
   {window, image, record, record shadow cover, frame, frame shadow}, writes {window, frame, frame shadow}. *)
Lemma cm_stage_s5 : forall (i : nat) pos ly2 S2 W2 mem2 md2 (regs2 : bvmap 5 word)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (Qf : world tfibsegs -> config -> Prop),
  (i < 11)%nat -> lib.Prog.RcMatch.cm_gate len fb = true ->
  (forall j, (j < i)%nat -> nth j lib.Prog.RcMatch.DECLS [] <> lib.Prog.RcMatch.cm_blk fb) ->
  cmCut pos ly2 S2 W2 mem2 md2 ->
  aregs_preserved (cmMBR i pos q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11) regs2 ->
  lib.Reusable.YK11.getr regs2 10 = w64 (lib.Prog.RcSynth.rc (reac_box_catalogue_match_lib.cm_row i) 0) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (FRp pos + 112)
    (lib.Prog.RcSynth.synth (reac_box_catalogue_match_lib.cm_row i) 0 []) ->
  A.AsanRT.addressable mem2 (FRp pos + 112) 32 ->
  (forall lyc Sc Wc mr mdc (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
     cmCut pos lyc Sc Wc mr mdc -> (i + 1 < 11)%nat ->
     (forall j, (j < i + 1)%nat -> nth j lib.Prog.RcMatch.DECLS [] <> lib.Prog.RcMatch.cm_blk fb) ->
     SRr tfibsegs Wc (mkCfg (cmLHst (i + 1) pos mr rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6)
                         mdc) Qf) ->
  (forall lyc Sc Wc mr mdc (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
     cmCut pos lyc Sc Wc mr mdc ->
     SRr tfibsegs Wc (mkCfg (cmXCst pos mr x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6) mdc) Qf) ->
  SRr tfibsegs W2 (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x846cc) mem2 (seg_rom tfibsegs)) md2) Qf.
Proof.
  intros i pos ly2 S2 W2 mem2 md2 regs2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 Qf Hi Hgate Hno HC HP2 Ha0 BY2 AD2 KL KX.
  pose proof HC as (J & Eab & Hpos & HSAV & HFW).
  destruct (cm_cut_base pos ly2 S2 W2 mem2 md2 HC) as (EF & Hin & HRm & HAR & BB & INV).
  destruct (cm_frame_facts pos ly2 S2 W2 mem2 md2 HC) as (HFb & HFsh & EFA & EB2 & HFlo & HFhi & _).
  pose proof BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP &
    HMEMCMP & HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & Pstk) & _ & _ & _ & HFSlo & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold A.AsanRT.APPMEM_END in HAE'. unfold A.AsanRT.HIGHMEM_BEG in HHM'.
  destruct (cm_CA SP) as (HCA32 & HCAlo & HCAhi).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & _ & _ & _ & _ & G7).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  destruct (cm_fs2 FS pos) as (E1 & _ & E3).
  pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _). unfold CM_STK in Hslo.
  assert (Hac : lib.Reusable.YM05.alloc_ceiling <= SP - 9136) by (clear - Hceil Hslo; lia).
  unfold A.Prog.asan_stack_malloc_c.FS_SIZE in HFSlo, P4.
  assert (HFR64 : FRp pos mod 64 = 0) by (rewrite E1; clear - P2; Z.div_mod_to_equations; lia).
  set (sF := A.AsanRT.shadow_addr (FRp pos)).
  set (mb := A.MemNorm.normalize A.Img0.rsegs mem2).
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem2 HRm) as REL0. fold mb in REL0.
  (* the gate gives 50 <= len, so the record is a live block *)
  assert (H50 : 50 <= len).
  { revert Hgate. unfold lib.Prog.RcMatch.cm_gate. destruct (50 <=? len) eqn:E50.
    - intros _. apply Z.leb_le. exact E50.
    - cbn [andb]. intros Hg. discriminate Hg. }
  destruct (HBLK H50) as (Hb0 & Hreq).
  assert (Hb : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Eab; exact Hb0).
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 f Lf HAR Hb) as (_ & _ & Hceilb & Happb & _).
  pose proof (BLKFS LAWS ly2 S2 W2 mem2 md2 f Lf HAR Hb) as HBF0. rewrite EF in HBF0.
  unfold lib.Reusable.YG0f.kFakeStackSize in HBF0.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happb. unfold ASAN_CEIL in Hceilb.
  assert (Hrec1 : f + 50 <= lib.Reusable.YM05.alloc_ceiling) by lia.
  assert (Happ' : f + 50 <= A.AsanRT.LOWMEM_END \/ A.AsanRT.HIGHMEM_BEG <= f).
  { unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG. destruct Happb as (_ & [Hl | (Hh1 & Hh2)]); [left | right]; lia. }
  assert (HBF : f + 50 <= FS \/ FS + 11571200 <= f) by lia.
  (* visibility *)
  assert (VF : A.ProgBridge.range_visible (w_H W2) (FRp pos) 256).
  { apply (cm_vis_of_present _ mem2); [lia | lia | intros a Ha; exact (proj1 (HFb a Ha))]. }
  assert (VS : A.ProgBridge.range_visible (w_H W2) sF 32).
  { split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; assert (0 <= FRp pos / 8) by (apply Z.div_pos; lia); lia|].
    split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            assert (FRp pos / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia); lia|].
    intros a Ha. replace a with (sF + (a - sF)) by lia. exact (proj1 (proj1 (HFsh (a - sF) ltac:(lia)))). }
  assert (VW : forall lo n, SP - 9136 <= lo -> lo + n <= SP -> A.ProgBridge.range_visible (w_H W2) lo n).
  { intros lo n Hlo Hhi.
    exact (cm_win_vis SP ly S0 W mem md [(2, pos)] ly2 S2 W2 mem2 md2 0 lo n J ltac:(lia) ltac:(unfold CM_STK; lia)
             Hhi ltac:(lia)). }
  (* the footprint and the write set *)
  set (R5 := [(SP - 9136, SP); (A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI); (f + 18, f + 50);
              (8 * (A.AsanRT.shadow_addr (f + 18) / 8), 8 * (A.AsanRT.shadow_addr (f + 18 + 32 - 1) / 8) + 8);
              (FRp pos, FRp pos + 256); (sF, sF + 32)]).
  set (WR5 := [(SP - 9136, SP); (FRp pos, FRp pos + 256); (sF, sF + 32)]).
  set (RNG5 := A.ProgBridge.RNG_W (cm_Hk (w_H W2) R5)).
  assert (R1 : lib.Lib.RngBytes.rng_bytes RNG5) by exact (A.ProgBridge.rng_bytes_RNG_W _).
  assert (R2 : lib.Lib.ExecF.rng RNG5 A.Prog.bcmp_wrap_c.IMG_LO
                 (A.Prog.bcmp_wrap_c.IMG_HI - A.Prog.bcmp_wrap_c.IMG_LO)).
  { change A.Prog.bcmp_wrap_c.IMG_LO with A.Prog.ImgBounds.IMG_LO.
    change A.Prog.bcmp_wrap_c.IMG_HI with A.Prog.ImgBounds.IMG_HI.
    apply cm_rng_Hk; [|exact (A.ProgBridge.img_vis_W W2)].
    intros a Ha. apply (cm_inR_In R5 A.Prog.ImgBounds.IMG_LO A.Prog.ImgBounds.IMG_HI); [right; left; reflexivity | lia]. }
  assert (R3 : lib.Lib.ExecF.rng RNG5 (reac_box_catalogue_match.CA SP - A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
                 A.Prog.bcmp_wrap_c.BCMP_WRAP_K).
  { change A.Prog.bcmp_wrap_c.BCMP_WRAP_K with 4560.
    apply cm_rng_Hk; [|apply VW; lia].
    intros a Ha. apply (cm_inR_In R5 (SP - 9136) SP); [left; reflexivity | lia]. }
  assert (R4 : lib.Lib.ExecF.rng RNG5 (f + 18) 32).
  { apply cm_rng_Hk;
      [|exact (A.ProgWorldVisHeap.heap_vis B LAWS ly2 S2 W2 mem2 md2 f Lf (f + 18) 32 HAR Hb ltac:(lia) ltac:(lia))].
    intros a Ha. apply (cm_inR_In R5 (f + 18) (f + 50)); [right; right; left; reflexivity | lia]. }
  assert (R5c : lib.Lib.ExecF.rng RNG5 (8 * (A.AsanRT.shadow_addr (f + 18) / 8))
                  (8 * (A.AsanRT.shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (f + 18) / 8))).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly2 S2 W2 mem2 md2 f Lf (f + 18) 32 HAR Hb
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E0|V0]; [lia|].
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in V0.
    apply cm_rng_Hk.
    - intros a Ha. apply (cm_inR_In R5 (8 * (A.AsanRT.shadow_addr (f + 18) / 8))
                           (8 * (A.AsanRT.shadow_addr (f + 18 + 32 - 1) / 8) + 8));
        [right; right; right; left; reflexivity | lia].
    - rewrite (Z.mul_comm 8 (A.AsanRT.shadow_addr (f + 18) / 8)),
              (Z.mul_comm 8 (A.AsanRT.shadow_addr (f + 18 + 32 - 1) / 8)).
      exact V0. }
  assert (R6 : lib.Lib.ExecF.rng RNG5 (FRp pos + 112) 32).
  { apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ (FRp pos) 256); [exact VF | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R5 (FRp pos) (FRp pos + 256)); [right; right; right; right; left; reflexivity | lia]. }
  assert (E7a : 8 * (A.AsanRT.shadow_addr (FRp pos + 112) / 8) = sF + 8).
  { clear - HFR64. unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (E7b : 8 * (A.AsanRT.shadow_addr (FRp pos + 112 + 32 - 1) / 8) + 8 = sF + 24).
  { clear - HFR64. unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (R7 : lib.Lib.ExecF.rng RNG5 (8 * (A.AsanRT.shadow_addr (FRp pos + 112) / 8))
                 (8 * (A.AsanRT.shadow_addr (FRp pos + 112 + 32 - 1) / 8) + 8 -
                  8 * (A.AsanRT.shadow_addr (FRp pos + 112) / 8))).
  { rewrite E7b, E7a. replace (sF + 24 - (sF + 8)) with 16 by lia.
    apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ sF 32); [exact VS | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R5 sF (sF + 32)); [right; right; right; right; right; left; reflexivity | lia]. }
  assert (R8 : lib.Lib.ExecF.rng RNG5 sF 24).
  { apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ sF 32); [exact VS | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R5 sF (sF + 32)); [right; right; right; right; right; left; reflexivity | lia]. }
  (* the stretch's continuations *)
  set (P5 := cmP5 i pos mb).
  assert (XT : reac_box_catalogue_match_F5_on.cmXt_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                 (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                 (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                 mb f len SP FS fb RNG5 P5 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1).
  { intros mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Hr INV'.
    apply lib.Lib.ExecF.evtF_done. unfold P5, cmP5. right.
    exists mc, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z4, z5, z8, z9, z10, u3, u4, u5, u6.
    split; [subst r; reflexivity | exact INV']. }
  assert (BK : (i + 1 < 11)%nat ->
               reac_box_catalogue_match_F5_on.cmLH_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                 (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                 (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                 mb f len SP FS fb RNG5 (i + 1) P5 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1).
  { intros Hi1 mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 _ Hno' INV' _.
    apply lib.Lib.ExecF.evtF_done. unfold P5, cmP5. left.
    exists mc, rra, rt0, rt1, rt2, ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, rt3, rt4, rt5, rt6.
    split; [reflexivity|]. split; [exact Hi1|]. split; [exact Hno' | exact INV']. }
  pose proof (reac_box_catalogue_match_F5_on.cm_none_holds_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                mb f len SP FS fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 RNG5 P5 (FRp pos)
                (reac_box_catalogue_match.CA SP) pos 1 XT) as NONE.
  pose proof (reac_box_catalogue_match_F5_on.cm_hit_holds_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                mb f len SP FS fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 RNG5 P5 (FRp pos)
                (reac_box_catalogue_match.CA SP) pos 1 XT) as HIT.
  pose proof (reac_box_catalogue_match_F5_on.cm_bcmp_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                mb f len SP FS fb A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU
                HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 RNG5 i P5 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1
                Hi BK NONE HIT) as CMBC.
  (* the registers at the return, in the stretch's shape *)
  set (R5reg := lib.Lib.Frame.mkR (reg_get regs2 (Z_to_bv 5 1)) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (cm_rg regs 3) (cm_rg regs 4) (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
         (reg_get regs2 (Z_to_bv 5 7)) (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (Z_to_bv 64 (lib.Prog.RcSynth.rc (reac_box_catalogue_match_lib.cm_row i) 0))
         (reg_get regs2 (Z_to_bv 5 11)) (reg_get regs2 (Z_to_bv 5 12)) (reg_get regs2 (Z_to_bv 5 13))
         (reg_get regs2 (Z_to_bv 5 14)) (reg_get regs2 (Z_to_bv 5 15)) (reg_get regs2 (Z_to_bv 5 16))
         (reg_get regs2 (Z_to_bv 5 17))
         (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 (reac_box_catalogue_match_c.CM_T + 296 * Z.of_nat i))
         (Z_to_bv 64 (FRp pos + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 sF) (Z_to_bv 64 (FRp pos))
         (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) (cm_rg regs 27)
         (reg_get regs2 (Z_to_bv 5 28)) (reg_get regs2 (Z_to_bv 5 29)) (reg_get regs2 (Z_to_bv 5 30))
         (reg_get regs2 (Z_to_bv 5 31))).
  assert (EQV : lib.Lib.Regs6ss.xregs_eqv regs2 R5reg).
  { unfold R5reg. apply lib.Lib.Regs6ss.mkR_eqv_of;
      first [ reflexivity
               | match goal with |- reg_get ?RR ?r = _ =>
                   let k := eval vm_compute in (bv_unsigned r) in
                   (transitivity (reg_get RR (Z_to_bv 5 k)); [reflexivity|]);
                   first [ (rewrite (cm_pres_get _ _ k HP2 ltac:(unfold acallee_saved; lia)); reflexivity)
                         | (transitivity (lib.Reusable.YK11.getr RR 10); [reflexivity | rewrite Ha0; reflexivity]) ]
                 end ]. }
  change (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x846cc) mem2 (seg_rom tfibsegs)) md2)
    with (mkCfg (lib.Lib.MState.MS regs2 fp_regs (Z_to_bv 64 0x846cc) fp_csr None mem2 (seg_rom tfibsegs)) md2).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv tfibsegs W2 R5reg regs2 fp_regs (Z_to_bv 64 0x846cc) fp_csr None mem2
           (seg_rom tfibsegs) md2 Qf); [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ EQV)].
  (* lift: S5 *)
  apply (cm_lift_base W2 R5reg fp_regs (Z_to_bv 64 0x846cc) fp_csr mem2 md2 R5 P5 Qf HRm).
  { refine (reac_box_catalogue_match_F5_on.cm_model_ret_rb_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
              (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
              (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
              mb f len SP FS fb RNG5 i P5 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 Hi CMBC
              (reg_get regs2 (Z_to_bv 5 1)) (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
              (reg_get regs2 (Z_to_bv 5 7)) (reg_get regs2 (Z_to_bv 5 11)) (reg_get regs2 (Z_to_bv 5 12))
              (reg_get regs2 (Z_to_bv 5 13)) (reg_get regs2 (Z_to_bv 5 14)) (reg_get regs2 (Z_to_bv 5 15))
              (reg_get regs2 (Z_to_bv 5 16)) (reg_get regs2 (Z_to_bv 5 17)) (reg_get regs2 (Z_to_bv 5 28))
              (reg_get regs2 (Z_to_bv 5 29)) (reg_get regs2 (Z_to_bv 5 30)) (reg_get regs2 (Z_to_bv 5 31))
              Hgate Hno INV (A.MemNormTr.addressable_normalize mem2 _ _ HRm AD2)
              (proj1 (A.MemNorm.bytes_at_rel A.Img0.rsegs mem2 mb _ _ REL0) BY2) R1 R2 R3 R4 R5c R6 R7 R8). }
  (* after S5 *)
  assert (INC : forall a, cm_inR R5 a = true -> ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) a ->
                  ~ lib.Lib.Frame.outside WR5 a).
  { intros a Hr Hx. unfold cm_inR in Hr. apply existsb_exists in Hr as ([lo hi] & Hin5 & Hlh).
    apply andb_prop in Hlh as [Hl Hh]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hh. cbn [fst snd] in Hl, Hh.
    unfold R5 in Hin5. destruct Hin5 as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
    - exact (cm_in_not_outside WR5 (SP - 9136) SP a (or_introl eq_refl) (conj Hl Hh)).
    - exfalso. pose proof (cm_aWc_hi SP FS a HHM P3 Hx). lia.
    - exfalso. apply Hx. apply cm_rec_out; [lia | exact Hrec1 | exact Happ' | exact HBF | exact P2 | exact P1 |
                                            exact HFSlo | exact P4 | exact Hac | exact HHM | exact HAE | left; lia].
    - exfalso. apply Hx. apply cm_rec_out; [lia | exact Hrec1 | exact Happ' | exact HBF | exact P2 | exact P1 |
                                            exact HFSlo | exact P4 | exact Hac | exact HHM | exact HAE | right; lia].
    - exact (cm_in_not_outside WR5 (FRp pos) (FRp pos + 256) a (or_intror (or_introl eq_refl)) (conj Hl Hh)).
    - exact (cm_in_not_outside WR5 sF (sF + 32) a (or_intror (or_intror (or_introl eq_refl))) (conj Hl Hh)). }
  assert (HWR5 : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR5 a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B ly2 S2) ly2 [(2, pos)] a).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & Hr & Hra).
    unfold WR5 in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hra.
    - left. unfold CM_STK. lia.
    - right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB2. lia.
    - right. right. right. exists 2, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB28, <- G7. fold sF. lia. }
  intros ms5 s5 md5 HP5 Hrel5 Hsame5 Hfs5 Hkeep5 Hsbm5.
  unfold P5, cmP5 in HP5.
  destruct HP5 as [(mc & rra & rt0 & rt1 & rt2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & rt3 & rt4 & rt5 & rt6 &
                    Es5 & Hi1 & Hno1 & INV5) |
                   (mc & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & z5 & z8 & z9 & z10 & u3 & u4 &
                    u5 & u6 & Es5 & INV5)];
    subst s5; [unfold cmLHst in Hrel5 | unfold cmXCst in Hrel5];
    destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel5) as (Ems5 & REL5);
    pose proof INV5 as (_ & MU5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAV5 & FW5);
    pose proof (A.MemNorm.munch_rel A.Img0.rsegs _ mem2 mb (ms_mem ms5) mc REL0 REL5 Hsame5 MU5) as MUa;
    pose proof (cm_munch_of_keep W2 _ _ WR5 mem2 (ms_mem ms5) Hkeep5 MUa INC (cm_aWc_noseg SP FS HHM P3)) as MU5';
    (match type of Hfs5 with lib.Reusable.YK04R.fsteps _ _ ?st0 _ =>
       pose proof (AJF LAWS ctrl_wx CM_STK SP [] ly S0 W mem md [(2, pos)] ly2 S2 W2 st0 ms5 md2 md5 0 _ _ J Hfs5
                     (cm_fp_avoids_Hk (w_H W2) _) MU5' Hsbm5 HWR5) as J5
     end);
    (assert (HC5 : cmCut pos ly2 S2 W2 (ms_mem ms5) md5);
     [ split; [exact J5|]; split; [exact Eab|]; split; [exact Hpos|]; split;
       [ exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ REL5 SAV5)
       | exact (proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs _ _ _ _ REL5) (FW5 eq_refl)) ] |]);
    rewrite Ems5.
  - exact (KL ly2 S2 W2 (ms_mem ms5) md5 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 HC5 Hi1 Hno1).
  - exact (KX ly2 S2 W2 (ms_mem ms5) md5 x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 HC5).
Qed.

(* ---- the 11-row loop: from the loop head of row i, by induction on 11 - i ----
   Each row is the model_block stage (S4, the call) then the S5 stage, which ends at the loop head of row i + 1
   (the induction hypothesis) or at the exit cut (cm_stage_exit). *)
Lemma cm_rows : forall (n i : nat) pos lyc Sc Wc mr mdc
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (11 - i = n)%nat -> (i < 11)%nat -> lib.Prog.RcMatch.cm_gate len fb = true ->
  (forall j, (j < i)%nat -> nth j lib.Prog.RcMatch.DECLS [] <> lib.Prog.RcMatch.cm_blk fb) ->
  cmCut pos lyc Sc Wc mr mdc ->
  SRr tfibsegs Wc (mkCfg (cmLHst i pos mr rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6) mdc)
    (treac_box_catalogue_match_post regs ly S0 W mem md len fb).
Proof.
  induction n as [|n IH];
    intros i pos lyc Sc Wc mr mdc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hn Hi Hg Hno HC;
    [lia|].
  apply (cm_stage_mb i pos lyc Sc Wc mr mdc _ rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
           Hi Hg Hno HC).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ly2 S2 W2 mem2 md2 regs2 HCt2 HP2 Ha0 BY2 AD2.
  apply (cm_stage_s5 i pos ly2 S2 W2 mem2 md2 regs2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 _ Hi Hg Hno HCt2 HP2 Ha0
           BY2 AD2).
  - intros lyc' Sc' Wc' mr' mdc' rra' rt0' rt1' rt2' ra0' ra1' ra2' ra3' ra4' ra5' ra6' ra7' rt3' rt4' rt5' rt6'
      HC' Hi1 Hno1.
    exact (IH (i + 1)%nat pos lyc' Sc' Wc' mr' mdc' rra' rt0' rt1' rt2' ra0' ra1' ra2' ra3' ra4' ra5' ra6' ra7'
             rt3' rt4' rt5' rt6' ltac:(lia) Hi1 Hg Hno1 HC').
  - intros lyc' Sc' Wc' mr' mdc' x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 HC'.
    exact (cm_stage_exit pos lyc' Sc' Wc' mr' mdc' x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 HC').
Qed.

(* range_addressable (the core's reader form) of a sub-range of our frame, from ctrl's addressable. *)
Lemma cm_range_addr : forall pos lyc Sc Wc mr mdc o n, cmCut pos lyc Sc Wc mr mdc ->
  FRp pos <= o -> o + n <= FRp pos + 256 -> 0 <= n ->
  A.AsanRT.addressable mr o n ->
  lib.Reusable.YG0v.range_addressable (aview tfibsegs (w_H Wc) mr) lib.Reusable.YG0f.SHADOW_OFF o n.
Proof.
  intros pos lyc Sc Wc mr mdc o n HC Hlo Hhi Hn AD.
  pose proof HC as (_ & _ & _ & _ & _).
  destruct (cm_cut_base pos lyc Sc Wc mr mdc HC) as (_ & _ & _ & _ & BB & _).
  pose proof BB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FP0 & _).
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & _ & _ & _) & _).
  destruct (cm_frame_facts pos lyc Sc Wc mr mdc HC) as (_ & HFsh & _).
  destruct (cm_fs2 FS pos) as (E1 & _ & _).
  assert (HFR64 : FRp pos mod 64 = 0) by (rewrite E1; clear - P2; Z.div_mod_to_equations; lia).
  intros x Hx.
  destruct (proj2 (proj2 (proj2 AD)) (x - o) ltac:(lia)) as (Happ & b & Hb & Hok).
  replace (o + (x - o)) with x in Happ, Hb, Hok by lia.
  exists (bv_unsigned b).
  assert (Esh : lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x = A.AsanRT.shadow_addr x)
    by (unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr,
          A.AsanRT.ASAN_K; lia).
  assert (Exs : A.AsanRT.shadow_addr x = A.AsanRT.shadow_addr (FRp pos) + (x - FRp pos) / 8).
  { clear - HFR64. unfold A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hix : 0 <= (x - FRp pos) / 8 < 32) by (clear - Hx Hlo Hhi; Z.div_mod_to_equations; lia).
  destruct (HFsh ((x - FRp pos) / 8) Hix) as ((Hh & _) & _). rewrite <- Exs in Hh.
  split.
  - rewrite Esh, (cm_aview_vis_mrd Wc _ _ Hh).
    change (lib.Lib.Mem.wa (A.AsanRT.shadow_addr x)) with (Z_to_bv 64 (A.AsanRT.shadow_addr x)) in Hb.
    rewrite Hb. reflexivity.
  - destruct Hok as [Hz|(Hlt & Hle)].
    + left. rewrite (cm_signed_small b ltac:(lia)). exact Hz.
    + right. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm8.
      rewrite (cm_signed_small b ltac:(lia)). lia.
Qed.

Lemma cm_pc_parse : Z_to_bv 64 0x83578 = lib.Reusable.YG0d.w64 C_reac_ctrl_parse.A_reac_ctrl_parseP.
Proof. unfold lib.Reusable.YG0d.w64. f_equal; vm_compute; reflexivity. Qed.

Lemma cm_retok_parse : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x84688).
Proof. vm_compute. reflexivity. Qed.

(* The registers at reac_ctrl_parse's entry 0x83578 (ra = 0x84688): a0 = f, a1 = len, a2 = F + 32. *)
Definition cmPR (pos : Z) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
  lib.Lib.Frame.mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 (reac_box_catalogue_match.CA SP)) (cm_rg regs 3) (cm_rg regs 4)
      t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (FRp pos + 32)) a3 a4 a5 a6 a7
      (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa A.AsanRT.ASAN_K)
      (Z_to_bv 64 (A.AsanRT.shadow_addr (FRp pos))) (Z_to_bv 64 (FRp pos))
      (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) t3 t4 t5 t6.

(* The end of the S3 lift: the loop head of row 0 (the gate holds), or the exit cut. *)
Definition cmP3 (pos : Z) (mb : word -> option byte) : machine_state -> Prop :=
  fun s =>
    (exists (mc : word -> option byte) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
       s = cmLHst 0 pos mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 /\
       lib.Prog.RcMatch.cm_gate len fb = true /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc) \/
    (exists (mc : word -> option byte) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
       s = cmXCst pos mc x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc).

(* The parse stage: reac_ctrl_parse (TPARSE) at f, len, o = F + 32, then the S3 lift (footprint the frame shadow
   bytes 4 .. 8) into the loop (cm_rows, row 0) or the exit (cm_stage_exit). The header bytes and 50 <= len are the
   facts the S2 stretch established before the call (its gate, 0x8462c .. 0x84680). *)
Lemma cm_stage_parse : forall pos lyc Sc Wc mr mdc (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  50 <= len -> lib.Prog.RcParse.cp_v fb 12 = 0x88 -> lib.Prog.RcParse.cp_v fb 13 = 0x19 ->
  lib.Prog.RcParse.cp_v fb 16 = 0xcd -> lib.Prog.RcParse.cp_v fb 17 = 0xea ->
  cmCut pos lyc Sc Wc mr mdc -> A.AsanRT.addressable mr (FRp pos + 32) 36 ->
  SRr tfibsegs Wc (mkCfg (lib.Lib.MState.MS (cmPR pos t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6) fp_regs
                            (Z_to_bv 64 0x83578) fp_csr None mr (seg_rom tfibsegs)) mdc)
    (treac_box_catalogue_match_post regs ly S0 W mem md len fb).
Proof.
  intros pos lyc Sc Wc mr mdc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 H50 Hh12 Hh13 Hh16 Hh17 HC ADp.
  pose proof HC as (J & Eab & Hpos & HSAV & HFW).
  destruct (cm_cut_base pos lyc Sc Wc mr mdc HC) as (EF & Hin & HRm & HAR & BB & INV).
  destruct (cm_frame_facts pos lyc Sc Wc mr mdc HC) as (HFb & HFsh & EFA & EB2 & HFlo & HFhi & _).
  pose proof BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP &
    HMEMCMP & HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & Pstk) & _ & _ & _ & HFSlo & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold A.AsanRT.APPMEM_END in HAE'. unfold A.AsanRT.HIGHMEM_BEG in HHM'.
  destruct (cm_CA SP) as (HCA32 & HCAlo & HCAhi).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & _ & _ & _ & _ & G7).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  destruct (cm_fs2 FS pos) as (E1 & _ & E3).
  pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
  pose proof J as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _). unfold CM_STK in Hslo.
  assert (Hac : lib.Reusable.YM05.alloc_ceiling <= SP - 9136) by (clear - Hceil Hslo; lia).
  unfold A.Prog.asan_stack_malloc_c.FS_SIZE in HFSlo, P4.
  assert (HFR64 : FRp pos mod 64 = 0) by (rewrite E1; clear - P2; Z.div_mod_to_equations; lia).
  set (sF := A.AsanRT.shadow_addr (FRp pos)).
  set (RP := cmPR pos t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  assert (Esp : spZ RP = reac_box_catalogue_match.CA SP).
  { change (spZ RP) with (bv_unsigned (Z_to_bv 64 (reac_box_catalogue_match.CA SP))). apply cm_u64. lia. }
  assert (Hra1 : lib.Reusable.YK11.getr RP 1 = Z_to_bv 64 0x84688) by reflexivity.
  assert (HRO1 : arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H Wc) mr)).
  { apply cm_arodataS.
    exact (arodata_ok_journalP tfibsegs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J (cm_arodataP _ HRO0)). }
  destruct (HBLK H50) as (Hb0 & Hreq).
  assert (Hb : In (f, Lf) (ablocks B lyc Sc)) by (rewrite Eab; exact Hb0).
  rewrite cm_pc_parse.
  eapply SRr_bind.
  { refine (TPARSE CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 RP f len (FRp pos + 32) fb
              J HRO1 _ _ Hgp0 Htp0 eq_refl eq_refl eq_refl Rlen _ _ _ _ _ _ _ Hfb _).
    - rewrite Hra1. exact cm_retok_parse.
    - unfold raZ. rewrite Hra1, cm_u64 by lia. lia.
    - rewrite Esp. Z.div_mod_to_equations. lia.
    - rewrite Esp. unfold CM_STK, C_reac_ctrl_parse.REAC_CTRL_PARSE_STK. lia.
    - rewrite Esp. lia.
    - rewrite Hfrs. change (count_cid 1 ((2, pos) :: frames S0)) with (count_cid 1 (frames S0)). exact HC1.
    - intros _. exists Lf. split; [exact Hb | exact Hreq].
    - intros _. split; [|split].
      + exists 2, pos. split; [exact Hin|]. split; [lia|]. rewrite EFA, EB2.
        split; [clear - HFR64; Z.div_mod_to_equations; lia|]. split; lia.
      + clear - HFR64. Z.div_mod_to_equations. lia.
      + apply (cm_range_addr pos lyc Sc Wc mr mdc); [exact HC | lia | lia | lia | exact ADp].
    - intros _ a Ha. right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB2. lia.
    - intros _ i Hi. exact (cm_rec_view ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 SP f fb Lf J Hb0 Hb Hreq Hfb
                              (HG H50) i Hi). }
  (* the return of reac_ctrl_parse *)
  intros W2 c2 Hle2 (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & HP2 & Hfr2 & Hab2 & Hff & Ha0 & Hbuf & HK2).
  subst c2. rewrite Esp in HK2.
  destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (cm_frame_facts_J pos ly2 S2 W2 mem2 md2 J2 Hpos) as (HFb2 & HFsh2 & _).
  assert (HCt2 : cmCut pos ly2 S2 W2 mem2 md2).
  { split; [exact J2|]. split; [rewrite Hab2; exact Eab|]. split; [exact Hpos|]. split.
    - apply (cm_rw_of_view2 Wc W2 mr mem2 (SP - 96) (cm_saves regs)); [|exact HSAV].
      assert (Csz : Z.of_nat (lib.Lib.Cells.cells_size (cm_saves regs)) = 96) by reflexivity.
      intros a Ha. rewrite Csz in Ha.
      assert (Ka : lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64) by (clear - Hac RS Ha; lia).
      assert (Na : ~ (reac_box_catalogue_match.CA SP - C_reac_ctrl_parse.REAC_CTRL_PARSE_STK <= a <
                      reac_box_catalogue_match.CA SP)) by lia.
      pose proof (Hpres a ltac:(unfold CM_STK; lia)) as Hp1.
      split; [exact (K1 a Ka Na)|]. split; [exact (proj1 Hp1)|]. exact (K5 a Ka Na Hp1).
    - apply (cm_bytes_of_view2 Wc W2 mr mem2 (FRp pos + 248) _); [|exact HFW].
      intros j Hj. rewrite lib.Lib.Mem.length_le8 in Hj.
      split; [|split].
      + apply (K4 2 pos); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, EB2; lia |
                           cbv beta; lia].
      + exact (proj1 (proj1 (HFb (FRp pos + 248 + Z.of_nat j) ltac:(lia)))).
      + exact (proj1 (proj1 (HFb2 (FRp pos + 248 + Z.of_nat j) ltac:(lia)))). }
  clear HSAV HFW.
  destruct (cm_cut_base pos ly2 S2 W2 mem2 md2 HCt2) as (_ & Hin2 & HRm2 & HAR2 & BB2 & INV2).
  pose proof BB2 as (RS2 & S162 & HK2' & HHM2 & HAE2 & ST2 & _ & _ & _ & _ & _ & SR2 & AW2 & _ & _ & _ & _ & _ & _ &
    _ & FP02 & _).
  set (mb := A.MemNorm.normalize A.Img0.rsegs mem2).
  (* the registers at the return, in the stretch's shape *)
  set (R3reg := lib.Lib.Frame.mkR (reg_get regs2 (Z_to_bv 5 1)) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (cm_rg regs 3) (cm_rg regs 4) (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
         (reg_get regs2 (Z_to_bv 5 7)) (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (Z_to_bv 64 (fst (lib.Prog.RcParse.ctrlparse len fb)))
         (reg_get regs2 (Z_to_bv 5 11)) (reg_get regs2 (Z_to_bv 5 12)) (reg_get regs2 (Z_to_bv 5 13))
         (reg_get regs2 (Z_to_bv 5 14)) (reg_get regs2 (Z_to_bv 5 15)) (reg_get regs2 (Z_to_bv 5 16))
         (reg_get regs2 (Z_to_bv 5 17))
         (Z_to_bv 64 (FRp pos)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa A.AsanRT.ASAN_K)
         (Z_to_bv 64 sF) (Z_to_bv 64 (FRp pos)) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27)
         (reg_get regs2 (Z_to_bv 5 28)) (reg_get regs2 (Z_to_bv 5 29)) (reg_get regs2 (Z_to_bv 5 30))
         (reg_get regs2 (Z_to_bv 5 31))).
  assert (EQV : lib.Lib.Regs6ss.xregs_eqv regs2 R3reg).
  { unfold R3reg. apply lib.Lib.Regs6ss.mkR_eqv_of;
      first [ reflexivity
            | match goal with |- reg_get ?RR ?r = _ =>
                let k := eval vm_compute in (bv_unsigned r) in
                (transitivity (reg_get RR (Z_to_bv 5 k)); [reflexivity|]);
                first [ (rewrite (cm_pres_get _ _ k HP2 ltac:(unfold acallee_saved; lia)); reflexivity)
                      | (transitivity (lib.Reusable.YK11.getr RR 10); [reflexivity | rewrite Ha0; reflexivity]) ]
              end ]. }
  change (mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr RP 1) mem2 (seg_rom tfibsegs)) md2)
    with (mkCfg (lib.Lib.MState.MS regs2 fp_regs (Z_to_bv 64 0x84688) fp_csr None mem2 (seg_rom tfibsegs)) md2).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv tfibsegs W2 R3reg regs2 fp_regs (Z_to_bv 64 0x84688) fp_csr None mem2
           (seg_rom tfibsegs) md2 _); [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ EQV)].
  (* lift: S3 *)
  assert (VS : A.ProgBridge.range_visible (w_H W2) sF 32).
  { split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; assert (0 <= FRp pos / 8) by (apply Z.div_pos; lia); lia|].
    split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            assert (FRp pos / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia); lia|].
    intros a Ha. replace a with (sF + (a - sF)) by lia. exact (proj1 (proj1 (HFsh2 (a - sF) ltac:(lia)))). }
  set (R3 := [(sF, sF + 32)]).
  set (RNG3 := A.ProgBridge.RNG_W (cm_Hk (w_H W2) R3)).
  assert (R3sh : lib.Lib.ExecF.rng RNG3 (A.AsanRT.shadow_addr (FRp pos) + 4) 5).
  { fold sF. apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ sF 32); [exact VS | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R3 sF (sF + 32)); [left; reflexivity | lia]. }
  set (PP3 := cmP3 pos mb).
  assert (LHF : reac_box_catalogue_match_F3.cmLHF_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                  (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                  (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                  mb f len SP FS fb RNG3 0 PP3 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1).
  { intros mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hg _ INV'.
    apply lib.Lib.ExecF.evtF_done. unfold PP3, cmP3. left.
    exists mc, rra, rt0, rt1, rt2, ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, rt3, rt4, rt5, rt6.
    split; [reflexivity|]. split; [exact Hg | exact INV']. }
  assert (XCF : reac_box_catalogue_match_F3.cmXCF_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                  (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                  (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                  mb f len SP FS fb RNG3 PP3 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1).
  { intros mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Hr INV'.
    apply lib.Lib.ExecF.evtF_done. unfold PP3, cmP3. right.
    exists mc, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z4, z5, z8, z9, z10, u3, u4, u5, u6.
    split; [subst r; reflexivity | exact INV']. }
  apply (cm_lift_base W2 R3reg fp_regs (Z_to_bv 64 0x84688) fp_csr mem2 md2 R3 PP3 _ HRm2).
  { exact (reac_box_catalogue_match_F3.cm_parse_S3_rb_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
             (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
             (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
             mb f len SP FS fb Rf Rlen RS2 S162 HK2' ST2 Hfb SR2 HHM2 HAE2 AW2 FP02 RNG3 PP3 (FRp pos)
             (reac_box_catalogue_match.CA SP) pos 1 LHF XCF R3sh
             (reg_get regs2 (Z_to_bv 5 1)) (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
             (reg_get regs2 (Z_to_bv 5 7)) (reg_get regs2 (Z_to_bv 5 11)) (reg_get regs2 (Z_to_bv 5 12))
             (reg_get regs2 (Z_to_bv 5 13)) (reg_get regs2 (Z_to_bv 5 14)) (reg_get regs2 (Z_to_bv 5 15))
             (reg_get regs2 (Z_to_bv 5 16)) (reg_get regs2 (Z_to_bv 5 17)) (reg_get regs2 (Z_to_bv 5 28))
             (reg_get regs2 (Z_to_bv 5 29)) (reg_get regs2 (Z_to_bv 5 30)) (reg_get regs2 (Z_to_bv 5 31))
             H50 Hh12 Hh13 Hh16 Hh17 INV2). }
  (* after S3 *)
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem2 HRm2) as REL0. fold mb in REL0.
  assert (INC : forall a, cm_inR R3 a = true -> ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) a ->
                  ~ lib.Lib.Frame.outside R3 a) by (intros a Hr _; exact (cm_inR_not_outside R3 a Hr)).
  assert (HWR3 : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside R3 a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B ly2 S2) ly2 [(2, pos)] a).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & Hr & Hra).
    unfold R3 in Hr. destruct Hr as [<-|[]]; cbn [fst snd] in Hra.
    destruct (cm_frame_facts pos ly2 S2 W2 mem2 md2 HCt2) as (_ & _ & EFA2 & _).
    right. right. right. exists 2, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA2, EB28, <- G7. fold sF. lia. }
  intros ms3 s3 md3 HP3 Hrel3 Hsame3 Hfs3 Hkeep3 Hsbm3.
  unfold PP3, cmP3 in HP3.
  destruct HP3 as [(mc & rra & rt0 & rt1 & rt2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & rt3 & rt4 & rt5 & rt6 &
                    Es3 & Hg & INV3) |
                   (mc & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & z5 & z8 & z9 & z10 & u3 & u4 &
                    u5 & u6 & Es3 & INV3)];
    subst s3; [unfold cmLHst in Hrel3 | unfold cmXCst in Hrel3];
    destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel3) as (Ems3 & REL3);
    pose proof INV3 as (_ & MU3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAV3 & FW3);
    pose proof (A.MemNorm.munch_rel A.Img0.rsegs _ mem2 mb (ms_mem ms3) mc REL0 REL3 Hsame3 MU3) as MUa;
    pose proof (cm_munch_of_keep W2 _ _ R3 mem2 (ms_mem ms3) Hkeep3 MUa INC (cm_aWc_noseg SP FS HHM P3)) as MU3';
    (match type of Hfs3 with lib.Reusable.YK04R.fsteps _ _ ?st0 _ =>
       pose proof (AJF LAWS ctrl_wx CM_STK SP [] ly S0 W mem md [(2, pos)] ly2 S2 W2 st0 ms3 md2 md3 0 _ _ J2 Hfs3
                     (cm_fp_avoids_Hk (w_H W2) _) MU3' Hsbm3 HWR3) as J3
     end);
    (assert (HC3 : cmCut pos ly2 S2 W2 (ms_mem ms3) md3);
     [ split; [exact J3|]; split; [rewrite Hab2; exact Eab|]; split; [exact Hpos|]; split;
       [ exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ REL3 SAV3)
       | exact (proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs _ _ _ _ REL3) (FW3 eq_refl)) ] |]);
    rewrite Ems3.
  - exact (cm_rows 11 0 pos ly2 S2 W2 (ms_mem ms3) md3 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
             eq_refl ltac:(lia) Hg ltac:(intros j Hj; lia) HC3).
  - exact (cm_stage_exit pos ly2 S2 W2 (ms_mem ms3) md3 x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 HC3).
Qed.

(* ---- the S2 stage: from the return of __asan_stack_malloc_2 (0x84508) to reac_ctrl_parse's entry or the exit ---- *)

(* The record's bytes and their shadow bytes (cm_gate_F's reads) lie outside aWc. *)
Lemma cm_rec_out2 : forall a,
  0 <= f -> f + 50 <= lib.Reusable.YM05.alloc_ceiling ->
  (f + 50 <= A.AsanRT.LOWMEM_END \/ A.AsanRT.HIGHMEM_BEG <= f) ->
  (f + 50 <= FS \/ FS + 11571200 <= f) ->
  FS mod 4096 = 0 -> 0 < FS -> FS + 11571200 <= SP - 9136 ->
  (forall b, FS <= b < FS + 11571200 -> A.AsanRT.app_mem b) ->
  lib.Reusable.YM05.alloc_ceiling <= SP - 9136 -> A.AsanRT.HIGHMEM_BEG <= SP - 9136 -> SP <= A.AsanRT.APPMEM_END ->
  (f <= a < f + 50 \/ A.AsanRT.shadow_addr f <= a < A.AsanRT.shadow_addr (f + 49) + 1) ->
  lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) a.
Proof.
  intros a H0 Hac Happ HBF HF64 HF0 HFS HPF HacSP HHM HAE Ha.
  destruct (cm_outside_dec (reac_box_catalogue_match.aWc SP FS) a) as [Ho|Hin]; [exact Ho|]. exfalso.
  pose proof lib.Reusable.YM05.alloc_ceiling_value as (Hmn & Hm4).
  assert (Hac64 : lib.Reusable.YM05.alloc_ceiling mod 64 = 0) by (clear - Hm4; Z.div_mod_to_equations; lia).
  assert (HFS64 : FS mod 64 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  pose proof (cm_sa_ge_lo f ltac:(lia)) as CL.
  pose proof (cm_cover_le (f + 49) lib.Reusable.YM05.alloc_ceiling ltac:(lia) Hac64) as CH.
  assert (CH' : A.AsanRT.shadow_addr (f + 49) + 1 <= A.AsanRT.shadow_addr lib.Reusable.YM05.alloc_ceiling).
  { assert (A.AsanRT.shadow_addr (f + 49) < 8 * (A.AsanRT.shadow_addr (f + 49) / 8) + 8)
      by (clear; Z.div_mod_to_equations; lia). lia. }
  pose proof (cm_sa_mono lib.Reusable.YM05.alloc_ceiling (SP - 9136) HacSP) as M1.
  pose proof (cm_sa_le_hi SP ltac:(unfold A.AsanRT.HIGHMEM_BEG in HHM; lia)) as M2.
  pose proof (cm_sa_le_hi lib.Reusable.YM05.alloc_ceiling ltac:(unfold A.AsanRT.APPMEM_END in *; lia)) as M3.
  pose proof (cm_sa_ge_lo (SP - 9136) ltac:(unfold A.AsanRT.HIGHMEM_BEG in HHM; lia)) as M4.
  destruct (cm_aWc_cases SP FS a Hin) as [Hw | [Hws | (d & Hd & Hda)]].
  - destruct Ha as [Ha|Ha]; unfold A.AsanRT.HIGHMEM_BEG in *; lia.
  - destruct Ha as [Ha|Ha]; unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG in *; lia.
  - pose proof (cm_sa_ge_lo FS ltac:(lia)) as M5.
    pose proof (cm_sa_le_hi (FS + 3182592) ltac:(unfold A.AsanRT.HIGHMEM_BEG in *; lia)) as M6.
    destruct (cm_fpw_in FS d Hd ltac:(lia)) as [(D1 & D2) | (D1 & D2)]; destruct Ha as [Ha|Ha].
    + lia.
    + pose proof (HPF a ltac:(lia)) as Ap. unfold A.AsanRT.app_mem in Ap.
      unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia.
    + unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG in *. lia.
    + destruct HBF as [HB|HB].
      * pose proof (cm_cover_le (f + 49) FS ltac:(lia) HFS64).
        assert (A.AsanRT.shadow_addr (f + 49) < 8 * (A.AsanRT.shadow_addr (f + 49) / 8) + 8)
          by (clear; Z.div_mod_to_equations; lia). lia.
      * pose proof (cm_sa_mono (FS + 3182592) f ltac:(lia)). lia.
Qed.

(* The end of the S2 lift: reac_ctrl_parse's entry (the gate passed) or the exit cut (the gate missed). *)
Definition cmP2 (pos : Z) (mb : word -> option byte) : machine_state -> Prop :=
  fun s =>
    (exists (mc : word -> option byte) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       s = lib.Lib.MState.MS (cmPR pos t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6) fp_regs (Z_to_bv 64 0x83578) fp_csr None
             mc (seg_rom tfibsegs) /\
       50 <= len /\ lib.Prog.RcParse.cp_v fb 12 = 0x88 /\ lib.Prog.RcParse.cp_v fb 13 = 0x19 /\
       lib.Prog.RcParse.cp_v fb 16 = 0xcd /\ lib.Prog.RcParse.cp_v fb 17 = 0xea /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc /\
       A.AsanRT.addressable mc (FRp pos + 32) 36) \/
    (exists (mc : word -> option byte) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
       s = cmXCst pos mc x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 /\
       reac_box_catalogue_match_on.cmInv_on (cm_rg regs 1) (cm_rg regs 4) (cm_rg regs 8) (cm_rg regs 9) (cm_rg regs 18)
         (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24)
         (cm_rg regs 25) (cm_rg regs 26) mb f len SP FS (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc).

(* The S2 stage: from the return of __asan_stack_malloc_2 (a0 = the class-2 frame) through S2 (cm_resume_rb_F,
   which includes the header stores, then cm_gate_F; one lift, footprint {window, frame, frame shadow} and, when
   50 <= len, the record and its shadow bytes) to reac_ctrl_parse's entry (cm_jal_parse_F; then cm_stage_parse) or,
   on a miss (cm_miss_F), to the exit cut (cm_stage_exit). *)
Lemma cm_stage_s2 : forall pos lyc Sc Wc mr mdc (rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  cmCut pos lyc Sc Wc mr mdc ->
  SRr tfibsegs Wc (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR rr (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      (cm_rg regs 3) (cm_rg regs 4) u0 u1 u2 (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
      (Z_to_bv 64 (FRp pos)) x1 x2 x3 x4 x5 x6 x7 (cm_rg regs 18) (Z_to_bv 64 f) (Z_to_bv 64 len)
      (lib.Lib.Mem.wa A.AsanRT.ASAN_K) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26)
      (cm_rg regs 27) u3 u4 u5 u6) fp_regs (Z_to_bv 64 0x84508) fp_csr None mr (seg_rom tfibsegs)) mdc)
    (treac_box_catalogue_match_post regs ly S0 W mem md len fb).
Proof.
  intros pos lyc Sc Wc mr mdc rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 HC.
  pose proof HC as (J & Eab & Hpos & HSAV & HFW).
  destruct (cm_cut_base pos lyc Sc Wc mr mdc HC) as (EF & Hin & HRm & HAR & BB & INV).
  destruct (cm_frame_facts pos lyc Sc Wc mr mdc HC) as (HFb & HFsh & EFA & EB2 & HFlo & HFhi & _).
  pose proof BB as (RS & S16 & HK & HHM & HAE & ST & Hwin & HF & HT & MI & AC & SR & AW & AFU & AT & HBCMP &
    HMEMCMP & HGOT & HCF254 & HCF255 & FP0 & TLS0).
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & Pstk) & _ & _ & _ & HFSlo & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold A.AsanRT.APPMEM_END in HAE'. unfold A.AsanRT.HIGHMEM_BEG in HHM'.
  destruct (cm_CA SP) as (HCA32 & HCAlo & HCAhi).
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & _ & _ & _ & _ & G7).
  assert (EB28 : lib.Reusable.YG00.fs_frame_bytes 2 / 8 = 32) by (rewrite EB2; reflexivity).
  destruct (cm_fs2 FS pos) as (E1 & _ & E3).
  pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _). unfold CM_STK in Hslo.
  assert (Hac : lib.Reusable.YM05.alloc_ceiling <= SP - 9136) by (clear - Hceil Hslo; lia).
  unfold A.Prog.asan_stack_malloc_c.FS_SIZE in HFSlo, P4.
  assert (HFR64 : FRp pos mod 64 = 0) by (rewrite E1; clear - P2; Z.div_mod_to_equations; lia).
  set (sF := A.AsanRT.shadow_addr (FRp pos)).
  set (mb := A.MemNorm.normalize A.Img0.rsegs mr).
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mr HRm) as REL0. fold mb in REL0.
  (* visibility *)
  assert (VF : A.ProgBridge.range_visible (w_H Wc) (FRp pos) 256).
  { apply (cm_vis_of_present _ mr); [lia | lia | intros a Ha; exact (proj1 (HFb a Ha))]. }
  assert (VS : A.ProgBridge.range_visible (w_H Wc) sF 32).
  { split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; assert (0 <= FRp pos / 8) by (apply Z.div_pos; lia); lia|].
    split; [unfold sF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            assert (FRp pos / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia); lia|].
    intros a Ha. replace a with (sF + (a - sF)) by lia. exact (proj1 (proj1 (HFsh (a - sF) ltac:(lia)))). }
  assert (VW : forall lo n, SP - 9136 <= lo -> lo + n <= SP -> A.ProgBridge.range_visible (w_H Wc) lo n).
  { intros lo n Hlo Hhi.
    exact (cm_win_vis SP ly S0 W mem md [(2, pos)] lyc Sc Wc mr mdc 0 lo n J ltac:(lia) ltac:(unfold CM_STK; lia)
             Hhi ltac:(lia)). }
  (* the footprint and the write set *)
  set (RR := if 50 <=? len then [(f, f + 50); (A.AsanRT.shadow_addr f, A.AsanRT.shadow_addr (f + 49) + 1)] else []).
  set (R2 := [(SP - 9136, SP); (FRp pos, FRp pos + 256); (sF, sF + 32)] ++ RR).
  set (WR2 := [(SP - 9136, SP); (FRp pos, FRp pos + 256); (sF, sF + 32)]).
  set (RNG2 := A.ProgBridge.RNG_W (cm_Hk (w_H Wc) R2)).
  assert (InW : forall lo hi, In (lo, hi) WR2 -> In (lo, hi) R2) by (intros lo hi H; apply in_or_app; left; exact H).
  assert (RWa : lib.Lib.ExecF.rng RNG2 (reac_box_catalogue_match.CA SP + 24) 8).
  { apply cm_rng_Hk; [|apply VW; lia].
    intros a Ha. apply (cm_inR_In R2 (SP - 9136) SP); [apply InW; left; reflexivity | lia]. }
  assert (RFr : lib.Lib.ExecF.rng RNG2 (FRp pos) 24).
  { apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ (FRp pos) 256); [exact VF | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R2 (FRp pos) (FRp pos + 256)); [apply InW; right; left; reflexivity | lia]. }
  assert (RSh : lib.Lib.ExecF.rng RNG2 sF 24).
  { apply cm_rng_Hk; [|apply (A.ProgBridge.range_visible_sub _ sF 32); [exact VS | lia | lia | lia]].
    intros a Ha. apply (cm_inR_In R2 sF (sF + 32)); [apply InW; right; right; left; reflexivity | lia]. }
  assert (Esh : A.Prog.asan_stack_malloc_c.fs_frame FS 2 pos / 8 + A.AsanRT.ASAN_K = sF) by reflexivity.
  (* the record ranges, when 50 <= len *)
  assert (RRec : 50 <= len -> lib.Lib.ExecF.rng RNG2 f 50 /\
                 lib.Lib.ExecF.rng RNG2 (f / 8 + A.AsanRT.ASAN_K) ((f + 49) / 8 - f / 8 + 1)).
  { intros H50. destruct (HBLK H50) as (Hb0 & Hreq).
    assert (Hb : In (f, Lf) (ablocks B lyc Sc)) by (rewrite Eab; exact Hb0).
    assert (E50 : (50 <=? len) = true) by (apply Z.leb_le; exact H50).
    assert (InR : forall lo hi, In (lo, hi) [(f, f + 50); (A.AsanRT.shadow_addr f, A.AsanRT.shadow_addr (f + 49) + 1)] ->
                    In (lo, hi) R2).
    { intros lo hi H. apply in_or_app. right. unfold RR. rewrite E50. exact H. }
    split.
    - apply cm_rng_Hk;
        [|exact (A.ProgWorldVisHeap.heap_vis B LAWS lyc Sc Wc mr mdc f Lf f 50 HAR Hb ltac:(lia) ltac:(lia))].
      intros a Ha. apply (cm_inR_In R2 f (f + 50)); [apply InR; left; reflexivity | lia].
    - destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS lyc Sc Wc mr mdc f Lf f 50 HAR Hb
                  ltac:(lia) ltac:(lia) ltac:(lia)) as [E0|V0]; [lia|].
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in V0.
      replace (f + 50 - 1) with (f + 49) in V0 by lia.
      replace (f / 8 + A.AsanRT.ASAN_K) with (A.AsanRT.shadow_addr f) by reflexivity.
      replace ((f + 49) / 8 - f / 8 + 1) with (A.AsanRT.shadow_addr (f + 49) + 1 - A.AsanRT.shadow_addr f)
        by (unfold A.AsanRT.shadow_addr; lia).
      apply cm_rng_Hk.
      + intros a Ha. apply (cm_inR_In R2 (A.AsanRT.shadow_addr f) (A.AsanRT.shadow_addr (f + 49) + 1));
          [apply InR; right; left; reflexivity | lia].
      + pose proof (cm_sa_mono f (f + 49) ltac:(lia)) as Mf.
        apply (A.ProgBridge.range_visible_sub _ (A.AsanRT.shadow_addr f / 8 * 8)
                 (A.AsanRT.shadow_addr (f + 49) / 8 * 8 + 8 - A.AsanRT.shadow_addr f / 8 * 8));
          [exact V0 | (clear - Mf; Z.div_mod_to_equations; lia) ..]. }
  (* the stretch run: S2's resume (with the header), the gate, then the parse jal or the miss *)
  set (PP2 := cmP2 pos mb).
  apply (cm_lift_base Wc _ fp_regs (Z_to_bv 64 0x84508) fp_csr mr mdc R2 PP2 _ HRm).
  { eapply lib.Lib.ExecF.evtF_cut.
    { refine (reac_box_catalogue_match_F2.cm_resume_rb_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                mb f len SP FS fb Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 RNG2 pos
                rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hpos RWa RFr _ INV).
      rewrite Esh. exact RSh. }
    intros s1 HK1.
    destruct HK1 as (mc1 & rra & rt0 & rt1 & rt2 & ra0 & ra1 & ra3 & ra4 & ra5 & ra6 & ra7 & rt3 & rt4 & rt5 & rt6 &
                     -> & INV1).
    eapply lib.Lib.ExecF.evtF_cut.
    { refine (reac_box_catalogue_match_F2.cm_gate_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                mb f len SP FS fb Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RNG2 (FRp pos)
                (reac_box_catalogue_match.CA SP) pos 1 mc1 rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
                (fun H => proj1 (RRec H)) (fun H => proj2 (RRec H)) _ INV1).
      exact RSh. }
    intros s2 [HPB | HMS].
    - destruct HPB as (mc2 & rra2 & rt0' & rt1' & rt2' & ra3' & ra4' & ra5' & ra6' & ra7' & rt3' & rt4' & rt5' & rt6' &
                       -> & H50 & H12 & H13 & H16 & H17 & INV2 & AD2).
      apply reac_box_catalogue_match_F2.cm_jal_parse_F.
      unfold PP2, cmP2. left.
      exists mc2, rt0', rt1', rt2', ra3', ra4', ra5', ra6', ra7', rt3', rt4', rt5', rt6'.
      split; [reflexivity|].
      exact (conj H50 (conj H12 (conj H13 (conj H16 (conj H17 (conj INV2 AD2)))))).
    - destruct HMS as (mc2 & rra2 & rt0' & rt1' & rt2' & ra0' & ra1' & ra2' & ra3' & ra4' & ra5' & ra6' & ra7' & rt3' &
                       rt4' & rt5' & rt6' & -> & Hw0 & INV2).
      eapply lib.Lib.ExecF.evtF_cut.
      { exact (reac_box_catalogue_match_F2.cm_miss_F_on (cm_rg regs 1) (cm_rg regs 3) (cm_rg regs 4) (cm_rg regs 8)
                 (cm_rg regs 9) (cm_rg regs 18) (cm_rg regs 19) (cm_rg regs 20) (cm_rg regs 21) (cm_rg regs 22)
                 (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25) (cm_rg regs 26) (cm_rg regs 27) fp_regs fp_csr
                 mb f len SP FS fb RNG2 (FRp pos) (reac_box_catalogue_match.CA SP) pos 1 mc2
                 rra2 rt0' rt1' rt2' ra0' ra1' ra2' ra3' ra4' ra5' ra6' ra7' rt3' rt4' rt5' rt6' Hw0 INV2). }
      intros s3 HX.
      destruct HX as (r & mc3 & x1' & u0' & u1' & u2' & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & z5 & z8 & z9 &
                      z10 & u3' & u4' & u5' & u6' & -> & Hr & INV3).
      subst r. apply lib.Lib.ExecF.evtF_done. unfold PP2, cmP2. right.
      exists mc3, x1', u0', u1', u2', y0, y1, y2, y3, y4, y5, y6, y7, z4, z5, z8, z9, z10, u3', u4', u5', u6'.
      split; [reflexivity | exact INV3]. }
  (* after S2 *)
  assert (INC : forall a, cm_inR R2 a = true -> ~ lib.Lib.Frame.outside (reac_box_catalogue_match.aWc SP FS) a ->
                  ~ lib.Lib.Frame.outside WR2 a).
  { intros a Hr Hx. unfold cm_inR in Hr. apply existsb_exists in Hr as ([lo hi] & Hin2 & Hlh).
    apply andb_prop in Hlh as [Hl Hh]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hh. cbn [fst snd] in Hl, Hh.
    unfold R2 in Hin2. apply in_app_or in Hin2 as [Hin2|Hin2].
    - exact (cm_in_not_outside WR2 lo hi a Hin2 (conj Hl Hh)).
    - exfalso. unfold RR in Hin2. destruct (Z.leb_spec 50 len) as [H50|H50]; [|destruct Hin2].
      destruct (HBLK H50) as (Hb0 & Hreq).
      assert (Hb : In (f, Lf) (ablocks B lyc Sc)) by (rewrite Eab; exact Hb0).
      destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc Wc mr mdc f Lf HAR Hb) as (_ & _ & Hceilb & Happb & _).
      pose proof (BLKFS LAWS lyc Sc Wc mr mdc f Lf HAR Hb) as HBF0. rewrite EF in HBF0.
      unfold lib.Reusable.YG0f.kFakeStackSize in HBF0.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happb. unfold ASAN_CEIL in Hceilb.
      assert (Hrec1 : f + 50 <= lib.Reusable.YM05.alloc_ceiling) by lia.
      assert (Happ' : f + 50 <= A.AsanRT.LOWMEM_END \/ A.AsanRT.HIGHMEM_BEG <= f).
      { unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG.
        destruct Happb as (_ & [Hl' | (Hh1 & Hh2)]); [left | right]; lia. }
      apply Hx. apply cm_rec_out2; [lia | exact Hrec1 | exact Happ' | lia | exact P2 | exact P1 | exact HFSlo |
                                    exact P4 | exact Hac | exact HHM | exact HAE |].
      destruct Hin2 as [E|[E|[]]]; injection E as <- <-; [left | right]; lia. }
  assert (HWR2 : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR2 a ->
     awr_byte CM_STK SP [] (ablocks B ly S0) (ablocks B lyc Sc) lyc [(2, pos)] a).
  { intros a Ha Hx. destruct (cm_not_outside _ _ Hx) as (r & Hr & Hra).
    unfold WR2 in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hra.
    - left. unfold CM_STK. lia.
    - right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB2. lia.
    - right. right. right. exists 2, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite EFA, EB28, <- G7. fold sF. lia. }
  intros ms2 s2 md2 HP2 Hrel2 Hsame2 Hfs2 Hkeep2 Hsbm2.
  unfold PP2, cmP2 in HP2.
  destruct HP2 as [(mc & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Es2 & H50 & H12 & H13 & H16 &
                    H17 & INV2 & AD2) |
                   (mc & x1' & u0' & u1' & u2' & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & z5 & z8 & z9 & z10 &
                    u3' & u4' & u5' & u6' & Es2 & INV2)];
    subst s2; [| unfold cmXCst in Hrel2];
    destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel2) as (Ems2 & REL2);
    pose proof INV2 as (_ & MU2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAV2 & FW2);
    pose proof (A.MemNorm.munch_rel A.Img0.rsegs _ mr mb (ms_mem ms2) mc REL0 REL2 Hsame2 MU2) as MUa;
    pose proof (cm_munch_of_keep Wc _ _ WR2 mr (ms_mem ms2) Hkeep2 MUa INC (cm_aWc_noseg SP FS HHM P3)) as MU2';
    (match type of Hfs2 with lib.Reusable.YK04R.fsteps _ _ ?st0 _ =>
       pose proof (AJF LAWS ctrl_wx CM_STK SP [] ly S0 W mem md [(2, pos)] lyc Sc Wc st0 ms2 mdc md2 0 _ _ J Hfs2
                     (cm_fp_avoids_Hk (w_H Wc) _) MU2' Hsbm2 HWR2) as J2
     end);
    (assert (HCs2 : cmCut pos lyc Sc Wc (ms_mem ms2) md2);
     [ split; [exact J2|]; split; [exact Eab|]; split; [exact Hpos|]; split;
       [ exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ REL2 SAV2)
       | exact (proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs _ _ _ _ REL2) (FW2 eq_refl)) ] |]);
    rewrite Ems2.
  - exact (cm_stage_parse pos lyc Sc Wc (ms_mem ms2) md2 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 H50 H12 H13 H16 H17 HCs2
             (cm_addressable_of_rel _ _ _ _ REL2 AD2)).
  - exact (cm_stage_exit pos lyc Sc Wc (ms_mem ms2) md2 x1' u0' u1' u2' y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3' u4'
             u5' u6' HCs2).
Qed.

(* ---- the whole walk ---- *)
Lemma cm_main : SRr tfibsegs W (cfg_at tfibsegs A_catalogue_matchP regs mem md)
  (treac_box_catalogue_match_post regs ly S0 W mem md len fb).
Proof.
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (S16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _). unfold CM_STK in Hslo.
  destruct (cm_CA SP) as (HCA32 & HCAlo & HCAhi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSPlo : 9136 <= SP) by lia.
  assert (HSPhi : SP < 2 ^ 64) by lia.
  apply (cm_S1 ly S0 W regs mem md ch f len Lf _ HPRE HRO0 H10 H11 Rf Rlen HBLK).
  intros mc model' J1 SAV1.
  assert (Esm : pc_stack_malloc (as_code B) 2 = 0x3d8bc).
  { rewrite <- (palf_sm2 B TLF). vm_compute. reflexivity. }
  assert (ECA : reac_box_catalogue_match_F1.CA SP = reac_box_catalogue_match.CA SP) by reflexivity.
  set (RT := cm_R1j regs SP f len).
  change (lib.Lib.MState.MS RT fp_regs (Z_to_bv 64 0x3d8bc) fp_csr None mc (seg_rom tfibsegs))
    with (lib.Reusable.YK11.mkst RT (Z_to_bv 64 0x3d8bc) mc (seg_rom tfibsegs)).
  rewrite <- Esm.
  assert (ESP : spZ RT = SP + (reac_box_catalogue_match.CA SP - SP)).
  { transitivity (bv_unsigned (Z_to_bv 64 (reac_box_catalogue_match.CA SP))); [reflexivity|].
    rewrite (cm_u64 (reac_box_catalogue_match.CA SP) ltac:(lia)). lia. }
  assert (Hretok : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x84508)) by (vm_compute; reflexivity).
  eapply SRr_bind.
  { exact (cm_sm2_at W RT mc CM_STK SP [] ly S0 W mem md [] ly S0 model' 0 (reac_box_catalogue_match.CA SP - SP)
             (Z_to_bv 64 0x84508) J1 ESP ltac:(clear - HCA32 S16; Z.div_mod_to_equations; lia) ltac:(lia)
             ltac:(unfold ESTACK, CM_STK; lia) Hgp Htp eq_refl Hretok HC2). }
  intros W2 c2 _ (EW & S2 & regs2 & mem2 & md2 & pos & Ec2 & J2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hfresh & Hnev2 & Hbb2 &
                  Hz & Hflag & HKp & J2' & Hsfs & HPREc & HAR2 & Hfpres & Hkept & Hwpres).
  subst W2 c2.
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ1 & _).
  unfold CM_STK in HpresJ1.
  assert (Hsp : spZ RT = reac_box_catalogue_match.CA SP) by (rewrite ESP; lia).
  pose proof (FSAS ctl_fs_geom LAWS ltac:(lia) ly S0 S2 W RT regs2 mc mem2 model' md2 pos (SP - 9136) 256 HPREc
                ltac:(lia) ltac:(rewrite Hsp; unfold ESTACK; lia)
                ltac:(intros a Ha; rewrite Hsp in Ha; apply HpresJ1; unfold ESTACK in Ha; lia)
                Hfrs2 Hfresh HAR2 Ha0 Hz Hflag Hwpres Hkept ltac:(split; [lia | vm_compute; discriminate])) as HFS.
  cbv zeta in HFS.
  change (Z.to_nat 2) with 2%nat in HFS.
  destruct HFS as (Hpos & _ & _ & Hfw & _).
  replace (A.Prog.asan_stack_malloc_c.fs_B 2) with 256 in Hfw by (vm_compute; reflexivity).
  replace (A.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 2 pos + 256 - 8)
    with (A.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 2 pos + 248) in Hfw by lia.
  pose proof (ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & G3 & _).
  change (Z.to_nat 2) with 2%nat in G3.
  assert (EFA0 : frame_addr ly 2 pos = FRp pos) by (unfold frame_addr; rewrite G3; reflexivity).
  destruct HKp as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (HCt : cmCut pos ly S2 W mem2 md2).
  { split; [exact J2|]. split; [exact Eab2|]. split; [exact Hpos|]. split; [|exact Hfw].
    apply (cm_rw_of_view2 W W mc mem2 (SP - 96) (cm_saves regs)); [|exact SAV1].
    assert (Csz : Z.of_nat (lib.Lib.Cells.cells_size (cm_saves regs)) = 96) by reflexivity.
    intros a Ha. rewrite Csz in Ha.
    assert (Ka : lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64) by (clear - Hceil Hslo Ha HSPhi; lia).
    assert (Na : ~ (SP + (reac_box_catalogue_match.CA SP - SP) - ESTACK <= a < SP + (reac_box_catalogue_match.CA SP - SP)))
      by (unfold ESTACK; lia).
    pose proof (HpresJ1 a ltac:(lia)) as Hp1.
    split; [exact (K1 a Ka Na)|]. split; [exact (proj1 Hp1)|]. exact (K5 a Ka Na Hp1). }
  set (R2reg := lib.Lib.Frame.mkR (reg_get regs2 (Z_to_bv 5 1)) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (cm_rg regs 3) (cm_rg regs 4) (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
         (reg_get regs2 (Z_to_bv 5 7)) (Z_to_bv 64 SP) (Z_to_bv 64 (reac_box_catalogue_match.CA SP))
         (Z_to_bv 64 (FRp pos))
         (reg_get regs2 (Z_to_bv 5 11)) (reg_get regs2 (Z_to_bv 5 12)) (reg_get regs2 (Z_to_bv 5 13))
         (reg_get regs2 (Z_to_bv 5 14)) (reg_get regs2 (Z_to_bv 5 15)) (reg_get regs2 (Z_to_bv 5 16))
         (reg_get regs2 (Z_to_bv 5 17)) (cm_rg regs 18) (Z_to_bv 64 f) (Z_to_bv 64 len)
         (lib.Lib.Mem.wa A.AsanRT.ASAN_K) (cm_rg regs 22) (cm_rg regs 23) (cm_rg regs 24) (cm_rg regs 25)
         (cm_rg regs 26) (cm_rg regs 27)
         (reg_get regs2 (Z_to_bv 5 28)) (reg_get regs2 (Z_to_bv 5 29)) (reg_get regs2 (Z_to_bv 5 30))
         (reg_get regs2 (Z_to_bv 5 31))).
  assert (EQV : lib.Lib.Regs6ss.xregs_eqv regs2 R2reg).
  { unfold R2reg. apply lib.Lib.Regs6ss.mkR_eqv_of;
      first [ reflexivity
            | match goal with |- reg_get ?RR ?r = _ =>
                let k := eval vm_compute in (bv_unsigned r) in
                (transitivity (reg_get RR (Z_to_bv 5 k)); [reflexivity|]);
                first [ (rewrite (cm_pres_get _ _ k HP2 ltac:(unfold acallee_saved; lia)); reflexivity)
                      | (transitivity (lib.Reusable.YK11.getr RR 10); [reflexivity | rewrite Ha0, EFA0; reflexivity]) ]
              end ]. }
  change (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x84508) mem2 (seg_rom tfibsegs)) md2)
    with (mkCfg (lib.Lib.MState.MS regs2 fp_regs (Z_to_bv 64 0x84508) fp_csr None mem2 (seg_rom tfibsegs)) md2).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv tfibsegs W R2reg regs2 fp_regs (Z_to_bv 64 0x84508) fp_csr None mem2
           (seg_rom tfibsegs) md2 _); [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ EQV)].
  exact (cm_stage_s2 pos ly S2 W mem2 md2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCt).
Qed.

End walk.

(* ==== The theorem ================================================================================================ *)
Theorem pb_reac_box_catalogue_match : treac_box_catalogue_match_spec.
Proof.
  intros ly S0 W regs mem md ch f len fb HPRE HRO H10 H11 Rf Rlen Hfb HBLK HG HTG HGL HIMG1 HIMG2 HTBL HC2 HC1 HC0
    Hnev Hlive.
  destruct (Z_le_gt_dec 50 len) as [H50|H50].
  - destruct (HBLK H50) as (Lf & Hin & Hreq).
    apply (cm_main ly S0 W regs mem md ch f len fb Lf); try assumption.
    intros _. exact (conj Hin Hreq).
  - apply (cm_main ly S0 W regs mem md ch f len fb 0); try assumption.
    intros H. lia.
Qed.

(* The Section hypotheses the theorem rests on (printed while they are still Section variables). *)
Print Assumptions pb_reac_box_catalogue_match.
End h.
End d.
End b.
Print Assumptions pb_reac_box_catalogue_match.
