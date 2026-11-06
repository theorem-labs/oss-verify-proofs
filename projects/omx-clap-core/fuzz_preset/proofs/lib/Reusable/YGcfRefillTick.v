(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfRefillTick.v (a working branch 6ffa5fd37e27, file sha256 dc3436c09eaa), the cf refill lane's tick step (a Theorem Labs lane refill-b2 head, on the round-3 cf layer d0377850faab of round6f); module paths changed only: 32 modules to this unit's lib/Reusable. No other edit; no image numeral is stated here. *)
(* Theorem Labs, 2026-10-30: the TICK transport of the cf refill walk,
   written once for both halves.
   YGcfInstRefill.refill_walk_cf (and MnRefillSeamcf.refill_case_cf) run refill_tree_cf from the TICKED entry state
   set_nev (st_nev S0 + 1) S0, while their premises (ARXq_cf, rpre_cf) and their leaf (rwalk_leaf_cf) are at S0.
   The tick changes st_nev only, and no part of the cf relation reads st_nev except Wf_cf's lower bounds, which
   YG02cf.WfP_cf_tick keeps.  So:
   - ARmcf_tick / ARcf_tick / xs_mapped_cf_tick / qloose_tick / ROOM_cf_tick: the state premises move to the ticked
     state (every field but amc_wf by conversion: set_nev changes one record field that the field does not read);
   - rwalk_leaf_cf_untick: a leaf stated at the ticked start state is the leaf at S0 (rwalk_leaf_cf reads its start
     state only through AOX_cf and length (st_secs ..)).
   EVENT-FREE: st_nev appears only in the tick itself.  rule 24: no function proved (kind: model-state transport). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG02cf YGcfRoomPre YGcfRmodel YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfInstBase YGcfInstRefill.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section b.
Variable segs : list Segment.
Variable B : asyms.

Local Notation tick S := (set_nev (st_nev S + 1) S).

Lemma ARmcf_tick : forall ly S Hp rd, ARmcf B ly S Hp rd -> ARmcf B ly (tick S) Hp rd.
Proof.
intros ly S Hp rd M.
destruct M as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi Mhp Mxs].
constructor; try assumption; try (destruct S; assumption).
exact (WfP_cf_tick _ 0 0 0 S Mwf).
Qed.

Lemma ARcf_tick : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> ARcf segs B ly (tick S) Hp W mem md.
Proof.
intros ly S Hp W mem md (M & L & BU & MW & HS).
refine (conj (ARmcf_tick ly S Hp _ M) _).
split; [destruct S; destruct L; constructor; assumption|]. split.
{ (* abudget_cf's hull term is the CfParams projection cf_hull, which does not reduce under the tick: cf_hull_frame *)
  destruct BU as (B1 & B2 & B3). split; [|split; [destruct S; exact B2 | exact B3]].
  unfold abudget_cf in *. rewrite (cf_hull_frame S (tick S)) by (destruct S; reflexivity). destruct S; exact B1. }
split; [exact MW|]. destruct S; exact HS.
Qed.

Lemma xs_mapped_cf_tick : forall ly S md, xs_mapped_cf ly S md -> xs_mapped_cf ly (tick S) md.
Proof. intros ly S md H. destruct S; exact H. Qed.

Lemma qloose_tick : forall S, qloose S -> qloose (tick S).
Proof. intros S H. destruct S; exact H. Qed.

Lemma ROOM_cf_tick : forall S, ROOM_cf S -> ROOM_cf (tick S).
Proof. intros S H. destruct S; exact H. Qed.
End b.

Section c.
Context {IM : AImg} {AG : AGImg}.
Variable B : asyms.

(* The leaf at the ticked start is the leaf at S0: rwalk_leaf_cf reads its start state only through AOX_cf and
   length (st_secs ..), and the tick changes neither. *)
Lemma rwalk_leaf_cf_untick : forall Hp ly S0 cl W regs mem md r W' c',
  rwalk_leaf_cf B Hp ly (set_nev (st_nev S0 + 1) S0) cl W regs mem md r W' c' ->
  rwalk_leaf_cf B Hp ly S0 cl W regs mem md r W' c'.
Proof. intros Hp ly S0 cl W regs mem md r W' c' H. destruct S0; exact H. Qed.
End c.
End a.
