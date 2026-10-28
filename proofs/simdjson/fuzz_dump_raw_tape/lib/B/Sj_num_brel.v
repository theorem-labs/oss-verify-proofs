(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_bkit Sj_num_bdefs Sj_num_abig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section BRel.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variables (Σ0 : rts RT) (SP lo X FS : Z) (me : mem).
  Hypothesis LOR : rt_sp0 RT Σ0 - STACK_WIN <= lo.
  Hypothesis FS0 : 0 <= FS.
  Hypothesis ROOMF : lo + FS <= SP.
  Hypothesis SPTOP : SP <= USTACK_TOP.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ f <= X /\ X + 504 <= f + fs_size c - 8.

  Definition b_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ rt_credit RT Σ0 - used <= rt_credit RT Σ.
  Definition b_mrel (mm : mem) : Prop :=
    wmono bsegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)] me mm.
  Notation W := [(SP - FS, SP); (X, X + 504)].

  Lemma b_srel_0 : b_srel Σ0 0.
  Proof. unfold b_srel. repeat split; lia. Qed.
  Lemma b_mrel_0 : b_mrel me.
  Proof. split; [apply wmono_refl| apply pres_fp_refl]. Qed.

  Lemma b_fpok : forall Σ used, b_srel Σ used -> fp_ok RT Σ lo W.
  Proof using LOR FS0 ROOMF SPTOP XFR.
    intros Σ used (EF & _).
    constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
    right; right; left. destruct XFR as (f & c & Hin & F1 & F2). exists f, c. rewrite EF. cbn [fst snd]. split; [exact Hin| lia].
  Qed.

  Lemma b_art : forall Σ used mb mm, b_srel Σ used -> ART RT Σ mb -> munch W mb mm -> wmono bsegs mb mm -> ART RT Σ mm.
  Proof using AF LOR FS0 ROOMF SPTOP XFR.
    intros Σ used mb mm SR HA MU WM. pose proof SR as (_ & _ & ES & _).
    exact (art_of_munch RT AF Σ mb mm lo W HA ltac:(rewrite ES; exact LOR) (b_fpok Σ used SR) MU WM).
  Qed.

  Lemma b_mrel_step : forall Σ used mb mm, b_srel Σ used -> ART RT Σ mb -> b_mrel mb -> munch W mb mm -> wmono bsegs mb mm -> b_mrel mm.
  Proof using AF LOR FS0 ROOMF SPTOP XFR.
    intros Σ used mb mm (EF & EL & ES & _) HA [WM0 PR0] MU WM. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. rewrite <- EL, <- EF in Ha. pose proof (aclient_split_c RT AF Σ mb _ a HA Ha) as SPL. rewrite ES in SPL.
    cbn [outside] in Hd |- *. destruct Hd as [Hd _].
    split; [lia|]. split; [exact Hd| exact I].
  Qed.

  Lemma b_mrel_ex : forall Σ used mb m' sp' d n, b_srel Σ used -> b_mrel mb -> wmono bsegs mb m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp' d n mb m' -> sp' <= SP -> X <= d -> d + n <= X + 504 -> b_mrel m'.
  Proof using.
    intros Σ used mb m' sp' d n (EF & EL & _) [WM0 PR0] WM PR HS D1 D2. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. rewrite EL, EF in PR. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| auto| auto| lia].
    - cbn [outside] in Hd. lia.
  Qed.

  Lemma b_mrel_fp : forall Σ used mb m' sp', b_srel Σ used -> b_mrel mb -> wmono bsegs mb m' ->
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp' [(X, X + 504)] mb m' -> sp' <= SP -> b_mrel m'.
  Proof using.
    intros Σ used mb m' sp' (EF & EL & _) [WM0 PR0] WM PR HS. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. rewrite EL, EF in PR. eapply pres_fp_sp; [exact PR| exact HS].
  Qed.

  Lemma b_bbig : forall Σ used mm bs len, b_srel Σ used -> X mod 8 = 0 ->
    u8arr bsegs mm X bs -> length bs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] -> 0 <= len <= 62 ->
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) -> bbig RT Σ mm X bs len.
  Proof using XFR.
    intros Σ used mm bs len (EF & _) X8 XA XL XN LEN ZR.
    pose proof (abig_intro RT Σ mm X bs len) as AI. unfold abig_raw in AI.
    assert (AB : abig RT Σ mm X) by (apply AI; repeat (split; [assumption|]); rewrite EF; exact XFR).
    destruct AB as (FO & _ & _). split; [exact FO|]. split; [exact XL|]. split; [exact XA|]. split; [exact XN| exact LEN].
  Qed.
End BRel.
