(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_pro Sj_num_lm_kit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FCTK.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variables (Σ0 Σ1 : rts RT).
  Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (OUT lo d spq f : Z) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880).
  Hypothesis ROOM : lo + SPA_STACK <= SP.
  Hypothesis TOP : SP + 16 <= USTACK_TOP.
  Hypothesis LOR : rt_sp0 RT Σ0 - STACK_WIN <= lo.
  Hypothesis EF : rt_frames RT Σ1 = (f, 4%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis SPQ : (d = 0 \/ d = 16) /\ spq = SP - 192 - d.
  Hypothesis NF : f mod 64 = 0 /\ 0x6c2000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo.
  Hypothesis OUTR : OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP.

  Collection TKH := AF ROOM TOP LOR EF EL ES SPQ NF OUTR.

  Lemma tk_inF : In (f, 4%nat) (rt_frames RT Σ1).
  Proof using TKH. rewrite EF. left. reflexivity. Qed.

  Definition tk_wf (W : list (Z * Z)) : Prop :=
    Forall (fun r => (lo <= fst r /\ snd r <= SP) \/ (f <= fst r /\ snd r <= f + 1016) \/ (S <= fst r /\ snd r <= S + 127) \/ (OUT <= fst r /\ snd r <= OUT + 8)) W.

  Lemma tk_fpok : forall W, tk_wf W -> fp_ok RT Σ1 lo W.
  Proof using TKH.
    intros W H. unfold fp_ok. eapply Forall_impl; [| exact H]. intros [a b] Hr. cbn [fst snd] in *.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]].
    - left. unfold USTACK_TOP in *. lia.
    - right; right; left. exists f, 4%nat. split; [exact tk_inF|]. change (fs_size 4) with 1024. lia.
    - right; right; right. exists f, 4%nat. split; [exact tk_inF|]. unfold shad, SHB. change (fs_size 4) with 1024.
      replace (f + 1024) with (f + 128 * 8) by lia. rewrite Z.div_add by lia. lia.
    - left. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *. lia.
  Qed.

  Lemma tk_wf_W : tk_wf (fc_W lo spq f OUT).
  Proof using TKH.
    unfold tk_wf, fc_W, SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in *. destruct SPQ as [Hd Hs]. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6).
    repeat constructor; cbn [fst snd]; lia.
  Qed.
  Lemma tk_wf_W2 : tk_wf [(f, f + 32); (S, S + 92)].
  Proof using TKH. unfold tk_wf. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). repeat constructor; cbn [fst snd]; lia. Qed.
  Lemma tk_wf_WR : tk_wf [(f, f + 8); (f / 8 + 2147450956, f / 8 + 2147450965)].
  Proof using TKH. unfold tk_wf. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). repeat constructor; cbn [fst snd]; lia. Qed.

  Definition fc_mrel (mm : mem) : Prop :=
    wmono asegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(OUT, OUT + 8)] me mm.

  Lemma tk_apart : forall (m1 : mem) a, ART RT Σ1 m1 -> aclient (rt_live RT Σ0) (rt_frames RT Σ0) SP a ->
    (SP <= a \/ a < lo) /\ ~ (f <= a < f + 1024) /\ ~ (S <= a < S + 128).
  Proof using TKH.
    intros m1 a HA Ha.
    pose proof (newframe_apart RT AF Σ0 Σ1 m1 f 4%nat SP a HA EF EL ES) as NA.
    assert (HA' : aclient (rt_live RT Σ1) (rt_frames RT Σ1) SP a).
    { eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| lia]. }
    pose proof (aclient_split_c RT AF Σ1 m1 SP a HA HA') as SPL. rewrite ES in SPL.
    split; [destruct SPL; [left; assumption| right; lia]|].
    assert (LS : rt_sp0 RT Σ0 - STACK_WIN <= SP).
    { destruct SPL as [H|H]; [|]; pose proof (af_sp0_range RT AF Σ1 m1 HA) as R; rewrite ES in R; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in *; lia. }
    destruct (NA LS Ha) as [N1 N2]. change (fs_size 4) with 1024 in N1, N2. unfold shad, SHB in N2.
    replace (f + 1024) with (f + 128 * 8) in N2 by lia. rewrite Z.div_add in N2 by lia.
    split; [exact N1| lia].
  Qed.

  Lemma fc_mrel_munch : forall W (mb mm : mem), tk_wf W -> ART RT Σ1 mb -> fc_mrel mb -> munch W mb mm -> wmono asegs mb mm -> fc_mrel mm.
  Proof using TKH.
    intros W mb mm HW HA [WM0 PR0] MU WM. split; [exact (wmono_trans asegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. destruct (tk_apart mb a HA Ha) as (A1 & A2 & A3). cbn [outside] in Hd. destruct Hd as [Hd _].
    clear MU. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [outside fst snd] in *. split; [| exact IH].
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in *. destruct Hr as [Hr|[Hr|[Hr|Hr]]]; lia.
  Qed.

  Lemma fc_mrel_ex : forall (mb m' : mem) D N, ART RT Σ1 mb -> fc_mrel mb -> wmono asegs mb m' ->
    rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq D N mb m' ->
    ((f <= D /\ D + N <= f + 1024) \/ (S <= D /\ D + N <= S + 128)) -> fc_mrel m'.
  Proof using TKH.
    intros mb m' D N HA [WM0 PR0] WM PR HD. split; [exact (wmono_trans asegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| destruct SPQ; lia].
    - destruct (tk_apart mb _ HA Ha) as (A1 & A2 & A3). destruct HD as [HD|HD]; lia.
  Qed.

  Definition fc_park (mm : mem) : Prop :=
    (exists jh, rw_cells asegs mm (spq + 88) [CB (Z.to_nat d) jh]) /\
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
    (exists h, rw_cells asegs mm f [CB 32 h]) /\
    wr_at asegs mm S 128 /\
    wr_at asegs mm (f + 32) 504.

  Definition tk_wfp (W : list (Z * Z)) : Prop :=
    Forall (fun r => (lo <= fst r /\ snd r <= spq + 88) \/ (f + 32 <= fst r /\ snd r <= f + 1016) \/ (S <= fst r /\ snd r <= S + 127)
                     \/ (OUT <= fst r /\ snd r <= OUT + 8)) W.

  Lemma tk_wfp_disj : forall W a n, tk_wfp W -> 0 <= n ->
    ((spq + 88 <= a /\ a + n <= SP) \/ (f <= a /\ a + n <= f + 32)) ->
    disjoint_from W a n.
  Proof using TKH.
    intros W a n HW N0 HA. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [disjoint_from fst snd] in *. split; [| exact IH].
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in *. destruct SPQ as [Hd Hs]. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct OUTR as (O1 & O2 & O3).
    assert (Hd' : 0 <= d <= 16) by lia. clear Hd.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; destruct HA as [HA|HA]; first [ clear N4; lia | lia ].
  Qed.

  Lemma fc_park_munch : forall W (mb mm : mem), tk_wfp W -> fc_park mb -> munch W mb mm -> wmono asegs mb mm -> fc_park mm.
  Proof using TKH.
    intros W mb mm HW ((jh & P2) & P3 & (h & P4) & P6 & P7) MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in *. pose proof SPQ as [Hd Hs]. pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6).
    split; [exists jh; eapply rw_cells_transport; [exact P2| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    split; [eapply rw_cells_transport; [exact P3| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| unfold LM_SAVED; cbn [cells_size csize Nat.add]; lia]]|].
    split; [exists h; eapply rw_cells_transport; [exact P4| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    split; [exact (wr_at_transport asegs mb mm _ _ P6 WM)| exact (wr_at_transport asegs mb mm _ _ P7 WM)].
  Qed.

  Lemma tk_wfp_W : tk_wfp (fc_W lo spq f OUT).
  Proof using TKH.
    unfold tk_wfp, fc_W. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). repeat constructor; cbn [fst snd]; lia.
  Qed.
End FCTK.
