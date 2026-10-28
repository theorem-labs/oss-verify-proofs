(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_fc_defs Sj_num_fc_rel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition fcb_at (E : fcbenv) (mb : mem) : fcbenv :=
  mkFcbEnv (q_ra E) (q_sp E) (q_gp E) (q_tp E) (q_s0 E) (q_s1 E) (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E)
           (q_A E) (q_FIRST E) (q_LAST E) (q_OUT E) (q_lo E) (q_spq E) (q_f E) (q_txt E) mb.
Lemma fcb_ok_at : forall E mb, fcb_ok E -> fcb_ok (fcb_at E mb).
Proof. intros E mb [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]. constructor; assumption. Qed.

Lemma aevt_frame_release : forall (RT : rt_sig) (PMc : Model -> Prop) (Σ Σ' : rts RT) (K : config -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> aevt RT PMc Σ' K ms -> aevt RT PMc Σ K ms.
Proof.
  intros RT PMc Σ Σ' K ms HA HM H T c Hc Hk. exact (H T c (ASTA_switch RT Σ Σ' PMc (eq ms) c Hc HA HM) Hk).
Qed.

Section FCTK.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variables (Σ0 Σ1 : rts RT).
  Variable E : fcbenv.
  Variable me : mem.
  Notation SP := (q_SP E).
  Notation S := (q_S E).
  Notation f := (q_f E).
  Notation lo := (q_lo E).
  Notation spq := (q_spq E).
  Notation OUT := (q_OUT E).
  Hypothesis OK : fcb_ok E.
  Hypothesis LOR : rt_sp0 RT Σ0 - STACK_WIN <= lo.
  Hypothesis EF : rt_frames RT Σ1 = (f, 4%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Collection TKH := AF OK LOR EF EL ES.

  Lemma tk_inF : In (f, 4%nat) (rt_frames RT Σ1).
  Proof using TKH. rewrite EF. left. reflexivity. Qed.

  Definition tk_wf (W : list (Z * Z)) : Prop :=
    Forall (fun r => (lo <= fst r /\ snd r <= SP) \/ (f <= fst r /\ snd r <= f + 1016) \/ (S <= fst r /\ snd r <= S + 127) \/ (OUT <= fst r /\ snd r <= OUT + 8)) W.

  Lemma tk_fpok : forall W, tk_wf W -> fp_ok RT Σ1 lo W.
  Proof using TKH.
    intros W H. unfold fp_ok. eapply Forall_impl; [| exact H]. intros [a b] Hr. cbn [fst snd] in *.
    pose proof OK as OK'. fcb_env OK'.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]].
    - left. lia.
    - right; right; left. exists f, 4%nat. split; [exact tk_inF|]. change (fs_size 4) with 1024. lia.
    - right; right; right. exists f, 4%nat. split; [exact tk_inF|]. unfold shad, SHB. change (fs_size 4) with 1024.
      replace (f + 1024) with (f + 128 * 8) by lia. rewrite Z.div_add by lia. lia.
    - left. lia.
  Qed.

  Lemma tk_wf_W : tk_wf (fcb_W E).
  Proof using TKH.
    unfold tk_wf, fcb_W. pose proof OK as OK'. fcb_env OK'. destruct FF as (F1 & F2 & F3). repeat constructor; cbn [fst snd]; lia.
  Qed.

  Lemma tk_wf_W2 : tk_wf [(spq + 64, spq + 72); (f, f + 32); (S, S + 76)].
  Proof using TKH. unfold tk_wf. pose proof OK as OK'. fcb_env OK'. destruct FF as (F1 & F2 & F3). repeat constructor; cbn [fst snd]; lia. Qed.

  Definition fc_mrel (mm : mem) : Prop :=
    wmono bsegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(OUT, OUT + 8)] me mm.

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
    { pose proof OK as OK'. fcb_env OK'. destruct SPL as [H|H]; [|]; pose proof (af_sp0_range RT AF Σ1 m1 HA) as R; rewrite ES in R; lia. }
    destruct (NA LS Ha) as [N1 N2]. change (fs_size 4) with 1024 in N1, N2. unfold shad, SHB in N2.
    replace (f + 1024) with (f + 128 * 8) in N2 by lia. rewrite Z.div_add in N2 by lia.
    split; [exact N1| lia].
  Qed.

  Lemma fc_mrel_munch : forall W (mb mm : mem), tk_wf W -> ART RT Σ1 mb -> fc_mrel mb -> munch W mb mm -> wmono bsegs mb mm -> fc_mrel mm.
  Proof using TKH.
    intros W mb mm HW HA [WM0 PR0] MU WM. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. destruct (tk_apart mb a HA Ha) as (A1 & A2 & A3). cbn [outside] in Hd. destruct Hd as [Hd _].
    clear MU. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [outside fst snd] in *. split; [| exact IH].
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; lia.
  Qed.

  Lemma fc_mrel_ex : forall (mb m' : mem) D N, ART RT Σ1 mb -> fc_mrel mb -> wmono bsegs mb m' ->
    rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq D N mb m' ->
    ((f <= D /\ D + N <= f + 1024) \/ (S <= D /\ D + N <= S + 128) \/ (lo <= D /\ D + N <= SP)) -> fc_mrel m'.
  Proof using TKH.
    intros mb m' D N HA [WM0 PR0] WM PR HD. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| pose proof OK as OK'; fcb_env OK'; lia].
    - destruct (tk_apart mb _ HA Ha) as (A1 & A2 & A3). destruct HD as [HD|[HD|HD]]; lia.
  Qed.

  Lemma fc_mrel_fp : forall (mb m' : mem) D N, ART RT Σ1 mb -> fc_mrel mb -> wmono bsegs mb m' ->
    rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spq [(D, D + N)] mb m' ->
    (f <= D /\ D + N <= f + 1024) -> fc_mrel m'.
  Proof using TKH.
    intros mb m' D N HA [WM0 PR0] WM PR HD. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| pose proof OK as OK'; fcb_env OK'; lia].
    - destruct (tk_apart mb _ HA Ha) as (A1 & A2 & A3). cbn [outside]. split; [lia| exact I].
  Qed.

  Definition fc_park (mm : mem) : Prop :=
    (exists jh, rw_cells bsegs mm (spq + 152) [CB (Z.to_nat (SP - 256 - spq)) jh]) /\
    rw_cells bsegs mm (SP + -104) (fcb_saved E) /\
    (exists h, rw_cells bsegs mm (f + 8) [CB 24 h]) /\
    wr_at bsegs mm S 128.

  Definition tk_wfp (W : list (Z * Z)) : Prop :=
    Forall (fun r => (lo <= fst r /\ snd r <= spq + 152) \/ (f <= fst r /\ snd r <= f + 8) \/ (f + 32 <= fst r /\ snd r <= f + 1016) \/ (S <= fst r /\ snd r <= S + 127)
                     \/ (OUT <= fst r /\ snd r <= OUT + 8)) W.

  Lemma tk_wfp_disj : forall W a n, tk_wfp W -> 0 <= n ->
    ((spq + 152 <= a /\ a + n <= SP) \/ (f + 8 <= a /\ a + n <= f + 32)) ->
    disjoint_from W a n.
  Proof using TKH.
    intros W a n HW N0 HA. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [disjoint_from fst snd] in *. split; [| exact IH].
    pose proof OK as OK'. fcb_env OK'. destruct FF as (F1 & F2 & F3). destruct OUTR as (O1 & O2 & O3). destruct SPQ as [SPQ _]. clear TSEP TXR FLR.
    destruct Hr as [Hr|[Hr|[Hr|[Hr|Hr]]]]; destruct HA as [HA|HA]; first [ clear FSH; lia | lia ].
  Qed.

  Lemma fc_park_munch : forall W (mb mm : mem), tk_wfp W -> fc_park mb -> munch W mb mm -> wmono bsegs mb mm -> fc_park mm.
  Proof using TKH.
    intros W mb mm HW ((jh & P2) & P3 & (h & P4) & P6) MU WM.
    pose proof OK as OK'. fcb_env OK'. destruct SPQ as [SPQ _].
    split; [exists jh; eapply rw_cells_transport; [exact P2| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    split; [eapply rw_cells_transport; [exact P3| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| unfold fcb_saved; cbn [cells_size csize Nat.add]; lia]]|].
    split; [exists h; eapply rw_cells_transport; [exact P4| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    exact (wr_at_transport bsegs mb mm _ _ P6 WM).
  Qed.

  Lemma tk_wfp_W : tk_wfp (fcb_W E).
  Proof using TKH.
    unfold tk_wfp, fcb_W. pose proof OK as OK'. fcb_env OK'. destruct FF as (F1 & F2 & F3). repeat constructor; cbn [fst snd]; lia.
  Qed.
End FCTK.
