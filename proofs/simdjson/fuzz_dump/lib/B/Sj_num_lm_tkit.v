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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_lm_pro Sj_num_lm_kit Sj_num_lm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section LMTK.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variables (Σ0 Σ1 : rts RT).
  Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880).
  Hypothesis ROOM : lo + LMB_STACK <= SP.
  Hypothesis TOP : SP + 16 <= USTACK_TOP.
  Hypothesis LOR : rt_sp0 RT Σ0 - STACK_WIN <= lo.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis SPQ : (d = 0 \/ d = 16) /\ spq = SP - 224 - d.
  Hypothesis NF : f mod 64 = 0 /\ 0x6cd000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo.
  Hypothesis X8 : X mod 8 = 0.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ g <= X /\ X + 504 <= g + fs_size kg - 8.
  Hypothesis XNUM : 0x6cd000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                    /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo.
  Hypothesis SEP : (X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                   /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                   /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880).

  Collection TKH := AF ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP.

  Lemma tk_inF : In (f, 5%nat) (rt_frames RT Σ1).
  Proof using TKH. rewrite EF. left. reflexivity. Qed.
  Lemma tk_inG : In (g, kg) (rt_frames RT Σ1).
  Proof using TKH. rewrite EF. right. exact (proj1 XG). Qed.

  Definition tk_wf (W : list (Z * Z)) : Prop :=
    Forall (fun r => (lo <= fst r /\ snd r <= SP) \/ (f <= fst r /\ snd r <= f + 2040) \/ (S <= fst r /\ snd r <= S + 255) \/ (X <= fst r /\ snd r <= X + 504)) W.

  Lemma tk_fpok : forall W, tk_wf W -> fp_ok RT Σ1 lo W.
  Proof using TKH.
    intros W H. unfold fp_ok. eapply Forall_impl; [| exact H]. intros [a b] Hr. cbn [fst snd] in *.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]].
    - left. unfold USTACK_TOP in *. lia.
    - right; right; left. exists f, 5%nat. split; [exact tk_inF|]. change (fs_size 5) with 2048. lia.
    - right; right; right. exists f, 5%nat. split; [exact tk_inF|]. unfold shad, SHB. change (fs_size 5) with 2048.
      replace (f + 2048) with (f + 256 * 8) by lia. rewrite Z.div_add by lia. lia.
    - right; right; left. exists g, kg. split; [exact tk_inG|]. lia.
  Qed.

  Lemma tk_wf_WL : tk_wf (lm_WL X spq f).
  Proof using TKH.
    unfold tk_wf, lm_WL, LMB_STACK, RT_STACK in *. destruct SPQ as [Hd Hs]. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6).
    repeat constructor; cbn [fst snd]; lia.
  Qed.

  Definition lm_mrel (mm : mem) : Prop :=
    wmono bsegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)] me mm.

  Lemma tk_apart : forall (m1 : mem) a, ART RT Σ1 m1 -> aclient (rt_live RT Σ0) (rt_frames RT Σ0) SP a ->
    (SP <= a \/ a < lo) /\ ~ (f <= a < f + 2048) /\ ~ (S <= a < S + 256).
  Proof using TKH.
    intros m1 a HA Ha.
    pose proof (newframe_apart RT AF Σ0 Σ1 m1 f 5%nat SP a HA EF EL ES) as NA.
    assert (HA' : aclient (rt_live RT Σ1) (rt_frames RT Σ1) SP a).
    { eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| lia]. }
    pose proof (aclient_split_c RT AF Σ1 m1 SP a HA HA') as SPL. rewrite ES in SPL.
    split; [destruct SPL; [left; assumption| right; lia]|].
    assert (LS : rt_sp0 RT Σ0 - STACK_WIN <= SP).
    { destruct SPL as [H|H]; [|]; pose proof (af_sp0_range RT AF Σ1 m1 HA) as R; rewrite ES in R; unfold LMB_STACK, RT_STACK in *; lia. }
    destruct (NA LS Ha) as [N1 N2]. change (fs_size 5) with 2048 in N1, N2. unfold shad, SHB in N2.
    replace (f + 2048) with (f + 256 * 8) in N2 by lia. rewrite Z.div_add in N2 by lia.
    split; [exact N1| lia].
  Qed.

  Lemma lm_mrel_munch : forall W (mb mm : mem), tk_wf W -> ART RT Σ1 mb -> lm_mrel mb -> munch W mb mm -> wmono bsegs mb mm -> lm_mrel mm.
  Proof using TKH.
    intros W mb mm HW HA [WM0 PR0] MU WM. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. destruct (tk_apart mb a HA Ha) as (A1 & A2 & A3). cbn [outside] in Hd. destruct Hd as [Hd _].
    clear MU. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [outside fst snd] in *. split; [| exact IH].
    unfold LMB_STACK, RT_STACK in *. destruct Hr as [Hr|[Hr|[Hr|Hr]]]; lia.
  Qed.

  Lemma lm_mrel_ex : forall (mb m' : mem) D N, ART RT Σ1 mb -> lm_mrel mb -> wmono bsegs mb m' ->
    rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq D N mb m' ->
    ((f <= D /\ D + N <= f + 2048) \/ (X <= D /\ D + N <= X + 504)) -> lm_mrel m'.
  Proof using TKH.
    intros mb m' D N HA [WM0 PR0] WM PR HD. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| rewrite EL; auto| rewrite EF; intros e He; right; exact He| destruct SPQ; lia].
    - destruct (tk_apart mb _ HA Ha) as (A1 & A2 & A3). cbn [outside] in Hd. destruct HD; lia.
  Qed.

  Lemma lm_mrel_free : forall (mb m' : mem), lm_mrel mb -> wmono bsegs mb m' ->
    rt_pres (rt_live RT Σ1) (rt_frames RT Σ0) spq mb m' -> lm_mrel m'.
  Proof using TKH.
    intros mb m' [WM0 PR0] WM PR. split; [exact (wmono_trans bsegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. intros a Ha _. apply PR.
    eapply aclient_mono; [exact Ha| rewrite EL; auto| auto| destruct SPQ; lia].
  Qed.

  Definition lm_park (mm : mem) : Prop :=
    (exists jh, rw_cells bsegs mm (spq + 120) [CB (Z.to_nat d) jh]) /\
    rw_cells bsegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
    (exists h, rw_cells bsegs mm f [CB 32 h]) /\
    (exists zbs, u8arr bsegs mm (f + 32) zbs /\ length zbs = 496%nat) /\
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)].

  Definition tk_wfp (W : list (Z * Z)) : Prop :=
    Forall (fun r => (spq - 80 <= fst r /\ snd r <= spq + 120) \/ (f + 528 <= fst r /\ snd r <= f + 2040) \/ (S + 67 <= fst r /\ snd r <= S + 255)
                     \/ (X <= fst r /\ snd r <= X + 504)) W.

  Lemma tk_wfp_disj : forall W a n, tk_wfp W -> 0 <= n ->
    ((spq + 120 <= a /\ a + n <= SP) \/ (f <= a /\ a + n <= f + 528) \/ (S <= a /\ a + n <= S + 67)) ->
    disjoint_from W a n.
  Proof using TKH.
    intros W a n HW N0 HA. induction HW as [|[wl wh] W' Hr HW' IH]; [exact I|]. cbn [disjoint_from fst snd] in *. split; [| exact IH].
    unfold LMB_STACK, RT_STACK in *. destruct SPQ as [Hd Hs]. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). destruct XNUM as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct SEP as (E1 & E2 & E3 & E4).
    assert (Hd' : 0 <= d <= 16) by lia. clear Hd.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]]; destruct HA as [HA|[HA|HA]];
      first [ clear N4 Q3 E1 E2 E3 E4; lia | clear Q3 E1 E2 E3 E4; lia | clear N4 Q3 E3 E4; lia | lia ].
  Qed.

  Lemma lm_park_munch : forall W (mb mm : mem), tk_wfp W -> lm_park mb -> munch W mb mm -> wmono bsegs mb mm -> lm_park mm.
  Proof using TKH.
    intros W mb mm HW ((jh & P2) & P3 & (h & P4) & (zbs & P5 & L5) & P6) MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LMB_STACK, RT_STACK in *. pose proof SPQ as [Hd Hs]. pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6).
    split; [exists jh; eapply rw_cells_transport; [exact P2| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    split; [eapply rw_cells_transport; [exact P3| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| unfold LM_SAVED; cbn [cells_size csize Nat.add]; lia]]|].
    split; [exists h; eapply rw_cells_transport; [exact P4| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]]|].
    split; [exists zbs; split; [eapply u8arr_transport; [exact P5| exact MU| exact WM| apply tk_wfp_disj; [exact HW| lia| rewrite L5; lia]]| exact L5]|].
    eapply rw_cells_transport; [exact P6| exact MU| exact WM| apply tk_wfp_disj; [exact HW| cbn; lia| cbn [cells_size csize Nat.add]; lia]].
  Qed.

  Lemma tk_wfp_WL : tk_wfp (lm_WL X spq f).
  Proof using TKH.
    unfold tk_wfp, lm_WL. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). repeat constructor; cbn [fst snd]; lia.
  Qed.
  Lemma tk_wf_WA : tk_wf [(spq, spq + 120); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)].
  Proof using TKH.
    unfold tk_wf, LMB_STACK, RT_STACK in *. destruct SPQ as [Hd Hs]. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6).
    repeat constructor; cbn [fst snd]; lia.
  Qed.
  Lemma tk_wf_W3 : tk_wf [(f, f + 8); (f / 8 + 2147450884, f / 8 + 2147450947)].
  Proof using TKH.
    unfold tk_wf. destruct NF as (N1 & N2 & N3 & N4 & N5 & N6). repeat constructor; cbn [fst snd]; lia.
  Qed.
End LMTK.
