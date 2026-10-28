(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_sec_defs R_mmapordie RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_drain_istmt RT_drain_itemp RT_dsec_defs RT_dsec_nw RT_dsec_fkit RT_dsec_kit RT_dsec_geo RT_dsec_art RT_dsec_art2 RT_freeP_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition liveP (Σ : rtsA) (s : secst) (live0 : list (Z * Z)) : Prop :=
  forall p n, In (p, n) live0 ->
    (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg (l_SB (lay Σ)) c i n)
    \/ (exists t, In t (sec Σ) /\ t <> s /\ s_quar t = false /\ s_n t = n /\ p = s_ubeg t).

Lemma liveP_remove : forall Σ s, live_wf Σ -> liveP Σ s (live_remove (s_ubeg s) (live Σ)).
Proof.
  intros Σ s (_ & _ & V3 & _) p n Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
  destruct (V3 p n Hin) as [X|(t & Ht & Htq & Htn & Ep)]; [left; exact X | right].
  exists t. split; [exact Ht|]. split; [intros ->; exact (Hne Ep)|]. split; [exact Htq|]. split; [exact Htn | exact Ep].
Qed.

Section DsCliP.
Variables (Σ : rtsA) (W0 : list ivl) (k : nat) (s lst : secst) (TZ : list ivl) (zlo zhi : Z) (live0 : list (Z * Z)).
Hypothesis HG : geo_ok Σ.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hlst : In lst (sec Σ).
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW0 : Forall (dzoneP Σ [] [] [k] TZ IZ_S [] zlo zhi) W0.
Hypothesis Hlive : liveP Σ s live0.
#[local] Notation L := (lay Σ).

Lemma ds_clientP : forall x, aclient live0 (frames Σ) zhi x -> outside (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) x.
Proof using HG Hk Hlst HTZ Hzlo Hzlh HW0 Hlive.
  intros x Hx. apply outside_app; [|cbn [outside]; split; [|exact I]].
  - pose proof (dp_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    destruct Hx as [H|[H|[H|[H|H]]]].
    + apply (disjoint_outside W0 x 1); [|lia].
      apply (dp_stack_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo Hzlh W0 HW0); lia.
    + destruct H as ((lo0 & hi0 & Hin & Hlh) & Hnrt).
      assert (Hx : 0x16e760 <= x < 0x1705d8 \/ 0x696290 <= x < 0x6a6290 \/ 0x6a6290 <= x < 0x6c9858).
      { unfold CLIENT_STATIC in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply (disjoint_outside W0 x 1); [|lia].
      apply (dp_img Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0);
        [lia | unfold SEGTOP_A; lia|].
      unfold IZ_S, i_sec_mutex, i_sec_nres, i_sec_sorted, i_gstat_alloc, INST, g_instance. cbn [disjoint_from].
      repeat split; try exact I; lia.
    + destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W0 p n); [|lia].
      destruct (Hlive p n Hin) as [(c & i & Hc & Hn & ->)|(t & Ht & Hts & Htq & Htn & ->)].
      * pose proof (dp_slot_in Σ HG c i _ Hc Hn) as (S1 & S2 & S3 & S4 & S5 & S6).
        assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
        { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
          pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
          pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
        pose proof (fl_rz_facts n) as (R1 & R2).
        apply (dp_slot_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 c i (CkAlloc n));
          [exact Hc | exact Hn | intros [] | unfold p_ubeg; lia | unfold p_ubeg; lia].
      * destruct (In_nth_error _ _ Ht) as (kt & Hkt).
        pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
        pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
        apply (dp_secmap_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 kt t);
          [exact Hkt | | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Htn; lia].
        intros [E|[]]. subst kt. rewrite Hk in Hkt. injection Hkt as <-. exact (Hts eq_refl).
    + destruct H as (f & k0 & Hin & Hfx). apply (disjoint_outside W0 f (fs_size k0 - 8)); [|lia].
      destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      apply (dp_grant_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 5 (l_FSB L) 0xb09000);
        [reflexivity | lia | lia | lia].
    + destruct H as (f & k0 & Hin & Hfx). apply (disjoint_outside W0 (shad f) (shad (f + fs_size k0) - shad f)); [|lia].
      destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
      pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as A05. cbn [fst snd] in A05. unfold apart in A05.
      apply (dp_shad_app_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 f (f + fs_size k0));
        [lia | lia | lia | | lia | lia].
      intros k' s' Hk' _. pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
      pose proof (proj1 (Forall_forall _ _) SW4 s' (nth_error_In _ _ Hk')) as (_ & _ & _ & X & _). unfold apart in X. lia.
  -
    pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
    pose proof (proj1 (Forall_forall _ _) SW4 lst Hlst) as ((Ln1 & _) & (LG1 & _ & LG3 & LG4 & LG5) & LGP & LGF & _).
    pose proof (smsz_big (s_n lst) ltac:(lia)) as Lbig. unfold apart in LGP, LGF.
    pose proof (dp_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    destruct Hx as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
    + clear - Hs Hzlo Hzlh LG3 Lbig Ln1. lia.
    + destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hx LG5 Lbig Ln1; unfold SEGTOP_A in *; lia.
    + destruct Hl as (p & n & Hin & Hx). destruct (Hlive p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Hts & Htq & Htn & Ep)].
      * pose proof (dp_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
        assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
        { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
          pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
          pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
        pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx. clear - Hx S1 S2 G7 LGP Hfit R1 R2 Lbig Ln1. lia.
      * subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
        destruct (Z.eq_dec (s_mb t) (s_mb lst)) as [E|NE]; [clear - Hx E; lia|].
        destruct (In_nth_error _ _ Ht) as (jt & Hjt). destruct (In_nth_error _ _ Hlst) as (jl & Hjl).
        assert (Hne : jt <> jl) by (intros ->; rewrite Hjl in Hjt; injection Hjt as ->; exact (NE eq_refl)).
        pose proof (SW5 jt jl t lst Hjt Hjl Hne) as A. unfold apart in A.
        pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
        clear - Hx A Lbig Tbig Ln1 Tn1. lia.
    + destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3). clear - Hx Y1 Y2 Y3 LGF Lbig Ln1. lia.
    + destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
      pose proof (dp_shad_rng f ltac:(lia)) as X1. pose proof (dp_shad_rng (f + fs_size k0) ltac:(lia)) as X2.
      clear - Hx X1 X2 LG4 Lbig Ln1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

End DsCliP.

Lemma ds_client_mapP : forall Σ k s z a live0, geo_ok Σ -> liveP Σ s live0 -> nth_error (sec Σ) k = Some s ->
  l_ACEIL (lay Σ) <= z -> aclient live0 (frames Σ) z a ->
  ~ (s_mb s <= a < s_mb s + smsz (s_n s)) /\ (z <= a \/ a < l_ACEIL (lay Σ)).
Proof.
  intros Σ k s z a live0 HG Hlive Hk Hz Ha.
  pose proof (an_map Σ k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
  pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _). unfold apart in AF.
  destruct Ha as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
  - split; [clear - Hs Hz M2; lia | left; lia].
  - destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split; [clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia |
      clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia | clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia].
  - destruct Hl as (p & n & Hin & Hx). destruct (Hlive p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Hts & Htq & Htn & Ep)].
    + pose proof (dk_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
      assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
      { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
        pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
      pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx.
      split; [clear - Hx S1 S2 G7 M5 Hfit R1 R2; lia | right; clear - Hx S1 S2 G7 G4 Hfit R1 R2; lia].
    + subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
      destruct (In_nth_error _ _ Ht) as (jt & Hjt).
      pose proof (dk_map Σ HG _ t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & T9).
      pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
      destruct (Nat.eq_dec jt k) as [->|Hne].
      * rewrite Hk in Hjt. injection Hjt as <-. exfalso. exact (Hts eq_refl).
      * pose proof (T9 k s Hk (fun E => Hne (eq_sym E))) as A. unfold apart in A.
        split; [clear - Hx A Tbig Tn1; lia | right; clear - Hx T2 Tbig Tn1; lia].
  - destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
    pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
    split; [clear - Hx Y1 Y2 Y3 AF; lia | right; clear - Hx Y2 Y3 Q3; lia].
  - destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
    pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
    pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
    pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1. pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
    split; [clear - Hx X1 X2 M3; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | right; clear - Hx X2 G1; lia].
Qed.

End GWIN.
