(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma stk_wmono : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells bsegs m a cs -> stk bsegs m a hi.
Proof.
  intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
  replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_wmono : forall (m m' : mem) a n, wr_at bsegs m a n -> wmono bsegs m m' -> wr_at bsegs m' a n.
Proof. intros m m' a n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W _ (H i Hi)). Qed.

Lemma u32arr_agree : forall (m m' : mem) a ws, u32arr bsegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> wmono bsegs m m' -> u32arr bsegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA W. split.
  - apply (bytes_at_agree bsegs m m' a _ Hb). rewrite u32s_length. intros x Hx. apply HA. lia.
  - exact (wr_at_wmono m m' _ _ Hw W).
Qed.

Definition in_rngs (l : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) l.

Definition consts_rngs (L : layoutA) : list (Z * Z) :=
  [ (i_spacebeg, i_spacebeg + 24); (i_premapped, i_premapped + 1);
    (0x17fea8, 0x17feb0); (0x17feb8, 0x17fec0); (0x219420, 0x219428); (0x21b538, 0x21b540); (0x21b5ac, 0x21b5ad);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x17fec8, 0x17fee8); (0x189978, 0x189980); (0x18a660, 0x18a678);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x21b59d, 0x21b59e); (0x21b5a4, 0x21b5a5); (0x17fec0, 0x17fec8); (0x17fef0, 0x17fef8);
    (0x181f38, 0x181f40); (0x187195, 0x187196); (0x18a67c, 0x18a680); (0x21b4ca, 0x21b4cb); (0x180cb8, 0x180cc0); (0x180cb8, 0x180cc0);
    (0x180a30, 0x180a38); (0x18a659, 0x18a65a); (0x181f40, 0x181f48); (0x181d78, 0x181d80); (0x181ee8, 0x181ef0); (0x181d48, 0x181d50); (0x21b5a3, 0x21b5a4);
    (0x187138, 0x187140); (0x187140, 0x187144); (0x20bbe2, 0x20bbe3); (0x187178 + 44, 0x187178 + 48); (0x187178 + 52, 0x187178 + 56); (0x187178 + 85, 0x187178 + 86);
    (0x6be3e8 + 16, 0x6be3e8 + 20); (0x180b28, 0x180b30); (0x21b440, 0x21b448); (0x1891dc, 0x1891dd); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x21b448, 0x21b450); (0x186630, 0x186648); (0x1871a8, 0x1871ac);

    (0x17ff08, 0x17ff10); (0x21b583, 0x21b584); (0x21b59c, 0x21b59d); (0x6de6a8, 0x6de6b0);

    (0x1891c0, 0x1891d0); (l_MT L + 0x24798, l_MT L + 0x24798 + 120); (l_MT L + 0x1b5760, l_MT L + 0x1b5760 + 120);
      (0x181ee0, 0x181ee8); (0x181e38, 0x181e40); (0x181e00, 0x181e08); (0x183fb4, 0x183fb8); (0x187194, 0x187195); (0x17ff60, 0x17ff68); (0x17d5c0, 0x17d5c8); (0x17d6e0, 0x17d6e8); (0x17da68, 0x17da70); (0x17db98, 0x17dba0); (0x17de28, 0x17de30); (0x17e0d8, 0x17e0e0);

    (0x181d88, 0x181d98); (0x187230, 0x187238);
    (0x1799e0, 0x1799f0); (0x17fdb8, 0x17fdc0); (0x17fe98, 0x17fea8); (0x180b30, 0x180b40); (0x180bb0, 0x180bc0); (0x180ce8, 0x180cf8);
    (0x181d40, 0x181d48); (0x181db8, 0x181dd0); (0x187190, 0x187194); (0x1871d8, 0x1871d9); (0x21b4fc, 0x21b4fd); (0x21b820, 0x21b821);
    (0x17a080, 0x17a0c0); (0x17a140, 0x17a1a0);   (0x180b50, 0x180b70);   (0x17d908, 0x17d930);   (0x17d8b8, 0x17d8c0);   (0x17d7a0, 0x17d7b0); (0x180ba0, 0x180ba8); (0x181d68, 0x181d78); (0x21b5a6, 0x21b5a8);
      (0x17dce0, 0x17dce8); (0x180ba8, 0x180bb0);
      (l_T L + 72, l_T L + 72 + 8); (0x181ed0, 0x181ed0 + 8);
      (0x17d058, 0x17d068); (0x17d230, 0x17d240); (0x17d278, 0x17d280); (0x17d290, 0x17d2a8); (0x17d2d0, 0x17d2d8); (0x17d2e0, 0x17d300); (0x17fc90, 0x17fca8); (0x17fcc0, 0x17fcd8); (0x17fce8, 0x17fcf0); (0x17fe70, 0x17fe78); (0x180bc8, 0x180bd0); (0x180bd0, 0x180bd8); (0x181d80, 0x181d88);
      (0x17dce8, 0x17dcf0);   (0x17e888, 0x17e890); (0x17e890, 0x17e8b8); (0x17de78, 0x17de90)   ].

End GWIN.
Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
End GWIN.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

End GWIN.
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

End GWIN.
Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
End GWIN.
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono bsegs m m' ->
  consts_rep L m'.
Proof.
  intros L m m' H HA W.
  destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
                 & (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
                    & X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43 & X44 & X45 & X46)).
  assert (M' : m2s_cells m') by (split; [rwc_frame | split; [rwc_frame | rwc_frame]]).
  split; [split; [rwc_frame | rwc_frame]|].
  split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]]]|].
  split; [split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]] | rwc_frame]|].
  split; [exact M'|].
  split; [split; [rwc_frame | split; [exact M' | split; [split; [rwc_frame | rwc_frame] | split; [rwc_frame | rwc_frame]]]]|].
  split; [split; [rwc_frame | rwc_frame]|].
  split; [split; [roc_frame | split; [roc_frame | split; [roc_frame | roc_frame]]]|].
  split; [rwc_frameX X1|]. split; [roc_frameX X2|]. split; [roc_frameX X3|]. split; [roc_frameX X4|]. split; [roc_frameX X5|]. split; [roc_frameX X6|].
  split; [roc_frameX X7|]. split; [rwc_frameX X8|]. split; [roc_frameX X9|]. split; [roc_frameX X10|]. split; [roc_frameX X11|]. split; [roc_frameX X12|].
  split; [roc_frameX X13|]. split; [roc_frameX X14|]. split; [roc_frameX X15|]. split; [roc_frameX X16|]. split; [roc_frameX X17|]. split; [roc_frameX X18|].
  split; [rwc_frameX X19|]. split; [rwc_frameX X20|]. split; [rwc_frameX X21|]. split; [rwc_frameX X22|]. split; [rwc_frameX X23|]. split; [rwc_frameX X24|].
  split; [rwc_frameX X25|]. split; [rwc_frameX X26|]. split; [rwc_frameX X27|]. split; [rwc_frameX X28|]. split; [rwc_frameX X29|]. split; [rwc_frameX X30|].
  split; [rwc_frameX X31|].
  split; [exact (stk_wmono m m' _ _ X32 W)|].
  split; [rwc_frameX X33|]. split; [rwc_frameX X34|]. split; [rwc_frameX X35|]. split; [rwc_frameX X36|].
  split; [rwc_frameX X37|]. split; [rwc_frameX X38|]. split; [rwc_frameX X39|]. split; [rwc_frameX X40|]. split; [rwc_frameX X41|].

  split; [destruct X42 as (Q1 & Q2 & Q3 & Q4); split; [rwc_frameX Q1|]; split; [rwc_frameX Q2|]; split; [rwc_frameX Q3 | rwc_frameX Q4]|].
  unfold io_rw, io_ro in *. refine (conj _ (conj _ (conj _ _))); [ | | rwc_frameX X45 | roc_frameX X46].
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwc_frameX Y|] end.
    apply Forall_nil.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; roc_frameX Y|] end.
    apply Forall_nil.
Qed.

End GWIN.
