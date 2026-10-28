(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
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
    (0x16e1b0, 0x16e1b8); (0x16e1c0, 0x16e1c8); (0x206be0, 0x206be8); (0x208cf8, 0x208d00); (0x208d6c, 0x208d6d);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x16e1d0, 0x16e1f0); (0x177138, 0x177140); (0x177e20, 0x177e38);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x208d5d, 0x208d5e); (0x208d64, 0x208d65); (0x16e1c8, 0x16e1d0); (0x16e1f8, 0x16e200);
    (0x1701d8, 0x1701e0); (0x174955, 0x174956); (0x177e3c, 0x177e40); (0x208c8a, 0x208c8b); (0x16ef68, 0x16ef70); (0x16ef68, 0x16ef70);
    (0x16ed38, 0x16ed40); (0x177e19, 0x177e1a); (0x1701e0, 0x1701e8); (0x170018, 0x170020); (0x170188, 0x170190); (0x16ffe8, 0x16fff0); (0x208d63, 0x208d64);
    (0x1748f8, 0x174900); (0x174900, 0x174904); (0x1f93a2, 0x1f93a3); (0x174938 + 44, 0x174938 + 48); (0x174938 + 52, 0x174938 + 56); (0x174938 + 85, 0x174938 + 86);
    (0x6ab368 + 16, 0x6ab368 + 20); (0x16ee30, 0x16ee38); (0x208c00, 0x208c08); (0x17699c, 0x17699d); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x208c08, 0x208c10); (0x173df0, 0x173e08); (0x174968, 0x17496c);

    (0x16e210, 0x16e218); (0x208d43, 0x208d44); (0x208d5c, 0x208d5d); (0x6cb628, 0x6cb630);

    (0x170028, 0x170038); (0x1749f0, 0x1749f8);
    (0x168408, 0x168418); (0x16e0c8, 0x16e0d0); (0x16e1a0, 0x16e1b0); (0x16ee38, 0x16ee48); (0x16ee98, 0x16eea8); (0x16ef98, 0x16efa8);
    (0x16ffe0, 0x16ffe8); (0x170058, 0x170070); (0x174950, 0x174954); (0x174998, 0x174999); (0x208cbc, 0x208cbd); (0x208fe0, 0x208fe1);
    (0x1689a0, 0x1689e0); (0x168a60, 0x168ac0); (0x16ee88, 0x16ee90); (0x170008, 0x170018); (0x208d66, 0x208d68);
    (0x168868, 0x168880); (0x16ee50, 0x16ee60); (0x16bff0, 0x16bff8); (0x16ee90, 0x16ee98);
      (l_T L + 72, l_T L + 72 + 8); (0x170170, 0x170170 + 8);
      (0x16b978, 0x16b988); (0x16bb50, 0x16bb60); (0x16bb98, 0x16bba0); (0x16bbb0, 0x16bbc8); (0x16bbf0, 0x16bbf8); (0x16bc00, 0x16bc20); (0x16dfa0, 0x16dfb8); (0x16dfd0, 0x16dfe8); (0x16dff8, 0x16e000); (0x16e178, 0x16e180); (0x16eeb0, 0x16eeb8); (0x16eeb8, 0x16eec0); (0x170020, 0x170028);
      (0x16bff8, 0x16c000);   (0x16cb98, 0x16cba0); (0x16cba0, 0x16cbc8); (0x16c188, 0x16c1a0); (0x16ef60, 0x16ef68) ].

End GWIN.
Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
End GWIN.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

End GWIN.
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
End GWIN.
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono bsegs m m' ->
  consts_rep L m'.
Proof.
  intros L m m' H HA W.
  destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
                 & (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
                    & X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43 & X44 & X45)).
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
  unfold io_rw, io_ro in *. refine (conj _ (conj _ (conj _ _))); [ | | rwc_frameX X44 | roc_frameX X45].
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwc_frameX Y|] end.
    apply Forall_nil.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; roc_frameX Y|] end.
    apply Forall_nil.
Qed.

End GWIN.
