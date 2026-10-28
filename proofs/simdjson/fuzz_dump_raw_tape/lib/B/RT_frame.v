(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
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
    (0x16e750, 0x16e758); (0x16e760, 0x16e768); (0x207660, 0x207668); (0x209778, 0x209780); (0x2097ec, 0x2097ed);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x16e770, 0x16e790); (0x177bb8, 0x177bc0); (0x1788a0, 0x1788b8);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x2097dd, 0x2097de); (0x2097e4, 0x2097e5); (0x16e768, 0x16e770); (0x16e798, 0x16e7a0);
    (0x170778, 0x170780); (0x1753d5, 0x1753d6); (0x1788bc, 0x1788c0); (0x20970a, 0x20970b); (0x16f508, 0x16f510); (0x16f508, 0x16f510);
    (0x16f2d8, 0x16f2e0); (0x178899, 0x17889a); (0x170780, 0x170788); (0x1705b8, 0x1705c0); (0x170728, 0x170730); (0x170588, 0x170590); (0x2097e3, 0x2097e4);
    (0x175378, 0x175380); (0x175380, 0x175384); (0x1f9e22, 0x1f9e23); (0x1753b8 + 44, 0x1753b8 + 48); (0x1753b8 + 52, 0x1753b8 + 56); (0x1753b8 + 85, 0x1753b8 + 86);
    (0x6abde8 + 16, 0x6abde8 + 20); (0x16f3d0, 0x16f3d8); (0x209680, 0x209688); (0x17741c, 0x17741d); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x209688, 0x209690); (0x174870, 0x174888); (0x1753e8, 0x1753ec);

    (0x16e7b0, 0x16e7b8); (0x2097c3, 0x2097c4); (0x2097dc, 0x2097dd); (0x6cc0a8, 0x6cc0b0);

    (0x1705c8, 0x1705d8); (0x175470, 0x175478);
    (0x168998, 0x1689a8); (0x16e668, 0x16e670); (0x16e740, 0x16e750); (0x16f3d8, 0x16f3e8); (0x16f438, 0x16f448); (0x16f538, 0x16f548);
    (0x170580, 0x170588); (0x1705f8, 0x170610); (0x1753d0, 0x1753d4); (0x175418, 0x175419); (0x20973c, 0x20973d); (0x209a60, 0x209a61);
    (0x168f40, 0x168f80); (0x169000, 0x169060); (0x16f428, 0x16f430); (0x1705a8, 0x1705b8); (0x2097e6, 0x2097e8);
    (0x168e08, 0x168e20); (0x16f3f0, 0x16f400); (0x16c590, 0x16c598); (0x16f430, 0x16f438);
      (l_T L + 72, l_T L + 72 + 8); (0x170710, 0x170710 + 8);
      (0x16bf18, 0x16bf28); (0x16c0f0, 0x16c100); (0x16c138, 0x16c140); (0x16c150, 0x16c168); (0x16c190, 0x16c198); (0x16c1a0, 0x16c1c0); (0x16e540, 0x16e558); (0x16e570, 0x16e588); (0x16e598, 0x16e5a0); (0x16e718, 0x16e720); (0x16f450, 0x16f458); (0x16f458, 0x16f460); (0x1705c0, 0x1705c8);
      (0x16c598, 0x16c5a0); (0x16d140, 0x16d168); (0x16c728, 0x16c740); (0x16f500, 0x16f508) ].

End GWIN.
Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
End GWIN.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

End GWIN.
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

End GWIN.
Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
End GWIN.
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.

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
