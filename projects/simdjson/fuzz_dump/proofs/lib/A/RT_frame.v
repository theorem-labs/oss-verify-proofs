(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s
  R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Lemma stk_wmono : forall (m m' : mem) lo hi, stk asegs m lo hi -> wmono asegs m m' -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells asegs m a cs -> stk asegs m a hi.
Proof.
  intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
  replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_wmono : forall (m m' : mem) a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W _ (H i Hi)). Qed.

Lemma u32arr_agree : forall (m m' : mem) a ws, u32arr asegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> wmono asegs m m' -> u32arr asegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA W. split.
  - apply (bytes_at_agree asegs m m' a _ Hb). rewrite u32s_length. intros x Hx. apply HA. lia.
  - exact (wr_at_wmono m m' _ _ Hw W).
Qed.

Definition in_rngs (l : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) l.

Definition consts_rngs (L : layoutA) : list (Z * Z) :=
  [ (i_spacebeg, i_spacebeg + 24); (i_premapped, i_premapped + 1);
    (0x161ef0, 0x161ef8); (0x161f00, 0x161f08); (0x1fa4e0, 0x1fa4e8); (0x1fc5f8, 0x1fc600); (0x1fc66c, 0x1fc66d);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x161f10, 0x161f30); (0x16aa38, 0x16aa40); (0x16b720, 0x16b738);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x1fc65d, 0x1fc65e); (0x1fc664, 0x1fc665); (0x161f08, 0x161f10); (0x161f38, 0x161f40);
    (0x163f10, 0x163f18); (0x168255, 0x168256); (0x16b73c, 0x16b740); (0x1fc58a, 0x1fc58b); (0x162ca8, 0x162cb0); (0x162ca8, 0x162cb0);
    (0x162a78, 0x162a80); (0x16b719, 0x16b71a); (0x163f18, 0x163f20); (0x163d50, 0x163d58); (0x163ec0, 0x163ec8); (0x163d20, 0x163d28); (0x1fc663, 0x1fc664);
    (0x1681f8, 0x168200); (0x168200, 0x168204); (0x1ecca2, 0x1ecca3); (0x168238 + 44, 0x168238 + 48); (0x168238 + 52, 0x168238 + 56); (0x168238 + 85, 0x168238 + 86);
    (0x69ec68 + 16, 0x69ec68 + 20); (0x162b70, 0x162b78); (0x1fc500, 0x1fc508); (0x16a29c, 0x16a29d); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x1fc508, 0x1fc510); (0x1676f0, 0x167708); (0x168268, 0x16826c);

    (0x161f50, 0x161f58); (0x1fc643, 0x1fc644); (0x1fc65c, 0x1fc65d); (0x6bef28, 0x6bef30);

    (0x163d60, 0x163d70); (0x1682f0, 0x1682f8);
    (0x15c138, 0x15c148); (0x161e08, 0x161e10); (0x161ee0, 0x161ef0); (0x162b78, 0x162b88); (0x162bd8, 0x162be8); (0x162cd8, 0x162ce8);
    (0x163d18, 0x163d20); (0x163d90, 0x163da8); (0x168250, 0x168254); (0x168298, 0x168299); (0x1fc5bc, 0x1fc5bd); (0x1fc8e0, 0x1fc8e1);
    (0x15c6e0, 0x15c720); (0x15c7a0, 0x15c800); (0x162bc8, 0x162bd0); (0x163d40, 0x163d50); (0x1fc666, 0x1fc668);
    (0x15c5a8, 0x15c5c0); (0x162b90, 0x162ba0); (0x15fd30, 0x15fd38); (0x162bd0, 0x162bd8);
      (l_T L + 72, l_T L + 72 + 8); (0x163ea8, 0x163ea8 + 8);
      (0x15f6b8, 0x15f6c8); (0x15f890, 0x15f8a0); (0x15f8d8, 0x15f8e0); (0x15f8f0, 0x15f908); (0x15f930, 0x15f938); (0x15f940, 0x15f960); (0x161ce0, 0x161cf8); (0x161d10, 0x161d28); (0x161d38, 0x161d40); (0x161eb8, 0x161ec0); (0x162bf0, 0x162bf8); (0x162bf8, 0x162c00); (0x163d58, 0x163d60);
      (0x15fd38, 0x15fd40);   (0x1608d8, 0x1608e0); (0x1608e0, 0x160908); (0x15fec8, 0x15fee0); (0x162ca0, 0x162ca8) ].

End GWIN.
Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
End GWIN.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

End GWIN.
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frameX X := eapply (rw_cells_agree asegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
End GWIN.
Ltac roc_frameX X := eapply (ro_cells_agree asegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono asegs m m' ->
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
