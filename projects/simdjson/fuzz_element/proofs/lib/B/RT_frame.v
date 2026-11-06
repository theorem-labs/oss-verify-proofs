(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
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
    (0x178e10, 0x178e18); (0x178e20, 0x178e28); (0x212720, 0x212728); (0x214838, 0x214840); (0x2148ac, 0x2148ad);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x178e30, 0x178e50); (0x182c78, 0x182c80); (0x183960, 0x183978);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x21489d, 0x21489e); (0x2148a4, 0x2148a5); (0x178e28, 0x178e30); (0x178e58, 0x178e60);
    (0x17ae60, 0x17ae68); (0x180495, 0x180496); (0x18397c, 0x183980); (0x2147ca, 0x2147cb); (0x179bd8, 0x179be0); (0x179bd8, 0x179be0);
    (0x179998, 0x1799a0); (0x183959, 0x18395a); (0x17ae68, 0x17ae70); (0x17aca0, 0x17aca8); (0x17ae10, 0x17ae18); (0x17ac68, 0x17ac70); (0x2148a3, 0x2148a4);
    (0x180438, 0x180440); (0x180440, 0x180444); (0x204ee2, 0x204ee3); (0x180478 + 44, 0x180478 + 48); (0x180478 + 52, 0x180478 + 56); (0x180478 + 85, 0x180478 + 86);
    (0x6b6ea8 + 16, 0x6b6ea8 + 20); (0x179a90, 0x179a98); (0x214740, 0x214748); (0x1824dc, 0x1824dd); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x214748, 0x214750); (0x17f930, 0x17f948); (0x1804a8, 0x1804ac);

    (0x178e70, 0x178e78); (0x214883, 0x214884); (0x21489c, 0x21489d); (0x6d7168, 0x6d7170);

    (0x17acb0, 0x17acc0); (0x180530, 0x180538);
    (0x172d88, 0x172d98); (0x178d28, 0x178d30); (0x178e00, 0x178e10); (0x179a98, 0x179aa8); (0x179b20, 0x179b30); (0x179c08, 0x179c18);
    (0x17ac60, 0x17ac68); (0x17ace0, 0x17acf8); (0x180490, 0x180494); (0x1804d8, 0x1804d9); (0x2147fc, 0x2147fd); (0x214b20, 0x214b21);
    (0x173600, 0x173640); (0x1736c0, 0x173720); (0x179ac0, 0x179ac8); (0x17ac90, 0x17aca0); (0x2148a6, 0x2148a8);
    (0x173228, 0x173240); (0x179ac8, 0x179ad8); (0x176c50, 0x176c58); (0x179b18, 0x179b20);
      (l_T L + 72, l_T L + 72 + 8); (0x17adf8, 0x17adf8 + 8);
      (0x173170, 0x173188); (0x1765d8, 0x1765e8); (0x1767b0, 0x1767c0); (0x1767f8, 0x176800); (0x176810, 0x176828); (0x176850, 0x176858); (0x176860, 0x176880); (0x178c00, 0x178c18); (0x178c30, 0x178c48); (0x178c58, 0x178c60); (0x178dd8, 0x178de0); (0x179ab8, 0x179ac0); (0x179b38, 0x179b40); (0x179b40, 0x179b48); (0x17aca8, 0x17acb0);
      (0x176c58, 0x176c60); (0x177800, 0x177828); (0x176de8, 0x176e00); (0x179bd0, 0x179bd8) ].

End GWIN.
Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
End GWIN.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

End GWIN.
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

End GWIN.
Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

End GWIN.
Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
End GWIN.
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

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
