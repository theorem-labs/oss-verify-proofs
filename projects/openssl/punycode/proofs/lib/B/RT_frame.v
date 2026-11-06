(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs RT_state RT_rep D_kit I_lkit TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stk_wmono : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition in_rngs (l : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition consts_rngs (L : layoutA) : list (Z * Z) :=
  [ (i_spacebeg, i_spacebeg + 24); (i_premapped, i_premapped + 1);
    (0x5e0f38, 0x5e0f40); (0x5e0f48, 0x5e0f50); (0x733520, 0x733528); (0x735638, 0x735640); (0x7356ac, 0x7356ad);
    (g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
    (g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
    (0x5e0f58, 0x5e0f78); (0x6a3a78, 0x6a3a80); (0x6a4760, 0x6a4778);
    (g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
    (g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
    (l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
    (g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
    (g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
    (l_T L + 0xc60, l_T L + 0xc60 + 1); (0x73569d, 0x73569e); (0x7356a4, 0x7356a5); (0x5e0f50, 0x5e0f58); (0x5e0f80, 0x5e0f88);
    (0x5e4188, 0x5e4190); (0x6a1295, 0x6a1296); (0x6a477c, 0x6a4780); (0x7355ca, 0x7355cb); (0x5e2ec8, 0x5e2ed0); (0x5e2ec8, 0x5e2ed0);
    (0x5e1ae0, 0x5e1ae8); (0x6a4759, 0x6a475a); (0x5e4190, 0x5e4198); (0x5e3fb0, 0x5e3fb8); (0x5e4138, 0x5e4140); (0x5e3f68, 0x5e3f70); (0x7356a3, 0x7356a4);
    (0x6a1238, 0x6a1240); (0x6a1240, 0x6a1244); (0x725ce2, 0x725ce3); (0x6a1278 + 44, 0x6a1278 + 48); (0x6a1278 + 52, 0x6a1278 + 56); (0x6a1278 + 85, 0x6a1278 + 86);
    (0xbdae10 + 32, 0xbdae10 + 36); (0x5e1bd0, 0x5e1bd8); (0x735540, 0x735548); (0x6a32dc, 0x6a32dd); (l_TCX L + 8, l_TCX L + 8 + 4);
    (l_T L, l_T L + 8); (0x735548, 0x735550); (0x6a0730, 0x6a0748); (0x6a12a8, 0x6a12ac);
    (* [comment removed for export] *)
    (0x5e0f98, 0x5e0fa0); (0x735683, 0x735684); (0x73569c, 0x73569d); (0xbfb0d0, 0xbfb0d8);
    (* [comment removed for export] *)
    (0x5e3fc0, 0x5e3fd8); (0x6a1330, 0x6a1338);
    (0x56b680, 0x56b698); (0x5e0e48, 0x5e0e50); (0x5e0f28, 0x5e0f38); (0x5e1bd8, 0x5e1be8); (0x5e2eb0, 0x5e2ec8); (0x5e2ef8, 0x5e2f08);
    (0x5e3f60, 0x5e3f68); (0x5e3ff8, 0x5e4010); (0x6a1290, 0x6a1294); (0x7355fc, 0x7355fd); (0x735920, 0x735921);
    (0x5e3f80, 0x5e3f88); (0x7356a5, 0x7356a6); (0x5e2558, 0x5e2560); (0x5e2570, 0x5e2578); (0x5e2630, 0x5e2638); (0x5e2590, 0x5e2598); (0x5e2598, 0x5e25a0) ].

Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
  g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
  g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Ltac in_rng_search := unfold in_rngs;
  solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.
(* [comment removed for export] *)
Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.

(* [comment removed for export] *)
Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
(* [comment removed for export] *)
Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono bsegs m m' ->
  consts_rep L m'.
Proof.
  intros L m m' H HA W.
  destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
                 & (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
                    & X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43)).
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
  unfold io_rw, io_ro in *. split.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwc_frameX Y|] end.
    apply Forall_nil.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; roc_frameX Y|] end.
    apply Forall_nil.
Qed.
