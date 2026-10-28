(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_cache_defs R_prim_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Lemma wr_at_app_P : forall segs m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rwc_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app_P by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma ri_tail_split : forall m R rand exh pad nalloc nfreed r0 r1 r2 r3,
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 -> length pad = 3%nat ->
  rw_cells bsegs m (R + 64) [C4 rand] /\ rw_cells bsegs m (R + 68) [C1 exh]
  /\ rw_cells bsegs m (R + 69) [CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed); C8 (Z_to_bv 64 r0);
                                C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)].
Proof.
  intros m R rand exh pad nalloc nfreed r0 r1 r2 r3 H Hp. unfold ri_tail in H.
  apply (rwc_app _ _ _ [C4 rand]) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H2.
  apply (rwc_app _ _ _ [C1 exh]) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H3.
  change (Z.of_nat 4) with 4 in H2, H3. change (Z.of_nat 1) with 1 in H3.
  replace (R + 64 + 4 + 1) with (R + 69) in H3 by lia. replace (R + 64 + 4) with (R + 68) in H2 by lia.
  split; [exact H1| split; [exact H2| exact H3]].
Qed.

Lemma ri_tail_join : forall m R rand exh pad nalloc nfreed r0 r1 r2 r3,
  rw_cells bsegs m (R + 64) [C4 rand] -> rw_cells bsegs m (R + 68) [C1 exh] ->
  rw_cells bsegs m (R + 69) [CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed); C8 (Z_to_bv 64 r0);
                             C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3.
Proof.
  intros m R rand exh pad nalloc nfreed r0 r1 r2 r3 H1 H2 H3. unfold ri_tail.
  change [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed); C8 (Z_to_bv 64 r0);
          C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)]
    with ([C4 rand] ++ [C1 exh] ++ [CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed); C8 (Z_to_bv 64 r0);
          C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)]).
  apply rwc_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
  apply rwc_app. split; cbn [cells_size csize Nat.add]; change (Z.of_nat 1) with 1.
  - replace (R + 64 + 4) with (R + 68) by lia. exact H2.
  - replace (R + 64 + 4 + 1) with (R + 69) by lia. exact H3.
Qed.

Lemma u32s_repeat0 : forall k, u32s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [repeat u32s]. rewrite IH. reflexivity.
Qed.

Lemma u32arr_app_zeros : forall m A ws k,
  u32arr bsegs m A ws ->
  rw_cells bsegs m (A + 4 * Z.of_nat (length ws)) [CB (4 * k)%nat (repeat (Z_to_bv 8 0) (4 * k))] ->
  u32arr bsegs m A (ws ++ repeat (Z_to_bv 64 0) k).
Proof.
  intros m A ws k [Hb Hw] [[_ Hz] Hwz]. split.
  - rewrite u32s_app, u32s_repeat0. apply bytes_at_app. split; [exact Hb|].
    rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia.
    cbn [cells_bytes cbytes] in Hz. rewrite app_nil_r in Hz. exact Hz.
  - rewrite app_length, repeat_length. cbn [cells_size csize] in Hwz. rewrite Nat.add_0_r in Hwz.
    replace (4 * Z.of_nat (length ws + k)) with (4 * Z.of_nat (length ws) + Z.of_nat (4 * k)) by lia.
    apply wr_at_app_P; [lia| lia|]. split; assumption.
Qed.

Fixpoint covered (lo hi : Z) (W : list (Z * Z)) : Prop :=
  match W with [] => False | (a, b) :: W' => (a <= lo /\ hi <= b) \/ covered lo hi W' end.
Fixpoint all_covered (W W' : list (Z * Z)) : Prop :=
  match W with [] => True | (lo, hi) :: W'' => covered lo hi W' /\ all_covered W'' W' end.

Lemma covered_outside : forall W lo hi x, covered lo hi W -> outside W x -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; intros lo hi x Hc Ho; cbn in *; [contradiction|].
  destruct Ho as [Ho1 Ho2]. destruct Hc as [Hc|Hc]; [lia| eapply IH; eauto].
Qed.

Lemma sub_fp_covered : forall W W', all_covered W W' -> sub_fp W W'.
Proof.
  induction W as [|[lo hi] W IH]; intros W' H x Hx; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [eapply covered_outside; eauto| apply (IH W' H2 x Hx)].
Qed.

Ltac cov_solve := first [ left; split; lia | right; cov_solve ].
Ltac solve_sub_fp := apply sub_fp_covered; cbn [all_covered covered]; repeat (split; [cov_solve|]); exact I.

Ltac dsolve := cbn [disjoint_from]; simpl_sizes; repeat (match goal with |- _ /\ _ => split end);
  first [ exact I | (left; lia) | (right; lia) | lia ].
Ltac dsolve_all := cbn [disjoint_from]; simpl_sizes;
  repeat (lazymatch goal with |- _ /\ _ => split; [first [ (left; lia) | (right; lia) | lia ] |] | |- True => exact I end).

Ltac trc m0 MU WM H :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport bsegs W m0 mc _ _) in H; [ | exact MU | exact WM | dsolve_all ]
  end.
Ltac trca m0 MU WM H :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (u32arr_transport bsegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes;
      repeat (lazymatch goal with |- _ /\ _ => split; [first [ (left; lia) | (right; lia) | lia ] |] | |- True => exact I end) ]
  end.

Ltac cov_eq := first [ left; split; apply Z.le_refl | right; cov_eq ].
Ltac cov_any := first [ cov_eq | cov_solve ].
Ltac solve_sub_fp2 := apply sub_fp_covered; cbn [all_covered covered]; repeat (split; [cov_any|]); exact I.

Ltac tr_geo m0 MU WM H G S :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport bsegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; clear - G S; lia ]
  end.
Ltac tr_geoa m0 MU WM H G S :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (u32arr_transport bsegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes;
      clear - G S; lia ]
  end.
