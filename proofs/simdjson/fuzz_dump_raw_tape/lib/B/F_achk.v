(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_m2s I_consts I_qck D_kit I_memcpyw I_memsetw I_strnlenw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition chkr (m : mem) (p n : Z) : Prop :=
  acc bsegs m p n
  /\ (forall i, 0 <= i < n -> exists w : word, ro_cells bsegs m (al8 (shad (p + i))) [C8 w])
  /\ (region_in_mem p n /\ n <= 2^40).

Lemma chkr_chk_ok : forall m p n, chkr m p n -> chk_ok m p n.
Proof.
  intros m p n (AC & QW & RO). split; [exact AC|]. split; [| intros _; exact RO].
  intros Hn. destruct (QW 0 ltac:(lia)) as (w1 & W1). destruct (QW (n - 1) ltac:(lia)) as (w2 & W2).
  exists w1, w2. rewrite Z.add_0_r in W1. replace (p + (n - 1)) with (p + n - 1) in W2 by lia. split; assumption.
Qed.

Lemma chkr_sub : forall m p n p' n', chkr m p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> chkr m p' n'.
Proof.
  intros m p n p' n' (AC & QW & RO) H1 H2 H3. split; [| split].
  - intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply AC. lia.
  - intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply QW. lia.
  - destruct RO as (RIM & Hb). split; [| lia].
    unfold region_in_mem in *. lia.
Qed.

Lemma chkr_bound : forall m p n, chkr m p n -> 0 <= p /\ p + n + 8 <= kHighMemEnd.
Proof. intros m p n (_ & _ & (RIM & _)). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. lia. Qed.

Definition SHADOW_LO : Z := 0x7fff8000.
Definition SHADOW_HI : Z := 0x10007fff8007.

Lemma chkr_agree : forall m m' p n, chkr m p n ->
  agree_on (fun x => SHADOW_LO <= x < SHADOW_HI) m m' -> chkr m' p n.
Proof.
  intros m m' p n C AG. pose proof (chkr_bound m p n C) as (H0 & H1). unfold kHighMemEnd in H1.
  destruct C as (AC & QW & RO). split; [| split; [| exact RO]].
  - intros i Hi. destruct (AC i Hi) as (b & Hb & Ok). exists b. split; [| exact Ok].
    apply (bytes_at_agree bsegs m m' _ _ Hb). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length] in Hx.
    unfold SHADOW_LO, SHADOW_HI, shad, SHB in *. Z.div_mod_to_equations. lia.
  - intros i Hi. destruct (QW i Hi) as (w & Hw). exists w.
    apply (ro_cells_agree bsegs m m' _ _ Hw). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize] in Hx.
    unfold SHADOW_LO, SHADOW_HI, al8, shad, SHB in *. Z.div_mod_to_equations. lia.
Qed.

Lemma chkr_munch : forall W m m' p n, chkr m p n -> munch W m m' ->
  (forall x, SHADOW_LO <= x < SHADOW_HI -> outside W x) -> chkr m' p n.
Proof.
  intros W m m' p n C MU HW. apply (chkr_agree m m' p n C). apply (agree_of_munch W m m' _ MU). exact HW.
Qed.

Definition ictx (m : mem) : Prop := icells m /\ icells_ms m /\ icells_sn m /\ m2s_cells m.

Fixpoint in_rl (l : list (Z * Z)) (x : Z) : Prop :=
  match l with [] => False | (lo, hi) :: l' => (lo <= x < hi) \/ in_rl l' x end.
Definition ICR : list (Z * Z) :=
  [(0x16e760, 0x16e790); (0x16f2d8, 0x16f2e0); (0x1705b8, 0x1705c0); (0x170728, 0x170730); (0x170778, 0x170788);
   (0x177bb8, 0x177bc0); (0x178898, 0x1788b8); (0x2097e3, 0x2097e4)].

Lemma ictx_agree : forall m m', ictx m -> agree_on (in_rl ICR) m m' -> wmono bsegs m m' -> ictx m'.
Proof.
  intros m m' ((G2 & G1 & RM & SHC & RI) & (M1 & M2 & M3 & M4 & M5) & (N1 & N2 & N3 & N4 & N5 & N6 & N7) & (X1 & X2 & X3)) AG WM.
  assert (RO : forall A cs, ro_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_rl ICR x) ->
                 ro_cells bsegs m' A cs).
  { intros A cs H HX. apply (ro_cells_agree bsegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
  assert (RW : forall A cs, rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_rl ICR x) ->
                 rw_cells bsegs m' A cs).
  { intros A cs H HX. apply (rw_cells_agree bsegs m m' _ _ H); [| exact WM].
    apply (agree_sub _ _ _ _ AG). exact HX. }
  unfold in_rl, ICR.
  split; [| split; [| split]].
  - split; [| split; [| split; [| split]]]; (apply RO; [assumption| cbn [cells_size csize]; intros x Hx; cbn; lia]).
  - split; [| split; [| split; [| split]]]; (apply RO; [assumption| cbn [cells_size csize]; intros x Hx; cbn; lia]).
  - split; [| split; [| split; [| split; [| split; [| split]]]]];
      first [ apply RO; [assumption| cbn [cells_size csize]; intros x Hx; cbn; lia]
            | apply RW; [assumption| cbn [cells_size csize]; intros x Hx; cbn; lia] ].
  - split; [| split]; (apply RW; [assumption| cbn [cells_size csize]; intros x Hx; cbn; lia]).
Qed.

Lemma ictx_munch : forall W m m', ictx m -> munch W m m' -> wmono bsegs m m' ->
  (forall x, in_rl ICR x -> outside W x) -> ictx m'.
Proof.
  intros W m m' C MU WM HW. apply (ictx_agree m m' C); [| exact WM]. apply (agree_of_munch W m m' _ MU). exact HW.
Qed.

Definition PFX_A : Z := 0x10ded.
Definition XDIG_A : Z := 0x33a18.
Definition NULLS_A : Z := 0x22da5.
Definition rod_chk (m : mem) : Prop := chkr m PFX_A 10 /\ chkr m XDIG_A 16 /\ chkr m NULLS_A 7.
