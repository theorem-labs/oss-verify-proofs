(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PPS.

Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as H.
  assert (L : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite L in H. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma grow_cap_facts : forall cap need, 24 <= cap -> cap mod 8 = 0 -> cap <= 2 ^ 26 -> 0 <= need < 2 ^ 26 ->
  let c := grow_cap cap need in 2 * cap <= c /\ need < c /\ c <= 2 ^ 27 /\ c mod 8 = 0.
Proof.
  intros cap need H24 H8 Hc Hn. cbv zeta. unfold grow_cap. set (m := Z.max need (2 * (cap - 1))).
  assert (Hm : 2 * cap - 2 <= m /\ need <= m /\ m <= 2 ^ 27 - 2) by (unfold m; lia).
  rewrite lor7 by lia. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as B.
  assert (Hq : (2 * cap - 2) / 8 <= m / 8) by (apply Z.div_le_mono; lia).
  assert (Hc8 : (2 * cap - 2) / 8 = cap / 4 - 1).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *.
    replace (2 * cap - 2) with (6 + (2 * q - 1) * 8) by lia. rewrite Z.div_add by lia. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hc4 : 4 * (cap / 4) = cap).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. change (0 / 4) with 0. lia. }
  assert (Hu : m / 8 < 2 ^ 24) by (apply Z.div_lt_upper_bound; lia).
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (8 * (m / 8) + 7 + 1) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma log2_halves : forall cap c, 24 <= cap -> 2 * cap <= c -> c <= 2 ^ 27 -> Z.log2 (2 ^ 27 / c) + 1 <= Z.log2 (2 ^ 27 / cap).
Proof.
  intros cap c H24 H2 Hc.
  assert (A : 2 ^ 27 / c <= 2 ^ 27 / (2 * cap)) by (apply Z.div_le_compat_l; lia).
  assert (B : 2 ^ 27 / (2 * cap) = 2 ^ 27 / cap / 2) by (rewrite Z.div_div by lia; f_equal; lia).
  assert (C : 2 <= 2 ^ 27 / cap) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_le_mono _ _ A) as M. rewrite B in M. set (x := 2 ^ 27 / cap) in *.
  assert (Y : 1 <= x / 2) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_double (x / 2) ltac:(lia)) as Dd. pose proof (Z.mul_div_le x 2 ltac:(lia)) as Le.
  pose proof (Z.log2_le_mono _ _ Le) as M2. lia.
Qed.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.

Definition bufcred (cr : credit) (cap kx bx : Z) : Prop :=
  cap <= 2 ^ 27 /\ 0 <= kx /\ 0 <= bx /\
  Z.log2 (2 ^ 27 / cap) * hl_k_per_malloc L + kx <= fst cr /\
  (2 ^ 28 - 2 * cap) + Z.log2 (2 ^ 27 / cap) * hl_b_overhead L + bx <= snd cr.

Lemma bufcred_grow : forall cr cap need kx bx, 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
  bufcred cr cap kx bx -> 24 <= cap -> cap mod 8 = 0 -> cap <= need -> need < 2 ^ 26 ->
  credit_ok L cr (grow_cap cap need) /\ bufcred (debit L cr (grow_cap cap need)) (grow_cap cap need) kx bx.
Proof.
  intros cr cap need kx bx Hk Hb (C1 & C2 & C3 & C4 & C5) H24 H8 Hn Hn2.
  destruct (grow_cap_facts cap need H24 H8 ltac:(lia) ltac:(lia)) as (G1 & G2 & G3 & G4). set (c := grow_cap cap need) in *.
  pose proof (log2_halves cap c H24 G1 G3) as LG. pose proof (Z.log2_nonneg (2 ^ 27 / c)) as L0.
  set (l' := Z.log2 (2 ^ 27 / c)) in *. set (l := Z.log2 (2 ^ 27 / cap)) in *.
  unfold credit_ok, debit, bufcred. cbn [fst snd]. repeat split; try lia; nia.
Qed.

Definition stk_kx (scap : Z) : Z := Z.log2 (1056 / scap) * hl_k_per_malloc L.
Definition stk_bx (scap : Z) : Z := (2112 - 2 * scap) + Z.log2 (1056 / scap) * hl_b_overhead L.
Lemma pcredit_bufcred : forall cr ps, 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> In (ps_scap ps) [66; 132; 264; 528; 1056] ->
  (pcredit L cr ps <-> bufcred cr (ps_bcap ps) (stk_kx (ps_scap ps)) (stk_bx (ps_scap ps))).
Proof.
  intros cr ps Hk Hb Hs. unfold pcredit, bufcred, kleft, bleft, stk_kx, stk_bx.
  pose proof (Z.log2_nonneg (1056 / ps_scap ps)) as L0.
  assert (S : 2 * ps_scap ps <= 2112) by (cbn [In] in Hs; lia).
  split; intros H; repeat split; try lia; nia.
Qed.

Lemma pcredit_x_bufcred : forall cr ps kx bx, 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> In (ps_scap ps) [66; 132; 264; 528; 1056] -> 0 <= kx -> 0 <= bx ->
  (pcredit_x L cr ps kx bx <-> bufcred cr (ps_bcap ps) (stk_kx (ps_scap ps) + kx) (stk_bx (ps_scap ps) + bx)).
Proof.
  intros cr ps kx bx Hk Hb Hs Hkx Hbx. unfold pcredit_x. rewrite (pcredit_bufcred _ ps Hk Hb Hs). unfold bufcred. cbn [fst snd].
  split; [intros (_ & _ & (A & B & C & D & F)) | intros (A & B & C & D & F)]; repeat split; try lia.
  - unfold stk_kx. pose proof (Z.log2_nonneg (1056 / ps_scap ps)). nia.
  - unfold stk_bx. pose proof (Z.log2_nonneg (1056 / ps_scap ps)). cbn [In] in Hs. nia.
Qed.

Definition convert_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o cap p cpa sp r kx bx : Z) (s : list Z),
    cps_heap L HI PC_CONVERT r sp PMS.CONVERT_SCR LB cr
      (fun R M => entry L R M sp r PMS.CONVERT_SCR /\ a0 R cpa /\ a1 R 1 /\ a2 R o /\ a3 R 0 /\
                  (exists v, u32 M cpa v) /\ sp <= cpa /\ cpa + 4 <= hl_sptop L /\ apart cpa 4 o 24 /\
                  str_at M o (SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ obj_on_stack L sp o 24 /\
                  Z.of_nat (length s) + 4 < 2 ^ 26 /\ bufcred cr cap kx bx)
      (fun R M R' M' LB' cr' LBk W => exists cap' p' s',
          str_at M' o (SLong cap' p' s') /\ 24 <= cap' /\ Z.of_nat (length s) <= Z.of_nat (length s') <= Z.of_nat (length s) + 4 /\
          LB' = (p', cap') :: lb_remove p LB /\ LBk = lb_remove p LB /\ W = [(o, 24)] /\ bufcred cr' cap' kx bx).
End Specs.
End PPS.
