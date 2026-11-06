(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF StepF.
Open Scope Z_scope.

Lemma shiftr3_mono : forall a b, a <= b -> Z.shiftr a 3 <= Z.shiftr b 3.
Proof. intros a b H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29782367974.3749188513.3  000001002SS".
rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [lia|exact H]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma rng_shadow_accP : forall RNG (OFF lo hi a : Z),
  rng RNG (Z.shiftr lo 3 + OFF) (Z.shiftr hi 3 - Z.shiftr lo 3 + 1) ->
  lo <= a <= hi ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + OFF), 1%nat).
Proof.
  intros RNG OFF lo hi a R [H1 H2].
  eapply (rng_acc_litZ' RNG _ _ _ 1%nat 1 R eq_refl eq_refl).
  pose proof (shiftr3_mono _ _ H1). pose proof (shiftr3_mono _ _ H2). Local Ltac2 Set LiaHints.tbl := fun () => "0010>37646909693.10000006S1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma rng_shadow_accA : forall RNG (OFF lo len a : Z),
  rng RNG (Z.shiftr lo 3 + OFF) len ->
  lo mod 8 = 0 -> lo <= a -> a + 1 <= lo + 8 * len ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + OFF), 1%nat).
Proof.
  intros RNG OFF lo len a R M H1 H2.
  eapply (rng_acc_litZ' RNG _ _ _ 1%nat 1 R eq_refl eq_refl).
  pose proof (shiftr3_mono _ _ H1) as X.
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>29782611829.1136509690331.1349415470992.1058862470656.1361028779636.1363374621462.1263487274686.1400000100600:00;00<00=00BSS1M1HS2H2SSSS1X1Y".
assert (Y : Z.shiftr a 3 <= Z.shiftr (lo + 8 * len - 1) 3) by (apply shiftr3_mono; lia).
  rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *.
  pose proof (Z_div_mod_eq_full lo 8). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
  assert (E : (lo + 8 * len - 1) / 8 = lo / 8 + len - 1).
  { replace (lo + 8 * len - 1) with ((lo / 8 + len - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite E in Y. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Ltac shacc_with R a :=
  lazymatch type of R with
  | rng ?RNG (Z.shiftr ?lo 3 + ?OFF) (Z.shiftr ?hi 3 - Z.shiftr ?lo2 3 + 1) =>
      apply (rng_shadow_accP RNG OFF lo hi a R); lia
  | rng ?RNG (Z.shiftr ?lo 3 + ?OFF) ?len =>
      apply (rng_shadow_accA RNG OFF lo len a R); [ solve [assumption | lia] | lia | lia ]
  end.
Ltac shacc :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + ?OFF), 1%nat) =>
      let X := leftmost a in
      first [ match goal with R : rng RNG (Z.shiftr ?lo 3 + OFF) _ |- _ => let Y := leftmost lo in constr_eq X Y; shacc_with R a end
            | match goal with R : rng RNG (Z.shiftr _ 3 + OFF) _ |- _ => shacc_with R a end ]
  end.
