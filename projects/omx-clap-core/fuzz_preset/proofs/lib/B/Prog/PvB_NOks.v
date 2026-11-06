(* fuzz_preset image B' (asan-ubsan pin d663f82d7f48, #102), parse_value 0x8637c, SEGMENT N (the number arm): the two
   RUN CONDITIONS the arm's refused fuzz_malloc needed until the kit re-keyed prh_oks / rd_ledger_move's refusal conjunct on
   n <= most (done on this tree: PRH_Base.v:946-950; no file Requires this one, PvB_N.v:36), and one satisfiability witness each.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma).
   WHY: f97c's fuzz_malloc (lib/A/PRH_FnAlloc.v 740f4d11d144, prh_alloc_post arm 2, #102's refused()) leaves, on an
   allocator refusal of n user bytes, g_peak' = max (g_peak, min (SIZE_MAX, g_live + n)) and g_ran_out' = 1 only when
   n <= g_most; parse_value's text (lib/A/PRH_FnParse.v 105eb463e190, rd_ledger_move at the trace [EFail (S m)] under
   the outcomes [false]) asks g_ran_out' = 1 (prh_oks's third conjunct) and g_peak' = max (g_peak, g_live). At the
   entry's ledger values (the call's: no allocator step precedes the call) the two agree exactly when
     pn_oks_ran  most ran m:   m + 1 <= g_most, or g_ran_out is already 1;
     pn_oks_peak Lam peak m:   min (SIZE_MAX, g_live + m + 1) <= g_peak.
   PvB_NQ.v and PvB_N.v carry them as the Section hypotheses K0_OKS_REFUSAL_RAN / K0_OKS_REFUSAL_PEAK, keyed on the
   entry and the arm's scan length m.
   WITNESSES (neither condition is false for every state):
   - pn_oks_ran_sat: at a real B' state g_most = PJ_ALLOC_BOUND (size) = 256 size + 20480, set once per input from its
     size (#102 fuzz/fuzz_preset.c:810, lib/Spec/PjReqBound.v), and a reading of the input reads a number of at most
     size bytes, so m + 1 <= g_most.
   - pn_oks_peak_sat: g_live = 0 (Lam = []) and g_peak >= m + 1. g_peak only rises (fuzz_alloc_peak_reset sets it to
     g_live), so that ledger is reached after any block of at least m + 1 user bytes was taken and freed (an earlier
     reading of the same input).
   Numerals: 1 (LENGTH: the token's terminating NUL byte); 0 (LENGTH: the empty ledger's live bytes). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjReqBound.
Import ListNotations.
Local Open Scope Z_scope.

(* the ran-out half: the refused request of m + 1 user bytes is at most g_most, or g_ran_out is already 1 *)
Definition pn_oks_ran (most ran : Z) (m : nat) : Prop := Z.of_nat m + 1 <= most \/ ran = 1.

(* the peak half: the refusal does not raise g_peak above its value *)
Definition pn_oks_peak (Lam : list (Z * Z)) (peak : Z) (m : nat) : Prop :=
  Z.min PRH_Base.SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat m + 1)) <= peak.

Lemma pn_oks_ran_sat : forall (size ran : Z) (m : nat), Z.of_nat m <= size ->
  pn_oks_ran (PjReqBound.PJ_ALLOC_BOUND size) ran m.
Proof. intros size ran m H. left. unfold PjReqBound.PJ_ALLOC_BOUND. clear - H. lia. Qed.

Lemma pn_oks_peak_sat : forall (peak : Z) (m : nat), Z.of_nat m + 1 <= peak -> pn_oks_peak [] peak m.
Proof.
  intros peak m H. unfold pn_oks_peak. assert (E : Ledger.lsum [] = 0) by reflexivity. rewrite E.
  eapply Z.le_trans; [apply Z.le_min_r|]. clear - H. lia.
Qed.

Print Assumptions pn_oks_ran_sat.
Print Assumptions pn_oks_peak_sat.
