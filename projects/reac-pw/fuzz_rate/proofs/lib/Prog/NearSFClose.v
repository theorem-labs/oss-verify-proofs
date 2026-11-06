(** The binary128 value facts pod_nearest's proof takes as its premise [near_sf_facts] (Prog/pod_nearest.v), closed
    by the lemmas of CJ/Spec/NearSF.v (and SFVal.v, SFSub.v, which it re-exports): the binary32 -> binary128 and
    int64 -> binary128 conversions are exact, f128_sub stays in 128 bits, and the comparisons pod_nearest makes
    (d against (long double)INT32_MIN - 1 and -2^63 - 1, frac against +-1/2) are the comparisons by value. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require pod_nearest.

Lemma near_sf_facts_ok : pod_nearest.near_sf_facts.
Proof.
  exact (conj f128_of_f32_low (conj f128_of_f32_range (conj f128_of_i64_range (conj f128_sub_range
        (conj words128 (conj near_sf_neginf (conj near_sf_lo (conj near_sf_c2 near_sf_frac)))))))).
Qed.
