(* PROOF-SIDE companion of sh_word_on.v: the cover lemmas that relate the Bz kit's aligned shadow word to the
   region. They need the Bz kit (I_qck, Shadow and their closure), so they live here and NOT in sh_word_on.v: a
   contract-side `_c_on.v` that Requires sh_word_on.v must not pull A.Bz.* into its importers' closure (a Theorem Labs lane's
   10:24Z rule, a Theorem Labs lane's finding). Require this file only from proof files (asan_memcpy_on.v, asan_memset_on.v,
   the wrapper `_on` proofs). Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_qck OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.Shadow.
Module SwQ := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_qck.
Module SwS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.Shadow.
Open Scope Z_scope.

(* The Bz kit's aligned shadow word (I_qck.al8 of Shadow.shad, the word the runtime's check loads) is AsanRT's. *)
Lemma al8_shad : forall x, SwQ.al8 (SwS.shad x) = 8 * ((x / 8 + ASAN_K) / 8).
Proof. intros x. unfold SwQ.al8, SwS.shad, SwS.SHB, ASAN_K. reflexivity. Qed.

(* The first and the last byte's aligned shadow words of [p, p + n) lie in sh_word_on p n: the cover every
   `shadow_word_on` / `chk_ok_of_ours_on` / `qc_word_on` call needs. *)
Lemma sh_word_on_cover : forall p n, 0 < n -> forall x j, (x = p \/ x = p + n - 1) -> 0 <= j < 8 ->
  sh_word_on p n (SwQ.al8 (SwS.shad x) + j).
Proof. intros p n Hn x j Hx Hj. rewrite al8_shad. exact (sh_word_on_end p n x j Hn Hx Hj). Qed.
