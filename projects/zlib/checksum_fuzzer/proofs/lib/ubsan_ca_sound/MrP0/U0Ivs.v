(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Import U0HBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ivs_subb (small big : list (Z * Z)) : bool :=
  forallb (fun iv => existsb (fun iv' => (fst iv' <=? fst iv) && (snd iv <=? snd iv')) big) small.

Lemma pristine_in_sub : forall (M : word -> option byte) small big,
  ivs_subb small big = true -> pristine_in big M -> pristine_in small M.
Proof.
  intros M small big HS PR lo hi a IN Ha. unfold ivs_subb in HS. rewrite forallb_forall in HS.
  specialize (HS (lo, hi) IN). apply existsb_exists in HS as ([lo' hi'] & IN' & HB). cbn [fst snd] in HB.
  apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (PR lo' hi' a IN'). lia.
Qed.
