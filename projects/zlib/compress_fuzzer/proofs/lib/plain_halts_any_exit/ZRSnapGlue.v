(** * ZRSnapGlue — one-lemma bridge between the walk record's token
      predicate and g6-bound's landed [ZReproG6N.tok_far_ok].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).

    [ZREvSnap.EvSnapOk]'s es_far clause spells [ZRTreeState.FarOkTok];
    g6's landed acct consumers spell [ZReproG6N.tok_far_ok].  The two
    are the SAME match term (citing G6N's name inside the record is a
    dependency cycle: ZReproG6N imports SwStep imports ZREvSnap), so
    the bridge is [reflexivity] — this file just gives the equation a
    name both sides can rewrite with. *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRTreeState ZREvSnap ZReproG6N.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma farok_eq_tok_far_ok : FarOkTok = ZReproG6N.tok_far_ok.
Proof. reflexivity. Qed.

Lemma farok_forall_iff : forall l,
  Forall FarOkTok l <-> Forall ZReproG6N.tok_far_ok l.
Proof. intro l. rewrite farok_eq_tok_far_ok. reflexivity. Qed.

(** The direction g6-bound's discharge consumes. *)
Lemma farok_forall_to : forall l,
  Forall FarOkTok l -> Forall ZReproG6N.tok_far_ok l.
Proof. intro l. apply farok_forall_iff. Qed.

Print Assumptions farok_eq_tok_far_ok.
