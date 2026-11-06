(* The conversions of link's printf calls (link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f) §1): literal
   bytes, %d and %s, as a piece predicate over the shared grammar lib/Rt/PfFacts.v (pf_piece, pf_parse).
   libreac/fuzz_disco's pf_disco_piece also covers %02x and %llu, which link's formats do not use. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts.

Definition pf_link_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pd | Ps => True | _ => False end.

Lemma pf_link_piece_disco : forall p, pf_link_piece p -> pf_disco_piece p.
Proof. intros [b| | | | | | |] H; cbn in *; tauto. Qed.
