(* reac-pw/fuzz_link, image A: the instance of LinkWalkErrno.v's hypothesis ERRF. On fuzz_link.asan errno is the
   thread-pointer cell TFIB_ERRNO = 0x631b6c (lib/A/AF0m.v), and none of the ranges of the runtime's owned static table
   Tfib_owned_static (AF0m.v) holds any of its 4 bytes: a computation over the table, as lib/A/AFk0.v errno_not_owned
   shows the same of TFIB_ERRNO. A walk that takes ERRF as a Section hypothesis is discharged at the image's asyms by
   `link_errno_not_static B TS` (TS : PcapSyms B).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma link_errno_not_static : forall B, PcapSyms B ->
  forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha O. rewrite (ts_owned B TS) in O. rewrite (ts_errno B TS) in Ha.
unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & X).
unfold in_zr in X. unfold TFIB_ERRNO in Ha. cbn [In] in Hr.
repeat match type of Hr with
| _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X; lia|]
| False => destruct Hr
end.
Qed.
