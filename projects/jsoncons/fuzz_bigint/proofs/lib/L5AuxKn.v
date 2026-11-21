(* SPDX-License-Identifier: MIT *)
(* The start knowledge [SegAuxv.aux_kn r phnum] of the throw-path segment certificates
   holds of every memory that has the LPS 727298f3 launch's auxiliary vector at [av]:
   the type words, the program-header values and the vector's bytes, as
   [L5StrctorKit.auxv_cells] gives them.  Any build's segments ([segs]). *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore L5Defs L5KnP.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegAuxv.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module L5AUX.

Lemma nth_small (l : list Z) i : Forall (fun x => 0 <= x <= 51) l -> 0 <= nth i l 0 <= 51.
Proof. intros F. revert i. induction F as [|x l Hx _ IH]; intros [|i]; cbn; try lia; auto. Qed.

Lemma auxt_small r : Forall (fun x => 0 <= x <= 51) (auxt r).
Proof. destruct r; unfold auxt; cbn [app]; repeat (apply Forall_cons; [lia|]); apply Forall_nil. Qed.

Lemma auxt_len r : (27 <= length (auxt r) <= 29)%nat.
Proof. destruct r; cbn; lia. Qed.

Lemma auxlen_val r : auxlen r = if r then 464 else 432.
Proof. destruct r; reflexivity. Qed.

Lemma aux_kn_ok segs E M av (r : bool) (phnum : Z) :
  bv_unsigned (ev E 32) = av -> 0 <= av -> av + auxlen r <= 2 ^ 64 -> 0 <= phnum < 2 ^ 64 ->
  (forall i, (i < length (auxt r))%nat -> L5.u64_at segs M (av + 16 * Z.of_nat i) (nth i (auxt r) 0)) ->
  L5.u64_at segs M (av + 216) 65600 -> L5.u64_at segs M (av + 232) 56 -> L5.u64_at segs M (av + 248) phnum ->
  L5.defined M av (auxlen r) ->
  know_ok segs E M (aux_kn r phnum).
Proof.
  intros HE Hav Hlen Hph HT H216 H232 H248 HD.
  pose proof (auxt_len r) as L27.
  assert (HL : auxlen r = 16 * Z.of_nat (length (auxt r))) by reflexivity.
  unfold know_ok, aux_kn. apply Forall_app. split.
  - apply Forall_forall. intros K HK. apply in_map_iff in HK as (i & <- & Hi). apply in_seq in Hi.
    pose proof (nth_small (auxt r) i (auxt_small r)) as Hs.
    eapply L5KP.kentry_KWord8;
      [cbn [edenot]; exact HE | cbn [edenot]; apply L5.unsigned_lit; lia | lia | lia | apply HT; lia].
  - repeat apply Forall_cons; try apply Forall_nil.
    + eapply L5KP.kentry_KWord8; [cbn [edenot]; exact HE | cbn [edenot]; apply L5.unsigned_lit; lia | lia | lia | exact H216].
    + eapply L5KP.kentry_KWord8; [cbn [edenot]; exact HE | cbn [edenot]; apply L5.unsigned_lit; lia | lia | lia | exact H232].
    + eapply L5KP.kentry_KWord8; [cbn [edenot]; exact HE | cbn [edenot]; apply L5.unsigned_lit; lia | lia | lia | exact H248].
    + eapply L5KP.kentry_KUnk;
        [cbn [edenot]; exact HE | cbn [edenot]; apply L5.unsigned_lit; lia | lia | lia | lia | rewrite Z.add_0_r; exact HD].
Qed.

End L5AUX.
