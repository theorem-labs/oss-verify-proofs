(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma lxor_signbit63' : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 k) as [<-|NE]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma ref_at_ualign : forall s OW LB m (ls : lstate bptr) AD r a,
  RHEAP s (OW ++ LB) m -> ad_blocks OW AD -> ref_at ls OW AD r a -> 0 < a /\ a mod 8 = 0.
Proof.
  intros s OW LB m ls AD r a HEAP (B1 & B2 & B3 & B4 & B5 & BC) HA.
  assert (X : forall p A n, In (p, A, n) OW -> 0 < A /\ A mod 16 = 0).
  { intros p A n Hin. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; assumption. }
  destruct r as [| | | | |i]; cbn [ref_at] in HA; subst.
  - destruct (X _ _ _ B1) as (P & Q). split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
  - destruct (X _ _ _ B2) as (P & Q). split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
  - destruct (X _ _ _ B3) as (P & Q). split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
  - destruct (X _ _ _ B4) as (P & Q). split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
  - destruct (X _ _ _ B5) as (P & Q). split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
  - destruct HA as (p & H & Eh & Hin & Hi & ->). destruct (X _ _ _ Hin) as (P & Q). split; [lia|]. clear - Q. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma block_ualign : forall s OW LB m p A n, RHEAP s (OW ++ LB) m -> In (p, A, n) OW -> 0 < A /\ A mod 8 = 0.
Proof.
  intros s OW LB m p A n HEAP Hin. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; [exact R0|].
  clear - R16. Z.div_mod_to_equations. lia.
Qed.

End WithCeiling0.
