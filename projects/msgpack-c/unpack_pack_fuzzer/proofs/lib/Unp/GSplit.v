(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module GSplit.
Section WithPc.
Variable S_PC : int.
Variable IDX : nat.
Variable N : nat.

Definition lit_of_nat (c : nat) : sv := VL (wlit (Uint63.of_Z (Z.of_nat c))).

Definition gsplit_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      match nth IDX ca (VL wzero) with
      | VP k o =>
          if weqb o wzero && Nat.leb N 16
             && dec_true (decide_ltu (s_facts st) (VP k o) (lit_of_nat N))
          then Some (List.map (fun c => addfact st (FEq (VP k o) (lit_of_nat c))) (List.seq 0 N))
          else None
      | _ => None
      end
  | None => None
  end.

Definition gsplit_contract : contract := Contract S_PC gsplit_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma lit_of_nat_val : forall E c, (c <= 16)%nat -> bv_unsigned (den E (lit_of_nat c)) = Z.of_nat c.
Proof.
  intros E c H. unfold lit_of_nat. rewrite den_VL, wlit_ok, Uint63.of_Z_spec. apply Z.mod_small.
  change wB with (2 ^ 63). lia.
Qed.

Theorem gsplit_sound : contract_sound segs OPS MP PB gsplit_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gsplit_contract c_apply] in HA. unfold gsplit_apply in HA.
  destruct (the_op st) as [[[[md aw] ws] ca]|]; [|discriminate].
  destruct (nth IDX ca (VL wzero)) as [|k o| | | | | | | | |] eqn:NTH; try discriminate.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end. injection HA as <-.
  apply andb_prop in COND as [COND DL]. apply andb_prop in COND as [_ N16]. apply Nat.leb_le in N16.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  unfold dec_true in DL. destruct (decide_ltu (s_facts st) (VP k o) (lit_of_nat N)) as [[|]|] eqn:D; try discriminate DL.
  apply (decide_ltu_sound E _ FH) in D. unfold bv_ltu in D. apply Z.ltb_lt in D. rewrite (lit_of_nat_val E N N16) in D.
  pose proof (bv_unsigned_in_range _ (den E (VP k o))) as R.
  set (c := Z.to_nat (bv_unsigned (den E (VP k o)))).
  assert (CN : (c < N)%nat) by (subst c; lia).
  refine (Hk (addfact st (FEq (VP k o) (lit_of_nat c))) _ E ms model (env_ext_refl (s_next st) E) HMP _).
  - apply in_map_iff. exists c. split; [reflexivity|]. apply in_seq. lia.
  - apply addfact_sound; [exact HS|]. cbn [fact_holds]. apply bv_eq. rewrite (lit_of_nat_val E c ltac:(lia)). subst c. rewrite Z2Nat.id by lia. reflexivity.
Qed.

End Sound.
End WithPc.
End GSplit.
