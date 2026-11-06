(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GMid.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GCnt.
Import GMid.

Definition cnt_of (v : sv) : option (sv * sv) :=
  match v with
  | VAlu ALU_SRA (VAlu ALU_SUB e b) (VL s1) => if weqb s1 GMid.w3 then Some (b, e) else None
  | _ => None
  end.

Definition side_ok (fs : list fact) (b e : sv) : bool :=
  aligned fs b 3%uint63 && aligned fs e 3%uint63
  && match decide_ltu fs e b with Some false => true | _ => false end
  && wltu (snd (sv_bounds fs e)) GMid.B63.

Section WithPc.
Variable C_PC : int.
Variable R : r5.

Definition gcnt_apply (st : sstate) : option (list sstate) :=
  let v := getr st R in
  match cnt_of v with
  | Some (b, e) => if side_ok (s_facts st) b e then Some [addfact st (FULt v (VL GMid.B60))] else None
  | None => None
  end.

Definition gcnt_contract : contract := Contract C_PC gcnt_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma cnt_of_spec : forall v b e, cnt_of v = Some (b, e) -> v = VAlu ALU_SRA (VAlu ALU_SUB e b) (VL GMid.w3).
Proof.
  intros v b e H. unfold cnt_of in H.
  destruct v as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [| |o2 x1 x2| | | | | | | |]; try discriminate H. destruct o2; try discriminate H.
  destruct y as [s1| | | | | | | | | |]; try discriminate H.
  destruct (weqb s1 GMid.w3) eqn:E1; [|discriminate H]. injection H as <- <-.
  apply (proj1 (weqb_ok _ _)) in E1. subst s1. reflexivity.
Qed.

Lemma side_ok_sound : forall E fs b e, facts_hold E fs -> side_ok fs b e = true ->
  bv_unsigned (den E b) <= bv_unsigned (den E e) /\ bv_unsigned (den E e) < 2 ^ 63
  /\ bv_unsigned (den E b) mod 8 = 0 /\ bv_unsigned (den E e) mod 8 = 0.
Proof.
  intros E fs b e FH SO. unfold side_ok in SO.
  destruct (aligned fs b 3%uint63) eqn:AB; [|discriminate].
  destruct (aligned fs e 3%uint63) eqn:AE; [|discriminate].
  destruct (decide_ltu fs e b) as [[|]|] eqn:DL; try discriminate.
  cbn [andb] in SO.
  pose proof (aligned_sound E fs FH b 3%uint63 AB ltac:(change (to_Z 3%uint63) with 3; lia)) as MB.
  pose proof (aligned_sound E fs FH e 3%uint63 AE ltac:(change (to_Z 3%uint63) with 3; lia)) as ME.
  change (to_Z 3%uint63) with 3 in MB, ME. change (2 ^ 3) with 8 in MB, ME.
  pose proof (decide_ltu_sound E fs FH e b false DL) as LE. apply (proj1 (ltu_iff _ _ false)) in LE.
  pose proof (sv_bounds_sound E fs FH e) as I0. unfold inb in I0.
  rewrite wltu_w2Z in SO. apply Z.ltb_lt in SO. replace (w2Z GMid.B63) with (2 ^ 63) in SO by (vm_compute; reflexivity).
  repeat split; try assumption; lia.
Qed.

Theorem gcnt_sound : contract_sound segs OPS MP PB gcnt_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcnt_contract c_apply] in HA. unfold gcnt_apply in HA.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  destruct (cnt_of (getr st R)) as [[b e]|] eqn:CO; [|discriminate].
  destruct (side_ok (s_facts st) b e) eqn:SO; [|discriminate]. injection HA as <-.
  apply cnt_of_spec in CO.
  destruct (side_ok_sound E (s_facts st) b e FH SO) as (LE & HI & MB & ME).
  destruct (GMid.mid_core E b e LE HI MB ME) as [CNT _].
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply addfact_sound; [exact HS|].
  cbn [fact_holds]. rewrite CO, CNT, den_VL. change (w2Z GMid.B60) with (2 ^ 60).
  pose proof (bv_unsigned_in_range _ (den E b)) as RB. rewrite bv_modulus_64 in RB. unfold two64 in RB.
  apply Z.div_lt_upper_bound; lia.
Qed.

End Sound.
End WithPc.
End GCnt.
