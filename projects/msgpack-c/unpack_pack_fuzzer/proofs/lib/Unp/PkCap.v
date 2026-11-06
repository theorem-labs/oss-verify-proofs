(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib GWin PkStack PkAux GCap.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL PkStack PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkCap.

Definition cap_of (i : Z) : int := Uint63.of_Z (24 * 2 ^ i).
Definition PK_CAPS : list int := Eval vm_compute in List.map cap_of (zseq 0 11).
Lemma PK_CAPS_eq : PK_CAPS = List.map cap_of (zseq 0 11).
Proof. vm_compute. reflexivity. Qed.

Definition pk_pre (st : sstate) (ca : list sv) : bool := dec_false (decide_eq0 (s_facts st) (GCap.carg ca 6)).

Lemma cap_of_val : forall i, 0 <= i <= 57 -> to_Z (cap_of i) = 24 * 2 ^ i.
Proof.
  intros i Hi. unfold cap_of. rewrite Uint63.of_Z_spec.
  assert (2 ^ i <= 2 ^ 57) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_small. change wB with (2 ^ 63). change (2 ^ 57) with 144115188075855872 in *. change (2 ^ 63) with 9223372036854775808. lia.
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.

Lemma pk_split : forall E st ms model aw ws ca kB ob,
  st_ok segs OPS E st ms model -> the_op st = Some (3%uint63, aw, ws, ca) ->
  GCap.carg ca 6 = VP kB ob -> weqb ob wzero = true -> pk_pre st ca = true ->
  bv_unsigned (den E (GCap.carg ca 7)) = bv_unsigned (den E (GCap.carg ca 8)) ->
  exists L, In L PK_CAPS /\ bv_unsigned (den E (GCap.carg ca 8)) = bv_unsigned (ev E kB) + to_Z L.
Proof.
  intros E st ms model aw ws ca kB ob HS TO EB OB PRE FULL.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (op & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ op Pops (op_in_In st op OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try (exfalso; exact HC).
  cbn [map decode_pk] in HC. unfold GCap.carg in *. cbn [nth] in *. subst eb.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in Leb, Lee, Lecap.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  unfold pk_pre, GCap.carg in PRE. cbn [nth] in PRE.
  pose proof (dnz_sound E _ _ Pfacts PRE) as EBNZ.
  destruct VE as [(B0 & _)|[(VV1 & VV2 & VV3 & VV4) (CPOS & CPOW & CLE)]]; [exfalso; apply EBNZ; rewrite <- Leb; exact B0|].
  pose proof (den_VP0 E kB ob OB) as DB.

  pose proof (proj1 O _ (owned_evec g VV3)) as VLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA VLB) as (Bb1 & Bb2 & Bb3 & Bb4 & _). cbn [fst snd] in Bb1, Bb2, Bb3.
  pose proof (aw_ceiling_small segs IMGX AW model) as CS. unfold Mem.two62Z in CS.
  unfold v_bytes in Bb2, Bb3. rewrite EL in Bb2, Bb3. unfold ELEM_SIZE in Bb2, Bb3.
  apply pow2_b_spec in CPOW. destruct CPOW as (k & Hk & CK).
  assert (K57 : k <= 10).
  { destruct (Z_le_gt_dec k 10) as [A|A]; [exact A| exfalso].
    assert (2 ^ 11 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). rewrite CK in CLE.
    change (2 ^ 11) with 2048 in *. lia. }
  exists (cap_of k). split.
  - rewrite PK_CAPS_eq. apply in_map. apply zseq_in. lia.
  - rewrite cap_of_val by lia. rewrite <- Lecap. unfold v_capend. rewrite EL, Leb, DB, CK. unfold ELEM_SIZE. reflexivity.
Qed.

Definition pkcap_contract (pc : int) : contract := GCap.cap_contract pc 3%uint63 6 7 8 PK_CAPS pk_pre.

Theorem pkcap_sound : forall pc MP PB, contract_sound segs OPS MP PB (pkcap_contract pc).
Proof. intros pc MP PB. exact (GCap.cap_sound pc 3%uint63 6 7 8 PK_CAPS pk_pre segs OPS MP PB pk_split). Qed.

End Sound.
End PkCap.
