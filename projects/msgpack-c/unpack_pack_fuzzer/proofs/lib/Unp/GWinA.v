(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GWA.
Section WithSegs.
Variable segs : list Segment.

Definition subst_all (f : sv -> sv) (R : IMap.t region) : IMap.t region := IMap.map (subst_cells f) R.

Lemma find_subst_all : forall f R k r', IMap.find k (subst_all f R) = Some r' ->
  exists r0, IMap.find k R = Some r0 /\ r' = subst_cells f r0.
Proof.
  intros f R k r' F. unfold subst_all in F. rewrite IMap.find_map in F. destruct (IMap.find k R) as [r0|]; [|discriminate].
  cbn [option_map] in F. injection F as <-. exists r0. auto.
Qed.

Lemma find_subst_all_fwd : forall f R k r0, IMap.find k R = Some r0 -> IMap.find k (subst_all f R) = Some (subst_cells f r0).
Proof. intros f R k r0 F. unfold subst_all. rewrite IMap.find_map, F. reflexivity. Qed.

Lemma st_ok_subst_cells_all : forall OPS E st ms mo f,
  st_ok segs OPS E st ms mo -> (forall v, den E (f v) = den E v) ->
  st_ok segs OPS E (setregs st (subst_all f (s_regs st))) ms mo.
Proof.
  intros OPS E st ms mo f HS HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RANGE : forall k' r', IMap.find k' (subst_all f (s_regs st)) = Some r' ->
            exists r0, IMap.find k' (s_regs st) = Some r0 /\ loZ r' = loZ r0 /\ (forall E0, hiZ E0 r' = hiZ E0 r0) /\ rg_w r' = rg_w r0).
  { intros k' r' F'. destruct (find_subst_all f _ k' r' F') as (r0 & F0 & ->). exists r0. repeat split; auto. }
  assert (BASED : forall a, in_based E (subst_all f (s_regs st)) a <-> in_based E (s_regs st) a).
  { intros a. unfold in_based. split.
    - intros (k' & r' & F' & K' & R'). destruct (RANGE k' r' F') as (r0 & F0 & L0 & H0 & _). exists k', r0. rewrite <- L0, <- (H0 E). auto.
    - intros (k' & r' & F' & K' & R'). exists k', (subst_cells f r'). split; [exact (find_subst_all_fwd f _ k' r' F')|]. split; [exact K'|]. exact R'. }
  constructor; cbn [setregs s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - unfold subst_all. apply IMap.bst_map. exact Pbst.
  - intros k' r' F'. destruct (find_subst_all f _ k' r' F') as (r0 & F0 & ->). apply region_ok_subst_cells; [exact HF| exact (Preg k' r0 F0)].
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a [A1 A2].
    destruct (RANGE k1 r1 F1) as (q1 & G1 & L1 & H1 & W1). destruct (RANGE k2 r2 F2) as (q2 & G2 & L2 & H2 & W2).
    rewrite L1, (H1 E) in A1. rewrite L2, (H2 E) in A2. rewrite W1, W2 in W.
    exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 W a (conj A1 A2)).
  - intros r0 g gr c F0 FG Hc. destruct (find_subst_all f _ _ r0 F0) as (q0 & Q0 & ->).
    cbn [subst_cells rg_cells] in FG. rewrite IMap.find_map in FG. destruct (IMap.find g (rg_cells q0)) as [gr0|] eqn:FG0; [|discriminate].
    cbn [option_map] in FG. injection FG as <-. cbn [sub_gran g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    cbn [sub_cell c_idx c_w]. exact (Ppub q0 g gr0 c0 Q0 FG0 Hc0).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. pose proof (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [A B].
    split; [| exact B]. intros X. apply A. exact (proj1 (BASED a) X).
  - intros a FA. apply Pcov. destruct FA as [B|S]; [left; exact (proj1 (BASED a) B)| right; exact S].
Qed.

Fixpoint notin (k : int) (l : list int) : bool :=
  match l with [] => true | x :: l' => negb (PrimInt63.eqb k x) && notin k l' end.
Lemma notin_sound : forall k l, notin k l = true -> ~ In k l.
Proof.
  induction l as [|x l IH]; intros H; cbn [notin] in H; [intros []|]. apply andb_prop in H as [H1 H2].
  intros [<-|Hin]; [rewrite Uint63.eqb_refl in H1; discriminate| exact (IH H2 Hin)].
Qed.

Definition len_in (key : int) (len hi : sv) : bool :=
  match lit len, lit hi with
  | Some l, Some h => Mem.keyZ key + to_Z l <=? to_Z h
  | _, _ => PrimInt63.eqb key 0%uint63 && sv_eqb len hi
  end.

Definition ghost_win_ok (R : IMap.t region) (own : list int) (w : sv * sv * sv) : bool :=
  match w with
  | (VP k lo, len, _) =>
      negb (PrimInt63.eqb k 0%uint63) && notin k own &&
      match IMap.find k R, okey lo with
      | Some r, Some key => PrimInt63.eqb key (rg_lo r) && len_in key len (rg_hi r)
      | _, _ => false
      end
  | _ => false
  end.

Lemma ghost_win_ok_sound : forall priv E m R own w,
  ghost_win_ok R own w = true ->
  (forall k r, IMap.find k R = Some r -> region_ok segs priv E m k r) ->
  exists k r, IMap.find k R = Some r /\ PrimInt63.eqb k 0%uint63 = false /\ ~ In k own /\
    forall a, in_iv (w_iv (wden E w)) a -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r.
Proof.
  intros priv E m R own [[lo len] kd] H HR. unfold ghost_win_ok in H.
  destruct lo as [|k o| | | | | | | | |]; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [K0 NI]. apply negb_true_iff in K0.
  destruct (IMap.find k R) as [r|] eqn:F; [|discriminate]. destruct (okey o) as [key|] eqn:OK; [|discriminate].
  apply andb_prop in H3 as [KEY LEN]. apply Uint63.eqb_correct in KEY.
  exists k, r. split; [exact F|]. split; [exact K0|]. split; [exact (notin_sound _ _ NI)|].
  pose proof (ro_range _ _ _ _ _ _ (HR k r F) K0) as [R0 R1].
  destruct (okey_sound o key OK) as [KZ _].
  assert (LOZ : loZ r = w2Zs o) by (unfold loZ, St.keyZ; rewrite <- KEY; exact KZ).
  intros a Ha. unfold in_iv, w_iv, wden in Ha. cbn [w_lo w_len fst snd] in Ha.
  rewrite (ValP.den_VP E k o) in Ha. rewrite <- LOZ in Ha.
  pose proof (bv_unsigned_in_range _ (den E len)) as RL. rewrite bv_modulus_64 in RL.
  assert (LPOS : 0 < bv_unsigned (den E len)) by lia.
  assert (LE : loZ r + bv_unsigned (den E len) <= hiZ E r).
  { unfold len_in in LEN. destruct (lit len) as [l|] eqn:L1.
    - destruct (lit (rg_hi r)) as [h|] eqn:L2.
      + apply Z.leb_le in LEN. rewrite (lit_sound E len l L1). unfold hiZ. rewrite (lit_sound E (rg_hi r) h L2).
        unfold loZ, St.keyZ. rewrite <- KEY. exact LEN.
      + apply andb_prop in LEN as [K00 EQ]. apply Uint63.eqb_correct in K00. apply sv_eqb_eq in EQ. subst len.
        unfold loZ, St.keyZ. rewrite <- KEY, K00. unfold hiZ. change (Mem.keyZ 0%uint63) with 0. lia.
    - apply andb_prop in LEN as [K00 EQ]. apply Uint63.eqb_correct in K00. apply sv_eqb_eq in EQ. subst len.
      unfold loZ, St.keyZ. rewrite <- KEY, K00. unfold hiZ. change (Mem.keyZ 0%uint63) with 0. lia. }
  rewrite Z.mod_small in Ha by lia. lia.
Qed.

End WithSegs.
End GWA.
