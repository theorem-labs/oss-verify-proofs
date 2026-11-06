(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTxS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTxS.
Local Set Keyed Unification.

Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

Definition PS (st : mstate) (q : aptr) : Prop :=
exists b m, hosts st b m /\ fst b = fst q /\
((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
\/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Definition geom_kept (st st' : mstate) : Prop :=
forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
/\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

End INTERIOR.
