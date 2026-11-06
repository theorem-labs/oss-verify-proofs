(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxCw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX8X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QX8X. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4l7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4l7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAPX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAPX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyFv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyFv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TF (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.

Definition TKS (st : mstate) (T : N) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh ->
(forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.

Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.

Section WRS.

End WRS.

Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.

Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.

Definition nl_list : list (aptr * Z) :=
[(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
(aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).

End NL.
