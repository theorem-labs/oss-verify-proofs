(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTxS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTxS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjEq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfGI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfGI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoeL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoeL.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ENFRAME.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Hfit : n + IB <= get_stride (MR st g).
Hypothesis TF : TF2 st.
Hypothesis Hres : get_stride (MR st g) - IB - n < 2 ^ 32.
Let X' := xpend X None.
Let stride := get_stride (MR st g).
Let slack := (stride - IB - n) / UNIT.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma ef_c16 : snd c mod 16 = 0.
Proof.
pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.

Definition pp (off : Z) : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv (off : Z) : Z := snd ee - snd (pp off) - n.
Definition qv (off : Z) : Z := (snd (pp off) - (snd bg + UNIT)) / UNIT.
Definition EL (off : Z) : list (aptr * Z) :=
(if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd (pp off) (-4), 0)] else [])
++ [(aadd (pp off) (-2), qv off); (aadd (aadd (pp off) (-2)) 1, Z.shiftr (qv off) 8); (aadd (pp off) (-3), idx)]
++ (if negb (resv off =? 0) then [(aadd ee (- resv off), 0)] else [])
++ (if 5 <=? resv off then [(aadd ee (-4), resv off); (aadd (aadd ee (-4)) 1, Z.shiftr (resv off) 8); (aadd (aadd ee (-4)) 2, Z.shiftr (resv off) 16); (aadd (aadd ee (-4)) 3, Z.shiftr (resv off) 24); (aadd ee (-5), 0)] else [])
++ [(aadd (pp off) (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5)].

Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).

Lemma pp16 off : snd (pp off) mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.

End ENFRAME.
