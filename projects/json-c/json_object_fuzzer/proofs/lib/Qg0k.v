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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q75l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q75l.
Import ListNotations.

Local Ltac one5_fast :=
intros;
repeat match goal with H : (_ \/ _) /\ (~ _ /\ _) |- _ => let Hd := fresh "Hd" in let HN := fresh "HN" in destruct H as [Hd HN] end;
lazymatch goal with |- (_ \/ _) /\ (~ _ /\ _) => idtac end;
split;
[ repeat match goal with H : ~ _ /\ _ |- _ => clear H end; tauto
| repeat split; intros [? ?]; repeat match goal with H : _ \/ _ |- _ => clear H end; tauto ].
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section AOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst bg, sstart (MR st g) i).
Hypothesis C1 : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0.
Hypothesis C2 : x_fresh X <> Some g -> m_sizeclass (MR st g) < 48 -> in_list LS g.
Hypothesis C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g).
Let st' := upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

End AOR.

Section ACT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (a ba : aptr) (aia : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Ha : s_groups st !! ba = Some (mkGhdr (Some a) aia).
Hypothesis AV0 : m_avail (MR st a) = 0.
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st a)))) = Some a.
Let act := mask_upto aia.
Let A' := Z.land (m_freed (MR st a)) act.
Let F' := Z.ldiff (m_freed (MR st a)) act.
Let st' := upd_meta a (fun r => m_set_avail A' (m_set_freed F' r)) st.

End ACT.
