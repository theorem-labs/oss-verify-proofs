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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4l7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4l7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAPX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAPX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwca.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwca. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q46y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q46y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDPG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDPG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3DL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3DL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp7R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp7R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTxS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTxS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjEq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfGI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfGI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMXW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMXW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHMY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHMY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qecj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qecj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwLV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwLV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoeL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoeL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZPm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZPm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxCw.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition CORE_POST (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
ld_live L1 = ld_live L /\ GP st0 (fst r) /\
match snd r with
| None => exists LS1, INVL x0 (fst r) L1 BL LS1
| Some (g, idx) => exists LS1 bg, let st1 := fst r in
hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
/\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
/\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
end.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

End CORE.

