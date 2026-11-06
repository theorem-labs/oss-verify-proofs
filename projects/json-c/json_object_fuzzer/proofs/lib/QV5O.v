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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyFv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyFv.
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

Section WR.
Variables (st : mstate) (q : aptr) (v : Z).
Let st' := wr8 q v st.

End WR.

Definition xpend (X : extras) (p : option aptr) : extras := mkX (x_idle X) (x_zomb X) p (x_orph X) (x_fresh X).
Definition xorph (X : extras) (o : option N) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) o (x_fresh X).

Definition NTF_SPEC : Prop :=
forall (T : Type) (f : nat) X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
(1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
exists st' mi LS',
nontrivial_free dec_hdr f st g i k bail = k st' mi /\
match mi with
| None => INVL (xpend X None) st' L BL LS'
| Some (base, len) =>
exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len
/\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
end.

Section DROP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (r : region).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = Some rid.
Hypothesis Hr : s_regions st !! rid = Some r.
Let st' := drop_region rid st.
Let L' := Qgp5.set_groups (g_remove (r_base r) (ld_groups L)) L.
Let X' := xorph X None.

End DROP.

Section FREE.
Hypothesis NTF : NTF_SPEC.

End FREE.
