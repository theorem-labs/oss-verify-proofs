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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
cs_secret : c_secret c' = c_secret c;
cs_init : c_init_done c' = c_init_done c;
cs_fmh : c_free_meta_head c' = c_free_meta_head c;
cs_am : c_avail_meta c' = c_avail_meta c;
cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
cs_mah : c_meta_area_head c' = c_meta_area_head c;
cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
cs_active : c_active c' = c_active c;
cs_usage : c_usage c' = c_usage c;
cs_brk : c_brk c' = c_brk c;

cs_mc : 0 <= c_mmap_counter c' < 2^32;
cs_seq : 0 <= c_seq c' < 256;
cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.

End CTX.

Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.

End UNZOMBIE.
