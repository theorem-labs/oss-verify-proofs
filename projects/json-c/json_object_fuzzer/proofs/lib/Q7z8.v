(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
Import ListNotations.
Open Scope Z_scope.

Definition BUDGET_A : Z := 0x2100000000.
Definition TOT0_A : Z := 0x102002647000.
Definition N0_A : Z := 64.
Definition kPrimResLen : Z := 0x2000011000.
Definition kPtrArrLen : Z := 0x800000.

Definition band_lo : Z * Z := (0x7fff7000, 0x8fff7000).
Definition band_gap : Z * Z := (0x8fff7000, 0x2008fff7000).
Definition band_hi : Z * Z := (0x2008fff7000, 0x10007fff8000).
Definition CEIL : Z := 0x7fffff800000.

Definition PERM_main (pres parr : Z) (objs : list (Z * Z)) : list (Z * Z) :=
[(pres, pres + kPrimResLen); (parr, parr + kPtrArrLen); band_hi; band_lo; band_gap] ++ objs.

Definition avoid_main (pres parr : Z) (objs : list (Z * Z)) (bl : Z) : list (Z * Z) :=
[(pres, pres + kPrimResLen); (parr, parr + kPtrArrLen)] ++ objs ++ [(0x10000, 0x5e8000); (0x7fff7000, 0x10007fff8000); (bl, 2^64)].

Definition L_alloc (sb pres parr : Z) (objs : list (Z * Z)) (bl : Z) : ALay := mkALay sb parr (avoid_main pres parr objs bl).

Definition lowhigh (r : Z * Z) : Prop := snd r <= kLowEnd \/ kHighMemBeg <= fst r.

Definition objs_ok (objs : list (Z * Z)) : Prop :=
Forall (fun r => lowhigh r /\ 0 < fst r /\ fst r < snd r /\ snd r <= CEIL) objs.

Definition KI_main_stmt (LV : lvp) (sb pres parr : Z) (objs : list (Z * Z)) (bl : Z) (mo : Model) : Prop :=
ll_ok (L_alloc sb pres parr objs bl) LV BUDGET_A (PERM_main pres parr objs) TOT0_A N0_A /\
KI LV BUDGET_A (PERM_main pres parr objs) TOT0_A N0_A (mkG [] 0) mo.

Record main_addrs_ok (sb pres parr : Z) : Prop := mkMA {
ma_pres_lh : lowhigh (pres, pres + kPrimResLen);
ma_pres_lo : 0 < pres;
ma_pres_hi : pres + kPrimResLen <= CEIL;
ma_sb_al   : sb mod 65536 = 0;
ma_sb_lo   : pres <= sb;
ma_sb_hi   : sb + 2^37 <= pres + kPrimResLen;
ma_parr_lh : lowhigh (parr, parr + kPtrArrLen);
ma_parr_lo : 0 < parr;
ma_parr_al : parr mod 4096 = 0;
ma_parr_hi : parr + kPtrArrLen <= CEIL
}.

Definition lv_alloc_ok (LV : lvp) : Prop :=
lv_shoff LV = 0x7fff8000 /\ (forall x, In x (lv_excl LV) -> kLowEnd <= fst x /\ snd x <= kHighMemBeg)
/\ (forall y, kLowEnd <= y < kHighMemBeg -> in_zivs y (lv_excl LV) = true).

Lemma excl_entry_lowhigh LV (e : word * word) :
lv_alloc_ok LV -> bv_unsigned (fst e) + bv_unsigned (snd e) <= kLowEnd \/ kHighMemBeg <= bv_unsigned (fst e) ->
excl_entry LV e = false.
Proof.
intros (_ & Hx & _) He. apply (excl_entry_false LV). intros x Hin Hne Hsz. pose proof (Hx x Hin). lia.
Qed.

