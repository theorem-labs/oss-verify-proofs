(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ro_addr_range : forall a, 0 <= a < 2^64 -> ro_addr rsegs (wa a) = true -> 0x10000 <= a < 0x99000.
Proof.
intros a Ha H. destruct (Z.lt_ge_cases a 0x10000) as [L|G1]; [|destruct (Z.lt_ge_cases a 0x99000) as [L2|G2]; [lia|]];
exfalso; rewrite ref_ro_addr_false in H; [discriminate| rewrite wa_unsigned by lia; lia | discriminate | rewrite wa_unsigned by lia; lia].
Qed.

#[using="Type"] Lemma ro_bytes_range : forall a bs, ro_bytes rsegs a bs -> bs <> [] -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
0x10000 <= a /\ a + Z.of_nat (length bs) <= 0x99000.
Proof.
intros a bs RO NE Ha Hb. destruct bs as [|b0 bs']; [congruence|].
assert (E : exists bl, nth_error (b0 :: bs') (length bs') = Some bl).
{ destruct (nth_error (b0 :: bs') (length bs')) eqn:En; [eexists; reflexivity|]. apply nth_error_None in En. cbn in En. lia. }
destruct E as [bl Hbl].
pose proof (ro_bytes_nth rsegs _ _ _ _ RO Hbl) as [_ RL].
destruct RO as [[_ R0] _]. pose proof (ro_addr_range a ltac:(cbn in Hb; lia) R0).
pose proof (ro_addr_range (a + Z.of_nat (length bs')) ltac:(cbn in Hb; lia) RL).
cbn [length]. lia.
Qed.

#[using="Type"] Lemma src_cls_fresh_sep : forall (HIx : heap_iface S4L) A LB m md r n len SP s src,
HEAP S4L HIx A ((r, n) :: LB) m md ->
src_cls LB len SP s src -> Z.of_nat (length src) = len -> 0 <= s -> s + len <= 2^64 -> alloc_ceiling <= SP ->
len = 0 \/ s + len <= r \/ r + n <= s.
Proof.
intros HIx A LB m md r n len SP s src HP SCL SRCL Hs Hsl HSP.
pose proof (heap_blk S4L HIx _ _ _ _ r n HP ltac:(left; reflexivity)) as (Hn & _ & Hr0 & Hrhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r n HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
destruct (Z.eq_dec len 0) as [->|NZ]; [left; reflexivity| right].
destruct SCL as [[Ha|[Hst|(b & Hb & Hb1 & Hb2)]]|RO].
- right. unfold_consts. lia.
- pose proof (hl_static_in_img S4L _ (Hst s ltac:(lia))) as X1. pose proof (hl_static_in_img S4L _ (Hst (s + len - 1) ltac:(lia))) as X2.
cbn [hl_img_lo hl_img_hi S4L] in X1, X2. lia.
- destruct b as [ba bn]. cbn in Hb1, Hb2.
assert (Hne : r <> ba) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ bn HP Hb)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r n ba bn HP ltac:(left; reflexivity) ltac:(right; exact Hb) Hne). lia.
- destruct (ro_bytes_range s src RO ltac:(destruct src; [cbn in SRCL; lia|congruence]) Hs ltac:(lia)) as [R1 R2]. lia.
Qed.

#[using="Type"] Lemma src_cls_where : forall LB len SP s src,
src_cls LB len SP s src -> Z.of_nat (length src) = len -> 0 <= s -> s + len <= 2^64 ->
(forall HIx A LBc m md, HEAP S4L HIx A LBc m md -> (forall b, In b LB -> In b LBc) ->
len = 0 \/ SP <= s \/ s + len <= alloc_ceiling).
Proof.
intros LB len SP s src SCL SRCL Hs Hsl HIx A LBc m md HP SUB.
destruct (Z.eq_dec len 0) as [->|NZ]; [left; reflexivity| right].
destruct SCL as [[Ha|[Hst|(b & Hb & Hb1 & Hb2)]]|RO].
- left. lia.
- right. pose proof (hl_static_in_img S4L _ (Hst (s + len - 1) ltac:(lia))) as X2.
cbn [hl_img_lo hl_img_hi S4L] in X2. unfold_consts. lia.
- right. destruct b as [ba bn]. cbn in Hb1, Hb2.
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP (SUB _ Hb)) as (_ & _ & _ & Hhi & _). lia.
- right. destruct (ro_bytes_range s src RO ltac:(destruct src; [cbn in SRCL; lia|congruence]) Hs ltac:(lia)) as [R1 R2].
unfold_consts. lia.
Qed.

End RC__1.
