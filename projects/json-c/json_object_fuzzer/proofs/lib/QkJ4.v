(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMSY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMSY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma hjunk_hdr : forall m a, hjunk m a (a + 16) ->
exists (b0 b1 : byte) (h w d : word), rw_cells asegs m a [C1 b0; C1 b1; C2 h; C4 w; C8 d].
Proof.
intros m a HJ. destruct (hjunk_cells m a 16 HJ) as [junk RC].
assert (LEN : length junk = 16%nat) by (destruct RC as [[[WF _] _] _]; cbn in WF; lia).
destruct junk as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 junk]]]]]]]]; try (cbn in LEN; lia).
exists x0, x1, (wz (bytes_le_to_Z [x2; x3])), (wz (bytes_le_to_Z [x4; x5; x6; x7])), (wz (bytes_le_to_Z junk)).
eapply rw_cells_recast'; [exact RC| cbn; tauto|].
cbn [cells_bytes cbytes app]. rewrite le2_of_bytes, le4_of_bytes, le8_of_bytes by (cbn in LEN |- *; lia). reflexivity.
Qed.

Definition hb1z (x : Z) : Z := Z.lor (Z.land (Z.lor (Z.land x 18446744073709551612) 1) 143) 16.
Definition hb1 (b : byte) : Z := hb1z (bv_unsigned b).
Definition hb1f (b : byte) : Z := Z.land (hb1 b) 243.

Lemma hb1_norm : forall b : byte,
bv_unsigned (wz (Z.lor (bv_unsigned (wz (Z.land (bv_unsigned (wz (Z.lor (bv_unsigned (wz (Z.land (bv_unsigned (zxb b)) 18446744073709551612))) 1))) 143))) 16))
= hb1 b.
Proof. intros b. unfold hb1, hb1z, zxb. zsimp. reflexivity. Qed.

Lemma hb1z_all : forallb (fun x => (hb1z x <? 256) && ((Z.land (hb1z x) 243 =? 17) || (Z.land (hb1z x) 243 =? 145))) (zrange 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hb1_facts : forall b, 0 <= hb1 b < 256 /\ (hb1f b = 0x11 \/ hb1f b = 0x91).
Proof.
intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
unfold hb1f, hb1. pose proof hb1z_all as H. rewrite forallb_forall in H.
specialize (H (bv_unsigned b) ltac:(apply in_zrange; cbn; lia)).
apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1.
split; [split; [unfold hb1z; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]| lia]| exact H1]|].
apply orb_prop in H2. destruct H2 as [H2|H2]; apply Z.eqb_eq in H2; [left| right]; exact H2.
Qed.

Lemma rt_avoid_depot_img {BAND : Band} : forall RE X, rlay_ok RE X -> rt_avoid RE X (SS_BASE, DP_END).
Proof.
intros RE X RL x [H1 H2] Fx. unfold SS_BASE, DP_END in *. cbn [fst snd] in H1, H2.
destruct (fp_RTconst_where RE X x Fx) as [L|(o & Ho & [O1 O2])].
- destruct Fx as [H|[H|[H|H]]].
+ destruct (rtconst_img_bounds x H); lia.
+ pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
+ pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
+ pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dtls_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
- pose proof (QSsj.rlay_obj_facts_lia RE X o RL Ho) as (_ & K & _). rewrite ?KHI_eq in K. lia.
Qed.

Lemma rt_avoid_dn {BAND : Band} : forall RE X, rlay_ok RE X -> rt_avoid RE X (rl_dn X, rl_dn X + 0x100000).
Proof.
intros RE X RL x [H1 H2] Fx. cbn [fst snd] in H1, H2.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 1 0 D12. pd_pair PD 2 1 D24.
destruct Fx as [H|[H|[H|H]]].
- destruct (rtconst_img_ok x H); lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
Qed.

Lemma rt_avoid_ssb {BAND : Band} : forall RE X, rlay_ok RE X -> rt_avoid RE X (rl_ssb X, rl_ssb X + 0x800000).
Proof.
intros RE X RL x [H1 H2] Fx. cbn [fst snd] in H1, H2.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 2 D03. pd_pair PD 1 1 D13. pd_pair PD 3 0 D34.
destruct Fx as [H|[H|[H|H]]].
- destruct (rtconst_img_ok x H); lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
- destruct H as [K1 K2]; cbn [fst snd] in K1, K2. lia.
Qed.

Lemma land_mask8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 281474976710648 = Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Ltac phase_done MU ma mb MUk WMk :=
let SF := fresh "SF" in let MU' := fresh "MU'" in
lazymatch type of MU with munch ?W ?m0 _ => lazymatch type of MUk with munch ?Wk _ _ =>
assert (SF : sub_fp Wk W) by sub_fp_solve;
pose proof (munch_chain W Wk m0 ma mb MU MUk SF) as MU'; clear MU SF; rename MU' into MU;
transport_after_call asegs ma mb MUk WMk; clear MUk WMk end end.

Ltac ctr H MU WM :=
lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]);
clear H; rename H' into H end end. Ltac mkr__ctr_1 H MU WM := lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]);
clear H; rename H' into H end end.

Ltac refold RE n c i AB H := try replace (class_of n) with c in H by reflexivity; try replace (slot_beg RE c i) with AB in H by reflexivity.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Local Ltac gl := first [lia| Z.div_mod_to_equations; lia].

Lemma geom : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof.
pose proof (class_of_facts n Hn HP) as (H1 & H2 & H3 & H4 & _). cbv zeta in H1, H2, H3, H4.
pose proof (rz_size_range n) as [R1 R2]. pose proof (needed_facts n Hn) as NF.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _). unfold prim_hi in PC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB. unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & CK & CC & CD & _). cbn [fst snd] in CK, CC. unfold iv_disjoint in CD. cbn [fst snd] in CD.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & ND & _). cbn [fst snd] in NK, NC. unfold iv_disjoint in ND. cbn [fst snd] in ND.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & BD & _). cbn [fst snd] in BK, BC. unfold iv_disjoint in BD. cbn [fst snd] in BD.
unfold prim_lo in *. rewrite ?KHI_eq in *. idtac.
subst c sz rz n' nd AB A. unfold used_size.
split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|].
split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|]. split; [gl|].
split; [gl|]. split; [gl|].
split; [exact TK|]. split; [gl|]. split; [gl|]. split; [gl|].
split; [exact CK|]. split; [gl|]. split; [gl|].
split; [exact NK|]. split; [gl|]. split; [gl|].
split; [exact BK|]. split; [gl| gl].
Qed.

End S.

Lemma fas_length : forall k, length (fas k) = Z.to_nat k.
Proof. intros k. unfold fas. apply repeat_length. Qed.

Lemma fas_app : forall a b, 0 <= a -> 0 <= b -> fas a ++ fas b = fas (a + b).
Proof. intros a b Ha Hb. unfold fas. rewrite <- repeat_app. f_equal. lia. Qed.

Lemma fas_split : forall m a N k, rw_cells asegs m a [CB (Z.to_nat N) (fas N)] -> 0 <= k <= N ->
rw_cells asegs m a [CB (Z.to_nat k) (fas k)] /\ rw_cells asegs m (a + k) [CB (Z.to_nat (N - k)) (fas (N - k))].
Proof.
intros m a N k H Hk.
assert (H' : rw_cells asegs m a ([CB (Z.to_nat k) (fas k)] ++ [CB (Z.to_nat (N - k)) (fas (N - k))])).
{ eapply rw_cells_recast'; [exact H| cbn; rewrite !fas_length; lia|].
cbn [cells_bytes cbytes app]. rewrite !app_nil_r. replace N with (k + (N - k)) at 2 by lia. apply fas_app; lia. }
apply (proj1 (rw_cells_app asegs m a _ _)) in H'. cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'.
replace (a + Z.of_nat (Z.to_nat k)) with (a + k) in H' by lia. exact H'.
Qed.

Lemma fas_one : forall m a, rw_cells asegs m a [CB (Z.to_nat 1) (fas 1)] -> rw_cells asegs m a [C1 fa_byte].
Proof. intros m a H. eapply rw_cells_recast'; [exact H| cbn; tauto| reflexivity]. Qed.

Lemma slot_pieces : forall m (AB sz rz n' : Z),
hjunk m AB (AB + sz) -> rw_cells asegs m (SH AB) [CB (Z.to_nat (sz / 8)) (fas (sz / 8))] ->
16 <= rz -> rz mod 16 = 0 -> AB mod 16 = 0 -> 1 <= n' -> rz + round_up n' 8 <= sz -> sz mod 8 = 0 ->
exists (b0 b1 : byte) (h w d g1 g2 : word),
rw_cells asegs m (AB + rz + -16) [C1 b0; C1 b1; C2 h; C4 w; C8 d]
/\ hjunk m (AB + rz) (AB + sz)
/\ hjunk m (AB + 16) (AB + rz + -16)
/\ (16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2])
/\ rw_cells asegs m (SH AB) [C1 fa_byte]
/\ rw_cells asegs m (SH AB + 1) [CB (Z.to_nat (rz / 8 - 1)) (fas (rz / 8 - 1))]
/\ (n' / 8 <> 0 -> rw_cells asegs m (SH (AB + rz)) [CB (Z.to_nat (n' / 8)) (fas (n' / 8))])
/\ (n' mod 8 <> 0 -> rw_cells asegs m (SH (AB + rz) + n' / 8) [C1 fa_byte])
/\ rw_cells asegs m (SH (AB + rz) + ngran n') [CB (Z.to_nat ((sz - rz - round_up n' 8) / 8)) (fas ((sz - rz - round_up n' 8) / 8))].
Proof.
intros m AB sz rz n' HJ SHD R1 R2 A16 N1 FIT S8.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
pose proof HJ as (LO & _ & _).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (Z.div_mod_to_equations; lia).
assert (SHA : SH (AB + rz) = SH AB + rz / 8) by (rewrite <- SH_plus8; f_equal; Z.div_mod_to_equations; lia).

destruct (hjunk_split _ _ (AB + rz) _ HJ ltac:(lia)) as [HJl HJu].
destruct (hjunk_split _ _ (AB + rz + -16) _ HJl ltac:(lia)) as [HJm HJh].
replace (AB + rz) with (AB + rz + -16 + 16) in HJh at 2 by lia. destruct (hjunk_hdr _ _ HJh) as (b0 & b1 & h & w & d & HDR).
assert (MG : exists g1 g2 : word, 16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2]).
{ destruct (Z.eq_dec rz 16) as [E|NE].
- exists (wz 0), (wz 0). intros; lia.
- assert (R32 : 32 <= rz) by (Z.div_mod_to_equations; lia).
destruct (hjunk_split _ _ (AB + 16) _ HJm ltac:(lia)) as [HJg _]. destruct (hjunk_C8x2 _ _ HJg) as (g1 & g2 & G). exists g1, g2. intros _; exact G. }
destruct MG as (g1 & g2 & MG).
assert (HJm' : hjunk m (AB + 16) (AB + rz + -16)) by (destruct HJm as (X1 & X2 & X3); split; [lia|]; split; [lia|]; intros z Hz; apply X3; lia).

destruct (fas_split _ _ _ 1 SHD ltac:(Z.div_mod_to_equations; lia)) as [P1 Q1]. apply fas_one in P1.
destruct (fas_split _ _ _ (rz / 8 - 1) Q1 ltac:(Z.div_mod_to_equations; lia)) as [R1' Q2].
replace (SH AB + 1 + (rz / 8 - 1)) with (SH (AB + rz)) in Q2 by lia.
destruct (fas_split _ _ _ (n' / 8) Q2 ltac:(Z.div_mod_to_equations; lia)) as [P2 Q3].
destruct (fas_split _ _ _ (ngran n' - n' / 8) Q3 ltac:(rewrite NG1; unfold round_up; Z.div_mod_to_equations; lia)) as [P3 Q4].
exists b0, b1, h, w, d, g1, g2.
split; [exact HDR|]. split; [exact HJu|]. split; [exact HJm'|]. split; [exact MG|]. split; [exact P1|]. split; [exact R1'|].
split; [intros _; exact P2|]. split.
- intros NZ. replace (ngran n' - n' / 8) with 1 in P3 by (rewrite NG1; unfold round_up; Z.div_mod_to_equations; lia). apply fas_one. exact P3.
- replace (SH (AB + rz) + n' / 8 + (ngran n' - n' / 8)) with (SH (AB + rz) + ngran n') in Q4 by lia.
replace (sz / 8 - 1 - (rz / 8 - 1) - n' / 8 - (ngran n' - n' / 8)) with ((sz - rz - round_up n' 8) / 8) in Q4
by (rewrite NG1; unfold round_up; Z.div_mod_to_equations; lia).
exact Q4.
Qed.

Lemma C1_CB_app : forall m a b n l, rw_cells asegs m a [C1 b] -> rw_cells asegs m (a + 1) [CB n l] ->
rw_cells asegs m a [CB (S n) (b :: l)].
Proof.
intros m a b n l H1 H2.
assert (H : rw_cells asegs m a ([C1 b] ++ [CB n l])).
{ apply (proj2 (rw_cells_app asegs m a [C1 b] [CB n l])). cbn [cells_size csize Nat.add]. split; assumption. }
destruct H2 as [[[L2 _] _] _]. cbn in L2.
eapply rw_cells_recast'; [exact H| cbn; lia| cbn; rewrite app_nil_r; reflexivity].
Qed.

Lemma ush_cells : forall m a n', 1 <= n' ->
(n' / 8 <> 0 -> rw_cells asegs m a [CB (Z.to_nat (n' / 8)) (repeat (b8 0) (Z.to_nat (n' / 8)))]) ->
(n' mod 8 <> 0 -> rw_cells asegs m (a + n' / 8) [C1 (b8 (n' mod 8))]) ->
0 <= a -> a + ngran n' <= 2^64 ->
rw_cells asegs m a [CB (Z.to_nat (ngran n')) (ush n')].
Proof.
intros m a n' N1 P2 P3 A0 A1.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (Z.div_mod_to_equations; lia).
unfold ush. destruct (Z.eqb_spec (n' mod 8) 0) as [Z0|NZ].
- assert (Q : n' / 8 <> 0) by lia. specialize (P2 Q). rewrite app_nil_r.
replace (ngran n') with (n' / 8) by (rewrite NG1; unfold round_up; Z.div_mod_to_equations; lia). exact P2.
- specialize (P3 NZ).
assert (NGE : ngran n' = n' / 8 + 1) by (rewrite NG1; unfold round_up; Z.div_mod_to_equations; lia).
destruct (Z.eq_dec (n' / 8) 0) as [Q0|QP].
+ rewrite Q0 in *. cbn [Z.to_nat repeat app]. rewrite NGE. cbn [Z.add Z.to_nat Pos.to_nat].
rewrite Z.add_0_r in P3. eapply rw_cells_recast'; [exact P3| cbn [cells_wf cell_wf]; rewrite length_app, repeat_length; cbn [length]; split; [lia| exact I]| cbn [cells_bytes cbytes Z.to_nat Z.add Pos.to_nat Pos.add repeat app]; reflexivity].
+ specialize (P2 QP).
assert (H : rw_cells asegs m a ([CB (Z.to_nat (n' / 8)) (repeat (b8 0) (Z.to_nat (n' / 8)))] ++ [C1 (b8 (n' mod 8))])).
{ apply (proj2 (rw_cells_app asegs m a _ _)). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
replace (a + Z.of_nat (Z.to_nat (n' / 8))) with (a + n' / 8) by lia. split; assumption. }
eapply rw_cells_recast'; [exact H| cbn; rewrite length_app, repeat_length; cbn; lia| cbn; rewrite app_nil_r; reflexivity].
Qed.

Lemma slot_chunk {BAND : Band} : forall m (AB sz n b1f : Z) (idw : word),
let rz := rz_size n in let n' := used_size n in let A := AB + rz in
0 <= n -> 16 <= rz -> rz mod 16 = 0 -> AB mod 16 = 0 -> rz + round_up n' 8 <= sz -> sz mod 8 = 0 ->
(lowhigh AB sz /\ off_hull AB sz) -> AB + sz <= band_lo -> (b1f = 0x11 \/ b1f = 0x91) ->
(16 < rz -> rw_cells asegs m AB [C8 (wz kMagic); C8 (wz (A + -16))]) -> hjunk m (AB + 16) (A + -16) ->
rw_cells asegs m (A + -16) [C1 (b8 2); C1 (b8 b1f); C2 (wz 0); C4 (wz n'); C8 idw] ->
hjunk m A (AB + sz) ->
rw_cells asegs m (SH AB) [C1 fa_byte] -> rw_cells asegs m (SH AB + 1) [CB (Z.to_nat (rz / 8 - 1)) (fas (rz / 8 - 1))] ->
(n' / 8 <> 0 -> rw_cells asegs m (SH A) [CB (Z.to_nat (n' / 8)) (repeat (b8 0) (Z.to_nat (n' / 8)))]) ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
rw_cells asegs m (SH A + ngran n') [CB (Z.to_nat ((sz - rz - round_up n' 8) / 8)) (fas ((sz - rz - round_up n' 8) / 8))] ->
chunk_mem m AB (AB + sz) A n.
Proof.
intros m AB sz n b1f idw rz n' A Hn R1 R2 A16 FIT S8 KAB CAB B1 MG HJm HDR HJU P1 Q1 P2 P3 R4.
pose proof (ngran_eq n' ltac:(subst n'; unfold used_size; lia)) as (NG1 & NG2 & NG3).
assert (N1 : 1 <= n' /\ n <= n') by (subst n'; unfold used_size; lia).
pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (Z.div_mod_to_equations; lia).
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH A = SH AB + rz / 8) by (subst A; rewrite <- SH_plus8; f_equal; Z.div_mod_to_equations; lia).
rewrite ?KHI_eq in KAB. idtac.
unfold chunk_mem. fold n'. split; [| split; [| split; [| split; [| split]]]].
- intros RZ. replace (AB + 16) with (AB + 16) by lia. split; [| replace (A - 16) with (A + -16) by lia; exact HJm].
replace (A - 16) with (A + -16) by lia. apply MG. subst A rz. lia.
- exists b1f, idw. split; [exact B1|]. replace (A - 16) with (A + -16) by lia. unfold hdr_cells. exact HDR.
- destruct (hjunk_split _ _ (A + n') _ HJU ltac:(subst A; lia)) as [HJ1 _].
replace (A + n') with (A + Z.of_nat (Z.to_nat n')) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
pose proof (proj2 UC) as WR. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r, Z2Nat.id in WR by lia. exact WR.
- destruct (hjunk_split _ _ (A + n) _ HJU ltac:(subst A; lia)) as [_ HJ2]. exact HJ2.
-
assert (S1 : rw_cells asegs m (SH AB) [CB (Z.to_nat ((A - AB) / 8)) (fas ((A - AB) / 8))]).
{ replace ((A - AB) / 8) with (rz / 8) by (subst A; f_equal; lia).
pose proof (C1_CB_app _ _ _ _ _ P1 Q1) as H. eapply rw_cells_recast'; [exact H| cbn; rewrite fas_length; Z.div_mod_to_equations; lia|].
cbn [cells_bytes cbytes app]. unfold fas. replace (Z.to_nat (rz / 8)) with (S (Z.to_nat (rz / 8 - 1))) by (Z.div_mod_to_equations; lia). reflexivity. }
assert (S2 : rw_cells asegs m (SH A) [CB (Z.to_nat (ngran n')) (ush n')]).
{ apply ush_cells; [lia| exact P2| exact P3| rewrite SHA, SHa; Z.div_mod_to_equations; lia| rewrite SHA, SHa, NG1; unfold round_up; Z.div_mod_to_equations; lia]. }
replace ((AB + sz - (A + round_up n' 8)) / 8) with ((sz - rz - round_up n' 8) / 8) by (subst A; f_equal; lia).
apply (proj2 (rw_cells_app asegs m (SH AB) [CB _ _] _)). split; [exact S1|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (SH AB + Z.of_nat (Z.to_nat ((A - AB) / 8))) with (SH A) by (rewrite SHA; subst A; Z.div_mod_to_equations; lia).
apply (proj2 (rw_cells_app asegs m (SH A) [CB _ _] _)). split; [exact S2|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (SH A + Z.of_nat (Z.to_nat (ngran n'))) with (SH A + ngran n') by lia. exact R4.
- rewrite ?KHI_eq. subst A rz n'. repeat split; first [lia| Z.div_mod_to_equations; lia].
Qed.
