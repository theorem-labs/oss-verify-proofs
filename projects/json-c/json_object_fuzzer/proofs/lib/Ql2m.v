(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.Riscv Require Fpu Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QZAi QdBa QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Fpu LinuxProcessSemantics.Riscv.Sem.
Import Qc3B.
Import QZAi.Mq1 QZAi QdBa QfYR. Unset Keyed Unification.
Open Scope Z_scope.

Section FinalK.
Variables (bits emin sign emax : Z) (bias0 : Z).

Definition fin_K3 (y frac bias e2 : Z) : option Z :=
let y := f128_add y frac in
let y := f128_sub y bias in
let '(y, e2) :=
if emax - 5 <? Z.land (u32 (e2 + LDBL_MANT_DIG_)) INT_MAX_ then
let ay := m_fabsl y in
let two := f128_of_i32 2 in
let lim := f128_div two C_LDBL_EPS in
if 0 <=? f128_ge ay lim then
let half := f128_of_d (bv_unsigned D_05) in
let y := f128_mul y half in (y, e2 + 1)
else (y, e2)
else (y, e2) in
Some (m_scalbnl y e2).

Definition fin_K2 (a z : Z) (x : list Z) (i bits' y frac bias e2 : Z) : option Z :=
let r :=
if negb (Z.land (a + i) MASK =? z) then
let t := znth x (Z.land (a + i) MASK) in
let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in
let od :=
if (t <? 500000000) && (nz t || negb (Z.land (a + i + 1) MASK =? z))
then Some (fmul_d RNE D_025 signd)
else if 500000000 <? t
then Some (fmul_d RNE D_075 signd)
else if t =? 500000000 then
(if Z.land (a + i + 1) MASK =? z
then Some (fmul_d RNE D_05 signd)
else Some (fmul_d RNE D_075 signd))
else None in
let frac := match od with
| Some d => let e := f128_of_d (bv_unsigned d) in f128_add frac e
| None => frac end in
if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl frac one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add frac C_ONE) else Some frac
end
else Some frac
else Some frac in
match r with
| None => None
| Some frac => fin_K3 y frac bias e2
end.

Definition fin_K1 (a z : Z) (x : list Z) (i y e2 : Z) : option Z :=
let sf := f128_of_i32 sign in
let y := f128_mul y sf in
let '(bits', denormal) :=
if LDBL_MANT_DIG_ + e2 - emin <? bits then
let b := LDBL_MANT_DIG_ + e2 - emin in ((if b <? 0 then 0 else b), 1)
else (bits, 0) in
let r :=
if bits' <? LDBL_MANT_DIG_ then
let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (2 * LDBL_MANT_DIG_ - bits' - 1) in
let t := f128_of_d (bv_unsigned d) in
let bias := m_copysignl t y in
let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (LDBL_MANT_DIG_ - bits') in
let t := f128_of_d (bv_unsigned d) in
match m_fmodl y t with
| None => None
| Some frac => Some (f128_add (f128_sub y frac) bias, frac, bias)
end
else Some (y, bias0, bias0) in
match r with
| None => None
| Some (y, frac, bias) => fin_K2 a z x i bits' y frac bias e2
end.

#[using="Type"] Lemma df_final_split : forall a z x e2,
df_final a z x e2 bits emin sign emax bias0 bias0 =
match df_asm_loop 5%nat a (mkAS 0 (f128_of_i32 0) z x) with
| None => None
| Some (mkAS i y z x) => fin_K1 a z x i y e2
end.
Proof.
intros a z x e2. unfold df_final, fin_K1, fin_K2, fin_K3.
destruct (df_asm_loop _ _ _) as [[i y z1 x1]|]; reflexivity.
Qed.

#[using="Type"] Lemma df_asm_loop_step : forall n a s,
df_asm_loop (S n) a s = if as_i s <? LD_B1B_DIG then df_asm_loop n a (df_asm_body a s) else Some s.
Proof. reflexivity. Qed.
End FinalK.
End Mq0.
From Stdlib Require NArith Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl Q7S0 Qfya Qatc QSfG QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya Qatc QSfG.Mq2 QdBa.Mq1 QpFQ.
Import ListNotations.
Local Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

#[using="Type"] Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [M1 M2 M3 M4 M5]; constructor.
- intros m Hm. rewrite !ME in *. apply M1. exact Hm.
- intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
- intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
- intros m Hm. rewrite HM. apply M4. exact Hm.
- intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

#[using="Type"] Lemma inv_L_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> (forall h, get_head st' h = get_head st h) ->
inv_L st LS -> inv_L st' LS.
Proof.
intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
- intros h. rewrite HE. apply L1.
- intros h. apply (dll_ext_metas st st' HM). apply L2.
- exact L3.
- exact L4.
- intros m. rewrite !ME. apply L5.
- intros m Hm. rewrite !ME. apply L6. exact Hm.
- intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
- exact L9.
Qed.

#[using="Type"] Lemma group_ok_ext m b ai : s_metas st' = s_metas st -> s_slots st' = s_slots st ->
(forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> fst b = rid -> s_regions st' !! rid = Some r) ->
group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
- intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
- intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

#[using="Type"] Lemma inv_S_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> s_slots st' = s_slots st ->
inv_S X st BL -> inv_S X st' BL.
Proof.
intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
- intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
- intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
- intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
- intros c Hc. rewrite HS. apply S4. exact Hc.
- exact S5.
- intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ.
Import ListNotations.
Local Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 :
hosts st b1 m1 -> hosts st b2 m2 -> 0 <= i1 <= m_last_idx (MR st m1) -> 0 <= i2 <= m_last_idx (MR st m2) ->
slot_start' (MR st m1) i1 = slot_start' (MR st m2) i2 -> m1 = m2 /\ i1 = i2.
Proof.
intros H1 H2 R1 R2 E.
pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

#[using="Type"] Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : 0 <= A' /\ 0 <= F'
/\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
/\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
/\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
/\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
let s := slot_start' (R g) i in
one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).

Hypothesis C_pend : pend' = x_pend X \/
((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
/\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.

#[using="Type"] Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
#[using="Type"] Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma fR_mem : m_mem (f (R g)) = m_mem (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_prev : m_prev (f (R g)) = m_prev (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_next : m_next (f (R g)) = m_next (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gbase : gbase (f (R g)) = gbase (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g). Proof. reflexivity. Qed.

#[using="Type"] Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_stride x : get_stride (R' x) = get_stride (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gend x : gend (R' x) = gend (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x). Proof. intros; rewrite R'_other; auto. Qed.
#[using="Type"] Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x). Proof. intros; rewrite R'_other; auto. Qed.

#[using="Type"] Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_shadow : s_shadow st' = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
#[using="Type"] Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
#[using="X ai pend' C_masks C_pend"] Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
split; [auto| intros _; discriminate].
Qed.

#[using="ai Hg"] Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

#[using="b ai INV Hg C_masks C_part C_pend C_rest C_unlisted C_under"] Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
assert (Gpres : s_metas st !! g <> None).
{ exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
split; [|split; [|split; [|split; [|split; [|split]]]]].
-  destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
-  destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
+ intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
destruct K as [K| ->].
* destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
* destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
* apply K. apply Hk. exact Hk2.
* apply Gpres. rewrite <- K. apply Hk. exact Hk2.
+ intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
rewrite R'_sc, R'_cnt. reflexivity.
-  destruct IM as [M1 M2 M3 M4 M5]; constructor.
+ intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
* exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
* apply M1. exact Hm.
+ intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
+ intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
+ intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
+ intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
-  destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
+ intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
+ intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
+ exact L3.
+ exact L4.
+ intros m. rewrite R'_next, R'_prev. apply L5.
+ intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
+ intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
+ exact L9.
-  destruct IG as [G1 G2 G3 G4 G5]; constructor.
+ intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
destruct (aptr_eqb_spec m g) as [->|NE].
*
pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
all: try (apply keys'; left; exact g_present).
all: try exact C_masks.
all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
all: try (intros NF Hsc NI; apply C_unlisted; assumption).
all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
all: try (intros NF Hsc Hs; apply C_under; assumption).
all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
all: match goal with |- ?g => idtac "REMAINS-G" g end.
* destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
all: try (apply keys'; left; assumption).
all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
all: match goal with |- ?g => idtac "REMAINS-O" g end.
+ intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
+ intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
+ intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
-  destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
+ intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
+ intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
+ intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
* rewrite fR_avail, fR_freed. apply C_part. exact Hi.
*
pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
{ intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
{ intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
+ intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
* apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
* destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
-  apply (inv_SH_view st st'); try reflexivity; try assumption.
+ apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.

End RC__1.
End Mq2.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 QWxq_c1.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
match fuel with
| O => munr
| S fuel' => mbind (body x) (fun s => match s with
| inl x' => mloop fuel' body x'
| inr r => mret r
end)
end.

#[using="Type"] Lemma mbind_mret : forall {A B} (a : A) (f : A -> M B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mbind_munr : forall {A B} (f : A -> M B) s, mbind (munr (A:=A)) f s = Ret Unr.
Proof. reflexivity. Qed.

Section Machine.
Variable segs : list Segment.

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

#[using="Type"] Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implM, mret. apply impl_ret_ok. exact H. Qed.

#[using="Type"] Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof. intros. unfold implM, munr. apply impl_ret_unr. Qed.

#[using="Type"] Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
implM m s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
implM (mbind m f) s Q ms.
Proof.
intros A B m f s Q1 Q ms Hm Hf. unfold implM, mbind in *.
eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

#[using="Type"] Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
intros A m s Q Q' ms H HQ. unfold implM in *. eapply impl_epost_mono; [exact H|].
intros [a s'] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_sys : forall {A} n (dec : resp -> option A) s Q ms,
evt segs (fun ms1 => at_node segs n ms1 /\
forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
implM (msys n dec) s Q ms.
Proof.
intros A n dec s Q ms H. unfold implM, msys. apply impl_enode.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp [a s'] E. cbn. specialize (Hk rsp).
destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

#[using="Type"] Lemma implM_get : forall s Q ms, evt segs (Q s s) ms -> implM mget s Q ms.
Proof. intros. unfold implM, mget. apply impl_ret_ok. exact H. Qed.
#[using="Type"] Lemma implM_put : forall s s' Q ms, evt segs (Q tt s') ms -> implM (mput s') s Q ms.
Proof. intros. unfold implM, mput. apply impl_ret_ok. exact H. Qed.
#[using="Type"] Lemma implM_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implM (mupd f) s Q ms.
Proof. intros. unfold implM, mupd. apply impl_ret_ok. exact H. Qed.

#[using="Type"] Lemma implM_evt : forall {A} (c : M A) s Q P ms,
evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof. intros A c s Q P ms H K. unfold implM in *. eapply impl_evt; eauto. Qed.

#[using="Type"] Lemma implM_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
implM (body x) s (fun r s' ms' => match r with
| inl x' => implM (mloop fuel body x') s' Q ms'
| inr v => evt segs (Q v s') ms'
end) ms ->
implM (mloop (S fuel) body x) s Q ms.
Proof.
intros X R fuel body x s Q ms H. cbn [mloop]. eapply implM_bind; [exact H|].
intros [x'|v] s' ms' H'; cbn in H'.
- exact H'.
- apply implM_ret. exact H'.
Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
End Mq3.

From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. Unset Keyed Unification.
Open Scope Z_scope.

Definition fmodl_scale (sx : Z) (st : Z * Z * Z) : Z :=
let '(xhi, xlo, ex) := st in
if ex <=? 0 then
let ux := mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor (ex + 120) sx) 0xffff) 48)) xlo in
f128_mul ux C_2PM120
else
mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor ex sx) 0xffff) 48)) xlo.

Definition fmodl_K2 (sx : Z) (st : Z * Z * Z) : option Z :=
match fmodl_norm_loop 130%nat st with
| None => None
| Some st' => Some (fmodl_scale sx st')
end.

Definition fmodl_fin (x yhi ylo : Z) (xhi xlo : Z) : (Z * Z) + Z :=
let hi := u64 (xhi - yhi) in
let lo := u64 (xlo - ylo) in
let hi := if xlo <? ylo then u64 (hi - 1) else hi in
if Z.shiftr hi 63 =? 0 then
if Z.lor hi lo =? 0 then inr (let t := f128_of_i32 0 in f128_mul t x)
else inl (hi, lo)
else inl (xhi, xlo).

Definition fmodl_K1 (x yhi ylo sx : Z) (res : (Z * Z * Z) + Z) : option Z :=
match res with
| inr v => Some v
| inl (xhi, xlo, ex) =>
match fmodl_fin x yhi ylo xhi xlo with
| inr v => Some v
| inl (xhi, xlo) => fmodl_K2 sx (xhi, xlo, ex)
end
end.

Lemma m_fmodl_split : forall x y,
m_fmodl x y =
let uxhi := hi64 x in let uxlo := lo64 x in
let uyhi := hi64 y in let uylo := lo64 y in
let ex := Z.land (Z.shiftr uxhi 48) 0x7fff in
let ey := Z.land (Z.shiftr uyhi 48) 0x7fff in
let sx := Z.land (Z.shiftr uxhi 48) 0x8000 in
let t := f128_of_i32 0 in
if (f128_le y t =? 0) || (m_fpclassifyl y =? 0) || (ex =? 0x7fff) then
let t := f128_mul x y in Some (f128_div t t)
else
let ux := mk128 (Z.land uxhi 0x7fffffffffffffff) uxlo in
let uy := mk128 (Z.land uyhi 0x7fffffffffffffff) uylo in
if f128_le ux uy <=? 0 then
if f128_le ux uy =? 0 then let t := f128_of_i32 0 in Some (f128_mul t x) else Some x
else
let '(ux, ex) := if ex =? 0 then
let ux := f128_mul ux C_2P120 in (ux, Z.shiftr (hi64 ux) 48 - 120) else (ux, ex) in
let '(uy, ey) := if ey =? 0 then
let uy := f128_mul uy C_2P120 in (uy, Z.shiftr (hi64 uy) 48 - 120) else (uy, ey) in
let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
let xlo := lo64 ux in
let ylo := lo64 uy in
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) x yhi ylo ey (xhi, xlo, ex) with
| None => None
| Some res => fmodl_K1 x yhi ylo sx res
end.
Proof.
intros x y. unfold m_fmodl. cbv zeta.
destruct (_ || _ || _); [reflexivity|].
destruct (f128_le _ _ <=? 0); [reflexivity|].
destruct (Z.land (Z.shiftr (hi64 x) 48) 32767 =? 0), (Z.land (Z.shiftr (hi64 y) 48) 32767 =? 0);
(destruct (fmodl_sub_loop _ _ _ _ _ _) as [[[[xhi xlo] ex]|v]|]; [|reflexivity|reflexivity]);
unfold fmodl_K1, fmodl_fin, fmodl_K2, fmodl_scale; cbv zeta;
(destruct (Z.shiftr _ 63 =? 0); [destruct (Z.lor _ _ =? 0); [reflexivity|]|]);
(destruct (fmodl_norm_loop _ _) as [[[xhi2 xlo2] ex2]|]; [|reflexivity]); destruct (ex2 <=? 0); reflexivity.
Qed.

Lemma fmodl_sub_loop_step : forall n x yhi ylo ey xhi xlo ex,
fmodl_sub_loop (S n) x yhi ylo ey (xhi, xlo, ex) =
if ey <? ex then
match fmodl_sub_body x yhi ylo (xhi, xlo, ex) with
| inl st' => fmodl_sub_loop n x yhi ylo ey st'
| inr r => Some (inr r)
end
else Some (inl (xhi, xlo, ex)).
Proof. reflexivity. Qed.

Lemma fmodl_norm_loop_step : forall n xhi xlo ex,
fmodl_norm_loop (S n) (xhi, xlo, ex) =
if Z.shiftr xhi 48 =? 0 then fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) else Some (xhi, xlo, ex).
Proof. reflexivity. Qed.

Section DecfloatK.
Variables (fuelc : nat) (bits emin sign pok : Z).
Let emax := - emin - bits + 3.
Let zero0 := f128_of_i32 0.

Definition dfK_dn (f : shfile) (rp a z e2 : Z) (x : list Z) : option (shfile * Z) :=
match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
| None => None
| Some (mkDS rp a z e2 x i) =>
match df_final a z x e2 bits emin sign emax zero0 zero0 with
| None => None
| Some y => Some (f, y)
end
end.

Definition dfK_up (f : shfile) (rp a z e2 : Z) (x : list Z) : option (shfile * Z) :=
match df_up_loop FUEL_SCALE (mkUS rp a z e2 x) with
| None => None
| Some (mkUS rp a z e2 x) => dfK_dn f rp a z e2 x
end.

Definition dfK_al (f : shfile) (rp z : Z) (x : list Z) : option (shfile * Z) :=
match (if nz (Z.rem rp 9) then
let rpm9 := if 0 <=? rp then Z.rem rp 9 else Z.rem rp 9 + 9 in
let p10 := znth p10s (8 - rpm9) in
match df_al_loop FUEL_RING p10 z (mkAL 0 0 rp 0 x) with
| None => None
| Some (mkAL _ a rp carry x) =>
let '(z, x) := if nz carry then (z + 1, zupd x z carry) else (z, x) in
Some (a, z, rp + (9 - rpm9), x)
end
else Some (0, z, rp, x)) with
| None => None
| Some (a, z, rp, x) => dfK_up f rp a z 0 x
end.

Definition dfK_tz (f : shfile) (rp k : Z) (x : list Z) : option (shfile * Z) :=
match df_tz_loop FUEL_RING x k with
| None => None
| Some z => dfK_al f rp z x
end.

Definition dfK_mid (f : shfile) (rp lnz k : Z) (x : list Z) : option (shfile * Z) :=
let x0 := znth x 0 in
match (if (lnz <? 9) && (lnz <=? rp) && (rp <? 18) then
if rp =? 9 then
Some (inr (f, f128_mul (f128_of_i32 sign) (f128_of_u32 x0)))
else if rp <? 9 then
Some (inr (f, f128_div (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (8 - rp)))))
else
let bitlim := bits - 3 * (rp - 9) in
if (30 <? bitlim) || (Z.shiftr x0 bitlim =? 0) then
Some (inr (f, f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10)))))
else Some (inl tt)
else Some (inl tt)) with
| None => None
| Some (inr r) => Some r
| Some (inl _) => dfK_tz f rp k x
end.

Definition dfK_pad (f : shfile) (lrp lnz j k : Z) (x : list Z) : option (shfile * Z) :=
match (if nz j then
match df_pad_loop 10%nat k (j, x) with
| None => None
| Some (j, x) => Some (k + 1, x)
end
else Some (k, x)) with
| None => None
| Some (k, x) => dfK_mid f (s32 lrp) lnz k x
end.

Definition dfK_rng (f : shfile) (lrp dc lnz j k : Z) (x : list Z) : option (shfile * Z) :=
let x0 := znth x 0 in
if x0 =? 0 then
Some (f, f128_of_d (bv_unsigned (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) D_ZERO)))
else if (lrp =? dc) && (dc <? 10) && ((30 <? bits) || (Z.shiftr x0 bits =? 0)) then
Some (f, f128_mul (f128_of_i32 sign) (f128_of_u32 x0))
else if Z.quot (- emin) 2 <? lrp then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MAX) C_LDBL_MAX)
else if lrp <? emin - 2 * LDBL_MANT_DIG_ then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MIN) C_LDBL_MIN)
else dfK_pad f lrp lnz j k x.

Definition dfK_exp (s : st_dig) : option (shfile * Z) :=
let 'mkDL f c j k lrp dc lnz gotdig gotrad x := s in
let lrp := if nz gotrad then lrp else dc in
match (if nz gotdig && (Z.lor c 32 =? 101) then
match scanexp fuelc f pok with
| None => None
| Some (f, e10) =>
if e10 =? LLONG_MIN_ then
if nz pok then Some (inl (sh_unget f, lrp + 0))
else Some (inr (sh_lim0 f, f128_of_i32 0))
else Some (inl (f, lrp + e10))
end
else Some (inl ((if 0 <=? c then sh_unget f else f), lrp))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, lrp)) =>
if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0)
else dfK_rng f lrp dc lnz j k x
end.

Definition dfK_dig (s : st_dig) : option (shfile * Z) :=
match df_dig_loop fuelc s with
| None => None
| Some s' => dfK_exp s'
end.

Definition dfK_rz (gotdig c : Z) (f : shfile) : option (shfile * Z) :=
match (if c =? 46 then
let '(c, f) := sh_getc f in
match df_rz_loop fuelc (gotdig, 0, c, f) with
| None => None
| Some (gotdig, lrp, c, f) => Some (gotdig, 1, lrp, c, f)
end
else Some (gotdig, 0, 0, c, f)) with
| None => None
| Some (gotdig, gotrad, lrp, c, f) =>
dfK_dig (mkDL f c 0 0 lrp 0 0 gotdig gotrad (zupd (zrepeat 0 KMAX) 0 0))
end.

#[using="Type"] Lemma decfloat_split : forall f c,
decfloat fuelc f c bits emin sign pok =
match df_lz_loop fuelc (0, c, f) with
| None => None
| Some (gotdig, c, f) => dfK_rz gotdig c f
end.
Proof.
intros f c. unfold decfloat, dfK_rz, dfK_dig, dfK_exp, dfK_rng, dfK_pad, dfK_mid, dfK_tz, dfK_al, dfK_up, dfK_dn.
subst emax zero0.
destruct (df_lz_loop _ _) as [[[gotdig c1] f1]|]; [|reflexivity].
destruct (if c1 =? 46 then _ else _) as [[[[[gd gr] lrp] c2] f2]|]; [|reflexivity].
destruct (df_dig_loop _ _) as [[f3 c3 j k lrp3 dc lnz gotdig3 gotrad3 x]|]; [|reflexivity].
cbv beta iota zeta.
destruct (if nz gotdig3 && _ then _ else _) as [[[f4 lrp4]|r]|]; [| reflexivity | reflexivity].
destruct (negb (nz gotdig3)); [reflexivity|].
destruct (znth x 0 =? 0); [reflexivity|].
destruct (_ && _ && _); [reflexivity|].
destruct (_ <? lrp4); [reflexivity|].
destruct (lrp4 <? _); [reflexivity|].
destruct (if nz j then _ else _) as [[k5 x5]|]; [|reflexivity].
cbv beta iota zeta.
destruct (if (lnz <? 9) && _ && _ then _ else _) as [[u|r]|]; [| reflexivity | reflexivity].
destruct (df_tz_loop _ _ _) as [z|]; [|reflexivity].
destruct (if nz (Z.rem _ 9) then _ else _) as [[[[a6 z6] rp6] x6]|]; [|reflexivity].
destruct (df_up_loop _ _) as [[rp7 a7 z7 e27 x7]|]; [|reflexivity].
destruct (df_dn_loop _ _) as [[rp8 a8 z8 e28 x8 i8]|]; [|reflexivity].
reflexivity.
Qed.
End DecfloatK.
