(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW QlEo_c1 QWxq_c1 Q5Rg Q6q3 QZAi QUZl Q7S0 Qfya Ql2m QGeV QkRc QSui QQIi QdTb Q1lV Qqcs Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO QPa2 QOb0 Qt4u Q6sh QvDJ QzgH QKTr Qqyb QNqr QeDS QGaR QwuX QCrt QgTJ QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi QdTb Q1lV.

Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QPa2 QOb0.Mq0 Qt4u.Mq0 Q6sh QvDJ QzgH QKTr.
Import Qqyb.Mq0.
Import QNqr QeDS QNqr.Mq0 QGaR QwuX QCrt.Mq0 QgTJ.Mq2 QCrt.Mq1 QCrt.Mq4.
Import QFL8.
Import ListNotations.
Open Scope Z_scope.

Module ON := QWxq_c1.Mq1.
Module OI := QlEo_c1.Mq0.
Module OD := Q5Rg.Mq0.
Module RC := Q6q3.
Module SM := QUZl.
Module ST := QZAi.Mq2.
Module KV := Qfya.
Module MG := QGeV.
Module MO := Ql2m.Mq3.
Module IR := QkRc.
Module MSU := QSui.

Lemma at_node_mmap_bridge : forall segs LV len ms,
ON.at_node segs (ON.NMmap 0 len 3 34) ms -> at_nodeA LV segs (NMmap 0 len QKTr.PROT_RW QKTr.FL_ANON) ms.
Proof.
intros segs LV len ms H. cbn [at_nodeA]. cbn [ON.at_node] in H. cbn [at_node].
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _). repeat split; assumption.
Qed.

Lemma at_node_munmap_bridge : forall segs LV a len ms,
ON.at_node segs (ON.NMunmap a len) ms -> sh_some LV (Z_to_bv 64 a) (rlenw len) (ms_mem ms) ->
at_nodeA LV segs (NMunmap a len) ms.
Proof.
intros segs LV a len ms H Hs. cbn [at_nodeA]. split; [|exact Hs]. cbn [ON.at_node] in H. cbn [at_node].
destruct H as (H1 & H2 & H3). repeat split; assumption.
Qed.

Lemma at_node_restrict : forall segs H n ms,
(exists len, n = ON.NMmap 0 len 3 34) \/ (exists a len, n = ON.NMunmap a len) ->
ON.at_node segs n (restrict H ms) -> ON.at_node segs n ms.
Proof. intros segs H n ms [[len ->]|(a & len & ->)] Hat; exact Hat. Qed.

Lemma round_up_pg_aligned : forall len, len mod 4096 = 0 -> SM.round_up_pg len = len.
Proof.
intros len H. unfold SM.round_up_pg, SM.PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
change (2 ^ 12) with 4096. rewrite (Z_mod_zero_opp_full len 4096 H). lia.
Qed.

Lemma zrange_In : forall k lo z, In z (zrange lo k) <-> lo <= z < lo + Z.of_nat k.
Proof.
induction k as [|k IH]; intros lo z; cbn [zrange In]; [lia|]. rewrite IH. lia.
Qed.

Section MembedVj.
Context {RC__ : RC.RunConsts}.
Variable segs : list Segment.
Variable LA : ALay.
Variable LV : lvp.

Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Hypothesis LL0 : ll_ok LA LV 0 PERM0 TMAX NMAX.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Hypothesis Hbase47 : forall iv, In iv (lv_base LV) -> 0 <= fst iv /\ snd iv <= 2^47.

Definition in_sh (b l : Z) (x : word) : bool := (sh_lo b <=? bv_unsigned x) && (bv_unsigned x <? sh_hi b (mmap_len l)).
Definition grp_add (x len : Z) (Lg : KV.mled) : KV.mled := KV.set_groups ((x, len) :: KV.ld_groups Lg) Lg.
Definition rsp0_grant (x len : Z) : resp := mkEffectU (Z_to_bv 64 x) [] [(Z_to_bv 64 x, Z_to_bv 64 (mmap_len len))] [] [] [].

Lemma in_sh_bounds : forall b l y, 0 <= b -> 0 < mmap_len l -> b + mmap_len l <= kCeil -> in_sh b l y = true ->
kLowEnd < bv_unsigned y < KHI.
Proof.
intros b l y Hb Hl Hc H. unfold in_sh in H. apply andb_prop in H as [H1 H2']. apply Z.leb_le in H1. apply Z.ltb_lt in H2'.
unfold sh_lo, sh_hi, kShadowOffset in *. rewrite kCeil_val in Hc. unfold kLowEnd, KHI.
assert (0 <= b / 8) by (apply Z.div_pos; lia).
assert ((b + mmap_len l - 1) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in *. unfold Qqcs.Mq0.kHighMemBeg. lia.
Qed.

Definition ev_supp (e : SM.ev) : Prop :=
match e with
| SM.EMmap a len prot flags => a = 0 /\ prot = 3 /\ flags = 34 /\ 0 < len /\ len mod 4096 = 0 /\ len <= kMaxChunk
| SM.EMunmap a len => True
| _ => False
end.
Definition is_grant (e : SM.ev) : bool := match e with SM.EMmap _ _ _ _ => true | _ => false end.

Fixpoint tree_supp {R} (Lg : KV.mled) (t : ST.stree SM.ev Z R) (N : nat) : Prop :=
match t with
| ST.SRet _ => True
| ST.SVis e k => ev_supp e /\
(if is_grant e then exists N', N = S N' /\ forall z, KV.answer_ok Lg e z = true -> tree_supp (KV.event_post Lg e z) (k z) N'
else forall z, KV.answer_ok Lg e z = true -> tree_supp (KV.event_post Lg e z) (k z) N)
end.

Lemma tree_supp_of_tsyn : forall {R} (P : R -> Prop) (t : ST.stree SM.ev Z R) Lg N Post,
MSU.tsynP P t N -> KV.ctree_ok Lg t Post -> tree_supp Lg t N.
Proof.
intros R P. induction t as [r|e k IH]; intros Lg N Post HS HC; [exact I|].
cbn [MSU.tsynP] in HS. destruct HS as [He HS]. cbn [KV.ctree_ok] in HC. destruct HC as [PRE HC]. cbn [tree_supp].
destruct e as [req|a len prot flags|a len|a len prot|p0 c0 h0|w|a ol nl fl]; cbn [MSU.esyn] in He; try (destruct He; fail);
try (cbn [KV.event_pre] in PRE; destruct PRE; fail).
-
destruct He as (Hprot & Hfix & Hmod & Hlen). cbn [MSU.is_mmap] in HS. destruct HS as (N' & -> & HS).
cbn [KV.event_pre] in PRE. split.
+ destruct PRE as [(_ & -> & -> & _ & _)|(cur & _ & _ & _ & _ & ->)].
* cbn [ev_supp]. unfold SM.PROT_RW in Hprot. unfold kMaxChunk. repeat split; try assumption; try reflexivity; lia.
* exfalso. revert Hfix. unfold KV.MAPFX, SM.MAP_PRIVATE, SM.MAP_ANON, SM.MAP_FIXED. cbn. discriminate.
+ cbn [is_grant]. exists N'. split; [reflexivity|]. intros z Hz. eapply IH; [apply HS| apply HC; exact Hz].
-
cbn [MSU.is_mmap] in HS. split; [exact I|]. cbn [is_grant]. intros z Hz. eapply IH; [apply HS| apply HC; exact Hz].
Qed.

Corollary cmalloc_tree_supp : forall cs n Lg Post,
25 <= MSU.cntm cs -> 0 <= n < SM.MMAP_THRESHOLD ->
KV.ctree_ok Lg (SM.cmalloc cs n) Post -> tree_supp Lg (SM.cmalloc cs n) 1.
Proof. intros cs n Lg Post Hc Hn HC. exact (tree_supp_of_tsyn _ _ Lg 1%nat Post (MSU.tsyn_cmalloc cs n Hc Hn) HC). Qed.

Corollary cfree_tree_supp : forall cs p Lg Post,
KV.ctree_ok Lg (SM.cfree cs p) Post -> tree_supp Lg (SM.cfree cs p) 0.
Proof. intros cs p Lg Post HC. exact (tree_supp_of_tsyn _ _ Lg 0%nat Post (MSU.tsyn_cfree cs p) HC). Qed.

Definition oranges (Lg : KV.mled) : list (Z * Z) :=
KV.ld_resv Lg ++ map (fun m => (fst (fst m), SM.round_up_pg (snd (fst m)))) (KV.ld_metas Lg)
++ match KV.ld_brkreg Lg with Some (b, l) => [(b + SM.PGSZ, SM.round_up_pg l - SM.PGSZ)] | None => [] end.

Lemma lranges_split : forall Lg r, In r (KV.lranges Lg) ->
(exists b l, In (b, l) (KV.ld_groups Lg) /\ r = (b, SM.round_up_pg l)) \/ In r (oranges Lg).
Proof.
intros Lg r H. unfold KV.lranges, oranges in *. apply in_app_iff in H as [H|H]; [right; apply in_app_iff; left; exact H|].
apply in_app_iff in H as [H|H]; [|right; apply in_app_iff; right; exact H].
left. apply in_map_iff in H as ([b l] & <- & Hin). exists b, l. split; [exact Hin| reflexivity].
Qed.

Lemma mmap_len_aligned : forall l, l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l H. rewrite mmap_len_rlen. apply rlen_aligned. exact H. Qed.

Lemma g_remove_In : forall a l gs b l',
List.NoDup (map fst gs) -> In (a, l) gs -> In (b, l') (KV.g_remove a gs) -> In (b, l') gs /\ b <> a.
Proof.
induction gs as [|[y ly] gs IH]; intros b l' ND Hin Hb; [destruct Hb|].
cbn [map fst] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
cbn [KV.g_remove fst] in Hb. destruct (Z.eqb_spec y a) as [->|Ne].
- split; [right; exact Hb|]. intros ->. apply Hny. apply in_map_iff. exists (a, l'). split; [reflexivity| exact Hb].
- destruct Hin as [E|Hin]; [injection E as -> _; contradiction|].
destruct Hb as [E|Hb]; [injection E as <- <-; split; [left; reflexivity| exact Ne]|].
destruct (IH b l' NDl Hin Hb) as [H1 H2']. split; [right; exact H1| exact H2'].
Qed.

Lemma g_remove_nodup : forall a gs, List.NoDup (map fst gs) -> List.NoDup (map fst (KV.g_remove a gs)).
Proof.
induction gs as [|[y ly] gs IH]; intros ND; [constructor|]. cbn [map fst] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
cbn [KV.g_remove fst]. destruct (y =? a); [exact NDl|]. cbn [map fst]. constructor; [| apply IH; exact NDl].
intros Hin. apply Hny. apply in_map_iff in Hin as ([b l'] & Eb & Hb). cbn [fst] in Eb. subst b.
clear IH ND Hny. induction gs as [|[z lz] gs IHg]; [destruct Hb|]. cbn [KV.g_remove fst] in Hb. cbn [map fst].
inversion NDl as [|z0 l0 Hnz NDg]; subst.
destruct (z =? a); [right; apply in_map_iff; exists (y, l'); split; [reflexivity| exact Hb]|].
destruct Hb as [E|Hb]; [injection E as -> _; left; reflexivity| right; apply IHg; assumption].
Qed.

Lemma in_sh_shadow_iv : forall a l y, 0 <= a -> 0 < l -> l mod 4096 = 0 -> a + l <= kCeil ->
(In y (bytes_of (shadow_iv LV (w64 a) (rlenw l))) <-> in_sh a l y = true).
Proof.
intros a l y Ha Hl Hal Hc. rewrite (bytes_of_shadow LV Hsh). rewrite kCeil_val in Hc.
unfold shadow_iv, sh_iv, wiv2z, shz, zin, in_sh, sh_lo, sh_hi. cbn [fst snd].
rewrite (llo_shoff _ _ _ _ _ _ LL0), (rlenw_w64 l Hal), (mmap_len_aligned l Hal), !u_w64 by lia. reflexivity.
Qed.

Definition PERMc (Lg : KV.mled) : list (Z * Z) := map civ (KV.ld_groups Lg) ++ PERM0.

Definition ocov (h : VmMaps) (r : Z * Z) : Prop :=
exists e, (In e (vm_reserved h) \/ exists p, In p PERM0 /\ e = z2w p)
/\ bv_unsigned (fst e) <= fst r /\ fst r + snd r <= bv_unsigned (fst e) + bv_unsigned (snd e).

Definition gstatic (b l : Z) : Prop :=
l mod 4096 = 0 /\ 0 < l <= kMaxChunk /\ 0 < b /\ b mod 4096 = 0 /\ (b + l <= kLowEnd \/ KHI <= b) /\ b + l <= kCeil /\
excl_entry LV (cent (b, l)) = false /\
(forall iv y, In iv (lv_base LV) -> b <= y < b + l -> ~ (fst iv <= y < snd iv) /\ ~ (fst iv <= shz LV y < snd iv)) /\
~ In (civ (b, l)) PERM0.

Variable GH : word -> bool.
Hypothesis GH_off : H_off_segments segs GH.
Definition HG (H : word -> bool) : word -> bool := fun y => H y || GH y.

Definition in_grp (Lg : KV.mled) (y : word) : bool :=
existsb (fun bl : Z * Z => (fst bl <=? bv_unsigned y) && (bv_unsigned y <? fst bl + snd bl)) (KV.ld_groups Lg).

Record KLA (Lg : KV.mled) (g : ghost) (c : config) (H : word -> bool) (m : word -> option byte) (B T N : Z) : Prop := mkKLA {
kla_ki : KI LV B (PERMc Lg) T N g (cfg_model c);
kla_par : 0 <= B /\ zsum (map snd (KV.ld_groups Lg)) <= T <= TMAX /\ zlen (KV.ld_groups Lg) <= N <= NMAX;
kla_cinv : cinvA LV (cfg_ms c) (cfg_model c);
kla_halt : m_halted (cfg_model c) = None;
kla_top : alloc_top (m_vmmaps (cfg_model c)) = RC.alloc_ceiling;
kla_groups : forall b l, In (b, l) (KV.ld_groups Lg) -> gstatic b l;
kla_cov : forall r, In r (oranges Lg) -> ocov (m_vmmaps (cfg_model c)) r;
kla_nodup : List.NoDup (map fst (KV.ld_groups Lg));
kla_Hrange : forall y, H y = true -> kLowEnd < bv_unsigned y < KHI;
kla_Hmem : forall y, H y = true -> m y <> None;
kla_Hsh : forall b l y, In (b, l) (KV.ld_groups Lg) -> in_sh b l y = true -> H y = true;
kla_Hex : forall y, H y = true -> exists b l, In (b, l) (KV.ld_groups Lg) /\ in_sh b l y = true;
kla_G : forall y, GH y = true -> m y <> None /\ in_grp Lg y = false /\ H y = false
}.

Lemma in_grp_true : forall Lg y, in_grp Lg y = true <-> exists b l, In (b, l) (KV.ld_groups Lg) /\ b <= bv_unsigned y < b + l.
Proof.
intros Lg y. unfold in_grp. rewrite existsb_exists. split.
- intros ([b l] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2']. apply Z.leb_le in H1. apply Z.ltb_lt in H2'.
exists b, l. split; [exact Hin| lia].
- intros (b & l & Hin & Hb). exists (b, l). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma in_grp_false : forall Lg y b l, in_grp Lg y = false -> In (b, l) (KV.ld_groups Lg) -> ~ (b <= bv_unsigned y < b + l).
Proof.
intros Lg y b l Hf Hin Hb. assert (Ht : in_grp Lg y = true) by (apply in_grp_true; exists b, l; auto). congruence.
Qed.

Lemma z2w_civ : forall c, z2w (civ c) = cent c.
Proof. intros c. unfold z2w, civ, cent. cbn [fst snd]. replace (fst c + snd c - fst c) with (snd c) by lia. reflexivity. Qed.

Lemma groups_zsum_nonneg : forall gs, (forall b l, In (b, l) gs -> gstatic b l) -> 0 <= zsum (map snd gs).
Proof.
induction gs as [|[b l] gs IH]; intros Hg; [cbn; lia|]. cbn [map snd]. rewrite zsum_cons.
destruct (Hg b l (or_introl eq_refl)) as (_ & Hl & _). specialize (IH (fun b' l' Hin => Hg b' l' (or_intror Hin))). lia.
Qed.

Lemma g_remove_sums : forall a l gs, List.NoDup (map fst gs) -> In (a, l) gs ->
zsum (map snd (KV.g_remove a gs)) = zsum (map snd gs) - l /\ zlen (KV.g_remove a gs) = zlen gs - 1.
Proof.
induction gs as [|[y ly] gs IH]; intros ND Hin; [destruct Hin|]. cbn [map fst] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
cbn [KV.g_remove fst]. destruct (Z.eqb_spec y a) as [->|Ne].
- destruct Hin as [E|Hin]; [injection E as ->| exfalso; apply Hny; apply in_map_iff; exists (a, l); split; [reflexivity| exact Hin]].
cbn [map snd]. rewrite zsum_cons, zlen_cons. lia.
- destruct Hin as [E|Hin]; [injection E as -> _; contradiction|]. destruct (IH NDl Hin) as [I1 I2].
cbn [map snd]. rewrite !zsum_cons, !zlen_cons, I1, I2. lia.
Qed.

Lemma g_remove_In_conv : forall a gs b l', In (b, l') gs -> b <> a -> In (b, l') (KV.g_remove a gs).
Proof.
induction gs as [|[y ly] gs IH]; intros b l' Hin Hne; [destruct Hin|]. cbn [KV.g_remove fst].
destruct (Z.eqb_spec y a) as [->|Ne]; [destruct Hin as [E|Hin]; [injection E as <- _; contradiction| exact Hin]|].
destruct Hin as [E|Hin]; [left; exact E| right; apply IH; assumption].
Qed.

Lemma KLA_ll : forall Lg g c H m B T N, KLA Lg g c H m B T N -> ll_ok LA LV B (PERMc Lg) T N.
Proof.
intros Lg g c H m B T N KL. destruct (kla_par _ _ _ _ _ _ _ _ KL) as (HB & [HT1 HT2] & [HN1 HN2]).
pose proof (groups_zsum_nonneg _ (kla_groups _ _ _ _ _ _ _ _ KL)) as Hz.
assert (0 <= zlen (KV.ld_groups Lg)) by (unfold zlen; lia).
unfold PERMc. apply (ll_ok_ext LA LV 0 PERM0 TMAX NMAX B _ T N LL0 HB); [| lia| lia].
intros r Hr. apply in_map_iff in Hr as ([b l] & <- & Hin). destruct (kla_groups _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
unfold civ. cbn [fst snd]. lia.
Qed.

Lemma KLA_group_map : forall Lg g c H m B T N b l, KLA Lg g c H m B T N -> In (b, l) (KV.ld_groups Lg) ->
In (cent (b, l)) (vm_maps (m_vmmaps (cfg_model c))) /\ bv_unsigned (w64 b) = b /\ bv_unsigned (w64 l) = l.
Proof.
intros Lg g c H m B T N b l KL Hin. destruct (kla_groups _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
rewrite kCeil_val in G6. unfold kMaxChunk in G2.
assert (Hp : In (civ (b, l)) (PERMc Lg)) by (unfold PERMc; apply in_app_iff; left; apply in_map; exact Hin).
destruct (ki_perm LV B (PERMc Lg) T N _ _ (kla_ki _ _ _ _ _ _ _ _ KL) _ Hp) as (P1 & _). rewrite z2w_civ in P1.
split; [exact P1|]. split; apply u_w64; lia.
Qed.

Lemma sh_disjoint : forall a l b l' y, a mod 4096 = 0 -> l mod 4096 = 0 -> 0 < l -> b mod 4096 = 0 -> l' mod 4096 = 0 -> 0 < l' ->
(a + l <= b \/ b + l' <= a) -> in_sh a l y = true -> in_sh b l' y = true -> False.
Proof.
intros a l b l' y A1 A4 A2 B1 B4 B2 Hd Hy1 Hy2.
unfold in_sh, sh_lo, sh_hi in Hy1, Hy2. rewrite (mmap_len_aligned l A4) in Hy1. rewrite (mmap_len_aligned l' B4) in Hy2.
apply andb_prop in Hy1 as [P1 P2]. apply andb_prop in Hy2 as [Q1 Q2].
apply Z.leb_le in P1, Q1. apply Z.ltb_lt in P2, Q2.
clear - A1 A4 B1 B4 Hd P1 P2 Q1 Q2 A2 B2. Z.div_mod_to_equations. lia.
Qed.

Lemma KLA_groups_disjoint : forall Lg g c H m B T N a l b l', KLA Lg g c H m B T N ->
In (a, l) (KV.ld_groups Lg) -> In (b, l') (KV.ld_groups Lg) -> a <> b -> a + l <= b \/ b + l' <= a.
Proof.
intros Lg g c H m B T N a l b l' KL Ha Hb Hne.
destruct (KLA_group_map _ _ _ _ _ _ _ _ a l KL Ha) as (Ma & Ua & Ul).
destruct (KLA_group_map _ _ _ _ _ _ _ _ b l' KL Hb) as (Mb & Ub & Ul').
assert (Hp : In (civ (b, l')) (PERMc Lg)) by (unfold PERMc; apply in_app_iff; left; apply in_map; exact Hb).
destruct (ki_perm LV B (PERMc Lg) T N _ _ (kla_ki _ _ _ _ _ _ _ _ KL) _ Hp) as (_ & P2 & _).
destruct (P2 _ Ma) as [E|D].
- exfalso. rewrite z2w_civ in E. apply Hne.
assert (E2 : bv_unsigned (fst (cent (a, l))) = bv_unsigned (fst (cent (b, l')))) by (rewrite E; reflexivity).
unfold cent in E2. cbn [fst snd] in E2. rewrite Ua, Ub in E2. exact E2.
- unfold zdisj, wiv2z, cent, civ in D. cbn [fst snd] in D. rewrite Ua, Ul in D. lia.
Qed.

Lemma appcov_bound : forall B P T N g mo y, KI LV B P T N g mo -> appcov LV mo y = true -> 0 <= y < 2^47.
Proof.
intros B P T N g mo y K Hc. unfold appcov in Hc. apply orb_prop in Hc as [Hc|Hc].
- unfold bcov, in_zivs in Hc. apply existsb_exists in Hc as (iv & Hiv & Hz). apply zin_true in Hz.
destruct (Hbase47 iv Hiv). lia.
- unfold ecov, emaps in Hc. apply covered_true in Hc as (e & He & Hr). apply filter_In in He as [He _].
pose proof (ki_x LV B P T N g mo K) as [_ (_ & _ & [Ht Hb])]. specialize (Hb e He).
pose proof (bv_unsigned_in_range _ (fst e)). unfold grant_ceilA, sp_window_hi, stack_max_size in Ht. lia.
Qed.

Lemma fresh_hidden : forall B P T N g mo (a : word) len, ll_ok LA LV B P T N -> KI LV B P T N g mo ->
0 < len -> len < 2^64 ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (w64 len) = true ->
bv_unsigned a + len <= alloc_top (m_vmmaps mo) -> (bv_unsigned a + len <= kLowEnd \/ KHI <= bv_unsigned a) ->
forall y : word, bv_unsigned a <= bv_unsigned y < bv_unsigned a + len -> hidden LV mo y = true.
Proof.
intros B P T N g mo a len LLx K Hlen Hl64 Hfree Htop Hpl y Hy.
assert (Hul : bv_unsigned (w64 len) = len) by (apply u_w64; lia).
apply hidden_iff. split.
- apply (fresh_range_uncovered LV mo (vm_reserved (m_vmmaps mo)) a (w64 len) Hfree); [| rewrite Hul; exact Hy].
apply (fresh_off_base LA LV B P T N LLx g mo a (w64 len) K); [rewrite Hul; exact Hlen| exact Hfree| rewrite Hul; exact Htop].
- intros y' Hc Hs. pose proof (appcov_bound B P T N g mo y' K Hc) as Hb.
pose proof (shz_in_band LA LV B P T N LLx y' Hb) as Hband. lia.
Qed.

Variable J : config -> Prop.
Hypothesis J_nclosed : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, J (nx i)) -> J c.

Lemma step_mmap : forall Lg g c H ms1 len B T N,
KLA Lg g c H (ms_mem ms1) B T N ->
0 < len -> len mod 4096 = 0 -> len <= kMaxChunk ->
g_spent g + sec_cost len <= B -> zlen (g_chunks g) + 1 <= kMaxCnt -> T + len <= TMAX -> N + 1 <= NMAX ->
ON.at_node segs (ON.NMmap 0 len 3 34) (restrict (HG H) ms1) ->
(forall x msv' c' H',
OD.dec_mmap len [] (rsp0_grant x len) = Some (OD.MmOk x) ->
SM.mmap_answer_ok (KV.lranges Lg) len x = true -> SM.is_err x = false ->
restrict (HG H') msv' = OI.nret (restrict (HG H) ms1) (rsp0_grant x len) ->
KLA (grp_add x len Lg) g c' H' (ms_mem msv') (B - sec_cost len) (T + len) (N + 1) ->
(forall y, GH y = true -> ms_mem msv' y = ms_mem ms1 y) ->
(forall y, ms_mem msv' y <> None -> ms_mem ms1 y <> None \/ x <= bv_unsigned y < x + len \/ (H' y = true /\ H y = false)) ->
(forall y, H y = true -> H' y = true) ->
vm_onlyA (cfg_model c) (cfg_model c') -> vmst (cfg_model c) (cfg_model c') ->
VJ LV J c' msv') ->
VJ LV J c ms1.
Proof.
intros Lg g c H ms1 len B T N KL Hlen Hmod Hmax Hbud Hcnt HTm HNm Hat HK msR moR HrelR.
pose proof (KLA_ll _ _ _ _ _ _ _ _ KL) as LLc. pose proof (kla_ki _ _ _ _ _ _ _ _ KL) as K.
set (avoid := al_avoid LA ++ map civ (g_chunks g)).
assert (G : gev LA B g (EvMapAnon len avoid)).
{ cbn [gev]. split; [exact Hlen|]. split; [exact Hmod|]. split; [exact Hmax|]. split; [apply incl_refl|].
split; [apply incl_appr, incl_refl|]. split; assumption. }
refine (vj_ev segs LA LV B (PERMc Lg) T N LLc Hwx Hsegs Hsh Hbx Hbc J J_nclosed (EvMapAnon len avoid) g c ms1 _ (kla_cinv _ _ _ _ _ _ _ _ KL) K G _ msR moR HrelR).
{ cbn [node_of]. apply at_node_mmap_bridge. eapply at_node_restrict; [left; eexists; reflexivity| exact Hat]. }
intros rsp ans c1 mo1 Hd Hr Hdec Hok K' HC1 Hh1.
pose proof (KI_drift LV B (PERMc Lg) T N g _ _ Hd K) as K1.
pose proof (vm_onlyA_trans _ _ _ (vm_onlyA_drift LV _ _ Hd) (vm_onlyA_nstep_raw LA LV B (PERMc Lg) T N LLc g mo1 _ rsp _ [] K1 G Hr)) as HVO.
assert (HVS : vmst (cfg_model c) (cfg_model c1)).
{ pose proof (drift_frame LV _ _ Hd) as (_ & _ & _ & _ & _ & Hvm0 & _).
destruct (nstep_raw_vmst LV _ mo1 rsp _ [] (node_of_mm _) Hr) as [V1 V2]. split; rewrite <- Hvm0; assumption. }
cbn [node_of] in Hr.
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON anon_place_ok grant_model rsp_grant reveal wunit rlenw rlen] in Hr.
rewrite kind_anon in Hr. destruct Hr as [_ (a & ws & Hpl & Hrev & Hwu & Hmo & ->)].
rewrite (rlen_aligned len Hmod) in Hpl. rewrite (rlenw_w64 len Hmod) in *.
cbn [dec_of] in Hdec.
destruct ans as [|x]; [apply dec_anonA_err_inv in Hdec; discriminate|].
destruct (dec_anonA_ok_inv len avoid _ x Hdec) as (ws' & Hrsp & Hx & Hgo & Hav & Hws & Hcov).
unfold rsp_grant in Hrsp. injection Hrsp as Ea Ews. subst ws'. cbn [eff_ret rsp_grant] in Hx.
assert (Hml : mmap_len len = len) by (apply mmap_len_aligned; exact Hmod).
rewrite Hml in *.
pose proof (drift_frame LV _ _ Hd) as (_ & _ & _ & _ & _ & Hvm & _).
unfold anon_place_ok in Hpl. apply andb_prop in Hpl as [Hpl Hfree]. apply andb_prop in Hpl as [Hpl Htop].
apply andb_prop in Hpl as [Hal Hpos]. apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
pose proof Htop as Htop0.
rewrite Hvm, (kla_top _ _ _ _ _ _ _ _ KL) in Htop. unfold page_size in Hal.
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Exa : Z_to_bv 64 x = a) by (rewrite Hx; apply Z_to_bv_bv_unsigned).
assert (Hnewch : chunk_ok LV (m_vmmaps (cfg_model c1)) (x, len)).
{ apply (ki_ch LV B (PERMc Lg) T N _ _ K'). cbn [gstep g_chunks]. left. reflexivity. }
destruct Hnewch as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). cbn [fst snd] in C0, C1, C2, C3, C4, C5, C6.
assert (Hul : bv_unsigned (Z_to_bv 64 len) = len) by (apply (u_w64 len); unfold kMaxChunk in Hmax; lia).
assert (Hdis1 : forall e, In e (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) ->
bv_unsigned a + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned a).
{ intros e He. pose proof (proj1 (region_free_iff _ a (Z_to_bv 64 len)) Hfree (fst e) (snd e)) as Hdis.
rewrite <- surjective_pairing in Hdis. specialize (Hdis He). rewrite Hul in Hdis. exact Hdis. }
assert (Hdis0 : forall e, In e (vm_reserved (m_vmmaps (cfg_model c)) ++ vm_maps (m_vmmaps (cfg_model c))) ->
bv_unsigned a + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned a).
{ intros e He. rewrite <- Hvm in He. exact (Hdis1 e He). }

assert (Hdisp : forall p, In p (PERMc Lg) -> bv_unsigned a + len <= fst p \/ snd p <= bv_unsigned a).
{ intros p Hp. destruct (ki_perm LV B (PERMc Lg) T N _ _ K p Hp) as (P1 & _).
destruct (perm_u LA LV B (PERMc Lg) T N LLc p Hp) as (U1 & U2 & _).
specialize (Hdis0 (z2w p) ltac:(apply in_app_iff; right; exact P1)). rewrite U1, U2 in Hdis0. lia. }

assert (Hsh_ws : forall y, in_sh x len y = true <-> In y (map fst ws)).
{ intros y. split.
- intros E1. unfold in_sh in E1. rewrite Hml in E1. apply andb_prop in E1 as [E1a E1b]. apply Z.leb_le in E1a. apply Z.ltb_lt in E1b.
assert (Hin : In (bv_unsigned y) (map (fun w : word * list byte => bv_unsigned (fst w)) ws)).
{ rewrite Hcov. apply zrange_In. rewrite Z2Nat.id by lia. lia. }
apply in_map_iff in Hin as (w & Ew & Hw). apply bv_unsigned_inj in Ew. rewrite <- Ew. apply in_map. exact Hw.
- intros E2. apply in_map_iff in E2 as (w & <- & Hw).
assert (Hin : In (bv_unsigned (fst w)) (map (fun w : word * list byte => bv_unsigned (fst w)) ws)) by (apply in_map_iff; exists w; auto).
rewrite Hcov in Hin. apply zrange_In in Hin.
unfold in_sh. rewrite Hml. apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply Z.ltb_lt.
destruct (Z.le_gt_cases (sh_hi x len) (sh_lo x)); [rewrite Z2Nat.nonpos in Hin by lia; lia| rewrite Z2Nat.id in Hin by lia; lia]. }
assert (Hws_rng : forall y, In y (map fst ws) -> kLowEnd < bv_unsigned y < KHI).
{ intros y Hy. apply Hsh_ws in Hy. apply (in_sh_bounds x len y C0); [rewrite Hml; exact Hlen| rewrite Hml; exact C6| exact Hy]. }

assert (Hhid_none : forall y, hidden LV mo1 y = true -> ms_mem ms1 y = None).
{ intros y Hy. destruct HrelR as (Hv & HdR & _ & _ & _).
assert (HhR : hidden LV moR y = true).
{ rewrite (hidden_ext LV _ _ (drift_vmeq LV _ _ HdR)). rewrite <- (hidden_ext LV _ _ (drift_vmeq LV _ _ Hd)). exact Hy. }
rewrite <- Hv. rewrite msview_mem. apply view_hidden. exact HhR. }
assert (Hws_none : forall y, In y (map fst ws) -> ms_mem ms1 y = None).
{ intros y Hy. rewrite Hrev in Hy. apply (reveal_In LV Hsh) in Hy as [Hy _]. exact (Hhid_none y Hy). }
assert (Hrng_none : forall y : word, bv_unsigned a <= bv_unsigned y < bv_unsigned a + len -> ms_mem ms1 y = None).
{ intros y Hy. apply Hhid_none.
apply (fresh_hidden B (PERMc Lg) T N g mo1 a len LLc K1 Hlen ltac:(unfold kMaxChunk in Hmax; lia) Hfree Htop0); [| exact Hy].
rewrite <- Hx. exact C5. }
apply (HK x (nret ms1 (rsp_grant a (w64 len) ws)) c1 (hid_add H (map fst ws))).
-
unfold OD.dec_mmap, rsp0_grant. rewrite Hml.
change (OD.mmap_len len) with (mmap_len len). rewrite Hml.
rewrite Exa, !bv_eqb_refl. cbn [andb].
unfold OD.mmap_addr_ok. change (OD.mmap_len len) with (mmap_len len). rewrite Hml.
replace (bv_unsigned a mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hal).
replace (0 <? bv_unsigned a) with true by (symmetry; apply Z.ltb_lt; exact Hpos).
replace (bv_unsigned a + len <=? RC.alloc_ceiling) with true by (symmetry; apply Z.leb_le; exact Htop).
cbn. rewrite Hx. reflexivity.
-
unfold SM.mmap_answer_ok. rewrite (round_up_pg_aligned len Hmod). apply orb_true_intro. right.
replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
replace (x mod SM.PGSZ =? 0) with true by (symmetry; apply Z.eqb_eq; unfold SM.PGSZ; rewrite Hx; exact Hal).
replace (x + len <=? RC.alloc_ceiling) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. unfold SM.ranges_free. apply forallb_forall. intros r Hr.
unfold SM.iv_disjoint. apply orb_true_intro.
destruct (lranges_split Lg r Hr) as [(b & l & Hbl & ->)|Hr'].
+ destruct (kla_groups _ _ _ _ _ _ _ _ KL b l Hbl) as (G1 & _). rewrite (round_up_pg_aligned l G1). cbn [fst snd].
specialize (Hdisp (civ (b, l)) ltac:(unfold PERMc; apply in_app_iff; left; apply in_map; exact Hbl)).
unfold civ in Hdisp. cbn [fst snd] in Hdisp. destruct Hdisp as [Hdis|Hdis]; [left|right]; apply Z.leb_le; lia.
+ destruct (kla_cov _ _ _ _ _ _ _ _ KL r Hr') as (e & He & Hlo & Hhi).
assert (He' : In e (vm_reserved (m_vmmaps (cfg_model c)) ++ vm_maps (m_vmmaps (cfg_model c)))).
{ apply in_app_iff. destruct He as [He|(p & Hp & ->)]; [left; exact He| right].
exact (proj1 (ki_perm LV B (PERMc Lg) T N _ _ K p ltac:(unfold PERMc; apply in_app_iff; right; exact Hp))). }
destruct (Hdis0 e He') as [Hdis|Hdis]; [left|right]; apply Z.leb_le; lia.
-
unfold SM.is_err, SM.TWO64. apply Z.ltb_ge. lia.
-
unfold rsp0_grant. rewrite Exa, Hml.
replace (HG (hid_add H (map fst ws))) with (hid_add (HG H) (map fst ws))
by (apply functional_extensionality; intros y; unfold HG, hid_add; destruct (H y), (GH y), (existsb (bv_eqb y) (map fst ws)); reflexivity).
refine (restrict_nret_grant (HG H) ms1 a a (w64 len) ws Hwu _ _).
+ intros y Hy. exact (Hws_none y Hy).
+ intros y Hy. unfold zeros_cover in Hy. cbn [existsb fst snd] in Hy. rewrite orb_false_r in Hy.
apply andb_prop in Hy as [Hy1 Hy2]. apply Z.leb_le in Hy1. apply Z.ltb_lt in Hy2.
rewrite (u_w64 len) in Hy2 by (unfold kMaxChunk in Hmax; lia). rewrite <- Hx in Hy1, Hy2.
split.
* unfold HG. apply orb_false_intro.
-- destruct (H y) eqn:E; [|reflexivity]. exfalso. pose proof (kla_Hrange _ _ _ _ _ _ _ _ KL y E). lia.
-- destruct (GH y) eqn:E; [|reflexivity]. exfalso. destruct (kla_G _ _ _ _ _ _ _ _ KL y E) as (Gm & _).
apply Gm. apply Hrng_none. lia.
* intros Hin. pose proof (Hws_rng y Hin). lia.
-
assert (Hcnt1 : count_occ pdec (vm_maps (m_vmmaps (cfg_model c1))) (cent (x, len)) = 1%nat).
{ rewrite Hmo, maps_grant. unfold cent. cbn [fst snd]. fold (w64 x) in Exa. rewrite Exa. rewrite count_occ_cons_eq by reflexivity.
f_equal. apply count_occ_not_In. intros Hin.
specialize (Hdis1 (a, w64 len) ltac:(apply in_app_iff; right; exact Hin)). cbn [fst snd] in Hdis1. unfold w64 in Hdis1. rewrite Hul in Hdis1. lia. }
pose proof (ki_sp0 LV B (PERMc Lg) T N _ _ K) as Hsp0.
destruct (kla_par _ _ _ _ _ _ _ _ KL) as (HB & [HT1 HT2] & [HN1 HN2]).
constructor.
+ cbn [gstep] in K'. pose proof (KI_chunk_to_perm LV B (PERMc Lg) T N (x, len) (g_chunks g) (g_spent g) (sec_cost len) _ K' Hcnt1 Hsp0) as K2.
cbn [snd] in K2. destruct g as [gc gs]. exact K2.
+ unfold grp_add. cbn [KV.set_groups KV.ld_groups map snd]. rewrite zsum_cons, zlen_cons. lia.
+ exact HC1.
+ exact Hh1.
+ rewrite Hmo, top_grant, Hvm. exact (kla_top _ _ _ _ _ _ _ _ KL).
+ intros b l Hin. unfold grp_add in Hin. cbn [KV.set_groups KV.ld_groups] in Hin.
destruct Hin as [E|Hin]; [injection E as <- <-| exact (kla_groups _ _ _ _ _ _ _ _ KL b l Hin)].
unfold gstatic. split; [exact Hmod|]. split; [lia|]. split; [lia|]. split; [rewrite Hx; exact Hal|]. split; [exact C5|]. split; [exact C6|].
split; [exact C10|]. split.
* intros iv y Hiv Hy. rewrite Hx in Hy. split.
-- pose proof (fresh_off_base LA LV B (PERMc Lg) T N LLc g mo1 a (Z_to_bv 64 len) K1 ltac:(rewrite Hul; exact Hlen) Hfree ltac:(rewrite Hul; exact Htop0) y iv ltac:(rewrite Hul; exact Hy) Hiv). lia.
-- intros Hs.
assert (Ha8 : bv_unsigned a mod 8 = 0) by (clear -Hal; Z.div_mod_to_equations; lia).
assert (Hn8 : bv_unsigned (Z_to_bv 64 len) mod 8 = 0) by (rewrite Hul; clear -Hmod; Z.div_mod_to_equations; lia).
pose proof (fresh_shadow_uncovered LA LV B (PERMc Lg) T N LLc g mo1 a (Z_to_bv 64 len) K1 ltac:(rewrite Hul; exact Hlen) Ha8 Hn8 Hfree ltac:(rewrite Hul; exact Htop0) (shz LV y)) as Hunc.
assert (Hz : zin (shz LV y) (shadow_iv LV a (Z_to_bv 64 len)) = true).
{ apply zin_true. unfold shadow_iv, sh_iv, wiv2z. cbn [fst snd]. rewrite Hul.
apply (proj2 (sh_iv_iff LV (bv_unsigned a) (bv_unsigned a + len) (shz LV y) ltac:(lia))). exists y. split; [exact Hy| reflexivity]. }
specialize (Hunc Hz). unfold appcov in Hunc. apply orb_false_elim in Hunc as [Hb _].
destruct (proj1 (bcov_false_iff LV (shz LV y)) Hb iv Hiv); lia.
* intros Hin. specialize (Hdisp (civ (x, len)) ltac:(unfold PERMc; apply in_app_iff; right; exact Hin)).
unfold civ in Hdisp. cbn [fst snd] in Hdisp. lia.
+ intros r Hr. change (oranges (grp_add x len Lg)) with (oranges Lg) in Hr.
destruct (kla_cov _ _ _ _ _ _ _ _ KL r Hr) as (e & He & Hlo & Hhi).
exists e. split; [| split; assumption]. rewrite Hmo, reserved_grant, Hvm. exact He.
+ unfold grp_add. cbn [KV.set_groups KV.ld_groups map fst]. constructor; [| exact (kla_nodup _ _ _ _ _ _ _ _ KL)].
intros Hin. apply in_map_iff in Hin as ([b l] & Eb & Hin). cbn [fst] in Eb. subst b.
destruct (kla_groups _ _ _ _ _ _ _ _ KL x l Hin) as (_ & Gl & _).
specialize (Hdisp (civ (x, l)) ltac:(unfold PERMc; apply in_app_iff; left; apply in_map; exact Hin)).
unfold civ in Hdisp. cbn [fst snd] in Hdisp. lia.
+ intros y Hy. apply hid_add_In in Hy as [Hy|Hy]; [exact (kla_Hrange _ _ _ _ _ _ _ _ KL y Hy)| exact (Hws_rng y Hy)].
+ intros y Hy. apply hid_add_In in Hy.
unfold rsp_grant. rewrite nret_mem.
destruct (in_dec weq_dec y (map fst ws)) as [Hin|Hnin]; [apply apply_writes_units_In; assumption|].
destruct Hy as [Hy|Hy]; [|contradiction].
rewrite (apply_writes_units_notIn ws _ y Hwu Hnin). cbn [apply_unmaps]. rewrite apply_zeros_1.
destruct (inR a (w64 len) (bv_unsigned y)); [discriminate| exact (kla_Hmem _ _ _ _ _ _ _ _ KL y Hy)].
+ intros b l y Hin Hy. apply hid_add_In. unfold grp_add in Hin. cbn [KV.set_groups KV.ld_groups] in Hin.
destruct Hin as [E|Hin]; [injection E as <- <-; right; apply Hsh_ws; exact Hy| left; exact (kla_Hsh _ _ _ _ _ _ _ _ KL b l y Hin Hy)].
+
intros y Hy. apply hid_add_In in Hy as [Hy|Hy].
* destruct (kla_Hex _ _ _ _ _ _ _ _ KL y Hy) as (b & l & Hb & Hs). exists b, l. split; [right; exact Hb| exact Hs].
* exists x, len. split; [left; reflexivity| apply Hsh_ws; exact Hy].
+
intros y Gy. destruct (kla_G _ _ _ _ _ _ _ _ KL y Gy) as (Gm & Gg & GHy).
assert (Hnw : ~ In y (map fst ws)) by (intros Hin; apply Gm; exact (Hws_none y Hin)).
assert (Hnr : ~ (bv_unsigned a <= bv_unsigned y < bv_unsigned a + len)) by (intros Hr; apply Gm; exact (Hrng_none y Hr)).
split; [| split].
* unfold rsp_grant. rewrite nret_mem. rewrite (apply_writes_units_notIn ws _ y Hwu Hnw). cbn [apply_unmaps]. rewrite apply_zeros_1.
replace (inR a (w64 len) (bv_unsigned y)) with false; [exact Gm|].
symmetry. unfold inR, Qqcs.in_rng. unfold w64. rewrite Hul.
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned a + len)); cbn [andb]; try reflexivity. exfalso. lia.
* unfold in_grp, grp_add. cbn [KV.set_groups KV.ld_groups existsb fst snd]. fold (in_grp Lg y). rewrite Gg, orb_false_r.
rewrite Hx. destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned a + len)); cbn [andb]; try reflexivity. exfalso. lia.
* unfold hid_add. rewrite GHy. cbn [orb]. destruct (existsb (bv_eqb y) (map fst ws)) eqn:E; [|reflexivity].
exfalso. apply Hnw. apply existsb_exists in E as (z & Hz & Ez). apply bv_eqb_eq in Ez. subst z. exact Hz.
-
intros y Gy. destruct (kla_G _ _ _ _ _ _ _ _ KL y Gy) as (Gm & _).
assert (Hnw : ~ In y (map fst ws)) by (intros Hin; apply Gm; exact (Hws_none y Hin)).
assert (Hnr : ~ (bv_unsigned a <= bv_unsigned y < bv_unsigned a + len)) by (intros Hr; apply Gm; exact (Hrng_none y Hr)).
unfold rsp_grant. rewrite nret_mem. rewrite (apply_writes_units_notIn ws _ y Hwu Hnw). cbn [apply_unmaps]. rewrite apply_zeros_1.
replace (inR a (w64 len) (bv_unsigned y)) with false; [reflexivity|].
symmetry. unfold inR, Qqcs.in_rng. unfold w64. rewrite Hul.
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned a + len)); cbn [andb]; try reflexivity. exfalso. lia.
-
intros y Hy. destruct (in_dec weq_dec y (map fst ws)) as [Hin|Hnin].
{ right. right. split; [apply hid_add_In; right; exact Hin|].
destruct (H y) eqn:E; [|reflexivity]. exfalso. apply (kla_Hmem _ _ _ _ _ _ _ _ KL y E). exact (Hws_none y Hin). }
destruct (Z.le_gt_cases (bv_unsigned a) (bv_unsigned y)) as [Hlo|Hlo]; [destruct (Z.lt_ge_cases (bv_unsigned y) (bv_unsigned a + len)) as [Hhi|Hhi]|].
+ right. left. rewrite Hx. lia.
+ left. revert Hy. unfold rsp_grant. rewrite nret_mem. rewrite (apply_writes_units_notIn ws _ y Hwu Hnin). cbn [apply_unmaps]. rewrite apply_zeros_1.
replace (inR a (w64 len) (bv_unsigned y)) with false; [exact (fun h => h)|].
symmetry. unfold inR, Qqcs.in_rng. unfold w64. rewrite Hul.
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned a + len)); cbn [andb]; try reflexivity. exfalso. lia.
+ left. revert Hy. unfold rsp_grant. rewrite nret_mem. rewrite (apply_writes_units_notIn ws _ y Hwu Hnin). cbn [apply_unmaps]. rewrite apply_zeros_1.
replace (inR a (w64 len) (bv_unsigned y)) with false; [exact (fun h => h)|].
symmetry. unfold inR, Qqcs.in_rng. unfold w64. rewrite Hul.
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned a + len)); cbn [andb]; try reflexivity. exfalso. lia.
- intros y Hy. apply hid_add_In. left. exact Hy.
- exact HVO.
- exact HVS.
Qed.

Definition grp_del (a : Z) (Lg : KV.mled) : KV.mled := KV.set_groups (KV.g_remove a (KV.ld_groups Lg)) Lg.
Definition rsp0_unmap (a l : Z) : resp := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 (mmap_len l))] [] [].

Lemma nodup_fst_unique : forall (gs : list (Z * Z)) a l l', List.NoDup (map fst gs) -> In (a, l) gs -> In (a, l') gs -> l = l'.
Proof.
induction gs as [|[y ly] gs IH]; intros a l l' ND H1 H2; [destruct H1|]. cbn [map fst] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- injection E1 as _ <-. injection E2 as _ <-. reflexivity.
- injection E1 as -> _. exfalso. apply Hny. apply in_map_iff. exists (a, l'). split; [reflexivity| exact H2].
- injection E2 as -> _. exfalso. apply Hny. apply in_map_iff. exists (a, l). split; [reflexivity| exact H1].
- exact (IH a l l' NDl H1 H2).
Qed.

Lemma step_munmap : forall Lg g c H ms1 a l B T N,
KLA Lg g c H (ms_mem ms1) B T N -> In (a, l) (KV.ld_groups Lg) ->
ON.at_node segs (ON.NMunmap a l) (restrict (HG H) ms1) ->
(forall msv' c' H',
OD.dec_munmap a l (rsp0_unmap a l) = Some (OD.RgDone true) ->
restrict (HG H') msv' = OI.nret (restrict (HG H) ms1) (rsp0_unmap a l) ->
KLA (grp_del a Lg) g c' H' (ms_mem msv') B (T - l) (N - 1) ->
(forall y, GH y = true -> ms_mem msv' y = ms_mem ms1 y) ->
(forall y, ms_mem msv' y <> None -> ms_mem ms1 y <> None /\ ~ (a <= bv_unsigned y < a + l) /\ (H y = true -> H' y = true)) ->
(forall y, H' y = true -> H y = true) ->
vm_onlyA (cfg_model c) (cfg_model c') -> vmst (cfg_model c) (cfg_model c') ->
VJ LV J c' msv') ->
VJ LV J c ms1.
Proof.
intros Lg g c H ms1 a l B T N KL Hin Hat HK.
destruct (kla_groups _ _ _ _ _ _ _ _ KL a l Hin) as (Hal & Hl & Ha0 & Haal & Hpl & Hceil & Hexc & Hbase & HnP0).
pose proof (kla_ki _ _ _ _ _ _ _ _ KL) as K.
destruct (kla_par _ _ _ _ _ _ _ _ KL) as (HB & [HT1 HT2] & [HN1 HN2]).
pose proof (kla_nodup _ _ _ _ _ _ _ _ KL) as ND.
destruct (g_remove_sums a l _ ND Hin) as [Hzs Hzl].

assert (Heq : forall r, In r (PERMc Lg) <-> In r (civ (a, l) :: PERMc (grp_del a Lg))).
{ intros r. unfold PERMc, grp_del. cbn [KV.set_groups KV.ld_groups]. split.
- intros Hr. apply in_app_iff in Hr as [Hr|Hr]; [| right; apply in_app_iff; right; exact Hr].
apply in_map_iff in Hr as ([b l'] & <- & Hb). destruct (Z.eq_dec b a) as [->|Hne].
+ left.
rewrite (nodup_fst_unique _ a l' l ND Hb Hin). reflexivity.
+ right. apply in_app_iff. left. apply in_map. apply g_remove_In_conv; assumption.
- intros [<-|Hr]; [apply in_app_iff; left; apply in_map; exact Hin|].
apply in_app_iff in Hr as [Hr|Hr]; [| apply in_app_iff; right; exact Hr].
apply in_map_iff in Hr as ([b l'] & <- & Hb). apply in_app_iff. left. apply in_map.
exact (proj1 (g_remove_In a l _ b l' ND Hin Hb)). }
pose proof (KI_perm_equiv LV B _ _ T N g _ Heq K) as Kh.
assert (HnP : ~ In (civ (a, l)) (PERMc (grp_del a Lg))).
{ unfold PERMc, grp_del. cbn [KV.set_groups KV.ld_groups]. intros Hr. apply in_app_iff in Hr as [Hr|Hr]; [| exact (HnP0 Hr)].
apply in_map_iff in Hr as ([b l'] & E & Hb). destruct (g_remove_In a l _ b l' ND Hin Hb) as [_ Hne].
unfold civ in E. cbn [fst snd] in E. injection E as E _. contradiction. }
assert (KLd_groups : forall b l', In (b, l') (KV.ld_groups (grp_del a Lg)) -> In (b, l') (KV.ld_groups Lg) /\ b <> a).
{ intros b l' Hb. unfold grp_del in Hb. cbn [KV.set_groups KV.ld_groups] in Hb. exact (g_remove_In a l _ b l' ND Hin Hb). }
assert (HPb : forall r', In r' (PERMc (grp_del a Lg)) -> 0 < fst r' /\ fst r' < snd r' /\ snd r' <= kCeil).
{ intros r' Hr'. unfold PERMc in Hr'. apply in_app_iff in Hr' as [Hr'|Hr'].
- apply in_map_iff in Hr' as ([b l'] & <- & Hb). destruct (KLd_groups b l' Hb) as [Hb' _].
destruct (kla_groups _ _ _ _ _ _ _ _ KL b l' Hb') as (_ & G2 & G3 & _ & _ & G6 & _). unfold civ. cbn [fst snd]. lia.
- exact (llo_perm LA LV 0 PERM0 TMAX NMAX LL0 r' Hr'). }
pose proof (KI_perm_to_chunk LV B (PERMc (grp_del a Lg)) T N (civ (a, l)) g 0 _ Kh HnP HPb) as K2.
unfold civ in K2. cbn [fst snd] in K2. replace (a + l - a) with l in K2 by lia.
specialize (K2 Ha0 Haal Hal Hl Hpl Hceil).
assert (Ezc : z2w (a, a + l) = cent (a, l)) by (rewrite <- (z2w_civ (a, l)); reflexivity).
rewrite Ezc in K2. specialize (K2 Hexc Hbase ltac:(lia)).
rewrite !Z.add_0_r in K2.
set (g1 := mkG ((a, l) :: g_chunks g) (g_spent g)) in *.
pose proof (groups_zsum_nonneg _ (fun b l' Hb => kla_groups _ _ _ _ _ _ _ _ KL b l' (proj1 (KLd_groups b l' Hb)))) as Hz'.
unfold grp_del in Hz' at 1. cbn [KV.set_groups KV.ld_groups] in Hz'.
assert (Hzl0 : 0 <= zlen (KV.g_remove a (KV.ld_groups Lg))) by (unfold zlen; lia).
assert (LLd : ll_ok LA LV B (PERMc (grp_del a Lg)) (T - l) (N - 1)).
{ unfold PERMc. apply (ll_ok_ext LA LV 0 PERM0 TMAX NMAX B _ (T - l) (N - 1) LL0 HB); [| lia| lia].
intros r Hr. apply HPb. unfold PERMc. apply in_app_iff. left. exact Hr. }
assert (G : gev LA B g1 (EvMunmap a l)) by (cbn [gev g1 g_chunks]; split; [left; reflexivity| lia]).
rewrite kCeil_val in Hceil.
refine (vj_ev segs LA LV B (PERMc (grp_del a Lg)) (T - l) (N - 1) LLd Hwx Hsegs Hsh Hbx Hbc J J_nclosed (EvMunmap a l) g1 c ms1 _ (kla_cinv _ _ _ _ _ _ _ _ KL) K2 G _).
{ cbn [node_of]. apply at_node_munmap_bridge; [eapply at_node_restrict; [right; eexists; eexists; reflexivity| exact Hat]|].
intros y Hy. apply (kla_Hmem _ _ _ _ _ _ _ _ KL). apply (kla_Hsh _ _ _ _ _ _ _ _ KL a l y Hin).
apply (in_sh_shadow_iv a l y ltac:(lia) ltac:(lia) Hal ltac:(rewrite kCeil_val; lia)). exact Hy. }
intros rsp ans c1 mo1 Hd Hr Hdec Hok K' HC1 Hh1.
pose proof (KI_drift LV B (PERMc (grp_del a Lg)) (T - l) (N - 1) g1 _ _ Hd K2) as K21.
pose proof (vm_onlyA_trans _ _ _ (vm_onlyA_drift LV _ _ Hd) (vm_onlyA_nstep_raw LA LV B (PERMc (grp_del a Lg)) (T - l) (N - 1) LLd g1 mo1 _ rsp _ [] K21 G Hr)) as HVO.
assert (HVS : vmst (cfg_model c) (cfg_model c1)).
{ pose proof (drift_frame LV _ _ Hd) as (_ & _ & _ & _ & _ & Hvm0 & _).
destruct (nstep_raw_vmst LV _ mo1 rsp _ [] (node_of_mm _) Hr) as [V1 V2]. split; rewrite <- Hvm0; assumption. }
cbn [node_of] in Hr. cbn -[munmap_model rsp_munmap rlenw] in Hr. destruct Hr as (_ & Hmo & ->).
cbn [dec_of] in Hdec. destruct (dec_munmapA_inv a l _ ans Hdec) as (-> & _).
rewrite (rlenw_w64 l Hal) in *.
set (us := conceal LV (cfg_model c1) (Z_to_bv 64 a) (w64 l)).
pose proof (drift_frame LV _ _ Hd) as (_ & _ & _ & _ & _ & Hvm & _).
assert (Hus : forall y, zeros_cover us y = true -> in_sh a l y = true).
{ intros y Hy. unfold us, conceal in Hy. rewrite zeros_cover_bytes in Hy. apply existsb_bv_eqb in Hy. apply filter_In in Hy as [Hy _].
apply (in_sh_shadow_iv a l y ltac:(lia) ltac:(lia) Hal ltac:(rewrite kCeil_val; lia)). rewrite (rlenw_w64 l Hal). exact Hy. }

assert (Hul : bv_unsigned (w64 l) = l) by (apply u_w64; unfold kMaxChunk in Hl; lia).
assert (Hua : bv_unsigned (w64 a) = a) by (apply u_w64; lia).
assert (Hall : forall y, in_sh a l y = true -> zeros_cover us y = true).
{ intros y Hy. unfold us, conceal. rewrite zeros_cover_bytes. apply existsb_bv_eqb.
pose proof (ki_ch LV B _ (T - l) (N - 1) _ _ K2 (a, l) ltac:(cbn [g1 g_chunks]; left; reflexivity)) as CK.
destruct CK as (_ & _ & _ & _ & _ & _ & _ & CIn & _ & CFree & _). cbn [fst snd] in CIn, CFree.
pose proof (ki_x LV B _ (T - l) (N - 1) _ _ K2) as [_ (_ & _ & [_ Hbt])]. specialize (Hbt _ CIn). unfold cent in Hbt. cbn [fst snd] in Hbt.
rewrite Hua, Hul in Hbt.
assert (Hfree' : region_free (vm_reserved (m_vmmaps (cfg_model c1)) ++ vm_maps (m_vmmaps (cfg_model c1))) (w64 a) (w64 l) = true).
{ rewrite Hmo, reserved_munmap, maps_munmap, Hvm. exact CFree. }
assert (Htop' : bv_unsigned (w64 a) + bv_unsigned (w64 l) <= alloc_top (m_vmmaps (cfg_model c1))).
{ rewrite Hmo, top_munmap, Hvm, Hua, Hul. exact Hbt. }
assert (Ha8 : bv_unsigned (w64 a) mod 8 = 0) by (rewrite Hua; clear - Haal; Z.div_mod_to_equations; lia).
assert (Hn8 : bv_unsigned (w64 l) mod 8 = 0) by (rewrite Hul; clear - Hal; Z.div_mod_to_equations; lia).
assert (Hrv : reveal LV (cfg_model c1) (w64 a) (w64 l) = bytes_of (shadow_iv LV (w64 a) (w64 l))).
{ apply (reveal_all LV Hsh (cfg_model c1) (w64 a) (w64 l)); [rewrite Hul; lia| exact Ha8| exact Hn8| |].
- apply (fresh_range_uncovered LV (cfg_model c1) (vm_reserved (m_vmmaps (cfg_model c1))) (w64 a) (w64 l) Hfree').
apply (fresh_off_base LA LV B _ (T - l) (N - 1) LLd _ (cfg_model c1) (w64 a) (w64 l) K'); [rewrite Hul; lia| exact Hfree'| exact Htop'].
- apply (fresh_shadow_uncovered LA LV B _ (T - l) (N - 1) LLd _ (cfg_model c1) (w64 a) (w64 l) K'); [rewrite Hul; lia| exact Ha8| exact Hn8| exact Hfree'| exact Htop']. }
fold (w64 a). unfold reveal in Hrv. rewrite Hrv. rewrite <- (rlenw_w64 l Hal).
apply (proj2 (in_sh_shadow_iv a l y ltac:(lia) ltac:(lia) Hal ltac:(rewrite kCeil_val; lia))). exact Hy. }
apply (HK (nret ms1 (rsp_munmap LV (cfg_model c1) (Z_to_bv 64 a) (w64 l))) c1 (fun y => H y && negb (zeros_cover us y))).
- unfold OD.dec_munmap, rsp0_unmap. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. rewrite !bv_eqb_refl. reflexivity.
- unfold rsp0_unmap, rsp_munmap. rewrite (mmap_len_aligned l Hal). fold us.
refine (restrict_nret_unmap (HG H) _ ms1 (Z_to_bv 64 0) (Z_to_bv 64 a) (w64 l) us _ _ _).
+ intros y Hy. unfold HG in *. apply orb_prop in Hy as [Hy|Hy]; [apply andb_prop in Hy as [Hy _]; rewrite Hy; reflexivity| rewrite Hy; apply orb_true_r].
+ intros y Hy Hy'. unfold HG in Hy, Hy'. apply orb_false_elim in Hy' as [Hy1 Hy2]. rewrite Hy2, orb_false_r in Hy.
rewrite Hy in Hy1. cbn [andb] in Hy1. apply negb_false_iff in Hy1.
unfold zeros_cover in *. cbn [existsb]. rewrite Hy1. apply orb_true_r.
+ intros y Hy. unfold HG. rewrite (kla_Hsh _ _ _ _ _ _ _ _ KL a l y Hin (Hus y Hy)). reflexivity.
- constructor.
+ cbn [gstep g1 g_chunks g_spent remove_first fst snd] in K'. rewrite !Z.eqb_refl in K'. cbn [andb] in K'. destruct g as [gc gs]. exact K'.
+ unfold grp_del. cbn [KV.set_groups KV.ld_groups]. lia.
+ exact HC1.
+ exact Hh1.
+ rewrite Hmo, top_munmap, Hvm. exact (kla_top _ _ _ _ _ _ _ _ KL).
+ intros b l' Hb. exact (kla_groups _ _ _ _ _ _ _ _ KL b l' (proj1 (KLd_groups b l' Hb))).
+ intros r Hr. change (oranges (grp_del a Lg)) with (oranges Lg) in Hr.
destruct (kla_cov _ _ _ _ _ _ _ _ KL r Hr) as (e & He & Hlo & Hhi).
exists e. split; [| split; assumption]. rewrite Hmo, reserved_munmap, Hvm. exact He.
+ unfold grp_del. cbn [KV.set_groups KV.ld_groups]. apply g_remove_nodup. exact ND.
+ intros y Hy. apply andb_prop in Hy as [Hy _]. exact (kla_Hrange _ _ _ _ _ _ _ _ KL y Hy).
+ intros y Hy. apply andb_prop in Hy as [Hy Hnc]. apply negb_true_iff in Hnc.
pose proof (kla_Hrange _ _ _ _ _ _ _ _ KL y Hy) as Hrng.
unfold rsp_munmap. fold us. rewrite nret_mem. cbn [apply_zeros apply_writes]. rewrite apply_unmaps_cons, Hnc.
replace (inR (Z_to_bv 64 a) (w64 l) (bv_unsigned y)) with false; [exact (kla_Hmem _ _ _ _ _ _ _ _ KL y Hy)|].
symmetry. unfold inR, Qqcs.in_rng. fold (w64 a). rewrite !u_w64 by (unfold kMaxChunk in Hl; lia).
destruct (Z.leb_spec a (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (a + l)); cbn [andb]; try reflexivity.
exfalso. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in *. lia.
+ intros b l' y Hb Hy. destruct (KLd_groups b l' Hb) as [Hb' Hne].
apply andb_true_intro. split; [exact (kla_Hsh _ _ _ _ _ _ _ _ KL b l' y Hb' Hy)|]. apply negb_true_iff.
destruct (zeros_cover us y) eqn:E; [|reflexivity]. exfalso.
destruct (kla_groups _ _ _ _ _ _ _ _ KL b l' Hb') as (G1 & G2 & _ & G4 & _).
pose proof (KLA_groups_disjoint _ _ _ _ _ _ _ _ a l b l' KL Hin Hb' (fun E' => Hne (eq_sym E'))) as Hdj.
exact (sh_disjoint a l b l' y Haal Hal ltac:(lia) G4 G1 ltac:(lia) Hdj (Hus y E) Hy).
+
intros y Hy. apply andb_prop in Hy as [Hy Hnc]. apply negb_true_iff in Hnc.
destruct (kla_Hex _ _ _ _ _ _ _ _ KL y Hy) as (b & l' & Hb & Hs). exists b, l'. split; [| exact Hs].
unfold grp_del. cbn [KV.set_groups KV.ld_groups]. apply g_remove_In_conv; [exact Hb|].
intros ->. rewrite (nodup_fst_unique _ a l' l ND Hb Hin) in Hs. rewrite (Hall y Hs) in Hnc. discriminate.
+
intros y Gy. destruct (kla_G _ _ _ _ _ _ _ _ KL y Gy) as (Gm & Gg & GHy).
pose proof (in_grp_false Lg y a l Gg Hin) as Hnr.
assert (Hnc : zeros_cover us y = false).
{ destruct (zeros_cover us y) eqn:E; [|reflexivity]. exfalso.
rewrite (kla_Hsh _ _ _ _ _ _ _ _ KL a l y Hin (Hus y E)) in GHy. discriminate. }
split; [| split].
* unfold rsp_munmap. fold us. rewrite nret_mem. cbn [apply_zeros apply_writes]. rewrite apply_unmaps_cons, Hnc.
replace (inR (Z_to_bv 64 a) (w64 l) (bv_unsigned y)) with false; [exact Gm|].
symmetry. unfold inR, Qqcs.in_rng. fold (w64 a). rewrite Hua, Hul.
destruct (Z.leb_spec a (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (a + l)); cbn [andb]; try reflexivity. exfalso. lia.
* destruct (in_grp (grp_del a Lg) y) eqn:E; [|reflexivity]. exfalso.
apply in_grp_true in E as (b & l' & Hb & Hr). destruct (KLd_groups b l' Hb) as [Hb' _].
exact (in_grp_false Lg y b l' Gg Hb' Hr).
* rewrite GHy. reflexivity.
-
intros y Gy. destruct (kla_G _ _ _ _ _ _ _ _ KL y Gy) as (Gm & Gg & GHy).
pose proof (in_grp_false Lg y a l Gg Hin) as Hnr.
assert (Hnc : zeros_cover us y = false).
{ destruct (zeros_cover us y) eqn:E; [|reflexivity]. exfalso.
rewrite (kla_Hsh _ _ _ _ _ _ _ _ KL a l y Hin (Hus y E)) in GHy. discriminate. }
unfold rsp_munmap. fold us. rewrite nret_mem. cbn [apply_zeros apply_writes]. rewrite apply_unmaps_cons, Hnc.
replace (inR (Z_to_bv 64 a) (w64 l) (bv_unsigned y)) with false; [reflexivity|].
symmetry. unfold inR, Qqcs.in_rng. fold (w64 a). rewrite Hua, Hul.
destruct (Z.leb_spec a (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (a + l)); cbn [andb]; try reflexivity. exfalso. lia.
- intros y Hy. revert Hy. unfold rsp_munmap. fold us. rewrite nret_mem. cbn [apply_zeros apply_writes]. rewrite apply_unmaps_cons.
destruct (inR (Z_to_bv 64 a) (w64 l) (bv_unsigned y)) eqn:ER; [cbn [orb]; intros Hy; exfalso; apply Hy; reflexivity|].
destruct (zeros_cover us y) eqn:EC; [cbn [orb]; intros Hy; exfalso; apply Hy; reflexivity|]. cbn [orb]. intros Hy.
split; [exact Hy|]. split.
+ intros Hr. unfold inR, Qqcs.in_rng in ER. fold (w64 a) in ER. rewrite Hua, Hul in ER.
destruct (Z.leb_spec a (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) (a + l)); cbn [andb] in ER; try discriminate; lia.
+ intros HHy. apply andb_true_intro. split; [exact HHy| reflexivity].
- intros y Hy. apply andb_prop in Hy as [Hy _]. exact Hy.
- exact HVO.
- exact HVS.
Qed.

Hypothesis segs_low : forall y : word, kLowEnd < bv_unsigned y < KHI -> find_segment segs (bv_unsigned y) 1 = None.

Lemma KLA_Hoff : forall Lg g c H m B T N, KLA Lg g c H m B T N -> H_off_segments segs H.
Proof. intros Lg g c H m B T N KL y Hy. apply segs_low. exact (kla_Hrange _ _ _ _ _ _ _ _ KL y Hy). Qed.

Lemma KLA_mem_ext : forall Lg g c H m m' B T N, KLA Lg g c H m B T N -> (forall y, HG H y = true -> m' y = m y) -> KLA Lg g c H m' B T N.
Proof.
intros Lg g c H m m' B T N KL E. destruct KL as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13]. constructor; auto.
- intros y Hy. rewrite (E y ltac:(unfold HG; rewrite Hy; reflexivity)). auto.
- intros y Gy. destruct (k13 y Gy) as (G1 & G2 & G3). rewrite (E y ltac:(unfold HG; rewrite Gy; apply orb_true_r)). auto.
Qed.

Definition MI (m0 : word -> option byte) (H0 : word -> bool) (Lg0 : KV.mled)
(m : word -> option byte) (H : word -> bool) (Lg : KV.mled) : Prop :=
(forall y, GH y = true -> m y = m0 y) /\
(forall y, offseg segs y = true -> m y <> None ->
H y = true \/ in_grp Lg y = true \/ (m0 y <> None /\ in_grp Lg0 y = false /\ H0 y = false)).

Lemma MI_refl : forall m H Lg, MI m H Lg m H Lg.
Proof.
intros m H Lg. split; [reflexivity|]. intros y _ Hy.
destruct (H y) eqn:E1; [left; reflexivity|]. destruct (in_grp Lg y) eqn:E2; [right; left; reflexivity|]. right; right. auto.
Qed.

Lemma MI_evt : forall m0 H0 Lg0 m H Lg m1, MI m0 H0 Lg0 m H Lg ->
(forall y, HG H y = true -> m1 y = m y) -> (forall y, offseg segs y = true -> m y = None -> m1 y = None) ->
MI m0 H0 Lg0 m1 H Lg.
Proof.
intros m0 H0 Lg0 m H Lg m1 [I1 I2] Hs Hn. split.
- intros y Gy. rewrite (Hs y ltac:(unfold HG; rewrite Gy; apply orb_true_r)). exact (I1 y Gy).
- intros y Ho Hy. apply (I2 y Ho). intros E. apply Hy. exact (Hn y Ho E).
Qed.

Lemma sec_cost_mono : forall len M, 0 <= len <= M -> sec_cost len <= sec_cost M.
Proof.
intros len M H. unfold sec_cost, kPage. assert (len / 32768 <= M / 32768) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma vj_coarse_evt : forall Lg g c H msv B T N (P : machine_state -> Prop),
KLA Lg g c H (ms_mem msv) B T N ->
O.evt segs P (restrict (HG H) msv) ->
(forall ms1, P (restrict (HG H) ms1) -> KLA Lg g c H (ms_mem ms1) B T N ->
(forall y, HG H y = true -> ms_mem ms1 y = ms_mem msv y) ->
(forall y, offseg segs y = true -> ms_mem msv y = None -> ms_mem ms1 y = None) -> VJ LV J c ms1) ->
VJ LV J c msv.
Proof.
intros Lg g c H msv B T N P KL He HK.
apply (vj_evt segs LV Hwx Hsegs J (J_silent_closed segs LV J J_nclosed)).
assert (HGoff : H_off_segments segs (HG H)).
{ intros y Hy. unfold HG in Hy. apply orb_prop in Hy as [Hy|Hy]; [exact (KLA_Hoff _ _ _ _ _ _ _ _ KL y Hy)| exact (GH_off y Hy)]. }
apply evt_bridge in He. apply (evt_restrict_lift2 segs Hwx (HG H) HGoff) in He.
eapply evt_mono; [exact He|]. intros ms1 (HP & Hh & Hn). apply (HK ms1 HP); [| exact Hh| exact Hn].
apply (KLA_mem_ext _ _ _ _ _ _ _ _ _ KL). intros y Hy. apply Hh. exact Hy.
Qed.

Lemma MI_grant : forall m0 H0 Lg0 m1 H Lg m' H' x len, MI m0 H0 Lg0 m1 H Lg ->
(forall y, GH y = true -> m' y = m1 y) ->
(forall y, m' y <> None -> m1 y <> None \/ x <= bv_unsigned y < x + len \/ (H' y = true /\ H y = false)) ->
(forall y, H y = true -> H' y = true) ->
MI m0 H0 Lg0 m' H' (grp_add x len Lg).
Proof.
intros m0 H0 Lg0 m1 H Lg m' H' x len [I1 I2] E1 E2 Hm. split.
- intros y Gy. rewrite (E1 y Gy). exact (I1 y Gy).
- intros y Ho Hy. destruct (E2 y Hy) as [Hy1|[Hr|[Hh _]]].
+ destruct (I2 y Ho Hy1) as [Hh|[Hg|Hold]]; [left; exact (Hm y Hh)| right; left| right; right; exact Hold].
unfold in_grp, grp_add. cbn [KV.set_groups KV.ld_groups existsb]. fold (in_grp Lg y). rewrite Hg. apply orb_true_r.
+ right. left. unfold in_grp, grp_add. cbn [KV.set_groups KV.ld_groups existsb fst snd].
replace (x <=? bv_unsigned y) with true by (symmetry; apply Z.leb_le; lia).
replace (bv_unsigned y <? x + len) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ left. exact Hh.
Qed.

Lemma MI_unmap : forall m0 H0 Lg0 m1 H Lg m' H' a l, MI m0 H0 Lg0 m1 H Lg ->
List.NoDup (map fst (KV.ld_groups Lg)) -> In (a, l) (KV.ld_groups Lg) ->
(forall y, GH y = true -> m' y = m1 y) ->
(forall y, m' y <> None -> m1 y <> None /\ ~ (a <= bv_unsigned y < a + l) /\ (H y = true -> H' y = true)) ->
MI m0 H0 Lg0 m' H' (grp_del a Lg).
Proof.
intros m0 H0 Lg0 m1 H Lg m' H' a l [I1 I2] ND Hin E1 E2. split.
- intros y Gy. rewrite (E1 y Gy). exact (I1 y Gy).
- intros y Ho Hy. destruct (E2 y Hy) as (Hy1 & Hnr & Hm).
destruct (I2 y Ho Hy1) as [Hh|[Hg|Hold]]; [left; exact (Hm Hh)| right; left| right; right; exact Hold].
apply in_grp_true in Hg as (b & l' & Hb & Hr). apply in_grp_true. exists b, l'. split; [| exact Hr].
unfold grp_del. cbn [KV.set_groups KV.ld_groups]. apply g_remove_In_conv; [exact Hb|].
intros ->. rewrite (nodup_fst_unique _ a l' l ND Hb Hin) in Hr. exact (Hnr Hr).
Qed.

Theorem membed_vj_coarse_gen {R} : forall (t : ST.stree SM.ev Z R) (Ngr : nat) (Post : KV.mled -> R -> Prop) (s : MG.PState)
(Q : R -> MG.PState -> machine_state -> Prop) msv c g Lg H B T N m0 H0 Lg0 c0,
MO.implM segs (MG.membed t) s Q (restrict (HG H) msv) ->
KV.ctree_ok Lg t Post -> tree_supp Lg t Ngr ->
KLA Lg g c H (ms_mem msv) B T N ->
MI m0 H0 Lg0 (ms_mem msv) H Lg ->
vm_onlyA (cfg_model c0) (cfg_model c) -> vmst (cfg_model c0) (cfg_model c) ->
g_spent g + Z.of_nat Ngr * sec_cost kMaxChunk <= B -> (Ngr <> 0%nat -> zlen (g_chunks g) + 1 <= kMaxCnt) ->
T + Z.of_nat Ngr * kMaxChunk <= TMAX -> N + Z.of_nat Ngr <= NMAX ->
(forall r s' msv' Lg' c' H' B' T' N',
Q r s' (restrict (HG H') msv') -> Post Lg' r -> KV.cpath Lg t Lg' r ->
MG.ps_m s' = MG.ps_m s -> MG.ps_brk s' = MG.ps_brk s ->
KLA Lg' g c' H' (ms_mem msv') B' T' N' ->
B - Z.of_nat Ngr * sec_cost kMaxChunk <= B' -> T' <= T + Z.of_nat Ngr * kMaxChunk -> N' <= N + Z.of_nat Ngr ->
(KV.ld_resv Lg' = KV.ld_resv Lg /\ KV.ld_metas Lg' = KV.ld_metas Lg /\ KV.ld_brkreg Lg' = KV.ld_brkreg Lg) ->
MI m0 H0 Lg0 (ms_mem msv') H' Lg' ->
vm_onlyA (cfg_model c0) (cfg_model c') -> vmst (cfg_model c0) (cfg_model c') ->
VJ LV J c' msv') ->
VJ LV J c msv.
Proof.
intros t. induction t as [r|e k IH]; intros Ngr Post s Q msv c g Lg H B T N m0 H0 Lg0 c0 Himpl CT TS KL HMI HVO HVS Hbud Hcnt HTm HNm HQ.
-
cbn [MG.membed] in Himpl. unfold MO.implM, MO.mret in Himpl. cbn [OI.impl] in Himpl.
apply (vj_coarse_evt Lg g c H msv B T N _ KL Himpl). intros ms1 HP KL1 Hh1 Hn1. cbn in HP. cbn in CT.
assert (HC0 : 0 <= sec_cost kMaxChunk) by (vm_compute; discriminate).
apply (HQ r s ms1 Lg c H B T N HP CT (KV.cpath_ret Lg r) eq_refl eq_refl KL1); [nia| unfold kMaxChunk; nia| lia| repeat split; reflexivity| | exact HVO| exact HVS].
exact (MI_evt _ _ _ _ _ _ _ HMI Hh1 Hn1).
-
assert (HC0 : 0 <= sec_cost kMaxChunk) by (vm_compute; discriminate).
cbn [MG.membed] in Himpl. apply IR.implM_bind_inv in Himpl.
cbn [KV.ctree_ok] in CT. destruct CT as [PRE CT]. cbn [tree_supp] in TS. destruct TS as [SUP TS].
destruct e as [req|a len prot flags|a len|a len prot|p0 cc0 h0|w|a ol nl fl]; try (destruct SUP; fail).
+
destruct SUP as (-> & -> & -> & Hlen & Hmod & Hmax). cbn [is_grant] in TS. destruct TS as (N' & -> & TS).
pose proof (IR.ev_step_implM segs (SM.EMmap 0 len 3 34) (ON.NMmap 0 len 3 34) s _ _ eq_refl eq_refl Himpl) as HE.
apply (vj_coarse_evt Lg g c H msv B T N _ KL HE). intros ms1 [Hat Hc] KL1 Hh1 Hn1.
pose proof (MI_evt _ _ _ _ _ _ _ HMI Hh1 Hn1) as HMI1.
pose proof (sec_cost_mono len kMaxChunk ltac:(lia)) as Hsc.
rewrite Nat2Z.inj_succ in Hbud, HTm, HNm.
apply (step_mmap Lg g c H ms1 len B T N KL1 Hlen Hmod Hmax); [nia| apply Hcnt; discriminate| nia| lia| exact Hat|].
intros x msv' c' H' Hdec0 Hans Hnerr Hres KL' E1 E2 Hmono HVO1 HVS1.
pose proof (MI_grant _ _ _ _ _ _ _ _ x len HMI1 E1 E2 Hmono) as HMI'.
assert (Hd : IR.ev_dec (SM.EMmap 0 len 3 34) (MG.ps_brk s) (rsp0_grant x len) = Some x).
{ cbn -[OD.dec_mmap rsp0_grant]. rewrite Hdec0. reflexivity. }
specialize (Hc (rsp0_grant x len) x Hd). rewrite <- Hres in Hc.
apply (vj_coarse_evt _ g c' H' msv' _ _ _ _ KL' Hc). intros ms2 H2' KL2 Hh2 Hn2.
pose proof (MI_evt _ _ _ _ _ _ _ HMI' Hh2 Hn2) as HMI2.
assert (Eans : KV.answer_ok Lg (SM.EMmap 0 len 3 34) x = true) by exact Hans.
assert (Epost : KV.event_post Lg (SM.EMmap 0 len 3 34) x = grp_add x len Lg).
{ cbn -[SM.is_err]. rewrite Hnerr. reflexivity. }
apply (IH x N' Post _ Q ms2 c' g (grp_add x len Lg) H' (B - sec_cost len) (T + len) (N + 1) m0 H0 Lg0 c0 H2').
* rewrite <- Epost. apply CT. exact Eans.
* rewrite <- Epost. apply TS. exact Eans.
* exact KL2.
* exact HMI2.
* exact (vm_onlyA_trans _ _ _ HVO HVO1).
* exact (vmst_trans _ _ _ HVS HVS1).
* nia.
* intros _. apply Hcnt. discriminate.
* nia.
* lia.
* intros r s' msv'' Lg'' c'' H'' B'' T'' N'' HQ' HP CP Em Eb KL'' HB'' HT'' HN'' HOR'' HMI'' HVO'' HVS''.
apply (HQ r s' msv'' Lg'' c'' H'' B'' T'' N'' HQ' HP).
-- eapply KV.cpath_vis; [exact Eans|]. rewrite Epost. exact CP.
-- rewrite Em. apply IR.ev_post_state_m.
-- rewrite Eb. reflexivity.
-- exact KL''.
-- rewrite Nat2Z.inj_succ. nia.
-- rewrite Nat2Z.inj_succ. nia.
-- rewrite Nat2Z.inj_succ. lia.
-- exact HOR''.
-- exact HMI''.
-- exact HVO''.
-- exact HVS''.
+
cbn [is_grant] in TS. cbn [KV.event_pre] in PRE. destruct PRE as (_ & l & Hin & Hll).
assert (El : len = l).
{ destruct (kla_groups _ _ _ _ _ _ _ _ KL a l Hin) as (G1 & _). rewrite (round_up_pg_aligned l G1) in Hll. destruct Hll; assumption. }
subst len.
pose proof (IR.ev_step_implM segs (SM.EMunmap a l) (ON.NMunmap a l) s _ _ eq_refl eq_refl Himpl) as HE.
apply (vj_coarse_evt Lg g c H msv B T N _ KL HE). intros ms1 [Hat Hc] KL1 Hh1 Hn1.
pose proof (MI_evt _ _ _ _ _ _ _ HMI Hh1 Hn1) as HMI1.
apply (step_munmap Lg g c H ms1 a l B T N KL1 Hin Hat).
intros msv' c' H' Hdec0 Hres KL' E1 E2 Hsub HVO1 HVS1.
pose proof (MI_unmap _ _ _ _ _ _ _ _ a l HMI1 (kla_nodup _ _ _ _ _ _ _ _ KL) Hin E1 E2) as HMI'.
assert (Hd : IR.ev_dec (SM.EMunmap a l) (MG.ps_brk s) (rsp0_unmap a l) = Some 0).
{ cbn -[OD.dec_munmap rsp0_unmap]. rewrite Hdec0. reflexivity. }
specialize (Hc (rsp0_unmap a l) 0 Hd). rewrite <- Hres in Hc.
apply (vj_coarse_evt _ g c' H' msv' _ _ _ _ KL' Hc). intros ms2 H2' KL2 Hh2 Hn2.
pose proof (MI_evt _ _ _ _ _ _ _ HMI' Hh2 Hn2) as HMI2.
assert (Eans : KV.answer_ok Lg (SM.EMunmap a l) 0 = true) by reflexivity.
destruct (kla_groups _ _ _ _ _ _ _ _ KL a l Hin) as (_ & Gl & _).
apply (IH 0 Ngr Post _ Q ms2 c' g (grp_del a Lg) H' B (T - l) (N - 1) m0 H0 Lg0 c0 H2').
* apply (CT 0 Eans).
* apply (TS 0 Eans).
* exact KL2.
* exact HMI2.
* exact (vm_onlyA_trans _ _ _ HVO HVO1).
* exact (vmst_trans _ _ _ HVS HVS1).
* exact Hbud.
* exact Hcnt.
* lia.
* lia.
* intros r s' msv'' Lg'' c'' H'' B'' T'' N'' HQ' HP CP Em Eb KL'' HB'' HT'' HN'' HOR'' HMI'' HVO'' HVS''.
apply (HQ r s' msv'' Lg'' c'' H'' B'' T'' N'' HQ' HP).
-- eapply KV.cpath_vis; [exact Eans| exact CP].
-- rewrite Em. apply IR.ev_post_state_m.
-- rewrite Eb. reflexivity.
-- exact KL''.
-- exact HB''.
-- lia.
-- lia.
-- exact HOR''.
-- exact HMI''.
-- exact HVO''.
-- exact HVS''.
Qed.

Theorem membed_vj_coarse {R} : forall (t : ST.stree SM.ev Z R) (Ngr : nat) (Post : KV.mled -> R -> Prop) (s : MG.PState)
(Q : R -> MG.PState -> machine_state -> Prop) msv c g Lg H B T N,
MO.implM segs (MG.membed t) s Q (restrict (HG H) msv) ->
KV.ctree_ok Lg t Post -> tree_supp Lg t Ngr ->
KLA Lg g c H (ms_mem msv) B T N ->
g_spent g + Z.of_nat Ngr * sec_cost kMaxChunk <= B -> (Ngr <> 0%nat -> zlen (g_chunks g) + 1 <= kMaxCnt) ->
T + Z.of_nat Ngr * kMaxChunk <= TMAX -> N + Z.of_nat Ngr <= NMAX ->
(forall r s' msv' Lg' c' H' B' T' N',
Q r s' (restrict (HG H') msv') -> Post Lg' r -> KV.cpath Lg t Lg' r ->
MG.ps_m s' = MG.ps_m s -> MG.ps_brk s' = MG.ps_brk s ->
KLA Lg' g c' H' (ms_mem msv') B' T' N' ->
B - Z.of_nat Ngr * sec_cost kMaxChunk <= B' -> T' <= T + Z.of_nat Ngr * kMaxChunk -> N' <= N + Z.of_nat Ngr ->
(KV.ld_resv Lg' = KV.ld_resv Lg /\ KV.ld_metas Lg' = KV.ld_metas Lg /\ KV.ld_brkreg Lg' = KV.ld_brkreg Lg) ->
MI (ms_mem msv) H Lg (ms_mem msv') H' Lg' ->
vm_onlyA (cfg_model c) (cfg_model c') -> vmst (cfg_model c) (cfg_model c') ->
VJ LV J c' msv') ->
VJ LV J c msv.
Proof.
intros t Ngr Post s Q msv c g Lg H B T N Himpl CT TS KL Hbud Hcnt HTm HNm HQ.
exact (membed_vj_coarse_gen t Ngr Post s Q msv c g Lg H B T N (ms_mem msv) H Lg c Himpl CT TS KL (MI_refl _ _ _)
(vm_onlyA_refl _) (vmst_refl _) Hbud Hcnt HTm HNm HQ).
Qed.

End MembedVj.

Section Repack.
Context {RC__ : RC.RunConsts}.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.

Lemma KLA_GH : forall GH GH' Lg g c H m B T N,
KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N ->
(forall y, GH' y = true -> m y <> None /\ in_grp Lg y = false /\ H y = false) ->
KLA LV PERM0 TMAX NMAX GH' Lg g c H m B T N.
Proof. intros GH GH' Lg g c H m B T N KL HG'. destruct KL. constructor; assumption. Qed.

Lemma KLA_GH_none : forall GH Lg g c H m B T N,
KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (fun _ => false) Lg g c H m B T N.
Proof. intros. eapply KLA_GH; [eassumption|]. intros y Hy. discriminate. Qed.

Lemma KLA_set_live : forall GH lv Lg g c H m B T N,
KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX GH (KV.set_live lv Lg) g c H m B T N.
Proof. intros GH lv Lg g c H m B T N KL. destruct KL. constructor; assumption. Qed.

Lemma KLA_asan_step : forall Lg g g' c c' H m m' B T N,
KLA LV PERM0 TMAX NMAX (fun _ => false) Lg g c H m B T N ->
KI LV B (PERMc PERM0 Lg) T N g' (cfg_model c') ->
cinvA LV (cfg_ms c') (cfg_model c') -> m_halted (cfg_model c') = None ->
vmst (cfg_model c) (cfg_model c') ->
(forall y, H y = true -> m' y = m y) ->
KLA LV PERM0 TMAX NMAX (fun _ => false) Lg g' c' H m' B T N.
Proof.
intros Lg g g' c c' H m m' B T N KL K' HC' Hh' [Vr Vt] Hm. destruct KL as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13].
constructor; try assumption.
- rewrite Vt. exact k5.
- intros r Hr. destruct (k7 r Hr) as (e & He & Hlo & Hhi). exists e. split; [| split; assumption]. rewrite Vr. exact He.
- intros y Hy. rewrite (Hm y Hy). exact (k10 y Hy).
- intros y Hy. discriminate.
Qed.

End Repack.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsCz.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module PE := QsRG.Mq0.
Module AN := Q9ox.Mq0.
Module MG := Qhd4.Mq1.

Section Inst.
Context {fF : PE.FPF} {fC : PE.FPC}.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.

Lemma areg_epend_g : forall regs pc mem rom x8 (r : bv 5), r <> 0%bv -> areg (AN.epend regs pc mem rom x8) r = PE.getr regs r.
Proof.
intros regs pc mem rom x8 r Hr. unfold areg, PE.getr. cbn [ms_regs AN.epend].
destruct (bv_eqb r 0) eqn:E; [apply Fs.bv_eqb_eq in E; contradiction | reflexivity].
Qed.

End Inst.
