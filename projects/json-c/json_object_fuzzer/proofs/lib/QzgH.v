(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXmm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXmm.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqyb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqyb.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned (only parsing).
Definition w64 (z : Z) : word := Z_to_bv 64 z.

Definition z2w (iv : Z * Z) : word * word := (w64 (fst iv), w64 (snd iv - fst iv)).
Definition cent (c : Z * Z) : word * word := (w64 (fst c), w64 (snd c)).

Definition zdisj (a b : Z * Z) : Prop := snd a <= fst b \/ snd b <= fst a.

Definition kCeil : Z := grant_ceilA.

Lemma kCeil_val : kCeil = 0x7fffff800000.
Proof. reflexivity. Qed.

Definition kLowEnd : Z := 0x7fff7000.

Lemma u_w64 z : 0 <= z < 2^64 -> bv_unsigned (w64 z) = z.
Proof. intros H. unfold w64. apply fg_u64_lit. exact H. Qed.

Lemma u_range (x : word) : 0 <= bv_unsigned x < 2^64.
Proof. apply fg_u64_range. Qed.

Lemma w64_u (x : word) : w64 (bv_unsigned x) = x.
Proof. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma w64_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> w64 a = w64 b -> a = b.
Proof. intros Ha Hb E. rewrite <- (u_w64 a Ha), <- (u_w64 b Hb), E. reflexivity. Qed.

Lemma wiv2z_z2w iv : 0 <= fst iv -> fst iv <= snd iv -> snd iv < 2^64 -> wiv2z (z2w iv) = iv.
Proof.
intros H1 H2 H3. unfold wiv2z, z2w. cbn [fst snd]. rewrite !u_w64 by lia. destruct iv; cbn in *. f_equal. lia.
Qed.

Lemma iv_overlap_false_iff (a n b m : word) :
iv_overlap a n b m = false <-> (u a + u n <= u b \/ u b + u m <= u a).
Proof.
unfold iv_overlap. rewrite andb_false_iff, !Z.ltb_ge. lia.
Qed.

Lemma region_free_incl l l' a n : incl l' l -> region_free l a n = true -> region_free l' a n = true.
Proof.
intros Hi H. apply region_free_intro. intros b s Hin. eapply State.region_free_In; [exact H| apply Hi; exact Hin].
Qed.

Lemma region_free_app l1 l2 a n : region_free (l1 ++ l2) a n = true <-> region_free l1 a n = true /\ region_free l2 a n = true.
Proof.
split.
- intros H. split; (eapply region_free_incl; [| exact H]); intros x Hx; apply in_app_iff; auto.
- intros [H1 H2]. apply region_free_intro. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (State.region_free_In _ _ _ _ _ H1 Hin)| exact (State.region_free_In _ _ _ _ _ H2 Hin)].
Qed.

Lemma region_free_sub l (a n a' n' : word) :
u a <= u a' -> u a' + u n' <= u a + u n -> region_free l a n = true -> region_free l a' n' = true.
Proof.
intros H1 H2 H. apply region_free_intro. intros b s Hin. pose proof (QVsB.region_free_In _ _ _ _ _ H Hin) as F.
apply iv_overlap_false_iff. pose proof (u_range n'). lia.
Qed.

Lemma region_free_iff l (a n : word) :
region_free l a n = true <-> forall b s, In (b, s) l -> u a + u n <= u b \/ u b + u s <= u a.
Proof.
split.
- intros H b s Hin. exact (QVsB.region_free_In _ _ _ _ _ H Hin).
- intros H. apply region_free_intro. intros b s Hin. apply iv_overlap_false_iff. exact (H b s Hin).
Qed.

Lemma map_remove_filter l a : map_remove l a = List.filter (fun p => negb (bv_eqb (fst p) a)) l.
Proof. reflexivity. Qed.

Lemma In_map_remove l a e : In e (map_remove l a) <-> In e l /\ fst e <> a.
Proof.
rewrite map_remove_filter, filter_In. split; intros [H1 H2]; split; auto.
- intros E. rewrite E, bv_eqb_refl in H2. discriminate.
- destruct (bv_eqb (fst e) a) eqn:B; [|reflexivity]. apply Fs.bv_eqb_eq in B. contradiction.
Qed.

Lemma incl_map_remove l a : incl (map_remove l a) l.
Proof. intros e He. apply In_map_remove in He. tauto. Qed.

Section Ledger.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).

Variables TOT0 N0 : Z.

Definition KHI : Z := kHighMemBeg.

Record ll_ok : Prop := mkLL {
llo_lay   : lay_ok L;
llo_shoff : lv_shoff LV = kShadowOffset;
llo_perm  : forall r, In r PERM -> 0 < fst r /\ fst r < snd r /\ snd r <= kCeil;

llo_avoid : forall iv, In iv (al_avoid L) -> fst iv < snd iv /\ forall y, fst iv <= y < snd iv ->
(exists r, In r PERM /\ fst r <= y < snd r) \/ (exists iv', In iv' (lv_base LV) /\ fst iv' <= y < snd iv') \/ kCeil <= y;
llo_space : exists r, In r PERM /\ excl_entry LV (z2w r) = false /\
fst r <= al_space_beg L /\ al_space_beg L + 2^37 <= snd r;
llo_parr  : exists r, In r PERM /\ excl_entry LV (z2w r) = false /\
fst r <= al_ptrarr L /\ al_ptrarr L + 8388608 <= snd r;
llo_band  : exists r, In r PERM /\ fst r <= kShadowOffset + KHI / 8 /\ kShadowOffset + kCeil / 8 + 1 <= snd r;
llo_lband : exists r, In r PERM /\ fst r <= kShadowOffset /\ kShadowOffset + kLowEnd / 8 + 1 <= snd r;
llo_bands : forall y, kLowEnd <= y < KHI -> exists r, In r PERM /\ fst r <= y < snd r;
llo_exband: forall y, kLowEnd <= y < KHI -> in_zivs y (lv_excl LV) = true;
llo_budget: 0 <= BUDGET;
llo_gap   : 0 <= TOT0 /\ 0 <= N0 /\
page_size + (TOT0 + kMaxCnt * kMaxChunk) + (N0 + kMaxCnt + 1) * (kMaxChunk + 4095) <= QybZ.Mq0.alloc_ceiling
}.

Definition pdec (x y : word * word) : {x = y} + {x <> y}.
Proof. decide equality; apply weq_dec. Defined.

Definition perm_ok (g : ghost) (h : VmMaps) (r : Z * Z) : Prop :=
In (z2w r) (vm_maps h) /\
(forall e, In e (vm_maps h) -> e = z2w r \/ zdisj (wiv2z e) r) /\
count_occ pdec (vm_maps h) (z2w r) = 1%nat /\
region_free (vm_reserved h) (fst (z2w r)) (snd (z2w r)) = true /\
(forall c, In c (g_chunks g) -> zdisj r (civ c)).

Definition chunk_ok (h : VmMaps) (c : Z * Z) : Prop :=
let a := fst c in let n := snd c in
0 <= a /\ a mod 4096 = 0 /\ 0 < n /\ n <= kMaxChunk /\ n mod 4096 = 0 /\ (a + n <= kLowEnd \/ KHI <= a) /\ a + n <= kCeil /\
In (cent c) (vm_maps h) /\
(forall e, In e (vm_maps h) -> fst e = w64 a -> snd e = w64 n) /\
region_free (vm_reserved h ++ map_remove (vm_maps h) (w64 a)) (w64 a) (w64 n) = true /\
excl_entry LV (cent c) = false.

Definition app_cov (h : VmMaps) (y : Z) : Prop :=
(exists e, In e (vm_reserved h) /\ bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e))
\/ (exists r, In r PERM /\ excl_entry LV (z2w r) = false /\ fst r <= y < snd r).

Record KI (g : ghost) (mo : Model) : Prop := mkKI {
ki_x    : xinvA LV mo;
ki_em   : excl_mapped LV mo;
ki_perm : forall r, In r PERM -> perm_ok g (m_vmmaps mo) r;
ki_ch   : forall c, In c (g_chunks g) -> chunk_ok (m_vmmaps mo) c;
ki_nd   : List.NoDup (map fst (g_chunks g));
ki_ne   : forall e, In e (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned (snd e);
ki_sp0  : 0 <= g_spent g;
ki_phi  : Phi LV mo + (BUDGET - g_spent g) <= vm_limit (m_vmmaps mo);
ki_resv : forall e, In e (vm_reserved (m_vmmaps mo)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= kLowEnd;
ki_base : forall iv y, In iv (lv_base LV) -> fst iv <= y < snd iv ->
alloc_top (m_vmmaps mo) <= y \/ app_cov (m_vmmaps mo) y \/ (exists y', app_cov (m_vmmaps mo) y' /\ y = shz LV y');
ki_tot  : gw_sizes (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= TOT0 + zsum (map snd (g_chunks g)) /\
zlen (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= N0 + zlen (g_chunks g)
}.

Lemma KI_drift g mo mo' : drift LV mo mo' -> KI g mo -> KI g mo'.
Proof.
intros Hd K. pose proof (drift_vmeq LV _ _ Hd) as Hv. pose proof Hv as [Hvm _].
constructor; try (rewrite Hvm; apply K).
- eapply xinvA_drift; [exact Hd| apply K].
- eapply excl_mapped_vmeq; [exact Hv| apply K].
- apply (ki_nd _ _ K).
- apply (ki_sp0 _ _ K).
- rewrite (drift_Phi LV _ _ Hd), Hvm. apply K.
Qed.

Lemma kind_anon : mmap_kind 0 QKTr.PROT_RW QKTr.FL_ANON = KAnon.
Proof. reflexivity. Qed.
Lemma kind_fixed addr : mmap_kind addr QKTr.PROT_RW QKTr.FL_FIXED = KFixed.
Proof. unfold mmap_kind. cbn. reflexivity. Qed.
Lemma kind_remap addr : mmap_kind addr QKTr.PROT_RW QKTr.FL_FIXED_NR = KRemap.
Proof. unfold mmap_kind. cbn. reflexivity. Qed.

Lemma rlen_aligned len : len mod 4096 = 0 -> rlen len = len.
Proof.
intros H. unfold rlen, page_round_up_Z, page_size.
pose proof (Z.div_mod len 4096 ltac:(lia)) as D. rewrite H in D.
replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia.
rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

Lemma mmap_len_rlen len : mmap_len len = rlen len.
Proof. reflexivity. Qed.

Lemma rlenw_w64 len : len mod 4096 = 0 -> rlenw len = w64 len.
Proof. intros H. unfold rlenw, w64. rewrite rlen_aligned by exact H. reflexivity. Qed.

Lemma sec_cost_cost_anon len : len mod 4096 = 0 -> cost_anon len = sec_cost len.
Proof. intros H. unfold cost_anon, sh_cost, sec_cost, kPage. rewrite rlen_aligned by exact H. lia. Qed.

Lemma dec_anonA_grant_shape len avoid (r a n : word) ws :
dec_anonA len avoid (mkEffectU r ws [(a, n)] [] [] []) =
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && grant_ok len (bv_unsigned r)
&& avoids (bv_unsigned r) (mmap_len len) avoid && wshape_ok (bv_unsigned r) (mmap_len len) ws
&& wcover_ok (bv_unsigned r) (mmap_len len) ws
then Some (AOk (bv_unsigned r)) else None.
Proof. destruct ws; reflexivity. Qed.

Lemma dec_anonA_grant len avoid (a : word) ws :
len mod 4096 = 0 ->
grant_ok len (bv_unsigned a) = true -> avoids (bv_unsigned a) len avoid = true ->
wshape_ok (bv_unsigned a) len ws = true -> wcover_ok (bv_unsigned a) len ws = true ->
dec_anonA len avoid (rsp_grant a (rlenw len) ws) = Some (AOk (bv_unsigned a)).
Proof.
intros Hm Hg Hav Hws Hwc. unfold rsp_grant. rewrite dec_anonA_grant_shape.
rewrite mmap_len_rlen, (rlen_aligned len Hm), Hg, Hav, Hws, Hwc, (rlenw_w64 len Hm). unfold w64. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma zbytes_zrange lo k : 0 <= lo -> lo + Z.of_nat k <= 2^64 -> map bv_unsigned (zbytes lo k) = zrange lo k.
Proof.
revert lo. induction k as [|k IH]; intros lo H0 Hk; cbn [zbytes zrange map]; [reflexivity|].
rewrite unsigned_lit by lia. rewrite (IH (lo + 1)) by lia. reflexivity.
Qed.

Lemma wcover_ok_all (a n : word) ws :
lv_shoff LV = kShadowOffset -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= kCeil ->
map fst ws = bytes_of (shadow_iv LV a n) ->
wcover_ok (bv_unsigned a) (bv_unsigned n) ws = true.
Proof.
intros Hsh Hn Hc Hrev. unfold wcover_ok. apply zlist_eqb_eq. rewrite <- map_map, Hrev.
unfold bytes_of, shadow_iv, sh_iv, wiv2z, shz. cbn [fst snd]. rewrite Hsh. unfold sh_lo, sh_hi.
pose proof (u_range a). rewrite kCeil_val in Hc. unfold kShadowOffset.
replace (2147450880 + (bv_unsigned a + bv_unsigned n - 1) / 8 + 1 - (2147450880 + bv_unsigned a / 8))
with ((bv_unsigned a + bv_unsigned n - 1) / 8 + 1 - bv_unsigned a / 8) by lia.
apply zbytes_zrange; [Z.div_mod_to_equations; lia|].
rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Lemma wshape_ok_reveal LV' mo (a n : word) ws :
lv_shoff LV' = kShadowOffset ->
map fst ws = reveal LV' mo a n -> wunit ws = true ->
wshape_ok (bv_unsigned a) (bv_unsigned n) ws = true.
Proof.
intros Hsh Hrev Hwu. unfold wshape_ok. apply forallb_forall. intros w Hw.
unfold wunit in Hwu. rewrite forallb_forall in Hwu. rewrite (Hwu w Hw), andb_true_r.
assert (Hin : In (fst w) (reveal LV' mo a n)) by (rewrite <- Hrev; apply in_map; exact Hw).
apply (reveal_In LV') in Hin as [_ Hz]; [| unfold shoff_ok; rewrite Hsh; unfold kShadowOffset; lia].
unfold shadow_iv, sh_iv, wiv2z, zin in Hz. cbn [fst snd] in Hz.
unfold shz in Hz. rewrite Hsh in Hz. unfold sh_lo, sh_hi.
apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
Qed.

Lemma dec_fixedA_grant addr len :
len mod 4096 = 0 ->
dec_fixedA addr len (rsp_grant (w64 addr) (rlenw len) []) = Some (AOk addr).
Proof.
intros Hm. unfold dec_fixedA, rsp_grant. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
unfold w64. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma dec_remapA_ok addr len :
len mod 4096 = 0 ->
dec_remapA addr len (rsp_remap (w64 addr) (rlenw len)) = Some (AOk addr).
Proof.
intros Hm. unfold dec_remapA, dec_fixedA_full, rsp_remap. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
unfold w64. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma ucover_ok_conceal mo' addr len :
lv_shoff LV = kShadowOffset -> len mod 4096 = 0 -> 0 < len -> 0 <= addr -> addr + len <= kCeil ->
ucover_ok addr (mmap_len len) (conceal LV mo' (w64 addr) (rlenw len)) = true.
Proof.
intros Hsh Hm Hl Ha Hc. rewrite mmap_len_rlen, (rlen_aligned len Hm). unfold ucover_ok. apply forallb_forall. intros u Hu.
unfold conceal in Hu. apply in_map_iff in Hu as (x & <- & Hx). apply filter_In in Hx as [Hx _]. cbn [fst snd].
apply (bytes_of_shadow LV) in Hx; [| unfold shoff_ok; rewrite Hsh; unfold kShadowOffset; lia].
unfold shadow_iv, sh_iv, wiv2z, zin, shz in Hx. cbn [fst snd] in Hx. rewrite Hsh in Hx.
rewrite (rlenw_w64 len Hm) in Hx. unfold w64 in Hx. rewrite kCeil_val in Hc. rewrite !unsigned_lit in Hx by lia.
apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
change (bv_unsigned (Z_to_bv 64 1)) with 1. unfold sh_lo, sh_hi.
apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.leb_le; lia].
Qed.

Lemma dec_munmapA_ok mo' addr len :
lv_shoff LV = kShadowOffset -> len mod 4096 = 0 -> 0 < len -> 0 <= addr -> addr + len <= kCeil ->
dec_munmapA addr len (rsp_munmap LV mo' (w64 addr) (rlenw len)) = Some (AOk 0).
Proof.
intros Hsh Hm Hl Ha Hc. unfold dec_munmapA, rsp_munmap. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
change (bv_unsigned (Z_to_bv 64 0)) with 0. cbn [Z.eqb andb].
rewrite (ucover_ok_conceal mo' addr len Hsh Hm Hl Ha Hc), andb_true_r.
unfold w64. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma reserved_grant mo a n : vm_reserved (m_vmmaps (grant_model mo a n)) = vm_reserved (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma reserved_commit mo a n : vm_reserved (m_vmmaps (commit_model mo a n)) = vm_reserved (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma reserved_remap mo a n : vm_reserved (m_vmmaps (remap_model mo a n)) = vm_reserved (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma reserved_munmap mo a n : vm_reserved (m_vmmaps (munmap_model mo a n)) = vm_reserved (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma mbase_commit mo a n : vm_mmap_base (m_vmmaps (commit_model mo a n)) = vm_mmap_base (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mbase_remap mo a n : vm_mmap_base (m_vmmaps (remap_model mo a n)) = vm_mmap_base (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mbase_munmap mo a n : vm_mmap_base (m_vmmaps (munmap_model mo a n)) = vm_mmap_base (m_vmmaps mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma gw_sizes_app l1 l2 : gw_sizes (l1 ++ l2) = gw_sizes l1 + gw_sizes l2.
Proof. induction l1 as [|x l1 IH]; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma gw_sizes_filter_le f l : gw_sizes (List.filter f l) <= gw_sizes l /\ (length (List.filter f l) <= length l)%nat.
Proof.
induction l as [|x l IH]; cbn; [split; [lia| constructor]|]. pose proof (u_range (snd x)).
destruct (f x); cbn; destruct IH; split; lia.
Qed.

Lemma gw_sizes_map_remove l (a n : word) :
In (a, n) l -> gw_sizes (map_remove l a) + bv_unsigned n <= gw_sizes l /\ (length (map_remove l a) < length l)%nat.
Proof.
induction l as [|x l IH]; intros Hin; [destruct Hin|]. rewrite map_remove_filter. cbn [List.filter].
destruct Hin as [->|Hin].
- cbn [fst]. rewrite bv_eqb_refl. cbn [negb gw_sizes length snd]. rewrite <- map_remove_filter.
pose proof (gw_sizes_filter_le (fun p => negb (bv_eqb (fst p) a)) l) as [A B]. rewrite <- map_remove_filter in A, B. lia.
- destruct (IH Hin) as [A B]. pose proof (u_range (snd x)). rewrite <- map_remove_filter.
destruct (negb (bv_eqb (fst x) a)); cbn [gw_sizes length]; lia.
Qed.

Lemma count_occ_cons_neq (x y : word * word) l : x <> y -> count_occ pdec (x :: l) y = count_occ pdec l y.
Proof. intros H. cbn. destruct (pdec x y); [contradiction| reflexivity]. Qed.

Lemma count_occ_filter_keep (f : word * word -> bool) l y :
f y = true -> count_occ pdec (List.filter f l) y = count_occ pdec l y.
Proof.
intros Hf. induction l as [|x l IH]; [reflexivity|]. cbn.
destruct (pdec x y) as [->|Hne].
- rewrite Hf. cbn. destruct (pdec y y); [| contradiction]. rewrite IH. reflexivity.
- destruct (f x); [cbn; destruct (pdec x y); [contradiction|]|]; exact IH.
Qed.

Lemma overlap_sum_perm_range l (r : Z * Z) lo hi :
(forall e, In e l -> e = z2w r \/ zdisj (wiv2z e) r) ->
0 < fst r -> fst r < snd r -> snd r <= kCeil ->
fst r <= lo -> lo <= hi -> hi <= snd r ->
overlap_sum l lo hi <= (hi - lo) * Z.of_nat (count_occ pdec l (z2w r)).
Proof.
intros Hl R1 R2 R3 H1 H2 H3. rewrite kCeil_val in R3.
induction l as [|e l IH].
- rewrite overlap_sum_nil. cbn. lia.
- rewrite overlap_sum_cons. cbn [count_occ].
assert (IH' : overlap_sum l lo hi <= (hi - lo) * Z.of_nat (count_occ pdec l (z2w r))) by (apply IH; intros e' He'; apply Hl; right; exact He').
destruct (pdec e (z2w r)) as [->|Hne].
+ rewrite Nat2Z.inj_succ. pose proof (iv_count_in_rng_le (z2w r) lo hi H2). lia.
+ destruct (Hl e (or_introl eq_refl)) as [E|Hd]; [contradiction|].
rewrite (iv_count_in_rng_disjoint e lo hi); [lia|].
unfold zdisj, wiv2z in Hd. unfold B, S. destruct e as [b sz]; cbn [fst snd] in *. lia.
Qed.

Lemma remove_first_nodup (x : Z * Z) l c :
List.NoDup (map fst l) -> In x l -> In c (remove_first x l) -> In c l /\ fst c <> fst x.
Proof.
induction l as [|y l IH]; intros ND Hx Hc; [destruct Hc|].
cbn [map] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
cbn [remove_first] in Hc.
destruct (Z.eqb_spec (fst y) (fst x)) as [E1|N1]; [destruct (Z.eqb_spec (snd y) (snd x)) as [E2|N2]|]; cbn [andb] in Hc.
- split; [right; exact Hc|]. intros E. apply Hny. rewrite E1, <- E. apply in_map. exact Hc.
- destruct Hx as [->|Hx]; [congruence|]. exfalso. apply Hny. rewrite E1. apply in_map. exact Hx.
- destruct Hx as [->|Hx]; [congruence|]. destruct Hc as [<-|Hc]; [split; [left; reflexivity| exact N1]|].
destruct (IH NDl Hx Hc) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

Lemma remove_first_nodup_fst (x : Z * Z) l : List.NoDup (map fst l) -> List.NoDup (map fst (remove_first x l)).
Proof.
induction l as [|y l IH]; intros ND; [constructor|]. cbn [map] in ND. inversion ND as [|y0 l0 Hny NDl]; subst.
cbn [remove_first]. destruct (_ && _); [exact NDl|]. cbn [map]. constructor; [| apply IH; exact NDl].
intros Hin. apply Hny. apply in_map_iff in Hin as (c & <- & Hc). apply in_map. eapply remove_first_incl. exact Hc.
Qed.

Section Events.
Hypothesis LL : ll_ok.

Definition aok0 : evA -> ansA -> Prop := QQwg.aok astate0.

Lemma perm_u r : In r PERM ->
bv_unsigned (fst (z2w r)) = fst r /\ bv_unsigned (snd (z2w r)) = snd r - fst r /\ wiv2z (z2w r) = r /\
0 < fst r /\ fst r < snd r /\ snd r <= kCeil /\ kCeil = 0x7fffff800000.
Proof.
intros Hr. pose proof (llo_perm LL r Hr) as (A & B & C). rewrite kCeil_val in C.
split; [unfold z2w; cbn [fst snd]; apply u_w64; lia|]. split; [unfold z2w; cbn [fst snd]; apply u_w64; lia|].
split; [apply wiv2z_z2w; lia|]. rewrite kCeil_val. lia.
Qed.

Lemma chunk_u g mo c : KI g mo -> In c (g_chunks g) ->
bv_unsigned (w64 (fst c)) = fst c /\ bv_unsigned (w64 (snd c)) = snd c /\ kCeil = 0x7fffff800000.
Proof.
intros K Hc. pose proof (ki_ch _ _ K c Hc) as (C0 & _ & C2 & _ & _ & _ & C6 & _). rewrite kCeil_val in C6.
split; [apply u_w64; lia|]. split; [apply u_w64; lia| apply kCeil_val].
Qed.

Lemma ki_top g mo : KI g mo -> QybZ.Mq0.alloc_ceiling <= alloc_top (m_vmmaps mo).
Proof.
intros K. pose proof (ki_x _ _ K) as [_ [(_ & _ & _ & Hsp) _]]. exact (alloc_ceiling_le_alloc_top _ Hsp).
Qed.

Lemma ki_top_hi g mo : KI g mo -> alloc_top (m_vmmaps mo) <= kCeil.
Proof. intros K. pose proof (ki_x _ _ K) as [_ [_ [_ [T _]]]]. exact T. Qed.

Lemma gw_sizes_zsumf l : gw_sizes l = zsumf esz l.
Proof. induction l as [|x l IH]; cbn [gw_sizes zsumf fold_right]; [reflexivity|]. fold (zsumf esz l). rewrite <- IH. reflexivity. Qed.

Lemma ki_gap g mo len : KI g mo -> 0 <= len <= kMaxChunk -> zlen (g_chunks g) + 1 <= kMaxCnt ->
vm_gap_available (m_vmmaps mo) len = true.
Proof.
intros K Hl Hcnt. pose proof (ki_tot _ _ K) as [T1 T2]. pose proof (llo_gap LL) as (G0 & G1 & G2). pose proof (ki_top g mo K) as Htop.
assert (Hsum : zsum (map snd (g_chunks g)) <= kMaxCnt * kMaxChunk).
{ etransitivity; [apply (zsum_map_le snd (fun _ => kMaxChunk))|].
- intros c Hc. pose proof (ki_ch _ _ K c Hc) as (_ & _ & _ & C3 & _). exact C3.
- rewrite zsum_map_const. pose proof (zlen_nonneg (g_chunks g)). unfold kMaxChunk, kMaxCnt in *. nia. }
apply (vm_gap_available_of_count (m_vmmaps mo) len (N0 + kMaxCnt) (TOT0 + kMaxCnt * kMaxChunk)); [lia| | |].
- unfold zlen in T2, Hcnt. lia.
- rewrite <- gw_sizes_zsumf. lia.
- assert ((N0 + kMaxCnt + 1) * (len + 4095) <= (N0 + kMaxCnt + 1) * (kMaxChunk + 4095)) by (unfold kMaxCnt in *; nia). lia.
Qed.

Lemma ev_anon_safe g mo len avoid :
KI g mo -> gev L BUDGET g (EvMapAnon len avoid) -> nsafeA LV (NMmap 0 len QKTr.PROT_RW QKTr.FL_ANON) mo.
Proof.
intros K (Hlen & Hmod & H40 & _ & _ & Hb & Hcnt).
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR fixed_contained fixed_free Phi cost_anon cost_commit cost_fixed fixed_gates range_vis excl_mapped rlenw rlen m_vmmaps Z.pow Z.le Z.lt vm_gap_available].
rewrite kind_anon.
split; [exact Hlen|]. split; [unfold kMaxChunk in H40; lia|]. split; [apply (ki_em _ _ K)|].
split; [rewrite sec_cost_cost_anon by exact Hmod; pose proof (ki_phi _ _ K); lia|].
rewrite (rlen_aligned len Hmod). apply (ki_gap g mo len K); [lia| exact Hcnt].
Qed.

Lemma placement_split g mo (a n : word) :
KI g mo -> 0 < bv_unsigned n ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
bv_unsigned a + bv_unsigned n <= kLowEnd \/ KHI <= bv_unsigned a.
Proof.
intros K Hn Hfree. destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned n) kLowEnd) as [H|H]; [left; exact H|].
destruct (Z.le_gt_cases KHI (bv_unsigned a)) as [H'|H']; [right; exact H'|]. exfalso.
set (y := Z.max (bv_unsigned a) kLowEnd).
assert (Hy : kLowEnd <= y < KHI) by (unfold y, kLowEnd, KHI, kHighMemBeg in *; lia).
destruct (llo_bands LL y Hy) as (r & Hr & R1).
pose proof (ki_perm _ _ K r Hr) as (P1 & _). pose proof (llo_perm LL r Hr) as (A & B & C).
apply region_free_app in Hfree as [_ Hfm]. rewrite region_free_iff in Hfm.
specialize (Hfm (fst (z2w r)) (snd (z2w r)) ltac:(rewrite <- surjective_pairing; exact P1)).
unfold z2w in Hfm. cbn [fst snd] in Hfm. rewrite !u_w64 in Hfm by (rewrite kCeil_val in C; lia).
unfold y in *. lia.
Qed.

Lemma shz_in_band y : 0 <= y < 2^47 -> kLowEnd <= shz LV y < KHI.
Proof.
intros Hy. unfold shz. rewrite (llo_shoff LL). unfold kShadowOffset, kLowEnd, KHI, kHighMemBeg.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert (y / 8 < 2^44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma app_cov_fresh g mo (a n : word) y :
KI g mo -> region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
bv_unsigned a <= y < bv_unsigned a + bv_unsigned n -> app_cov (m_vmmaps mo) y -> False.
Proof.
intros K Hfree Hy [(e & He & E1)|(r & Hr & Hex & R1)].
- apply region_free_app in Hfree as [Hfr _]. rewrite region_free_iff in Hfr.
specialize (Hfr (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact He)). lia.
- pose proof (ki_perm _ _ K r Hr) as (P1 & _). pose proof (llo_perm LL r Hr) as (A & B & C).
apply region_free_app in Hfree as [_ Hfm]. rewrite region_free_iff in Hfm.
specialize (Hfm (fst (z2w r)) (snd (z2w r)) ltac:(rewrite <- surjective_pairing; exact P1)).
unfold z2w in Hfm. cbn [fst snd] in Hfm. rewrite !u_w64 in Hfm by (rewrite kCeil_val in C; lia). lia.
Qed.

Lemma app_cov_bound g mo y : KI g mo -> app_cov (m_vmmaps mo) y -> 0 <= y < 2^47.
Proof.
intros K [(e & He & E1)|(r & Hr & Hex & R1)].
- pose proof (ki_resv _ _ K e He). pose proof (u_range (fst e)). unfold kLowEnd in *. lia.
- pose proof (llo_perm LL r Hr) as (A & B & C). rewrite kCeil_val in C. lia.
Qed.

Lemma fresh_off_base g mo (a n : word) :
KI g mo -> 0 < bv_unsigned n ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
bv_unsigned a + bv_unsigned n <= alloc_top (m_vmmaps mo) ->
forall y iv, bv_unsigned a <= y < bv_unsigned a + bv_unsigned n -> In iv (lv_base LV) -> y < fst iv \/ snd iv <= y.
Proof.
intros K Hn Hfree Htop y iv Hy Hiv. destruct (Z.lt_ge_cases y (fst iv)) as [H|H]; [left; exact H|].
destruct (Z.lt_ge_cases y (snd iv)) as [H'|H']; [| right; exact H']. exfalso.
destruct (ki_base _ _ K iv y Hiv ltac:(lia)) as [Ht|[Hc|(y' & Hc & ->)]].
- lia.
- exact (app_cov_fresh g mo a n y K Hfree Hy Hc).
- pose proof (shz_in_band y' (app_cov_bound g mo y' K Hc)) as Hb.
destruct (placement_split g mo a n K Hn Hfree); lia.
Qed.

Lemma fresh_shadow_uncovered g mo (a n : word) :
KI g mo -> 0 < bv_unsigned n -> bv_unsigned a mod 8 = 0 -> bv_unsigned n mod 8 = 0 ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
bv_unsigned a + bv_unsigned n <= alloc_top (m_vmmaps mo) ->
forall z, zin z (shadow_iv LV a n) = true -> appcov LV mo z = false.
Proof.
intros K Hn Ha8 Hn8 Hfree Htop z Hz. pose proof (ki_top g mo K) as HT.
unfold shadow_iv, sh_iv, wiv2z in Hz. cbn [fst snd] in Hz. apply zin_true in Hz.
destruct (proj1 (sh_iv_iff LV (bv_unsigned a) (bv_unsigned a + bv_unsigned n) z ltac:(lia)) Hz) as (y & Hy & Hs).
assert (Hy47 : 0 <= y < 2^47) by (pose proof (u_range a); pose proof (ki_top_hi g mo K) as HT'; rewrite kCeil_val in HT'; lia).
pose proof (shz_in_band y Hy47) as Hb. rewrite Hs in Hb.
apply appcov_false_intro.
- apply bcov_false_iff. intros iv Hiv. destruct (Z.lt_ge_cases z (fst iv)) as [H|H]; [left; exact H|].
destruct (Z.lt_ge_cases z (snd iv)) as [H'|H']; [| right; exact H']. exfalso.
destruct (ki_base _ _ K iv z Hiv ltac:(lia)) as [Ht|[Hc|(y' & Hc & Hs')]].
+ unfold QybZ.Mq0.alloc_ceiling, KHI, kHighMemBeg in *. lia.
+ destruct Hc as [(e & He & E1)|(r & Hr & Hex & R1)].
* pose proof (ki_resv _ _ K e He). unfold kLowEnd in *. lia.
*
pose proof (llo_exband LL z Hb) as HX. apply in_zivs_true in HX as (x & Hx & Hzx).
pose proof (proj1 (excl_entry_false LV (z2w r)) Hex x Hx) as D. pose proof (llo_perm LL r Hr) as (A & B & C).
pose proof (perm_u r Hr) as (U1 & U2 & _). rewrite U1, U2 in D.
assert (D1 : fst x < snd x) by lia. assert (D2 : 0 < snd r - fst r) by lia.
destruct (D D1 D2); lia.
+
rewrite <- Hs in Hs'. unfold shz in Hs'. assert (Hg : y / 8 = y' / 8) by lia.
assert (Hy' : bv_unsigned a <= y' < bv_unsigned a + bv_unsigned n) by (clear -Hg Hy Ha8 Hn8; Z.div_mod_to_equations; lia).
exact (app_cov_fresh g mo a n y' K Hfree Hy' Hc).
- pose proof (llo_exband LL z Hb) as HX. apply in_zivs_true in HX as (x & Hx & Hzx).
exact (ecov_excl LV mo x z Hx Hzx).
Qed.

Lemma avoid_complete g mo (a n : word) len avoid :
KI g mo -> incl avoid (al_avoid L ++ map civ (g_chunks g)) ->
bv_unsigned n = len -> 0 < len ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
bv_unsigned a + bv_unsigned n <= alloc_top (m_vmmaps mo) ->
avoids (bv_unsigned a) len avoid = true.
Proof.
intros K Hincl Hn Hlen Hfree Htop. unfold avoids. apply forallb_forall. intros iv Hiv. cbn [fst snd].
pose proof Hfree as Hfree0.
apply region_free_app in Hfree as [_ Hfree]. rewrite region_free_iff in Hfree.
destruct (in_app_or _ _ _ (Hincl _ Hiv)) as [Ha|Hc].
- apply orb_true_intro.
destruct (Z.le_gt_cases (bv_unsigned a + len) (fst iv)) as [H1|H1]; [left; apply Z.leb_le; exact H1|].
destruct (Z.le_gt_cases (snd iv) (bv_unsigned a)) as [H2|H2]; [right; apply Z.leb_le; exact H2|].
exfalso. destruct (llo_avoid LL iv Ha) as [Hne HY]. set (y := Z.max (bv_unsigned a) (fst iv)).
assert (Hy1 : fst iv <= y < snd iv) by (unfold y; lia). assert (Hy2 : bv_unsigned a <= y < bv_unsigned a + bv_unsigned n) by (unfold y; lia).
destruct (HY y Hy1) as [(r & Hr & R1)|[(iv' & Hiv' & R1)|Hk]].
+ pose proof (ki_perm _ _ K r Hr) as (Hin & _). pose proof (perm_u r Hr) as (U1 & U2 & _ & R2 & R3 & R4 & _).
specialize (Hfree (fst (z2w r)) (snd (z2w r)) ltac:(rewrite <- surjective_pairing; exact Hin)). rewrite U1, U2 in Hfree. lia.
+ destruct (fresh_off_base g mo a n K ltac:(lia) Hfree0 Htop y iv' Hy2 Hiv'); lia.
+ pose proof (ki_top_hi g mo K). lia.
- apply in_map_iff in Hc as (c & <- & Hc). pose proof (chunk_u g mo c K Hc) as (U1 & U2 & _).
pose proof (ki_ch _ _ K c Hc) as (C0 & _ & C2 & _ & _ & _ & C6 & Cin & _).
specialize (Hfree (w64 (fst c)) (w64 (snd c)) Cin). rewrite U1, U2 in Hfree. unfold civ. cbn [fst snd].
apply orb_true_intro. destruct Hfree; [left|right]; apply Z.leb_le; lia.
Qed.

Lemma ev_anon_step g mo len avoid rsp mo' evs :
KI g mo -> gev L BUDGET g (EvMapAnon len avoid) ->
nstep_raw LV (NMmap 0 len QKTr.PROT_RW QKTr.FL_ANON) mo rsp mo' evs ->
exists ans, dec_anonA len avoid rsp = Some ans /\ aok0 (EvMapAnon len avoid) ans /\
KI (gstep g (EvMapAnon len avoid) ans) mo'.
Proof.
intros K G Hst. pose proof G as (Hlen & Hmod & H40 & Hav1 & Hav2 & Hb & Hcnt0).
pose proof (ev_anon_safe g mo len avoid K G) as Hsafe.
pose proof (Phi_nstep_raw LV _ _ _ _ _ (ki_x _ _ K) Hsafe Hst) as [HPhi Hlim].
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR anon_place_ok grant_model rsp_grant rsp_err rsp_remap reveal wunit rlenw rlen fixed_contained fixed_free commit_model remap_model m_vmmaps] in Hst.
rewrite kind_anon in Hst.

destruct Hst as [_ (a & ws & Hpl & Hrev & Hwu & -> & ->)].

unfold anon_place_ok in Hpl. apply andb_prop in Hpl as [Hpl Hfree].
apply andb_prop in Hpl as [Hpl Htop]. apply andb_prop in Hpl as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
pose proof (ki_top_hi g mo K) as HtopC.
assert (Hceil : bv_unsigned a + len <= kCeil) by (rewrite (rlen_aligned len Hmod) in Htop; lia).
rewrite (rlen_aligned len Hmod) in *. rewrite (rlenw_w64 len Hmod) in *. change (Z_to_bv 64 len) with (w64 len) in Hfree.
unfold page_size in Hal.
pose proof (u_range a) as Hau. pose proof Hceil as HceilV. rewrite kCeil_val in HceilV.
assert (Hwl : bv_unsigned (w64 len) = len) by (apply u_w64; lia).
pose proof (ki_sp0 _ _ K) as Hsp0.
assert (Hsc : 2 * len + 8192 <= sec_cost len).
{ unfold sec_cost, kPage. pose proof (Z.div_pos len 32768 ltac:(lia) ltac:(lia)). lia. }

assert (Hka : bv_unsigned a + len <= kLowEnd \/ KHI <= bv_unsigned a).
{ pose proof (placement_split g mo a (w64 len) K ltac:(rewrite Hwl; exact Hlen) Hfree) as P. rewrite Hwl in P. exact P. }
assert (Hav : avoids (bv_unsigned a) len avoid = true) by (apply (avoid_complete g mo a (w64 len)); auto; rewrite Hwl; lia).
assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a (w64 len) = true) by (apply region_free_app in Hfree; apply Hfree).
assert (Hexcl : excl_entry LV (a, w64 len) = false).
{ apply (fresh_not_excl LV mo a (w64 len)); [apply (ki_em _ _ K)| rewrite Hwl; exact Hlen| exact Hfm]. }
pose proof Hfree as HfreeD. apply region_free_app in HfreeD as [Hfr HfmD]. rewrite region_free_iff in HfmD. rewrite region_free_iff in Hfr.
assert (Hws : wshape_ok (bv_unsigned a) len ws = true).
{ rewrite <- Hwl. apply (wshape_ok_reveal LV mo); [apply (llo_shoff LL)| exact Hrev| exact Hwu]. }

assert (HSO : shoff_ok LV) by (unfold shoff_ok; rewrite (llo_shoff LL); unfold kShadowOffset; lia).
assert (Ha8 : bv_unsigned a mod 8 = 0) by (clear -Hal; Z.div_mod_to_equations; lia).
assert (Hn8 : bv_unsigned (w64 len) mod 8 = 0) by (rewrite Hwl; clear -Hmod; unfold kPage in Hmod; Z.div_mod_to_equations; lia).
assert (Hall : reveal LV mo a (w64 len) = bytes_of (shadow_iv LV a (w64 len))).
{ apply (reveal_all LV HSO mo a (w64 len)).
- rewrite Hwl. exact Hlen.
- exact Ha8.
- exact Hn8.
- apply (fresh_range_uncovered LV mo (vm_reserved (m_vmmaps mo)) a (w64 len) Hfree).
apply (fresh_off_base g mo a (w64 len) K ltac:(rewrite Hwl; exact Hlen) Hfree). rewrite Hwl. exact Htop.
- apply (fresh_shadow_uncovered g mo a (w64 len) K ltac:(rewrite Hwl; exact Hlen) Ha8 Hn8 Hfree). rewrite Hwl. exact Htop. }
assert (Hwc : wcover_ok (bv_unsigned a) len ws = true).
{ rewrite <- Hwl. apply wcover_ok_all; [apply (llo_shoff LL)| rewrite Hwl; exact Hlen| rewrite Hwl; exact Hceil| rewrite Hrev; exact Hall]. }
exists (AOk (bv_unsigned a)). split.
{ rewrite <- (rlenw_w64 len Hmod). apply dec_anonA_grant; [exact Hmod| |exact Hav| exact Hws| exact Hwc]. unfold grant_ok. rewrite mmap_len_rlen, (rlen_aligned len Hmod).
unfold page_size. rewrite Hal, Z.eqb_refl. cbn [andb]. apply andb_true_intro. split; [apply Z.ltb_lt; exact Hpos| apply Z.leb_le; exact Hceil]. }
split.
{ cbn. split; [unfold kPage; exact Hal|]. split; [exact Hpos|]. unfold zavoids. unfold avoids in Hav. exact Hav. }

cbn [gstep].
assert (Hcent : cent (bv_unsigned a, len) = (a, w64 len)) by (unfold cent; cbn [fst snd]; rewrite w64_u; reflexivity).
assert (HcostA : costA LV (NMmap 0 len QKTr.PROT_RW QKTr.FL_ANON) mo (rsp_grant a (w64 len) ws) = sec_cost len).
{ unfold costA. cbn [eff_ret rsp_grant]. rewrite (placed_not_errno0 a len) by lia. rewrite kind_anon. apply sec_cost_cost_anon. exact Hmod. }
rewrite HcostA in HPhi.
constructor; cbn [g_chunks g_spent].
- pose proof (ki_x _ _ K) as [HF [HW [HX HY]]].
eapply xinvA_intro; [apply vm_onlyA_grant| exact HF| apply wf_grant; [exact HW| rewrite Hwl; lia]| |].
+ apply excl_inside_grant; [exact HX| exact Hexcl].
+ apply mbt_grant; [exact HY| rewrite Hwl; exact Htop].
- unfold excl_mapped. rewrite maps_grant. intros x y Hx Hy. rewrite covered_cons. apply orb_true_intro. right. exact (ki_em _ _ K x y Hx Hy).
- intros r Hr. pose proof (ki_perm _ _ K r Hr) as (P1 & P2 & P3 & P4 & P5). pose proof (perm_u r Hr) as (U1 & U2 & U3 & R1 & R2 & R3 & _).
assert (Hd : zdisj (bv_unsigned a, bv_unsigned a + len) r).
{ specialize (HfmD (fst (z2w r)) (snd (z2w r)) ltac:(rewrite <- surjective_pairing; exact P1)). rewrite U1, U2, Hwl in HfmD. unfold zdisj. cbn [fst snd]. lia. }
unfold perm_ok. rewrite maps_grant, reserved_grant. split; [right; exact P1|]. split.
{ intros e [<-|He]; [| exact (P2 e He)]. right. unfold wiv2z. cbn [fst snd]. rewrite Hwl. exact Hd. }
split.
{ rewrite count_occ_cons_neq; [exact P3|]. intros E. rewrite <- E in U1, U2. cbn [fst snd] in U1, U2. unfold zdisj in Hd. cbn [fst snd] in Hd. lia. }
split; [exact P4|].
intros c [<-|Hc]; [| exact (P5 c Hc)]. unfold civ. cbn [fst snd]. unfold zdisj in Hd |- *. cbn [fst snd] in *. lia.
- intros c [<-|Hc].
+
unfold chunk_ok. cbn [fst snd]. rewrite Hcent, maps_grant, reserved_grant.
split; [lia|]. split; [exact Hal|]. split; [exact Hlen|]. split; [exact H40|]. split; [exact Hmod|]. split; [exact Hka|].
split; [unfold kCeil; exact Hceil|]. split; [left; reflexivity|]. split.
{ intros e [<-|He]; cbn [fst snd]; [reflexivity|]. rewrite w64_u. intros Efst.
exfalso. specialize (HfmD (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact He)). rewrite Efst, Hwl in HfmD.
pose proof (ki_ne _ _ K e He). lia. }
split; [| exact Hexcl].
rewrite w64_u. cbn [map_remove List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
eapply region_free_incl; [| exact Hfree]. intros e He. apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right]. eapply incl_map_remove. exact He.
+
pose proof (ki_ch _ _ K c Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). pose proof (chunk_u g mo c K Hc) as (V1 & V2 & _).
assert (Hd : bv_unsigned a + len <= fst c \/ fst c + snd c <= bv_unsigned a).
{ specialize (HfmD (w64 (fst c)) (w64 (snd c)) C7). rewrite V1, V2, Hwl in HfmD. exact HfmD. }
unfold chunk_ok. rewrite maps_grant, reserved_grant.
split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
split; [right; exact C7|]. split.
{ intros e [<-|He]; [| exact (C8 e He)]. cbn [fst snd]. intros Efst. exfalso.
assert (bv_unsigned a = fst c) by (rewrite <- V1, <- Efst; reflexivity). lia. }
split; [| exact C10].
assert (Hne : bv_eqb a (w64 (fst c)) = false).
{ destruct (bv_eqb a (w64 (fst c))) eqn:E; [|reflexivity]. apply Fs.bv_eqb_eq in E. exfalso.
assert (bv_unsigned a = fst c) by (rewrite <- V1, <- E; reflexivity). lia. }
cbn [map_remove List.filter fst]. rewrite Hne. cbn [negb]. fold (map_remove (vm_maps (m_vmmaps mo)) (w64 (fst c))).
rewrite region_free_iff. intros b sz Hin. apply in_app_iff in Hin as [Hin|[E|Hin]].
* rewrite region_free_iff in C9. apply C9. apply in_app_iff. left. exact Hin.
* injection E as <- <-. rewrite V1, V2, Hwl. lia.
* rewrite region_free_iff in C9. apply C9. apply in_app_iff. right. exact Hin.
- constructor; [| apply (ki_nd _ _ K)]. cbn [fst]. intros Hin. apply in_map_iff in Hin as (c & Efst & Hc).
pose proof (ki_ch _ _ K c Hc) as (C0 & _ & C2 & _ & _ & _ & C6 & C7 & _). pose proof (chunk_u g mo c K Hc) as (V1 & V2 & _).
specialize (HfmD (w64 (fst c)) (w64 (snd c)) C7). rewrite V1, V2, Hwl in HfmD. lia.
- rewrite maps_grant. intros e [<-|He]; [cbn [snd]; rewrite Hwl; exact Hlen| exact (ki_ne _ _ K e He)].
- lia.
- rewrite Hlim. pose proof (ki_phi _ _ K). lia.
- rewrite reserved_grant. exact (ki_resv _ _ K).
- rewrite top_grant. unfold app_cov. rewrite reserved_grant. exact (ki_base _ _ K).
- pose proof (ki_tot _ _ K) as [T1 T2]. rewrite reserved_grant, maps_grant. cbn [map snd]. rewrite zsum_cons, zlen_cons.
rewrite gw_sizes_app, zlen_app in *. cbn [gw_sizes snd]. rewrite zlen_cons, Hwl. lia.
Qed.

Lemma fixed_target addr len :
in_res L addr len \/ in_parr L addr len ->
exists r, In r PERM /\ excl_entry LV (z2w r) = false /\ fst r <= addr /\ addr + len <= snd r.
Proof.
intros [[H1 H2]|[H1 H2]].
- destruct (llo_space LL) as (r & Hr & He & R1 & R2). exists r. repeat split; auto; lia.
- destruct (llo_parr LL) as (r & Hr & He & R1 & R2). exists r. repeat split; auto; lia.
Qed.

Lemma ev_fixed_facts g mo addr len :
KI g mo -> gev L BUDGET g (EvMapFixed addr len) ->
fixed_contained mo (w64 addr) (rlenw len) = true /\
range_vis LV mo (w64 addr) (rlenw len) /\
cost_commit mo addr len <= len /\
0 < addr /\ addr + len <= kCeil /\
nsafeA LV (NMmap addr len QKTr.PROT_RW QKTr.FL_FIXED) mo.
Proof.
intros K (Hlen & Hmod & Hal & Hwhere & Hb).
destruct (fixed_target addr len Hwhere) as (r & Hr & Hex & H1 & H2).
pose proof (ki_perm _ _ K r Hr) as (P1 & P2 & P3 & P4 & P5). pose proof (perm_u r Hr) as (U1 & U2 & U3 & R1 & R2 & R3 & Ceil).
rewrite (rlenw_w64 len Hmod).
assert (Hwa : bv_unsigned (w64 addr) = addr) by (apply u_w64; lia).
assert (Hwl : bv_unsigned (w64 len) = len) by (apply u_w64; lia).
assert (Hfc : fixed_contained mo (w64 addr) (w64 len) = true).
{ unfold fixed_contained. apply andb_true_intro. split.
- eapply region_free_sub; [| | exact P4]; rewrite ?Hwa, ?Hwl, ?U1, ?U2; lia.
- unfold map_contains. apply existsb_exists. exists (z2w r). split; [exact P1|]. rewrite U1, U2, Hwa, Hwl.
apply andb_true_intro. split; apply Z.leb_le; lia. }
assert (Hvis : range_vis LV mo (w64 addr) (w64 len)).
{ unfold range_vis. rewrite Hwa, Hwl. intros x Hx. apply visible_iff. left.
unfold appcov. apply orb_true_intro. right. unfold ecov, emaps. apply covered_true.
exists (z2w r). split; [apply filter_In; split; [exact P1| rewrite Hex; reflexivity]|]. rewrite U1, U2. lia. }
assert (Hcc : cost_commit mo addr len <= len).
{ unfold cost_commit. rewrite (rlen_aligned len Hmod).
etransitivity; [apply (overlap_sum_perm_range _ r); auto; try lia|]. rewrite P3. cbn. lia. }
split; [exact Hfc|]. split; [exact Hvis|]. split; [exact Hcc|]. split; [lia|]. split; [lia|].
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR fixed_contained fixed_free Phi cost_anon cost_commit cost_fixed fixed_gates range_vis excl_mapped rlenw rlen m_vmmaps Z.pow Z.le Z.lt].
rewrite kind_fixed. rewrite (rlenw_w64 len Hmod). change (Z_to_bv 64 addr) with (w64 addr).
split.
{ unfold fixed_gates. rewrite (rlen_aligned len Hmod). split; [exact Hlen|]. split.
- destruct Hwhere as [[W1 W2]|[W1 W2]]; lia.
- split; [lia|]. split; [exact Hal|]. unfold kCeil in R3. lia. }
split.
{
unfold fixed_top. rewrite (rlen_aligned len Hmod). pose proof (ki_x _ _ K) as [_ [_ [_ [_ MB]]]].
specialize (MB (z2w r) P1). rewrite U1, U2 in MB. lia. }
left. split; [exact Hfc|]. split; [exact Hvis|]. pose proof (ki_phi _ _ K). lia.
Qed.

Lemma ev_fixed_step g mo addr len rsp mo' evs :
KI g mo -> gev L BUDGET g (EvMapFixed addr len) ->
nstep_raw LV (NMmap addr len QKTr.PROT_RW QKTr.FL_FIXED) mo rsp mo' evs ->
exists ans, dec_fixedA addr len rsp = Some ans /\ aok0 (EvMapFixed addr len) ans /\
KI (gstep g (EvMapFixed addr len) ans) mo'.
Proof.
intros K G Hst. pose proof G as (Hlen & Hmod & Hal & Hwhere & Hb).
destruct (ev_fixed_facts g mo addr len K G) as (Hfc & Hvis & Hcc & Hpos & Hceil & Hsafe).
pose proof (Phi_nstep_raw LV _ _ _ _ _ (ki_x _ _ K) Hsafe Hst) as [HPhi Hlim].
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR anon_place_ok grant_model rsp_grant rsp_err rsp_remap reveal wunit rlenw rlen fixed_contained fixed_free commit_model remap_model m_vmmaps] in Hst.
rewrite kind_fixed in Hst. change (Z_to_bv 64 addr) with (w64 addr) in Hst. rewrite Hfc in Hst.
destruct Hst as [_ [-> ->]].
exists (AOk addr). split; [apply dec_fixedA_grant; exact Hmod|]. split; [exact I|].
cbn [gstep].
assert (HcostA : costA LV (NMmap addr len QKTr.PROT_RW QKTr.FL_FIXED) mo (rsp_grant (w64 addr) (rlenw len) []) <= len).
{ unfold costA. cbn [eff_ret rsp_grant]. rewrite kCeil_val in Hceil.
rewrite (placed_not_errno0 (w64 addr) len) by (rewrite ?u_w64; lia).
rewrite kind_fixed. change (Z_to_bv 64 addr) with (w64 addr). rewrite Hfc. exact Hcc. }
pose proof K as [X EM PE CH ND NE SP PH RSV BASE TOT].
constructor; cbn [g_chunks g_spent]; rewrite ?maps_commit, ?reserved_commit, ?mbase_commit, ?limit_commit, ?top_commit.
- destruct X as [HF [HW [HX HY]]]. eapply xinvA_intro; [apply vm_onlyA_commit| exact HF| apply wf_commit; exact HW| apply excl_inside_commit; exact HX| apply mbt_commit; exact HY].
- unfold excl_mapped. rewrite maps_commit. exact EM.
- intros r Hr. unfold perm_ok. rewrite maps_commit, reserved_commit. exact (PE r Hr).
- intros c Hc. unfold chunk_ok. rewrite maps_commit, reserved_commit. exact (CH c Hc).
- exact ND.
- exact NE.
- lia.
- lia.
- exact RSV.
- unfold app_cov. rewrite reserved_commit. exact BASE.
- exact TOT.
Qed.

Lemma ev_remap_facts g mo pb m :
KI g mo -> gev L BUDGET g (EvRemap pb m) ->
fixed_contained mo (w64 pb) (rlenw m) = true /\ range_vis LV mo (w64 pb) (rlenw m) /\
0 < pb /\ pb + m <= kCeil /\ m <= 2^40 /\
nsafeA LV (NMmap pb m QKTr.PROT_RW QKTr.FL_FIXED_NR) mo.
Proof.
intros K (Hm & Hpal & Hmal & (c & Hc & Hlo & Hhi)).
pose proof (ki_ch _ _ K c Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). pose proof (chunk_u g mo c K Hc) as (V1 & V2 & Ceil).
pose proof (ki_top g mo K) as HT.
unfold shadow_of in Hlo, Hhi. rewrite Ceil in *.

assert (Hband : exists r, In r PERM /\ fst r <= kShadowOffset + fst c / 8 /\ kShadowOffset + (fst c + snd c - 1) / 8 + 1 <= snd r).
{ destruct C5 as [Hlow|Hhigh].
- destruct (llo_lband LL) as (r & Hr & B1 & B2). exists r. split; [exact Hr|].
pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)).
assert ((fst c + snd c - 1) / 8 <= kLowEnd / 8) by (apply Z.div_le_mono; lia). lia.
- destruct (llo_band LL) as (r & Hr & B1 & B2). exists r. split; [exact Hr|]. rewrite kCeil_val in B2. unfold KHI, kHighMemBeg in *.
assert (0x10007fff8000 / 8 <= fst c / 8) by (apply Z.div_le_mono; lia).
assert ((fst c + snd c - 1) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). lia. }
destruct Hband as (r & Hr & B1 & B2).
pose proof (ki_perm _ _ K r Hr) as (P1 & P2 & P3 & P4 & P5). pose proof (perm_u r Hr) as (U1 & U2 & U3 & R1 & R2 & R3 & _).
assert (Hspan : (fst c + snd c - 1) / 8 + 1 - fst c / 8 <= snd c / 8 + 1).
{ clear - C1 C4. rewrite Z.mod_divide in C1 by lia. rewrite Z.mod_divide in C4 by lia.
destruct C1 as [k Hk]. destruct C4 as [k' Hk']. rewrite Hk, Hk'.
replace (k * 4096) with ((k * 512) * 8) by lia. replace (k' * 4096) with ((k' * 512) * 8) by lia.
rewrite !Z.div_mul by lia.
replace (k * 512 * 8 + k' * 512 * 8 - 1) with ((k * 512 + k' * 512 - 1) * 8 + 7) by lia.
rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
assert (Hc47 : (fst c + snd c - 1) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
assert (Hpb0 : 0 < pb) by (pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)); unfold kShadowOffset in *; lia).
assert (Hpbc : pb + m <= 0x10007fff8000) by (unfold kShadowOffset in *; change (0x7fffff800000 / 8) with 17592184995840 in Hc47; lia).
assert (Hm40 : m <= 2^40).
{ unfold kMaxChunk in C3. assert (snd c / 8 <= (2^26 + 16384) / 8) by (apply Z.div_le_mono; lia).
change ((2^26 + 16384) / 8) with 8390656 in *. lia. }
rewrite (rlenw_w64 m Hmal).
assert (Hwp : bv_unsigned (w64 pb) = pb) by (apply u_w64; lia).
assert (Hwm : bv_unsigned (w64 m) = m) by (apply u_w64; lia).
assert (Hfc : fixed_contained mo (w64 pb) (w64 m) = true).
{ unfold fixed_contained. apply andb_true_intro. split.
- eapply region_free_sub; [| | exact P4]; rewrite ?Hwp, ?Hwm, ?U1, ?U2; unfold kShadowOffset in *; lia.
- unfold map_contains. apply existsb_exists. exists (z2w r). split; [exact P1|]. rewrite U1, U2, Hwp, Hwm.
apply andb_true_intro. split; apply Z.leb_le; unfold kShadowOffset in *; lia. }
assert (Hvis : range_vis LV mo (w64 pb) (w64 m)).
{ unfold range_vis. rewrite Hwp, Hwm. intros x Hx. apply visible_iff. right.
destruct (proj1 (sh_iv_iff LV (fst c) (fst c + snd c) (bv_unsigned x) ltac:(lia))) as (y & Hy & Hsy).
{ unfold shz. rewrite (llo_shoff LL). unfold kShadowOffset in *. lia. }
exists y. split; [| exact Hsy].
unfold appcov. apply orb_true_intro. right. unfold ecov, emaps. apply covered_true.
exists (cent c). split; [apply filter_In; split; [exact C7| rewrite C10; reflexivity]|].
unfold cent. cbn [fst snd]. rewrite V1, V2. lia. }
split; [exact Hfc|]. split; [exact Hvis|]. split; [exact Hpb0|]. split; [lia|]. split; [exact Hm40|].
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR fixed_contained fixed_free Phi cost_anon cost_commit cost_fixed fixed_gates fixed_top range_vis excl_mapped rlenw rlen m_vmmaps Z.pow Z.le Z.lt].
rewrite kind_remap. rewrite (rlenw_w64 m Hmal). change (Z_to_bv 64 pb) with (w64 pb).
split; [| split; [| split; [exact Hfc| exact Hvis]]].
- unfold fixed_gates. rewrite (rlen_aligned m Hmal). unfold grant_ceilA, sp_window_hi, stack_max_size. repeat split; auto; lia.
- unfold fixed_top. rewrite (rlen_aligned m Hmal). unfold QybZ.Mq0.alloc_ceiling in HT. lia.
Qed.

Lemma ev_remap_step g mo pb m rsp mo' evs :
KI g mo -> gev L BUDGET g (EvRemap pb m) ->
nstep_raw LV (NMmap pb m QKTr.PROT_RW QKTr.FL_FIXED_NR) mo rsp mo' evs ->
exists ans, dec_remapA pb m rsp = Some ans /\ aok0 (EvRemap pb m) ans /\ KI (gstep g (EvRemap pb m) ans) mo'.
Proof.
intros K G Hst. pose proof G as (Hm & Hpal & Hmal & _).
destruct (ev_remap_facts g mo pb m K G) as (Hfc & Hvis & Hpb0 & Hpbc & Hm40 & Hsafe).
pose proof (Phi_nstep_raw LV _ _ _ _ _ (ki_x _ _ K) Hsafe Hst) as [HPhi Hlim].
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR anon_place_ok grant_model rsp_grant rsp_err rsp_remap reveal wunit rlenw rlen fixed_contained fixed_free commit_model remap_model m_vmmaps] in Hst.
rewrite kind_remap in Hst. change (Z_to_bv 64 pb) with (w64 pb) in Hst.
assert (HcostA : forall r, costA LV (NMmap pb m QKTr.PROT_RW QKTr.FL_FIXED_NR) mo r = 0).
{ intros r. unfold costA. rewrite kind_remap. match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. }
rewrite HcostA in HPhi.
pose proof K as [X EM PE CH ND NE SP PH RSV BASE TOT].
destruct Hst as [_ [-> ->]].
exists (AOk pb). split; [apply dec_remapA_ok; exact Hmal|]. split; [exact I|].
assert (Eg : gstep g (EvRemap pb m) (AOk pb) = g) by (destruct g; reflexivity). rewrite Eg.
rewrite kCeil_val in Hpbc.
constructor; rewrite ?maps_remap, ?reserved_remap, ?mbase_remap, ?limit_remap, ?top_remap.
- destruct X as [HF [HW [HX HY]]]. eapply xinvA_intro; [apply vm_onlyA_remap| exact HF| apply wf_remap; [exact HW| rewrite (rlenw_w64 m Hmal), !u_w64; lia]| apply excl_inside_remap; exact HX| apply mbt_remap; exact HY].
- unfold excl_mapped. rewrite maps_remap. exact EM.
- intros r Hr. unfold perm_ok. rewrite maps_remap, reserved_remap. exact (PE r Hr).
- intros c Hc. unfold chunk_ok. rewrite maps_remap, reserved_remap. exact (CH c Hc).
- exact ND.
- exact NE.
- exact SP.
- lia.
- exact RSV.
- unfold app_cov. rewrite reserved_remap. exact BASE.
- exact TOT.
Qed.

Lemma ev_munmap_safe g mo a sz :
KI g mo -> gev L BUDGET g (EvMunmap a sz) -> nsafeA LV (NMunmap a sz) mo.
Proof.
intros K [Hc Hsz].
pose proof (ki_ch _ _ K _ Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). cbn [fst snd] in *.
pose proof (chunk_u g mo _ K Hc) as (V1 & V2 & Ceil). cbn [fst snd] in V1, V2.
cbn -[rlenw rlen map_has region_free map_remove excl_entry m_vmmaps Z.pow Z.le Z.lt].
rewrite (rlenw_w64 sz C4), (rlen_aligned sz C4). change (Z_to_bv 64 a) with (w64 a).
split; [exact C2|]. split; [unfold kMaxChunk in C3; lia|]. split; [exact C1|]. split; [exact C0|]. split; [rewrite Ceil in C6; unfold TASK_SIZE; lia|].
split.
{ unfold map_has. apply existsb_exists. exists (cent (a, sz)). split; [exact C7|]. unfold cent. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
split; [exact C8|]. split; [| exact C10].
apply region_free_app in C9. apply C9.
Qed.

Lemma ev_munmap_step g mo a sz rsp mo' evs :
KI g mo -> gev L BUDGET g (EvMunmap a sz) ->
nstep_raw LV (NMunmap a sz) mo rsp mo' evs ->
exists ans, dec_munmapA a sz rsp = Some ans /\ aok0 (EvMunmap a sz) ans /\ KI (gstep g (EvMunmap a sz) ans) mo'.
Proof.
intros K G Hst. pose proof G as [Hc Hsz].
pose proof (ev_munmap_safe g mo a sz K G) as Hsafe.
pose proof (Phi_nstep_raw LV _ _ _ _ _ (ki_x _ _ K) Hsafe Hst) as [HPhi Hlim].
pose proof (ki_ch _ _ K _ Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). cbn [fst snd] in *.
pose proof (chunk_u g mo _ K Hc) as (V1 & V2 & Ceil). cbn [fst snd] in V1, V2.
cbn -[rlenw rlen munmap_model rsp_munmap m_vmmaps] in Hst. rewrite (rlenw_w64 sz C4) in Hst. change (Z_to_bv 64 a) with (w64 a) in Hst.
destruct Hst as (_ & -> & ->).
exists (AOk 0). split; [rewrite <- (rlenw_w64 sz C4); apply dec_munmapA_ok; [apply (llo_shoff LL)| exact C4| exact C2| exact C0| exact C6]|]. split; [exact I|].
cbn [gstep].
assert (HcostA : costA LV (NMunmap a sz) mo (rsp_munmap LV (munmap_model mo (w64 a) (w64 sz)) (w64 a) (w64 sz)) = 0) by reflexivity.
rewrite HcostA in HPhi.
pose proof K as [X EM PE CH ND NE SP PH RSV BASE TOT].
assert (Hsub : forall c', In c' (remove_first (a, sz) (g_chunks g)) -> In c' (g_chunks g) /\ fst c' <> a).
{ intros c' Hc'. exact (remove_first_nodup (a, sz) (g_chunks g) c' ND Hc Hc'). }
assert (C9m : region_free (map_remove (vm_maps (m_vmmaps mo)) (w64 a)) (w64 a) (w64 sz) = true) by (apply region_free_app in C9; apply C9).
constructor; cbn [g_chunks g_spent]; rewrite ?maps_munmap, ?reserved_munmap, ?mbase_munmap, ?limit_munmap, ?top_munmap.
- destruct X as [HF [HW [HX HY]]]. eapply xinvA_intro; [apply vm_onlyA_munmap| exact HF| apply wf_munmap; exact HW| apply excl_inside_munmap; exact HX| apply mbt_munmap; exact HY].
- unfold excl_mapped. rewrite maps_munmap. intros x y Hx Hy.
rewrite (covered_map_remove _ (w64 a) (w64 sz) y C8 C9m ltac:(rewrite V2; exact C2)). rewrite (EM x y Hx Hy). cbn [andb].
rewrite V1, V2. apply negb_true_iff. apply in_rng_false.
destruct (Z.lt_ge_cases y a); [left; lia|]. destruct (Z.le_gt_cases (a + sz) y); [right; lia|]. exfalso.
assert (E : excl_entry LV (cent (a, sz)) = true); [| rewrite C10 in E; discriminate].
apply excl_entry_true. exists x. unfold cent. cbn [fst snd]. rewrite V1, V2. repeat split; auto; lia.
- intros r Hr. pose proof (PE r Hr) as (P1 & P2 & P3 & P4 & P5). pose proof (perm_u r Hr) as (U1 & U2 & U3 & R1 & R2 & R3 & _).
assert (Hne : fst (z2w r) <> w64 a).
{ intros E. pose proof (P5 _ Hc) as Hd. unfold zdisj, civ in Hd. cbn [fst snd] in Hd.
assert (fst r = a) by (rewrite <- U1, E; exact V1). lia. }
unfold perm_ok. rewrite maps_munmap, reserved_munmap. split; [apply In_map_remove; split; [exact P1| exact Hne]|]. split.
{ intros e He. apply In_map_remove in He as [He _]. exact (P2 e He). }
split.
{ rewrite map_remove_filter, count_occ_filter_keep; [exact P3|]. cbn [fst]. destruct (bv_eqb (fst (z2w r)) (w64 a)) eqn:E; [|reflexivity].
apply Fs.bv_eqb_eq in E. contradiction. }
split; [exact P4|]. intros c' Hc'. apply P5. apply (Hsub c' Hc').
- intros c' Hc'. destruct (Hsub c' Hc') as [Hin Hfa].
pose proof (CH c' Hin) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). pose proof (chunk_u g mo c' K Hin) as (W1 & W2 & _).
assert (Hne : w64 (fst c') <> w64 a).
{ intros E. apply Hfa. rewrite <- W1, E. exact V1. }
unfold chunk_ok. rewrite maps_munmap, reserved_munmap.
split; [exact D0|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|].
split; [apply In_map_remove; split; [exact D7| exact Hne]|]. split.
{ intros e He. apply In_map_remove in He as [He _]. exact (D8 e He). }
split; [| exact D10].
eapply region_free_incl; [| exact D9]. intros e He. apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right].
apply In_map_remove in He as [He Hb]. apply In_map_remove in He as [He _]. apply In_map_remove. split; assumption.
- apply remove_first_nodup_fst. exact ND.
- intros e He. apply In_map_remove in He as [He _]. exact (NE e He).
- exact SP.
- lia.
- exact RSV.
- unfold app_cov. rewrite reserved_munmap. exact BASE.
- destruct TOT as [T1 T2]. rewrite gw_sizes_app, zlen_app in *.
pose proof (gw_sizes_map_remove (vm_maps (m_vmmaps mo)) (w64 a) (w64 sz) C7) as [G1 G2]. rewrite V2 in G1.
assert (Hz : zsum (map snd (remove_first (a, sz) (g_chunks g))) + sz = zsum (map snd (g_chunks g)) /\
zlen (remove_first (a, sz) (g_chunks g)) + 1 = zlen (g_chunks g)).
{ pose proof (remove_first_perm (a, sz) (g_chunks g) Hc) as HP.
rewrite <- (zsum_map_perm snd _ _ HP). pose proof (Permutation_length HP) as HL. cbn [map snd length] in *.
rewrite zsum_cons. unfold zlen. lia. }
unfold zlen in *. lia.
Qed.

Definition node_of (e : evA) : node :=
match e with
| EvMapAnon len _ => NMmap 0 len QKTr.PROT_RW QKTr.FL_ANON
| EvMapFixed addr len => NMmap addr len QKTr.PROT_RW QKTr.FL_FIXED
| EvRemap addr len => NMmap addr len QKTr.PROT_RW QKTr.FL_FIXED_NR
| EvMunmap addr len => NMunmap addr len
end.

Definition dec_of (e : evA) : resp -> option ansA :=
match e with
| EvMapAnon len avoid => dec_anonA len avoid
| EvMapFixed addr len => dec_fixedA addr len
| EvRemap addr len => dec_remapA addr len
| EvMunmap addr len => dec_munmapA addr len
end.

Lemma ev_stepA_eq e : ev_stepA e = msys (node_of e) (dec_of e).
Proof. destruct e; reflexivity. Qed.

Theorem ev_safe g mo e : KI g mo -> gev L BUDGET g e -> nsafeA LV (node_of e) mo.
Proof.
intros K G. destruct e as [len avoid|addr len|addr len|addr len]; cbn [node_of].
- apply (ev_anon_safe g mo len avoid K G).
- apply (ev_fixed_facts g mo addr len K G).
- apply (ev_remap_facts g mo addr len K G).
- apply (ev_munmap_safe g mo addr len K G).
Qed.

Theorem ev_step g mo e rsp mo' evs :
KI g mo -> gev L BUDGET g e -> nstep_raw LV (node_of e) mo rsp mo' evs ->
exists ans, dec_of e rsp = Some ans /\ aok0 e ans /\ KI (gstep g e ans) mo'.
Proof.
intros K G Hst. destruct e as [len avoid|addr len|addr len|addr len]; cbn [node_of dec_of] in *.
- apply (ev_anon_step g mo len avoid rsp mo' evs K G Hst).
- apply (ev_fixed_step g mo addr len rsp mo' evs K G Hst).
- apply (ev_remap_step g mo addr len rsp mo' evs K G Hst).
- apply (ev_munmap_step g mo addr len rsp mo' evs K G Hst).
Qed.

End Events.

Section Glue.
Hypothesis LL : ll_ok.

#[local] Notation MSPEC := (mspec (nstepsA LV) (nsafeA LV)).

Lemma vm_onlyA_refl mo : vm_onlyA mo mo.
Proof. repeat split; reflexivity. Qed.

Lemma vm_onlyA_trans a b c : vm_onlyA a b -> vm_onlyA b c -> vm_onlyA a c.
Proof. intros HA HB. unfold vm_onlyA in *. intuition congruence. Qed.

Lemma vm_onlyA_drift mo mo' : drift LV mo mo' -> vm_onlyA mo mo'.
Proof. intros (P & _ & _ & ->). destruct mo as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

Lemma vm_onlyA_nstep_raw g mo e rsp mo' evs :
KI g mo -> gev L BUDGET g e -> nstep_raw LV (node_of e) mo rsp mo' evs -> vm_onlyA mo mo'.
Proof.
intros K G Hst. destruct e as [len avoid|addr len|addr len|addr len]; cbn [node_of] in Hst;
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON QKTr.FL_FIXED QKTr.FL_FIXED_NR anon_place_ok grant_model rsp_grant rsp_err rsp_remap reveal wunit rlenw rlen fixed_contained fixed_free commit_model remap_model munmap_model rsp_munmap m_vmmaps] in Hst.
- rewrite kind_anon in Hst. destruct Hst as [_ (a & ws & _ & _ & _ & -> & ->)]. apply vm_onlyA_grant.
- rewrite kind_fixed in Hst. destruct (ev_fixed_facts LL g mo addr len K G) as (Hfc & _).
change (Z_to_bv 64 addr) with (w64 addr) in Hst. rewrite Hfc in Hst.
destruct Hst as [_ [-> ->]]. apply vm_onlyA_commit.
- rewrite kind_remap in Hst. destruct Hst as [_ [-> ->]]. apply vm_onlyA_remap.
- destruct Hst as (_ & -> & ->). apply vm_onlyA_munmap.
Qed.

Theorem membedA_spec {R} (t : T R) (P : R -> Prop) (RG : ghost -> R -> Prop) (g : ghost) (s : PStateA) (mo0 : Model) :
tall aok0 (rok P) t -> teva L BUDGET aok0 RG g t -> KI g mo0 ->
MSPEC (fun s0 mo => s0 = s /\ mo = mo0) (membedA t)
(fun r s' mo' => s' = s /\ P r /\ vm_onlyA mo0 mo' /\ exists g', RG g' r /\ KI g' mo').
Proof.
revert g mo0. induction t as [[r| |w]|e k IH]; intros g mo0 Ht Hg K.
-  cbn [membedA]. apply mspec_ret. intros s0 mo [-> ->]. split; [reflexivity|]. split; [exact Ht|].
split; [apply vm_onlyA_refl|]. exists g. split; [exact Hg| exact K].
-
cbn [membedA]. unfold mspin. apply mspec_sys. intros s0 mo [-> ->]. split; [exact I|].
intros rsp mo' evs (mo1 & _ & Hst). destruct Hst.
-  destruct Ht.
-
cbn [membedA]. destruct Hg as [Ge Gk]. change (forall a, aok0 e a -> tall aok0 (rok P) (k a)) in Ht.
apply (mspec_bind _ _ (ev_stepA e) (fun a => membedA (k a)) _
(fun a s' mo' => s' = s /\ aok0 e a /\ vm_onlyA mo0 mo' /\ KI (gstep g e a) mo')).
+ rewrite ev_stepA_eq. apply mspec_sys. intros s0 mo [-> ->]. split; [apply (ev_safe LL g mo0 e K Ge)|].
intros rsp mo' evs (mo1 & Hd & Hst).
pose proof (KI_drift g mo0 mo1 Hd K) as K1.
destruct (ev_step LL g mo1 e rsp mo' evs K1 Ge Hst) as (a & Hdec & Ha & K').
exists a. split; [exact Hdec|]. split; [reflexivity|]. split; [exact Ha|]. split; [| exact K'].
eapply vm_onlyA_trans; [apply vm_onlyA_drift; exact Hd| eapply vm_onlyA_nstep_raw; eauto].
+ intros a s0 mo [-> (Ha & Hv & K')].
eapply etwf_mono; [eapply (IH a (gstep g e a) mo (Ht a Ha) (Gk a Ha) K'); split; reflexivity|].
intros [r s1] mo1 H1. cbn [fst snd] in H1. destruct H1 as (-> & HP & Hv1 & Hg1).
cbn [fst snd]. split; [reflexivity|]. split; [exact HP|]. split; [| exact Hg1].
eapply vm_onlyA_trans; [exact Hv| exact Hv1].
Qed.

Definition malloc_room (X : list aptr) (a : AState) (n : Z) : Prop :=
(from_primary n = true -> class_size (class_of n) * (tot X [] 0 a (class_of n) + 17) <= kFreeArrayOffset) /\
(from_primary n = false -> zlen (as_reg a) < kMaxNumChunks).

End Glue.

Lemma rz_size_bound n : 16 <= rz_size n <= 2048.
Proof.
unfold rz_size. destruct (n <=? 48); [lia|]. destruct (n <=? 96); [lia|]. destruct (n <=? 448); [lia|].
destruct (n <=? 3968); [lia|]. destruct (n <=? 16128); [lia|]. destruct (n <=? 32256); [lia|]. destruct (n <=? 64512); lia.
Qed.

End Ledger.
