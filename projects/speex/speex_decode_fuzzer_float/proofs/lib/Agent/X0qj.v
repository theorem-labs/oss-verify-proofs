(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0qn X0qh X0qk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
intros Hsc. unfold usages.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.

Lemma mrep_set_usage {RCEIL : RunCeiling} : forall st m sc v,
mrep st m -> 0 <= sc < 48 ->
mrep (set_usage sc v st) (write_to_mem m (wa (CTX + 464 + 8 * sc)) (le8 (wz v))).
Proof.
intros st m sc v MR Hsc. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (wz v)) as L8.
pose proof (munch_write [(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8)] m m (CTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
ltac:(unfold CTX; lia) ltac:(rewrite L8; unfold CTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write asegs m m (wa (CTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl asegs m)) as WM.
eapply (mrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
- ctx_same.
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- left. rewrite usages_set_usage by lia. replace (CTX + 464 + 8 * sc) with ((CTX + 464) + 8 * sc) by lia.
apply u64arr_write; [exact X3| rewrite usages_length; lia].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [| ctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

Lemma mrep_set_seq {RCEIL : RunCeiling} : forall st m v,
mrep st m -> 0 <= v < 256 ->
mrep (upd_ctx (set_seq v) st) (write_to_mem m (wa (CTX + 912)) [b8 v]).
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [(CTX + 912, CTX + 913)] m m (CTX + 912) [b8 v] (munch_refl _ m)
ltac:(unfold CTX; lia) ltac:(cbn; unfold CTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write asegs m m (wa (CTX + 912)) [b8 v] (wmono_refl asegs m)) as WM.
eapply (mrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
- ctx_same.
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- left.
pose proof (rw_cells_write asegs m (CTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.

Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold unmap_seqs.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

Lemma mrep_set_unmap_seq {RCEIL : RunCeiling} : forall st m i v,
mrep st m -> 0 <= i < 32 ->
mrep (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) (write_to_mem m (wa (CTX + 848 + i)) [b8 v]).
Proof.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [(CTX + 848 + i, CTX + 848 + i + 1)] m m (CTX + 848 + i) [b8 v] (munch_refl _ m)
ltac:(unfold CTX; lia) ltac:(cbn; unfold CTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write asegs m m (wa (CTX + 848 + i)) [b8 v] (wmono_refl asegs m)) as WM.
eapply (mrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- ctx_same.
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- left. rewrite unmap_seqs_set by lia. replace (CTX + 848 + i) with ((CTX + 848) + i) by lia.
apply (u8arr_write asegs m (CTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
- right. split; [reflexivity| ctx_same].
- right. split; [| ctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.

Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q. Proof. destruct q; reflexivity. Qed.
Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q. Proof. intros H; exact H. Qed.
Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.

Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.

Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ]. unfold meta_word. lia. Qed.
Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ].
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ].
change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). first [ sf_destruct 4%nat H as LI FB SCR ML | sf_fb; destruct H as (LI & FB & SCR & ML) ]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ].
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ].
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros sfH_; first [ sf_destruct 4%nat sfH_ as LI FB SCR ML | sf_fb; destruct sfH_ as (LI & FB & SCR & ML) ]. unfold meta_word. lia. Qed.

Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed.

Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
intros Hf Ha. split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed.

Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma mrep_group_hdr_zero {RCEIL : RunCeiling} : forall st m p gh bs,
mrep st m -> (s_groups st) !! p = Some gh ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
length bs = 8%nat ->
mrep (del_group p st) (write_to_mem m (wa (conc st p)) bs).
Proof.
intros st m p gh bs MR Hp UNK L8.
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ].
first [ pose proof (group_conc st p gh WF Hp) as sfP_; sf_destruct 9%nat sfP_ as r Hr Cp Kr Sp0 Sp1 SpA RB0 RBC | sf_fb; destruct (group_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC) ].
first [ pose proof (WR _ r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ RBAL _ _ RF | sf_fb; destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2].
pose proof (round_up_pg_ge (r_len r)) as RU. unfold alloc_ceiling in RBC.
eapply mrep_transport_unowned.
- apply mrep_del_group. exact MR.
- apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
- apply wmono_write. apply wmono_refl.
- intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
intros [C|[C|[C|[C|[C|[C|C]]]]]].
+ unfold CTX in C. lia.
+ unfold MLOCK in C. lia.
+ unfold NEED_LOCKS in C. lia.
+ unfold PAGE_SIZE_A in C. lia.
+ first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ]. cbn in Hak.
first [ pose proof (area_conc st ak ar WF Hak) as sfP_; sf_destruct 8%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK _ | sf_fb; destruct (area_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _) ].
assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
change (conc (del_group p st) ak) with (conc st ak) in Hin.
pose proof (area_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
+ first [ sf_destruct 4%nat C as b gh' Hb Hin | sf_fb; destruct C as (b & gh' & Hb & Hin) ]. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
change (conc (del_group p st) b) with (conc st b) in Hin.
first [ pose proof (group_conc st b gh' WF Hb) as sfP_; sf_destruct 8%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 SbA _ | sf_fb; destruct (group_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _) ].
destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
Z.div_mod_to_equations. lia.
* pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
+ first [ sf_destruct 7%nat C as rid r' v Hr' Hk' Hin HC | sf_fb; destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC) ]. cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
destruct (N.eq_dec rid (fst p)) as [E|NE].
* subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
* pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
Qed.

Lemma mrep_grp_del_eq {RCEIL : RunCeiling} : forall st m g p, mrep (del_group p st) m -> mrep (grp_del st g p) m.
Proof. intros. unfold grp_del. apply mrep_del_slots. exact H. Qed.

Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
