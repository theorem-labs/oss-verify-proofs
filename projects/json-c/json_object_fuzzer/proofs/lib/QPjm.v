(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QnDM_c1 Q2qa QZAi QUZl Q7S0 QytA Qy5Y Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Qy5Y.Mq6 Q4J3.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QnDM_c1.Mq0 QytA Qy5Y.Mq4 QlQE.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Ql2m Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QnDM_c1.Mq0 Q2qa.Mq1 Q4J3.Mq1 QytA Qy5Y.Mq6.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA Qy5Y.Mq6 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
intros Hsc. unfold usages.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.
End RC__1.

Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold unmap_seqs.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

#[using="Type"] Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

#[using="Type"] Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q. Proof. intros H; exact H. Qed.
#[using="Type"] Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
#[using="Type"] Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.
End RC__2.

Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

#[using="Type"] Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
#[using="Type"] Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
#[using="Type"] Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
intros (LI & FB & SCR & ML).
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
#[using="Type"] Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

#[using="Type"] Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed.

#[using="Type"] Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

#[using="Type"] Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
intros Hf Ha. split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

#[using="Type"] Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed.

#[using="Type"] Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

#[using="Type"] Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.
End RC__3.

Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q4J3.Mq3 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AGP : Z := 0x1a800.
Definition ATP : Z := 0x1a620.
Definition ERRNO : Z := ATP - 164.
Definition MALLOC_SYM : Z := 0x1596c.
Definition FREE_SYM : Z := 0x156e0.
Definition MALLOC_STACK : Z := 8192.
Definition FREE_STACK : Z := 8192.

Definition MEDTAB : Z := 0x1a060.
Definition alloc_static (a : Z) : Prop :=
(MLOCK <= a < MLOCK + 4) \/ (LIBC <= a < CTX + 928) \/ (ERRNO <= a < ERRNO + 4) \/ (MEDTAB <= a < MEDTAB + 4).

Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

Definition in_block (LB : list block) (a : Z) : Prop :=
exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Definition client_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (0x19000 <= a < 0x1b000 /\ ~ alloc_static a) \/ in_block LB a.

Definition client_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (0x19000 <= A /\ A + n <= 0x1b000 /\ (A + n <= MLOCK \/ MLOCK + 4 <= A) /\ (A + n <= LIBC \/ CTX + 928 <= A)
/\ (A + n <= ERRNO \/ ERRNO + 4 <= A) /\ (A + n <= MEDTAB \/ MEDTAB + 4 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

#[using="Type"] Lemma client_range_addr : forall LB SP A n a,
client_range LB SP A n -> A <= a < A + n -> client_addr LB SP a.
Proof.
intros LB SP A n a HR Ha. unfold client_range, client_addr, alloc_static, MLOCK, LIBC, CTX, ERRNO, ATP, MEDTAB in *.
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Definition block_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x1b000 <= A).

Definition client_write_ok (LB : list block) (iv : Z * Z) : Prop :=
alloc_ceiling <= fst iv
\/ (0x19000 <= fst iv /\ snd iv <= 0x1b000 /\ (snd iv <= MLOCK \/ MLOCK + 4 <= fst iv) /\ (snd iv <= LIBC \/ CTX + 928 <= fst iv)
/\ (snd iv <= ERRNO \/ ERRNO + 4 <= fst iv) /\ (snd iv <= MEDTAB \/ MEDTAB + 4 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition bptr_eqb (p q : bptr) : bool :=
aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).

Definition lb_remove (p : bptr) (LB : list block) : list block :=
filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition div_core_entry := 0x10e4c%Z.
Definition div_core_mid_pc := 0x11110%Z.

Lemma A4_even : forall x,
Z.land (Z.land (Z.shiftl x 1) 18446744073709551615) 4294967294 = Z.land (Z.land (Z.shiftl x 1) 18446744073709551615) 4294967295.
Proof.
intros x. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.eq_dec i 0) as [->|Hnz].
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- f_equal.
replace 4294967295 with (Z.lor 4294967294 1) by reflexivity.
rewrite Z.lor_spec. replace (Z.testbit 1 i) with false. { now rewrite orb_false_r. }
symmetry. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma half_iter_range : forall x b, 0 <= half_iter x b < 18446744073709551616.
Proof.
intros. unfold half_iter, shl64, mul64, mulhu, sub64.
apply Z_lor_range.
- apply (zr_shiftr _ 63). apply QZAi.wrap64_range. lia.
- apply QZAi.wrap64_range.
Qed.
Ltac hi_rng X := let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply half_iter_range).
Ltac mulhu_rng X := let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply mulhu_range; (change (inr64 _) || idtac); zrange).

