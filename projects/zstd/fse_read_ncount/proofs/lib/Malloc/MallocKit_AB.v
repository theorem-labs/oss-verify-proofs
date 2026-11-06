(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma get_meta_rec_put : forall st g mr g',
get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
#[using="Type"] Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.
#[using="Type"] Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.
#[using="Type"] Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.
#[using="Type"] Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.
#[using="Type"] Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
intros x Hx. cbn in Hx |- *. tauto.
Qed.
End CANSEC1.
Ltac munch_grow MU iv :=
lazymatch type of MU with
| munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
end.
Section CANSEC2. Context {rc : runConstT}.
Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.
End CTXFRAME.
End CANSEC2.
Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).
Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
#[using="Type"] Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
End CANSEC3.
Section CANSEC4. Context {rc : runConstT}.
Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.
#[using="Type"] Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. Local Ltac2 Set LiaHints.tbl := fun () => "0010<8929260062.600000>S2LI2FB3SCR2ML".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "0040=22703930437.629317658818.646609756872.668569543065.6000001002003007SSSS2LI".
rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
change 63 with (Z.ones 6). Local Ltac2 Set LiaHints.tbl := fun () => "0060=2844262140.6 3368230809.6 53724683464.658136753095.663967083442.665351495264.600000100600700>00?00@SS3SCRSS2LI2FBSS".
rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). Local Ltac2 Set LiaHints.tbl := fun () => "0010>35960435360.1000000>S2Hf2Ha1S1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
intros Hf Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>35960435360.1062759100339.5 00000>00BS2Hf2Ha1S1H2H0S2Hf".
split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC4.
Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
Section CANSEC5. Context {rc : runConstT}.
#[using="Type"] Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.
End CANSEC5.
