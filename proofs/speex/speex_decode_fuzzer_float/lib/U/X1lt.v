(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1po X1q3 X1pj X1qd X1q6 X1qm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qd X0px X0q5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1lw X1kr X1kt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition rre_ip_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
let r := E - P - n in
let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
let m2 := if 5 <=? r then write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else m1 in
write_to_mem m2 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl (if 5 <=? r then 5 else r) 5)].

Definition rre_ip_post (ra sp gp tp t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k : Z) : machine_state -> Prop :=
fun ms' => exists t0 a1 a2 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33688) fc None m' (seg_rom rsegs)
/\ m' = rre_ip_mem m P E n k
/\ mem_inv rsegs m'.

Lemma rre_ip_walk : forall (ra sp gp tp t1 t2 s0 s1 a0 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
(P E n k : Z),
bv_unsigned a0 = P ->
mem_inv rsegs m ->
wr_at rsegs m (P - 3) (E - P + 4) ->
bytes_at rsegs m (P - 3) [b8 k] ->
16 <= P -> P + n <= E -> E + 8 <= 2^64 -> 0 <= n -> E - P - n < 2^31 -> 0 <= k < 256 ->
evt rsegs (rre_ip_post ra sp gp tp t1 t2 s0 s1 a0 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P E n k)
(MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33638) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros HP MI WR BK P16 PNE E64 N0 RS HK.
pose proof (bv_unsigned_in_range _ a0) as PWR. change (bv_modulus 64) with (2^64) in PWR.
set (r := E - P - n).
assert (K31 : 0 <= Z.land k 31 < 32).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2^5)). lia. }

assert (TAILJ : forall (x5 x12 : word) (rc : Z) (mj : word -> option byte),
0 <= rc <= 5 -> mem_inv rsegs mj -> wr_at rsegs mj (P - 3) (E - P + 4) -> bytes_at rsegs mj (P - 3) [b8 k] ->
evt rsegs (fun ms' => exists t0 a1 a2 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33688) fc None m' (seg_rom rsegs)
/\ m' = write_to_mem mj (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl rc 5)] /\ mem_inv rsegs m')
(MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 (Z_to_bv 64 rc) x12 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33674) fc None mj (seg_rom rsegs))).
{ intros x5 x12 rc mj RC MIj WRj BKj.

pose proof (bytes_at_read rsegs mj (P - 3) [b8 k] 0 1 BKj ltac:(lia) ltac:(cbn; lia)) as RK.
cbv [take drop Z.to_nat] in RK. replace (P - 3 + 0) with (bv_unsigned a0 + -3) in RK by lia.
change (wa (bv_unsigned a0 + -3)) with (Z_to_bv 64 (bv_unsigned a0 + -3)) in RK.
assert (SH5 : Z.shiftl rc 5 = rc * 2 ^ 5) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k) by lia.
step. rewrite ?(unsigned_lit rc) by lia.
step. rewrite (unsigned_lit (Z.shiftl rc 5)), (unsigned_lit (Z.land k 31)) by lia. rewrite SH5 at 1.
rewrite (lor_shl5 rc (Z.land k 31)) by lia.
replace (Z.land (Z.land k 31) 31) with (Z.land k 31) by (rewrite <- Z.land_assoc; reflexivity).
pose proof (wr_at_store_ok rsegs mj _ _ 0 1 WRj ltac:(lia) ltac:(lia)) as SO.
replace (P - 3 + 0) with (bv_unsigned a0 + -3) in SO by lia. change (wa (bv_unsigned a0 + -3)) with (Z_to_bv 64 (bv_unsigned a0 + -3)) in SO.
step. change (le1 (Z_to_bv 64 (Z.land k 31 + Z.shiftl rc 5))) with (le1 (wz (Z.land k 31 + Z.shiftl rc 5))).
rewrite (le1_wz (Z.land k 31 + Z.shiftl rc 5)) by lia. sdk.
apply evt_done. sf_eexists 4%nat. split; [reflexivity|]. split; [| assumption].
rewrite EQm0. f_equal. unfold wa. f_equal. lia. }

step. step. rewrite (unsigned_lit E), (unsigned_lit (n + bv_unsigned a0)) by lia. rewrite HP. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.

step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
-
step. step.
eapply evt_mono; [eapply (TAILJ _ _ 0 m); [lia| exact MI| exact WR| exact BK]|].
cbv beta. intros ms' sfH_; first [ sf_destruct 7%nat sfH_ as x5 x11 x12 m' -> EM MI' | sf_fb; destruct sfH_ as (x5 & x11 & x12 & m' & -> & EM & MI') ]. sf_eexists 4%nat. split; [reflexivity|]. split; [| exact MI'].
rewrite EM. unfold rre_ip_mem. fold r. rewrite KR. cbn [Z.eqb Z.leb]. reflexivity.
-
step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.
step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
step. replace (E + (0 - r)) with (E - r + 0) by lia.
step.
sok (n + 3) 1%nat (E - r + 0).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
+
step.
eapply evt_mono; [eapply (TAILJ _ _ r); [lia| assumption| exact WR| exact BK]|].
cbv beta. intros ms' sfH_; first [ sf_destruct 7%nat sfH_ as x5 x11 x12 m' -> EM MI' | sf_fb; destruct sfH_ as (x5 & x11 & x12 & m' & -> & EM & MI') ]. sf_eexists 4%nat. split; [reflexivity|]. split; [| exact MI'].
rewrite EM. unfold rre_ip_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
+
sok (E - P - 2) 1%nat (E + 4 + -9).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
sok (E - P - 1) 4%nat (E + 4 + -8).
step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
step.
eapply evt_mono; [eapply (TAILJ _ _ 5); [lia| assumption| exact WR| exact BK]|].
cbv beta. intros ms' sfH_; first [ sf_destruct 7%nat sfH_ as x5 x11 x12 m' -> EM MI' | sf_fb; destruct sfH_ as (x5 & x11 & x12 & m' & -> & EM & MI') ]. sf_eexists 4%nat. split; [reflexivity|]. split; [| exact MI'].
rewrite EM. unfold rre_ip_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

Section INPLACE_MODEL.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (m : word -> option byte) (blk : block) (r : region) (g bm : aptr) (ai : Z) (ar : area) (b3 lo hi i off n' : Z).
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis HF : hdr_facts st blk r g bm ai ar b3 lo hi i off.
Hypothesis N0 : 0 <= n'.
Hypothesis FIT : UNIT * off + n' <= get_stride (get_meta_rec st g) - IB.
Hypothesis R32 : get_stride (get_meta_rec st g) - IB - UNIT * off - n' < 2^32.

Let c := blk_slot blk.
Let stride := get_stride (get_meta_rec st g).
Let po := snd c + UNIT * off.
Let e := snd c + stride - IB.

#[using="bm ai ar b3 lo hi i off HF po e"] Lemma rip_wr8 : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st -> s_groups stx = s_groups st ->
snd c - 3 <= o < snd c + stride - 4 ->
0 <= v < 256 ->
rmrep (wr8 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst c, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Hv.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hr. pose proof (hf_kind _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hk.
pose proof (hf_snd _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hsnd. pose proof (hf_span _ _ _ _ _ _ _ _ _ _ _ _ HF) as SPAN.
pose proof (hf_b0 _ _ _ _ _ _ _ _ _ _ _ _ HF) as B0. pose proof (hf_i _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hi.
pose proof (hf_stride _ _ _ _ _ _ _ _ _ _ _ _ HF) as [S16 _]. pose proof (hf_nogrp _ _ _ _ _ _ _ _ _ _ _ _ HF) as NOGRP.
assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold stride, UNIT in *; lia).
assert (SIL : stride * i + stride <= stride * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold stride, UNIT in *; lia. }
split; [|apply ticks_ok_wr8; exact TKx].
apply (rmrep_wr8 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold c, stride, UNIT, IB in *; lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); unfold c, stride in *; lia.
Qed.

#[using="bm ai ar b3 lo hi i off HF po e"] Lemma rip_wr32 : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st -> s_groups stx = s_groups st ->
snd c - 3 <= o -> o + 4 <= snd c + stride - 4 ->
0 <= v < 2^32 ->
rmrep (wr32 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst c, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hr. pose proof (hf_kind _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hk.
pose proof (hf_snd _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hsnd. pose proof (hf_span _ _ _ _ _ _ _ _ _ _ _ _ HF) as SPAN.
pose proof (hf_b0 _ _ _ _ _ _ _ _ _ _ _ _ HF) as B0. pose proof (hf_i _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hi.
pose proof (hf_stride _ _ _ _ _ _ _ _ _ _ _ _ HF) as [S16 _]. pose proof (hf_nogrp _ _ _ _ _ _ _ _ _ _ _ _ HF) as NOGRP.
assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold stride, UNIT in *; lia).
assert (SIL : stride * i + stride <= stride * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold stride, UNIT in *; lia. }
apply (rmrep_wr32 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold c, stride, UNIT, IB in *; lia| unfold c, stride, UNIT, IB in *; lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); unfold c, stride in *; lia.
Qed.

#[using="bm ai ar lo hi MR TK HF N0 FIT R32"] Lemma rre_ip_rmrep :
rmrep (X1qm.stf st c off n' g i) (rre_ip_mem m (r_base r + po) (r_base r + e) n' b3)
/\ ticks_ok (X1qm.stf st c off n' g i).
Proof.
pose proof (hf_stride _ _ _ _ _ _ _ _ _ _ _ _ HF) as [S16 _]. pose proof (hf_off _ _ _ _ _ _ _ _ _ _ _ _ HF) as OFF.
pose proof (hf_idx _ _ _ _ _ _ _ _ _ _ _ _ HF) as IDX. pose proof (hf_b3 _ _ _ _ _ _ _ _ _ _ _ _ HF) as B3.
pose proof (hf_i _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hi. pose proof (hf_li _ _ _ _ _ _ _ _ _ _ _ _ HF) as LI.
unfold X1qm.stf. rewrite <- (resize_body_eq st c off n' g i).
unfold X1qm.res, X1qm.ee, X1qm.pp, X1qm.st0, rre_ip_mem. unfold X1po.MR. fold stride. unfold aadd. cbn [fst snd].
set (res := snd c + (stride - IB) - (snd c + UNIT * off) - n').
replace (r_base r + e - (r_base r + po) - n') with res by (unfold res, e, po; lia).
assert (RES : 0 <= res < 2^32) by (unfold res, stride, UNIT, IB in *; lia).
assert (I31 : Z.land i 31 = Z.land b3 31).
{ rewrite IDX. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (M0 : rmrep st0 m /\ ticks_ok st0 /\ s_regions st0 = s_regions st /\ s_groups st0 = s_groups st).
{ split; [apply rmrep_set_tick; exact MR|]. split; [apply ticks_ok_set_tick; [cbn; lia| exact TK]|]. split; reflexivity. }

set (st1 := if negb (res =? 0) then _ else _). set (m1 := if res =? 0 then _ else _).
assert (M1 : rmrep st1 m1 /\ ticks_ok st1 /\ s_regions st1 = s_regions st /\ s_groups st1 = s_groups st).
{ subst st1 m1. destruct (Z.eqb_spec res 0) as [R0|R0]; cbn [negb]; [exact M0|].
first [ sf_destruct 4%nat M0 as A B C D | sf_fb; destruct M0 as (A & B & C & D) ].
destruct (rip_wr8 st0 m (snd c + (stride - IB) + - res) 0 A B C D ltac:(unfold res, stride, UNIT, IB in *; lia) ltac:(lia)) as [A1 B1].
replace (r_base r + e - res) with (r_base r + (snd c + (stride - IB) + - res)) by (unfold e; lia).
split; [exact A1|]. split; [exact B1|]. split; [rewrite s_regions_wr8; exact C| rewrite s_groups_wr8; exact D]. }
clearbody st1 m1. first [ sf_destruct 4%nat M1 as A1 B1 C1 D1 | sf_fb; destruct M1 as (A1 & B1 & C1 & D1) ].

set (st2 := if 5 <=? res then _ else st1). set (m2 := if 5 <=? res then _ else m1).
assert (M2 : rmrep st2 m2 /\ ticks_ok st2 /\ s_regions st2 = s_regions st /\ s_groups st2 = s_groups st).
{ subst st2 m2. destruct (Z.leb_spec 5 res) as [R5|R5]; [| split; [exact A1| split; [exact B1| split; [exact C1| exact D1]]]].
destruct (rip_wr8 st1 m1 (snd c + (stride - IB) + -5) 0 A1 B1 C1 D1 ltac:(unfold res, stride, UNIT, IB in *; lia) ltac:(lia)) as [A2 B2].
destruct (rip_wr32 _ _ (snd c + (stride - IB) + -4) res A2 (B2) ltac:(rewrite s_regions_wr8; exact C1) ltac:(rewrite s_groups_wr8; exact D1)
ltac:(unfold res, stride, UNIT, IB in *; lia) ltac:(unfold res, stride, UNIT, IB in *; lia) ltac:(lia)) as [A3 B3'].
replace (r_base r + e - 5) with (r_base r + (snd c + (stride - IB) + -5)) by (unfold e; lia).
replace (r_base r + e - 4) with (r_base r + (snd c + (stride - IB) + -4)) by (unfold e; lia).
split; [exact A3|]. split; [exact B3'|]. split; [reflexivity || (cbn; exact C1)| reflexivity || (cbn; exact D1)]. }
clearbody st2 m2. first [ sf_destruct 4%nat M2 as A2 B2 C2 D2 | sf_fb; destruct M2 as (A2 & B2 & C2 & D2) ].

assert (KV : 0 <= Z.land i 31 + Z.shiftl (if 5 <=? res then 5 else res) 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32. rewrite I31, IDX. destruct (Z.leb_spec 5 res); lia. }
destruct (rip_wr8 st2 m2 (snd c + UNIT * off + -3) _ A2 B2 C2 D2 ltac:(unfold stride, UNIT, IB in *; lia) KV) as [A4 B4].
replace (r_base r + po - 3) with (r_base r + (snd c + UNIT * off + -3)) by (unfold po; lia).
rewrite <- I31.
exact (rmrep_havoc _ _ (fst c, snd c + UNIT * off) n' A4 B4).
Qed.
End INPLACE_MODEL.
