(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0px X0q5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1ky.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rallzerop_entry : Z := 0x330f4.

Definition rallzerop_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 a5 a6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).

Lemma land_3072 x : 0 <= x -> Z.land x 3072 = x mod 4096 / 1024 * 1024.
Proof.
intros Hx. change 3072 with (Z.ldiff (Z.ones 12) (Z.ones 10)).
rewrite land_ldiff_distr, Z.land_ones, Z.ldiff_ones_r, Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.mod_pos_bound x (2^12) ltac:(lia)). change (2^12) with 4096 in *. change (2^10) with 1024. lia.
Qed.

Lemma rallzerop_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 x1 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
(mword last_idx freeable sc maplen : Z),
mword = last_idx + 32 * freeable + 64 * sc + 4096 * maplen ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 48 -> 0 <= maplen < 2^40 ->
ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))) ->
(maplen <> 0 -> last_idx = 0 -> 16 * size_class sc <= maplen * 4096 - 16) ->
evt rsegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) x1 (Z_to_bv 64 last_idx) (Z_to_bv 64 maplen) (Z_to_bv 64 sc) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33200) fc None m (seg_rom rsegs)).
Proof.
intros until maplen. intros MW LI FB SC ML RS HSTR.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (L3 : Z.land mword 3072 = sc / 16 * 1024).
{ rewrite land_3072 by lia. f_equal.
replace mword with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia. rewrite Z.mod_add, Z.mod_small by lia.
Z.div_mod_to_equations. nia. }

assert (RS2 : forall k, ov_read_bytes rsegs m (Z_to_bv 64 (k + sc * 2)) 2 = Some (le2 (wz (size_class sc))) \/ k <> 88424).
{ intros k. destruct (Z.eq_dec k 88424) as [->|NE]; [left| right; exact NE].
replace (Z_to_bv 64 (88424 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
destruct (RS2 88424) as [RS'|]; [|congruence]. clear RS2.
st1. st1. st1. rewrite L3. st1. if_cases K14; zify_cond K14.
2:{ exfalso. clear -K14 SC. Z.div_mod_to_equations. nia. }

st1. if_cases K15; zify_cond K15.
-
st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. st1. st1. st1.
rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z]. unfold rallzerop_post. finish.
- st1. if_cases K16; zify_cond K16.
+
st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. st1. st1. st1.
rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z]. unfold rallzerop_post. finish.
+
specialize (HSTR ltac:(lia) ltac:(lia)).
st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
try rewrite (Z.mod_small (size_class sc)) by lia.
st1. st1. rewrite land_pgmask by lia.
assert (MP : mword - mword mod 4096 = maplen * 4096).
{ replace mword with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
rewrite MP. st1. st1. st1. st1.
rewrite v_sltu_b2z, Z.shiftl_mul_pow2, !unsigned_lit by lia. change (2^4) with 16.
replace (maplen * 4096 + -16 <? size_class sc * 16) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. unfold rallzerop_post. finish.
Qed.

Lemma rallzerop_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 48 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
size_class sc * idx <= off16 < size_class sc * (idx + 1) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
(maplen <> 0 -> last_idx = 0 -> 16 * size_class sc <= maplen * 4096 - 16) ->
evt rsegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x330f4) fc None m (seg_rom rsegs)).
Proof.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hml HSTR.
specialize (RS ltac:(lia)).
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (EA0 : a0 = Z_to_bv 64 P) by (rewrite <- HP; symmetry; apply Z_to_bv_bv_unsigned). rewrite EA0. clear EA0.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite ?unsigned_lit, zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.

assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
{ exfalso. rewrite ?wz_unsigned in K8 by lia. lia. }

st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (88424 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (88424 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1.

assert (MW4 : Z.shiftr mword 12 = maplen).
{ subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia. }
st1. rewrite MW4. st1. if_cases K12; zify_cond K12; rewrite ?wz_unsigned, ?unsigned_lit in K12 by lia.
- eapply rallzerop_tail; eauto; lia.
- st1. st1. st1. if_cases K13; zify_cond K13.
2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K13 by lia. change (2^8) with 256 in K13. change 18446744073709551615 with (Z.ones 64) in K13.
rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K13 by lia. rewrite Z.mod_small in K13 by lia. lia. }
eapply rallzerop_tail; eauto; lia.
Qed.

Lemma rallzerop_spec {RCEIL : RunCeiling} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st (blk : block) r g bm ai ar (b3 lo hi i off : Z),
rmrep st m -> mem_inv rsegs m ->
hdr_facts st blk r g bm ai ar b3 lo hi i off ->
bv_unsigned a0 = blk_addr blk ->
m_sizeclass (get_meta_rec st g) < 48 ->
UNIT * size_class (m_sizeclass (get_meta_rec st g)) <= get_stride (get_meta_rec st g) ->
evt rsegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom rsegs)).
Proof.
intros until off. intros MR MI HF HP SC48 STR.
destruct HF as [Fslot Fhosts Ffst Freg Fkind Frbase Fmem Fsnd Fb0 Fb16 Foff Faddr Fsize Ffit Fspan Fstride Fk4 Fk3 Fk2 Fk1 Fb3 Flo Fhi Fidx Fres Foff16 Fmslot Fg0 Farea Fcheck Fsecret Favail Ffreed Fli Ffreeable Fmaplen Fsc Fi Fnav Fnfr Ftop Fg16 Fg63 Fg17 Ffoot Fnogrp Finit].
clear Ffoot Fres.
set (c := blk_slot blk) in *. set (mr := get_meta_rec st g) in *.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ].
first [ sf_destruct 5%nat WF as Hres WR DISJ WA WG | sf_fb; destruct WF as (Hres & WR & DISJ & WA & WG) ].
pose proof Fstride as [S16 SM]. pose proof Frbase as (RB0 & RBM & RBC). unfold alloc_ceiling in RBC.
assert (SI0 : 0 <= get_stride mr * i) by (clear -S16 Fi; apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride mr * i + get_stride mr <= get_stride mr * (m_last_idx mr + 1)).
{ clear -S16 Fi. rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
set (po := snd c + UNIT * off).
assert (OFF16 : 16 * off + 16 <= get_stride mr).
{ clear -Ffit Fsize SM Foff. unfold UNIT, IB in *. Z.div_mod_to_equations. lia. }
assert (SIM : (get_stride mr * i) mod 16 = 0) by (clear -SM; unfold UNIT in SM; rewrite Z.mul_mod, SM, Z.mul_0_l by lia; reflexivity).
assert (RNG : 16 <= po /\ po + 16 <= round_up_pg (r_len r) /\ 0 <= r_base r + po /\ r_base r + po + 16 <= 2^64 /\ po mod 16 = 0).
{ subst po. rewrite Fsnd. pose proof (round_up_pg_ge (r_len r)).
clear -SI0 SIL Fspan OFF16 Fi Foff Fb0 Fb16 S16 RB0 RBC H SIM. unfold UNIT, IB in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
Z.div_mod_to_equations. lia. }
first [ sf_destruct 5%nat RNG as PLO PHI P0 P64 P16 | sf_fb; destruct RNG as (PLO & PHI & P0 & P64 & P16) ].

destruct (rmrep_shadow_read st m (fst c) r (po - 4) 0 MR Freg Fkind ltac:(clear -PLO PHI; lia) Fk4) as [R4 _].
destruct (rmrep_shadow_read st m (fst c) r (po - 3) b3 MR Freg Fkind ltac:(clear -PLO PHI; lia) Fk3) as [R3 _].
destruct (rmrep_shadow_read2 st m (fst c) r (po - 2) lo hi MR Freg Fkind ltac:(clear -PLO PHI; lia) ltac:(clear -PLO PHI; lia) Fk2
ltac:(replace (po - 2 + 1) with (po - 1) by (clear; lia); exact Fk1)) as (R2 & _ & _).
rewrite <- le2_lohi in R2 by assumption.

destruct (rmrep_group_read st m bm _ MR Fhosts) as [RG _]. cbn [g_meta pw oconc] in RG.

pose proof (rmrep_meta_chunk st m g MR Fmslot) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Fmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m (area_of g) ar MR Farea) as RA. rewrite run_secret_wz in RA.
pose proof (rmrep_ctx_secret_read1 st m MR Finit) as RC. rewrite run_secret_wz in RC.

assert (Hrb : s_regions st !! fst bm = Some r) by (rewrite Ffst; exact Freg).
assert (HB : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hrb).
first [ sf_destruct 6%nat Fmslot as a ara k Ha Hkk Eg | sf_fb; destruct Fmslot as (a & ara & k & Ha & Hkk & Eg) ].
first [ pose proof (WA a ara Ha) as sfP_; sf_destruct 7%nat sfP_ as rg Hrg A0 A1 AAL ANG _ | sf_fb; destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _) ].
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
first [ pose proof (WR (fst a) rg Hrg) as sfP_; sf_destruct 5%nat sfP_ as RB0' RBAL' RL0' RBC' _ | sf_fb; destruct (WR (fst a) rg Hrg) as (RB0' & RBAL' & RL0' & RBC' & _) ]. unfold alloc_ceiling in RBC'.
pose proof (round_up_pg_ge (r_len rg)) as RUG.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ clear -Hkk RB0' RBAL' A0 AAL. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [clear; lia|].
clear -Hkk A0 AAL. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
assert (G40 : 0 <= conc st g /\ conc st g + 40 <= 2^64).
{ rewrite HG. clear -Hkk RB0' A0 A1 RBC' RUG. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
assert (EB : conc st bm = r_base r + po - 16 * (lo + 256 * hi) - 16).
{ rewrite HB. subst po. rewrite Fsnd. clear -Foff16. unfold UNIT in *. lia. }
assert (EP : bv_unsigned a0 = r_base r + po) by (rewrite HP, Faddr; subst po c; clear; lia).
assert (STR' : m_maplen mr <> 0 -> m_last_idx mr = 0 -> 16 * size_class (m_sizeclass mr) <= m_maplen mr * 4096 - 16).
{ intros NZ L0. revert STR. subst mr. unfold get_stride. rewrite L0. cbn [Z.eqb].
destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [contradiction|]. cbn [negb andb]. unfold UNIT. clear. lia. }
pose proof (Fg16 SC48) as G16. rewrite <- Fidx in G16, Fi, Fnav, Fnfr.
unfold rallzerop_entry.
eapply (rallzerop_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st bm) (conc st (area_of g)) b3 (lo + 256 * hi) (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) SECRET
(pw st (m_prev mr)) (pw st (m_next mr))).
- exact EP.
- clear -RBM P16. Z.div_mod_to_equations. lia.
- clear -EB HB RB0 Fb0. lia.
- exact P64.
- exact EB.
- exact HA.
- exact (proj1 G40).
- exact (proj2 G40).
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by (clear; lia). exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by (clear; lia). exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by (clear; lia). exact R2.
- rewrite HB in RG |- *. exact RG.
- exact MM.
- exact RA.
- exact RC.
- intros Hlt. apply rsize_classes_read; [exact MI | clear -Hlt Fsc; lia].
- exact Fb3.
- clear -Flo Fhi. lia.
- exact Favail.
- exact Ffreed.
- exact SECRET_range.
- clear -Fli. lia.
- clear -Ffreeable. lia.
- clear -Fsc SC48. lia.
- clear -Fmaplen. lia.
- clear -Fi. lia.
- exact Fnav.
- exact Fnfr.
- exact G16.
- exact Fg17.
- exact STR'.
Qed.
