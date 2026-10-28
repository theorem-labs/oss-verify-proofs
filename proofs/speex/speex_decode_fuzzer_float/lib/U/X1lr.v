(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1po X1q3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0qd X0px X0q5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1ky X1kt X1kg X1lq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rmrep_shadow_read4 {RCEIL : RunCeiling} : forall st m rid r o v,
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= o -> o + 4 <= round_up_pg (r_len r) -> 0 <= v < 2^32 ->
cell_read (get_shadow st rid) o = Known (byte_of v 0) ->
cell_read (get_shadow st rid) (o + 1) = Known (byte_of v 1) ->
cell_read (get_shadow st rid) (o + 2) = Known (byte_of v 2) ->
cell_read (get_shadow st rid) (o + 3) = Known (byte_of v 3) ->
ov_read_bytes rsegs m (wa (r_base r + o)) 4 = Some (le4 (wz v)).
Proof.
intros st m rid r o v MR Hr Hk Ho Ho4 Hv H0 H1 H2 H3.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF _ _ _ _ SH | sf_fb; destruct sfP_ as (WF & _ & _ & _ & _ & SH) ].
destruct (SH rid r Hr Hk) as [HW HB].
destruct (HB o _ ltac:(lia) H0) as [B0 _]. destruct (HB (o + 1) _ ltac:(lia) H1) as [B1 _].
destruct (HB (o + 2) _ ltac:(lia) H2) as [B2 _]. destruct (HB (o + 3) _ ltac:(lia) H3) as [B3 _].
assert (B : bytes_at rsegs m (r_base r + o) ([b8 (byte_of v 0)] ++ ([b8 (byte_of v 1)] ++ ([b8 (byte_of v 2)] ++ [b8 (byte_of v 3)])))).
{ apply bytes_at_app. split; [exact B0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia; exact B1|].
apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
- replace (r_base r + o + 1 + 1) with (r_base r + (o + 2)) by lia. exact B2.
- replace (r_base r + o + 1 + 1 + 1) with (r_base r + (o + 3)) by lia. exact B3. }
cbn [app] in B.
replace (le4 (wz v)) with [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
2:{ rewrite le4_bytes by lia. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
replace ((v / 16777216) mod 256) with (v / 16777216) by (symmetry; apply Z.mod_small; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). reflexivity. }
rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ _ 0 4 B); [lia|cbn; lia].
Qed.

Lemma rre_hdr_spec {RCEIL : RunCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
st (blk : block) r g bm ai ar (b3 lo hi i off : Z),
rmrep st m -> mem_inv rsegs m ->
hdr_facts st blk r g bm ai ar b3 lo hi i off ->
bv_unsigned a0 = blk_addr blk ->
let mr := get_meta_rec st g in
let e := snd (blk_slot blk) + get_stride mr - IB in
evt rsegs (rre_hdr_post ra sp gp tp t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11
(blk_addr blk) (conc st g) (conc st bm) (r_base r + e) (m_sizeclass mr) (meta_word mr)
(e - (snd (blk_slot blk) + UNIT * off) - blk_size blk) (get_stride mr) F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x332c8) fc None m (seg_rom rsegs)).
Proof.
intros until off. intros MR MI HF HP.
destruct HF as [Fslot Fhosts Ffst Freg Fkind Frbase Fmem Fsnd Fb0 Fb16 Foff Faddr Fsize Ffit Fspan Fstride Fk4 Fk3 Fk2 Fk1 Fb3 Flo Fhi Fidx Fres Foff16 Fmslot Fg0 Farea Fcheck Fsecret Favail Ffreed Fli Ffreeable Fmaplen Fsc Fi Fnav Fnfr Ftop Fg16 Fg63 Fg17 Ffoot Fnogrp Finit].
cbv zeta in Ffoot. first [ sf_destruct 4%nat Ffoot as F5 FZ FE _ | sf_fb; destruct Ffoot as (F5 & FZ & FE & _) ].
cbv zeta. set (mr := get_meta_rec st g) in *. set (c := blk_slot blk) in *. set (e := snd c + get_stride mr - IB) in *.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ].
first [ sf_destruct 5%nat WF as Hres WR DISJ WA WG | sf_fb; destruct WF as (Hres & WR & DISJ & WA & WG) ].
pose proof Fstride as [S16 SM]. pose proof Frbase as (RB0 & RBM & RBC). unfold alloc_ceiling in RBC.
assert (SI0 : 0 <= get_stride mr * i) by (clear -S16 Fi; apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride mr * i + get_stride mr <= get_stride mr * (m_last_idx mr + 1)).
{ clear -S16 Fi. rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
set (po := snd c + UNIT * off).
set (res := e - po - blk_size blk).
assert (OFF16 : 16 * off + 16 <= get_stride mr).
{ clear -Ffit Fsize SM Foff. unfold UNIT, IB in *. Z.div_mod_to_equations. lia. }
assert (SIM : (get_stride mr * i) mod 16 = 0) by (clear -SM; unfold UNIT in SM; rewrite Z.mul_mod, SM, Z.mul_0_l by lia; reflexivity).
pose proof (round_up_pg_ge (r_len r)) as RUP.
assert (RNG : 16 <= po /\ po + 16 <= round_up_pg (r_len r) /\ 0 <= r_base r + po /\ r_base r + po + 16 <= 2^64 /\ po mod 16 = 0
/\ po <= e /\ e + 4 <= round_up_pg (r_len r) /\ 0 <= res /\ res = get_stride mr - IB - UNIT * off - blk_size blk).
{ subst po e res. rewrite Fsnd.
clear -SI0 SIL Fspan OFF16 Fi Foff Fb0 Fb16 S16 RB0 RBC RUP SIM Ffit Fsize. unfold UNIT, IB in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. lia. }
first [ sf_destruct 9%nat RNG as PLO PHI P0 P64 P16 PE EHI RES0 RESEQ | sf_fb; destruct RNG as (PLO & PHI & P0 & P64 & P16 & PE & EHI & RES0 & RESEQ) ].

destruct (rmrep_shadow_read st m (fst c) r (po - 4) 0 MR Freg Fkind ltac:(clear -PLO PHI; lia) Fk4) as [R4 _].
destruct (rmrep_shadow_read st m (fst c) r (po - 3) b3 MR Freg Fkind ltac:(clear -PLO PHI; lia) Fk3) as [R3 _].
destruct (rmrep_shadow_read2 st m (fst c) r (po - 2) lo hi MR Freg Fkind ltac:(clear -PLO PHI; lia) ltac:(clear -PLO PHI; lia) Fk2
ltac:(replace (po - 2 + 1) with (po - 1) by (clear; lia); exact Fk1)) as (R2 & _ & _).
rewrite <- le2_lohi in R2 by assumption.

destruct (rmrep_shadow_read st m (fst c) r e 0 MR Freg Fkind ltac:(clear -PLO PE EHI; lia) FE) as [RE0 _].
destruct (rmrep_shadow_read st m (fst c) r (e - res) 0 MR Freg Fkind ltac:(clear -PLO PE EHI RES0 RESEQ Fsize; subst res; lia)
ltac:(destruct (Z.eq_dec res 0) as [R0|R0]; [rewrite R0, Z.sub_0_r; exact FE| apply FZ; clear -R0 RES0; lia])) as [RZ _].
assert (BIG : 160 <= b3 -> Z.shiftr b3 5 = 5 /\ 5 <= res < 2^32
/\ ov_read_bytes rsegs m (wa (r_base r + e - 4)) 4 = Some (le4 (wz res)) /\ ov_read_bytes rsegs m (wa (r_base r + e - 5)) 1 = Some [b8 0]).
{ intros H160. subst res.
assert (R5 : 5 <= e - po - blk_size blk).
{ clear -H160 Fb3 Fres RESEQ RES0. rewrite Z.shiftr_div_pow2 in Fres by lia. change (2^5) with 32 in Fres.
Z.div_mod_to_equations. lia. }
first [ pose proof (F5 R5) as sfP_; sf_destruct 6%nat sfP_ as C0 C1 C2 C3 C5 R32 | sf_fb; destruct (F5 R5) as (C0 & C1 & C2 & C3 & C5 & R32) ].
split; [rewrite Fres; clear -R5; lia|]. split; [clear -R5 R32; lia|]. split.
- replace (r_base r + e - 4) with (r_base r + (e - 4)) by (clear; lia).
apply (rmrep_shadow_read4 st m (fst c) r (e - 4) _ MR Freg Fkind); try (clear -PLO PE EHI R5 R32 RES0; lia).
+ exact C0.
+ replace (e - 4 + 1) with (e - 3) by (clear; lia). exact C1.
+ replace (e - 4 + 2) with (e - 2) by (clear; lia). exact C2.
+ replace (e - 4 + 3) with (e - 1) by (clear; lia). exact C3.
- replace (r_base r + e - 5) with (r_base r + (e - 5)) by (clear; lia).
exact (proj1 (rmrep_shadow_read st m (fst c) r (e - 5) 0 MR Freg Fkind ltac:(clear -PLO PE EHI R5; lia) C5)). }

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
pose proof Fi as Fi'. rewrite <- Fidx in Fi', Fnav, Fnfr, Fg16.

eapply evt_cut.
{ eapply (rre_hdr_walk1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
- clear -Fsc. lia.
- clear -Fmaplen. lia.
- clear -Fi'. lia.
- exact Fnav.
- exact Fnfr.
- exact Fg16.
- exact Fg63. }
cbv beta. intros ms1 (x28 & x29 & ->).

assert (STRIDE : (if negb (m_maplen mr =? 0) && (m_last_idx mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr)) = get_stride mr).
{ unfold get_stride. destruct (m_last_idx mr =? 0); destruct (m_maplen mr =? 0); cbn [negb andb]; unfold UNIT; clear; lia. }
assert (EE : conc st bm + 16 + get_stride mr * Z.land b3 31 + get_stride mr - 4 = r_base r + e).
{ rewrite HB, Fidx. subst e. rewrite Fsnd. unfold UNIT, IB. clear. lia. }
assert (ERSV : (if 160 <=? b3 then res else Z.shiftr b3 5) = res).
{ destruct (Z.leb_spec 160 b3) as [H|H]; [reflexivity|]. rewrite Fres. subst res. rewrite <- RESEQ.
clear -H Fb3 Fres RES0. rewrite Z.shiftr_div_pow2 in Fres by lia. change (2^5) with 32 in Fres. Z.div_mod_to_equations. lia. }
eapply evt_mono.
{ eapply (rre_hdr_walk2 ra sp gp tp s2 x28 x29 t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
(r_base r + po) (conc st g) (conc st bm) b3 (lo + 256 * hi) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) res);
rewrite ?STRIDE, ?EE, ?ERSV.
- exact EP.
- clear -HB RB0 Fb0. lia.
- clear -S16. unfold UNIT in S16. lia.
- clear -PE. lia.
- clear -EHI RBC RUP. lia.
- intros HH. assert (SC48 : m_sizeclass mr < 48) by (clear -HH Fsc; lia). split; [exact SC48|]. apply rsize_classes_read; [exact MI| clear -SC48 Fsc; lia].
- exact Fb3.
- clear -Flo Fhi. lia.
- clear -Fli. lia.
- clear -Ffreeable. lia.
- clear -Fsc. lia.
- clear -Fmaplen. lia.
- exact Fg17.
- intros H160. first [ pose proof (BIG H160) as sfP_; sf_destruct 4%nat sfP_ as X1 X2 X3 X4 | sf_fb; destruct (BIG H160) as (X1 & X2 & X3 & X4) ]. split; [exact X1|]. split; [exact X2|]. split; [exact X3| exact X4].
- rewrite <- EP, HP, Faddr. subst res po c. clear -Fsize. lia.
- replace (r_base r + e - res) with (r_base r + (e - res)) by (clear; lia). exact RZ.
- exact RE0. }
cbv beta. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as y7 y28 y29 -> | sf_fb; destruct sfH_ as (y7 & y28 & y29 & ->) ]. unfold rre_hdr_post. first [ unshelve sf_eexists 3%nat; [ exact (y7) | exact (y28) | exact (y29) | ] | sf_fb; exists y7, y28, y29 ].
rewrite STRIDE, EE, ERSV. rewrite <- EP, HP. subst res po c. reflexivity.
Qed.
