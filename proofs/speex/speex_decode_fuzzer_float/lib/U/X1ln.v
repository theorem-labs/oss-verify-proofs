(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0qk X0pm X0qf X0qj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m1 X1ky X1li X1ll.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rnest_call_post {RCEIL : RunCeiling} (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x31f68) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31ce0) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

Lemma rntf_nest_call {RCEIL : RunCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
let mr := get_meta_rec st g in
let mr1 := get_meta_rec st g1 in
let idx1 := Z.land b3 31 in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
(s_groups st) !! p = Some ghp ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
bytes_at rsegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
base1 = aadd p (- (UNIT * off16) - UNIT) ->
(s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
(s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) ->
c_init_done (ctx st) = 1 ->
0 <= c_secret (ctx st) < 2^64 ->
idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
(m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
(48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
(m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31f3c) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk INIT1 SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as sfP_; first [ sf_destruct 4%nat sfP_ as LI FB SCR ML | sf_fb; destruct sfP_ as (LI & FB & SCR & ML) ].
pose proof (meta_word_maplen _ MW) as M12.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ]. pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DISJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DISJ & WA & WG) ].
first [ pose proof (rgroup_conc st p ghp WF Hp) as sfP_; sf_destruct 9%nat sfP_ as r Hr Cp Kr Sp0 Sp1 SpA RB0 RBC | sf_fb; destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC) ].
first [ pose proof (WR _ r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ RBAL _ _ RFr | sf_fb; destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr) ]. pose proof (round_up_pg_ge (r_len r)) as RU.
pose proof (rreserved_disjoint _ _ RFr) as sfP_; first [ sf_destruct 4%nat sfP_ as Dr1 Dr2 Dr3 Dr4 | sf_fb; destruct sfP_ as (Dr1 & Dr2 & Dr3 & Dr4) ].

first [ pose proof (WG base1 gh1 Hgh1) as sfP_; sf_destruct 6%nat sfP_ as rb Hrb _ Bb0 Bb1 BbA | sf_fb; destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA) ]. rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
{ rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
pose proof MS1 as sfP_; first [ sf_destruct 6%nat sfP_ as a ara k Ha Hkk Eg | sf_fb; destruct sfP_ as (a & ara & k & Ha & Hkk & Eg) ].
first [ pose proof (WA a ara Ha) as sfP_; sf_destruct 7%nat sfP_ as rg Hrg Sa0 Sa1 AAL ANG ALR | sf_fb; destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR) ].
first [ pose proof (WR (fst a) rg Hrg) as sfP_; sf_destruct 5%nat sfP_ as RgB0 RgBAL _ RgBC RFa | sf_fb; destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa) ].
assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
assert (Hao : area_of g1 = a).
{ rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
{ rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
unfold alloc_ceiling, RCTX, AREA_HDR, META_SIZE, NSLOTS in *.
assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.

change (frozen (conc st p mod 16 = 0)) in P16m.
change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
clear HGm AAL RBAL RgBAL SpA BbA.
first [ sf_destruct 4%nat GB as GB0 GB1 GB2 _ | sf_fb; destruct GB as (GB0 & GB1 & GB2 & _) ]. first [ sf_destruct 4%nat G1B as G1B0 G1B1 G1B2 _ | sf_fb; destruct G1B as (G1B0 & G1B1 & G1B2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.

st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
pose proof (rmrep_ctx_secret_read1 st mX MR INIT1) as RC;
pose proof (bytes_at_read rsegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
pose proof (bytes_at_read rsegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
pose proof (bytes_at_read rsegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
end.
rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.

rewrite run_secret_wz in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. rewrite run_secret_wz in RC. unfold RCTX in RC.
pose proof (SECRET_range) as SER.
change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.

st1.
eapply evt_cut.
{ eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
(m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
(m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) SECRET).
all: lazymatch goal with
| |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
| |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
| |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
| |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
| |- ov_read_bytes _ _ (wa 448336) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
| |- rw_cells _ _ (conc _ _) _ => exact MM
| |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
| |- _ => idtac
end.
all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
| (clear - RBC Sp1 Cp r b3 p st RCEIL HBc off16 base1 G1B2 G1B0 g1 G1B1 B3 O16 HI8 LO8 hi8 lo8 AV1 FR1 SER LI1 FB1 SC1 ML1; lia) | unfold wz; rewrite ?unsigned_lit by (clear - Dr4 Dr3 Dr2 Dr1 RBC RB0 Sp1 Sp0 Cp r b3 p st RCEIL; lia); (clear - p st; lia) | unfold UNIT in *; (clear - Bb0 RB0 Cp r off16 b3 p st RCEIL; lia) ]. }
intros ms' sfH_; first [ sf_destruct 5%nat sfH_ as ga2 ga3 ga4 ga5 -> | sf_fb; destruct sfH_ as (ga2 & ga3 & ga4 & ga5 & ->) ].
replace (ret_pc (Z_to_bv 64 0x31f54)) with (Z_to_bv 64 0x31f54) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

st1.
unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
st1.

clear CH MM RG RA RC R4 R2.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ GR0 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & GR0 & _) ]. destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rw_cells_store_ok_at rsegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
clear RWp.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
end.
rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
apply (rmrep_grp_del_eq st _ g p) in MR2.

st1. st1.
apply evt_done. unfold rnest_call_post. sf_eexists 14%nat.
split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
cbv delta [mkR]. unfold RCTX. reflexivity. }
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_group; [exact Hp | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

Lemma rntf_nest_ret {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> fm_facts st g ->
conc st g = conc st0 g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
(MS (mkR (Z_to_bv 64 0x31f68) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31f68) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
st1. st1. st1.
rewrite <- Hcg.
eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia].
Qed.
