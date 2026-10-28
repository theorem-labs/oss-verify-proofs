(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0qk X0pm X0pq X0qf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m1 X1kt X1li X1ll.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rntf_seq {RCEIL : RunCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31f9c) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as sfP_; first [ sf_destruct 4%nat sfP_ as LI FB SCR ML | sf_fb; destruct sfP_ as (LI & FB & SCR & ML) ].
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite ?(unsigned_lit sc) by lia. st1.

pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
pose proof (rw_cells_store_ok_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (448336 + 912)) C6 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish (448336 + 912) [b8 ns] FR ST MU WM SOK.
set (st1 := upd_ctx (set_seq ns) st) in MR1.

st1.
assert (JOIN : forall m2 (a1' : word),
rmrep (seq_st ns sc st) m2 -> mem_inv rsegs m2 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (448336, 448336 + 928)] m0 m2 -> wmono rsegs m0 m2 ->
stk rsegs m2 lo (bv_unsigned sp + -96) -> rw_cells rsegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 run_canary; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 448336) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31fb4) fc None m2 (seg_rom rsegs))).
{ intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
rmeta_chunk MR2 MS2 CH.
assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.

st1. st1. st1. st1. clear CH.
rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
eapply evt_mono.
{ eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | unfold alloc_ceiling; lia | lia | idtac].
unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
intros ms' PO. unfold rntf_ret_post in PO |- *.
first [ sf_destruct 20%nat PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m' -> PE WM' MI' ST' MR' | sf_fb; destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR') ].
sf_eexists 14%nat. split; [reflexivity|].
split.
{ eapply rpres_except_trans.
- apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
- eapply rpres_except_mono; [exact PE|]. intros a Ha.
eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
if_cases K; zify_cond K.
-
assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
- assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }

st1.
pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_store_ok rsegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (448336 + (sc + -7) + 848)) US
ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
clear US.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish (448336 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
eapply JOIN; try eassumption.
unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
unfold upd_ctx. cbn. reflexivity.
Qed.

Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. vm_compute. reflexivity. Qed.

Lemma rntf_top {RCEIL : RunCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
0 <= c_seq (ctx st) < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31f3c) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as sfP_; first [ sf_destruct 4%nat sfP_ as LI FB SCR ML | sf_fb; destruct sfP_ as (LI & FB & SCR & ML) ].
pose proof (meta_word_maplen _ MW) as M12.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.

pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
st1. clear RDS. st1.

st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
-
st1.
replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | unfold alloc_ceiling; lia].
-
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (rw_cells_of_u8arr rsegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
replace (448336 + 848) with 449184 in UB by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(448336 + 848, 448336 + 880)]%Z mX) as MUz; pose proof (wmono_refl rsegs mX) as WMz end.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UA' : u8arr rsegs mX (RCTX + 848) (zeros 32))
by (apply (u8arr_of_rw_cells rsegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
clear UB.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
{ eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }

st1. st1.
replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
replace (conc st p) with (conc stz p) by reflexivity.
change (get_meta_rec st g) with (get_meta_rec stz g).
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | unfold alloc_ceiling; lia
| apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.
