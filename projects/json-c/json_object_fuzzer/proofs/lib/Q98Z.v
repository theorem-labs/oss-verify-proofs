(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 QnDM_c1 QTp6 Lib.CodeAt Lib.StepGen Lib.GwInst Lib.GwEq Lib.GwApply QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QnDM_c1.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.wr_at_app). Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.rw_cells_app). Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.sx32_neg). Qed.

End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Qfw3_c1 Q2qa Qy5Y QCwx QZAi QUZl Q7S0 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1.
Import QCwx.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof.
intros Ha Hi. split.
- intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
rewrite H, Z.bits_0 in T. discriminate.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.

#[using="Type"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).

#[using="Type"] Lemma rget_meta_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc m
(off16 mword maplen : Z),
0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> Z.shiftr mword 12 = maplen ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt rsegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) (wz mword) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcdf64) fc None m (seg_rom rsegs)).
Proof.
intros until maplen. intros O16 MW ML MW4 Hml.
st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
- st1. unfold rget_meta_post. finish.
- st1. st1. st1. if_cases K2; zify_cond K2.
+ st1. unfold rget_meta_post. finish.
+ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

#[using="Type"] Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt rsegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcde70) fc None m (seg_rom rsegs)).
Proof.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
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

st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
-  specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
- specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (159560 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (159560 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma rget_meta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st (p : aptr) r g gh ar (b3 lo hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
evt rsegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz (conc st g)) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rget_meta_entry) fc None m (seg_rom rsegs)).
Proof.
intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.

destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.

destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.

pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m MR) as RC.

destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
{ unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
unfold rget_meta_entry.
eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
- intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.

Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).

#[using="Type"] Lemma runlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
bv_unsigned a0 = RMLOCK ->
rw_cells rsegs m (bv_unsigned a0) [C4 (wz 0)] ->
evt rsegs (runlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 runlock_entry) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HA LK. unfold runlock_entry.
step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
{ exfalso. rewrite wz_unsigned in K by lia. lia. }
step. apply evt_done. reflexivity.
Qed.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1.
Export Qy5Y.Mq6.
Import QCwx.Mq1 QFqQ.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rrepfoot (st : mstate) (a : Z) : Prop :=
(RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4 \/ 0x6446f8 <= a < 0x6446f8 + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
\/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

#[using="Type"] Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a. Proof. intros; right; left; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_vmlock st a : RVMLOCK <= a < RVMLOCK + 4 -> rrepfoot st a. Proof. unfold RVMLOCK; intros; right; left; right; assumption. Qed.
#[using="Type"] Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma rrepfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> rrepfoot st a.
Proof. intros; do 6 right; left. exists rid, r, v. auto. Qed.
#[using="Type"] Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a. Proof. intros; do 7 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a. Proof. intros; do 8 right; assumption. Qed.

#[using="Type"] Lemma rbytes_at_agree : forall m m' A bs,
bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree : forall m m' A cs,
rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono rsegs m m' -> rw_cells rsegs m' A cs.
Proof.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree : forall m m' A ws,
u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono rsegs m m' -> u64arr rsegs m' A ws.
Proof.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree : forall m m' A bs,
u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono rsegs m m' -> u8arr rsegs m' A bs.
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

#[using="Type"] Lemma rmrep_transport_unowned : forall st m m' W,
rmrep st m -> munch W m m' -> wmono rsegs m m' -> ivs_avoid W (rrepfoot st) -> rmrep st m'.
Proof.
intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
+ apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
+ apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
+ apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
+ apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
+ apply TC; [exact G6 |]. intros a Ha. apply rrepfoot_vmlock. cbn in Ha. unfold RVMLOCK in *. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
+ apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
pose proof Bt as (B0 & B1 & _). cbn in B1.
eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

#[using="Type"] Lemma rmrep_put_meta_frame : forall st m m' g mr',
rmrep st m -> meta_slot st g ->
munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono rsegs m m' ->
rw_cells rsegs m' (conc st g) (meta_cells st mr') ->
rmrep (put_meta g mr' st) m'.
Proof.
intros st m m' g mr' MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
pose proof (round_up_pg_ge (r_len ra)) as RU.

assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
assert (TC : forall A cs, rw_cells rsegs m A cs ->
(A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx. unfold RCTX in *.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 | cbn; lia].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
+ apply TC; [exact C6 | cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros a' ar' Ha'. cbn in Ha'.
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
destruct (decide (a' = a)) as [->|NEa].
+ rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k' Hk'. rewrite Hmc, get_meta_rec_put.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
* apply TC; [exact PD| cbn; lia].
+ assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
{ rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
- rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
eapply rarea_rep_ext; [exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
* apply TC; [exact PD| cbn; lia].
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [|exact I].
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

#[using="Type"] Lemma rmrep_ctx_frame' : forall st st' m m',
rmrep st m -> munch [(RCTX, RCTX + 928)] m m' -> wmono rsegs m m' ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
rmrep_ctx st' m' -> rmrep st' m'.
Proof.
intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
unfold RCTX in *.
split; [|split; [exact CX'|split; [|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len ra)).
destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
+ apply TC; [exact A1| cbn; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
+ apply TC; [exact A3| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len rb)).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

#[using="Type"] Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof.
intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof.
intros st m v (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

#[using="Type"] Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 80 + 8 * sc) ->
ov_read_bytes rsegs m a 8 = Some (le8 (pw st (active st sc))).
Proof.
intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 464 + 8 * sc) ->
ov_read_bytes rsegs m a 8 = Some (le8 (wz (usage st sc))).
Proof.
intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa (RCTX + 880 + i) ->
ov_read_bytes rsegs m a 1 = Some [b8 (bounces st i)].
Proof.
intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa (RCTX + 912) ->
ov_read_bytes rsegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof.
intros st m a (_ & (_ & _ & _ & _ & _ & C6 & _) & _) ->.
apply (rw_cells_read_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_fmh_read : forall st m a, rmrep st m -> a = wa (RCTX + 16) ->
ov_read_bytes rsegs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof.
intros st m a (_ & (C1 & _) & _) ->.
apply (rw_cells_read_at rsegs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); reflexivity.
Qed.

#[using="Type"] Lemma rbytes_at_cons : forall m a b bs, bytes_at rsegs m a (b :: bs) <-> bytes_at rsegs m a [b] /\ bytes_at rsegs m (a + 1) bs.
Proof.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app rsegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.

#[using="Type"] Lemma rmrep_group_word8 : forall st m b gh,
rmrep st m -> (s_groups st) !! b = Some gh ->
exists bs : list byte, ov_read_bytes rsegs m (wa (conc st b + 8)) 8 = Some bs /\ length bs = 8%nat
/\ (bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs))) mod 32 = g_active_idx gh.
Proof.
intros st m b gh MR Hb. pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (GR b gh Hb) as (w8 & R & Hw8).
destruct (SH (fst b) r Hr Kr) as [HWr _].
pose proof WF as (_ & WR & _). destruct (WR (fst b) r Hr) as (_ & _ & _ & RC2 & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
destruct (rwr_at_bytes_exist m (conc st b + 9) 7) as (bs & Lbs & Bbs).
{ eapply wr_at_sub; [exact HWr| rewrite Cb; lia | rewrite Cb; lia]. }
{ lia. }
{ rewrite Cb. lia. }
assert (B8 : bytes_at rsegs m (conc st b + 8) [w8]).
{ destruct R as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
replace (conc st b + Z.of_nat 8) with (conc st b + 8) in HB by lia.
first [ apply bytes_at_app in HB; destruct HB as [HB _]; exact HB | exact HB ]. }
assert (B : bytes_at rsegs m (conc st b + 8) (w8 :: bs)).
{ apply rbytes_at_cons. split; [exact B8|]. replace (conc st b + 8 + 1) with (conc st b + 9) by lia. exact Bbs. }
exists (w8 :: bs).
assert (L8 : length (w8 :: bs) = 8%nat) by (cbn; lia).
split; [|split; [exact L8|]].
- rewrite <- (Z.add_0_r (conc st b + 8)). rewrite (bytes_at_read rsegs m _ _ 0 8 B); [|lia|rewrite L8; cbn; lia].
cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite L8; lia). reflexivity.
- rewrite load8_le_val by exact L8. cbn [map le_val]. rewrite <- Hw8.
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
set (L := le_val (map bv_unsigned bs)). replace (256 * L) with ((8 * L) * 32) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

#[using="Type"] Lemma rmeta_slot_bounds : forall st m g, rmrep st m -> meta_slot st g ->
0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ (conc st g + 40 <= 0x10000 \/ 0x645000 <= conc st g) /\ conc st g mod 4 = 0
/\ conc st g mod 4096 >= 24.
Proof.
intros st m g MR (a & ar & k & Ha & Hk & Eg). pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS, alloc_ceiling in *. pose proof (round_up_pg_ge (r_len ra)).
rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.

#[using="Type"] Lemma rgroup_bounds : forall st m b gh, rmrep st m -> (s_groups st) !! b = Some gh ->
0 <= conc st b /\ conc st b + 16 <= alloc_ceiling /\ (conc st b + 16 <= 0x10000 \/ 0x645000 <= conc st b) /\ conc st b mod 16 = 0.
Proof.
intros st m b gh MR Hb. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.

Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> rfree_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

#[using="Type"] Lemma rfree_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> rfree_fp st lo sp a.
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.

#[using="Type"] Lemma rfree_fp_mono : forall st st' lo sp sp' a,
s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
(forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
sp' <= sp ->
rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
intros st st' lo sp sp' a ER ES HG HS H.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
- right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch' : forall C W m m',
munch W m m' -> wmono rsegs m m' ->
(forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
rpres_except C m m'.
Proof.
intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_cov : forall C W m m',
munch W m m' -> wmono rsegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

#[using="MU WIN"] Lemma rctxW_avoid : forall A n, (A + n <= RCTX \/ RCTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; exact Hin.
+ destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

#[using="m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW :
(rw_cells rsegs m' RCTX (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 80 <= lo \/ hi <= RCTX)) ->
(u64arr rsegs m' (RCTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> RCTX + 464 <= lo \/ hi <= RCTX + 80)) ->
(u64arr rsegs m' (RCTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> RCTX + 848 <= lo \/ hi <= RCTX + 464)) ->
(u8arr rsegs m' (RCTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> RCTX + 880 <= lo \/ hi <= RCTX + 848)) ->
(u8arr rsegs m' (RCTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> RCTX + 912 <= lo \/ hi <= RCTX + 880)) ->
(rw_cells rsegs m' (RCTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 928 <= lo \/ hi <= RCTX + 912)) ->
c_init_done (ctx st') = c_init_done (ctx st) ->
rmrep st' m'.
Proof.
intros H1 H2 H3 H4 H5 H6 H7.
pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6 & C7) & GL & AR & GR & SH).
assert (CX' : rmrep_ctx st' m').
{ unfold rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- rewrite H7. exact C7. }
eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
- apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.

Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QnDM_c1.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.wr_at_app). Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.rw_cells_app). Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.sx32_neg). Qed.

End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1.
Import QCwx.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof.
intros Ha Hi. split.
- intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
rewrite H, Z.bits_0 in T. discriminate.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.

#[using="Type"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).

#[using="Type"] Lemma rget_meta_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc m
(off16 mword maplen : Z),
0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> Z.shiftr mword 12 = maplen ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) (wz mword) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0628) fc None m (seg_rom usegs)).
Proof.
intros until maplen. intros O16 MW ML MW4 Hml.
st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
- st1. unfold rget_meta_post. finish.
- st1. st1. st1. if_cases K2; zify_cond K2.
+ st1. unfold rget_meta_post. finish.
+ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

#[using="Type"] Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0534) fc None m (seg_rom usegs)).
Proof.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.

assert (RG' : ov_read_bytes usegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
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

st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
-  specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
- specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (159656 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (159656 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma rget_meta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st (p : aptr) r g gh ar (b3 lo hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz (conc st g)) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rget_meta_entry) fc None m (seg_rom usegs)).
Proof.
intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.

destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.

destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.

pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m MR) as RC.

destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
{ unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
unfold rget_meta_entry.
eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
- intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.

Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).

#[using="Type"] Lemma runlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
bv_unsigned a0 = RMLOCK ->
rw_cells usegs m (bv_unsigned a0) [C4 (wz 0)] ->
evt usegs (runlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 runlock_entry) fc None m (seg_rom usegs)).
Proof.
intros until m. intros HA LK. unfold runlock_entry.
step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
{ exfalso. rewrite wz_unsigned in K by lia. lia. }
step. apply evt_done. reflexivity.
Qed.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1.
Export Qy5Y.Mq6.
Import QCwx.Mq3 QFqQ.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rrepfoot (st : mstate) (a : Z) : Prop :=
(RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4 \/ 0x646db8 <= a < 0x646db8 + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
\/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

#[using="Type"] Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a. Proof. intros; right; left; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_vmlock st a : RVMLOCK <= a < RVMLOCK + 4 -> rrepfoot st a. Proof. unfold RVMLOCK; intros; right; left; right; assumption. Qed.
#[using="Type"] Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma rrepfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> rrepfoot st a.
Proof. intros; do 6 right; left. exists rid, r, v. auto. Qed.
#[using="Type"] Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a. Proof. intros; do 7 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a. Proof. intros; do 8 right; assumption. Qed.

#[using="Type"] Lemma rbytes_at_agree : forall m m' A bs,
bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof.
intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree : forall m m' A cs,
rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono usegs m m' -> rw_cells usegs m' A cs.
Proof.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree : forall m m' A ws,
u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono usegs m m' -> u64arr usegs m' A ws.
Proof.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree : forall m m' A bs,
u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono usegs m m' -> u8arr usegs m' A bs.
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

#[using="Type"] Lemma rmrep_transport_unowned : forall st m m' W,
rmrep st m -> munch W m m' -> wmono usegs m m' -> ivs_avoid W (rrepfoot st) -> rmrep st m'.
Proof.
intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (TC : forall A cs, rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells usegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (u64arr_bound usegs m _ _ C2) as B2. pose proof (u64arr_bound usegs m _ _ C3) as B3.
pose proof (u8arr_bound usegs m _ _ C4) as B4. pose proof (u8arr_bound usegs m _ _ C5) as B5.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
+ apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
+ apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
+ apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
+ apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
+ apply TC; [exact G6 |]. intros a Ha. apply rrepfoot_vmlock. cbn in Ha. unfold RVMLOCK in *. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
+ apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
pose proof Bt as (B0 & B1 & _). cbn in B1.
eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

#[using="Type"] Lemma rmrep_put_meta_frame : forall st m m' g mr',
rmrep st m -> meta_slot st g ->
munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono usegs m m' ->
rw_cells usegs m' (conc st g) (meta_cells st mr') ->
rmrep (put_meta g mr' st) m'.
Proof.
intros st m m' g mr' MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
pose proof (round_up_pg_ge (r_len ra)) as RU.

assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
assert (TC : forall A cs, rw_cells usegs m A cs ->
(A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells usegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx. unfold RCTX in *.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 | cbn; lia].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
+ apply TC; [exact C6 | cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros a' ar' Ha'. cbn in Ha'.
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
destruct (decide (a' = a)) as [->|NEa].
+ rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k' Hk'. rewrite Hmc, get_meta_rec_put.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
* apply TC; [exact PD| cbn; lia].
+ assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
{ rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
- rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
eapply rarea_rep_ext; [exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
* apply TC; [exact PD| cbn; lia].
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [|exact I].
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

#[using="Type"] Lemma rmrep_ctx_frame' : forall st st' m m',
rmrep st m -> munch [(RCTX, RCTX + 928)] m m' -> wmono usegs m m' ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
rmrep_ctx st' m' -> rmrep st' m'.
Proof.
intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
assert (TC : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells usegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
unfold RCTX in *.
split; [|split; [exact CX'|split; [|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len ra)).
destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
+ apply TC; [exact A1| cbn; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
+ apply TC; [exact A3| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len rb)).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

#[using="Type"] Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof.
intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof.
intros st m v (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

#[using="Type"] Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 80 + 8 * sc) ->
ov_read_bytes usegs m a 8 = Some (le8 (pw st (active st sc))).
Proof.
intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 464 + 8 * sc) ->
ov_read_bytes usegs m a 8 = Some (le8 (wz (usage st sc))).
Proof.
intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa (RCTX + 880 + i) ->
ov_read_bytes usegs m a 1 = Some [b8 (bounces st i)].
Proof.
intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa (RCTX + 912) ->
ov_read_bytes usegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof.
intros st m a (_ & (_ & _ & _ & _ & _ & C6 & _) & _) ->.
apply (rw_cells_read_at usegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_fmh_read : forall st m a, rmrep st m -> a = wa (RCTX + 16) ->
ov_read_bytes usegs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof.
intros st m a (_ & (C1 & _) & _) ->.
apply (rw_cells_read_at usegs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); reflexivity.
Qed.

#[using="Type"] Lemma rbytes_at_cons : forall m a b bs, bytes_at usegs m a (b :: bs) <-> bytes_at usegs m a [b] /\ bytes_at usegs m (a + 1) bs.
Proof.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app usegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.

#[using="Type"] Lemma rmrep_group_word8 : forall st m b gh,
rmrep st m -> (s_groups st) !! b = Some gh ->
exists bs : list byte, ov_read_bytes usegs m (wa (conc st b + 8)) 8 = Some bs /\ length bs = 8%nat
/\ (bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs))) mod 32 = g_active_idx gh.
Proof.
intros st m b gh MR Hb. pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (GR b gh Hb) as (w8 & R & Hw8).
destruct (SH (fst b) r Hr Kr) as [HWr _].
pose proof WF as (_ & WR & _). destruct (WR (fst b) r Hr) as (_ & _ & _ & RC2 & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
destruct (rwr_at_bytes_exist m (conc st b + 9) 7) as (bs & Lbs & Bbs).
{ eapply wr_at_sub; [exact HWr| rewrite Cb; lia | rewrite Cb; lia]. }
{ lia. }
{ rewrite Cb. lia. }
assert (B8 : bytes_at usegs m (conc st b + 8) [w8]).
{ destruct R as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
replace (conc st b + Z.of_nat 8) with (conc st b + 8) in HB by lia.
first [ apply bytes_at_app in HB; destruct HB as [HB _]; exact HB | exact HB ]. }
assert (B : bytes_at usegs m (conc st b + 8) (w8 :: bs)).
{ apply rbytes_at_cons. split; [exact B8|]. replace (conc st b + 8 + 1) with (conc st b + 9) by lia. exact Bbs. }
exists (w8 :: bs).
assert (L8 : length (w8 :: bs) = 8%nat) by (cbn; lia).
split; [|split; [exact L8|]].
- rewrite <- (Z.add_0_r (conc st b + 8)). rewrite (bytes_at_read usegs m _ _ 0 8 B); [|lia|rewrite L8; cbn; lia].
cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite L8; lia). reflexivity.
- rewrite load8_le_val by exact L8. cbn [map le_val]. rewrite <- Hw8.
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
set (L := le_val (map bv_unsigned bs)). replace (256 * L) with ((8 * L) * 32) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

#[using="Type"] Lemma rmeta_slot_bounds : forall st m g, rmrep st m -> meta_slot st g ->
0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ (conc st g + 40 <= 0x10000 \/ 0x647000 <= conc st g) /\ conc st g mod 4 = 0
/\ conc st g mod 4096 >= 24.
Proof.
intros st m g MR (a & ar & k & Ha & Hk & Eg). pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS, alloc_ceiling in *. pose proof (round_up_pg_ge (r_len ra)).
rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.

#[using="Type"] Lemma rgroup_bounds : forall st m b gh, rmrep st m -> (s_groups st) !! b = Some gh ->
0 <= conc st b /\ conc st b + 16 <= alloc_ceiling /\ (conc st b + 16 <= 0x10000 \/ 0x647000 <= conc st b) /\ conc st b mod 16 = 0.
Proof.
intros st m b gh MR Hb. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.

Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> rfree_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

#[using="Type"] Lemma rfree_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> rfree_fp st lo sp a.
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.

#[using="Type"] Lemma rfree_fp_mono : forall st st' lo sp sp' a,
s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
(forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
sp' <= sp ->
rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
intros st st' lo sp sp' a ER ES HG HS H.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
- right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch' : forall C W m m',
munch W m m' -> wmono usegs m m' ->
(forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
rpres_except C m m'.
Proof.
intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_cov : forall C W m m',
munch W m m' -> wmono usegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono usegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

#[using="MU WIN"] Lemma rctxW_avoid : forall A n, (A + n <= RCTX \/ RCTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; exact Hin.
+ destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

#[using="m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW :
(rw_cells usegs m' RCTX (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 80 <= lo \/ hi <= RCTX)) ->
(u64arr usegs m' (RCTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> RCTX + 464 <= lo \/ hi <= RCTX + 80)) ->
(u64arr usegs m' (RCTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> RCTX + 848 <= lo \/ hi <= RCTX + 464)) ->
(u8arr usegs m' (RCTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> RCTX + 880 <= lo \/ hi <= RCTX + 848)) ->
(u8arr usegs m' (RCTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> RCTX + 912 <= lo \/ hi <= RCTX + 880)) ->
(rw_cells usegs m' (RCTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 928 <= lo \/ hi <= RCTX + 912)) ->
c_init_done (ctx st') = c_init_done (ctx st) ->
rmrep st' m'.
Proof.
intros H1 H2 H3 H4 H5 H6 H7.
pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6 & C7) & GL & AR & GR & SH).
assert (CX' : rmrep_ctx st' m').
{ unfold rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- rewrite H7. exact C7. }
eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
- apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.

Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

End RC__1.
End Mq5.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_pe.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaBw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaBw.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := tt.
End GwI.

Section M.
Variables (txt : list Z) (p : Z).
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.

Local Notation JF := (JF txt p).
Local Notation JR := (JR p).

#[using="BYT Hp Hnul"] Lemma JF_getc' : forall k c f c2 f2, JF k c f -> c <> 0 -> sh_getc f = (c2, f2) -> JF (k + 1) c2 f2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_getc') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_getc')]. Qed.

#[using="Type"] Lemma JF_JR : forall k c f, JF k c f -> c <> 0 -> JR f.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_JR)]. Qed.
#[using="Hp"] Lemma JF_unget_JR : forall k c f, JF k c f -> 1 <= k -> JF (k - 1) 0 (sh_unget f) /\ JR (sh_unget f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_unget_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_unget_JR)]. Qed.
#[using="Hp"] Lemma JF_ungets_JR : forall n k c f, JF k c f -> Z.of_nat n <= k -> (1 <= n)%nat -> JR (fs_unget_loop n f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_ungets_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_ungets_JR)]. Qed.
#[using="Type"] Lemma JR_lim0' : forall f, JR f -> JR (sh_lim0 f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JR_lim0') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JR_lim0')]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QzgB.JR) (@QaBw.JR) (Q6nq.gwt_def (@QzgB.JF) (@QaBw.JF) Q6nq.gwt_nil)).
#[using="BYT Hp Hnul"] Lemma fs_ws_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J)]. Qed.

#[using="Type"] Lemma lor32_nz : forall c v, (Z.lor c 32 =? v) = true -> 97 <= v -> c <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.lor32_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.lor32_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_inf_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_nan_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J)]. Qed.

#[using="Type"] Lemma alnum_nz : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz) [] '([(-97); (-65); 95]%Z : list Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_par_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma df_lz_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk)]. Qed.
#[using="BYT Hp Hnul"] Lemma df_rz_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk)]. Qed.

#[using="Type"] Lemma ishexc_nz : forall c, ishexc c = true -> c <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.ishexc_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.ishexc_nz)]. Qed.
#[using="Type"] Lemma hx_dig_cond_nz : forall s, hx_dig_cond s = true -> hx_c s <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_cond_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_cond_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma hx_dig_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk)]. Qed.

#[using="Type"] Lemma df_lz_0 : forall n g f r, df_lz_loop n (g, 0, f) = Some r -> r = (g, 0, f).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_0)]. Qed.
#[using="Type"] Lemma df_rz_0 : forall n g l f r, df_rz_loop n (g, l, 0, f) = Some r -> r = (g, l, 0, f).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_0)]. Qed.

Section HXJ.
Variables (fuelc : nat) (bits emin sign pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation HX_e2' := (HX_e2 bits emin sign).
Local Notation HX_rz' := (HX_rz fuelc bits emin sign pok).
Local Notation HX_alz' := (HX_alz fuelc bits emin sign pok).
Local Notation HX_lz' := (HX_lz fuelc bits emin sign pok).

#[using="Type"] Lemma HX_e2_f : forall f x y e2 f' y', HX_e2' f x y e2 = Some (f', y') -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_e2_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_e2_f)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_tail_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_dig_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_rz_J : forall gd rp c f k f' y', HX_rz' gd rp c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_rz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_rz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_alz_J : forall gd c f k f' y', HX_alz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_alz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_alz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_lz_J : forall gd c f k f' y', HX_lz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_lz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_lz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma hexfloat_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J)]. Qed.
End HXJ.

Section FSJ.
Variables (fuelc : nat) (pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation FS_zero' := (FS_zero fuelc 53 (-1074) pok).
Local Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Local Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

#[using="BYT Hp Hnul Hpk"] Lemma FS_zero_J : forall sg c2 f2 k f' y', FS_zero' sg c2 f2 = Some (f', y') -> JF k c2 f2 -> 2 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_zero_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_zero_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_tail_h_J : forall sg c f k f' y', FS_tail_h' sg c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_tail_h_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_tail_h_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_nan_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_inf_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_sign_J : forall c f k f' y', FS_sign' c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_sign_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_sign_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma floatscan_h_JR : forall f f' y, floatscan_h fuelc f 1 pok = Some (f', y) -> JF 0 1 f -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.floatscan_h_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.floatscan_h_JR)]. Qed.
End FSJ.
End M.
