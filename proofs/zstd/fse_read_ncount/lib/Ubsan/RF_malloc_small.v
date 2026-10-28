(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section CANSEC1. Context {rc : runConstT}.
Definition rcoarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
(pw st (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f4c) fc None m (seg_rom usegs)
/\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).
Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR : rmrep st1 m1.
Hypothesis MI : mem_inv usegs m1.
#[using="LB m1 MF MR"] Lemma ractive_ptr_facts sc g : active st sc = Some g -> 0 < conc st1 g /\ conc st1 g + 40 <= ATOP /\ meta_slot st1 g
/\ (exists b, m_mem (get_meta_rec st g) = Some b)
/\ 0 <= m_avail (get_meta_rec st g) < 2^32 /\ 0 <= m_freed (get_meta_rec st g) < 2^32
/\ 0 <= m_last_idx (get_meta_rec st g) + 32 * m_freeable (get_meta_rec st g) + 64 * m_sizeclass (get_meta_rec st g) + 4096 * m_maplen (get_meta_rec st g) < 2^64.
Proof.
intros ACT.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & NN).
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hm). cbv zeta in FG. destruct FG as (MSL & AV & FR & LI & FB & SC & ML & _).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _).
split; [exact G0|]. split; [exact GC|]. split; [exact MSL|]. split; [exists b; reflexivity|]. split; [exact AV|]. split; [exact FR|].
pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8939814016.2900000FS4SC483GSC2LI2FB2ML2MP".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc LB MF MR"] Lemma rcoarse_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' : word) F fc (n sc : Z),
0 <= sc < 48 -> (sc < 32 -> 0 <= Z.lor sc 1 < 48) ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15e90) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros SC48 SC1.
pose proof MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
unfold RNEED_LOCKS, RCTX, RMLOCK, RDEBRUIJN in *. atop_facts.
step. Local Ltac2 Set LiaHints.tbl := fun () => "0110>10201937053.5910238199168.6110248686495.5011050469525.7611642439126.6413393755217.6513398065251.6413398065505.5914948325015.5816075526003.8616075585089.9016075585474.8816077671799.7018640779162.6618902113350.7620227092868.7621120493065.8422690918617.7325873574711.5929452098538.6029784363385.4929786642503.5929788478954.6632506860313.6032506876824.493287173647.66 33049509228.6433619798654.5935215642241.6735215749309.6035598392397.6435598392655.5941204535006.6441363640385.9041363640770.8843629686293.5943629686551.6446691848436.6846706283971.6652514159926.5952977498993.7252977498993.7353512850223.5953519151387.7653519152145.5655066363918.6557035524481.9057037638922.7558746133639.5959308628304.5659308628304.6059308629082.7659308629082.8759314923118.5959314923118.7061869901873.4962569856042.6667898097258.6767900194410.697436804850.66 7441084001.49 7441128644.57 7441129283.58 7441129410.59 9148053109.58 00000300900?00C00L00S00Z00a00b00g00l01501901>01B01F01U01Z01_01d01e01f01g01m02302B02H02M02Z02g02n03503>03C03H03M03R03W03\03]03b03g03h03i03j04;04@04E04J04N04U04Y04a04d04j05005505:05?05E05K05Q05W05]05cS1HS4SC48S4SC48S2U1S4FUsc2K6S5SC432S5SC432S5SC432FS3AV1S3RF1S3RA13FR1S2AVS3SC1S2K9S2K9S3G103G1C5ATOPRS3FU1S3SC'S3SC'SSSS4SC48S4SC48S2K22K31H2H02H1S4FUscS3SC'S2G02GC5ATOPRS2G02GC5ATOPRS5SC432S5SC432S4FUsc2K6S3FR1S3AV1S3NE6S3NE6S3SC1S3SC1SS3FU1S3FU1SSSS4SC482K22K31H2H0S3FU1S3FU1S3SC'S2K1S2G02K1S2K7S3G102K7S1KS2G01KS4SC48S3SC1S3SC1S3SC1S4SC48S4SC48S4SC48S4SC48S4SC48S4SC48".
rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc _ (wa (324152 + 80 + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.
assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144) a0' a1' a2' a3' a4 a5 a6 a7
(pw st1 (active st sc')) (Z_to_bv 64 68660) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f3c) fc None m1 (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc' SC'.
destruct (active st sc') as [g|] eqn:ACT'.
- destruct (ractive_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW). atop_facts.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & _).
change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM.
step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [subst gw; reflexivity| reflexivity].
- unfold pw. cbn [oconc].
step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }
assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144) a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 68660) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f48) fc None m1 (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc' ACT'. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }
assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 68660) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f28) fc None m1 (seg_rom usegs))).
{ intros a1' a2' a3' s4' sc' SC'.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc' _ (wa (324152 + 80 + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
step. step. apply J40. exact SC'. }
step.
destruct (active st sc) as [g|] eqn:ACT.
-
destruct (ractive_ptr_facts sc g ACT) as (G0 & GC & _). atop_facts.
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. exact SC48.
-
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
coarse_sc st sc = if b then
(let usage1 := usage st (Z.lor sc 1) in
let usage1 := match active st (Z.lor sc 1) with
| None => usage1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
end in
if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
{ intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }
step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
+
rewrite (CS false) by (subst sc; reflexivity).
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
+
step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), land_ones64 in K3 by lia.
*
rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
* assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.
step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
--
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). exact EV. }
step. step. apply J4c. exact ACT.
-- pose proof (proj1 (land_1_even sc) K4) as EV.
pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (usages st1) sc _ (wa (324152 + 464 + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
step. pose proof (FU sc) as FUsc.
step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
**
assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.
step. rewrite (unsigned_lit sc) by lia. fold sc1.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc1 _ (wa (324152 + 80 + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
step.
pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (usages st1) sc1 _ (wa (324152 + 464 + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
step. pose proof (FU sc1) as FU1.
set (u1 := match active st sc1 with
| None => usage st sc1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
assert (U1 : 0 <= u1 < 2^61).
{ unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
{ rewrite (CS true COND). reflexivity. }
clear CS.
assert (J20 : forall (a2' a3' : word),
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 68660) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f1c) fc None m1 (seg_rom usegs))).
{ intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
-
rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. exact SC1.
-
step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. exact SC48. }
change (Z_to_bv 64 0) with (wz 0).
destruct (active st sc1) as [g1|] eqn:ACT1.
+++
destruct (ractive_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1). atop_facts.
pose proof (rmeta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM1.
step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
cbn [default from_option id] in u1.
step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
***
assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NA). reflexivity. }
apply J20.
*** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.
step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NF). reflexivity. }
apply J20.
---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.
step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
2:{ unfold u1. rewrite K8, K9. reflexivity. }
apply J20.
+++
unfold pw. cbn [oconc].
step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by reflexivity.
apply J20.
**
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
step. step. apply J4c. exact ACT.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End COARSE.
End CANSEC1.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma mul_srliw27_sxv k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ k))) * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
Local Ltac2 Set LiaHints.tbl := fun () => "0040=2589538102.3 38715781522.342470662452.353395063683.3000001002003004SSSS".
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
gw (wz k) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15fa8) fc None m3 (seg_rom usegs)
/\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
/\ munch [(G + 24, G + 28)]%Z m m3 /\ wmono usegs m m3 /\ mem_inv usegs m3
/\ rw_cells usegs m3 (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)].
#[using="Type"] Lemma rfast_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw prev next memw : word) F fc m
(G avail k freed mword : Z),
bv_unsigned gw = G ->
rw_cells usegs m (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
mem_inv usegs m -> (G + 40 <= 0x10000 \/ 0x50000 <= G) ->
0 < avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= mword < 2^64 ->
0 <= k < 32 -> lowbit avail = 2 ^ k ->
evt usegs (rfc_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v F fc m G avail k prev next memw freed mword)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv avail)) a1 a2 a3 a4 a5 a6 a7
gw (Z_to_bv 64 RDEBRUIJN) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f4c) fc None m (seg_rom usegs)).
Proof.
intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
unfold RMLOCK, RDEBRUIJN in *.
assert (P2 : 0 < 2 ^ k <= avail).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00E0>11805467289.6517149291614.5917404331924.5927380570520.5228155396397.5835048811823.5637183207711.5341422216306.5444015292588.5344969372623.564814699815.65 49705053714.6551796758275.5451796758275.5659250900146.5659251192621.5759314873579.5860348278314.576485907384.59 9538873720.53 9544701510.56 00000700;00?00C00G00K00O00P00Q00V00^00b00f00j00n01201801@01D01E01FS2HG2HBS2AVS2HGS2AVS2HKS2AVS2HKSSS3Hk'S3GWR2HBS2HBS2HKS2HKS2HKS2HKS2P21HS2P23P32S2P2SS".
destruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.
step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.
step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
rewrite (swrap_word (sxv avail - sxv (2 ^ k))).
step.
lazymatch goal with H : rw_cells usegs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
apply (rw_cells_congr usegs mc (bv_unsigned gw) cs
[C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
[| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
end.
step.
apply evt_done. unfold rfc_post.
do 4 eexists.
lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
split; [reflexivity|].
split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Lemma rcore0_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw : word) F fc (m : mem),
evt usegs (fun ms' => exists a1', ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f84) fc None m (seg_rom usegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f4c) fc None m (seg_rom usegs)).
Proof.
intros.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))). Local Ltac2 Set LiaHints.tbl := fun () => "0010>10073487437.33000001S".
rewrite (negw_and_lowbit 0) by lia. rewrite lowbit_0.
step. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. }
apply evt_done. eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.
Let st1 := set_tick t st.
#[using="LB HENF MF TP CLO LO N0 NT BL"] Lemma rfast_core_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word) (sc : Z) (g : aptr),
let mr := get_meta_rec st g in
let mask := m_avail mr in
let first := lowbit mask in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
active st sc = Some g -> 0 < mask -> n + 4 <= 16 * size_class sc ->
rimplT o (K (upd_meta g (m_set_avail (mask - first)) st1) (Some (g, ctz32 first))) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (wz (sxv mask)) a1 a2 a3 a4 a5 a6 a7
(pw st1 (Some g)) (Z_to_bv 64 RDEBRUIJN) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f4c) fc None m1 (seg_rom usegs)).
Proof.
intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
atop_facts.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & _). change (get_meta_rec st g) with mr in GSC.
pose proof (mf_gmeta _ _ MF) as FG0.
assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
{ change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
destruct (m_mem mr) as [b|] eqn:Hm.
- specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
destruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48. Local Ltac2 Set LiaHints.tbl := fun () => "00I0?11805646497.13311805747091.12511805747091.12713743418541.11314667198462.13018663383848.13026370078405.11334265700178.1273501531155.132 35473938759.12736799961766.13141306280664.11341418021747.89 43145348523.11351792547494.12351792562178.89 51792638050.90 52977661291.12 54133380533.11354133478644.86 59249111820.11359315137787.12859999277384.1278826125952.125 8927264033.113 00000300800C00P00Y00`00i01201301;01G01L01M01R01W01\01a02:02B02J02O02U02j02k03ES1HS3GI2S3CLO2LO2GCS5ATOPR2G02GCS5ATOPR1HS2X12X2S3GI13GI2S3AVr3P2kSS3CLO2GCS3GR03GR12HXS3LBKSS3FRrS3K32S3K32S3K32S4SC483GSC2A12A22A32A42A5S2AV3AVrS2AV3AVrS3K32S2NT1XS3CLO2LO5ATOPR2GC3GI2SS4SC483GSC3LIr3FBr3SCr3MPr".
lia.
- exfalso. destruct (FA sc g ACT) as (_ & _ & NN). apply NN. exact Hm. }
destruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr).
destruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK). fold first in LBK.
assert (P2k : 0 < 2 ^ k <= mask).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE'). unfold first, lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
destruct (rfast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr).
fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. destruct FC as (CTR & SEC & INI & _).
assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)). atop_facts.
set (G := conc st1 g) in *.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.
riprefixT.
eapply evt_mono.
{ eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
(m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
| |- _ => idtac end.
all: try lia. all: try assumption. }
intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
destruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM').
pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
replace (ctz32 first) with k by (rewrite LBK; symmetry; exact CTZ).
replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
change (pw st1 (Some g)) with (pw st2 (Some g)).
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= ATOP).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). atop_facts. lia. }
assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
{ intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
eapply (HENF st2 g b r k m3 s errv).
- rewrite E3. unfold st2. apply rmrep_meta_set_avail; [exact MR| exact MSL| lia].
- apply ticks_ok_upd_meta. exact TK.
- eapply unk_agree_munch; [| exact MU | |].
+ eapply unk_agree_ext; [exact UA| reflexivity| intros; reflexivity| reflexivity].
+ intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
+ intros rid r1 H1. exact (RB rid r1 H1).
- exact MI'.
- eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_munch_frame; [| exact MU| exact WM|].
+ eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_mono; [|exact Ha].
intros rid r1 H1. exists r1. repeat split; auto. lia.
+ intros x Hx NC. cbn. split; [|exact I].
intros HX. apply NC. left. right. right. right. exists rid0, r0. split; [exact Hr0|]. split; [exact Hk0|]. lia.
- intros a Ha. right. right. left. apply SPANFP.
replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [exact Ha|].
unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
- exact CTR.
- exact SO.
- intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
- apply mrel_same; reflexivity.
- exact BL.
- reflexivity.
- reflexivity.
- reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FASTCORE.
Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.
Let st1 := set_tick t st.
#[using="as_inv RAS HENF HFAIL MR0 TP CLO LO NT BL"] Lemma ras_call_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
as_pre st st1 sc n FUEL ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
0 <= sc < 48 ->
rimplT o (alloc_slot full_lay FUEL st1 sc n
(fun st2 idx => if idx <? 0 then K st2 None
else match active st2 sc with
| Some gp => K st2 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f84) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
atop_facts. pose proof (RAS_STACK_ge sc) as ASG. Local Ltac2 Set LiaHints.tbl := fun () => "00X0?10248604446.79 10248686495.15014790831251.11614790831670.81 15329108121.81 17991103377.11717991433096.81 1800609155.126 18663383848.87 19613546272.81 19681647996.81 24638473347.12526373526162.81 2778534265.116 27905022521.11729786642460.14932508664573.1493501531155.123 35287317527.11638446806799.12540223843627.11743988483203.12449628078609.11749630411483.12049630411483.15349712594560.15050584054793.11651709126181.11654243526019.12554743483735.81 57462221169.81 59308630497.11859308630497.15059315137787.15261867999894.81 6266820779.117 64997134979.1267442835204.149 8532466695.126 8828223154.81  00000600<00V01001101601;01<01C01D01L01M01]01^01j01k02102202302402502602702802902H02X02Y02Z02[02\02`02m03303903:03;03A03G03HS4SC48S4SC48S3CLO2LO3SPR5ATOPR3ASG3ASMS3CLO2LO3SPR5ATOPR3ASG3ASMFS3CLOS3CLOSS2X12X2FS2LO3ASMSS3CLO2LO3ASG3ASMSS2LO3ASG3ASMSS4SC48SSSSSSSSS4IDX03IDX4LI32S3CLO2LO3ASG3ASMSSFFS2KBS3IDX4LI322KBS2NT1XS4SC48SSS4SC48S4IDX0S".
pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= ATOP).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). atop_facts. lia. }
subst tp. unfold RATP in *. rewrite unsigned_lit in ERR by lia.
unfold RMLOCK, RDEBRUIJN in *.
riprefixT.
step. rewrite sextw_small by lia. step. step.
step. apply evt_done.
eapply (RAS FUEL) with (st0 := st) (lo := lo).
all: lazymatch goal with
| |- as_pre _ _ _ _ _ => try exact PRE
| |- rmrep _ _ => try exact MR
| |- ticks_ok _ => try exact TK
| |- unk_agree _ _ _ => try exact UA
| |- brk_link_ps _ _ => try exact BL
| |- rauxv_ok _ _ => try (rewrite unsigned_lit by lia; eapply rauxv_ok_weaken; [exact AUX| atop_facts; lia])
| |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; exact ST)
| |- mem_inv _ _ => try assumption
| |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; exact ERR)
| |- _ => idtac
end.
all: try (rewrite ?unsigned_lit by lia; atop_facts; lia).
all: try reflexivity.
intros st2 idx s' ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES).
replace (ret_pc (Z_to_bv 64 0x15f94)) with (Z_to_bv 64 0x15f94) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.
pose proof (rframe_after_call st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:(atop_facts; lia)) as FR'.
assert (AUX2' : rauxv_ok m' (bv_unsigned sp)) by (eapply (rauxv_ok_malloc_fp st st2 lo _ m0 m' m1 m'); [exact MR0| exact MR'| exact AUX| exact PE'| atop_facts; lia| lia]).
assert (PE2 : rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m').
{ eapply rpres_except_trans; [| eapply rpres_except_mono; [exact PE'|]; intros a Ha; eapply rmalloc_fp_sp_mono; [|exact Ha]; lia].
eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_st_mono; [exact MREL|].
eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. repeat split; auto. lia. }
assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|exact MREL]; apply mrel_same; reflexivity).
pose proof MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _). unfold RCTX in CXA'. unfold RMLOCK in ML'.
clear MU WM PE AUX.
destruct RES as [-> | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
-
change (-1 <? 0) with true. cbv iota.
riprefixT.
step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
clear KB.
step. step.
step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact ML']. }
intros ms'' ->.
replace (ret_pc (Z_to_bv 64 0x15ff0)) with (Z_to_bv 64 0x15ff0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
step. step. step. step. step. step. step. step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. eapply (HFAIL st2 m' s' errv').
all: try assumption.
-
replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
riprefixT.
step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
clear KB.
step. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st2) sc (pw st2 (Some g)) (wa (324152 + 80 + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.
apply evt_done.
change (Z_to_bv 64 idx) with (wz idx).
eapply (HENF st2 g b r idx m' s' errv').
all: try assumption.
+ intros a Ha. eapply rmalloc_fp_sp_mono; [|apply SPANFP; exact Ha]. lia.
+ intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. exact X.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ASCALL.
Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.
Let st1 := set_tick t st.
#[using="LB as_inv RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL"] Lemma rmalloc_small_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
sc = size_to_class n -> 0 <= sc < 48 -> n + 4 <= 16 * size_class sc ->
(forall sc', 0 <= sc' < 48 -> n + 4 <= 16 * size_class sc' -> as_pre st st1 sc' n FUEL) ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_small_ctrl full_lay st1 n K bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15e90) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
pose proof (RAS_STACK_ge 0) as ASG. unfold st1 in *.
rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
pose proof (coarse_sc_cases st sc SC48) as CC.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>22411087419.812422975426.95 29511724752.9532504696989.8032504696989.8232504696989.8533439172646.9536924239871.8936924239871.9141365644648.9141414005484.9451804930461.9457688986768.9568562630614.8500000600:00F00L00R00X00\00]00^00g00h00m01601>S4NFITS2N0S2LO3ASG3K32S4SC48S4SC48S4SC48S2P2FFS3ANZ3AVrSS3K32S3ANZ3AVrS4NFIT1H".
assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
{ destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
set (sc' := coarse_sc st sc) in *.
change (active (set_tick t st) sc') with (active st sc').
riprefixT. eapply evt_cut.
{ eapply (rcoarse_walk st LB m1 t MF MR); [exact SC48| intros; apply lor1_range; lia]. }
fold sc'. intros ms' (a0' & a1' & a2' & a3' & -> & HA0).
change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
destruct (active st sc') as [g|] eqn:ACT'.
- cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
+
rewrite AZ, lowbit_0. cbn.
eapply evt_cut. { apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
+
apply evt_done.
destruct (ractive_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _).
destruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK).
assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
cbn [negb]. cbv iota.
change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
eapply rfast_core_implT; try eassumption; try lia.
- cbn iota. subst a0'.
eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End SMALL.
End CANSEC3.
