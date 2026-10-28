(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W12.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RF_malloc_entry RAllocSlot_iface RASlot_I RMallocKit_A3 RASlot_W2 RASlot_W4.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.
#[using="SC"] Lemma rag_entry_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rt1_regs sc (Z_to_bv 64 0x161ec) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x161d4) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
pose proof (size_class_range sc SC) as SZR.
step. Local Ltac2 Set LiaHints.tbl := fun () => "0040>28427635284.3542794413067.356753472924.34 7442835684.34 00000100600700;SS3SZRSS2SC".
rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (68784 + 2 * sc) with (68784 + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AG1.
#[using="Type"] Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then 0x16854 else 0x161f8)) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x161ec) fc None m (seg_rom usegs)).
Proof.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.
#[using="SZC CR SMALL"] Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof.
unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.
#[using="SZC CR SMALL"] Lemma rnest_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv usegs m ->
evt usegs (fun ms' => exists a2' a3' a4',
ms' = MS (mkR (Z_to_bv 64 0x163d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16304) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
unfold RSIZE_CLASSES, ralloc_slot_entry in *.
assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt usegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x163d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 68784) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 90100) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 68784) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x163c8) fc None m (seg_rom usegs))).
{ intros a0' a2' a3' jv ->.
Local Ltac2 Set LiaHints.tbl := fun () => "01T0>10022931269.6310023289312.6411028254010.6912076517061.6612712880528.591482069293.72 16075583823.6616916892674.5918179265889.5318179724641.5518181367782.5218395536607.4918468417428.6021606054183.6422796385821.5723235732884.7124140338504.7425109010663.7126454810024.6127316758952.4927648159986.6927688007078.6327690091296.6228155396397.6130261996870.6631323011143.7231464074128.7131464074129.6431799012504.7232185887926.7132509216314.6935516470224.6635842097472.7035842273781.7136759189123.6536761272705.6637991463626.6640823607660.6240829623250.4641415828429.5341416053612.6041417920842.5241417920844.5941418040267.7441652169568.6042704510862.4643071640411.6043073741533.5743393816798.724351261724.71 4353507130.72 4353685161.72 43901314518.6945615793312.5946778126076.5448460604158.7148775325161.6449098857183.7049099320514.4850998141849.6051185923522.6451792457914.7452488874831.6252514079877.7252514229526.7253279723706.6953517140246.6953519091638.7253519207973.7255899452735.4756775177115.6656777654300.715687589883.74 5690084950.56 5690538106.67 5690538235.64 5690538876.61 5690555260.58 5742896305.57 5742896310.52 5744989872.54 59251176999.5959251192621.6063370523563.6565199789371.6666468437330.6367482146131.6067507599744.656753458106.52 6753458109.57 6753473980.71 6753473981.64 67961326483.66679672258.69  7178147913.66 7620900481.57 7620900486.52 8396965519.62 9540561407.74 9627047418.69 00000400800900=00B00G00L00P00T00X00\00d00i00j00o01401901=01E01K01P01U01Z01_01c01j01n02202902A02B02C02H02M02R02W02[02\02]02^02_02`02a02b02g03103503903>03C03H03M03R03W03[03\03`03j04404904:04?04D04E04F04K04L04M04N04X04\04`04a04b04c04d04e04f04j04n05205705<05=05D05H05L05Q05R05S05T05U05V05[05b05f05j05k05l061S2IRS2IRSS2R5S3RV2S3SR2S3SR1S2P2S2XRS2XRS2XRS2PR3Q10S3K13SS3RV1S3SR2S3K13S2HcS3K132EKS4SCRjS3RW4S3RW2S3RW2S3K13S2IRS2EX2LTS2IRS2IRS2EX2GES3Q102LGSSS3I1RS3I1RS3RW3S3RW3S2IRSSSSSSSS3K13S5SMALL2PRS2R1S2R1S3I1RS3I1RS3I1RS3I1RS3RW4S3RV2S2R2SS2IRS5SMALL2PRS5SMALL2PRS3K13SS3K13S3Q10SSS3RW4SSSS5SMALL2PRS2QRS2QRSSSSSSS2XRS2XRS2XRS3K13S3K13SS2EX2K3S2R4S2R3S3SR1SSSSSS3RW4S2EX2K3S2XRS2XRSSS3RW4".
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite SysStep.sextw_small by lia. step. step.
apply evt_done. do 3 eexists. reflexivity. }
step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
-
apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
-
assert (Q10 : 10 <= q) by (unfold n' in K; nia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].
step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.
step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.
step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
assert (K13 : 3 <= k <= 12).
{ unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
step. rewrite ?zxb_b8 by lia. clear DBR.
step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (68784 + (i + 1) * 2) with (68784 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.
assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt usegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x163d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 68784) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 90100) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 68660) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 68784) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x163ac) fc None m (seg_rom usegs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.
step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (68784 + i1 * 2) with (68784 + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.
step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End STC.
#[using="Type"] Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then 0x1644c else 0x163d8)) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x163d4) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros IR MI.
step. Local Ltac2 Set LiaHints.tbl := fun () => "0050>35497614361.3949712512005.3949718884623.3859308548964.3959314923118.3700000100800900?00BSS2IR2NEFS2IR1KS1K".
if_cases K; zify_cond K.
- replace (idx =? -1) with true.
2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
apply evt_done. reflexivity.
- replace (idx =? -1) with false.
2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
