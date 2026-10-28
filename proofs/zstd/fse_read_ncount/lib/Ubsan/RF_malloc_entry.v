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
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section CANSEC1. Context {rc : runConstT}.
Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.
#[using="Type"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. Local Ltac2 Set LiaHints.tbl := fun () => "0010=42464846132.2000001S".
pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes usegs RDEBRUIJN 32 with Some bs => bs | None => [] end).
#[using="Type"] Lemma rdebruijn_ro : forall m, mem_inv usegs m -> ro_cells usegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.
#[using="Type"] Lemma rdebruijn_read : forall m k, mem_inv usegs m -> 0 <= k < 32 ->
ov_read_bytes usegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
intros m k MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
Local Ltac2 Set LiaHints.tbl := fun () => "0050=12561274796.736800083462.843035830038.749165022855.766731657638.700000300:00>00A00ES1RS2Hk2HnS2HkS1RS2Hk".
rewrite (bytes_at_read usegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mul_srliw27 k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi.
Local Ltac2 Set LiaHints.tbl := fun () => "0050=25673529136.341415986323.342464509897.451794599906.353401755006.400000400500600:00;S2HkSSS2HkS".
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.
#[using="Type"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0010=39913182148.3000004S2Hk".
assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). Local Ltac2 Set LiaHints.tbl := fun () => "0010<6755913577.4000001S".
rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15e90) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
#[using="Type"] Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
stk usegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
rw_cells usegs m RNEED_LOCKS [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until n. intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry, RNEED_LOCKS in *.
step. Local Ltac2 Set LiaHints.tbl := fun () => "02;0>10022931269.6910023289312.7011028254010.7811805467289.5711805467289.5811805467289.5911805467289.6012076517061.7512712880528.681482069293.85 16075583823.7216918837679.651800609155.59 18179265889.6218179724641.6418181367782.6118392021271.5818468417428.6620112476756.5120979536691.5821606054183.7022796385821.6623102976490.6223235732884.8424140570697.792425334338.53 24638473347.5925604052563.5725604052563.5925604052563.6026454810024.6727648159986.7827688007078.7227690091296.7128155396397.6730264064457.7931323011143.8531378308326.5031464074128.8431464074129.7031799012504.8532509216314.7833721217258.5835516470224.7235842097472.8335842273781.8436759189123.7436761272705.7537989264965.7938446806799.5840346260359.8440823607660.7140825509068.5141247213570.5841415828429.6241416053612.6641417920842.6141417920844.6841418135242.7941652169568.6643061431595.4843071640411.6943073741533.6643393816798.854351261724.84 4353507130.85 4353685161.85 43901314518.7843988483203.574541396730.70 45615793312.6845848756903.5746778126076.6348460604158.8448775325161.7049649769127.6049705053714.5749705053714.5849705053714.5949705053714.6050998141849.6651792414139.7952105090727.5952488874831.6852488886504.6252489072197.6452514079877.8552514229526.8553279723706.7853517140246.7853519091638.8553519141806.6653519207973.8554243526019.5955347555524.8456775177115.7256777654300.845687611130.79 5690084950.65 5690538106.76 5690538235.73 5690538876.70 5690555260.67 57017997905.655742896305.66 5742896310.61 5744989872.63 59249165194.6559251192621.6659308628179.5259308628304.5259308631791.6660858483367.5961929812114.5261929812241.5261929812368.5662241974760.5762241974760.5862241974760.5962241974760.6063305555623.5963370523563.7464997134979.6065199789371.7266468437330.7267482146131.6967507599744.716753458106.61 6753458109.66 6753473980.84 6753473981.70 67961326483.72679672258.78  7178147913.72 7620900481.66 7620900486.61 8396965519.68 9540656382.79 9627047418.78 00000400800900=00A00E00I00M00R00W00\00`00a00e00i00m01501:01=01>01?01D01M01R01Z01]01^01b01f01j02202702<02A02F02J02Q02R02V02Z02a02b02f02g02l03103603;03?03@03D03E03F03N03O03P03Q03R03S03X03\03`03d03i03n04304804=04>04?04D04E04I04J04N04O04W04_04g04o05405<05=05B05K05P05Q05R05W05X05Y05Z05[05\05g05k05o06006106206306406506606:06>06B06G06L06R06X06\06]06`06c06f07107<07G07R07S07T07U07\07`07d07i07j07k07l07m07n08308:08>08B08C08D08IS2IRS2IRSS2HBS2HBS2HBS2HBS2R5S3RV2S3SR2S3SR1S2P2SS2XRS2XRS2XRS2QR3Q10S3K13S1NSSS3RV1S2K21H2H0S3SR2S2LG3Q10S1NSS2HBS2HBS2HBS2EK3K13S3RW4S3RW2S3RW2S3K13S2IRS2EX2LTSS2IRS2IRS2EX2GESS2HBSS3I1RS3I1RS3RW3S3RW3S2IRSS2HcSSS1N1H2H0SSSSSS3K13S2LOS2R1S2R1S3I1RS3I1RS3I1RS3I1RS3RW4SSS3RV2SS2R2SS2IRSS3SPR2HBS3SPR2HBS3SPR2HBS3SPR2HBS3K13S2LG3Q10SS3Q10S2K21H2H0S3Q10SSS3RW4SSSSSS2IR2Hc3I1RS2QRS2QRSSSSSSSS2XRS2XRS2XRS3K13S3K13S1N2K0S1N2K1S2KLSS1NS1NS1NS3ILO2LO2HBS3ILO2LO2HBS3ILO2LO2HBS3ILO2LO2HBSSSS2EX2K3S2R4S2R3S3SR1SSSSSS3RW4S2EX2K3S2XRS2XRSSS3RW4".
carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 324035 [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 68660) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15e78) fc None mj (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].
step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step.
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
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.
step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step. replace (68784 + (i + 1) * 2) with (68784 + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
step. rewrite ?zx16_wz by lia. clear RS1.
assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 324035 [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 324144)
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 68784) (Z_to_bv 64 c) (Z_to_bv 64 (68784 + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 68660) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15e5c) fc None mj (seg_rom usegs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.
step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (68784 + i1 * 2) with (68784 + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.
step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15cf8) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
#[using="Type"] Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
stk usegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
evt usegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00N0>11805467289.5311805467289.5411805467289.5511805467289.561800609155.55 20979536691.5424638473347.5525604052563.5325604052563.5525604052563.5631378308326.4633721217258.5438446806799.5443061431595.4443988483203.5345848756903.5349649769127.5649705053714.5349705053714.5449705053714.5549705053714.5652105090727.5554243526019.5559308628179.4859308628304.4860858483367.5561929812114.4861929812241.4863305555623.5564997134979.5600000400800<00@00A00B00C00G00K00O00P00T00U00Y00Z00[00\00d00l01401<01=01>01D01J01K01N01Q01R01SS2HBS2HBS2HBS2HBSSSS2HBS2HBS2HBSS2HBSS2LOSSSS3SPR2HBS3SPR2HBS3SPR2HBS3SPR2HBSSS1N2K0S1N2K1SS1NS1NSS".
carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
