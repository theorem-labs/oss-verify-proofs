(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_extenddftf2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
bytes_at bsegs m VA (u64s slots).
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
if (ty =? T_PTR)%Z then slot
else if (ty =? T_INT)%Z then sx32 slot
else if (ty =? T_UINT)%Z then zx32 slot
else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Definition pop_arg_hi (ty : Z) (slot y : word) : word :=
if (ty =? T_DBL)%Z then Z_to_bv 64 (hi64 (f128_of_d (bv_unsigned slot))) else y.
Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
/\ rw_cells bsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
/\ rw_cells bsegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
/\ va_area m' VA slots
/\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).
#[using="Type"] Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.
#[using="Type"] Lemma va_read8 : forall m VA slots (i : Z) w a,
bytes_at bsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes bsegs m a 8 = Some (le8 w).
Proof.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25273904528.1546081068896.1558870951973.1561555382922.1500000:00D00Q00[S4Hlen3HluS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read bsegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma va_read4 : forall m VA slots (i : Z) w a,
bytes_at bsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes bsegs m a 4 = Some (le4 w).
Proof.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
Local Ltac2 Set LiaHints.tbl := fun () => "0030>46081068896.1558870951973.1561555382922.1500000:00G00QS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read bsegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
rewrite firstn4_le8. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=49631155169.6000003S1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac if_lit :=
lazymatch goal with
| |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma pop_arg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
rw_cells bsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
rw_cells bsegs m (bv_unsigned a0) [C8 x; C8 y] ->
stk bsegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
mem_inv bsegs m ->
a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
(16 <= bv_unsigned sp)%Z ->
(bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
rng_aimg RNG -> rng RNG (bv_unsigned sp - 16) 16 -> rng RNG (bv_unsigned a2) 8 -> rng RNG (bv_unsigned a0) 16 ->
rng RNG VA (8 * Z.of_nat (length slots)) ->
evtF bsegs RNG (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x90460) fc None m (seg_rom bsegs)).
Proof.
intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4 RIMG RFR RAP RARG RVA.
pose_word_ranges.
pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
-
zstep. zstep. zstep. if_lit. Local Ltac2 Set LiaHints.tbl := fun () => "01E0>1117198066.90 11644661809.7712845283803.8112845283803.9014688241258.7714854759593.8114854759593.9017642112187.8117642112187.9018325627288.8118325627288.9018875403752.8018875403752.8420433961190.7122852259490.8023936172728.8023936172728.8424832007610.7825330349198.8626494647592.7826494647592.8026494647592.8126494647592.8426494647592.9026494647592.9828047646240.6929767269876.9831399144472.8431479571293.8031479571293.8431740050026.7732600174396.7833033815030.7734074473065.8534410679733.8034410679733.843487105106.78 36466374884.7936466374884.9237234173994.7739377301110.7740201484047.8040201484047.9340718019890.8541799641086.7842831019478.8042914771958.8442914771962.7843104399792.8043151311506.8043299102787.8943299102793.8045221239098.7847553572531.7047553572531.855029132897.79 5029132898.83 5033547470.78 50947489494.9852867051505.7753667699702.7753691135086.8054164510851.7854164510851.9256555195377.7759788593898.7762583080755.8062686474143.9863078755697.7763141673385.8163141673385.9063540640753.9764762567087.9865975047387.8065975047387.8466424594827.8166424594827.9066929201389.8467081926311.788378109814.77 8938742845.98 9494287207.77 9494287207.91 9745816336.80 9745816336.84 00000400800<00@00D00H00L00P00T00W00Z00^00b00f00j01301<01C01_01`01a01b01c01d01e01i01l02002402802<02B02F02J02N02R02[02_02c02g02k02o03303703;03?03F03M03S03W03[03_03c03g03k03o04304704;04?04C04L04P04T04X04\04`04i04m05605?05C05G05K05O05X05a05e05i05m06606:06>06G06PS2A0S2ILS2ILS2ILS2ILS2ILS2ILS2HBS2HBS1HS1HS2HBS2HBS2ILS2A0S4SEP32ILS4SEP32ILS2Hi2ILS2A22A04SEP14SEP34SEP42IL2HkSSSSSSS2ILS1HS2ILS2ILS2ILS2ILS4SPLOS2ILS2ILS2H0S2H0S4SEP22ILS2ILS2ILS2ILS2ILS2ILS2ILS2ILS2A2S2H1S2Hi2ILS2Hi2ILS4SPLOS2A2S2ILS2ILS2H1S2ILS2ILS2ILS2ILS2A0S2A0S2ILS2ILS4SEP22ILS2ILS2ILS2ILS2ILS2ILS4SEP12ILS2ILS4SEP42ILS4SEP42ILS2ILS2HBS2ILS2ILS4SEP12ILS4SEP12ILS2A2S2ILS2ILS4SEP42ILS2ILS2ILS4SEP12ILS4SEP12IL".
do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
carve_frame 16%nat ST.
zstep. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep.
zstep. call extenddftf2_spec. 1:{ exact MI. }
rewrite freg_get_same by reflexivity.
zstep. zstep. zstep. zstep. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
release_frame FR ST (bv_unsigned sp).
finish.
{ intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
