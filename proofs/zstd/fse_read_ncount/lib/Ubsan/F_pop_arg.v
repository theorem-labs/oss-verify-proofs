(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memset F_extenddftf2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
bytes_at usegs m VA (u64s slots).
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
Ft (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
/\ rw_cells usegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
/\ rw_cells usegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
/\ va_area m' VA slots
/\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).
Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.
Lemma va_read8 : forall m VA slots (i : Z) w a,
bytes_at usegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes usegs m a 8 = Some (le8 w).
Proof.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25273904528.1446081068896.1458870951973.1461555382922.1400000:00D00Q00[S4Hlen3HluS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read usegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma va_read4 : forall m VA slots (i : Z) w a,
bytes_at usegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes usegs m a 4 = Some (le4 w).
Proof.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
Local Ltac2 Set LiaHints.tbl := fun () => "0030>46081068896.1458870951973.1461555382922.1400000:00G00QS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read usegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
rewrite firstn4_le8. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=49631155169.5000003S1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.
Lemma pop_arg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
rw_cells usegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
rw_cells usegs m (bv_unsigned a0) [C8 x; C8 y] ->
stk usegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
mem_inv usegs m ->
a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
(16 <= bv_unsigned sp)%Z ->
(bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
evt usegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x18750) fc None m (seg_rom usegs)).
Proof.
intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
pose_word_ranges.
pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
-
zstep. zstep. zstep. if_lit. Local Ltac2 Set LiaHints.tbl := fun () => "0190>1117198066.83 12845283803.7412845283803.8314854759593.7414854759593.8317642112187.7417642112187.8318325627288.7418325627288.8318875403752.7318875403752.77190241905.70  20433961190.6420719263210.7022852259490.7323936172728.7323936172728.7725330349198.7926494647592.7126494647592.7326494647592.7426494647592.7726494647592.8326494647592.9128047646240.6229767269876.9131399144472.7731479571293.7331479571293.7732600174396.7134074473065.7834410679733.7334410679733.773487105106.71 3931000625.70 40201484047.7340201484047.8641799641086.7142831019478.7343104399792.7343151311506.7344337469802.7045221239098.7147553572531.6347553572531.7848874195697.705033547470.71 50947489494.9153691135086.7354164510851.7154164510851.8558663411441.706000815094.70 61552360810.7061996751410.7862583080755.7362686474143.9163141673385.7463141673385.8363706824566.7064762567087.9165217526774.7065975047387.7365975047387.7766424594827.7466424594827.8366883533610.7066929201389.7767081926311.718420494966.70 8938742845.91 9745816336.73 9745816336.77 00000400800<00@00D00H00L00O00R00V00Z00^00b00f00j01301<01C01D01E01F01G01H01I01M01P01T01X01\01b01f01j01n02702;02?02C02G02K02Q02U02Y02]02a02e02i02m03103:03>03B03F03J03N03R03V03\03e03n04204604:04>04B04H04N04R04V04Z04^04g04m053S2A0S2ILS2ILS2ILS2ILS2HBS2HBS1HS1HS2HBS2HBS2ILS2ILS2ILS2A0S4SEP32ILS4SEP32ILS2IL2HkSSSSSSS2ILS1HS2ILS2ILS2ILS4SPLOS2ILS2H0S2H0S4SEP22ILS2ILS2ILS2ILS2A2S2H1S4SPLOS2A2S2ILS2H1S2ILS2ILS2ILS2A0S2A0S4SEP22ILS2ILS2ILS2ILS2ILS2ILS2ILS2ILS4SEP1S4SEP42ILS4SEP42ILS2ILS2HBS2ILS2ILS2ILS4SEP1S4SEP1S2ILS2A2S2ILS2ILS4SEP42ILS4SEP1S4SEP1".
do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 7 zstep.
carve_frame 16%nat ST.
zstep. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep.
zstep. call extenddftf2_spec. 1:{ exact MI. }
cbv delta [usegs] in *. fold usegs in *.
rewrite freg_get_same by reflexivity.
zstep. zstep. zstep. zstep. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
release_frame FR ST (bv_unsigned sp).
finish.
{ intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
