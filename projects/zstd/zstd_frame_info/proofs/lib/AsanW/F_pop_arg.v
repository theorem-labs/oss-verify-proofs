(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_extenddftf2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition pop_arg_entry := 0x8f984%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at asegs m VA (u64s slots).

(* [comment removed for export] *)
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
             Ft (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells asegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells asegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

#[using="Type"] Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

#[using="Type"] Lemma va_read8 : forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>25273904528.1546081068896.1558870951973.1561555382922.1500000:00D00Q00[S4Hlen3HluS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma va_read4 : forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>46081068896.1558870951973.1561555382922.1500000:00G00QS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
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

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma pop_arg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells asegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG (bv_unsigned sp - 16) 16 -> rng RNG (bv_unsigned a2) 8 -> rng RNG (bv_unsigned a0) 16 ->
  rng RNG VA (8 * Z.of_nat (length slots)) ->
  evtF asegs RNG (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8f984) fc None m (seg_rom asegs)).
Proof.
  intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4 RIMG RFR RAP RARG RVA.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. Local Ltac2 Set LiaHints.tbl := fun () => "01E0>1117198066.90 11644661809.7712845283803.8112845283803.9014688241258.7714854759593.8114854759593.9017642112187.8117642112187.9018325627288.8118325627288.9018875403752.8018875403752.8420433961190.7122794301302.7722852259490.8023936172728.8023936172728.8424832007610.7825330349198.8626494647592.7826494647592.8026494647592.8126494647592.8426494647592.9026494647592.9828047646240.6928290880502.7729767269876.9831399144472.8431479571293.8031479571293.8431740050026.7732600174396.7833847179382.7734074473065.8534410679733.8034410679733.843487105106.78 36466374884.7936466374884.9237234173994.7740201484047.8040201484047.9341799641086.7841983118326.7742831019478.8042914771958.8442914771962.7843104399792.8043151311506.8043299102787.8943299102793.8045221239098.7847553572531.7047553572531.855029132897.79 5029132898.83 5033547470.78 50947489494.9851747315378.8552867051505.7753691135086.8054164510851.7854164510851.9256555195377.7759788593898.7762583080755.8062686474143.9863078755697.7763141673385.8163141673385.9063540640753.9764762567087.9865975047387.8065975047387.8466424594827.8166424594827.9066929201389.8467081926311.788938742845.98 9494287207.77 9494287207.91 9745816336.80 9745816336.84 00000400800<00@00D00H00L00P00T00W00Z00^00b00f00j00n01701@01G01c01d01e01f01g01h01i01m02102402802<02@02D02J02N02R02V02Z02c02g02k02o03303703;03?03C03J03Q03W03[03_03c03g03k03o04304704;04?04C04G04P04T04X04\04`04d04m05105:05C05G05K05O05S05\05e05i05m06606:06>06G06PS2A0S2ILS2ILS2ILS2ILS2ILS2ILS2HBS2HBS1HS1HS2HBS2HBS2ILS2ILS2A0S4SEP32ILS4SEP32ILS2Hi2ILS2A22A04SEP14SEP34SEP42IL2HkSSSSSSS2ILS2ILS1HS2ILS2ILS2ILS2ILS4SPLOS2ILS2ILS2H0S2H0S4SEP22ILS2ILS2ILS2ILS2ILS2ILS2A2S2ILS2H1S2Hi2ILS2Hi2ILS4SPLOS2A2S2ILS2ILS2H1S2ILS2ILS2ILS2ILS2A0S2A0S2ILS2ILS4SEP22ILS2ILS2ILS2ILS2ILS2ILS4SEP12ILS2ILS4SEP42ILS4SEP42ILS2ILS2HBS2ILS2ILS4SEP12ILS4SEP12ILS2A2S2ILS4SEP42ILS2ILS2ILS4SEP12ILS4SEP12IL".
do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
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
