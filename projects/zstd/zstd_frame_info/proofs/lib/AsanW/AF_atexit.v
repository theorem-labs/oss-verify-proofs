(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg F_syscalls MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APATEXIT : Z := 0x88838.       (* [comment removed for export] *)
Definition APATX : Z := 0x5f3e60.         (* [comment removed for export] *)
Definition APATX_CALLFN : Z := 0x888fc.   (* [comment removed for export] *)
Definition APNEED_LOCKS : Z := 0x5f40a3.  (* [comment removed for export] *)
Definition ACOV_HOOK : Z := 0x6f1f0.      (* [comment removed for export] *)
Definition ACOV_FLAG : Z := 0x132d20.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition APEXIT_GUARD : Z := 0x7fbb8.   (* [comment removed for export] *)
Definition APAEF_INCB : Z := 0x5d34d4.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atx_cellsA (slot f1 a1 : Z) (m : mem) : Prop :=
  rw_cells asegs m 0x5f3e60 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x5f3e64 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x5f3e68 [C4 (Z_to_bv 64 slot)]
  /\ rw_cells asegs m 0x5f3e70 [C8 (Z_to_bv 64 0x5f3e78)]
  /\ rw_cells asegs m 0x5f3e78 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x5f3e80 [C8 (Z_to_bv 64 APATX_CALLFN)]
  /\ rw_cells asegs m 0x5f3f80 [C8 (Z_to_bv 64 ACOV_HOOK)]
  /\ rw_cells asegs m 0x5f3e88 [C8 (Z_to_bv 64 f1)]
  /\ rw_cells asegs m 0x5f3f88 [C8 (Z_to_bv 64 a1)].

(* [comment removed for export] *)
Definition atx_stateA (reg : bool) (m : mem) : Prop :=
  atx_cellsA (if reg then 2 else 1) (if reg then APATX_CALLFN else 0) (if reg then APEXIT_GUARD else 0) m
  /\ rw_cells asegs m APAEF_INCB [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m ACOV_FLAG [C1 (Z_to_bv 8 0)].

Definition atx_addrA (a : Z) : Prop :=
  (0x5f3e60 <= a < 0x5f3e61)%Z \/ (0x5f3e64 <= a < 0x5f3e6c)%Z \/ (0x5f3e70 <= a < 0x5f3e90)%Z \/ (0x5f3f80 <= a < 0x5f3f90)%Z.
Definition atx_state_addrA (a : Z) : Prop := atx_addrA a \/ (0x5d34d4 <= a < 0x5d34d5)%Z \/ (0x132d20 <= a < 0x132d21)%Z.

Lemma atx_cellsA_agree : forall (P : Z -> Prop) m m' slot f1 a1,
  magree asegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cellsA slot f1 a1 m -> atx_cellsA slot f1 a1 m'.
Proof.
  intros P m m' slot f1 a1 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold atx_cellsA.
  Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addrA in *; cbn in Ha; lia].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>12476628164.19000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
  split; [agx AG HP A5|]. split; [agx AG HP A6|]. split; [agx AG HP A7|]. split; [agx AG HP A8| agx AG HP A9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_stateA_agree : forall (P : Z -> Prop) m m' reg,
  magree asegs P m m' -> (forall a, atx_state_addrA a -> P a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof.
  intros P m m' reg AG HP (AX & CB & CF). split; [| split].
  - eapply atx_cellsA_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>12455633568.1167731802912.11000004008S2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; left; unfold APAEF_INCB in *; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact CF| intros a Ha; apply HP; right; right; unfold ACOV_FLAG in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_stateA_munch : forall W m m' reg,
  munch W m m' -> wmono asegs m m' -> (forall a, atx_state_addrA a -> outside W a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof. intros W m m' reg MU WM HW. apply (atx_stateA_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition patexit_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo g : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ atx_cellsA 2 APATX_CALLFN g m'.

#[using="Type"] Lemma patexit_specA : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo g : Z),
  stk asegs m lo (bv_unsigned sp) ->
  atx_cellsA 1 0 0 m ->
  rw_cells asegs m APNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (patexit_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APATEXIT) fc None m (seg_rom asegs)).
Proof.
  intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) NL MI -> Hg LO KH RSTK RIMG.
  unfold APNEED_LOCKS, APATEXIT, APATX_CALLFN, ACOV_HOOK in *. pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01n0>11875767022.7012389690253.7214118943342.6915025058286.6715442153454.6716478086458.7417776320431.681800609155.69 18992537934.6919622476014.7020492762170.7221459134830.6921821697742.6922389541692.6722856607214.6922883414581.7423433232781.6923847006446.7024638473347.6924638473347.7025413936570.7425792608750.6726708505146.7427133822446.692746357306.74 27728284730.7427907070492.6128163884602.7228417259964.6928568521786.6929181207093.7229531591534.6929870281326.6930401015406.7030543425082.6931378308326.6031856720366.6732194692666.6932440122478.6932649475514.7232716547054.6933680001082.7033781268846.6933944158778.7234110508400.6934430152252.7034581665338.7435265982326.6735811162350.7035930198638.6936115622446.6936115622447.6836936768494.6937423617594.7438315871290.7438567244270.6738782755822.6939093924078.7040457739452.6940871484270.694109383610.69 41540547438.6941834437230.6942009944634.7243000880110.6943059266230.584365912122.69 43967450992.7243987951406.6943988483203.6743988483203.6844466451258.6944762256494.6945221239098.6945848756903.6746468661564.6947346188144.7448909296622.6949649769127.705087518190.69 51340875834.6951711223320.6052105090727.6952198366190.6952567164907.6752567164907.6952567164907.7052567164907.7252567164907.7452662526030.7052780046574.7053767577775.6854243526019.6954755617850.6954844324854.67563227834.69  56327961070.6756375174714.7256887963598.6957000382702.7057264760378.7257745675194.6958057019758.6958068748346.6960109265978.7260797519086.6960858483367.6962682870638.6962826138350.7063235321900.6663235321900.6763305555623.6963803339322.746491058798.69 64997134979.7065458892654.6765750190926.6766400913390.676747295797.69 7720336238.69 8054831726.69 8172837742.69 8442133389.74 8583720762.67 8967238126.67 9242432826.72 00000800900A00I00Q00R00V00W00_00g00h01001801<01D01L01M01U01V01W01X01`01a01i01j01k01o02002402502=02E02M02U02V02W02_02`02h02i03103603>03?03@03D03E03F03N03V03Z03^03f03g03h04004804@04D04L04M04U04]04^04f04j04k04l05005105205305;05@05A05E05F05N05O05W05X05Y05Z05b05c05d05e05f05g05o06706;06<06=06>06C06K06L06T06\06]06b06j06k06l07407507=07E07I07M07N07O07W07X07`07h08008808@08H08P08Q08V08^08_S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SS2LOSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'SS2LO3KH'SSSS2LO3KH'SS2LO3KH'SSS2LOSS2HBSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'SS2LO3KH'S3RSPS2LO3KH'SSS2HBSSS2LO3KH'S2LO3KH'S2LOS2LOS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LOSSS2LOSSSS2LO3KH'S3RSPSS2HBSS2LO3KH'SS2LO3KH'SSSS2LO3KH'SSSSSS2LO3KH'S2LO3KH'S2LOSSSS3RSPS2LO3KH'SS2LO3KH'S2LO3KH'SS3RSPS2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'S2LOS2LOSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS3RSPS2LO3KH'S".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x92a34%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  steps_to 0x88868%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. if_false.
  (* [comment removed for export] *)
  hstep. hstep. if_true.
  (* [comment removed for export] *)
  hstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. hstep. if_true.
  (* [comment removed for export] *)
  steps_to 0x92cbc%Z.
  (* [comment removed for export] *)
  hstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
  hstep. if_false. hstep.
  (* [comment removed for export] *)
  steps_to 0x888f4%Z.
  release_frame FR ST (bv_unsigned sp). astep. astep.
  unfold patexit_postA, atx_cellsA, APATX_CALLFN, ACOV_HOOK. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
