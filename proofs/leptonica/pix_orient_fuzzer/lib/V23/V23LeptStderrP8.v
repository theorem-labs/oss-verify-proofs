(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs PFLib PFSpecLib WalksLib LeptDefs LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23PFBase V23PFSpec V23LeptStderr V23LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition LU16P8 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x636a4; SSP.ls_handler_cell := 0x127c68; SSP.ls_devnull := 0x6366c;
     SSP.ls_canary_got := 0x126c00; SSP.ls_canary := 0x158440;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x123000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x159000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1b5e0; 0x113ab; 0x128e8; 0x113e5; 0x1e6fe; 0x121b5];
     SSP.ls_fmts2 := [0x1e3b4];
     SSP.ls_sev_got := 0x126a70; SSP.ls_sev := 0x127c60 |}.

Lemma LU16P8_ok1 : ls_ok1 LU16P8 = true.
Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1P8 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16P8).
Proof. exact (lept_stderr_s1_contract LU16P8 LU16P8_ok1). Qed.
End WithFP.

Section StderrP8.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma lept_stderr1P8_W : forall C A m md regs (s fmt a1 : Z) kf k1 (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + LSF <= s -> s <= c_top C ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 fmt -> getr regs 11 = Z_to_bv 64 a1 ->
  In fmt (SSP.ls_fmts1 LU16P8) -> str16 fmt kf -> str16 a1 k1 ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - LSF <= u a < s) -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x636a4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s fmt a1 kf k1 ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 Hin Sf S1 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro ll_lg ll_ag ll_errno ll_hcell LLU16] in *. unfold LSF in *.
  destruct (canary_any m) as (cv & Hcv & Ccan).
  pose proof Sf as (_ & Kf & Af & Bf). pose proof S1 as (_ & K1 & A1 & B1).
  assert (Wf : kf + 1 <= SSP.rostr_win fmt kf).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (fmt + kf) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fmt + kf) 8 ltac:(lia)). lia. }
  assert (W1 : k1 + 1 <= SSP.rostr_win a1 k1).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a1 + k1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a1 + k1) 8 ltac:(lia)). lia. }
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_lept_stderr_s1 LU16P8) [fmt; a1; 0x6366c; 0x158440; cv] regs m).
  { unfold SSP.spec_lept_stderr_s1. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    cbn [SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo SSP.ls_img_hi
         SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame LU16P8].
    rewrite H1, H2, H10, H11. rewrite !u_Z2bv by lia.
    split; [|split; [|split; [|exact Hret]]].
    - split; [split; [reflexivity | lia]|].
      split; [exact Hin|].
      split; [exists kf; split; [lia | exact (W_rostr C A m md fmt kf HW Sf)]|].
      split; [split; [reflexivity | lia]|].
      split; [exists k1; split; [lia | exact (W_rostr C A m md a1 k1 HW S1)]|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_hdl16 C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_can_got C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Ccan]]]|].
      split; [intros i Hi; exact (W_img16 C A m md i HW Hi)|].
      split; [split; [lia | exact Hs16]|].
      split; [lia | exact I].
    - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [|exact I].
      apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia].
    - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; try lia. all: exact I.
  }
  pose proof (lept_stderr_s1P8 (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [fmt; a1; 0x6366c; 0x158440; cv] regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
  unfold SSP.spec_lept_stderr_s1 in POST. SSP.spec_unfold_in POST. destruct POST as (KEPT & _ & FRMx & GR & _).
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_lept_stderr_s1 SSP.ls_entry SSP.ls_frame LU16P8] in RUN, FRMx.
  rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
  assert (OUT : forall a : word, ~ (s - 3376 <= u a < s) -> M' a = m a).
  { intros a Ha. apply FRMx. split; [lia | exact I]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity) end.
    exact RUN. }
  apply HK.
  - apply (W_mod_local C A m M' md CK HW).
    + intros a Ha. left. unfold win. destruct (Z_lt_ge_dec (u a) (s - 3376)); [exfalso; apply Ha; apply OUT; lia|].
      destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply Ha; apply OUT; lia.
    + exact GR.
    + intros a Ha. destruct (Z_lt_ge_dec (u a) (s - 3376)); [rewrite OUT in Ha by lia; exact Ha|].
      destruct (Z_lt_ge_dec (u a) s); [|rewrite OUT in Ha by lia; exact Ha].
      apply (w_win _ _ _ _ HW). unfold win. lia.
  - exact OUT.
  - exact GR.
  - exact (cs_kept_of_list regs R' KEPT).
Qed.

End StderrP8.
