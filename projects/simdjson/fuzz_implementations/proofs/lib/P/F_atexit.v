(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Exit.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := Image.psegs.

Ltac norm_addr H := lazymatch type of H with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in H end.

Definition RATEXIT : Z := 0xb972c.
Definition AEX1 : Z := 0x109de0.

Definition atexit1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (func : Z) (f0 a0v : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX1 + 8, AEX1 + 12); (AEX1 + 40, AEX1 + 48); (AEX1 + 296, AEX1 + 304)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (AEX1 + 4) [C4 z64; C4 (Z_to_bv 64 2)]
    /\ rw_cells psegs m' (AEX1 + 16) [C8 (Z_to_bv 64 (AEX1 + 24)); C8 z64; C8 f0; C8 (Z_to_bv 64 RAEX_CALL)]
    /\ rw_cells psegs m' (AEX1 + 288) [C8 a0v; C8 (Z_to_bv 64 func)].

Lemma atexit1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (f0 a0v : word) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells psegs m AEX1 [C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m (AEX1 + 4) [C4 z64; C4 (Z_to_bv 64 1)] ->
  rw_cells psegs m (AEX1 + 16) [C8 (Z_to_bv 64 (AEX1 + 24)); C8 z64; C8 f0; C8 z64] ->
  rw_cells psegs m (AEX1 + 288) [C8 a0v; C8 z64] ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 func -> (0 <= func < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x10b000 <= lo)%Z ->
  evt psegs (atexit1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func f0 a0v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATEXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST LCH X1 X2 X3 X4 MI -> Hf LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RATEXIT, RAEX_CALL, AEX1 in *.
  norm_addr X2. norm_addr X3. norm_addr X4.
  match type of X3 with context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v in X3 end.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de8, 0x109dec); (0x109e08, 0x109e10); (0x109f08, 0x109f10)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0xcb21c%Z. lock_ret.
  lstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep. lstep. if_false.
  lstep. lstep. if_true.
  lstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  lstep. lstep. if_true.
  steps_to 0xb97c8%Z.
  lstep. astep. unlock_ret.
  steps_to 0xb97ec%Z.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold atexit1_post, AEX1, RAEX_CALL. cbn [Z.add Pos.add].
  sys_finish.
Time Qed.

Definition atexit_tbl1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX1 + 8, AEX1 + 12); (AEX1 + 40, AEX1 + 48); (AEX1 + 296, AEX1 + 304)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ aex_tbl m' 2.

Lemma atexit_tbl1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  aex_tbl m 1 ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 RAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x10b000 <= lo)%Z ->
  evt psegs (atexit_tbl1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATEXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST LCH (X1 & X2 & X3 & X4) MI Ha0 LO LOLO.
  unfold RAEF_GUARD in Ha0.
  unfold GLOBALS_TOP in *. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

  lazymatch type of X3 with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: nil) =>
    pose proof (proj1 (rw_cells_app psegs m A [c1; c2; c3; c4] [c5]) X3) as [XL XF2] end.
  lazymatch type of X4 with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: nil) =>
    pose proof (proj1 (rw_cells_app psegs m A [c1; c2] [c3]) X4) as [YL YA2] end.
  cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Z.add Pos.add] in XF2, YA2.
  unfold AEX in *. cbn [Z.leb] in XL, YL, XF2, YA2.
  repeat match goal with H : rw_cells _ _ (?a + ?b)%Z _ |- _ => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in H end.
  match type of XL with context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v in XL end.
  eapply evt_mono.
  { eapply (atexit1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo RAEF_GUARD (Z_to_bv 64 X_IOSDTOR) (Z_to_bv 64 AEX_IOS) cdt thr sec tm1);
      [ exact ST | exact LCH | exact X1 | unfold AEX1; exact X2 | | | exact MI | exact Ha0 | unfold RAEF_GUARD; lia | exact LO | exact LOLO ].
    - unfold AEX1. lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end.
      match goal with |- context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v end. exact XL.
    - unfold AEX1. lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end. exact YL. }
  cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & P2 & PH & PA).
  unfold atexit_tbl1_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  unfold AEX1 in *.
  repeat match goal with H : rw_cells _ _ (?a + ?b)%Z _ |- _ => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in H end.
  repeat match type of MU with context [(?a + ?b)%Z] => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in MU end.
  match type of PH with context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v in PH end.
  assert (X1' : rw_cells psegs m' 0x109de0 [C1 (Z_to_bv 8 0)]) by (eapply (rw_cells_transport psegs _ m m'); [exact X1| exact MU| exact WM| cbn; lia]).
  assert (XF2' : rw_cells psegs m' 0x109e10 [C8 (Z_to_bv 64 0)]) by (eapply (rw_cells_transport psegs _ m m'); [exact XF2| exact MU| exact WM| cbn; lia]).
  assert (YA2' : rw_cells psegs m' 0x109f10 [C8 (Z_to_bv 64 0)]) by (eapply (rw_cells_transport psegs _ m m'); [exact YA2| exact MU| exact WM| cbn; lia]).
  unfold aex_tbl, AEX. cbn [Z.leb].
  split; [exact X1'|]. split; [exact P2|].
  split.
  { lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end.
    match goal with |- context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v end.
    apply (proj2 (rw_cells_app psegs m' 0x109df0 [_; _; _; _] [_])). split; [exact PH| cbn; exact XF2']. }
  lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end.
  apply (proj2 (rw_cells_app psegs m' 0x109f00 [_; _] [_])). split; [exact PA| cbn; exact YA2'].
Qed.
