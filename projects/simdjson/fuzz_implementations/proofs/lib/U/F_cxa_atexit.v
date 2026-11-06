(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Exit.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Definition RCXA_ATEXIT : Z := 0xc4b08.
Definition RLIBC_HEAD : Z := 0x1157d8.

Definition cxa_pre (m : word -> option byte) (k : Z) (f0 a0v : word) : Prop :=
  rw_cells usegs m AEX [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 k)]
  /\ rw_cells usegs m (AEX + 16) [C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else AEX + 24))]
  /\ rw_cells usegs m (AEX + 32 + 8 * k) [C8 f0]
  /\ rw_cells usegs m (AEX + 288 + 8 * k) [C8 a0v].

Definition cxa_atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo k func arg : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX + 8, AEX + 24); (AEX + 32 + 8 * k, AEX + 40 + 8 * k); (AEX + 288 + 8 * k, AEX + 296 + 8 * k)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (AEX + 4) [C4 z64; C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells usegs m' (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24))]
    /\ rw_cells usegs m' (AEX + 32 + 8 * k) [C8 (Z_to_bv 64 func)]
    /\ rw_cells usegs m' (AEX + 288 + 8 * k) [C8 (Z_to_bv 64 arg)].

Definition cxa_atexit_stmt (k : Z) : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func arg : Z) (f0 a0v : word) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  cxa_pre m k f0 a0v ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 func -> a1 = Z_to_bv 64 arg -> (0 <= func < 2^64)%Z -> (0 <= arg < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (GLOBALS_TOP <= lo)%Z ->
  evt usegs (cxa_atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo k func arg m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RCXA_ATEXIT) fc None m (seg_rom usegs)).

Ltac norm_addr H := lazymatch type of H with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in H end.

Lemma cxa_atexit_spec0 : cxa_atexit_stmt 0.
Proof.
  unfold cxa_atexit_stmt, cxa_pre.
  intros until tm1. intros ST LCH (X1 & X2 & X3 & X4 & X5) MI -> -> Hf Ha LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RCXA_ATEXIT, AEX, RLIBC_HEAD, GLOBALS_TOP in *. cbn [Z.eqb] in X3. norm_addr X2. norm_addr X3. norm_addr X4. norm_addr X5.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x115598, 0x1155a8); (0x1155b0, 0x1155b8); (0x1156b0, 0x1156b8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0xd66c0%Z. lock_ret.
  lstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep. lstep. if_false.
  lstep. lstep. if_false. lstep. lstep.
  lstep.
  try match goal with |- context [sx32 (Z_to_bv 64 ?z)] => replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 z : word) by (vm_compute; reflexivity) end.
  try (replace (sx32 z64) with z64 by (vm_compute; reflexivity)).
  lstep. lstep. if_true.
  steps_to 0xc4ba4%Z.
  lstep. astep. unlock_ret.
  steps_to 0xc4bcc%Z.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold cxa_atexit_post. sys_finish.
Qed.

Lemma cxa_atexit_spec2 : cxa_atexit_stmt 2.
Proof.
  unfold cxa_atexit_stmt, cxa_pre.
  intros until tm1. intros ST LCH (X1 & X2 & X3 & X4 & X5) MI -> -> Hf Ha LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RCXA_ATEXIT, AEX, RLIBC_HEAD, GLOBALS_TOP in *. cbn [Z.eqb] in X3. norm_addr X2. norm_addr X3. norm_addr X4. norm_addr X5.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x115598, 0x1155a8); (0x1155c0, 0x1155c8); (0x1156c0, 0x1156c8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0xd66c0%Z. lock_ret.
  lstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep. lstep. if_false.
  lstep. lstep. if_true.
  lstep.
  try match goal with |- context [sx32 (Z_to_bv 64 ?z)] => replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 z : word) by (vm_compute; reflexivity) end.
  try (replace (sx32 z64) with z64 by (vm_compute; reflexivity)).
  lstep. lstep. if_true.
  steps_to 0xc4ba4%Z.
  lstep. astep. unlock_ret.
  steps_to 0xc4bcc%Z.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold cxa_atexit_post. sys_finish.
Qed.

Definition cxa_atexit_tbl2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX + 8, AEX + 24); (AEX + 48, AEX + 56); (AEX + 304, AEX + 312)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ aex_tbl m' 3.

Lemma cxa_atexit_tbl2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  aex_tbl m 2 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 X_VECDTOR -> a1 = Z_to_bv 64 AEX_VEC_OBJ ->
  (lo <= bv_unsigned sp - 48)%Z -> (GLOBALS_TOP <= lo)%Z ->
  evt usegs (cxa_atexit_tbl2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RCXA_ATEXIT) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH (X1 & X2 & X3 & X4) MI Ha0 Ha1 LO LOLO.
  unfold X_VECDTOR, AEX_VEC_OBJ in Ha0, Ha1.
  unfold GLOBALS_TOP in *. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

  lazymatch type of X3 with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: nil) =>
    pose proof (proj1 (rw_cells_app usegs m A [c1] [c2; c3; c4; c5]) X3) as [XH XR];
    pose proof (proj1 (rw_cells_app usegs m _ [c2; c3; c4] [c5]) XR) as [XM XF] end.
  lazymatch type of X4 with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: nil) =>
    pose proof (proj1 (rw_cells_app usegs m A [c1; c2] [c3]) X4) as [YA YB] end.
  cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Z.add Pos.add] in XM, XF, YB.
  match type of XM with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in XM end.
  match type of XF with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in XF end.
  match type of YB with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in YB end.
  eapply evt_mono.
  { eapply (cxa_atexit_spec2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo X_VECDTOR AEX_VEC_OBJ _ _ cdt thr sec tm1);
      [ exact ST | exact LCH | | exact MI | exact Ha0 | exact Ha1 | unfold X_VECDTOR; lia | unfold AEX_VEC_OBJ; lia | exact LO | exact LOLO ].
    unfold cxa_pre. split; [exact X1|]. split; [exact X2|]. split; [cbn [Z.eqb]; exact XH|].
    unfold AEX. split; [lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v; exact XF end
                      | lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v; exact YB end]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & P2 & PH & PF & PA).
  unfold cxa_atexit_tbl2_post. do 15 eexists. split; [reflexivity|].
  unfold AEX in *.
  repeat match goal with H : rw_cells _ _ (?a + ?b)%Z _ |- _ => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in H end.
  repeat match type of MU with context [(?a + ?b)%Z] => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in MU end.
  split. { lazymatch goal with |- munch ?W _ _ => let v := eval cbn in W in idtac end.
           eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside fst snd]. intros; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].

  assert (X1' : rw_cells usegs m' 0x115590 [C1 (Z_to_bv 8 0)]) by (eapply (rw_cells_transport usegs _ m m'); [exact X1| exact MU| exact WM| cbn; lia]).
  assert (XM' : rw_cells usegs m' 0x1155a8 [C8 z64; C8 (Z_to_bv 64 X_IOSDTOR); C8 (Z_to_bv 64 (if (2 <=? 1)%Z then 0 else RAEX_CALL))])
    by (eapply (rw_cells_transport usegs _ m m'); [exact XM| exact MU| exact WM| cbn; lia]).
  assert (YA' : rw_cells usegs m' 0x1156b0 [C8 (Z_to_bv 64 AEX_IOS); C8 (Z_to_bv 64 (if (2 <=? 1)%Z then 0 else RAEF_GUARD))])
    by (eapply (rw_cells_transport usegs _ m m'); [exact YA| exact MU| exact WM| cbn; lia]).
  unfold aex_tbl, AEX. cbn [Z.leb].
  split; [exact X1'|]. split; [exact P2|].
  split.
  { lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end.
    apply (proj2 (rw_cells_app usegs m' 0x1155a0 [_] [_; _; _; _])). split; [exact PH|].
    apply (proj2 (rw_cells_app usegs m' _ [_; _; _] [_])). split; [cbn; exact XM'| cbn; exact PF]. }
  lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v end.
  apply (proj2 (rw_cells_app usegs m' 0x1156b0 [_; _] [_])). split; [cbn [Z.leb] in YA'; exact YA'| cbn; exact PA].
Qed.
