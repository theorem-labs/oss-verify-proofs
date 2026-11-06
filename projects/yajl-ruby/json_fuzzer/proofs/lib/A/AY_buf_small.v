(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.

(* [comment removed for export] *)
Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
Ltac ay_statics_close :=
  unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [|split; [|split]]; assumption.
Ltac ay_buf_struct_close HS :=
  split; [unfold buf_cells; rewrite HS; cbn [buf_state_code]; first [assumption | unfold wz; assumption] | split; [assumption| split; assumption]].
Ltac ay_oshadow_close BSeq :=
  unfold oshadow, block_shadow, A_SB; split; [assumption|]; split; [assumption|]; rewrite <- BSeq; assumption.

Theorem aybuf_err_proof : aybuf_err_stmt.
Proof. aceil.
  unfold aybuf_err_stmt. intros P B st lo OA On. intros until m.
  intros STA BUF STR B0 B4 BS OA1 OA2 OA0 OA4 OA5 OA6 MI ST LOC LO SPH EA PSTK PIMG PB PSH. subst a0.
  unfold wz in *. unfold AY_BUF_ERR.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  aceil.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PB, PSH, OA5, OA6. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (block_shadow_bound asegs m _ OA On BS) as BSB. unfold A_SB in BSB.
  unfold oshadow, A_SB in BS. open_shadow BS.
  assert (MU : munch [(lo, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  stepA. stepA.                                       (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso; lia. } (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  assert (B8 : B mod 8 + 4 <= 8) by (clear -CEILB B4; Z.div_mod_to_equations; lia).
  shadow_cases BS B 4.                                (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    do 2 stepA. stepA.                                (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold aybuf_err_rpost. finishA.
    + unfold wz. rewrite sx32_wz by lia. reflexivity.
    + unfold oshadow, block_shadow, A_SB. split; [assumption|]. split; [assumption|]. rewrite <- BSeq. assumption.
    + unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [|split; [|split]]; assumption.
  - (* [comment removed for export] *)
    shadow_slow.
    zstepA.                                           (* [comment removed for export] *)
    do 2 stepA. stepA.                                (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold aybuf_err_rpost. finishA.
    + unfold wz. rewrite sx32_wz by lia. reflexivity.
    + unfold oshadow, block_shadow, A_SB. split; [assumption|]. split; [assumption|]. rewrite <- BSeq. assumption.
    + unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [|split; [|split]]; assumption.
Qed.


Theorem aybuf_len_proof : aybuf_len_stmt.
Proof. aceil.
  unfold aybuf_len_stmt. intros P B D AF lo b. intros until m.
  intros STA (BUF & HD & HL & HU) HS B0 BS SEP1 SEP2 MI ST LOC LO SPH EA PSTK PIMG PB. subst a0.
  unfold wz in *. unfold AY_BUF_LEN. ay_statics_open STA.
  aceil. unfold SIZEOF_BUF in *.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PB, SEP1. unfold AY_IMG_LO, AY_IMG_HI in PIMG. destruct PB as [PB PBS].
  unfold buf_cells in BUF. rewrite HS in BUF. cbn [buf_state_code] in BUF.
  pose proof (block_shadow_bound asegs m _ B 32 BS) as BSB.
  unfold oshadow, A_SB in BS. open_shadow BS.
  assert (MU : munch [(lo, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  stepA. stepA.                                       (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso; lia. } (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  shadow_fast BS B 4.                                 (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  zstepA. if_false.                                   (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast BS (B + 8) 4.                           (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  do 2 stepA. stepA.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold aybuf_len_rpost. finishA.
  + rewrite sx32_wz by lia. reflexivity.
  + ay_buf_struct_close HS.
  + ay_oshadow_close BSeq.
  + ay_statics_close.
Qed.

Theorem aybuf_data_proof : aybuf_data_stmt.
Proof. aceil.
  unfold aybuf_data_stmt. intros P B D AF lo b. intros until m.
  intros STA (BUF & HD & HL & HU) HS B0 BS SEP1 SEP2 MI ST LOC LO SPH EA PSTK PIMG PB. subst a0.
  unfold wz in *. unfold AY_BUF_DATA. ay_statics_open STA.
  aceil. unfold SIZEOF_BUF in *.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PB, SEP1. unfold AY_IMG_LO, AY_IMG_HI in PIMG. destruct PB as [PB PBS].
  unfold buf_cells in BUF. rewrite HS in BUF. cbn [buf_state_code] in BUF.
  pose proof (block_shadow_bound asegs m _ B 32 BS) as BSB.
  unfold oshadow, A_SB in BS. open_shadow BS.
  assert (MU : munch [(lo, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  stepA. stepA.
  zstepA. if_cases K0; zify_cond K0. { exfalso; lia. }
  do 3 stepA.
  shadow_fast BS B 4.
  zstepA.
  zstepA. if_false.
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast BS (B + 16) 8.                          (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  do 2 stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aybuf_data_rpost. finishA.
  + reflexivity.
  + ay_buf_struct_close HS.
  + ay_oshadow_close BSeq.
  + ay_statics_close.
Qed.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Theorem aybuf_clear_proof : aybuf_clear_stmt.
Proof. aceil.
  unfold aybuf_clear_stmt. intros P B D AF lo b. intros until m.
  intros STA BST BD HS BI B0 BS SEP1 SEP2 DSH MI ST LOC LO SPH EA PSTK PIMG PB PD. subst a0.
  destruct BST as (BC & DZ & RL & RU). unfold buf_cells in BC. rewrite HS in BC. cbn [buf_state_code] in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  unfold wz in *. unfold AY_BUF_CLEAR. ay_statics_open STA.
  aceil. unfold SIZEOF_BUF in *.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PB, PD, SEP1, DSH. unfold AY_IMG_LO, AY_IMG_HI in PIMG. destruct PB as [PB PBS].
  pose proof (block_shadow_bound asegs m _ B 32 BS) as BSB.
  unfold oshadow, A_SB in BS. open_shadow BS.
  pose proof (wmono_refl asegs m) as WM.
  destruct BI as (I1 & I2 & I3 & I4 & I5 & I6).
  destruct (yb_data b) as [dp|] eqn:HD; cbn [app];
    [pose proof (munch_refl [(lo, bv_unsigned sp); (B + 8, B + 12); (D, D + 1)] m) as MU
    |pose proof (munch_refl [(lo, bv_unsigned sp); (B + 8, B + 12)] m) as MU].
  - (* [comment removed for export] *)
    assert (D0 : D <> 0) by (intros E; apply DZ in E; congruence).
    specialize (DSH ltac:(congruence)). destruct DSH as (DS & DLO & DHI & DSB).
    specialize (PD ltac:(congruence)). destruct PD as [PD PDS].
    specialize (I5 ltac:(congruence)).
    unfold buf_data in BD. rewrite HD in BD. destruct BD as (UL0 & junk0 & DC).
    pose proof (rw_cells_bound _ _ _ _ DC) as DCB. cbn [cells_size csize Nat.add] in DCB.
    pose proof (rw_cells_merge asegs _ D [] _ [] ltac:(rewrite app_nil_r; exact DC)) as DM. cbn [app] in DM.
    assert (DM' : rw_cells asegs m D [CB (Z.to_nat (yb_len b))
              (cells_bytes [CB (Z.to_nat (yb_used b)) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0);
                           CB (Z.to_nat (yb_len b - yb_used b - 1)) junk0])]).
    { destruct DC as [[Hwf _] _].
      eapply rw_cells_recast; [exact DM| | reflexivity|].
      - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite (cells_bytes_length _ Hwf). cbn [cells_size csize]. lia.
      - cbn [cells_size csize]. lia. }
    clear DM DC.
    pose proof (block_shadow_bound asegs m _ D (yb_len b) DS) as DSB0.
    unfold oshadow, A_SB in DS. open_shadow DS.
    carve_frame 16%nat ST.
    stepA. stepA.
    zstepA. if_cases K0; zify_cond K0. { exfalso; lia. }
    do 3 stepA.
    shadow_fast BS B 4.                               (* [comment removed for export] *)
    zstepA. zstepA. if_false.                         (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    shadow_fast BS (B + 8) 4.                         (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    shadow_fast BS (B + 16) 8.                        (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1. { kill K1. }   (* [comment removed for export] *)
    shadow_cases DS D 1.                              (* [comment removed for export] *)
    2: shadow_slow.
    all: match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
           pose proof (rw_cells_CB_store_ok asegs mx D _ _ 1%nat DM' ltac:(lia)) as SOK end.
    all: stepA.                                       (* [comment removed for export] *)
    all: match type of DM' with rw_cells _ ?mx _ _ =>
           pose proof (rw_cells_CB_prefix_write asegs mx D _ _ (le1 (Z_to_bv 64 0)) DM' ltac:(cbn; lia)) as DC' end.
    all: clear DM'; store_done.
    all: stepA; stepA; stepA.
    all: release_frame FR ST (bv_unsigned sp).
    all: unfold aybuf_clear_rpost; rewrite HD; cbn [app]; finishA.
    all: try (split; [| split; [cbn [yb_data buf_cleared]; rewrite HD; exact DZ| cbn; lia]]; unfold buf_cells, buf_cleared; cbn; exact BC).
    all: try ay_oshadow_close BSeq.
    all: try ay_statics_close.
    all: try (intros _; unfold oshadow, block_shadow, A_SB; split; [assumption|]; split; [assumption|]; rewrite <- DSeq; assumption).
    all: unfold buf_data, buf_cleared; cbn [yb_data yb_used yb_len yb_bytes]; rewrite HD; split; [lia|];
      destruct DC' as [[Hwf' HB'] HW']; cbn [cells_wf cell_wf] in Hwf'; destruct Hwf' as (_ & Hl2 & _);
      eexists; (split; [split|]);
      [ cbn [cells_wf cell_wf]; split; [reflexivity|]; split; [exact I|]; split; [|exact I]; rewrite Hl2, length_le1; lia
      | revert HB'; rewrite !length_le1; cbn [cells_bytes cbytes zbytes map app]; intros HB';
        replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in HB' by reflexivity; exact HB'
      | revert HW'; rewrite !length_le1; cbn [cells_size csize]; intros HW';
        replace (Z.to_nat 0 + (1 + (Z.to_nat (yb_len b - 0 - 1) + 0)))%nat with (1 + (Z.to_nat (yb_len b) - 1 + 0))%nat by lia;
        exact HW' ].
  - (* [comment removed for export] *)
    assert (D0 : D = 0) by (apply DZ; reflexivity). subst D.
    carve_frame 16%nat ST.
    stepA. stepA.
    zstepA. if_cases K0; zify_cond K0. { exfalso; lia. }
    do 3 stepA.
    shadow_fast BS B 4.
    zstepA. zstepA. if_false.
    zstepA.
    shadow_fast BS (B + 8) 4.
    zstepA.
    zstepA.
    shadow_fast BS (B + 16) 8.
    zstepA.
    zstepA. if_true.                                  (* [comment removed for export] *)
    stepA. stepA. stepA.
    release_frame FR ST (bv_unsigned sp).
    unfold aybuf_clear_rpost. rewrite HD. cbn [app]. finishA.
    + split; [| split; [cbn [yb_data buf_cleared]; rewrite HD; exact DZ| cbn; lia]]. unfold buf_cells, buf_cleared. cbn. exact BC.
    + unfold buf_data, buf_cleared. cbn [yb_data]. rewrite HD. exact I.
    + ay_oshadow_close BSeq.
    + intros NE. exfalso. apply NE. reflexivity.
    + ay_statics_close.
Qed.
End W.
End RC__1.
