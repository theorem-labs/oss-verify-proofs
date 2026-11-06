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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
Ltac ay_statics_close :=
  unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [|split; [|split]]; assumption.
Ltac ay_oshadow_close BSeq :=
  unfold oshadow, block_shadow, A_SB; split; [assumption|]; split; [assumption|]; rewrite <- BSeq; assumption.

(* [comment removed for export] *)
Theorem aycb_null_proof : aycb_null_stmt.
Proof. aceil. unfold aycb_null_stmt. intros P. intros until m. intros MI. unfold AY_CB_NULL, wz.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. stepA. stepA. unfold aycb_null_rpost. finishA; reflexivity. Qed.
Theorem aycb_boolean_proof : aycb_boolean_stmt.
Proof. aceil. unfold aycb_boolean_stmt. intros P. intros until m. intros MI. unfold AY_CB_BOOLEAN, wz.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. stepA. stepA. unfold aycb_boolean_rpost. finishA; reflexivity. Qed.
Theorem aycb_string_proof : aycb_string_stmt.
Proof. aceil. unfold aycb_string_stmt. intros P. intros until m. intros MI. unfold AY_CB_STRING, wz.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. stepA. stepA. unfold aycb_string_rpost. finishA; reflexivity. Qed.

Theorem aycb_number_proof : aycb_number_stmt.
Proof. aceil.
  unfold aycb_number_stmt. intros P l lo. intros until m. intros STA MI EA2 HL ST LOC LO SPH PSTK. subst a2.
  unfold AY_CB_NUMBER, wz in *. ay_statics_open STA. aceil. unfold pol in PSTK.
  assert (MU : munch [(lo, bv_unsigned sp)] m m) by apply munch_refl. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  stepA. stepA.
  zstepA. if_cases K0; zify_cond K0. { exfalso; lia. }
  stepA. stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_number_rpost. finishA. { reflexivity. } ay_statics_close.
Qed.

(* [comment removed for export] *)
Ltac cb_ctx_prologue STMT ENTRY :=
  red; intros P CX lo cx; intros until m;   (* [comment removed for export] *)
  intros STA CR HL CS MI ST LOC LO SPH SEP1 SEP2 EA PSTK PIMG PC; lazymatch type of EA with ?x = _ => subst x end;
  let CC := fresh "CC" in let CB1 := fresh "CB1" in let CB2 := fresh "CB2" in
  destruct CR as (CC & CB1 & CB2); unfold ctx_cells in CC;
  unfold ENTRY, wz in *; ay_statics_open STA;
  aceil;
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PC, SEP1; unfold AY_IMG_LO, AY_IMG_HI in PIMG;
  let PCS := fresh "PCS" in destruct PC as [PC PCS];
  let CSB := fresh "CSB" in let WM := fresh "WM" in
  lazymatch type of CS with oshadow ?mm ?cx ?n =>
    pose proof (block_shadow_bound asegs mm _ cx n CS) as CSB;
    pose proof (wmono_refl asegs mm) as WM end;
  unfold oshadow, A_SB in CS; open_shadow CS.

(* [comment removed for export] *)
Ltac shadow_reload BS E w :=
  let HR := fresh "SHR" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              assert (HR : ov_read_bytes segs m (Z_to_bv 64 (SB + E / 8)) 1 = Some [Z_to_bv 8 0])
                by (apply (block_shadow_read0_u segs m SB A n E w); [lia| lia| rewrite <- Eshb; exact BS| lia| lia| lia| lia])
          end
      end
  end;
  zstepA; clear HR; rewrite ?zxb_small, ?sxb_small by lia; zstepA; if_false.

Theorem aycb_start_map_proof : aycb_start_map_stmt.
Proof. aceil.
  cb_ctx_prologue aycb_start_map_stmt AY_CB_START_MAP.
  assert (MU : munch [(lo, bv_unsigned sp); (CX + 4, CX + 8)] m m) by apply munch_refl.
  carve_frame 16%nat ST.
  stepA. stepA. do 3 stepA.                           (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast CS (CX + 4) 4.
  zstepA. rewrite sx32_wz by lia; unfold wz.                     (* [comment removed for export] *)
  zstepA. stepA.                                      (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_start_map_rpost. finishA.
  + reflexivity.
  + split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz; assumption| cbn; lia].
  + ay_oshadow_close CSeq.
  + ay_statics_close.
Qed.

Theorem aycb_start_array_proof : aycb_start_array_stmt.
Proof. aceil.
  cb_ctx_prologue aycb_start_array_stmt AY_CB_START_ARRAY.
  assert (MU : munch [(lo, bv_unsigned sp); (CX, CX + 4)] m m) by apply munch_refl.
  carve_frame 16%nat ST.
  stepA. stepA. do 3 stepA.
  stepA.                                              (* [comment removed for export] *)
  shadow_fast CS CX 4.
  zstepA. rewrite sx32_wz by lia; unfold wz. zstepA. stepA. zstepA.
  stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_start_array_rpost. finishA.
  + reflexivity.
  + split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz; assumption| cbn; lia].
  + ay_oshadow_close CSeq.
  + ay_statics_close.
Qed.

Theorem aycb_map_key_proof : aycb_map_key_stmt.
Proof. aceil.
  cb_ctx_prologue aycb_map_key_stmt AY_CB_MAP_KEY.
  assert (MU : munch [(lo, bv_unsigned sp)] m m) by apply munch_refl.
  carve_frame 16%nat ST.
  stepA. stepA. do 3 stepA.
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast CS (CX + 4) 4.
  zstepA. rewrite sx32_wz by lia; unfold wz.                     (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?signed_lit_small by lia. lia. }   (* [comment removed for export] *)
  stepA. stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_map_key_rpost. finishA.
  + reflexivity.
  + split; [unfold ctx_cells; unfold wz; assumption| lia].
  + ay_oshadow_close CSeq.
  + ay_statics_close.
Qed.

Theorem aycb_end_map_proof : aycb_end_map_stmt.
Proof. aceil.
  cb_ctx_prologue aycb_end_map_stmt AY_CB_END_MAP.
  assert (MU : munch [(lo, bv_unsigned sp); (CX + 4, CX + 8)] m m) by apply munch_refl.
  carve_frame 16%nat ST.
  stepA. stepA. do 3 stepA.
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast CS (CX + 4) 4.
  zstepA. rewrite sx32_wz by lia; unfold wz.                     (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?signed_lit_small by lia. lia. }   (* [comment removed for export] *)
  shadow_reload CS (CX + 4) 4.                        (* [comment removed for export] *)
  zstepA. stepA. zstepA.                              (* [comment removed for export] *)
  stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_end_map_rpost. finishA.
  + reflexivity.
  + split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz|cbn; lia].
    match goal with H : rw_cells asegs _ CX _ |- _ => revert H end.
    replace (cx_objectLevel cx + -1) with (cx_objectLevel cx - 1) by lia. intros H; exact H.
  + ay_oshadow_close CSeq.
  + ay_statics_close.
Qed.

Theorem aycb_end_array_proof : aycb_end_array_stmt.
Proof. aceil.
  cb_ctx_prologue aycb_end_array_stmt AY_CB_END_ARRAY.
  assert (MU : munch [(lo, bv_unsigned sp); (CX, CX + 4)] m m) by apply munch_refl.
  carve_frame 16%nat ST.
  stepA. stepA. do 3 stepA.
  stepA.                                              (* [comment removed for export] *)
  shadow_fast CS CX 4.
  zstepA. rewrite sx32_wz by lia; unfold wz.
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?signed_lit_small by lia. lia. }
  shadow_reload CS CX 4.
  zstepA. stepA. zstepA.
  stepA. stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  unfold aycb_end_array_rpost. finishA.
  + reflexivity.
  + split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz|cbn; lia].
    match goal with H : rw_cells asegs _ CX _ |- _ => revert H end.
    replace (cx_arrayLevel cx + -1) with (cx_arrayLevel cx - 1) by lia. intros H; exact H.
  + ay_oshadow_close CSeq.
  + ay_statics_close.
Qed.
End W.
End RC__1.
