(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcppc0 AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.

Module AIcpaky.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcppc0 AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpa7e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpo65.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.

(* [comment removed for export] *)
Definition S_INT : list byte := [Z_to_bv 8 100; Z_to_bv 8 105; Z_to_bv 8 111; Z_to_bv 8 117; Z_to_bv 8 120; Z_to_bv 8 88; Z_to_bv 8 110; Z_to_bv 8 0]. (* [comment removed for export] *)
Lemma S_INT_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1cab5 S_INT.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x1cab5 S_INT MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.

Section DIRSEG4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).
  Hypothesis LOLE : (lo + PCM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis FLO : (A + Z.of_nat (length fbytes) + 1 <= lo)%Z.
  Notation DIRQ := (pcm_dir ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).
  Notation ATQ := (pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).

  (* [comment removed for export] *)
  #[using="FLO VLO LOLE Clg"] Lemma pcm_dir_d : forall (Q : machine_state -> Prop) off k ms,
    DIRQ off k ms -> (0 <= off)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 37) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 1)) = Some (Z_to_bv 8 100) ->
    (forall ms1, ATQ PCM_NEXT (off + 2) (k + 1) ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms TOP OFF0 H37 Hcb K; unpack_dir TOP; unfold PCM_STACK, PCM_DIR, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR; pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB; rewrite length_app in AB; cbn [length] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    zs; (* [comment removed for export] *)
    fmt_rd (off + 1)%Z.
    zs; cbv beta; change (bv_unsigned (Z_to_bv 8 100)) with 100%Z.
    zto 0x6a344%Z; call_istrchr S_FLAGS_at.
    zto 0x4a584%Z; fmt_rd (off + 1)%Z.
    zto 0x6a344%Z; call_istrchr S_LENMOD_at.
    zto 0x6a344%Z; call_istrchr S_cCsS_at.
    (* [comment removed for export] *)
    zto 0x4da9c%Z.
    lazymatch goal with STq : stk _ _ lo _ |- _ => carve_frame 32%nat STq end.
    zto 0x6a344%Z; call_istrchr S_INT_at.
    zto 0x4dc14%Z.
    lazymatch goal with FRq : rw_cells _ _ (bv_unsigned sp + -2272) _ |- _ =>
      lazymatch goal with STq : stk _ _ lo _ |- _ => release_frame FRq STq (bv_unsigned sp + -2240)%Z end end.
    zs; (* [comment removed for export] *)
    zto 0x6a344%Z; call_istrchr S_FLOAT_at.
    zto 0x4a494%Z.
    apply K; apply rw_cells_to_CB in DIR; cbn [cells_size csize Nat.add] in DIR.
    pack_pcm.
    replace (A + off + 2)%Z with (A + (off + 2))%Z by lia; replace (VA + 8 * k + 8)%Z with (VA + 8 * (k + 1))%Z by lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="FLO VLO LOLE Clg"] Lemma pcm_dir_u : forall (Q : machine_state -> Prop) off k ms,
    DIRQ off k ms -> (0 <= off)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 37) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 1)) = Some (Z_to_bv 8 117) ->
    (forall ms1, ATQ PCM_NEXT (off + 2) (k + 1) ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms TOP OFF0 H37 Hcb K; unpack_dir TOP; unfold PCM_STACK, PCM_DIR, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR; pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB; rewrite length_app in AB; cbn [length] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    zs; (* [comment removed for export] *)
    fmt_rd (off + 1)%Z.
    zs; cbv beta; change (bv_unsigned (Z_to_bv 8 117)) with 117%Z.
    zto 0x6a344%Z; call_istrchr S_FLAGS_at.
    zto 0x4a584%Z; fmt_rd (off + 1)%Z.
    zto 0x6a344%Z; call_istrchr S_LENMOD_at.
    zto 0x6a344%Z; call_istrchr S_cCsS_at.
    (* [comment removed for export] *)
    zto 0x4da9c%Z.
    lazymatch goal with STq : stk _ _ lo _ |- _ => carve_frame 32%nat STq end.
    zto 0x6a344%Z; call_istrchr S_INT_at.
    zto 0x4dc14%Z.
    lazymatch goal with FRq : rw_cells _ _ (bv_unsigned sp + -2272) _ |- _ =>
      lazymatch goal with STq : stk _ _ lo _ |- _ => release_frame FRq STq (bv_unsigned sp + -2240)%Z end end.
    zs; (* [comment removed for export] *)
    zto 0x6a344%Z; call_istrchr S_FLOAT_at.
    zto 0x4a494%Z.
    apply K; apply rw_cells_to_CB in DIR; cbn [cells_size csize Nat.add] in DIR.
    pack_pcm.
    replace (A + off + 2)%Z with (A + (off + 2))%Z by lia; replace (VA + 8 * k + 8)%Z with (VA + 8 * (k + 1))%Z by lia; reflexivity.
  Qed.
End DIRSEG4.
End AIcpaky.


Module AIcphe4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcppc0 AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpa7e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpo65.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.
Local Ltac icpt_consts_in H ::= unfold region_is_poisoned_post in H.

Section SB.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).
  Hypothesis LOLE : (lo + PCM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis FLO : (A + Z.of_nat (length fbytes) + 1 <= lo)%Z.
  Notation DIRQ := (pcm_dir ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).
  Notation ATQ := (pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).

  (* [comment removed for export] *)
  Section PHASE.
    Variables (Q : machine_state -> Prop) (so sk P len : Z).
    Variables (m1 : word -> option byte) (jm jd j8 : list byte) (vq cq : word) (ng : nat) (lastb : Z) (w1 w2 : word).
    Variables (x1 x5 x6 x7 x9 x15 x16 x17 x28 x29 x30 x31 : word).
    Hypothesis LEN : (0 <= len /\ len + 1 <= 2^31)%Z.
    Hypothesis IR : inmem_range P (len + 1).
    Hypothesis NG : ((P + len) / 8 - P / 8 = Z.of_nat ng)%Z.
    Hypothesis LB : (lastb = 0 \/ ((P + len) mod 8 < lastb <= 7))%Z.
    Hypothesis K : forall ms1, ATQ PCM_NEXT so sk ms1 -> evt rsegs Q ms1.
    Notation MEMS mq := (mem_inv rsegs mq /\ munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m0 mq /\ wmono rsegs m0 mq
      /\ stk rsegs mq lo (bv_unsigned sp + -2240)
      /\ rw_cells rsegs mq (bv_unsigned sp + -104) (pcm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ rw_cells rsegs mq (bv_unsigned sp + -2176) [CB 2072 jm]
      /\ rw_cells rsegs mq (bv_unsigned sp + -2216) [CB 40 jd]
      /\ rw_cells rsegs mq (bv_unsigned sp + -2240) [CB 8 j8; C8 vq; C8 cq]
      /\ bytes_at rsegs mq A (fbytes ++ [Z_to_bv 8 0])
      /\ bytes_at rsegs mq VA (u64s slots)) (only parsing).
    Notation AT pc mq xa0 xa1 xa2 xa3 xa4 xs7 :=
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9 xa0 xa1 xa2 xa3 xa4 x15 x16 x17
               (Z_to_bv 64 10) (Z_to_bv 64 (A + so)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * sk)) (Z_to_bv 64 P) xs7
               (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mq (seg_rom rsegs)) (only parsing).

    (* [comment removed for export] *)
    #[using="K"] Lemma sb_tail : forall mq y1 y5 y6 y7 xa0 xa1 xa2 xa3 xa4 y15 y16 y17 xs7 y28 y29 y30 y31, MEMS mq ->
      evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp x9 xa0 xa1 xa2 xa3 xa4 y15 y16 y17
               (Z_to_bv 64 10) (Z_to_bv 64 (A + so)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * sk)) (Z_to_bv 64 P) xs7
               (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
          F (Z_to_bv 64 0x4a814) fc None mq (seg_rom rsegs)).
    Proof.
      intros until y31. ((first [ intro dR_3; dand10 dR_3 as MI MU WM ST FRT FRM DIR FRL FB VAA | intros (MI & MU & WM & ST & FRT & FRM & DIR & FRL & FB & VAA) ])). unfold PCM_STACK in MU.
      pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      zs. zs. apply K. pack_pcm. reflexivity.
    Qed.

    Section Slow.
      Variables (sf sl : Z).
      Hypothesis ESF : (sf = P / 8 + shadow_off)%Z.
      Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.

      #[using="K ng"] Lemma sb_slow_end : forall xa0 xa3 xa4, MEMS m1 -> evt rsegs Q (AT 0x4a934 m1 xa0 (Z_to_bv 64 sl) (Z_to_bv 64 0) xa3 xa4 (Z_to_bv 64 (len + 1))).
      Proof.
        intros xa0 xa3 xa4 MM. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        zs. zs. brf Kb; try (deadK Kb).
        apply sb_tail. exact MM.
      Qed.

      #[using="ESL ESF K"] Lemma sb_slow_loop : forall (cc : nat) (j : Z) xa0 xa3 xa4,
        MEMS m1 -> bytes_at rsegs m1 (P / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) ->
        Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> xa0 = Z_to_bv 64 (sf + j) ->
        evt rsegs Q (AT 0x4a924 m1 xa0 (Z_to_bv 64 sl) (Z_to_bv 64 0) xa3 xa4 (Z_to_bv 64 (len + 1))).
      Proof.
        induction cc as [|cc IH]; intros j xa0 xa3 xa4 MM SH1 Hc Hj ->; [lia|].
        pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SBB.
        rewrite length_app, zeros_length in SBB. cbn [length] in SBB.
        pose proof (u8ro_read rsegs m1 (P / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
        specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                               replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                       ltac:(lia) ltac:(unfold wa; f_equal; lia)).
        zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zs. zs.
        zs. brf Kb.
        - apply (IH (j + 1)%Z); [exact MM| exact SH1| lia| lia| f_equal; lia].
        - apply sb_slow_end. exact MM.
      Qed.
    End Slow.

    (* [comment removed for export] *)
    #[using="K LB NG IR LEN FLO VLO CEIL LOLE Clg"] Lemma sb_rip : forall xa0 xa1 xa2 xa3 xa4,
      MEMS m1 -> map_cells m1 -> bytes_at rsegs m1 (P / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) ->
      evt rsegs Q (AT 0x4a93c m1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (len + 1))).
    Proof.
      intros until xa4. ((first [ intro dR_4; dand10 dR_4 as MI MU WM ST FRT FRM DIR FRL FB VAA | intros (MI & MU & WM & ST & FRT & FRM & DIR & FRL & FB & VAA) ]); intros MC SH1). unfold PCM_STACK in *.
      pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
      assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
      assert (AF : (0 <= P /\ P + (len + 1) + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      pose proof (bytes_at_bound _ _ _ _ FB) as AB. pose proof (bytes_at_bound _ _ _ _ VAA) as VB.
      unfold pcm_saved in FRT.
      zs. zs.
      zs. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH1); call_icpt region_is_poisoned_spec by (idtac;
        lazymatch goal with
        | |- map_cells _ => exact MC
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- mem_inv _ _ => eassumption
        | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
        | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; split; [replace (P + (len + 1) - 1)%Z with (P + len)%Z by lia; exact NG| split; [exact SH1| replace (P + (len + 1) - 1)%Z with (P + len)%Z by lia; exact LB]]
        | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
        end).
      zs. brf Kb; try (deadK Kb).
      apply sb_tail. unfold PCM_STACK. repeat (split; [eassumption|]). eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="K LB NG IR LEN FLO VLO CEIL LOLE Clg"] Lemma sb_phase : forall xa1 xa2 xa3 xa4,
      MEMS m1 -> map_cells m1 ->
      bytes_at rsegs m1 (P / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) ->
      bytes_at rsegs m1 (sha P - sha P mod 8) (le8 w1) ->
      bytes_at rsegs m1 (sha (P + len) - sha (P + len) mod 8) (le8 w2) ->
      evt rsegs Q (AT 0x4a8b8 m1 (Z_to_bv 64 len) xa1 xa2 xa3 xa4 (Z_to_bv 64 (len + 1))).
    Proof.
      intros until xa4. intros MM MC SH1 QB1 QB2. (first [ pose proof (MM) as dR_1; dand10 dR_1 as MI MU WM ST FRT FRM DIR FRL FB VAA | pose proof MM as (MI & MU & WM & ST & FRT & FRM & DIR & FRL & FB & VAA) ]). unfold PCM_STACK in *.
      pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
      assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
      assert (AF : (0 <= P /\ P + (len + 1) + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      pose proof MC as MC'. open_map_cells MC'.
      assert (QH1 : (sha P - sha P mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      assert (QH2 : (sha (P + len) - sha (P + len) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
      assert (SHhi : (P / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
      { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
      (* [comment removed for export] *)
      zs. first [rewrite zb_lxor_ones by lia | idtac].
      zs. brf K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1 AF LEN; try pose proof alloc_ceiling_val. lia. }
      zs. zs.
      zs. brf K2.
      - (* [comment removed for export] *)
        zs. brf K3; try (deadK K3).
        subst sbs. apply sb_rip; assumption.
      - (* [comment removed for export] *)
        assert (HS1 : (0 <= Z.shiftr P 3 <= P)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        assert (HS2 : (0 <= Z.shiftr (P + len) 3 <= P + len)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        do 10 zs.
        replace (P + (len + 1) + -1)%Z with (P + len)%Z by lia || idtac.
        pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
        pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
        zs. zs. zs. zs.
        zs. brf K7.
        + (* [comment removed for export] *)
          subst sbs. apply sb_tail. exact MM.
        + (* [comment removed for export] *)
          subst sbs.
          assert (LBR : (0 <= lastb < 128)%Z) by lia.
          pose proof (u8ro_read rsegs _ (P / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                        (Z_to_bv 64 (2147450880 + Z.shiftr (P + len) 3)) SH1) as RD.
          specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                         ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
          zs. first [rewrite sxb_small by lia | idtac].
          zs. zs. zs. zs. zs.
          rewrite (poisoned_last_zero (P + len) lastb) by (first [lia | exact LB]).
          rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
          set (sf := (2147450880 + P / 8)%Z). set (sl := (2147450880 + (P + len) / 8)%Z).
          assert (ESF : (sf = P / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
          assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
          assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
          { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
          clearbody sf sl.
          zs. brf K8.
          * eapply sb_slow_end; eassumption.
          * eapply sb_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
    Qed.
  End PHASE.

  (* [comment removed for export] *)
  #[using="FLO VLO CEIL LOLE Clg"] Lemma pcm_dir_sb : forall (Q : machine_state -> Prop) off k ms (P : Z) (str slack : list byte),
    DIRQ off k ms -> (0 <= off)%Z -> (0 <= k)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 37) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 1)) = Some (Z_to_bv 8 115) ->
    nth_error slots (Z.to_nat k) = Some (Z_to_bv 64 P) -> (0 < P)%Z ->
    bytes_at rsegs m0 P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    range_ok m0 P (Z.of_nat (length str) + 1) -> map_cells m0 ->
    (Z.of_nat (length str) + 1 <= 2^31)%Z ->
    (P + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - PCM_STACK \/ bv_unsigned sp <= P)%Z ->
    (forall ms1, ATQ PCM_NEXT (off + 2) (k + 1) ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms P str slack TOP OFF0 K0 H37 H115 HS PNZ STR0 NONUL RNG0 MC0 L31 SEP K.
    unpack_dir TOP. unfold PCM_STACK, PCM_DIR, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (bytes_at_bound _ _ _ _ VAA) as VB. rewrite u64s_length in VB.
    pose proof (bytes_at_bound _ _ _ _ STR0) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
    pose proof (nth_error_Some_length _ _ HS) as KL || assert (KL : (Z.to_nat k < length slots)%nat) by (destruct (Nat.lt_ge_cases (Z.to_nat k) (length slots)) as [L|G]; [exact L| rewrite (proj2 (nth_error_None _ _) G) in HS; discriminate]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (WL : wlow [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z) by (cbn [wlow]; unfold kHighMemBeg_z; lia).
    (* [comment removed for export] *)
    assert (STR : bytes_at rsegs mq P (str ++ Z_to_bv 8 0 :: slack)).
    { eapply bytes_at_transport; [exact STR0| exact MU|]. cbn [disjoint_from]. rewrite length_app. cbn [length]. split; [lia| exact I]. }
    assert (RNG : range_ok mq P (Z.of_nat (length str) + 1)). { refine (lowP_range_ok P _ _ _ _ _ MU WL RNG0). lia. }
    assert (MC : map_cells mq) by (eapply lowP_map_cells; [exact MU| exact WL| exact MC0]).
    clear STR0 RNG0 MC0.
    (first [ dand4 RNG as IR (ng & lastb & NG & SH & LB) QW1 QW2 | destruct RNG as (IR & (ng & lastb & NG & SH & LB) & QW1 & QW2) ]).
    assert (AF : (0 <= P /\ P + (Z.of_nat (length str) + 1) + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
    destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
    destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
    replace (P + (Z.of_nat (length str) + 1) - 1)%Z with (P + Z.of_nat (length str))%Z in NG, LB, QB2 by lia.
    assert (QH1 : (sha P - sha P mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (P + Z.of_nat (length str)) - sha (P + Z.of_nat (length str)) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (SHhi : (P / 8 + shadow_off + Z.of_nat (length (zeros ng ++ [Z_to_bv 8 lastb])) <= 0x100080000000)%Z).
    { rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
    pose proof MC as MC'. open_map_cells MC'.
    assert (PW : bv_unsigned (Z_to_bv 64 P) = P) by (rewrite unsigned_lit by lia; reflexivity).
    zs. (* [comment removed for export] *)
    fmt_rd (off + 1)%Z.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 115)) with 115%Z.
    zto 0x6a344%Z. call_istrchr S_FLAGS_at.
    zto 0x4a584%Z. fmt_rd (off + 1)%Z.
    zto 0x6a344%Z. call_istrchr S_LENMOD_at.
    zto 0x6a344%Z. call_istrchr S_cCsS_at.
    zto 0x6a344%Z. call_istrchr S_CS_at.
    zto 0x6a344%Z. call_istrchr S_csB_at.
    zto 0x6a344%Z. call_istrchr S_sS_at.
    zto 0x4a828%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with VAq : bytes_at rsegs mx VA (u64s slots) |- _ =>
        pose proof (slot_read8 mx VA slots k (Z_to_bv 64 P) (Z_to_bv 64 (VA + 8 * k)) VAq HS ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDV end end.
    zs. zs.
    zs. brf Kp. { exfalso. rewrite PW in Kp || idtac. lia. }
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
    zs. brf Ksp; try (deadK Ksp).
    zs. zs. brf Kpr; try (deadK Kpr).
    zs.
    zs. call_lit istrlen_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => rewrite ?PW, ?unsigned_lit by lia; eassumption
      | |- ~ In _ _ => exact NONUL
      | |- _ => eassumption
      end).
    zs.
    apply rw_cells_to_CB in DIR. cbn [cells_size csize Nat.add] in DIR.
    replace (A + off + 2)%Z with (A + (off + 2))%Z by lia. replace (VA + 8 * k + 8)%Z with (VA + 8 * (k + 1))%Z by lia.
    subst sbs.
    eapply (sb_phase Q (off + 2) (k + 1) P (Z.of_nat (length str)) _ _ _ _ _ _ ng lastb w1 w2).
    - lia.
    - exact IR.
    - exact NG.
    - exact LB.
    - exact K.
    - unfold PCM_STACK. repeat (split; [eassumption|]). eassumption.
    - repeat (split; [assumption|]). assumption.
    - eassumption.
    - eassumption.
    - eassumption.
  Qed.
End SB.
End AIcphe4.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpa7e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpo65 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp1qh.AIcpaky OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp1qh.AIcphe4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Definition FMTB_D : list byte := Eval cbv in zb [37; 100; 10]%Z.                                                   (* [comment removed for export] *)
Definition FMTB_USAGE : list byte := Eval cbv in zb [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10]%Z.   (* [comment removed for export] *)
Definition FMTB_COPEN : list byte := Eval cbv in zb [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10]%Z. (* [comment removed for export] *)
Definition FMTB_RERR : list byte := Eval cbv in zb [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10]%Z. (* [comment removed for export] *)
Definition FMTB_REFUSED : list byte := Eval cbv in zb [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z. (* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition pcm_stmt_str (fbytes : list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A VA : Z) (slots : list word)
         (P : Z) (str slack : list byte),
    a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0]) -> bytes_at rsegs m VA (u64s slots) ->
    nth_error slots 0 = Some (Z_to_bv 64 P) -> (0 < P)%Z ->
    bytes_at rsegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    range_ok m P (Z.of_nat (length str) + 1) -> (Z.of_nat (length str) + 1 <= 2^31)%Z ->
    (P + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - PCM_STACK \/ bv_unsigned sp <= P)%Z ->
    map_cells m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    (lo + PCM_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
    (bv_unsigned sp <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    range_ok m A (Z.of_nat (length fbytes) + 1) -> (A + Z.of_nat (length fbytes) + 1 <= lo)%Z ->
    evt rsegs (pcm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCM_ENTRY) fc None m (seg_rom rsegs)).

End CEIL.

Ltac lit_run_tac20 :=
  split;
  [ intros j b Hj Hb; do 20 (try (destruct j as [|j]; [cbn in Hb; inversion Hb; subst; rewrite !Z_to_bv_unsigned; vm_compute; lia |])); lia
  | intros j Hj; do 20 (try (destruct j as [|j]; [eexists; reflexivity|])); lia ].
Ltac seg_sides20 :=
  lazymatch goal with
  | |- pcm_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
  | |- pcm_dir _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
  | |- lit_run _ _ _ => lit_run_tac20
  | |- nth_error _ _ = Some _ => first [reflexivity | eassumption]
  | |- (bv_unsigned _ <> _)%Z => first [eassumption | byte_neq]
  | |- bytes_at _ _ _ _ => eassumption
  | |- ~ In _ _ => eassumption
  | |- range_ok _ _ _ => eassumption
  | |- map_cells _ => eassumption
  | |- _ \/ _ => eassumption
  | |- (_ <= _)%Z => lia
  | |- (_ < _)%Z => lia
  | |- forall _, _ => idtac
  | |- ?G => idtac "seg_sides: unexpected goal" G
  end.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem pcm_fmt_d : pcm_stmt FMTB_D SLOTS_C.
Proof.
  unfold pcm_stmt. intros until slots. intros -> -> FB VAA _ MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_D VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_D VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 0%nat); [seg_sides20 ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_d _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_D VA slots m) with (off := 0%Z) (k := 0%Z); [seg_sides20 ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_D VA slots m) with (off := 2%Z) (k := 1%Z); [seg_sides20 ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_D VA slots m) with (off := 2%Z) (k := 1%Z) (nl := 1%nat); [seg_sides20 ..].
Qed.

Theorem pcm_fmt_refused : pcm_stmt FMTB_REFUSED SLOTS_C.
Proof.
  unfold pcm_stmt. intros until slots. intros -> -> FB VAA _ MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_REFUSED VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_REFUSED VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 14%nat); [seg_sides20 ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_u _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_REFUSED VA slots m) with (off := 14%Z) (k := 0%Z); [seg_sides20 ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_REFUSED VA slots m) with (off := 16%Z) (k := 1%Z); [seg_sides20 ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_REFUSED VA slots m) with (off := 16%Z) (k := 1%Z) (nl := 16%nat); [seg_sides20 ..].
Qed.

(* [comment removed for export] *)

Theorem pcm_fmt_usage : pcm_stmt_str FMTB_USAGE.
Proof.
  unfold pcm_stmt_str. intros until slack. intros -> -> FB VAA HS PNZ STR NONUL RNGS L31 SEP MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_USAGE VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_USAGE VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 7%nat); [seg_sides20 ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_sb _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_USAGE VA slots m) with (off := 7%Z) (k := 0%Z); [seg_sides20 ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_USAGE VA slots m) with (off := 9%Z) (k := 1%Z); [seg_sides20 ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_USAGE VA slots m) with (off := 9%Z) (k := 1%Z) (nl := 7%nat); [seg_sides20 ..].
Qed.

Theorem pcm_fmt_copen : pcm_stmt_str FMTB_COPEN.
Proof.
  unfold pcm_stmt_str. intros until slack. intros -> -> FB VAA HS PNZ STR NONUL RNGS L31 SEP MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_COPEN VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_COPEN VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 17%nat); [seg_sides20 ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_sb _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_COPEN VA slots m) with (off := 17%Z) (k := 0%Z); [seg_sides20 ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_COPEN VA slots m) with (off := 19%Z) (k := 1%Z); [seg_sides20 ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_COPEN VA slots m) with (off := 19%Z) (k := 1%Z) (nl := 1%nat); [seg_sides20 ..].
Qed.

Theorem pcm_fmt_rerr : pcm_stmt_str FMTB_RERR.
Proof.
  unfold pcm_stmt_str. intros until slack. intros -> -> FB VAA HS PNZ STR NONUL RNGS L31 SEP MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_RERR VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_RERR VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 19%nat); [seg_sides20 ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_sb _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_RERR VA slots m) with (off := 19%Z) (k := 0%Z); [seg_sides20 ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_RERR VA slots m) with (off := 21%Z) (k := 1%Z); [seg_sides20 ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_RERR VA slots m) with (off := 21%Z) (k := 1%Z) (nl := 1%nat); [seg_sides20 ..].
Qed.

End CEIL2.
