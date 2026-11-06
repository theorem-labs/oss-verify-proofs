(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA.

Module RA_sfkt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition strcpy_entry := 0xa2814%Z.
Definition stpcpy_entry := 0xa283c%Z.
(* [comment removed for export] *)
Definition REQ_ADDR := 0x217c0%Z.
Definition REQ_BYTES : list byte := [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0].

Definition stpcpy_req_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (D + 3)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D (map C1 REQ_BYTES).

Lemma stpcpy_req_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (j0 j1 j2 j3 : byte),
  a0 = Z_to_bv 64 D ->
  rw_cells rsegs m D [C1 j0; C1 j1; C1 j2; C1 j3] ->
  a1 = Z_to_bv 64 REQ_ADDR ->
  mem_inv rsegs m ->
  evt rsegs (stpcpy_req_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa283c) fc None m (seg_rom rsegs)).
Proof.
  intros until j3. intros -> DST -> MI. unfold REQ_ADDR.
  pose proof (munch_refl [(D, D + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  zs. zs. zs. if_cases K.
  - (* [comment removed for export] *)
    zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit. zs.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. finish.
  - (* [comment removed for export] *)
    zs. zs. zs. if_lit. zs.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strcpy_req_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' D (map C1 REQ_BYTES).

Lemma strcpy_req_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D lo : Z) (j0 j1 j2 j3 : byte),
  stk rsegs m lo (bv_unsigned sp) ->
  a0 = Z_to_bv 64 D ->
  rw_cells rsegs m D [C1 j0; C1 j1; C1 j2; C1 j3] ->
  a1 = Z_to_bv 64 REQ_ADDR ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (D + 4 <= lo \/ bv_unsigned sp <= D)%Z ->
  evt rsegs (strcpy_req_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2814) fc None m (seg_rom rsegs)).
Proof.
  intros until j3. intros ST -> DST Ha1 MI LO SEP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST.
  zs. zs. zs. zs. zs.
  call_lit stpcpy_req_spec by (first [reflexivity | exact DST | exact Ha1 | assumption]).
  zs. zs. zs. zs. zs.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
End RA_sfkt.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpinq.RA_sfkt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition strcpy_icpt_entry : Z := 0x47a8c.
Definition STRCPY_ICPT_STACK : Z := 2160.

(* [comment removed for export] *)
Notation REQ_SHB := (ltac:(let v := eval cbv in (137152 / 8 + 2147450880)%Z in exact v)) (only parsing).
Notation REQ_SHQ := (ltac:(let v := eval cbv in ((137152 / 8 + 2147450880) / 8 * 8)%Z in exact v)) (only parsing).

Definition strcpy_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m                                          (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb2bd5 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaafd8 [C8 (Z_to_bv 64 0xa2814)]      (* [comment removed for export] *)
  /\ map_cells m.

Definition strcpy_req_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRCPY_ICPT_STACK, bv_unsigned sp); (D, D + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' D (map C1 REQ_BYTES).

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D lo : Z) (j0 j1 j2 j3 : byte).
  Notation POST := (strcpy_req_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -72)
                          [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2072 fjunk]).
  Hypothesis LOLE : (lo + STRCPY_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis DR : (D + 4 <= 0x10000 \/ 0x60a000 <= D)%Z.
  Notation SEPt := ((D + 4 <= lo \/ bv_unsigned sp <= D)%Z) (only parsing).

  Section M1.
    Variables (m1 : word -> option byte) (fjunk : list byte) (ngD : nat) (lastbD : Z) (w1D w2D : word).
    Notation LBDt := ((lastbD = 0 \/ ((3 + D) mod 8 < lastbD <= 7))%Z) (only parsing).
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis MU1 : munch [(bv_unsigned sp - STRCPY_ICPT_STACK, bv_unsigned sp); (D, D + 4)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
    Hypothesis FR1 : FRAME m1.
    Hypothesis FRB1 : FRAMEB m1 fjunk.
    Hypothesis DST1 : rw_cells rsegs m1 D [C1 j0; C1 j1; C1 j2; C1 j3].
    Hypothesis Creal : ro_cells rsegs m1 0xaafd8 [C8 (Z_to_bv 64 0xa2814)].
    Hypothesis Gsh : ro_cells rsegs m1 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
    Hypothesis Csh : ro_cells rsegs m1 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
    Hypothesis IRD : inmem_range D 4.
    Hypothesis NGD : ((3 + D) / 8 - D / 8 = Z.of_nat ngD)%Z.
    Hypothesis SHD1 : bytes_at rsegs m1 (D / 8 + shadow_off) (zeros ngD ++ [Z_to_bv 8 lastbD]).
    Hypothesis QBD1 : bytes_at rsegs m1 (sha D - sha D mod 8) (le8 w1D).
    Hypothesis QBD2 : bytes_at rsegs m1 (sha (3 + D) - sha (3 + D) mod 8) (le8 w2D).

    (* [comment removed for export] *)
    #[using="Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 ngD fjunk DR CEIL LOLE j3 j2 j1 j0 Clg"] Lemma scp_tail : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31,
      SEPt ->
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 0x217c0)
                 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 4) x21 s5 (Z_to_bv 64 (bv_unsigned sp + -2144)) x23
                 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4d4a0) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until x31. intros SEP. unfold STRCPY_ICPT_STACK in *.
      pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
      zstep. zstep. zstep. zstep.
      zstep. call_lit strcpy_req_spec by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
        | |- rw_cells _ _ _ _ => exact DST1
        | |- mem_inv _ _ => exact MI1
        | |- _ = Z_to_bv 64 _ => reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      do 12 zstep.
      lazymatch goal with ST : stk rsegs _ lo _ |- _ =>
        release_frame FRB1 ST (bv_unsigned sp + -72)%Z; release_frame FR1 ST (bv_unsigned sp) end.
      finish.
    Qed.

    Section SlowD.
      Variables (sf sl : Z) (x1 x5 x6 x7 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 : word).
      Hypothesis SEP : SEPt.
      Hypothesis ESF : (sf = D / 8 + shadow_off)%Z.
      Hypothesis ESL : (sl = sf + Z.of_nat ngD)%Z.
      Notation AT pc x10 x12 x13 :=
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 0x217c0)
                 x10 (Z_to_bv 64 sl) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 4) x21 s5 (Z_to_bv 64 (bv_unsigned sp + -2144)) x23
                 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

      #[using="SEP Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 ngD fjunk DR CEIL LOLE j3 j2 j1 j0 Clg"] Lemma scp_slowD_end : forall x10 x13, evt rsegs POST (AT 0x4d7d4 x10 (Z_to_bv 64 0) x13).
      Proof.
        intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
        eapply scp_tail; try eassumption.
      Qed.

      #[using="ESL ESF SEP SHD1 Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 lastbD fjunk DR CEIL LOLE j3 j2 j1 j0 Clg"] Lemma scp_slowD_loop : forall (c : nat) (j : Z) x10 x13,
        Z.to_nat (Z.of_nat ngD - j) = c -> (0 <= j < Z.of_nat ngD)%Z -> x10 = Z_to_bv 64 (sf + j) ->
        evt rsegs POST (AT 0x4d7c4 x10 (Z_to_bv 64 0) x13).
      Proof.
        induction c as [|c IH]; intros j x10 x13 Hc Hj ->; [lia|].
        pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHD1) as SB.
        rewrite length_app, zeros_length in SB. cbn [length] in SB.
        pose proof (u8ro_read rsegs m1 (D / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHD1) as RD.
        specialize (RD ltac:(rewrite (shadow_nth ngD lastbD (Z.to_nat j)) by lia;
                               replace (Z.to_nat j <? ngD)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                       ltac:(lia) ltac:(unfold wa; f_equal; lia)).
        zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zstep. zstep.
        zstep. if_cases K; zify_cond K.
        - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
        - apply scp_slowD_end.
      Qed.
    End SlowD.

    (* [comment removed for export] *)
    #[using="QBD2 QBD1 SHD1 NGD IRD Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 w2D w1D ngD fjunk DR CEIL LOLE j3 j2 j1 j0 Clg"] Lemma scp_p2 : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31,
      SEPt -> LBDt ->
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 0x217c0)
                 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 4) x21 s5 (Z_to_bv 64 (bv_unsigned sp + -2144)) x23
                 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4d458) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until x31. intros SEP LBD. pose proof LOLE as LOLE'. unfold STRCPY_ICPT_STACK in LOLE'.
      unfold STRCPY_ICPT_STACK in MU1.
      pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB.
      assert (AFD : (0 <= D /\ D + 4 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRD; lia).
      assert (QH1 : (sha D - sha D mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      assert (QH2 : (sha (3 + D) - sha (3 + D) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      pose proof (bytes_at_bound _ _ _ _ SHD1) as SHhi. rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi.
      zstep. rewrite zb_lxor_ones by lia.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      zstep. zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
      assert (HS1 : (0 <= Z.shiftr D 3 <= D)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
      assert (HS2 : (0 <= Z.shiftr (3 + D) 3 <= 3 + D)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
      do 10 zstep.
      pose proof (qc_read _ _ _ QBD1 ltac:(lia)) as RD1.
      pose proof (qc_read _ _ _ QBD2 ltac:(lia)) as RD2.
      zstep. zstep. zstep.
      zstep. if_cases K7; zify_cond K7.
      - (* [comment removed for export] *)
        assert (LBR : (0 <= lastbD < 128)%Z) by lia.
        pose proof (u8ro_read rsegs _ (D / 8 + shadow_off) _ (Z.of_nat ngD) (Z_to_bv 8 lastbD)
                      (Z_to_bv 64 (2147450880 + Z.shiftr (3 + D) 3)) SHD1) as RD.
        specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngD lastbD ngD), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                       ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
        zstep. rewrite sxb_small by lia.
        zstep. zstep. zstep. zstep. zstep.
        rewrite (poisoned_last_zero (3 + D) lastbD) by (first [lia | exact LBD]).
        rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
        set (sf := (2147450880 + D / 8)%Z). set (sl := (2147450880 + (3 + D) / 8)%Z).
        assert (ESF : (sf = D / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
        assert (ESL : (sl = sf + Z.of_nat ngD)%Z) by (unfold sf, sl; mlia).
        assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z) by (subst sf sl; unfold shadow_off in *; mlia).
        clearbody sf sl.
        zstep. if_cases K8; zify_cond K8.
        + eapply scp_slowD_end; eassumption.
        + eapply scp_slowD_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
      - eapply scp_tail; try eassumption.
    Qed.

    (* [comment removed for export] *)
    Variables (lastbS : Z) (wS : word).
    Hypothesis CS8 : ro_cells rsegs m1 REQ_SHQ [C8 wS].
    Hypothesis CS1 : ro_cells rsegs m1 REQ_SHB [C1 (Z_to_bv 8 lastbS)].
    Hypothesis LBS : (lastbS = 0 \/ (137155 mod 8 < lastbS <= 7))%Z.

    #[using="LBS CS1 CS8 wS lastbS QBD2 QBD1 SHD1 NGD IRD Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 w2D w1D ngD fjunk DR CEIL LOLE j3 j2 j1 j0 Clg"] Lemma scp_p1 : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31,
      SEPt -> LBDt ->
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 0x217c0)
                 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 4) x21 s5 (Z_to_bv 64 (bv_unsigned sp + -2144)) x23
                 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4d410) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until x31. intros SEP LBD. pose proof LOLE as LOLE'. unfold STRCPY_ICPT_STACK in LOLE'.
      pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      assert (LBR : (0 <= lastbS < 128)%Z) by lia.
      zstep.
      zstep. if_cases K4; zify_cond K4. { deadK K4. }
      zstep. zstep. if_cases K5; zify_cond K5. { deadK K5. }
      do 13 zstep.
      zstep. if_cases K7; zify_cond K7.
      - (* [comment removed for export] *)
        zstep. rewrite sxb_small by lia.
        zstep. zstep. zstep. zstep. zstep.
        change 9223372036854775811%Z with (Z.lxor (Z.land 137155 7) 9223372036854775808).
        rewrite (poisoned_last_zero 137155 lastbS) by (first [lia | exact LBS]).
        zstep. if_cases K8; zify_cond K8. 2:{ deadK K8. }
        zstep. zstep. if_cases K9; zify_cond K9. all: try (deadK K9).
        eapply scp_p2; try eassumption.
      - eapply scp_p2; try eassumption.
    Qed.
  End M1.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma strcpy_req_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D lo : Z) (j0 j1 j2 j3 : byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 REQ_ADDR ->
  rw_cells rsegs m D [C1 j0; C1 j1; C1 j2; C1 j3] ->
  mem_inv rsegs m -> strcpy_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRCPY_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (D + 4 <= lo \/ bv_unsigned sp <= D)%Z -> (D + 4 <= 0x10000 \/ 0x60a000 <= D)%Z ->
  range_ok m REQ_ADDR 4 -> range_ok m D 4 ->
  evt rsegs (strcpy_req_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47a8c) fc None m (seg_rom rsegs)).
Proof.
  intros until j3. intros -> -> DST MI CELLS ST LOLE CEIL SEP DR RS RD. unfold REQ_ADDR in *.
  pose proof LOLE as LOLE'. unfold STRCPY_ICPT_STACK in LOLE'.
  (first [ dand5 CELLS as CI Gaf Crs Creal MC | destruct CELLS as (CI & Gaf & Crs & Creal & MC) ]). unfold asan_inited_cell in CI. pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned sp - STRCPY_ICPT_STACK, bv_unsigned sp); (D, D + 4)]%Z m) as MU. unfold STRCPY_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  (first [ dand4 RS as _ (ngS & lastbS & NGS & SHS & LBS) QWS _ | destruct RS as (_ & (ngS & lastbS & NGS & SHS & LBS) & QWS & _) ]).
  assert (ngS = 0%nat) as -> by (change ((137152 + 4 - 1) / 8 - 137152 / 8)%Z with 0%Z in NGS; lia). cbn [zeros repeat app] in SHS.
  change (137152 / 8 + shadow_off)%Z with REQ_SHB%Z in SHS.
  change (sha 137152 - sha 137152 mod 8)%Z with REQ_SHQ%Z in QWS.
  destruct (mapped8_le8 _ _ QWS ltac:(lia) ltac:(lia)) as [wS QBS].
  assert (CS8 : ro_cells rsegs m REQ_SHQ [C8 wS]) by (split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact QBS]).
  assert (CS1 : ro_cells rsegs m REQ_SHB [C1 (Z_to_bv 8 lastbS)]) by (split; [exact (conj I I)| exact SHS]).
  clear QBS SHS. change ((137152 + 4 - 1) mod 8)%Z with (137155 mod 8)%Z in LBS.
  (* [comment removed for export] *)
  (first [ dand4 RD as IRD (ngD & lastbD & NGD & SHD & LBD) QWD1 QWD2 | destruct RD as (IRD & (ngD & lastbD & NGD & SHD & LBD) & QWD1 & QWD2) ]).
  assert (AFD : (0 <= D /\ D + 4 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRD; lia).
  replace (D + 4 - 1)%Z with (3 + D)%Z in NGD, LBD, QWD2 by lia.
  destruct (mapped8_le8 _ _ QWD1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1D QBD1].
  destruct (mapped8_le8 _ _ QWD2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2D QBD2].
  assert (QH1 : (sha D - sha D mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (3 + D) - sha (3 + D) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbsD eqn:EsbsD.
  assert (SHDhi : (D / 8 + shadow_off + Z.of_nat (length sbsD) <= 0x100080000000)%Z).
  { subst sbsD. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  freeze DST; freeze CI; freeze Gaf; freeze Crs; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme;
  freeze Ghe; freeze Che; freeze CS8; freeze CS1; freeze SHD; freeze QBD1; freeze QBD2.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  carve_frame 72%nat ST. carve_frame 2072%nat ST.
  do 12 zstep.
  thaw DST MUp WM; thaw CI MUp WM; thaw Gaf MUp WM; thaw Crs MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
  thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw CS8 MUp WM; thaw CS1 MUp WM; thaw SHD MUp WM; thaw QBD1 MUp WM; thaw QBD2 MUp WM.
  clear MUp.
  zstep. zstep.
  zstep. call_lit tryinit_spec by (idtac;
    lazymatch goal with
    | |- asan_inited_cell _ => exact CI
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
    | |- mem_inv _ _ => eassumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
  zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. lia. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zs. zs. zs. zs. zs. if_lit. zs. zs. zs. zs. if_lit. zs. zs. zs. zs. if_lit. zs. zs. zs. zs. if_lit. zs. zstep.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2.
  - subst sbsD. eapply scp_p1; try eassumption.
  - zstep. zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
    subst sbsD. eapply scp_p1; try eassumption.
Qed.

End CEIL.
