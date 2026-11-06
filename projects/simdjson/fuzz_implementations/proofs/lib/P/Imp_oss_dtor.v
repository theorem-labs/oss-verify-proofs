(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit Imp_oss_defs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r end; fail "PROBE".

Definition ios_dtorI_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo O fill : Z) (j124 j260 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 48, q); (O + 112, O + 120)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo q
    /\ rw_cells psegs m' (O + 112) (C8 (Z_to_bv 64 OSS_IOSB_VPTR) :: List.tl (ios_cellsI O fill j124 j260)).

Definition ios_dtorI_stmt : Prop :=
  forall ra q gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo O fill : Z) (j124 j260 : list byte),
  stk psegs m lo q -> (lo <= q - 48)%Z -> (0x10b000 <= lo)%Z ->
  rw_cells psegs m (O + 112) (ios_cellsI O fill j124 j260) -> (q <= O)%Z -> (O + 264 < 2^62)%Z ->
  mem_inv psegs m ->
  evt psegs (ios_dtorI_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo O fill j124 j260 m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (O + 112)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_IOS_DTOR) fc None m (seg_rom psegs)).

Theorem ios_dtorI_proof : ios_dtorI_stmt.
Proof.
  unfold ios_dtorI_stmt, OSS_IOS_DTOR. intros until j260. intros ST LO LOLO IOSF RO RO2 MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 48, q); (O + 112, O + 120)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold ios_dtorI_post.
  unfold ios_cellsI, OSS_IOS_VPTR, OSS_CLASSIC, OSS_IOSB_VPTR in IOSF |- *. cbn [List.tl].
  lstep.
  carve_frame 48%nat ST.
  do 12 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  lstep.
  takeZ IOSF 8%nat (O + 160) P0. takeZ IOSF 1%nat (O + 168) LOCM.
  replace (Z_to_bv 64 (O + 112 + 48)) with (Z_to_bv 64 (O + 160)) by (f_equal; lia).
  eapply evt_cut.
  { eapply (locale_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (O + 160)); [exact LOCM | lia | assumption]. }
  intros ms' (a0' & a1' & ->).
  replace (ret_pc (Z_to_bv 64 0x78dd8)) with (Z_to_bv 64 0x78dd8) by (apply bv_eq; vm_compute; reflexivity).
  glueZ LOCM IOSF. glueZ P0 LOCM. rename P0 into IOSF.

  lstep. lstep. do 2 lstep. if_true. lstep.
  lstep. lstep. do 2 lstep. if_true. lstep.
  lstep. lstep. do 2 lstep. if_true. lstep.

  do 7 lstep. release_frame FR ST q.
  do 3 lstep. if_true. lstep.
  sys_finish.
Qed.
