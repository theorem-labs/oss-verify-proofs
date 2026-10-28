(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_entry Sj_num_iface Sj_stage2_numa Sj_stage2_numo Sj_stage2_main.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Main2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis HSLOWF : slowfu_stmt_g usegs 0x5edf4 0x111000.
  Hypothesis HPFF : pffu_stmt_g usegs 0x5eea4 0x111000.
  Hypothesis HROOM : (e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E))%Z.
  Variable Q : machine_state -> Prop.
  Hypothesis KX : forall tws sbs, exit_k (s2_ghost E tws sbs) Q.
  Variable h0 : Z.
  Hypothesis ROOTNUM : is_numstart (e_tok E 0) = true -> rootprim_k (s2_ghost E [h0] []) Q 0x43a30.

  Lemma vexp_W : forall s, vexp E s -> (0 <= k s <= e_n E)%Z /\ (0 <= W s)%Z /\ (W s + 2 <= e_tcap E)%Z.
  Proof using OK.
    intros s (HK & HW & _). pose proof (n_le_len _ _ (ok_s1 _ OK)). pose proof (ok_tcap _ OK). lia.
  Qed.

  Theorem s2_main2 : forall docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 (s2_ghost E [h0] []) docv fc m1 ->
    evt usegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x4370c) fc None m1 (seg_rom usegs)).
  Proof using OK HSLOWF HPFF HROOM KX ROOTNUM.
    apply (s2_main E OK Q KX).
    - intros tws sbs s HV GLT KC. destruct (vexp_W s HV) as (HK & HW0 & HW).

      exact (seg_numa (s2_ghost E tws sbs) (env_ok_ghost _ _ _ OK) HSLOWF HPFF HROOM Q s HK HW0 HW GLT (KX tws sbs) KC).
    - intros tws sbs s HV GLT KC. destruct (vexp_W s HV) as (HK & HW0 & HW).
      exact (seg_numo (s2_ghost E tws sbs) (env_ok_ghost _ _ _ OK) HSLOWF HPFF HROOM Q s HK HW0 HW GLT (KX tws sbs) KC).
    - exact ROOTNUM.
  Qed.
End Main2.
