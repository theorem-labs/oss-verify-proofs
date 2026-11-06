(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs El_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section A08.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition getdbl_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m (seg_rom psegs)
      /\ frm0 fc'.

  Ltac zland HK := try rewrite land64_mod in HK; try rewrite Z.mod_mod in HK by lia.
  Ltac fin FRM := apply evt_done; unfold getdbl_post; do 15 eexists; eexists; eexists; split; [cbv delta [mkR]; reflexivity| first [exact FRM| apply frm0_slice_set_fflags; exact FRM| idtac]].

  Lemma getdbl_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> frm0 fc -> mem_inv psegs m -> 0 <= node -> node + 16 < 2^64 ->
    evt psegs (getdbl_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_GETDBL) fc None m (seg_rom psegs)).
  Proof.
    intros until node. intros AI ROOT HEAP FRM MI N0 N1.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (el_root_elem E OK) as [EL NR].
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_GETDBL.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) ltac:(destruct WF as (_ & ? & _); lia)) as TIR.

    step. step. step. astep. astep.

    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    astep.

    astep. astep.
    zstep. if_cases HK; zify_cond HK; zland HK.
    -
      astep. astep. zstep. if_cases HK2; zify_cond HK2; zland HK2.
      +
        astep. astep. zstep. if_cases HK3; zify_cond HK3; zland HK3.
        *
          astep. step. step. fin FRM.
        *
          pose proof (el_word_eq E OK _ _ _ t_i64 EL ltac:(lia) ltac:(lia) ltac:(exact HK3) ltac:(auto)) as J3.
          pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
          replace (ae_TAPE E + 8 * 2) with (ae_TAPE E + 8 + 8) in RDT2 by lia.
          astep. astep. step. step. fin FRM.
      +
        pose proof (el_word_eq E OK _ _ _ t_u64 EL ltac:(lia) ltac:(lia) ltac:(exact HK2) ltac:(auto)) as J3.
        pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
        replace (ae_TAPE E + 8 * 2) with (ae_TAPE E + 8 + 8) in RDT2 by lia.
        astep. astep. step. step. fin FRM.
    -
      pose proof (el_word_eq E OK _ _ _ t_dbl EL ltac:(lia) ltac:(lia) ltac:(exact HK) ltac:(auto)) as J3.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
      replace (ae_TAPE E + 8 * 2) with (ae_TAPE E + 8 + 8) in RDT2 by lia.
      step. astep. step. fin FRM.
  Qed.
End A08.
End WithCeiling0.
