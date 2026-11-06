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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act El_a23.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis THROW : throw_slot 0x3c458 0x3bed8.

  Theorem arm23_proof : arm_stmt 23 0x3bed0.
  Proof.
    unfold arm_stmt. intros until p50. intros EA AE HK.
    pose proof AE as AE'.
    destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                     & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).

    unfold el_act, el_throwing. rewrite EA. cbn [Z.eqb Pos.eqb orb].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix.

    step. step.
    eapply evt_cut.
    { eapply (begin_spec E OK) with (s := st) (lo := lo); [exact AI| exact ROOT| exact HEAP| exact MI| exact ST| rewrite ELO; lia| lia| rewrite EB; lia
        | clear - AL16; replace sp0 with (sp0 + 528 + (-33) * 16) by lia; rewrite Z.mod_add by lia; exact AL16| lia| rewrite EB; lia]. }
    cbv beta. intros ms2 PO. unfold arr_iter_post in PO.
    destruct PO as [(u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & TY)|(u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & junk & -> & FR2 & MU2 & WM2 & MI2 & ST2 & TY)].
    -
      replace (ret_pc (Z_to_bv 64 0x3bed8)) with (Z_to_bv 64 0x3bed8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step.
      ihere. to_implM. cbn [bind ret lib_malloc lib_free lops Target.ops cho]. apply implM_bind_assoc. apply (implM_chok psegs 0). cbn [Z.eqb]. apply implM_ret_bind. apply HK. unfold EL_EXIT in *.
      eapply act_post_here; [exact AE| reflexivity| reflexivity].
    -
      ihere. to_implM. cbn [bind ret lib_malloc lib_free lops Target.ops cho]. apply implM_bind_assoc. apply (implM_chok psegs 1). cbn [Z.eqb Pos.eqb]. apply implM_bind_assoc.
      replace (sp0 - 16) with (sp0 + -16) in MU2 by lia.
      eapply THROW; [exact AE| replace (sp0 - 16) with (sp0 + -16) by lia; exact MU2| exact WM2| exact MI2| exact ST2| exact FR2| exact HK].
  Qed.
End Proofs.
End WithCeiling0.
