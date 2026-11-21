(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM05.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RF_enframe.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RF_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RF_malloc_small.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM20.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM18.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RASlot_W2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RASlot_W4.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require RASlot_W3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require PM15.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W9.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07. Import MM07. Import MM07.ASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.ASlot_W3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM04. Import MM04. Import MM04.ASlot_W4. Import MM04.ASlot_W5. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06. Import MM06. Import MM06.ASlot_W6. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM05. Import MM05. Import MM05.ASlot_W7. Import MM06.ASlot_W8. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W9. Import MM06.F_ntf_C.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM21.RF_mm_syscalls. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RF_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RF_malloc_entry. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RF_malloc_small. Import PM20. Import PM20.RF_ntf_A. Import PM20.RF_ntf_C. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RASlot_W4. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RASlot_W3.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ RCTX <= a < RCTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. intros; left; assumption. Qed.
Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. intros; right; left; assumption. Qed.
Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. intros; do 2 right; left. exists q; auto. Qed.
Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. intros; do 3 right. exists b, gh; auto. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
  rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' -> stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo spv ->
  rpres_except (rta_fp st lo spv) m m' ->
  rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
  rmrep stX mZ -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mZ -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mZ (spv + -144) (FRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_fin stX g3 msk K) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x1b5a8) fc None mZ (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
  destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds st m g3) as GB0.
  pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
  unfold ta_fin. riprefixT. unfold RR, rt1_regs.
  eapply evt_mono.
  { eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
    rewrite unsigned_lit by lia. symmetry; exact ECONC. }
  cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
  assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
  eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
  eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
  cbn [ivs_covered]. split; [|split; [|exact I]].
  - intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
  - intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  (pc = 0x1b524 \/ pc = 0x1b530) ->
  ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
  rmrep stZ mZ -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mZ -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mZ (spv + -144) (FRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_avz K bail stZ g3) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
  destruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  unfold ta_avz, activate_group.
  destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
  apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
  rewrite EM, Hmem. cbn [default].
  replace (group_active_idx stZ b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
  destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
  apply Z.eqb_neq in MZ.
  rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
  assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; exact Hmem).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  unfold RR.
  eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b530) fc None mZ (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { destruct PC as [-> | ->].
    - eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [exact HG| exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
    - apply evt_done. eexists. reflexivity. }
  intros ms0 [a1x ->].
  riprefixT. eapply evt_mono.
  { eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| exact SC| exact HG| exact MIZ].
    intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
  cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
  set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
  set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
  assert (TR4 : ta_rel sc st st4).
  { eapply ta_rel_trans; [exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
    - repeat split; reflexivity.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
      apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
      destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
      pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (Z.ldiff_nonneg f act). lia. }
  assert (TR5 : ta_rel sc st st5).
  { eapply ta_rel_trans; [exact TR4|]. unfold st5. apply ta_rel_decay.
    pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
  assert (FR5 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m5 (spv + -144) (FRM junk)).
  { eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX in *; lia. }
  assert (ST5 : stk (run_segments psegs rc_inp rc_sp rc_mb) m5 lo (spv + -144)).
  { eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply disjoint_high; [|lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX in *; lia. }
  eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
    [exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
  - unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
  - unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
  - pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
  - eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    + intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
    + intros x Hx. apply rta_fp_ctx. unfold RCTX in *. atop_facts. lia.
Qed.

Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
  msk = m_freed (get_meta_rec stY g2) ->
  (forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
  m_next (get_meta_rec stY g2) <> None ->
  rmrep stY mY -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mY -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mY (spv + -144) (FRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) mY lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mY ->
  rimplT o (ta_act sc K bail stY g2 msk) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0x1b4fc) fc None mY (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
  destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
  assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  unfold ta_act. rewrite EMb. cbn [default].
  replace (group_active_idx stY b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold RR.
  destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
  -
    apply Z.eqb_eq in ZR.
    destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
    cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
    +
      apply aptr_eqb_eq in EQ. subst mn.
      destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
      *
        assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
        { destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
        assert (MZ : msk = 0).
        { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
          destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
          assert (IL : i <= m_last_idx (get_meta_rec st g2)).
          { pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
            apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
          assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
          { rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
            rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
          rewrite ZR, Z.bits_0 in TB2. discriminate. }
        cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
        destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
        cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
      *
        destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
        2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
        apply Z.eqb_eq in AV0.
        assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
        rewrite <- ECONC. riprefixT. eapply evt_mono.
        { eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
          intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
        cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
        cbv zeta iota beta.
        match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
        assert (TRG : ta_rel sc st stG).
        { eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
          - apply land31_range.
          - intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
        rewrite (tr_conc _ _ _ g2 TR).
        eapply (ravz_block 0x1b530 stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
        -- unfold stG. rewrite active_set_gai. exact HA.
        -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; atop_facts; lia.
        -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; atop_facts; lia.
        -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
           cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
    +
      assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
      pose proof (GN mn eq_refl) as GMn.
      destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
      rewrite <- ECONC. riprefixT. eapply evt_mono.
      { eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
      cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
      assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
      rewrite ECONCn.
      eapply (ravz_block 0x1b524 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
      -- rewrite active_set_active, Z.eqb_refl. reflexivity.
      -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
      -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
      -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
         cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. atop_facts. lia.
  -
    apply Z.eqb_neq in ZR.
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
    cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
    eapply (ravz_block 0x1b524 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
  rmrep stX mX -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (spv + -144) (FRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) mX lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mX ->
  rimplT o (ta_m sc K bail stX g1) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x1b4d0) fc None mX (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
  destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
  destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
  unfold ta_m, RR.
  set (f := m_freed (get_meta_rec stX g1)).
  destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
  -
    pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
    rewrite GN1.
    destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
    destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
    assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
    rewrite ECONCn.
    eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + reflexivity.
    + intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
    + rewrite rec_set_active, GN2. discriminate.
    + eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
    + eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
    + eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. atop_facts. lia.
  -
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
    eapply (ract_block stX g1 f mX); try eassumption.
    + reflexivity.
    + intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
    + rewrite GN1. discriminate.
Qed.

Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
  a0 = Z_to_bv 64 sc ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> stk (run_segments psegs rc_inp rc_sp rc_mb) m lo spv ->
  (forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
     ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
     rmrep st1 m' -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (spv + -144) (FRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (spv + -144) ->
     rpres_except (rta_fp st lo spv) m m' ->
     rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0x1b5e8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  rimplT o (try_avail sc st K bail) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until a7. intros A0 MR MI ST HK0.
  assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
  riprefixT. eapply evt_mono.
  { eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
  cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
  assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
  { eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
  clear MU1 WM1.
  rewrite (try_avail_eq sc K bail st).
  destruct (active st sc) as [g|] eqn:HA.
  2:{
      eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      unfold ta_fail, try_avail. rewrite HA. reflexivity. }
  destruct (taf_head _ _ TAF g HA) as [GM GSC].
  pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
  pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
  unfold pw. cbn [oconc]. unfold wz.
  destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
  2:{
      apply Z.eqb_neq in AV.
      riprefixT. eapply evt_mono.
      { eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
      cbv beta. intros ms' ->.
      eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
  apply Z.eqb_eq in AV.
  destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
  destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
  destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
  destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
  -
    apply Z.eqb_eq in FZ.
    riprefixT. eapply evt_mono.
    { eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' ->.
    destruct (decide (nx = g)) as [->|NEn].
    +
      rewrite (dequeue_self_eq sc g st GN).
      replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
        by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
      cbn [Z.eqb].
      riprefixT. eapply evt_mono.
      { eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
      cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
      eapply (HK0 _ m2).
      * unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
        rewrite (dequeue_self_eq sc g st GN).
        change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
        replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
      * change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * exact MR2.
      * exact MI2.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
    +
      assert (NEp : pv <> g).
      { intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
      rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
      match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
      assert (HA1 : active st1 sc = Some nx).
      { unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
      rewrite HA1.
      pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
      riprefixT. eapply evt_mono.
      { eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
      cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
      assert (TR1 : ta_rel sc st st1).
      { unfold st1.
        lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
          lazymatch sC with set_active _ _ ?sB =>
            lazymatch sB with put_meta _ _ ?sA =>
              apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
              unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
            end end end.
        rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
        rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
      assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
                 if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
                 else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
      { intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
        rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
        - apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
        - rewrite get_meta_rec_put. reflexivity. }
      eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
      * intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
        destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
        destruct (aptr_eqb q nx) eqn:E1.
        -- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
           destruct (aptr_eqb nx pv) eqn:E2.
           ++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
              rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
        -- destruct (aptr_eqb q pv) eqn:E2.
           ++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
              rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
          [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
  -
    apply Z.eqb_neq in FZ. rewrite GN.
    riprefixT. eapply evt_mono.
    { eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
    eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
    + apply ta_rel_set_active.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
      exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
    + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX in *; lia.
    + eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. atop_facts. lia.
Qed.
End PHASE.

End CANSEC1.
End RASlot_W9.

Module RASlot_M2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W9. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01. Import MM01. Import MM01.ASlot_M0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import RASlot_W4. Import RASlot_W9. Import PM11. Import PM11.RASlot_W12. Import PM15. Import PM15.RASlot_W19. Import PM03.RASlot_M0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01. Import MM01.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
  mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Definition rHAG_stmt : Prop :=
  forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
  IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
  am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
  rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m3 -> stk (run_segments psegs rc_inp rc_sp rc_mb) m3 lo (bv_unsigned sp + -144) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m3 (bv_unsigned sp + -144) (rFRM junk) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
  brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  rimplT o (ag_body f sc req k bail st2 mm) s' Q
    (MS (rag_regs (Z_to_bv 64 0x1b600) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
        F (Z_to_bv 64 0x1b60c) fc None m3 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Hypothesis HAG : rHAG_stmt.

Lemma rerrno_lit2 : errno_addr tp = 0x741cc.
Proof. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rta_fp_malloc_fp stE mE a :
  rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
  rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
  intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - left. left. exact X.
  - left. right. right. left. exact X.
  - left. do 3 right.
    pose proof (AREAS q MSq) as MSq'.
    destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
    exists rid0, r0. split; [exact H0|]. split; [exact K0|].
    rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
  - do 3 right. left. pose proof MR as (WF & _).
    destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct ER as [_ EG EGR _ _ _ _ _].
    destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
    exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
    rewrite Cb in Xq. lia.
Qed.

Lemma rta_fp_not_image a : 0x10000 <= a < 0x95000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - atop_facts. lia.
  - exact (Hc X).
  - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
  - pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
    destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
  pose proof (RAS_STACK_ge sc) as ASG. atop_facts.
  intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - unfold RCTX in X. lia.
  - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
  - pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). atop_facts. lia.
Qed.

Lemma runk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

Lemma rta_fp_not_inband rid r off :
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
  ~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). atop_facts.
  intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
  - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
  - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct (N.eq_dec (fst bq) rid) as [E|NE].
    + apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  rmrep st1 m1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -144) (rFRM junk) -> stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -144) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
  rimplT o (as_grp full_lay f sc req k bail st1) s Q
    (MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b5e8) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. atop_facts.
  pose proof rerrno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  rewrite (as_grp_eq f sc req k bail st1).
  riprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
  { apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| atop_facts; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply rta_fp_not_high. exact Ha.
    - intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
  assert (ERR2 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
  eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x1b600)) with (Z_to_bv 64 0x1b600) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x95000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x741cc <= a < 0x741d0)) ->
            ~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold RCTX in *. atop_facts. lia.
    - destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). atop_facts.
      pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. atop_facts.
      pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact (rstatics_reserved _ RS))). lia. }
  assert (FR3 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
  assert (REL02 : mrel st st2).
  { split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
    intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
  assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
  { intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
    exists ar, arr', kk. auto. }
  assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
    - eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
      + left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
      + do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
        * rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
        * intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }
  assert (UA3 : unk_agree st2 o m3).
  { eapply (runk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). atop_facts.
      transitivity (m1 (wa (r_base r + off))).
      + refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
        * lia.
        * rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
          specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
        * destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
        * assert (Hr2 : (s_regions st2) !! rid = Some r).
          { rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
          assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
          pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
        * rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
      + refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
  destruct mo as [mm|].
  -
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [atop_facts; lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  -
    cbn iota.
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
    cbv beta. intros ms' ->. cbn [Z.eqb].
    eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
    cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
    apply HK. unfold ras_post2.
    do 14 eexists. exists m3, errv3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
    split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
    split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
    split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
             pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
    left. reflexivity.
Qed.
End LEVEL.
End CANSEC1.
End RASlot_M2.
