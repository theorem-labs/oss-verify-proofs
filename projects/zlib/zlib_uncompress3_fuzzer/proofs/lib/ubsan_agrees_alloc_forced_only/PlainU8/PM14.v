(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM18.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM20.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RASlot_W2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RASlot_W4.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require RF_enframe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W18.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06. Import MM06. Import MM06.ASlot_W18.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3. Import PM20. Import PM20.RF_ntf_A. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RASlot_W4.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rmrep_set_free_head : forall st m v,
  rmrep st m ->
  rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (RCTX + 16)) (le8 (pw st v))).
Proof.
  intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (pw st v)) as L8.
  pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
  - left.
    pose proof (rw_cells_write (run_segments psegs rc_inp rc_sp rc_mb) m RCTX (rctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
    cbn [cbytes cell_upd rctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
    unfold rctx_head_cells, rsecw, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    exact W.
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

Lemma rmrep_extW : forall stX stY m,
  rmrep stX m ->
  s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
  s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
  s_statics stY = s_statics stX ->
  rmrep stY m.
Proof.
  intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - exact (rregions_wf_restatics stX stY ER EA EG ERs WF).
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

End CANSEC1.
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
      apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section CANSEC2.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
  (spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.

Lemma rfailm1_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  ATOP <= bv_unsigned sp - 144 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a1' s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1bcf8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b8f0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. unfold RCTX, RMLOCK, rta_frame in *. atop_facts.
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 607736) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1b94c) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 CAN; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 607736) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b8f0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros W HW1 HW2.
    pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    lazymatch type of CH with rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; ftauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono (run_segments psegs rc_inp rc_sp rc_mb) m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    step. st1. step. st1. step. st1. step. st1. step. st1.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; ftauto]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 CAN; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; ftauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  -
    destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (607744 + 16, 607744 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; ftauto|]. cbv beta.
    intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  -
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (607744 + 16, 607744 + 24)]%Z); cbn; ftauto|]. cbv beta.
    intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    step.
    pose proof MR1 as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (607736 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (607744 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
Lemma rfailm2_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  ATOP <= bv_unsigned sp - 144 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1bcf8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bc70) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. unfold RCTX, RMLOCK, rta_frame in *. atop_facts.
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 607736) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1bcc8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 CAN; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 607736) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bc70) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros W HW1 HW2.
    pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    lazymatch type of CH with rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; ftauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono (run_segments psegs rc_inp rc_sp rc_mb) m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    step. st1. step. st1. step. st1. step. st1. step. st1.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; ftauto]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 CAN; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; ftauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  -
    destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (607744 + 16, 607744 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; ftauto|]. cbv beta.
    intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    step.
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  -
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (607744 + 16, 607744 + 24)]%Z); cbn; ftauto|]. cbv beta.
    intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; ftauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    step.
    pose proof MR1 as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (607736 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (607744 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.
End CANSEC2.
End RASlot_W18.

Module RF_malloc_bigw.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.F_malloc_bigw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM21.RF_mm_syscalls. Import PM22.RMallocKit_A. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import RF_enframe. Import PM03. Import PM03.RMallocKit_A2.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
      apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (x + o) [b8 0]) -> bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m x (zeros k).
Proof.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.

Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

Lemma rbig_word_eq rid n : 0 <= n < 2^32 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof.
  intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
  rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma rbig_fail1_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
                        /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b1c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma rbig_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
                        /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b38c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma rbig_fail2a_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m RMLOCK [C4 (wz 0)] ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1b38c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b2b4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros LK. unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x1b380)) with (Z_to_bv 64 0x1b380) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x1b2b4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
                  a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
    /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -48)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ rmrep st' m'.

Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> ATOP <= lo -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b1c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until st. intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *. atop_facts. unfold ctx_tail_cells in C6.
  replace (607744 + 912) with 608656 in C6 by reflexivity. replace (607744 + 848) with 608592 in US by reflexivity.
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  step. rewrite ?zxb_b8 by lia. step.
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk (run_segments psegs rc_inp rc_sp rc_mb) mj lo (bv_unsigned sp + -48) -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mj ->
    munch [(607744 + 848, 607744 + 880); (607744 + 912, 607744 + 913)]%Z m mj -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m mj ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 607736)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b2ac) fc None mj (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (607744 + 912) with 608656 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 608656) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (607744 + 912) [b8 ns] FRj STj MUj WMj SOK.
    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  -
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  -
    pose proof (rw_cells_of_u8arr (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr (run_segments psegs rc_inp rc_sp rc_mb) m1 608592 (zeros 32)).
    { apply (u8arr_of_rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 608592 32). apply (rw_cells_congr (run_segments psegs rc_inp rc_sp rc_mb) m1 608592 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (607744 + 912) with 608656 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono (run_segments psegs rc_inp rc_sp rc_mb) m ?mX, FRc : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -48) _, STc : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX _ _, MIc : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : ATOP <= lo.

Lemma rbig_succ_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1b44c) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -48)
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b2b4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; atop_facts; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  unfold RCTX, RMLOCK in *. atop_facts.
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  unfold rctx_head_cells, rsecw in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix (run_segments psegs rc_inp rc_sp rc_mb) m _ [C8 (wz (SECRET * c_init_done (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  step. step.
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  step. rewrite (sx32_wz_sxv c) by lia. step.
  lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 607744 _ |- _ =>
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 607756) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (607744 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
End SUCC.
End CANSEC1.
End RF_malloc_bigw.
