(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W9.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_malloc_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module RASlot_W2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 ssp_guard_val; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk usegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono usegs m0 m ->
  evt usegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom usegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x179c4) fc None m (seg_rom usegs)).
Proof using .
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Lemma rfin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk usegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17304) fc None m (seg_rom usegs)).
Proof using CLO MASK MR MSL.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  unfold alloc_ceiling, rta_frame, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl usegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells usegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr usegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tclose ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
  (* [comment removed for export] *)
  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM]. }
  cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.


End CeilWrap.
End RASlot_W2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W11.
Module RASlot_W11.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 RASlot_W2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsmall_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RSMALL_CNT 27 return list byte with Some bs => bs | None => [] end).  (* [comment removed for export] *)
Definition rmed_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RMED_CNT 4 with Some bs => bs | None => [] end).

Lemma rsmall_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof using . intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
Lemma rmed_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof using . intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.

Lemma rsmall_cnt_read : forall m sc i, mem_inv usegs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
  ov_read_bytes usegs m (wa (RSMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof using .
  intros m sc i MI Hsc Hi.
  destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
  rewrite (bytes_at_read usegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
  unfold small_cnt. rewrite !Nat2Z.id.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

Lemma rmed_cnt_read : forall m i, mem_inv usegs m -> 0 <= i < 4 ->
  ov_read_bytes usegs m (wa (RMED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof using .
  intros m i MI Hi.
  destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read usegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' a3',
      ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x17408) fc None m (seg_rom usegs))
    (MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x173f4) fc None m (seg_rom usegs)).
Proof using SZ.
  induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
  - cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
    step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
    apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
  - cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
    assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
    step. rewrite (unsigned_lit (size * cnt)) by lia.
    step. rewrite (wz_unsigned cnt) by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    + (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
      rewrite (F_malloc_entry.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
      apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
    + rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
      apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
  intros H.
  assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|NE].
    - change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
    - replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
      rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
  rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x173f4) fc None m (seg_rom usegs))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x173cc) fc None m (seg_rom usegs)).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
  - change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
  - cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
    assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
      step. apply evt_done. do 2 eexists. reflexivity.
    + replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned cnt) by lia. rewrite (F_malloc_entry.srliw_small cnt 1) by lia.
      step. rewrite (wz_unsigned cnt) by lia. step.
      assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* [comment removed for export] *)
        assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
        assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
        { rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
        change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
        apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
      * (* [comment removed for export] *)
        step.
        assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
        replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
        apply evt_done. do 2 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x173f4) fc None m (seg_rom usegs))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x173c4) fc None m (seg_rom usegs)).
Proof.
  intros until m; intros CR C32 MI; unfold rcnt_regs.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt) by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
  - (* [comment removed for export] *)
    assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
    replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
    step. step. apply evt_done. do 2 eexists. reflexivity.
  - assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
    destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
    apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof using SC size u.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
      first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
  - pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

Lemma rcount_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
  mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' a3' a4',
      ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x17408) fc None m (seg_rom usegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
             (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17368) fc None m (seg_rom usegs)).
Proof using MR SC UR.
  intros until fc. intros MI.
  pose proof (size_class_range sc SC) as SZR.
  pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
  pose proof rcnt0_range as C0R.
  unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m sc (wa (347344 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
  step. clear RDU.
  (* [comment removed for export] *)
  step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
  - (* [comment removed for export] *)
    apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
    step. clear RDM. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
    eapply evt_mono.
    { eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
  - (* [comment removed for export] *)
    assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
    unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
    pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
    replace (wa (67800 + 3 * sc + 0)) with (Z_to_bv 64 (67800 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
    step. clear RD0. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
    { replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
    replace (wa (67800 + 3 * sc + 1)) with (Z_to_bv 64 (67800 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
    step. clear RD1. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
    { replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
    replace (wa (67800 + 3 * sc + 2)) with (Z_to_bv 64 (67800 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
    step. clear RD2. rewrite zxb_b8 by lia. step.
    apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Lemma rcnt2_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 (if big then 0x17430 else 0x17474)) fc None m (seg_rom usegs))
    (MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17408) fc None m (seg_rom usegs)).
Proof using C0 SZ.
  intros until m. intros MI. unfold rcnt_regs.
  assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
  pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
  assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?unsigned_lit by lia. step. step.
    assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
    { unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
      destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
    assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
    { rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
      destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
    rewrite EV. clear EV.
    assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.


End CeilWrap.
End RASlot_W11.

(* [comment removed for export] *)
Module RASlot_W19.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk usegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  evt usegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m (seg_rom usegs)
      /\ stk usegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x179c4) fc None m (seg_rom usegs)).
Proof using .
  intros until lo. intros MR' MI FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.


End CeilWrap.
End RASlot_W19.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RASlot_W4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3.
Import RASlot_W2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

Lemma ras_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  a0 = Z_to_bv 64 sc ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' : word) m' junk,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 ssp_guard_val a1' (pw st (active st sc)) a3 a4 a5 a6 a7
                   a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (match active st sc with None => 0x17344 | Some _ => 0x171c8 end)) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk usegs m' lo (bv_unsigned sp + -144)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep st m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof using AMS CLO MR SC.
  intros until fc. intros HA ST LO MI. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _). unfold wz in G4.
  unfold ralloc_slot_entry, alloc_ceiling, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step.
  rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]) end.
  pose proof (rmrep_active_read st _ sc (wa (347344 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
  step. clear RDA.
  (* [comment removed for export] *)
  step.
  replace (347336 + sc * 8 + 88) with (347344 + 80 + 8 * sc) by lia.
  replace (347336 + sc * 8) with (347336 + 8 * sc) by lia.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K.
  - destruct (active st sc) as [g|] eqn:HA.
    { exfalso. (nelimp (rmeta_slot_bounds st m g MR (AMS g eq_refl)) 3%nat; intros Gpos GC _).
      unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
    apply evt_done. nexists 3%nat. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
  - destruct (active st sc) as [g|] eqn:HA.
    2:{ exfalso. apply K. reflexivity. }
    apply evt_done. nexists 3%nat. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

(* [comment removed for export] *)
Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
      (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma rt1_fin_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr <> 0 -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17304) fc None m (seg_rom usegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171c8) fc None m (seg_rom usegs)).
Proof using AVR MR MSL.
  intros until fc. intros AVNZ MI. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
  pose proof (sxv_range (m_avail mr)) as RA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
  { exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
  step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt1_deq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr = 0 -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x171ec) fc None m (seg_rom usegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171c8) fc None m (seg_rom usegs)).
Proof using MR MSL.
  intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. unfold pw, wz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt1_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1722c) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_active sc (m_next mr) st) m')
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171c8) fc None m (seg_rom usegs)).
Proof using FRR MR MSL SC.
  intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
  pose proof (sxv_range (m_freed mr)) as RF.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. step.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
  { exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (347344 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

(* [comment removed for export] *)
Lemma rdeq_self_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_next mr = Some g -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17344) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171ec) fc None m (seg_rom usegs)).
Proof using MR MSL SC.
  intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step.
  (* [comment removed for export] *)
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (347344 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
  set (st1 := set_active sc None st) in MR1.
  assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).
  (* [comment removed for export] *)
  rmeta_open G MUg WMg.
  rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
  st1. st1.
  rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read _ _ sc (wa (347344 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

(* [comment removed for export] *)
Lemma rdeq_other_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
  m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  mem_inv usegs m ->
  let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
  let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
  let st3 := set_active sc (Some nx) st2 in
  let st4 := put_meta g (clr mr) st3 in
  evt usegs (fun ms' => exists (a1' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1722c) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep st4 m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171ec) fc None m (seg_rom usegs)).
Proof using HA MR MSL SC.
  intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rmeta_slot_bounds st m nx MR MSn) 5%nat; intros Npos NC NI _ _).
  (nelimp (rmeta_slot_bounds st m pv MR MSp) 5%nat; intros Ppos PC PI _ _).
  assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  step. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st pv) MUp WMp.
  rmchunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  (* [comment removed for export] *)
  rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. step. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st nx) MUn WMn.
  rmchunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st2 _ sc (wa (347344 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
  unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. clear CH. step.
  (* [comment removed for export] *)
  pose proof MR2 as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st2) sc (wa (347344 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
  fold st3 in MR3.
  assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).
  (* [comment removed for export] *)
  rmeta_open G MUg WMg.
  rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
  replace (get_meta_rec st3 g) with mr in CH.
  2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1.
  rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read _ _ sc (wa (347344 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
  change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

(* [comment removed for export] *)
Lemma rm_act_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  full_skip st g = false -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17258) fc None m (seg_rom usegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1722c) fc None m (seg_rom usegs)).
Proof using FRR MR MSL MW.
  intros until fc. intros NSK MI. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  pose proof (meta_word_range _ MW) as MWR. (nelimp MW 4%nat; intros LI FB SCR ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *) apply evt_done. do 2 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  { apply evt_done. do 2 eexists. reflexivity. }
  exfalso. unfold full_skip in NSK. fold mr f in NSK.
  assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
  rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

(* [comment removed for export] *)
Lemma rm_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
  full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
  0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17258) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_active sc (Some mn) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1722c) fc None m (seg_rom usegs)).
Proof using FRR MR MSL MW SC.
  intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rmeta_slot_bounds st m mn MR MSn) 5%nat; intros Npos NC NI _ _).
  pose proof (meta_word_range _ MW) as MWR. (nelimp MW 4%nat; intros LI FB SCR ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
  apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.
  (* [comment removed for export] *)
  step. clear CH.
  (* [comment removed for export] *)
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (347344 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
  rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
  step. rewrite sx32_wz_sxv by lia.
  apply evt_done. nexists 3%nat. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.


End CeilWrap.
End RASlot_W4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W13.
Module RASlot_W12.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W13.ASlot_W12.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 RASlot_W2 RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma rag_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rt1_regs sc (Z_to_bv 64 0x1735c) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
                   (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17344) fc None m (seg_rom usegs)).
Proof using SC.
  intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (size_class_range sc SC) as SZR.
  step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
  pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (67704 + 2 * sc) with (67704 + sc * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  step. apply evt_done. reflexivity.
Qed.
End AG1.

(* [comment removed for export] *)
Lemma rag_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
  0 <= gm < 2^64 -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if gm =? 0 then 0x179c4 else 0x17368)) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1735c) fc None m (seg_rom usegs)).
Proof using .
  intros until gm. intros GR MI.
  step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
  - replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof using CR SMALL SZC.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.


(* [comment removed for export] *)
Lemma rnest_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' a3' a4',
      ms' = MS (mkR (Z_to_bv 64 0x17544) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17474) fc None m (seg_rom usegs)).
Proof using CR SMALL SZC.
  intros until m. intros MI.
  assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
  set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
  pose proof rstc_q_eq as STC. fold q in STC.
  unfold RSIZE_CLASSES, ralloc_slot_entry in *.
  (* [comment removed for export] *)
  assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
    evt usegs (fun ms' => exists a2'' a3'' a4'',
      ms' = MS (mkR (Z_to_bv 64 0x17544) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 67704) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 94564) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 67704) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17538) fc None m (seg_rom usegs))).
  { intros a0' a2' a3' jv ->.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
    step. rewrite SysStep.sextw_small by lia. step. step.
    apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
  step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
  - (* [comment removed for export] *)
    apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (unfold n' in K; nia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
    assert (K13 : 3 <= k <= 12).
    { unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (67704 + (i + 1) * 2) with (67704 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt usegs (fun ms' => exists a2'' a3'' a4'',
        ms' = MS (mkR (Z_to_bv 64 0x17544) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 67704) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 94564) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 67672) (Z_to_bv 64 q) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 67704) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1751c) fc None m (seg_rom usegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (67704 + i1 * 2) with (67704 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.
(* [comment removed for export] *)
Lemma rnest_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
  -1 <= idx < 32 -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if idx =? -1 then 0x175bc else 0x17548)) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17544) fc None m (seg_rom usegs)).
Proof using .
  intros until idx. intros IR MI.
  step. if_cases K; zify_cond K.
  - replace (idx =? -1) with true.
    2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
        change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
    apply evt_done. reflexivity.
  - replace (idx =? -1) with false.
    2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
    apply evt_done. reflexivity.
Qed.


End CeilWrap.
End RASlot_W12.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W14.
Module RASlot_W13.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W13 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A RASlot_W2 RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

(* [comment removed for export] *)
Lemma rnenf_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
  0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv usegs m1 ->
  evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x17574) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x17574) fc None m' (seg_rom usegs)
      /\ munch [(P - 3, P)]%Z m1 m' /\ wmono usegs m1 m' /\ mem_inv usegs m'
      /\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17548) fc None m1 (seg_rom usegs)).
Proof using HA J MR MSL MW SCg SO STR TK UA.
  intros until fc. intros CTR MI.
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  (nelim (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0) 13%nat; intros x3 x2 x1 WRs Y E3 E2 E1 CB R4 PEND RC RI1)
.
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  (nelimp (rmeta_chunk_facts st m1 g MR MSL) 7%nat; intros MM G0 GC GI1 GI2 GDJ GRG).
  unfold alloc_ceiling in RC, GC.
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read usegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read usegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read usegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (nelimp MW 4%nat; intros LI0 FB0 SCR0 ML0).
  (nelimp MR 4%nat; intros WF' CX GL _). destruct CX as (CH & _). unfold rctx_head_cells in CH.
  unfold RSIZE_CLASSES, RMLOCK, RCTX in *.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  (* [comment removed for export] *)
  pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (67704 + 2 * j) with (67704 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st m1 j (wa (347344 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (347344 + 80 + 8 * j)) with (Z_to_bv 64 (347336 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  (* [comment removed for export] *)
  step.
  eapply evt_mono.
  { eapply (renframe_walk (Z_to_bv 64 0x17574) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  (nelim PO 18%nat; intros w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' -> EM MI').
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x17574)) with (Z_to_bv 64 0x17574) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  (nelim (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4) 5%nat; intros MRr TKr CONCr FSTr SNDr)
. clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  (* [comment removed for export] *)
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono usegs m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  nexists 14%nat. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
(* [comment removed for export] *)
Lemma rnoov16 (zb0 zb zs zx zi zc : Z) :
  zb0 = 16 * (zb0 / 16) -> zb = 16 * (zb / 16) -> zs = 16 * (zs / 16) ->
  ~ (zb0 <= zb + (16 + zs * zx) + (16 + zi * (16 * zc) - 4) < zb0 + 9).
Proof using N P.
  intros zE0 zE1 zE2 zC.
  assert (zE3 : zs * zx = 16 * ((zs / 16) * zx)) by (rewrite zE2 at 1; ring).
  rewrite zE3 in zC. replace (zi * (16 * zc)) with (16 * (zi * zc)) in zC by ring.
  set (zX := (zs / 16) * zx) in zC. set (zY := zi * zc) in zC.
  set (zq0 := zb0 / 16) in zE0. set (zq1 := zb / 16) in zE1.
  rewrite zE0, zE1 in zC. clearbody zX zY zq0 zq1. lia.
Qed.

Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof using N P. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

(* [comment removed for export] *)
Lemma renfD_walk :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
  meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
  rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv usegs mC ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1759c) fc None m' (seg_rom usegs)
      /\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono usegs mC m' /\ mem_inv usegs m'
      /\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
      /\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17574) fc None mC (seg_rom usegs)).
Proof using J MR SO TK.
  intros until mC. intros MST MWT CR MRC TKC MIC.
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  (nelimp (rregion_facts st m1 (fst b) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st st g b idx) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  (nelimp (rmeta_slot_bounds st0' mC mt MRC MST0) 5%nat; intros Tpos TC TI _ _).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  (nelimp (rmeta_chunk_facts st0' mC mt MRC MST0) 7%nat; intros _ _ _ _ _ GDJ _).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl usegs mC) as WM.
  (nelimp MWT 4%nat; intros LI0 FB0 SCR0 ML0). pose proof (meta_word_range _ MWT) as MWR.
  unfold alloc_ceiling in TC.
  (* [comment removed for export] *)
  rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  rmeta_open (conc st mt) MUt WMt.
  step.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 st g b idx j _ MWT).
  step.
  lazymatch goal with H : rw_cells usegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  (* [comment removed for export] *)
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  (* [comment removed for export] *)
  (nelimp MR5 6%nat; intros _ _ _ _ _ SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok usegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
(* [comment removed for export] *)
Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
  s_regions stz = s_regions st -> s_groups stz = s_groups st ->
  rmrep stz mC -> ticks_ok stz -> mem_inv usegs mC ->
  munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono usegs mC0 mC ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1786c) fc None m' (seg_rom usegs)
      /\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono usegs mC0 m' /\ mem_inv usegs m'
      /\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
      /\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
      /\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1759c) fc None mC (seg_rom usegs)).
Proof using MR STR SO.   (* [comment removed for export] *)
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  (nelimp (rregion_facts st m1 (fst b) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  (* [comment removed for export] *)
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  (nelimp MRz 6%nat; intros WFz _ _ _ _ SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok usegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). (nelimp WF 5%nat; intros _ _ _ _ GWF).
    (nelim (GWF b0 gh Hb0) 6%nat; intros r0 _ _ _ _ M16).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear M16 B16 SMOD. exact (rnoov16 _ _ _ _ _ _ E0 E1 E2 CONTRA). }   (* [comment removed for export] *)
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write usegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv usegs mX |- _ =>
        apply (mem_inv_store usegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. intros ms' nelH_; (nelim nelH_ 10%nat; intros m' -> X1 X2 X3 X4 X5 X6 X7 PW).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  - (* [comment removed for export] *)
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.


End CeilWrap.
End RASlot_W13.

(* [comment removed for export] *)
Module RASlot_W14.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A RASlot_W2 RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac step ::= step1.  Local Ltac stepz ::= step1.  (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof using .
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal. 
Qed.

Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
  (bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
  replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma unsigned_mod32_swrap_add_not a b :
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof using .
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition rtailW : list (Z * Z) :=
  [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

(* [comment removed for export] *)
Lemma rtail_walk :
  forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
  rmrep stT mC -> mem_inv usegs mC ->
  evt usegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x179c4) fc None m' (seg_rom usegs)
      /\ munch rtailW mC m' /\ wmono usegs mC m' /\ mem_inv usegs m'
      /\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1786c) fc None mC (seg_rom usegs)).
Proof using ACT AI CNT GNONE Hk Hr ML MST NOGRP OLD12 P0 P16 PEND REC SC TK UR.
  intros until mC. intros MR MI.
  pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl usegs mC) as WM. unfold rtailW in MU.
  (nelimp (rmeta_slot_bounds stT mC mt MR MST) 5%nat; intros Gpos GC GI G4 _). fold G in Gpos, GC, GI, G4.
  (nelimp (rregion_facts stT mC (fst p) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  (nelimp (AV_FR_range stT cnt ai mt p CNT AI P0) 3%nat; intros AVR FRR AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
  (* [comment removed for export] *)
  destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
  unfold RCTX, RMLOCK, alloc_ceiling in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read (stA stT p) mC sc (wa (347344 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage (stA stT p) sc) with (usage stT sc) in RDU.
  replace (wa (347344 + 464 + 8 * sc)) with (Z_to_bv 64 (347336 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
  (* [comment removed for export] *)
  pose proof MRA as (_ & (_ & _ & USG & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (usages (stA stT p)) sc (wa (347344 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (347344 + 464 + 8 * sc)) with (Z_to_bv 64 (347336 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
  rraw_store_finish0 (347344 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
  assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  rmeta_open G MUa WMa.
  (* [comment removed for export] *)
  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
  assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.
  (* [comment removed for export] *)
  (nelimp MRC 6%nat; intros WFC _ _ _ _ SHC). (nelimp WFC 5%nat; intros _ _ DJ _ WG).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    (nelim (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) 3%nat; intros hb LHB HB) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells usegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  (nelimp (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) 7%nat; intros _ _ _ _ _ GRG _).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
  (* [comment removed for export] *)
  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
      [ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  { (* [comment removed for export] *)
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold RCTX in X1. lia.
    - unfold RMLOCK in X2. lia.
    - unfold RNEED_LOCKS in X3. lia.
    - unfold RPAGE_SIZE in X4. lia.
    - change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
      (nelim (rarea_conc stT ak ar WFC Hak) 8%nat; intros rga Hra Ca Sa0 Sa1 _ NK _).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
      (nelim (rgroup_conc stT b gh WFC Hb) 7%nat; intros rb Hrb Cb Kb Sb0 Sb1 _).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold RGOT_SSP in X5. lia.
    - unfold RSSP_GUARD in X6. lia. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
  assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.
  (* [comment removed for export] *)
  pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
  rmchunk MRD MSTD CH.
  change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  rmeta_open G MUc WMc.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read usegs mX (347344 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (347344 + 80 + 8 * sc)) H
                  (actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (347344 + 80 + 8 * sc)) with (Z_to_bv 64 (347424 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tclose. }
  assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
  clear MRD TKD MSTD.
  (* [comment removed for export] *)
  clear CH3.
  lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok usegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (347344 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (347344 + 80 + 8 * sc)) with (Z_to_bv 64 (347424 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (347424 + 8 * sc + 0)) with (Z_to_bv 64 (347424 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. nexists 6%nat. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
End TAIL.


End CeilWrap.
End RASlot_W14.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W15.
Module RASlot_W15.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A RASlot_W2 RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rbounce_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x176e4) fc None m' (seg_rom usegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17430) fc None m (seg_rom usegs)).
Proof using SC.
  intros until m. intros MR SEQ BR USR MI.
  pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl usegs m) as WM. unfold rseqW in MU.
  unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
    rmrep stX mX -> stX = account_bounce sc st -> mem_inv usegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
    munch [(347344 + 848, 347344 + 913)]%Z m mX -> wmono usegs m mX ->
    evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x176e4) fc None m' (seg_rom usegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch [(347344 + 848, 347344 + 913)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x176e0) fc None mX (seg_rom usegs))).
  { intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
    pose proof (rmrep_seq_read stX mX (wa (347344 + 912)) MRX eq_refl) as RDS.
    replace (wa (347344 + 912)) with (Z_to_bv 64 (347336 + 920)) in RDS by (unfold wa; f_equal; lia).
    assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
    { rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
      destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
    rewrite SQX in RDS.
    step. rewrite ?zxb_b8 by lia. clear RDS.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *)
    assert (HO : sc_in_seq_range sc = false).
    { unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
      - replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
        replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    step. step.
    eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
    - unfold account_bounce. rewrite HO. reflexivity.
    - unfold is_bouncing. rewrite HO. reflexivity. }
  rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
  destruct (Z.lt_ge_cases sc 7) as [L7|G7].
  { exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
  rewrite Z.mod_small in K by lia.
  assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc + -7)) by lia.
  pose proof (rmrep_bounces_read st m (sc - 7) (wa (347344 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
  replace (wa (347344 + 880 + (sc - 7))) with (Z_to_bv 64 (347336 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
  pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
  step. rewrite ?zxb_b8 by lia. clear RDB.
  pose proof MR as (_ & (_ & _ & _ & US & _) & _).
  pose proof (u8arr_read usegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (347336 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
                ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
  step. rewrite ?zxb_b8 by lia. clear RDU.
  (* [comment removed for export] *)
  step. step.
  set (nos := 100 <=? bounces st (sc - 7)).
  assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
  assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
  { rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    change (bv_wrap 64 100) with 100.
    destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
  rewrite A3. clear A3.
  assert (AB : account_bounce sc st =
    (if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
     then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
     else st)) by (unfold account_bounce; rewrite IN; reflexivity).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
  { eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (347344 + 912)) MR eq_refl) as RDS.
  replace (wa (347344 + 912)) with (Z_to_bv 64 (347336 + 920)) in RDS by (unfold wa; f_equal; lia).
  step. rewrite ?zxb_b8 by lia. clear RDS.
  step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
  step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in K2.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. exact MR. }
  apply Z.ltb_ge in K2.
  assert (AB2 : account_bounce sc st =
    (if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
  { rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  clear AB K1 K2.
  pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
  pose proof (u8arr_store_ok usegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (347336 + (sc + -7) + 888)) BA
                ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (347344 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. step. st1. rewrite (le1_lit 150) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (347344 + 880 + (sc - 7)) [b8 150] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rseq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv usegs m ->
  munch rseqW m0 m -> wmono usegs m0 m ->
  evt usegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17710) fc None m' (seg_rom usegs)
      /\ munch rseqW m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (step_seq st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x176e4) fc None m (seg_rom usegs)).
Proof using .
  intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
  set (q := c_seq (ctx st)) in *.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
  unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
  replace (347344 + 912) with 348256 in C6 by reflexivity. replace (347344 + 848) with 348192 in US by reflexivity.
  (* [comment removed for export] *)
  assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv usegs mj ->
    munch [(347344 + 848, 347344 + 913)]%Z m0 mj -> wmono usegs m0 mj ->
    evt usegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17710) fc None m' (seg_rom usegs)
      /\ munch [(347344 + 848, 347344 + 913)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17708) fc None mj (seg_rom usegs))).
  { intros mj stj ns NS MRj CTj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (347344 + 912) with 348256 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (347336 + 920)) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    (* [comment removed for export] *)
    step. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    rraw_store_finish0 (347344 + 912) [b8 ns] MUj WMj SOK.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned q) by lia.
    eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
    pose proof (munch_refl [(347344 + 848, 347344 + 880)]%Z m) as MUz. pose proof (wmono_refl usegs m) as WMz.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (UZ : u8arr usegs mX 348192 (zeros 32));
    [ apply (u8arr_of_rw_cells usegs mX 348192 32);
      lazymatch goal with H : rw_cells usegs mX 348192 _ |- _ =>
        apply (rw_cells_congr usegs mX 348192 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRz : rmrep stz mX);
    [ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
    | clear MUc WMc ] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono usegs m0 ?mX, MIc : mem_inv usegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
(* [comment removed for export] *)
Lemma rmm_seq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17710) fc None m' (seg_rom usegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (step_seq (account_bounce sc st)) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17430) fc None m (seg_rom usegs)).
Proof using SC.
  intros until m. intros MR SEQ BR USR MI.
  eapply evt_cut; [eapply rbounce_walk; eassumption|].
  cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
  assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
  { unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
    destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
  rewrite <- SEQ'.
  eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
  cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
  do 6 eexists. split; [reflexivity|]. subst a3'.
  repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.


End CeilWrap.
End RASlot_W15.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W16.
Module RASlot_W16.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W16.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 RASlot_W2 RASlot_W4 RASlot_W11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

(* [comment removed for export] *)
Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop :=
  fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x177f4) fc None m (seg_rom usegs).

(* [comment removed for export] *)
Lemma rj2c_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
  1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
  evt usegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req u1 c1 nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
             (Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17798) fc None m (seg_rom usegs)).
Proof using RQ SZ.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * c1 < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR.
  unfold rmmc_post.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
  step. step. step. step. step. step.
  rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
  replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
  set (nd0 := round_up_pg (size * c1 + 16)).
  pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
  replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
  fold nd0 in RUR.
  assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
  { unfold mm_final, UNIT. reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
    do 9 eexists. reflexivity. }
  replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.
  (* [comment removed for export] *)
  step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    do 9 eexists. reflexivity. }
  replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
  replace (-20 + - req) with (- (req + 20)) by lia.
  set (rq' := round_up_pg (req + 20)).
  pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
  replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
  assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
  { unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
  rewrite ES in EF. clear ES. unfold PGSZ in EF. 
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
    step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
      do 9 eexists. reflexivity.
    + replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
      step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
      * (* [comment removed for export] *)
        step. step. step.
        apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
      * apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
    step. step. step.
    apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rred_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
  1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
  evt usegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17798) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17724) fc None m (seg_rom usegs)).
Proof using SC SZ.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * cnt < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR. pose proof (ASlot_W16.land3_range sc) as L3.
  (* [comment removed for export] *)
  assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
    evt usegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17798) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
             (Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17794) fc None m (seg_rom usegs))).
  { intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
  step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
  { eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
    rewrite Bool.andb_false_r. reflexivity. }
  assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
  assert (ER : mm_cnt_red sc size cnt u1 nos =
    (if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
     else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
     else cnt)).
  { unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold PGSZ in ER.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
  step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
  - (* [comment removed for export] *)
    replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
    step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    + (* [comment removed for export] *)
      replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
      (* [comment removed for export] *)
      step. step. step.
      step. if_cases KC; zify_cond KC.
      * (* [comment removed for export] *)
        rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
        destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
        assert (E0 : Z.land sc 3 = 0) by lia.
        step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
        apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
        { intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
          replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
          replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
        clear KC. step. step.
        step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
        { (* [comment removed for export] *)
          apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
          do 5 eexists. reflexivity. }
        rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
        replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
        step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
        step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
        -- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        -- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + (* [comment removed for export] *)
      rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
      step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
      step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
      * (* [comment removed for export] *)
        replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
        step. step. step.
        step. if_cases KG; zify_cond KG.
        { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
        clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
        apply evt_done. rewrite ER. do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
  - (* [comment removed for export] *)
    rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
    step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
    + (* [comment removed for export] *)
      replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
      step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
      step. step. step.
      step. if_cases KG; zify_cond KG.
      { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
      clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
      apply evt_done. rewrite ER. do 5 eexists. reflexivity.
    + (* [comment removed for export] *)
      step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      do 5 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rusage1_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
  rmrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt usegs (fun ms' => exists (a5' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17724) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17710) fc None m (seg_rom usegs)).
Proof using SC.
  intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
  pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
  { apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
    eexists. reflexivity. }
  apply Z.ltb_ge in K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia.
  step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
  { (* [comment removed for export] *)
    assert (ODD : Z.even sc = false).
    { rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
    apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
  assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m (sc + 1) (wa (347344 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
  replace (wa (347344 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (347336 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
  pose proof (USR (sc + 1)) as U1R.
  step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
  apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmmc_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
  rmrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt usegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17710) fc None m (seg_rom usegs)).
Proof using RQ SC SZ.
  intros until u0. intros MR CR UR USR.
  assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
  { unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
  eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
  cbv beta. intros ms' (a5' & ->).
  eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
  cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
  assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
  { unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
  eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
  cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
  do 9 eexists. reflexivity.
Qed.
End MMC.


End CeilWrap.
End RASlot_W16.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_M5D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_malloc_bigw.
Module RASlot_W17.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W17.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_bigw RASlot_W2 RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac step ::= step1.  Local Ltac stepz ::= step1.  (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rmm_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt usegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x17814) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x177f4) fc None m (seg_rom usegs)).
Proof using .
  intros. unfold rmmap_entry.
  step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmm_ret_fail_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt usegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1793c) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17814) fc None m (seg_rom usegs)).
Proof.
  intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

(* [comment removed for export] *)
Lemma rmm_ret_ok_walk :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
  rmrep st2 m -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1786c) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17814) fc None m (seg_rom usegs)).
Proof using CNT CR HC MST ND NDA REC SC SZ XA XA2.
  intros until m. intros MR MI.
  pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold alloc_ceiling, RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
  clear K.
  (* [comment removed for export] *)
  step.
  rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
  rmeta_open G MUa WMa.
  step.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
  step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
  rewrite (divu_word 4080 size) by lia.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
  set (d := 4080 / size) in *.
  (* [comment removed for export] *)
  pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
  step. rewrite (sx32_wz_sxv c) by lia.
  (* [comment removed for export] *)
  step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
  step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
  (* [comment removed for export] *)
  assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
  { unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  step.
  lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
    [ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
    | clear MUa WMa H ] end.
  set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
  (* [comment removed for export] *)
  pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (347336 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
  clear CX1.
  st1.
  rewrite le4_swrap_succ by lia.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
  clear MR3.
  rraw_store_finish0 (347344 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
  assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
  { unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
  rewrite <- E4 in MR4.
  assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
    evt usegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 347336) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1786c) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (347344 + 12, 347344 + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 347336) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17858) fc None mX (seg_rom usegs))) end.
  { intros a2v mn Hmn ->.
    assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
    replace (cnt + -1) with (cnt - 1) by lia.
    assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
    { unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
      destruct (Z.ltb_spec cnt d) as [LT|GE].
      - replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
        destruct (Z.eqb_spec d 0) as [E0|NE0].
        + rewrite E0. reflexivity.
        + replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
                  = Z_to_bv 64 (mm_ai cnt size)).
    { rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
      destruct (Z.eqb_spec mn 0) as [E0|NE0].
      - rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
      - rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
        destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    rewrite EA2.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
  if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.


End CeilWrap.
End RASlot_W17.

(* [comment removed for export] *)
Module RASlot_W18.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W18.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A RASlot_W2 RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rmrep_set_free_head : forall st m v,
  rmrep st m ->
  rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (RCTX + 16)) (le8 (pw st v))).
Proof.
  intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (pw st v)) as L8.
  pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
  - left.
    pose proof (rw_cells_write usegs m RCTX (rctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
    cbn [cbytes cell_upd rctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
    unfold rctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
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
  s_reserved stY = s_reserved stX ->
  rmrep stY m.
Proof using .
  intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact EA| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

(* [comment removed for export] *)
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
  (spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.

(* [comment removed for export] *)
Lemma rfailm1_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt usegs (fun ms' => exists (a1' s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x179c4) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x175bc) fc None m (seg_rom usegs)).
Proof using FL MST.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (nelimp (rmeta_slot_bounds st m mt MR MST) 5%nat; intros Gpos GC GI G4 _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt usegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17618) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 ssp_guard_val; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x175bc) fc None m (seg_rom usegs))).
  { intros W HW1 HW2.
    pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells usegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells usegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tclose]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tclose]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells usegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 ssp_guard_val; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tclose| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    (nelim (FL h eq_refl) 6%nat; intros MSh NEh p HP MSp NEp). rewrite HP.
    (nelimp (rmeta_slot_bounds st m h MR MSh) 5%nat; intros Hpos HC' HI _ _).
    (nelimp (rmeta_slot_bounds st m p MR MSp) 5%nat; intros Ppos PC PI _ _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (347344 + 16, 347344 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tclose|]. cbv beta.
    intros ms' nelH_; (nelim nelH_ 8%nat; intros m1 junk' -> FR1 MU WM1 MI1 MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. nexists 4%nat. split; [reflexivity|]. split; [exact FR1|].
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
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (347344 + 16, 347344 + 24)]%Z); cbn; tclose|]. cbv beta.
    intros ms' nelH_; (nelim nelH_ 8%nat; intros m1 junk' -> FR1 MU WM1 MI1 MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    pose proof MR1 as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at usegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (347336 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (347344 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. nexists 4%nat. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rfailm2_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt usegs (fun ms' => exists (s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x179c4) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1793c) fc None m (seg_rom usegs)).
Proof using FL MST.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (nelimp (rmeta_slot_bounds st m mt MR MST) 5%nat; intros Gpos GC GI G4 _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt usegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17994) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 ssp_guard_val; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 347336) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1793c) fc None m (seg_rom usegs))).
  { intros W HW1 HW2.
    pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells usegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells usegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tclose]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tclose]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells usegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 ssp_guard_val; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tclose| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    (nelim (FL h eq_refl) 6%nat; intros MSh NEh p HP MSp NEp). rewrite HP.
    (nelimp (rmeta_slot_bounds st m h MR MSh) 5%nat; intros Hpos HC' HI _ _).
    (nelimp (rmeta_slot_bounds st m p MR MSp) 5%nat; intros Ppos PC PI _ _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (347344 + 16, 347344 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tclose|]. cbv beta.
    intros ms' nelH_; (nelim nelH_ 8%nat; intros m1 junk' -> FR1 MU WM1 MI1 MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    step.
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells usegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. nexists 3%nat. split; [reflexivity|]. split; [exact FR1|].
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
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (347344 + 16, 347344 + 24)]%Z); cbn; tclose|]. cbv beta.
    intros ms' nelH_; (nelim nelH_ 8%nat; intros m1 junk' -> FR1 MU WM1 MI1 MR0). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    pose proof MR1 as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at usegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (347336 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (347344 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. nexists 3%nat. split; [reflexivity|]. split; [exact FR1|].
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


End CeilWrap.
(* [comment removed for export] *)
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
End RASlot_W18.

(* [comment removed for export] *)
Module RASlot_W3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3.
Import RASlot_W2 RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
  = Z_to_bv 64 (m_sizeclass mq).
Proof.
  intros MWq. pose proof (meta_word_range _ MWq) as WR. (nelimp MWq 4%nat; intros LI FB SCR ML).
  f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite swrap32_eq'.
  unfold meta_word.
  Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

(* [comment removed for export] *)
Lemma ravz_pre_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1728c) fc None m (seg_rom usegs))
    (MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17280) fc None m (seg_rom usegs)).
Proof using AV0 MR MSL.
  intros until fc. intros HG MI. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Lemma ravz_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17304) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep st5 m')
    (MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1728c) fc None m (seg_rom usegs)).
Proof using AI AV0 BNC FR32 Hgh Hmem MASK MR MSL MW SC0 st4.
  intros until fc. intros HG MI. unfold rt1_regs.
  pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI G4 G24). fold G in Gpos, GC, GI, G4, G24.
  pose proof (meta_word_range _ MW) as MWR.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
  { apply amo_aligned_intro; [unfold alloc_ceiling in GC; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
  clear G4 G24.
  unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  (* [comment removed for export] *)
  step.
  (nelim (rmrep_group_read st _ b gh MR Hgh) 4%nat; intros _ w8 RD8 L8). unfold wa in RD8.
  pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
  step.
  (* [comment removed for export] *)
  step. step.
  assert (W8M : bv_unsigned w8 mod 32 = ai).
  { unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
  rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
  set (y := 2 ^ (ai + 1)).
  (* [comment removed for export] *)
  step. step. rewrite negw_word.
  (* [comment removed for export] *)
  pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
  step. rewrite sx32_wz_sxv by lia.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  (* [comment removed for export] *)
  clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  step. if_false.
  amo_step AMO.
  step. if_false.
  step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.
  (* [comment removed for export] *)
  step. rewrite addiw_m1_word.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  step.
  (* [comment removed for export] *)
  assert (AI31 : Z.land ai 31 = ai).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
  assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
  assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
  pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
  pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
  pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
  { rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
    eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tclose].
    unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
    rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
  clear MUa WMa.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
      rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
  clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HRW : ov_read_bytes usegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
      by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read usegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
  step. step. step.
  rewrite (lw_slli52_srli58_sc mr MW).
  (nelimp MW 4%nat; intros _ _ SCR _). fold mr in SCR.
  set (sc := m_sizeclass mr) in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
  - (* [comment removed for export] *)
    assert (NR : (7 <=? sc) && (sc <? 39) = false).
    { destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
      apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
    apply evt_done. cbv beta. nexists 7%nat. split; [rewrite <- ACT; reflexivity|].
    split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
  - (* [comment removed for export] *)
    assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
    rewrite Z.mod_small in K2 by lia.
    assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    (* [comment removed for export] *)
    step.
    pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (347344 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
    change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
    pose proof (BNC (sc - 7)) as BR.
    step. rewrite ?zxb_b8 by lia.
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      apply evt_done. cbv beta. nexists 7%nat. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
    + (* [comment removed for export] *)
      step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
      pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
      pose proof (u8arr_store_ok usegs _ _ _ (sc - 7) (Z_to_bv 64 (347336 + (sc + -7) + 888)) X5
                    ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
      st1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
        pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
      rraw_store_finish0 (347344 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
      apply evt_done. cbv beta. nexists 7%nat. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|].
      split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End AVZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
    (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
  span_exit F span size = true -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' t1' a6' : word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x17694) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17680) fc None m (seg_rom usegs)).
Proof using SZ.
  induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
  cbn [span_exit] in EX. cbn [span_loop].
  rewrite Nat2Z.inj_succ in SB, CB.
  pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.
  (* [comment removed for export] *)
  step. rewrite ?wz_unsigned by lia.
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
  rewrite (Z.lxor_comm (span + size - 1) span).
  (* [comment removed for export] *)
  step. if_cases K.
  - (* [comment removed for export] *)
    assert (LT : Z.lxor span (span + size - 1) < 4096).
    { unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
    replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
    replace (c + 2) with (c + 1 + 1) by lia.
    eapply (IH (c + 1) (span + size)); try assumption; try lia.
  - assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
    { intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
    replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. nexists 3%nat. reflexivity.
Qed.
End SPANLOOP.
Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof using .
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace 224 with (Z.shiftl 7 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

(* [comment removed for export] *)
Ltac ract_prefix CH w8 :=
  rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
  step;
  let RD8 := fresh "RD8" in let L8 := fresh "L8" in
  (nelim (rmrep_group_read st _ b gh MR Hgh) 4%nat; intros _ w8 RD8 L8); unfold wa in RD8;
  let W8R := fresh "W8R" in
  pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
  step;
  let W8M := fresh "W8M" in
  assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
  step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
  step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
  step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

(* [comment removed for export] *)
Lemma ract_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) <> 0 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' a4' : word),
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x17280) fc None m (seg_rom usegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17258) fc None m (seg_rom usegs)).
Proof using AI0 Hgh Hmem MASKR MR MSL.
  intros until fc. intros NZ MI. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rgroup_bounds st m b gh MR Hgh) 4%nat; intros B0 BC BI _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
  step. if_cases K; zify_cond K.
  2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
      rewrite ?wz_unsigned in K by (apply sxv_range).
      first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
  apply evt_done. nexists 4%nat. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ract_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x17280) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_active sc (Some mn) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17258) fc None m (seg_rom usegs)).
Proof using AI0 Hgh Hmem MR MSL SC.
  intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rmeta_slot_bounds st m mn MR MSn) 5%nat; intros Npos NC NI _ _).
  (nelimp (rgroup_bounds st m b gh MR Hgh) 4%nat; intros B0 BC BI _).
  assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN in CH. cbn [oconc] in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (347344 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (347344 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. nexists 5%nat. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
(* [comment removed for export] *)
Lemma rspan_tail_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
  1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
                   (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1728c) fc None m' (seg_rom usegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
             (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x176a4) fc None m (seg_rom usegs)).
Proof using AI0 Hgh MR MSL.
  intros until wv. intros C2R WVR UNK GM AV0 MI.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rgroup_bounds st m b gh MR Hgh) 4%nat; intros B0 BC BI _).
  (nelimp MR 6%nat; intros _ _ _ _ GR _). (nelim (GR b gh Hgh) 3%nat; intros w8o RWB Hw8o). clear GR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl usegs m) as WMb.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
  pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
  pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
  rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
  set (nbv := Z.lor _ _).
  (* [comment removed for export] *)
  step. rewrite (le1_mod nbv). mem_after_store.
  pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
  pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
  lazymatch goal with H : rw_cells usegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
    [ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
    | ] end.
  { rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
  { lazymatch goal with H : rw_cells usegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
  { rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }
  (* [comment removed for export] *)
  assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
  rmchunk MR2 MS2 CH.
  replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
  replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
  rewrite AV0 in CH.
  step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
  apply evt_done. nexists 4%nat. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.

(* [comment removed for export] *)
Lemma ract_span_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 ->
  mem_inv usegs m ->
  let sc' := m_sizeclass mr in
  let cnt := ai0 + 2 in
  let size := size_class sc' * UNIT in
  let span := UNIT + size * cnt in
  let cnt1 := span_loop 300 cnt span size in
  let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
  evt usegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
                   (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1728c) fc None m' (seg_rom usegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x17258) fc None m (seg_rom usegs)).
Proof using AI0 Hgh Hmem MR MSL.
  intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
  (nelimp (rmeta_slot_bounds st m g MR MSL) 5%nat; intros Gpos GC GI _ _). fold G in Gpos, GC, GI.
  (nelimp (rgroup_bounds st m b gh MR Hgh) 4%nat; intros B0 BC BI _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  pose proof (meta_word_range _ MW) as MWR. (nelimp MW 4%nat; intros LI FB _ ML).
  pose proof (size_class_range sc' ltac:(lia)) as SZR.
  unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.
  (* [comment removed for export] *)
  assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
  step.
  lazymatch goal with HI : mem_inv usegs ?mc |- _ =>
    pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
  step. rewrite zx16_wz by lia. clear SCRD.
  fold cnt.
  assert (SZB : 16 <= size <= 131056) by (unfold size, UNIT; lia).
  assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
  assert (PR : 0 <= cnt * size <= 33 * 131056) by nia.
  assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
  assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
  assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
  pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
  assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
  assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
  clearbody size cnt span cnt1 cnt2.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
  step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
  replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
  step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
  step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
  replace (span + size - 16 + 15) with (span + size - 1) by lia.
  step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
  step.
  (* [comment removed for export] *)
  eapply evt_cut.
  { change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
    eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
  intros ms' nelH_; (nelim nelH_ 4%nat; intros t0' t1' a6' ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
  - replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 9%nat; intros a1'' a2'' a4'' m' -> MU WM MI' MR'). nexists 10%nat. split; [reflexivity|]. eauto.
  - (* [comment removed for export] *)
    step.
    replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 9%nat; intros a1'' a2'' a4'' m' -> MU WM MI' MR'). nexists 10%nat. split; [reflexivity|]. eauto.
Qed.
End ACT.


End CeilWrap.
End RASlot_W3.

(* [comment removed for export] *)
Module RASlot_W9.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3.
Import RASlot_W2 RASlot_W4 RASlot_W3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ RCTX <= a < RCTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof using . intros; left; assumption. Qed.
Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof using . intros; right; left; assumption. Qed.
Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof using . intros; do 2 right; left. exists q; auto. Qed.
Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof using . intros; do 3 right. exists b, gh; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
(* [comment removed for export] *)
Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
  rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo spv ->
  rpres_except (rta_fp st lo spv) m m' ->
  rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom usegs)).

Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
  rmrep stX mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_fin stX g3 msk K) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x17304) fc None mZ (seg_rom usegs)).
Proof using CLO HK1 LO a1.
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
  (pc = 0x17280 \/ pc = 0x1728c) ->
  ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
  rmrep stZ mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_avz K bail stZ g3) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom usegs)).
Proof using CLO HK1 LO SC TAF a1.
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
  (* [comment removed for export] *)
  unfold RR.
  eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1728c) fc None mZ (seg_rom usegs))).
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
  assert (FR5 : rw_cells usegs m5 (spv + -144) (FRM junk)).
  { eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
  assert (ST5 : stk usegs m5 lo (spv + -144)).
  { eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply disjoint_high; [|lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
  eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
    [exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
  - unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
  - unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
  - pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
  - eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    + intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
    + intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.

Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
  msk = m_freed (get_meta_rec stY g2) ->
  (forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
  m_next (get_meta_rec stY g2) <> None ->
  rmrep stY mY -> mem_inv usegs mY -> rw_cells usegs mY (spv + -144) (FRM junk) -> stk usegs mY lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mY ->
  rimplT o (ta_act sc K bail stY g2 msk) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0x17258) fc None mY (seg_rom usegs)).
Proof using CLO HK1 LO SC TAF a1.
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
  - (* [comment removed for export] *)
    apply Z.eqb_eq in ZR.
    destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
    cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
    + (* [comment removed for export] *)
      apply aptr_eqb_eq in EQ. subst mn.
      destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
      * (* [comment removed for export] *)
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
        (* [comment removed for export] *)
        cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
        destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
        cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
      * (* [comment removed for export] *)
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
        eapply (ravz_block 0x1728c stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
        -- unfold stG. rewrite active_set_gai. exact HA.
        -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
        -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
        -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
           cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
    + (* [comment removed for export] *)
      assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
      pose proof (GN mn eq_refl) as GMn.
      destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
      rewrite <- ECONC. riprefixT. eapply evt_mono.
      { eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
      cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
      assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
      rewrite ECONCn.
      eapply (ravz_block 0x17280 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
      -- rewrite active_set_active, Z.eqb_refl. reflexivity.
      -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
         cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in ZR.
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
    cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
    eapply (ravz_block 0x17280 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

(* [comment removed for export] *)
Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
  rmrep stX mX -> mem_inv usegs mX -> rw_cells usegs mX (spv + -144) (FRM junk) -> stk usegs mX lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mX ->
  rimplT o (ta_m sc K bail stX g1) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x1722c) fc None mX (seg_rom usegs)).
Proof using CLO HK1 LO SC TAF a1.
  intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
  destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
  destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
  unfold ta_m, RR.
  set (f := m_freed (get_meta_rec stX g1)).
  destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
  - (* [comment removed for export] *)
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
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
    + eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
    + eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
    eapply (ract_block stX g1 f mX); try eassumption.
    + reflexivity.
    + intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
    + rewrite GN1. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
  a0 = Z_to_bv 64 sc ->
  rmrep st m -> mem_inv usegs m -> stk usegs m lo spv ->
  (forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
     ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
     rmrep st1 m' -> mem_inv usegs m' -> rw_cells usegs m' (spv + -144) (FRM junk) -> stk usegs m' lo (spv + -144) ->
     rpres_except (rta_fp st lo spv) m m' ->
     rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0x17344) fc None m' (seg_rom usegs))) ->
  rimplT o (try_avail sc st K bail) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof using CLO HK1 LO SC TAF.
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
  2:{ (* [comment removed for export] *)
      eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      unfold ta_fail, try_avail. rewrite HA. reflexivity. }
  destruct (taf_head _ _ TAF g HA) as [GM GSC].
  pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
  pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
  unfold pw. cbn [oconc]. unfold wz.
  destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
  2:{ (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    apply Z.eqb_eq in FZ.
    riprefixT. eapply evt_mono.
    { eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' ->.
    destruct (decide (nx = g)) as [->|NEn].
    + (* [comment removed for export] *)
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
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
    + (* [comment removed for export] *)
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
      (* [comment removed for export] *)
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
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
          [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
  - (* [comment removed for export] *)
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
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
    + eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.



End CeilWrap.
End RASlot_W9.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RASlot_M0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv4.
Module RASlot_M1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof using LBK. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

Lemma rta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof using ER F FIT GM K0 LBK MSK RQ SC TR.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  (* [comment removed for export] *)
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
  assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  destruct (FM g b Hmem) as (FM1 & FM2 & _).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
    exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed.
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rerrno_lit : errno_addr tp = 0x3492c.
Proof using ERR HK TP. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
  rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof using AC AUX BL CLO ER ERR F0 FIT HK LO MR RQ SC TK TP UA.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
  fold st' in Hr', SO, STR, FSA.
  (* [comment removed for export] *)
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
  assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
      exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x56000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - unfold alloc_ceiling in CLO. lia.
    - exact (Hc X).
    - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold ras_post2.
  exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
  split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold RCTX in X. unfold alloc_ceiling in CLO. lia.
             + destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). unfold alloc_ceiling in CLO. lia.
             + destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in *. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). unfold alloc_ceiling in RC. lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
    - destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
    - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { (* [comment removed for export] *) constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
  split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. exists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M1.

(* [comment removed for export] *)
Module RASlot_M2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W2 RASlot_W4 RASlot_W9 RASlot_W12 RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
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

(* [comment removed for export] *)
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
  mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Definition rHAG_stmt : Prop :=
  forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
  IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
  am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
  rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -144) ->
  rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
  rw_cells usegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
  brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  rimplT o (ag_body f sc req k bail st2 mm) s' Q
    (MS (rag_regs (Z_to_bv 64 0x1735c) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
        F (Z_to_bv 64 0x17368) fc None m3 (seg_rom usegs)).
Hypothesis HAG : rHAG_stmt.

Lemma rerrno_lit2 : errno_addr tp = 0x3492c.
Proof using ACEIL TP. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma rta_fp_not_image a : 0x10000 <= a < 0x56000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - unfold alloc_ceiling in CLO. lia.
  - exact (Hc X).
  - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
  - pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
    destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof using CLO LO MR.
  pose proof (RAS_STACK_ge sc) as ASG. unfold alloc_ceiling in CLO.
  intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - unfold RCTX in X. lia.
  - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
  - pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in RC. lia.
Qed.

(* [comment removed for export] *)
Lemma runk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof using UA.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_inband rid r off :
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
  ~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC, CLO.
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
  rmrep st1 m1 -> mem_inv usegs m1 -> rw_cells usegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk usegs m1 lo (bv_unsigned sp + -144) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
  rimplT o (as_grp full_lay f sc req k bail st1) s Q
    (MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17344) fc None m1 (seg_rom usegs)).
Proof using AC AM AMP AUX BL CLO ER ERR F0 HAG HK LO MR SC TK TP UA.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof rerrno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  rewrite (as_grp_eq f sc req k bail st1).
  riprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
  { apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| unfold alloc_ceiling; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply rta_fp_not_high. exact Ha.
    - intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
  assert (ERR2 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
  eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x1735c)) with (Z_to_bv 64 0x1735c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).
  (* [comment removed for export] *)
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x56000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x3492c <= a < 0x34930)) ->
            ~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold RCTX in *. lia.
    - destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). unfold alloc_ceiling in BC.
      pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. unfold alloc_ceiling in XC.
      pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
  assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (UA3 : unk_agree st2 o m3).
  { eapply (runk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
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
  - (* [comment removed for export] *)
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [unfold alloc_ceiling in GC; lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  - (* [comment removed for export] *)
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


End CeilWrap.
End RASlot_M2.

(* [comment removed for export] *)
Module RASlot_M3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W2 RASlot_W4 RASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 RASlot_M2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)
Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv usegs m3 /\ stk usegs m3 lo (bv_unsigned sp + -144) /\
  rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rw_cells usegs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
  brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

(* [comment removed for export] *)
Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x1735c) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
          (wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
          a1 (wz cnt1) (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
          (wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 pc) fc None m3 (seg_rom usegs).

Definition rHMM_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
  rag_ctx st1 st2 mm m3 s' errv' junk oo ->
  1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
  rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0x17430 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
  rag_ctx st1 st2 mm m3 s' errv' junk oo ->
  1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0x17474 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using AR FIT HMM HNEST RQ SC.
  intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
  intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
  assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold alloc_ceiling in CLO.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
  pose proof (size_class_range sc SC) as SZR.
  rewrite (ag_body_eq f sc req k bail st2 mm).
  riprefixT. unfold rag_regs.
  eapply evt_cut.
  { eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
  cbv beta. intros ms' (a2'' & a3'' & a4'' & ->).
  set (size := size_class sc * UNIT).
  set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
  assert (C0R : 1 <= cnt0 <= 32).
  { pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
    subst cnt0. destruct (Z.ltb_spec sc 9).
    - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
      destruct (negb _); [lia|]. destruct (negb _); lia.
    - apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
      pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
  eapply evt_cut.
  { eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
  cbv beta. intros ms' ->. unfold rcnt_regs.
  set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
  assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
  assert (EC : ag_cnt1 sc st2 = cnt1).
  { unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
  rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
  apply evt_done.
  destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
  - pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
  - pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M3.

(* [comment removed for export] *)
Module RASlot_M5D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W2 RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 RASlot_M2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma rregion_byte_raw st m rid r off v :
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x3492c.
Proof using . intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x17544) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
      a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
      (wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

(* [comment removed for export] *)
Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
  leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
  mem_inv usegs m'' /\ stk usegs m'' lo (bv_unsigned sp - 144) /\
  rw_cells usegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
  rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells usegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x175bc) fc None m'' (seg_rom usegs)).

Definition rNSUCC_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
  0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
  (forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
             < r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
     rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
  (s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
  rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
              sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x17548) fc None m'' (seg_rom usegs)).
End LEVEL.


End CeilWrap.
End RASlot_M5D.

(* [comment removed for export] *)
Module RASlot_M5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RASlot_W2 RASlot_W4 RASlot_W12 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 RASlot_M2 RASlot_M3 RASlot_M5D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Hypothesis IHf : ralloc_slot_stmt2 f.

Hypothesis NFAIL : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Hypothesis NSUCC : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.

Lemma rhnest_ok : rHNEST_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR CLO ER IHf LO MR NFAIL NSUCC SC TP.
  clear A0 FIT RQ.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R SMc.
  destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  pose proof (RAS_STACK_nest sc (ncls sc cnt1) SCJ ltac:(lia)) as RSN. pose proof (RAS_STACK_ge (ncls sc cnt1)) as ASGj.
  unfold ag_nest. cbv zeta. fold (nreq sc cnt1). fold (ncls sc cnt1).
  pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
  unfold rcnt_state.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT * cnt1)) with (wz (size_class sc * 16 * cnt1)) by (unfold UNIT; reflexivity).
    eapply (rnest_call_walk (size_class sc) cnt1 SZR C1R ltac:(unfold UNIT in SMc; lia)). exact MI3. }
  cbv beta. intros ms' (a2x & a3x & a4x & ->).
  replace (size_to_class (size_class sc * 16 * cnt1 + 12)) with (ncls sc cnt1) by (unfold ncls; rewrite ENR; reflexivity).
  replace (wz (size_class sc * 16 * cnt1 + 12)) with (wz (nreq sc cnt1)) by (rewrite ENR; reflexivity).
  apply evt_done.
  assert (AUX4 : rauxv_ok m3 (bv_unsigned sp - 144)).
  { eapply rauxv_ok_weaken; [exact AUX3| split; [unfold alloc_ceiling; lia| lia]]. }
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 144) by (subst sp'; rewrite unsigned_lit by lia; lia).
  eapply (ralloc_slot_stmtL f IHf R _ bail o s' Q (Z_to_bv 64 0x17544) sp' gp tp) with (st0 := st0) (lo := lo) (sc := ncls sc cnt1) (req := nreq sc cnt1);
    rewrite ?SP'.
  - (* [comment removed for export] *) split; [exists LB; split; [exact AR| exact IS2]|]. split; [exact ER2|]. split; [exact AC2|]. split; [lia|]. split; [lia|]. exact NFIT.
  - exact MR3.
  - exact TK3.
  - exact UA3.
  - exact BL2.
  - exact AUX4.
  - replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact ST3.
  - exact CLO.
  - lia.
  - exact ERR3.
  - exact MI3.
  - exact TP.
  - reflexivity.
  - unfold wz. reflexivity.
  - (* [comment removed for export] *)
    intros st3 idx s'' ms'' PO LEAF.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & ut3 & ut4 & ut5 & ut6 & m'' & errv'' & -> & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & RES).
    rewrite ?SP' in *.
    (* [comment removed for export] *)
    assert (FR'' : rw_cells usegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply (rframe_keep_ER st0 st m MR ER st3 m'' lo (bv_unsigned sp - 144) m3 m''); [exact MR''| exact PE''| | lia| unfold alloc_ceiling; lia].
      replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact FR3. }
    assert (PSM2 : ps_m s'' = ps_m s) by (etransitivity; [exact PSM''| exact PSM]).
    assert (PSF2 : ps_fa s'' = ps_fa s) by (etransitivity; [exact PSF''| exact PSF]).
    assert (PSO2 : ps_so s'' = ps_so s) by (etransitivity; [exact PSO''| exact PSO]).
    assert (NCX : rnest_ctx f o s ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m st0 st lo sc st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o) by (repeat (split; [assumption|]); assumption).
    cbv beta.
    assert (IR : -1 <= idx < 32).
    { destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & _)]; [lia|]. pose proof (so_idx _ _ _ _ _ _ SO3). pose proof (so_li _ _ _ _ _ _ SO3). lia. }
    replace (ret_pc (Z_to_bv 64 0x17544)) with (Z_to_bv 64 0x17544) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT. eapply evt_cut.
    { eapply (rnest_ret_walk (Z_to_bv 64 0x17544) sp' gp tp) with (idx := idx); [exact IR| exact MI'']. }
    cbv beta. intros ms' ->. apply evt_done.
    replace sp' with (Z_to_bv 64 (bv_unsigned sp + -144)) by reflexivity.
    destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & SPAN3 & RDV3)].
    + change (-1 <? 0) with true. change (-1 =? -1) with true. cbv iota.
      apply (NFAIL st1 st2 mm cnt1 st3 m3 m'' s' s'' errv'' junk oo o). exact NCX.
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (idx =? -1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite HA3. cbv iota beta.
      apply (NSUCC st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o g3 b3 r3); [exact NCX| exact I0| exact HA3| exact SO3| exact SPAN3| exact RDV3].
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Export UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocKit_A2 MallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_AS ASlot_W0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import ASlot_W9.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W18.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import ASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import ASlot_M5D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_F.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RASlot_I.
Import RASlot_W2.
Import RASlot_W4.
Import RASlot_W18.
Import RASlot_W19.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RASlot_M0.
Import RASlot_M2.
Import RASlot_M5D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
  (0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x56000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
  \/ iv = (spv - 144, spv).

Lemma rlowW_meta spv st m' q : rmrep st m' -> meta_slot st q -> rlowW spv (conc st q, conc st q + 40).
Proof using .
  intros MR MS. destruct (rmeta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _). left. unfold alloc_ceiling. cbn [fst snd]. lia.
Qed.

Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).

Lemma rfailW_shape st mt spv :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rmetaW spv st) (rfailW st mt spv).
Proof using .
  intros MS FL. unfold rfailW.
  constructor; [right; right; reflexivity|].
  constructor; [left; exists mt; auto|].
  constructor; [right; left; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma rfailW_low st mt m' spv :
  rmrep st m' -> meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rlowW spv) (rfailW st mt spv).
Proof using .
  intros MR MS FL. eapply Forall_impl; [| exact (rfailW_shape st mt spv MS FL)].
  intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply rlowW_meta; eassumption| inversion E; subst; left; unfold alloc_ceiling, RCTX; cbn; lia| inversion E; subst; right; reflexivity].
Qed.

Lemma rlowW_disjoint spv W a n : Forall (rlowW spv) W -> alloc_ceiling <= a -> (a + n <= spv - 144 \/ spv <= a) -> disjoint_from W a n.
Proof using . intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.

Lemma rlowW_disjoint_img spv W a n : Forall (rlowW spv) W -> 0x10000 <= a -> a + n <= 0x56000 -> (a + n <= RCTX \/ RCTX + 928 <= a) ->
  alloc_ceiling <= spv - 144 -> disjoint_from W a n.
Proof. intros FW H1 H2 H3 H4. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(X1 & X2 & X3)|E]; [cbn in *; unfold alloc_ceiling in *; lia| inversion E; subst; unfold alloc_ceiling in *; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR AUX CLO ER ERR HK IS LO MR RQ SC TP.
  intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  pose proof (rmeta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
  pose proof (lf_freelist _ (isf_lf _ _ F3)) as FFL. change (fact_freelist (strip st3)) with (fact_freelist st3) in FFL.
  assert (FL : forall h, c_free_meta_head (ctx st3) = Some h ->
            meta_slot st3 h /\ h <> mm /\ exists p, m_prev (get_meta_rec st3 h) = Some p /\ meta_slot st3 p /\ p <> mm).
  { intros h Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp). destruct (NFL h Hh) as [NE1 NE2].
    change (meta_slot (strip st3) h) in MSh. change (get_meta_rec (strip st3) h) with (get_meta_rec st3 h) in MEMh, NXh, HP.
    change (meta_slot (strip st3) p) in MSp.
    split; [exact MSh|]. split; [exact NE1|]. exists p. split; [exact HP|]. split; [exact MSp|]. intros ->. apply NE2. exact HP. }
  rewrite as_free_meta_eq. cbn [as_kq].
  riprefixT. unfold rnest_regs.
  eapply evt_cut.
  { rewrite <- GE. unfold rFRM in FR''. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in FR'' by lia.
    eapply (rfailm1_walk st3 mm MS3 FL); [exact MR''| exact MI''| exact FR''| lia]. }
  cbv beta. intros ms' (a1x & s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
  assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW st3 mm (bv_unsigned sp))).
  { eapply (rfailW_low st3 mm m'' _ MR'' MS3). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
    split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
  assert (ST7 : stk usegs m7 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
    replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR7 : rw_cells usegs m7 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
  eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
  cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
  (* [comment removed for export] *)
  set (stF := as_fm_st st3 mm) in *.
  destruct (fm_proj st3 mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (FS : Forall (rmetaW (bv_unsigned sp) st3) (rfailW st3 mm (bv_unsigned sp))).
  { apply (rfailW_shape st3 mm _ MS3). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
  assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr.
      destruct (mrel_regions _ _ MREL'' rid r Hr) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto.
    - eapply rpres_except_trans.
      + eapply rpres_except_mono; [exact PE''|]. intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia)); [| exact Ha].
        intros rid r Hr. exists r. rewrite PF1. repeat split; auto. lia.
      + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
        intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
        * cbn in E1, E2. subst lo' hi'. left. do 3 right.
          assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
          destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
          exists rid0, r0. split; [exact H0|]. split; [exact K0|].
          assert (EC : conc stF q = conc st3 q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
        * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
        * inversion E; subst. left. left. lia. }
  apply HK. unfold ras_post2.
  do 14 eexists. exists m7, errv''. split; [reflexivity|].
  split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
  split; [exact MR7|].
  split; [eapply ticks_ok_same; [rewrite PF2; reflexivity| rewrite PF6; reflexivity| exact TK'']|].
  split. { eapply (unk_agree_xfer o st3 m'' stF m7 UA'').
    - exact PF2.
    - intros rid r Hk Hr. rewrite PF1 in Hr. exact Hr.
    - intros b. rewrite PF3. tclose.
    - intros rid r off h Hr Hk Ho Hc NG.
      pose proof MR'' as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
      destruct (rregion_facts st3 m'' rid r MR'' Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
      pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
      + cbn in E1, E2. subst lo' hi'.
        destruct (rmeta_chunk_facts st3 m'' q MR'' MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
      + inversion E; subst. unfold RCTX in Ha. lia.
      + inversion E; subst. lia. }
  split; [exact PE07|].
  split. { split.
    - intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _).
      destruct (mrel_regions _ _ MREL'' rid r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. rewrite PF1. repeat split; auto; [congruence| congruence| lia].
    - rewrite PF7. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF8, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF11. destruct (c_brk (ctx st3)) as [| |brid boff]; auto.
           unfold conc, get_region. rewrite PF1. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. rewrite PF9, (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF6, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros H; exfalso; lia.
    - intros _ H; exfalso; lia. }
  split; [rewrite PF12; exact CTR''|].
  left. reflexivity.
Qed.
End LEVEL.


End CeilWrap.
