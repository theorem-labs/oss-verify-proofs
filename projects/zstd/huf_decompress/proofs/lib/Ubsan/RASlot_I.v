(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (rimplT_steq, rimplT_nat2, ras_post2_post and 3 more; ralloc_meta_stmtL's is the proof of zstd/simple_decompress's same file)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W1 ASlot_I.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_I () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree:rimplT_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat:eruns_steqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2kSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8steq_symC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2bSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree@ralloc_meta_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTreeBrimplM_membed_steqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2KFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree;rimplT_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree<rimplT_reachC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan8RASlot_I;rimplT_steqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5Ubsan@RAllocSlot_iface8ras_postC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc7ASlot_I7as_inv200C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan8RASlot_IAralloc_slot_stmt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan@RAllocSlot_iface@ralloc_slot_stmtC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib5Ubsan8RASlot_I;rimplT_nat2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat>alloc_slot_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan8RASlot_I8ras_pre2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib5Ubsan@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00c59OSSVerify5KrLib5Ubsan8RASlot_I9ras_post2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5Ubsan:RMallocRepAralloc_slot_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat>alloc_meta_natC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib5Ubsan;RMallocTree8ram_postC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5Ubsan;RMallocTree9RAM_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepAralloc_meta_entryC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g _ ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
  intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof.
  intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

(* [comment removed for export] *)
Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 0x3b8a0 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.
End CANSEC1.
