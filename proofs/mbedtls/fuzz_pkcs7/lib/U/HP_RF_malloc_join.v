(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf F_malloc_join.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_A HP_RMalloc_fp HP_RF_malloc_enf HP_RAllocSlot_iface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_malloc_join () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"].

Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    under_virgin st2 g b idx ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4088c) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < rceil.
Proof.
  intros (WF & _) (WF2 & _) H. dpose WF as (_ & WR & _). dpose WF2 as (_ & WR2 & _).
  rceilb.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. ddestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). rceilb. lia.
  - right. ddestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). rceilb. lia.
  - right. ddestruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). rceilb. lia.
  - right. ddestruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). rceilb. lia.
  - right. rceilb. lia.
Qed.

#[using="Type"] Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_join ()) "P,(0.VhRP,O:.O6.)P,(0.VhRP,O9.O3.)P,(1.(2.VhRP,O:.O9.O8.O7.)O5.O4.)P,(3.$4.O5.O2.O1.)P,(5.O7.O2.)P,(5.(6.VhRP,)O2.)(3.$4.O4.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

#[using="Type"] Lemma rmalloc_fp_image st st2 lo sp m0 m2 a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_join ()) "P,(0.VhRP,O7.O3.)P,(0.VhRP,O6.O2.)P,(2.VhRP,O7.O6.O5.O4.O1.)P,(5.(6.VhRP,)O5.)P,(7.(5.+48000.O1.)(8.O1.+7>000.))(9.(7.(5.$:.O1.)(8.O1.(;.$:.+3:0.)))(7.(5.+5=024.O1.)(8.O1.+5=028.)))")
(* [comment removed for export] *).
Proof.
  intros (WF & _) (WF2 & _) H CLO HA. dpose WF as (_ & WR & _). dpose WF2 as (_ & WR2 & _).
  rceilb.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - ddestruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - ddestruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - (* [comment removed for export] *)
    exfalso. dpose WF as ((RS & RPRS) & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

#[using="Type"] Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_join ()) "P,(0.VhRP,O9.O5.)P,(0.VhRP,O8.O4.)P,(<.VhRP,O3.O1.)P,(1.(2.VhRP,O9.O8.O7.O6.)O3.O2.)P,(5.(6.VhRP,)O7.)P,(5.O6.O1.)(<.VhRP,O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    ddestruct AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). rceilb. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

End RP_1.
