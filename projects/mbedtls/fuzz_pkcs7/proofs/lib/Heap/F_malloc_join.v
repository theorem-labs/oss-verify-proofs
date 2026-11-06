(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_join () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc_fp.mrel"].



(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unk_agree_ext st st' o m : ltac2:(CDefT.buildp (gd_tbl_F_malloc_join ()) "P,(0.O4.O2.O1.)P,(1.(2.$3.$4.$5.$6.)(7.O3.)(7.O4.))P,Prid,$3.(1.$8.(9.O3.R1.)(9.O4.R1.))P,(1.(2.$:.(;.$3.$4.$<.$=.)(>.$3.$4.$5.$<.$=.$?.)$10.)(11.O3.)(11.O4.))(0.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
  apply (UA rid r off h Hr Hk Ho Hc). (intros dd_H; ddestruct dd_H as (b & gh & Hb & Hf & Hx)). apply NG. dexists b, gh. rewrite EG. auto.
Qed.

Lemma unk_agree_munch st o m m' W : ltac2:(CDefT.buildp (gd_tbl_F_malloc_join ()) "P,(0.O5.O4.O3.)P,(12.O1.O3.O2.)P,Prid,$3.Pr,$6.P,(1.(13.$6.)(14.$3.$6.(2.$3.$4.$5.$6.)(15.$3.$4.$5.$6.)R2.(7.O5.))(16.$6.R1.))P,(1.$17.(18.R2.)$19.)(1:.O1.(1;.R3.)(1<.(1=.R3.)))P,Prid,$3.Pr,$6.P,(1.(13.$6.)(14.$3.$6.(2.$3.$4.$5.$6.)(15.$3.$4.$5.$6.)R2.(7.O5.))(16.$6.R1.))(1>.(1?.=(1;.R2.))(1?.(20.(1;.R2.)(1<.(1=.R2.)))(21.+2.+40.)))(0.O5.O4.O2.)")
(* [comment removed for export] *).
Proof.
  intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
  rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
  destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (junk : list byte) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64)
       [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra] ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       malloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)).

Lemma mrel_same st st' : ltac2:(CDefT.buildp (gd_tbl_F_malloc_join ()) "P,(1.(2.$3.$4.$5.$6.)(7.O1.)(7.O2.))P,(1.$3.(22.O1.)(22.O2.))P,(1.(23.(24.$<.$<.))(25.O1.)(25.O2.))(26.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros ER EN ES. split; [| rewrite EN; lia | exact ES].
  intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : s_ceil st <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End FASTCORE.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)).


Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : s_ceil st <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End ASCALL.
