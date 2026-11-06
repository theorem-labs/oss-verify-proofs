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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require KArith. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocKit_A2 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.MallocRep.lr_lo"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "OSSVerify.KrLib.Heap.MallocRep.MLOCK"; "OSSVerify.KrLib.Heap.MallocRep.LIBC"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_head"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.c_active"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.MallocTree.ptrs_in"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.MallocTree.optr_in"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.put_meta"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.


End PEXT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (m m' : mem) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).


Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_round_up l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply KArith.round_up_pg_eq. Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : mrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= s_ceil st.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

#[using="r0"] Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.


#[using="Type"] Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : ltac2:(CDefT.buildp (gd_tbl_MallocKit_A2 ()) "Pa,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+40.)))P,(5.(3.R2.(6.Vr,))(2.(7.(8.Vr,)(9.(:.Vr,)))R2.))P,(5.(1.(2.$;.R3.)(3.R3.(7.$;.+4.)))(5.(1.(2.$<.R3.)(3.R3.(7.$<.+408.)))(=.$>.Lq,$>.(=.$?.Lrq,$?.(1.(10.(11.$?.)(12.$>.$?.(13.$>.$14.$15.$?.)(16.$>.$14.$15.$?.)R2.(17.Vst,))(18.$?.R1.))(1.(2.(6.R1.)R5.)(3.R5.(7.(8.R1.)(9.(:.R1.))))))))))(10.(11.(19.&8.))A1.Vm',(1:.R4.)A1.Vm,(1:.R4.))")
(* [comment removed for export] *).


End DROPREGION.


Lemma ptrs_in_upd_ctx_scalar P st f : ltac2:(CDefT.buildp (gd_tbl_MallocKit_A2 ()) "P,Pc,$1;.(10.$1<.(1=.A1.O1.R1.)(1=.R1.))P,Pc,$1;.(10.$1<.(1>.A1.O1.R1.)(1>.R1.))P,Pc,$1;.(10.$1<.(1?.A1.O1.R1.)(1?.R1.))P,Pc,$1;.(10.$1<.(20.A1.O1.R1.)(20.R1.))P,Pc,$1;.(10.$1<.(21.A1.O1.R1.)(21.R1.))P,Pc,$1;.(10.(13.$0.$22.$23.$24.)(25.A1.O1.R1.)(25.R1.))P,Pc,$1;.(10.$26.(27.A1.O1.R1.)(27.R1.))P,(28.O3.O2.)(28.O3.(29.O1.O2.))")
(* [comment removed for export] *).
Proof.
  (intros E1 E2 E3 E4 E5 E6 E7 dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E1, E2, E3, E4, E5, E6, E7.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.
Lemma ptrs_in_step_seq P st : ptrs_in P st -> ptrs_in P (step_seq st).
Proof. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
Lemma ptrs_in_put_meta P st g mr : ltac2:(CDefT.buildp (gd_tbl_MallocKit_A2 ()) "P,(2:.O4.(2;.O1.))P,(2:.O4.(2<.O1.))P,(2:.O4.(2=.O1.))P,(28.O4.O3.)(28.O4.(2>.O2.O1.O3.))")
(* [comment removed for export] *).
Proof.
  (intros Q1 Q2 Q3 dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
  destruct (decide (g' = g)) as [->|NE].
  - rewrite lookup_insert_eq. cbn. auto.
  - rewrite lookup_insert_ne by congruence. apply H8.
Qed.


