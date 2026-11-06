(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf4 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_hints MallocInv_sc MallocInv_sc2 MallocInv_sc3
  MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_aspieces MallocInv_agrp_iface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Definition chk_cnt1 (sc : Z) : bool :=
  forallb (fun c => negb (c =? 1) || ((sc mod 4 =? 3) && ((16 * size_class sc <=? 2032) || ((16 * size_class sc + 16) mod 4096 =? 0))))
          (cnt_cands sc).

Lemma chk_cnt1s : forallb chk_cnt1 (Zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cnt1_facts : forall sc c, 0 <= sc < 48 -> In c (cnt_cands sc) -> c = 1 ->
  sc mod 4 = 3 /\ (2032 < 16 * size_class sc -> (16 * size_class sc + 16) mod 4096 = 0).
Proof.
  intros sc c Hsc Hc ->.
  pose proof (proj1 (forallb_forall _ _) chk_cnt1s sc (Zseq_In 48 0 sc ltac:(llia))) as H.
  unfold chk_cnt1 in H. apply (proj1 (forallb_forall _ _)) with (x := 1) in H; [| exact Hc].
  cbn [Z.eqb Pos.eqb negb orb] in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H1. split; [exact H1|]. intros Hgt.
  apply Bool.orb_prop in H2. destruct H2 as [H2 | H2]; [apply Z.leb_le in H2; llia | apply Z.eqb_eq in H2; exact H2].
Qed.

Lemma as_cnt_m_cnt : forall sc usage size, as_cnt sc usage size = m_cnt sc usage size.
Proof. intros. reflexivity. Qed.

Theorem as_cnt_ok : as_cnt_spec.
Proof.
  intros R sp0 argv envp cb D A s sc usage size K P HII Hsc -> Hus HK.
  pose proof (ii_is HII) as [HW HR HC HWIN HE HG]. pose proof (envok_rodata _ _ _ _ HE) as HRO.
  pose proof (size_class_bound sc Hsc) as Hszc.
  rewrite as_cnt_m_cnt.
  replace (Z_to_bv 64 (16 * size_class sc)) with (v_slli (Z_to_bv 64 (size_class sc)) 4)
    by (rewrite v_slli_Z by llia; change (2^4) with 16; f_equal; lia).
  apply (ts_alloc_cnt s sc (Z_to_bv 64 usage) K P HRO HWIN Hsc).
  intros c Hc Hrange.
  pose proof (cnt_facts sc c Hsc Hc) as (Hc1 & Hspan & _). cbv zeta in Hspan. unfold cnt1_of in Hspan.
  apply HK; [exact Hc | exact Hrange | | intros E; exact (cnt1_facts sc c Hsc Hc E)].
  destruct (Z.eqb_spec c 1) as [-> | Hne]; [| exact Hspan].
  destruct (2048 <? 16 * size_class sc + 16); lnia.
Qed.

End WithLayout.
