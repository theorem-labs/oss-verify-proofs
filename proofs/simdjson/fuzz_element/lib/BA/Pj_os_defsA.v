(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PJ_SB_VPTR_A : Z := 0x1645c8.
Definition PJ_OS_VPTR_A : Z := 0x164650.
Definition PJ_IOS_VPTR_A : Z := 0x164678.
Definition PJ_IOS_DVPTR_A : Z := 0x167db8.
Definition PJ_SB_BVT_A : Z := 0x167e70.
Definition PJ_IOS_BVT_A : Z := 0x167ef0.

Definition PJ_NULSB_VT_A : Z := 0x164628.
Definition PJ_GOT_VT_A : Z := 0x16aec8.
Definition PJ_WIDEN_SLOT_A : Z := 0x168050.
Definition PJ_DO_WIDEN_A : Z := 0x133c98.
Definition PJ_GOT_CTYPE_ID_A : Z := 0x16af18.
Definition PJ_CTYPE_ID_A : Z := 0x6a6960.
Definition PJ_CTYPE_FACET_A : Z := 0x6a6bc8.

Definition PJ_SENTRY_CTOR_A : Z := 0x10d3d4.
Definition PJ_SENTRY_DTOR_A : Z := 0x10d430.
Definition PJ_GETLOC_A : Z := 0x10bdac.
Definition PJ_USE_FACET_A : Z := 0x132338.
Definition PJ_LOC_COPY_A : Z := 0x131aac.
Definition PJ_IOS_INIT_A : Z := 0x10bfa8.
Definition PJ_IOS_DTOR_BODY_A : Z := 0x10bdc8.
Definition PJ_MEMMOVE_SYM_A : Z := 0x812f0.

Definition sb_cellsA (pb pp ep : word) (dum : list byte) : list cell :=
  [C8 (Z_to_bv 64 PJ_SB_VPTR_A);
   C8 (Z_to_bv 64 PJ_LOC_IMP_A);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 pb; C8 pp; C8 ep;
   CB 64 dum].

Definition ios_cellsA (OS : Z) (vptr fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 0x1002); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 PJ_LOC_IMP_A);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition os_cellsA (OS : Z) (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cellsA pb pp ep dum ++ [C8 (Z_to_bv 64 PJ_OS_VPTR_A)] ++ ios_cellsA OS PJ_IOS_VPTR_A fill j148 j284.

Lemma os_cellsA_size : forall OS pb pp ep fill dum j148 j284, cells_size (os_cellsA OS pb pp ep fill dum j148 j284) = 288%nat.
Proof. intros. reflexivity. Qed.

Definition OSFRESHA (m : mem) (OS : Z) : Prop :=
  exists dum j148 j284, rw_cells asegs m OS (os_cellsA OS (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) 0xffffffff dum j148 j284).

Definition OSUSEDA (m : mem) (OS : Z) : Prop :=
  exists pb pp ep dum j148 j284, rw_cells asegs m OS (os_cellsA OS pb pp ep 0x20 dum j148 j284).

Lemma OSFRESHA_hull : forall m OS, OSFRESHA m OS -> exists bs, rw_cells asegs m OS [CB 288 bs].
Proof. intros m OS (dum & j148 & j284 & H). apply rw_cells_forget in H. rewrite os_cellsA_size in H. exact H. Qed.
Lemma OSUSEDA_hull : forall m OS, OSUSEDA m OS -> exists bs, rw_cells asegs m OS [CB 288 bs].
Proof. intros m OS (pb & pp & ep & dum & j148 & j284 & H). apply rw_cells_forget in H. rewrite os_cellsA_size in H. exact H. Qed.

Lemma OSUSEDA_parts : forall m OS, OSUSEDA m OS ->
  exists pb pp ep dum j148 j284,
    rw_cells asegs m OS (sb_cellsA pb pp ep dum) /\ rw_cells asegs m (OS + 128) [C8 (Z_to_bv 64 PJ_OS_VPTR_A)]
    /\ rw_cells asegs m (OS + 136) (ios_cellsA OS PJ_IOS_VPTR_A 0x20 j148 j284).
Proof.
  intros m OS (pb & pp & ep & dum & j148 & j284 & H). exists pb, pp, ep, dum, j148, j284.
  unfold os_cellsA in H.
  apply (proj1 (Startup_glue.rw_cells_app asegs m OS _ _)) in H. destruct H as [H1 H2].
  apply (proj1 (Startup_glue.rw_cells_app asegs m _ _ _)) in H2. destruct H2 as [H2 H3].
  cbn [sb_cellsA cells_size csize Nat.add] in H2, H3.
  replace (OS + Z.of_nat 128) with (OS + 128) in H2, H3 by lia.
  replace (OS + 128 + Z.of_nat 8) with (OS + 136) in H3 by lia.
  auto.
Qed.

Definition OSIOSA (m : mem) (OS : Z) : Prop :=
  exists (vp fill : Z) j148 j284, rw_cells asegs m (OS + 136) (ios_cellsA OS vp fill j148 j284).

Lemma OSFRESHA_loc : forall m m' OS, OSFRESHA m OS -> agree_on (fun a => OS <= a < OS + 288) m m' -> OSFRESHA m' OS.
Proof.
  intros m m' OS (dum & j148 & j284 & H) AG. exists dum, j148, j284. eapply rw_cells_agree_nw; [exact H|].
  intros a Ha. apply AG. rewrite os_cellsA_size in Ha. lia.
Qed.
Lemma OSUSEDA_imp : forall m OS, OSUSEDA m OS -> rw_cells asegs m (OS + 8) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)].
Proof.
  intros m OS H. destruct (OSUSEDA_parts m OS H) as (pb & pp & ep & dum & j148 & j284 & SB & _ & _). unfold sb_cellsA in SB.
  apply (proj1 (Startup_glue.rw_cells_app asegs m OS [C8 (Z_to_bv 64 PJ_SB_VPTR_A)] _)) in SB. destruct SB as [_ SB].
  apply (proj1 (Startup_glue.rw_cells_app asegs m _ [C8 (Z_to_bv 64 PJ_LOC_IMP_A)] _)) in SB. destruct SB as [SB _].
  cbn [cells_size csize Nat.add] in SB. replace (OS + Z.of_nat 8) with (OS + 8) in SB by lia. exact SB.
Qed.
Lemma OSUSEDA_ios : forall m m' OS, OSUSEDA m OS -> agree_on (fun a => OS + 136 <= a < OS + 288) m m' -> OSIOSA m' OS.
Proof.
  intros m m' OS H AG. destruct (OSUSEDA_parts m OS H) as (pb & pp & ep & dum & j148 & j284 & _ & _ & IOSF).
  exists PJ_IOS_VPTR_A, 0x20, j148, j284. eapply rw_cells_agree_nw; [exact IOSF|]. intros a Ha. apply AG. cbn [ios_cellsA cells_size csize Nat.add] in Ha. lia.
Qed.

Definition pj_os_roA (m : mem) : Prop :=
  ro_cells asegs m PJ_NULSB_VT_A [C8 (Z_to_bv 64 PJ_XSPUTN_A); C8 (Z_to_bv 64 PJ_OVERFLOW_A); C8 (Z_to_bv 64 8)]
  /\ ro_cells asegs m PJ_GOT_VT_A [C8 (Z_to_bv 64 PJ_IOS_BVT_A); C8 (Z_to_bv 64 PJ_SB_BVT_A)]
  /\ ro_cells asegs m PJ_WIDEN_SLOT_A [C8 (Z_to_bv 64 PJ_DO_WIDEN_A)]
  /\ ro_cells asegs m PJ_GOT_CTYPE_ID_A [C8 (Z_to_bv 64 PJ_CTYPE_ID_A)].

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition PJ_OS_XSPUTN_STACK_A : Z := 64 + 16 + RT_STACK.
Definition xsputn_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS S N CAP q lo fO : Z) (kO : nat) (pb : word) (dum bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  rw_cells asegs m OS (sb_cellsA pb (wz 0) (wz 0) dum) -> os_hullA m OS -> pj_os_roA m ->
  rw_cells asegs m S [CB (Z.to_nat CAP) bs] -> 0 <= N <= CAP -> 0 < S -> S + CAP <= lo -> acc asegs m S N -> buf_clsA RT Σ fO kO S CAP ->
  (S + CAP <= OS \/ OS + 288 <= S) ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_OS_XSPUTN_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (pb' pp' ep' : word) (dum' : list byte),
     ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo q -> os_hullA m' OS ->
     rw_cells asegs m' OS (sb_cellsA pb' pp' ep' dum') ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 40, OS + 128)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz N) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) (wz S) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_XSPUTN_A) fc None m (seg_rom asegs)).
End Stmts.

Notation ctor_cpsA_os RT PMc := (ctor_cpsA RT PMc OSFRESHA) (only parsing).
Notation put_cpsA_os RT PMc := (put_cpsA RT PMc OSFRESHA OSUSEDA) (only parsing).
Notation iosdtor_cpsA_os RT PMc := (iosdtor_cpsA RT PMc OSIOSA) (only parsing).
