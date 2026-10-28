(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk Hoare ShapeAlg SpinAlg LibSym HeapIface HeapIfaceX L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import MallocXCps_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module MXCU.
Import MXC.
Section SU.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition malloc_x_cpsU : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    PML.cps_heap L HI PML.PC_MALLOC r sp MALLOC_SCR LB cr
      (fun R M => PML.entry L R M sp r MALLOC_SCR /\ PML.a0 R n /\ 0 < n <= NBU /\ credit_ok L cr n)
      (fun R M R' M' LB' cr' LBk W => exists A, PML.a0 R' A /\ L5C.fresh_block L LB M' A n /\ LB' = (A, n) :: LB /\ cr' = debit L cr n /\ LBk = LB /\ W = []).

Hypothesis MX : malloc_u_spec L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.

Lemma malloc_x_cps_okU : malloc_x_cpsU.
Proof.
  intros LB cr n sp r. unfold PML.cps_heap.
  intros fx R M model K HH (Hmo1 & Hmo2 & Hmo3) HKnil Hfp (Hentry & Ha0 & Hn & Hk) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold MALLOC_SCR in *.
  pose proof Hstk as (S1 & S2 & S3 & S4 & S5). assert (HS : PML.HEAP_STACK = 8224) by reflexivity.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  unfold PML.cfg. rewrite <- LS, <- (PmLayout.ly_malloc L LAY).
  apply (MX fx R M model LB cr n K HH Hmo1 Hmo2 Hmo3 Ha0 Hn Hk).
  - rewrite Htp, (PmLayout.ly_tp L LAY). reflexivity.
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1 R2]. rewrite u64_of_Z by lia. exact R2.
  - (* [comment removed for export] *)
    rewrite U2. unfold stack_ok. rewrite LSTK. unfold hl_ceil. split; [exact S1|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros d m Hd Hm. pose proof (L5C.stk_writable (hl_segs L) (hl_sptop L) M sp PML.HEAP_STACK Hstk) as W.
    exact (W d m Hd Hm).
  - exact HKnil.
  - intros R' M' model' A HA HRP HBR HAP HDEF HPC Hbv HH'.
    rewrite U2 in HPC. rewrite Hra. unfold PML.cfg in Hcont. rewrite <- LS in Hcont.
    apply (Hcont fx R' M' model' ((A, n) :: LB) (debit L cr n) LB [] Hfp); [| exact HRP | | exact Hbv | exact HH'].
    + exists A. split; [exact HA|]. split; [split; [exact HBR | split; [exact HAP | exact HDEF]]|]. repeat split; reflexivity.
    + (* [comment removed for export] *)
      destruct HPC as [P1 P2]. rewrite LSTK in P1, P2. apply L5C.hpres_intro.
      * intros a (Ha & HC & HE & _). exact (P1 a Ha HC HE).
      * intros i Hi. replace (sp - PML.HEAP_STACK + i) with (sp - PML.HEAP_STACK + i) by lia. apply P2. lia.
      * intros a Ha HC HE Hd. rewrite (P1 a Ha HC HE). exact Hd.
Qed.
End SU.
End MXCU.
