(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhAcct.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RSUM (rs : list region) : Z := fold_right (fun r acc => rg_len r + acc) 0 rs.
Definition XSUM (X : list (word * word)) : Z := live_bytes X.

Lemma RSUM_cons : forall r rs, RSUM (r :: rs) = rg_len r + RSUM rs.
Proof. reflexivity. Qed.


Lemma RSUM_perm : forall l l', Permutation l l' -> RSUM l = RSUM l'.
Proof. intros l l' P. induction P; rewrite ?RSUM_cons in *; lia. Qed.

Lemma live_bytes_perm : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof. intros l l' P. induction P as [|[a n] l1 l2 P IH|[a n] [b k] l1|]; rewrite ?live_bytes_cons in *; lia. Qed.

Lemma live_bytes_regions : forall rs,
  (forall r, In r rs -> 0 <= rg_len r < 2 ^ 64) ->
  live_bytes (map region_entry rs) = RSUM rs.
Proof.
  induction rs as [|r rs IH]; intros H; cbn; [reflexivity|].
  pose proof (H r ltac:(left; reflexivity)) as Hr.
  change (bv_unsigned (Z_to_bv 64 (rg_len r)) + live_bytes (map region_entry rs) = rg_len r + RSUM rs). rewrite u64_lit by lia.
  rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record LEDGERX `{RN : mh_run} (st : mst) (X : list (word * word)) (vm : VmMaps) : Prop := LDX {
  lx_maps : Permutation (vm_maps vm) (X ++ map region_entry (s_regions st));
  lx_noacc : Permutation (vm_noaccess vm) (noacc_of st);
  lx_brk : match s_brk st with
           | BrkUntried => vm_brk vm = vm_start_brk vm /\ bv_unsigned (vm_start_brk vm) mod 4096 = 0 /\
                           IMG_HI <= bv_unsigned (vm_start_brk vm) /\ bv_unsigned (vm_start_brk vm) + 8192 <= CEIL
           | BrkLive b0 b _ => bv_unsigned (vm_brk vm) = b /\ bv_unsigned (vm_start_brk vm) = b0
           | BrkDead _ => True
           end;
  lx_res : vm_reserved vm = segments_reserved RSEGS;
  lx_top : page_floor (alloc_top vm) = CEIL
}.

Lemma LEDGERX_nil `{RN : mh_run} : forall st vm, LEDGER st vm <-> LEDGERX st [] vm.
Proof.
  intros st vm. split.
  - intros [A B C D E]. constructor; cbn [app]; assumption.
  - intros [A B C D E]. constructor; cbn [app] in A; assumption.
Qed.

Lemma LEDGERX_same `{RN : mh_run} : forall st st' X vm, s_regions st' = s_regions st -> s_brk st' = s_brk st -> LEDGERX st X vm -> LEDGERX st' X vm.
Proof.
  intros st st' X vm ER EB [LM LN LB LR LMB]. unfold noacc_of in LN. constructor; unfold noacc_of; rewrite ?ER, ?EB; assumption.
Qed.

(* [comment removed for export] *)
Definition xok `{RN : mh_run} (X : list (word * word)) : Prop :=
  forall e, In e X -> exists a n, e = (Z_to_bv 64 a, Z_to_bv 64 n) /\ HEAPLO <= a /\ 0 < n <= 2 ^ 35 /\ a + n <= CEIL /\ a mod 4096 = 0.

Lemma xok_nil `{RN : mh_run} : xok [].
Proof. intros e []. Qed.

Lemma XSUM_nil : XSUM [] = 0. Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rsegs_val : segments_reserved RSEGS =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x1e000); (Z_to_bv 64 0x2e000, Z_to_bv 64 0x43000);
   (Z_to_bv 64 0x71000, Z_to_bv 64 0x4000); (Z_to_bv 64 0x75000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_len : length (segments_reserved RSEGS) = 4%nat.
Proof. rewrite rsegs_val. reflexivity. Qed.

Lemma rsegs_small : Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (segments_reserved RSEGS).
Proof. rewrite rsegs_val. repeat constructor; cbn [snd]; rewrite u64_lit; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Budget.
  Context {RN : mh_run}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  Let WF_regions : wf_regions st := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))).

  Lemma region_len_rng : forall r, In r (s_regions st) -> 0 <= rg_len r < 2 ^ 64.
  Proof.
    intros r Hr. destruct (wr_rng st (WF_regions) r Hr) as (A & B & C & D & E). ceil; unfold HEAPLO in *. lia.
  Qed.


  Lemma live_bytes_ledgerx : forall X vm, LEDGERX st X vm ->
    vm_live_bytes vm = XSUM X + RSUM (s_regions st).
  Proof.
    intros X vm LG. unfold vm_live_bytes. rewrite (live_bytes_perm _ _ (lx_maps st X vm LG)).
    rewrite live_bytes_app. unfold XSUM. rewrite live_bytes_regions by (apply region_len_rng). reflexivity.
  Qed.

  Lemma backing_le : forall X mdl, LEDGERX st X (m_vmmaps mdl) ->
    m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
    vm_backing_used mdl <= XSUM X + RSUM (s_regions st).
  Proof.
    intros X mdl LG Hl Hm. rewrite <- (live_bytes_ledgerx X _ LG). apply vm_backing_used_le_live; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma mprotect_budget_of_ledgerx : forall X mdl addr n, LEDGERX st X (m_vmmaps mdl) ->
    m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
    XSUM X + RSUM (s_regions st) <= vm_limit (m_vmmaps mdl) ->
    mprotect_budget_ok mdl addr n = true.
  Proof.
    intros X mdl addr n LG Hl Hm HB. apply mprotect_budget_ok_intro; [exact Hl | exact Hm |].
    rewrite (live_bytes_ledgerx X _ LG). exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma ledgerx_entries_small : forall X vm, LEDGERX st X vm -> xok X ->
    Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved vm ++ vm_maps vm).
  Proof.
    intros X vm LG XOK. apply Forall_app. split.
    - rewrite (lx_res st X vm LG). exact rsegs_small.
    - apply Forall_forall. intros e He. apply (Permutation_in _ (lx_maps st X vm LG)) in He.
      apply in_app_iff in He. destruct He as [He|He].
      + destruct (XOK e He) as (a & n & -> & _ & Hn & _). cbn [snd]. ceil. rewrite u64_lit; lia.
      + apply in_map_iff in He. destruct He as (r & <- & Hr). cbn [region_entry snd].
        pose proof (region_len_rng r Hr). rewrite u64_lit by lia. exact (wr_len st WF_regions r Hr).
  Qed.

  Lemma ledgerx_entries_count : forall X vm, LEDGERX st X vm ->
    length (vm_reserved vm ++ vm_maps vm) = (4 + length X + length (s_regions st))%nat.
  Proof.
    intros X vm LG. rewrite length_app, (lx_res st X vm LG), rsegs_len.
    rewrite (Permutation_length (lx_maps st X vm LG)), length_app, length_map. lia.
  Qed.
End Budget.
End MhAcct.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap MhAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Grants.
  Context {RN : mh_run}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (mdl : Model).
  Hypothesis HWF : WF st L.
  Hypothesis LG : LEDGERX st X (m_vmmaps mdl).
  Hypothesis XOK : xok X.
  Hypotheses (Hl : m_vm_lazy mdl = []) (Hm : m_vm_materialized mdl = []).

  Lemma ledgerx_top : CEIL0 <= alloc_top (m_vmmaps mdl).
  Proof. exact (alloc_top_ge_CEIL0 _ (lx_top st X _ LG)). Qed.

  Lemma ledgerx_count : Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246 ->
    Z.of_nat (length (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl))) <= 250.
  Proof. intros H. rewrite (ledgerx_entries_count st X _ LG). lia. Qed.

  (* [comment removed for export] *)
  Lemma ledgerx_grant_rw : forall hint n,
    0 <= n <= 2 ^ 35 ->
    Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246 ->
    XSUM X + RSUM (s_regions st) + n <= vm_limit (m_vmmaps mdl) ->
    exists a, grant_ok hint mdl a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
  Proof.
    intros hint n Hn Hcnt Hbud.
    apply (grant_exists_big hint mdl n Hn (ledgerx_entries_small st L HWF X _ LG XOK) (ledgerx_count Hcnt) ledgerx_top).
    pose proof (backing_le st L HWF X mdl LG Hl Hm). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ledgerx_grant_na : forall n,
    0 <= n <= 2 ^ 35 ->
    Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246 ->
    exists a, grant_ok_na_pin mdl a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
  Proof.
    intros n Hn Hcnt.
    exact (grant_exists_na_big mdl n Hn (ledgerx_entries_small st L HWF X _ LG XOK) (ledgerx_count Hcnt) ledgerx_top).
  Qed.
End Grants.
