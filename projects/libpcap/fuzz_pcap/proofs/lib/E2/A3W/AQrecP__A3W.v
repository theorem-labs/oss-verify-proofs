(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require Sorting.Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amerge__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepQW.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AQrecP.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amerge__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepQW. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ACdeallocP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_aqrec_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepQW.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition aqrec_entry : Z := 0x35aa0.
Definition aqrec_retpc : Z := 0x35c10.     (* [comment removed for export] *)
End CANSEC1.
Notation AQREC_STACK := 1216 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition bqentries (X : list bq) : list (achunk * Z) := qentries (map fst X) (map snd X).
Definition bqslots (X : list bq) : list Z := map (fun x => qb_slot (snd x)) X.
Definition bqlen_ok (x : bq) : Prop := length (qb_ks (snd x)) = length (b_chunks (fst x)).

#[using="Type"] Lemma bqentries_cons : forall x X, bqentries (x :: X) = combine (b_chunks (fst x)) (qb_ks (snd x)) ++ bqentries X.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bqentries_app : forall X Y, bqentries (X ++ Y) = bqentries X ++ bqentries Y.
Proof. induction X as [|x X IH]; intros Y; [reflexivity|]. cbn [app]. rewrite !bqentries_cons, IH, app_assoc. reflexivity. Qed.
#[using="Type"] Lemma bqslots_app : forall X Y, bqslots (X ++ Y) = bqslots X ++ bqslots Y.
Proof. intros. unfold bqslots. apply map_app. Qed.

#[using="Type"] Lemma combine_app : forall {A B} (l1 l2 : list A) (k1 k2 : list B), length k1 = length l1 ->
  combine (l1 ++ l2) (k1 ++ k2) = combine l1 k1 ++ combine l2 k2.
Proof. induction l1 as [|a l1 IH]; intros l2 [|b k1] k2 LEN; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma merge_bq_keeps : forall R cur, Forall bqlen_ok (cur :: R) ->
  let '(l, e) := merge_bq cur R in
     Permutation (bqentries (l ++ e)) (bqentries (cur :: R))
  /\ Permutation (bqslots (l ++ e)) (bqslots (cur :: R))
  /\ Forall bqlen_ok (l ++ e)
  /\ Forall (fun x => b_size (fst x) = Q_BATCH_BYTES /\ b_count (fst x) = 0 /\ b_chunks (fst x) = [] /\ qb_ks (snd x) = []) e
  /\ (Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l)
  /\ batches_bytes (map fst l) + Q_BATCH_BYTES * Z.of_nat (length e) = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur LOK; cbn [merge_bq].
  - cbn [app length Z.of_nat]. split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [exact LOK|]. split; [constructor|].
    split; [intros H; exact H| lia].
  - pose proof (Forall_inv LOK) as L1. pose proof (Forall_inv (Forall_inv_tail LOK)) as L2. pose proof (Forall_inv_tail (Forall_inv_tail LOK)) as L3.
    unfold bqlen_ok in L1, L2.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) ltac:(constructor; [unfold bqlen_ok, bq_merge; cbn; rewrite !length_app; lia| exact L3])).
      destruct (merge_bq (bq_merge cur nx) R) as [l e]. (nd_pre IH 6%nat; intros PE PS LO EM SZ BB; nd_post).
      split; [| split; [| split; [| split; [| split]]]].
      * rewrite bqentries_app, bqentries_cons. cbn [bq_empty fst snd b_chunks qb_ks combine app].
        rewrite <- bqentries_app. eapply Permutation_trans; [exact PE|].
        rewrite !bqentries_cons. cbn [bq_merge fst snd b_chunks qb_ks]. rewrite combine_app by lia.
        rewrite <- !app_assoc. apply Permutation_app_swap_app.
      * rewrite bqslots_app. cbn [bqslots map bq_empty snd qb_slot]. fold (bqslots e). fold (bqslots l).
        eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
        eapply Permutation_trans; [apply perm_skip; rewrite <- bqslots_app; exact PS|].
        cbn [bqslots map bq_merge snd qb_slot]. apply perm_swap.
      * apply Forall_app in LO. destruct LO as [LOl LOe]. apply Forall_app. split; [exact LOl|]. constructor; [| exact LOe]. unfold bqlen_ok, bq_empty. reflexivity.
      * constructor; [| exact EM]. cbn. repeat split; reflexivity.
      * intros SZS. apply SZ. constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZS))].
        cbn [bq_merge fst b_size]. pose proof (Forall_inv SZS) as Z1. pose proof (Forall_inv (Forall_inv_tail SZS)) as Z2. cbn beta in Z1, Z2. lia.
      * cbn [length map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. cbn [bq_merge fst b_size] in BB. unfold Q_BATCH_BYTES in *. lia.
    + specialize (IH nx ltac:(constructor; [exact L2| exact L3])).
      destruct (merge_bq nx R) as [l e]. (nd_pre IH 6%nat; intros PE PS LO EM SZ BB; nd_post).
      split; [| split; [| split; [| split; [| split]]]].
      * cbn [app]. rewrite !bqentries_cons. apply Permutation_app_head. exact PE.
      * cbn [app bqslots map]. apply perm_skip. exact PS.
      * cbn [app]. constructor; [exact L1| exact LO].
      * exact EM.
      * intros SZS. constructor; [exact (Forall_inv SZS)| apply SZ; exact (Forall_inv_tail SZS)].
      * cbn [map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma deq_bq_split : forall gl bytes min_size,
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in gl = taken ++ rest /\ bytes2 = bytes - batches_bytes (map fst taken).
Proof.
  induction gl as [|b gl IH]; intros bytes min_size; cbn [deq_bq].
  - cbn. split; [reflexivity| lia].
  - destruct (min_size <? bytes).
    + specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq gl _ _) as [[tk rs] b2]. destruct IH as [E1 E2].
      cbn [app map]. rewrite batches_bytes_cons. split; [rewrite <- E1; reflexivity| lia].
    + cbn. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qrec_fun_keeps : forall X bytes min_size, Forall bqlen_ok X -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X ->
  bytes = batches_bytes (map fst X) ->
  let '(rest, T, bytes2) := qrec_fun X bytes min_size in
     Permutation (bqentries (rest ++ T)) (bqentries X)
  /\ Permutation (bqslots (rest ++ T)) (bqslots X)
  /\ Forall bqlen_ok (rest ++ T)
  /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest ++ T)
  /\ bytes2 = batches_bytes (map fst rest).
Proof.
  intros X bytes min_size LOK SZ EB. unfold qrec_fun.
  assert (GEN : forall gl ex, Permutation (bqentries (gl ++ ex)) (bqentries X) -> Permutation (bqslots (gl ++ ex)) (bqslots X) ->
             Forall bqlen_ok (gl ++ ex) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (gl ++ ex) ->
             batches_bytes (map fst gl) + Q_BATCH_BYTES * Z.of_nat (length ex) = bytes ->
             let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
             let '(rest0, T, bytes0) := (rest, ex ++ taken, bytes2) in
             Permutation (bqentries (rest0 ++ T)) (bqentries X) /\ Permutation (bqslots (rest0 ++ T)) (bqslots X) /\ Forall bqlen_ok (rest0 ++ T)
             /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest0 ++ T) /\ bytes0 = batches_bytes (map fst rest0)).
  { intros gl ex PE PS LO SZS BB.
    pose proof (deq_bq_split gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size) as DS.
    destruct (deq_bq gl _ min_size) as [[taken rest] bytes2]. destruct DS as [EGL EB2]. subst gl.
    assert (P3 : forall {A} (a b c : list A), Permutation (b ++ (c ++ a)) ((a ++ b) ++ c)).
    { intros A a b c. rewrite (app_assoc b c a). eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite app_assoc. apply Permutation_refl. }
    split; [| split; [| split; [| split]]].
    - eapply Permutation_trans; [| exact PE]. rewrite !bqentries_app. apply P3.
    - eapply Permutation_trans; [| exact PS]. rewrite !bqslots_app. apply P3.
    - rewrite !Forall_app in LO |- *. tauto.
    - rewrite !Forall_app in SZS |- *. tauto.
    - rewrite map_app, batches_bytes_app in BB. unfold Q_BATCH_BYTES, bq in *. lia. }
  destruct (qrec_mergeb (Z.of_nat (length X)) bytes).
  - destruct X as [|cur R].
    + cbn. repeat split; try apply Permutation_refl; try constructor. cbn in EB. lia.
    + unfold amerge_fun. pose proof (merge_bq_keeps R cur LOK) as MK. destruct (merge_bq cur R) as [l e]. (nd_pre MK 6%nat; intros PE PS LO EM SZl BB; nd_post).
      assert (SZ2 : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (l ++ e)).
      { apply Forall_app. split; [exact (SZl SZ)|]. eapply Forall_impl; [| exact EM]. cbn beta. intros x (E & _). rewrite E. lia. }
      pose proof (GEN l e PE PS LO SZ2 ltac:(rewrite EB; exact BB)) as G. revert G.
      destruct (deq_bq l _ min_size) as [[taken rest] bytes2]. intros G. exact G.
  - pose proof (GEN X [] ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; exact LOK)
                  ltac:(rewrite app_nil_r; exact SZ) ltac:(cbn [length Z.of_nat]; lia)) as G. revert G.
    cbn [length Z.of_nat Z.mul]. destruct (deq_bq X _ min_size) as [[taken rest] bytes2]. cbn [app]. intros G. exact G.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma map_fst_combine' : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.
#[using="Type"] Lemma map_snd_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map snd (combine l l') = l'.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma tfirst_qfirst : forall L X, tfirst L X 0 = qfirst L (map snd X).
Proof. intros L [|x X]; reflexivity. Qed.
#[using="Type"] Lemma tlast_qlast : forall L X, tlast L X 0 = qlast L (map snd X).
Proof. intros L X. unfold tlast, qlast, qaddrs, baddr. rewrite map_map. reflexivity. Qed.

#[using="Type"] Lemma chain_bqlen : forall L m X nxt, chain L m X nxt -> Forall bqlen_ok X.
Proof.
  intros L m X. induction X as [|x X IH]; intros nxt CH; [constructor|].
  unfold chain in CH. cbn [map abatches_to] in CH. destruct CH as [AC CH]. constructor; [| eapply IH; exact CH].
  (nd_pre AC 6%nat; intros _ _ _ _ LEN _; nd_post). exact LEN.
Qed.

#[using="Type"] Lemma map_fst_bqentries : forall X, Forall bqlen_ok X -> map fst (bqentries X) = flat_map b_chunks (map fst X).
Proof.
  induction X as [|x X IH]; intros LOK; [reflexivity|]. rewrite bqentries_cons, map_app. cbn [map flat_map].
  pose proof (Forall_inv LOK) as L1. unfold bqlen_ok in L1. rewrite (map_fst_combine' (b_chunks (fst x)) (qb_ks (snd x)) L1). rewrite IH by exact (Forall_inv_tail LOK). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deq_bq_stop : forall gl bytes min_size, bytes = batches_bytes (map fst gl) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) gl -> 0 <= min_size ->
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in (min_size <? bytes2) = false.
Proof.
  induction gl as [|b gl IH]; intros bytes min_size EB SZ M0; cbn [deq_bq].
  - cbn in EB. apply Z.ltb_ge. lia.
  - destruct (min_size <? bytes) eqn:E; [| exact E].
    specialize (IH (bytes - b_size (fst b)) min_size ltac:(cbn [map] in EB; rewrite batches_bytes_cons in EB; lia) (Forall_inv_tail SZ) M0).
    destruct (deq_bq gl _ _) as [[tk rs] b2]. exact IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_eq : forall {RT} st X0 min_size (K : astate -> AM RT),
  map fst X0 = a_qglob st -> a_qglob_bytes st = batches_bytes (a_qglob st) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0 -> Forall bqlen_ok X0 -> 0 <= min_size ->
  let '(rest, T, bytes2) := qrec_fun X0 (a_qglob_bytes st) min_size in
  recycle st min_size K = do_recycle (set_qglob (map fst rest) bytes2 st) (map fst T) K.
Proof.
  intros RT st X0 min_size K EX NB SZ LOK M0.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB, EX; reflexivity)) as KP.
  unfold qrec_fun in KP |- *. unfold recycle. rewrite <- EX, length_map.
  assert (OV : (a_qglob_bytes st <? Q_BATCH_BYTES * Z.of_nat (length X0)) = false).
  { apply Z.ltb_ge. rewrite NB, <- EX. pose proof (batches_bytes_lb (map fst X0) ltac:(apply Forall_map; exact SZ)) as LB. rewrite length_map in LB. lia. }
  rewrite OV.
  replace ((Q_BATCH_BYTES * Z.of_nat (length X0) <? a_qglob_bytes st) && (a_qglob_bytes st * 100 <? Q_BATCH_BYTES * Z.of_nat (length X0) * 200))
    with (qrec_mergeb (Z.of_nat (length X0)) (a_qglob_bytes st)) by reflexivity.
  destruct X0 as [|cur R].
  { (* [comment removed for export] *)
    cbn [map] in EX. assert (B0 : a_qglob_bytes st = 0) by (rewrite NB, <- EX; reflexivity). rewrite B0 in *.
    clear KP. destruct (qrec_mergeb _ _); cbn -[Z.ltb do_recycle set_qglob aundef_ Q_BATCH_BYTES];
      change (Z.of_nat 0) with 0; rewrite ?Z.mul_0_r, ?Z.sub_0_r;      (* [comment removed for export] *)
      replace (min_size <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
  destruct (qrec_mergeb (Z.of_nat (length (cur :: R))) (a_qglob_bytes st)) eqn:EMB; rewrite ?EMB in KP |- *;
    change (@length bq (cur :: R)) with (@length (abatch * qbatchc) (cur :: R)); rewrite ?EMB.      (* [comment removed for export] *)
  - cbn [map]. unfold amerge_fun in *. pose proof (merge_bq_fst R cur) as MF. pose proof (merge_bq_keeps R cur LOK) as MK.
    destruct (merge_batches (fst cur) (map fst R)) as [[l ex] exb]. destruct (merge_bq cur R) as [l2 e2]. cbn [fst snd] in MF, KP |- *.
    destruct MF as (<- & <- & ->). (nd_pre MK 6%nat; intros _ _ LO2 EM SZ2 BB; nd_post).
    assert (SZl : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l2) by (apply SZ2; exact SZ).
    assert (EBl : a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2) = batches_bytes (map fst l2)) by (rewrite NB, <- EX; cbn [map] in BB |- *; unfold Q_BATCH_BYTES, bq in *; lia).
    pose proof (deq_bq_stop l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size EBl SZl M0) as STOP.
    pose proof (deq_bq_fst l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size) as DF.
    destruct (deq_bq l2 _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP.
    rewrite map_app. reflexivity.
  - replace (a_qglob_bytes st - 0) with (a_qglob_bytes st) by lia.
    try (replace (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (@length bq [])) with (a_qglob_bytes st) in KP |- * by (cbn [length Z.of_nat]; lia)).
    cbn [length] in KP |- *. change (Z.of_nat 0) with 0 in KP |- *. rewrite ?Z.mul_0_r, ?Z.sub_0_r. rewrite ?Z.mul_0_r, ?Z.sub_0_r in KP.      (* [comment removed for export] *)
    pose proof (deq_bq_stop (cur :: R) (a_qglob_bytes st) min_size ltac:(rewrite NB, EX; reflexivity) SZ M0) as STOP.
    pose proof (deq_bq_fst (cur :: R) (a_qglob_bytes st) min_size) as DF.
    destruct (deq_bq (cur :: R) _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP.
    cbn [app]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AREP_qglob : forall AQ AQ' AS AS' ADp AFp L st X m g gb,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L (set_qglob g gb st) X m -> (AS L st X m -> AS' L (set_qglob g gb st) X m) ->
  AREP (mkAHoles AQ' AS' ADp AFp) L (set_qglob g gb st) X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m g gb (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disj_objs_img : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr ASECc AD AF.
(* [comment removed for export] *)
Definition AHq (R : qrconc) (mc mr : Z) (cs : list achunk) : aholes := mkAHoles (AQdr R mc mr) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
Hypothesis QREC : qrec_front_stmt.
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1804c8 <= a < 0x5d0510) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
(* [comment removed for export] *)
Hypothesis ASECc_qglob : forall cs L st X X' m g gb, ASECc cs L st X m -> ASECc cs L (set_qglob g gb st) X' m.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

#[using="AHr HL"] Lemma HLq : forall R mc mr cs, ahole_laws (AHq R mc mr cs).
Proof.
  intros R mc mr cs. destruct (HL R cs) as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHq AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in *; try assumption.
  intros L st st' X X' m m' W AQ MU WM UT QS. eapply AQdr_frame; eassumption.
Qed.

(* [comment removed for export] *)
Definition aqrec_ret (L : alayout) (RNG : footprint) (LB : list ablock)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (R : qrconc) (lo min_size : Z) (m : amem)
    (st1 : astate) (X1 : aconc) (RNG1 : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 R1,
    ms' = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m1 (seg_rom asegs)
    /\ fp_le RNG RNG1 /\ arng L RNG1 st1
    /\ qr_tmp R1 = [] /\ qr_pendb R1 = [] /\ qr_pend R1 = [] /\ qr_loc R1 = qr_loc R
    /\ AREP (AHq R1 0 0 (csx st1 R1)) L st1 X1 m1 /\ ablocks L st1 X1 LB /\ AF L LB m1
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
    /\ munch [(0, bv_unsigned sp)]%Z m m1 /\ cpres L (bv_unsigned sp) LB m m1
    /\ a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st
    /\ a_nres st1 = a_nres st /\ a_ptr_array st1 = a_ptr_array st /\ a_space_beg st1 = a_space_beg st
    /\ a_qglob_bytes st1 <= min_size.

Definition aqrec__stmt : Prop := forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint) (LB : list ablock) (R : qrconc) (X : aconc) (st : astate) (m : amem) (lo min_size : Z) (cbs : word)
    (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  alayout_ok L -> arng L RNG st -> AREP (AHq R 0 1 (csx st R)) L st X m ->
  qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  ablocks L st X LB -> AF L LB m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
  ATOP <= lo -> lo <= bv_unsigned sp - AQREC_STACK -> bv_unsigned sp <= 2^47 ->
  a_qglob_bytes st < 2^56 -> 0 <= min_size < 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st1 X1 RNG1 ms', aqrec_ret L RNG LB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st R lo min_size m st1 X1 RNG1 ms' ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (recycle st min_size K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 min_size) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 aqrec_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 0).
Variable K : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 4).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 5).
Variable R : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 6).
Variable X : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 7).
Variable st : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 8).
Variable m : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 9).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 10).
Variable min_size : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 11).
Variable cbs : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 12).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 13).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 14).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 15).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 16).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 17).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 18).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 19).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 20).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 21).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 22).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 23).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 24).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 25).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 26).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 27).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 28).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 29).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 30).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 31).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 32).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 33).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 34).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 35).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 36).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 37).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 40).
#[using="RSEC AHr HL SREC QREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres ASECc_qglob RSEC_app RSEC_perm' RSEC_mono' RSEC_arng"] Lemma aqrec__body : ltac:(let T := type of (fun (h : aqrec__stmt) => h RT K Q L RNG LB R X st m lo min_size cbs ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (K, (Q, (L, (RNG, (LB, (R, (X, (st, (m, (lo, (min_size, (cbs, (ra, (sp, (gp, (t0, (t1, (t2, (s0, (s1, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, fc))))))))))))))))))))))))))))))))))))))))) as _.

  intros ALO ARNG AR ET EB EP BL HF MI ST CEIL LO SP47 GB56 MIN RSTK KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. atop_facts.
  pose proof AR as AR0. (nd_pre AR0 8%nat; intros WF _ _ _ _ HQ HS _; nd_post). cbn [ah_quar ah_sec AHq] in HQ, HS.
  pose proof HQ as HQ0. (nd_pre HQ0 9%nat; intros QC MX TC GL TB IA CP NUM NT; nd_post).
  pose proof CP as CP0. (nd_pre CP0 8%nat; intros LN1 LN2 _ _ NDB BS _ NN; nd_post).
  (pose proof NUM as ndP__; nd_pre ndP__ 3%nat; intros NB1 NB2 NF; nd_post).
  destruct GL as [GH GA].
  set (X0 := combine (a_qglob st) (qr_glob R)).
  assert (EX1 : map fst X0 = a_qglob st) by (subst X0; apply map_fst_combine'; exact LN2).
  assert (EX2 : map snd X0 = qr_glob R) by (subst X0; apply map_snd_combine; exact LN2).
  assert (CH : chain L m X0 0) by (unfold chain; rewrite EX1, EX2; exact GA).
  pose proof (chain_bqlen L m X0 0 CH) as LOK.
  assert (SZ : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0).
  { apply Forall_app in NF. destruct NF as [_ NFg]. rewrite <- EX1 in NFg. clear -NFg. induction X0; [constructor|]. inversion NFg; subst. constructor; [assumption| apply IHX0; assumption]. }
  (* [comment removed for export] *)
  pose proof (recycle_eq st X0 min_size K EX1 NB2 SZ LOK (proj1 MIN)) as ME.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB2, EX1; reflexivity)) as KP.
  destruct (qrec_fun X0 (a_qglob_bytes st) min_size) as [[rest T] bytes2] eqn:EQF.
  (nd_pre KP 5%nat; intros PE PS LOK2 SZ2 EB2; nd_post). rewrite ME. clear ME.
  (* [comment removed for export] *)
  assert (XB : forall x, In x X0 -> exists bb, In bb (x_busy X) /\ xb_st bb = BBatch /\ xb_class bb = K_BATCH_CLASS /\ xb_slot bb = qb_slot (snd x)).
  { intros x Hx. apply (qcoupled_rec_bslot_busy L st X R _ CP). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (GEO : Forall (bgeom L AQ_GCACHE (bv_unsigned sp - 80)) X0).
  { apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
    unfold bgeom, baddr, abatch_addr, AIMG_HI, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. lia. }
  assert (SL0 : Forall (fun x => 0 <= qb_slot (snd x)) X0).
  { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) NN). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (NDX : List.NoDup (bqslots X0)).
  { unfold bqslots. rewrite <- (map_map snd qb_slot), EX2. unfold qr_bslots in NDB. rewrite !map_app in NDB.
    apply NoDup_app_remove_r in NDB. apply NoDup_app_remove_l in NDB. apply NoDup_app_remove_r in NDB. exact NDB. }
  assert (LEN40 : Z.of_nat (length X0) < 2^40).
  { pose proof (nodup_range_len (qr_bslots R) (Z.to_nat 458752) NDB) as LEN.
    assert (HFB : Forall (fun k => 0 <= k < Z.of_nat (Z.to_nat 458752)) (qr_bslots R)).
    { apply Forall_forall. intros k Hk. (nd_pre (proj1 (BS k) Hk) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ KR G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
      unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
    specialize (LEN HFB). unfold qr_bslots in LEN. rewrite length_app, !length_map, !length_app, length_map, <- EX2, length_map in LEN. clear -LEN. lia. }
  assert (RB : Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X0).
  { apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ _ G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3.
    (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _).
    unfold baddr, abatch_addr, Q_BATCH_BYTES. eapply rng_sub; [exact RR1| clear -G1; lia| clear -G2 G3; lia]. }
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.arng_tls _ _ _ ARNG) as RTLS.      (* [comment removed for export] *)
  rewrite <- EX1, <- EX2, length_map, <- tfirst_qfirst, <- tlast_qlast in GH.
  (* [comment removed for export] *)
  unfold aqrec_entry. iprefix. eapply evtF_cut.
  { eapply (QREC L RNG X0 (a_qglob_bytes st) min_size lo); try eassumption; try reflexivity;
      try lazymatch goal with
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => clear -LO; lia
      | |- rw_cells _ _ AQ_MUTEX _ => exact MX
      | |- _ = batches_bytes _ => rewrite EX1; exact NB2
      | |- _ (map _ X0) => first [exact NDX| apply (proj2 (NoDup_ListNoDup (bqslots X0))); exact NDX| apply (proj1 (NoDup_ListNoDup (bqslots X0))); exact NDX]
      end.
    all: match goal with |- ?G => idtac "REMQ" G end. all: fail. }
  cbv beta. intros ms1 PQ. unfold qrec_front_post in PQ. rewrite EQF in PQ.
  (nd_pre PQ 20%nat; intros t0' t1' t2' xs0 xs1 xs2 xs3 xs4 a0' a4' a5' a6' a7' t3' t4' t5' t6' tbw m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MUq WMq MI2 ST2 TH2 SAV2 MX2 GH2 CHr CHt EB2' BLE; nd_post).
  rewrite <- EB2 in *. clear EB2'.
  (* [comment removed for export] *)
  set (R2 := mkQR (qr_loc R) (map snd rest) (qr_ia R) T [] [] (qr_qpend R)).
  set (stD := set_qglob (map fst rest) bytes2 st).
  set (Wq := ([(bv_unsigned sp - 96, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X0)%Z) in *.
  assert (DJQ : forall A n, A + n <= AIMG_HI -> (A + n <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A) -> disjoint_from Wq A n).
  { intros A n H1 H2. subst Wq. apply disjoint_from_app; [| eapply disj_objs_img; [exact GEO| exact H1]].
    cbn [disjoint_from app]. unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE in *. clear -H1 H2 CEIL LO. repeat split; lia. }
  (* [comment removed for export] *)
  assert (DJL : forall q, In q (qr_loc R) -> disjoint_from Wq (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. subst Wq. apply disjoint_from_app.
    - (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
      cbn [disjoint_from app]. unfold abatch_addr, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. repeat split; lia.
    - apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
      assert (NE : qb_slot (snd x) <> qb_slot q).
      { intros E. (nd_pre (in_split _ _ Hq) 3%nat; intros l1 l2 EL; nd_post). pose proof NDB as ND0. unfold qr_bslots in ND0. rewrite EL, !map_app in ND0. cbn [map] in ND0.
        rewrite <- !app_assoc in ND0. cbn [app] in ND0.
        apply (List.NoDup_remove_2 _ _ _ ND0). apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
        rewrite <- E, <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
      pose proof (proj1 (Forall_forall _ _) SL0 x Hx) as S1. pose proof (proj1 (Forall_forall _ _) NN (qb_slot q) ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) as S2.
      cbn beta in S1, S2. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
      destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot q)); [left| right]; nia. }
  (* [comment removed for export] *)
  assert (HQ2 : AQdr R2 0 0 L stD X m2).
  { unfold AQdr. subst R2 stD. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob a_space_beg].
    split. { eapply cells_frame; [exact QC| exact MUq| exact WMq|]. cbn [cells_size csize Nat.add]. apply DJQ; unfold AQ_MAX, AIMG_HI, AQ_MUTEX; clear; lia. }
    split; [exact MX2|].
    split. { eapply (aqcache_frame L Wq m m2 MUq WMq); [exact TC| | exact DJL].
             (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 _ TL4u; nd_post). unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
             subst Wq. apply disjoint_from_app.
             - cbn [disjoint_from app]. unfold aq_tcache, AQ_MUTEX, AQ_GCACHE in *. clear -TL4u TL2 CEIL LO. repeat split; lia.
             - apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
               (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post). (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ G6 G7; nd_post).
               unfold xb_alloc in G6, G7. rewrite Cb, Kb in G6. rewrite Cb, Kb, size_of_class_24 in G7.
               pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTR. unfold baddr, abatch_addr, aq_tcache, Q_BATCH_BYTES. clear -G6 G7 DTR. lia. }
    split. { split; [| exact CHr]. rewrite length_map, <- tfirst_qfirst, <- tlast_qlast. exact GH2. }
    split; [exact CHt|].
    split. { eapply (aintal_frame Wq m m2 MUq WMq); [exact IA| |]; apply DJQ; unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIMG_HI, AQ_MUTEX, AQ_GCACHE; clear; lia. }
    split. { eapply qcoupled_rec_perm; [exact CP| exact LN1| cbn [qr_glob a_qglob set_qglob]; rewrite !length_map; reflexivity| | | reflexivity].      (* [comment removed for export] *)
             - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend a_qloc a_qglob set_qglob]. rewrite ET, EP. cbn [map qentries]. rewrite !List.app_nil_r.
               apply Permutation_app_head. fold (bqentries rest). fold (bqentries T). rewrite <- bqentries_app.
               eapply Permutation_trans; [exact PE|]. unfold bqentries. rewrite EX1, EX2. apply Permutation_refl.
             - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map]. rewrite !List.app_nil_r, !map_app.
               apply Permutation_app_head. rewrite !map_map. change (map (fun x : abatch * qbatchc => qb_slot (snd x)) rest ++ map (fun x => qb_slot (snd x)) T) with (bqslots rest ++ bqslots T).
               rewrite <- bqslots_app. eapply Permutation_trans; [exact PS|]. unfold bqslots. rewrite <- EX2, map_map. apply Permutation_refl. }
    split. { unfold qnumR. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob]. split; [exact NB1|]. split; [first [exact EB2| reflexivity]|].
             apply Forall_app in NF. destruct NF as [NFl _]. apply Forall_app. split; [exact NFl|].
             apply Forall_app in SZ2. destruct SZ2 as [SZr _]. clear -SZr. induction rest as [|y rest' IHr]; [constructor|]. inversion SZr; subst. constructor; [assumption| apply IHr; assumption]. }
    unfold qnum_tmp. apply Forall_app in SZ2. destruct SZ2 as [_ SZt]. clear -SZt. induction T as [|y T' IHt]; [constructor|]. inversion SZt; subst. constructor; [assumption| apply IHt; assumption]. }
  (* [comment removed for export] *)
  assert (QWP : Forall (qwp L X) Wq).
  { subst Wq. apply Forall_app. split.
    - repeat (apply Forall_cons || apply Forall_nil); unfold qwp; cbn [fst snd]; intros _;
        unfold AQ_MUTEX, AQ_GCACHE; [left; clear -CEIL LO; lia| right; left; clear; lia| right; left; clear; lia].
    - apply Forall_map. apply Forall_forall. intros x Hx. unfold qwp. cbn [fst snd]. intros _. right; right.
      (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post). exists bb. split; [exact Hb|]. split; [exact Sb|].
      unfold xb_alloc, baddr, abatch_addr. rewrite Cb, Kb, size_of_class_24. unfold Q_BATCH_BYTES. clear; lia. }
  (* [comment removed for export] *)
  assert (ESX : csx st R = sec_chunks_of st ++ []).
  { unfold csx, inflight, secsT. rewrite ET, EP. reflexivity. }
  assert (PCSX : Permutation (csx st R) (csx stD R2)).
  { rewrite ESX, List.app_nil_r. unfold csx, inflight, secsT. subst R2 stD. cbn [qr_tmp qr_pend]. change (esecs []) with (@nil achunk). rewrite List.app_nil_r.
    unfold sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob set_qglob]. rewrite !flat_map_app_chunks, !filter_is_sec_app, <- !app_assoc.
    apply Permutation_app_head. apply Permutation_app_head.
    rewrite <- EX1, <- (map_fst_bqentries X0 LOK).
    pose proof LOK2 as LOK3. apply Forall_app in LOK3. destruct LOK3 as [LOKr LOKt]. rewrite <- (map_fst_bqentries rest LOKr).
    change (List.filter is_sec (map fst (bqentries X0))) with (esecs (bqentries X0)).
    change (List.filter is_sec (map fst (bqentries rest))) with (esecs (bqentries rest)).
    fold (bqentries T).      (* [comment removed for export] *)
    rewrite <- esecs_app, <- bqentries_app. apply esecs_perm. apply Permutation_sym. exact PE. }
  assert (AR2 : AREP (AHr R2 (csx stD R2)) L stD X m2).
  { unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr.
    pose proof (AREP_frame_qw (AQdr R 0 1) (ASECc (csx st R)) AD AF (HLq R 0 1 (csx st R))
                  (fun L' s X' m' => AQdr R2 0 0 L' (set_qglob (map fst rest) bytes2 s) X' m') L st X m m2 Wq ALO AR MUq WMq QWP HQ2) as A1.
    subst stD. eapply AREP_qglob; [exact A1| exact HQ2| intros HS1; eapply ASECc_perm; [exact PCSX| eapply ASECc_qglob; exact HS1]]. }
  assert (ARNG2 : arng L RNG stD).
  { eapply (arng_sub L RNG st stD); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros ch Hch. assert (IN2 : In ch (csx stD R2)) by (unfold csx; apply in_app_iff; left; exact Hch).
    pose proof (Permutation_in _ (Permutation_sym PCSX) IN2) as IN1. rewrite ESX, List.app_nil_r in IN1. exact IN1. }
  assert (RS2 : RSEC (inflight R2) RNG).
  { pose proof (RSEC_arng L RNG st ARNG) as R0. rewrite <- (List.app_nil_r (sec_chunks_of st)), <- ESX in R0.
    pose proof (RSEC_perm' _ _ _ PCSX R0) as R1. unfold csx in R1. apply (proj1 (RSEC_app _ _ _)) in R1. exact (proj2 R1). }
  assert (BL2 : ablocks L stD X LB) by (eapply ablocks_same; [exact BL| reflexivity| reflexivity]).
  assert (HF2 : AF L LB m2).
  { eapply (hf_frame _ (HL R (csx st R)) L LB m m2 Wq); [exact HF| exact MUq| exact WMq|].
    subst Wq. unfold fake_untouched. apply Forall_app. split.
    - pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD. pose proof atop_range as ATR.   (* [comment removed for export] *)
      assert (SF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + 11571200 / 8 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF in *; clear -OF ATR; Z.div_mod_to_equations; lia).
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold AQ_MUTEX, AQ_GCACHE in *; rewrite ?shlen_div; clear -CEIL LO OF OD SF ATR; repeat split; lia.
    - apply Forall_map. apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ _ G1 G2 (G3a & G3 & G3b) _; nd_post). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3, G3a, G3b.
      eapply (wpiece_fake L ATOP ATOP); [exact ALO| apply Z.le_refl|]. unfold wpiece. right; right; right. cbn [fst snd].
      unfold baddr, abatch_addr, Q_BATCH_BYTES, K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      clear -G1 G2 G3 G3a G3b. lia. }
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 3%nat; intros TL1 TL2 _; nd_post).
  (* [comment removed for export] *)
  apply evtF_done.
  set (spD := Z_to_bv 64 (bv_unsigned sp - 80) : word).
  assert (USD : bv_unsigned spD = bv_unsigned sp - 80) by (subst spD; rewrite Z_to_bv_unsigned; apply Z.mod_small; unfold bv_modulus; clear -SPR CEIL LO; lia).
  eapply (adorec ASECc AD AF RSEC HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng
            L lo (bv_unsigned sp - 80) (bv_unsigned sp) LB cbs RNG m2 stD (Z_to_bv 64 aqrec_retpc) spD gp xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 F fc);
    rewrite ?USD;
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- ATOP <= _ => atop_facts; exact CEIL
    | |- lo <= _ => clear -LO; lia
    | |- _ <= 2 ^ 47 => clear -SP47 CEIL LO; lia
    | |- bv_unsigned sp - 80 <= bv_unsigned sp - 80 => apply Z.le_refl
    | |- bv_unsigned sp - 80 + 32 <= bv_unsigned sp => clear; lia
    | |- rng _ lo _ => eapply rng_sub; [exact RSTK| clear; lia| clear; lia]
    | |- rng _ (bv_unsigned sp - 80) _ => eapply rng_sub; [exact RSTK| clear -CEIL LO; lia| clear -CEIL LO; lia]
    | |- arng _ _ _ => exact ARNG2
    | |- AREP _ _ _ _ _ => exact AR2
    | |- ablocks _ _ _ _ => exact BL2
    | |- AF _ _ _ => exact HF2
    | |- RSEC _ _ => exact RS2
    | |- qr_tmp _ = _ => reflexivity
    | |- qr_pendb _ = _ => reflexivity
    | |- qr_pend _ = _ => reflexivity
    | |- mem_inv _ _ => exact MI2
    | |- stk _ _ _ _ => exact ST2
    | |- rw_cells _ _ _ (thdr _ _ _) => unfold thdr; rewrite <- tfirst_qfirst, <- tlast_qlast; exact TH2
    end.
  (* [comment removed for export] *)
  intros st3 X3 RNG3 m3 tb' t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c INV3 ST3 TH3.
  (pose proof INV3 as ndP__; nd_pre ndP__ 11%nat; intros ARNG3 AR3 BL3 HF3 RS3 MI3 ST3' FLE3 MU3 CP3 SK3; nd_post).
  rewrite USD in MU3. unfold thdr in TH3. cbn [length map qfirst qlast qaddrs hd List.last Z.of_nat] in TH3.
  pose proof (cells_frameD _ _ _ _ _ SAV2 MU3 ltac:(cbn [cells_size csize Nat.add disjoint_from]; clear; lia)) as SAV3.
  replace (ret_pc (Z_to_bv 64 aqrec_retpc)) with (Z_to_bv 64 aqrec_retpc : word) by (symmetry; apply ret_pc_even; [unfold aqrec_retpc; lia| reflexivity]).
  unfold aqrec_retpc. subst spD.
  assert (RSTK3 : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FLE3| exact RSTK]).
  assert (FRR : rw_cells asegs m3 (bv_unsigned sp - 80) ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 tb'] ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact TH3|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp - 80 + Z.of_nat 32) with (bv_unsigned sp - 48) by (clear; lia). exact SAV3. }
  clear TH3 SAV3. cbn [app] in FRR.
  iprefix.
  do 6 step.                                  (* [comment removed for export] *)
  zstep.                                      (* [comment removed for export] *)
  setreg 2 sp ltac:(replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
  step.                                       (* [comment removed for export] *)
  release_frame FRR ST3 (bv_unsigned sp).
  apply evtF_done. eapply KONT. unfold aqrec_ret.
  exists t0c, t1c, t2c, a0c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, m3, (qr_done R2).
  split; [reflexivity|].
  split; [intros bb j Hb; apply FLE3, Hb|]. split; [exact ARNG3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact AR3|]. split; [exact BL3|]. split; [exact HF3|]. split; [exact MI3|]. split; [exact ST3|].
  split. { (* [comment removed for export] *)
    eapply munch_trans; [| eapply munch_weaken; [| exact MU3]; unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; split; [clear -Hx; lia| split; [clear -Hx SPR CEIL LO; lia| exact I]]].
    eapply munch_weaken; [| exact MUq]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. subst Wq.
    apply outside_of_In. intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - cbn [In] in Hiv. unfold AQ_MUTEX, AQ_GCACHE in *. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; clear -Hx CEIL LO SPR; lia.
    - apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). cbn [fst snd]. (pose proof (proj1 (Forall_forall _ _) GEO y Hy) as ndP__; nd_pre ndP__ 3%nat; intros G1 G2 _; nd_post).
      unfold AIMG_HI, Q_BATCH_BYTES in *. clear -Hx G1 G2 CEIL LO SPR. lia. }
  split. { (* [comment removed for export] *)
    eapply cpres_trans; [| exact CP3]. eapply cpres_of_munch; [exact MUq|]. subst Wq. apply np_fp_app.
    - intros iv Hiv. cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd].
      + eapply (np_high L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| apply Z.le_refl].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_MUTEX in *; clear -Ha; lia| unfold AQ_MUTEX; clear; lia| unfold AQ_MUTEX, AIMG_HI; clear; lia].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_GCACHE in *; clear -Ha; lia| unfold AQ_GCACHE; clear; lia| unfold AQ_GCACHE, AIMG_HI; clear; lia].
    - intros iv Hiv. apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). cbn [fst snd]. (nd_pre (XB y Hy) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (nd_pre (in_split _ _ Hb) 3%nat; intros l1 l2 EXB; nd_post). destruct bb as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
      intros a Ha. eapply (np_slot L st X LB (bv_unsigned sp) BBatch K_BATCH_CLASS (qb_slot (snd y)) bn bb1 bctx l1 l2);
        [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| exact EXB| intros p; discriminate| | | exact Ha];
        unfold baddr, abatch_addr; [apply Z.le_refl| rewrite size_of_class_24; unfold Q_BATCH_BYTES; apply Z.le_refl]. }
  (nd_pre SK3 9%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9; nd_post). subst stD. cbn [a_live a_next a_qloc a_qloc_bytes a_nres a_ptr_array a_space_beg set_qglob] in K1, K2, K3, K4, K5, K6, K7, K8, K9.
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
  cbn [a_qglob_bytes set_qglob] in K6. rewrite K6. exact BLE.
Qed.
End Zd1.
#[using="RSEC AHr HL SREC QREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres ASECc_qglob RSEC_app RSEC_perm' RSEC_mono' RSEC_arng"] Theorem aqrec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint) (LB : list ablock) (R : qrconc) (X : aconc) (st : astate) (m : amem) (lo min_size : Z) (cbs : word)
    (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  alayout_ok L -> arng L RNG st -> AREP (AHq R 0 1 (csx st R)) L st X m ->
  qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  ablocks L st X LB -> AF L LB m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
  ATOP <= lo -> lo <= bv_unsigned sp - AQREC_STACK -> bv_unsigned sp <= 2^47 ->
  a_qglob_bytes st < 2^56 -> 0 <= min_size < 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st1 X1 RNG1 ms', aqrec_ret L RNG LB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st R lo min_size m st1 X1 RNG1 ms' ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (recycle st min_size K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 min_size) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 aqrec_entry) fc None m (seg_rom asegs)).
Proof. exact aqrec__body. Qed.
End QRec.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ACdeallocP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_aqrec_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepQW.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition aqrec_entry : Z := 0x35b08.
Definition aqrec_retpc : Z := 0x35c78.     (* [comment removed for export] *)
End CANSEC1.
Notation AQREC_STACK := 1216 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition bqentries (X : list bq) : list (achunk * Z) := qentries (map fst X) (map snd X).
Definition bqslots (X : list bq) : list Z := map (fun x => qb_slot (snd x)) X.
Definition bqlen_ok (x : bq) : Prop := length (qb_ks (snd x)) = length (b_chunks (fst x)).

#[using="Type"] Lemma bqentries_cons : forall x X, bqentries (x :: X) = combine (b_chunks (fst x)) (qb_ks (snd x)) ++ bqentries X.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bqentries_app : forall X Y, bqentries (X ++ Y) = bqentries X ++ bqentries Y.
Proof. induction X as [|x X IH]; intros Y; [reflexivity|]. cbn [app]. rewrite !bqentries_cons, IH, app_assoc. reflexivity. Qed.
#[using="Type"] Lemma bqslots_app : forall X Y, bqslots (X ++ Y) = bqslots X ++ bqslots Y.
Proof. intros. unfold bqslots. apply map_app. Qed.

#[using="Type"] Lemma combine_app : forall {A B} (l1 l2 : list A) (k1 k2 : list B), length k1 = length l1 ->
  combine (l1 ++ l2) (k1 ++ k2) = combine l1 k1 ++ combine l2 k2.
Proof. induction l1 as [|a l1 IH]; intros l2 [|b k1] k2 LEN; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma merge_bq_keeps : forall R cur, Forall bqlen_ok (cur :: R) ->
  let '(l, e) := merge_bq cur R in
     Permutation (bqentries (l ++ e)) (bqentries (cur :: R))
  /\ Permutation (bqslots (l ++ e)) (bqslots (cur :: R))
  /\ Forall bqlen_ok (l ++ e)
  /\ Forall (fun x => b_size (fst x) = Q_BATCH_BYTES /\ b_count (fst x) = 0 /\ b_chunks (fst x) = [] /\ qb_ks (snd x) = []) e
  /\ (Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l)
  /\ batches_bytes (map fst l) + Q_BATCH_BYTES * Z.of_nat (length e) = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur LOK; cbn [merge_bq].
  - cbn [app length Z.of_nat]. split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [exact LOK|]. split; [constructor|].
    split; [intros H; exact H| lia].
  - pose proof (Forall_inv LOK) as L1. pose proof (Forall_inv (Forall_inv_tail LOK)) as L2. pose proof (Forall_inv_tail (Forall_inv_tail LOK)) as L3.
    unfold bqlen_ok in L1, L2.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) ltac:(constructor; [unfold bqlen_ok, bq_merge; cbn; rewrite !length_app; lia| exact L3])).
      destruct (merge_bq (bq_merge cur nx) R) as [l e]. (nd_pre IH 6%nat; intros PE PS LO EM SZ BB; nd_post).
      split; [| split; [| split; [| split; [| split]]]].
      * rewrite bqentries_app, bqentries_cons. cbn [bq_empty fst snd b_chunks qb_ks combine app].
        rewrite <- bqentries_app. eapply Permutation_trans; [exact PE|].
        rewrite !bqentries_cons. cbn [bq_merge fst snd b_chunks qb_ks]. rewrite combine_app by lia.
        rewrite <- !app_assoc. apply Permutation_app_swap_app.
      * rewrite bqslots_app. cbn [bqslots map bq_empty snd qb_slot]. fold (bqslots e). fold (bqslots l).
        eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
        eapply Permutation_trans; [apply perm_skip; rewrite <- bqslots_app; exact PS|].
        cbn [bqslots map bq_merge snd qb_slot]. apply perm_swap.
      * apply Forall_app in LO. destruct LO as [LOl LOe]. apply Forall_app. split; [exact LOl|]. constructor; [| exact LOe]. unfold bqlen_ok, bq_empty. reflexivity.
      * constructor; [| exact EM]. cbn. repeat split; reflexivity.
      * intros SZS. apply SZ. constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZS))].
        cbn [bq_merge fst b_size]. pose proof (Forall_inv SZS) as Z1. pose proof (Forall_inv (Forall_inv_tail SZS)) as Z2. cbn beta in Z1, Z2. lia.
      * cbn [length map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. cbn [bq_merge fst b_size] in BB. unfold Q_BATCH_BYTES in *. lia.
    + specialize (IH nx ltac:(constructor; [exact L2| exact L3])).
      destruct (merge_bq nx R) as [l e]. (nd_pre IH 6%nat; intros PE PS LO EM SZ BB; nd_post).
      split; [| split; [| split; [| split; [| split]]]].
      * cbn [app]. rewrite !bqentries_cons. apply Permutation_app_head. exact PE.
      * cbn [app bqslots map]. apply perm_skip. exact PS.
      * cbn [app]. constructor; [exact L1| exact LO].
      * exact EM.
      * intros SZS. constructor; [exact (Forall_inv SZS)| apply SZ; exact (Forall_inv_tail SZS)].
      * cbn [map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma deq_bq_split : forall gl bytes min_size,
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in gl = taken ++ rest /\ bytes2 = bytes - batches_bytes (map fst taken).
Proof.
  induction gl as [|b gl IH]; intros bytes min_size; cbn [deq_bq].
  - cbn. split; [reflexivity| lia].
  - destruct (min_size <? bytes).
    + specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq gl _ _) as [[tk rs] b2]. destruct IH as [E1 E2].
      cbn [app map]. rewrite batches_bytes_cons. split; [rewrite <- E1; reflexivity| lia].
    + cbn. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qrec_fun_keeps : forall X bytes min_size, Forall bqlen_ok X -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X ->
  bytes = batches_bytes (map fst X) ->
  let '(rest, T, bytes2) := qrec_fun X bytes min_size in
     Permutation (bqentries (rest ++ T)) (bqentries X)
  /\ Permutation (bqslots (rest ++ T)) (bqslots X)
  /\ Forall bqlen_ok (rest ++ T)
  /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest ++ T)
  /\ bytes2 = batches_bytes (map fst rest).
Proof.
  intros X bytes min_size LOK SZ EB. unfold qrec_fun.
  assert (GEN : forall gl ex, Permutation (bqentries (gl ++ ex)) (bqentries X) -> Permutation (bqslots (gl ++ ex)) (bqslots X) ->
             Forall bqlen_ok (gl ++ ex) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (gl ++ ex) ->
             batches_bytes (map fst gl) + Q_BATCH_BYTES * Z.of_nat (length ex) = bytes ->
             let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
             let '(rest0, T, bytes0) := (rest, ex ++ taken, bytes2) in
             Permutation (bqentries (rest0 ++ T)) (bqentries X) /\ Permutation (bqslots (rest0 ++ T)) (bqslots X) /\ Forall bqlen_ok (rest0 ++ T)
             /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest0 ++ T) /\ bytes0 = batches_bytes (map fst rest0)).
  { intros gl ex PE PS LO SZS BB.
    pose proof (deq_bq_split gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size) as DS.
    destruct (deq_bq gl _ min_size) as [[taken rest] bytes2]. destruct DS as [EGL EB2]. subst gl.
    assert (P3 : forall {A} (a b c : list A), Permutation (b ++ (c ++ a)) ((a ++ b) ++ c)).
    { intros A a b c. rewrite (app_assoc b c a). eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite app_assoc. apply Permutation_refl. }
    split; [| split; [| split; [| split]]].
    - eapply Permutation_trans; [| exact PE]. rewrite !bqentries_app. apply P3.
    - eapply Permutation_trans; [| exact PS]. rewrite !bqslots_app. apply P3.
    - rewrite !Forall_app in LO |- *. tauto.
    - rewrite !Forall_app in SZS |- *. tauto.
    - rewrite map_app, batches_bytes_app in BB. unfold Q_BATCH_BYTES, bq in *. lia. }
  destruct (qrec_mergeb (Z.of_nat (length X)) bytes).
  - destruct X as [|cur R].
    + cbn. repeat split; try apply Permutation_refl; try constructor. cbn in EB. lia.
    + unfold amerge_fun. pose proof (merge_bq_keeps R cur LOK) as MK. destruct (merge_bq cur R) as [l e]. (nd_pre MK 6%nat; intros PE PS LO EM SZl BB; nd_post).
      assert (SZ2 : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (l ++ e)).
      { apply Forall_app. split; [exact (SZl SZ)|]. eapply Forall_impl; [| exact EM]. cbn beta. intros x (E & _). rewrite E. lia. }
      pose proof (GEN l e PE PS LO SZ2 ltac:(rewrite EB; exact BB)) as G. revert G.
      destruct (deq_bq l _ min_size) as [[taken rest] bytes2]. intros G. exact G.
  - pose proof (GEN X [] ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; exact LOK)
                  ltac:(rewrite app_nil_r; exact SZ) ltac:(cbn [length Z.of_nat]; lia)) as G. revert G.
    cbn [length Z.of_nat Z.mul]. destruct (deq_bq X _ min_size) as [[taken rest] bytes2]. cbn [app]. intros G. exact G.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma map_fst_combine' : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.
#[using="Type"] Lemma map_snd_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map snd (combine l l') = l'.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma tfirst_qfirst : forall L X, tfirst L X 0 = qfirst L (map snd X).
Proof. intros L [|x X]; reflexivity. Qed.
#[using="Type"] Lemma tlast_qlast : forall L X, tlast L X 0 = qlast L (map snd X).
Proof. intros L X. unfold tlast, qlast, qaddrs, baddr. rewrite map_map. reflexivity. Qed.

#[using="Type"] Lemma chain_bqlen : forall L m X nxt, chain L m X nxt -> Forall bqlen_ok X.
Proof.
  intros L m X. induction X as [|x X IH]; intros nxt CH; [constructor|].
  unfold chain in CH. cbn [map abatches_to] in CH. destruct CH as [AC CH]. constructor; [| eapply IH; exact CH].
  (nd_pre AC 6%nat; intros _ _ _ _ LEN _; nd_post). exact LEN.
Qed.

#[using="Type"] Lemma map_fst_bqentries : forall X, Forall bqlen_ok X -> map fst (bqentries X) = flat_map b_chunks (map fst X).
Proof.
  induction X as [|x X IH]; intros LOK; [reflexivity|]. rewrite bqentries_cons, map_app. cbn [map flat_map].
  pose proof (Forall_inv LOK) as L1. unfold bqlen_ok in L1. rewrite (map_fst_combine' (b_chunks (fst x)) (qb_ks (snd x)) L1). rewrite IH by exact (Forall_inv_tail LOK). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deq_bq_stop : forall gl bytes min_size, bytes = batches_bytes (map fst gl) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) gl -> 0 <= min_size ->
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in (min_size <? bytes2) = false.
Proof.
  induction gl as [|b gl IH]; intros bytes min_size EB SZ M0; cbn [deq_bq].
  - cbn in EB. apply Z.ltb_ge. lia.
  - destruct (min_size <? bytes) eqn:E; [| exact E].
    specialize (IH (bytes - b_size (fst b)) min_size ltac:(cbn [map] in EB; rewrite batches_bytes_cons in EB; lia) (Forall_inv_tail SZ) M0).
    destruct (deq_bq gl _ _) as [[tk rs] b2]. exact IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_eq : forall {RT} st X0 min_size (K : astate -> AM RT),
  map fst X0 = a_qglob st -> a_qglob_bytes st = batches_bytes (a_qglob st) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0 -> Forall bqlen_ok X0 -> 0 <= min_size ->
  let '(rest, T, bytes2) := qrec_fun X0 (a_qglob_bytes st) min_size in
  recycle st min_size K = do_recycle (set_qglob (map fst rest) bytes2 st) (map fst T) K.
Proof.
  intros RT st X0 min_size K EX NB SZ LOK M0.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB, EX; reflexivity)) as KP.
  unfold qrec_fun in KP |- *. unfold recycle. rewrite <- EX, length_map.
  assert (OV : (a_qglob_bytes st <? Q_BATCH_BYTES * Z.of_nat (length X0)) = false).
  { apply Z.ltb_ge. rewrite NB, <- EX. pose proof (batches_bytes_lb (map fst X0) ltac:(apply Forall_map; exact SZ)) as LB. rewrite length_map in LB. lia. }
  rewrite OV.
  replace ((Q_BATCH_BYTES * Z.of_nat (length X0) <? a_qglob_bytes st) && (a_qglob_bytes st * 100 <? Q_BATCH_BYTES * Z.of_nat (length X0) * 200))
    with (qrec_mergeb (Z.of_nat (length X0)) (a_qglob_bytes st)) by reflexivity.
  destruct X0 as [|cur R].
  { (* [comment removed for export] *)
    cbn [map] in EX. assert (B0 : a_qglob_bytes st = 0) by (rewrite NB, <- EX; reflexivity). rewrite B0 in *.
    clear KP. destruct (qrec_mergeb _ _); cbn -[Z.ltb do_recycle set_qglob aundef_ Q_BATCH_BYTES];
      change (Z.of_nat 0) with 0; rewrite ?Z.mul_0_r, ?Z.sub_0_r;      (* [comment removed for export] *)
      replace (min_size <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
  destruct (qrec_mergeb (Z.of_nat (length (cur :: R))) (a_qglob_bytes st)) eqn:EMB; rewrite ?EMB in KP |- *;
    change (@length bq (cur :: R)) with (@length (abatch * qbatchc) (cur :: R)); rewrite ?EMB.      (* [comment removed for export] *)
  - cbn [map]. unfold amerge_fun in *. pose proof (merge_bq_fst R cur) as MF. pose proof (merge_bq_keeps R cur LOK) as MK.
    destruct (merge_batches (fst cur) (map fst R)) as [[l ex] exb]. destruct (merge_bq cur R) as [l2 e2]. cbn [fst snd] in MF, KP |- *.
    destruct MF as (<- & <- & ->). (nd_pre MK 6%nat; intros _ _ LO2 EM SZ2 BB; nd_post).
    assert (SZl : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l2) by (apply SZ2; exact SZ).
    assert (EBl : a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2) = batches_bytes (map fst l2)) by (rewrite NB, <- EX; cbn [map] in BB |- *; unfold Q_BATCH_BYTES, bq in *; lia).
    pose proof (deq_bq_stop l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size EBl SZl M0) as STOP.
    pose proof (deq_bq_fst l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size) as DF.
    destruct (deq_bq l2 _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP.
    rewrite map_app. reflexivity.
  - replace (a_qglob_bytes st - 0) with (a_qglob_bytes st) by lia.
    try (replace (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (@length bq [])) with (a_qglob_bytes st) in KP |- * by (cbn [length Z.of_nat]; lia)).
    cbn [length] in KP |- *. change (Z.of_nat 0) with 0 in KP |- *. rewrite ?Z.mul_0_r, ?Z.sub_0_r. rewrite ?Z.mul_0_r, ?Z.sub_0_r in KP.      (* [comment removed for export] *)
    pose proof (deq_bq_stop (cur :: R) (a_qglob_bytes st) min_size ltac:(rewrite NB, EX; reflexivity) SZ M0) as STOP.
    pose proof (deq_bq_fst (cur :: R) (a_qglob_bytes st) min_size) as DF.
    destruct (deq_bq (cur :: R) _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP.
    cbn [app]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AREP_qglob : forall AQ AQ' AS AS' ADp AFp L st X m g gb,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L (set_qglob g gb st) X m -> (AS L st X m -> AS' L (set_qglob g gb st) X m) ->
  AREP (mkAHoles AQ' AS' ADp AFp) L (set_qglob g gb st) X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m g gb (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disj_objs_img : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr ASECc AD AF.
(* [comment removed for export] *)
Definition AHq (R : qrconc) (mc mr : Z) (cs : list achunk) : aholes := mkAHoles (AQdr R mc mr) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
Hypothesis QREC : qrec_front_stmt.
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1808c8 <= a < 0x5d0910) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
(* [comment removed for export] *)
Hypothesis ASECc_qglob : forall cs L st X X' m g gb, ASECc cs L st X m -> ASECc cs L (set_qglob g gb st) X' m.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

#[using="AHr HL"] Lemma HLq : forall R mc mr cs, ahole_laws (AHq R mc mr cs).
Proof.
  intros R mc mr cs. destruct (HL R cs) as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHq AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in *; try assumption.
  intros L st st' X X' m m' W AQ MU WM UT QS. eapply AQdr_frame; eassumption.
Qed.

(* [comment removed for export] *)
Definition aqrec_ret (L : alayout) (RNG : footprint) (LB : list ablock)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (R : qrconc) (lo min_size : Z) (m : amem)
    (st1 : astate) (X1 : aconc) (RNG1 : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 R1,
    ms' = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m1 (seg_rom asegs)
    /\ fp_le RNG RNG1 /\ arng L RNG1 st1
    /\ qr_tmp R1 = [] /\ qr_pendb R1 = [] /\ qr_pend R1 = [] /\ qr_loc R1 = qr_loc R
    /\ AREP (AHq R1 0 0 (csx st1 R1)) L st1 X1 m1 /\ ablocks L st1 X1 LB /\ AF L LB m1
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
    /\ munch [(0, bv_unsigned sp)]%Z m m1 /\ cpres L (bv_unsigned sp) LB m m1
    /\ a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st
    /\ a_nres st1 = a_nres st /\ a_ptr_array st1 = a_ptr_array st /\ a_space_beg st1 = a_space_beg st
    /\ a_qglob_bytes st1 <= min_size.

Definition aqrec__stmt : Prop := forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint) (LB : list ablock) (R : qrconc) (X : aconc) (st : astate) (m : amem) (lo min_size : Z) (cbs : word)
    (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  alayout_ok L -> arng L RNG st -> AREP (AHq R 0 1 (csx st R)) L st X m ->
  qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  ablocks L st X LB -> AF L LB m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
  ATOP <= lo -> lo <= bv_unsigned sp - AQREC_STACK -> bv_unsigned sp <= 2^47 ->
  a_qglob_bytes st < 2^56 -> 0 <= min_size < 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st1 X1 RNG1 ms', aqrec_ret L RNG LB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st R lo min_size m st1 X1 RNG1 ms' ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (recycle st min_size K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 min_size) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 aqrec_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 0).
Variable K : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 4).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 5).
Variable R : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 6).
Variable X : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 7).
Variable st : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 8).
Variable m : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 9).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 10).
Variable min_size : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 11).
Variable cbs : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 12).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 13).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 14).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 15).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 16).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 17).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 18).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 19).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 20).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 21).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 22).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 23).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 24).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 25).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 26).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 27).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 28).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 29).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 30).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 31).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 32).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 33).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 34).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 35).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 36).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 37).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'aqrec__stmt 40).
#[using="RSEC AHr HL SREC QREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres ASECc_qglob RSEC_app RSEC_perm' RSEC_mono' RSEC_arng"] Lemma aqrec__body : ltac:(let T := type of (fun (h : aqrec__stmt) => h RT K Q L RNG LB R X st m lo min_size cbs ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (K, (Q, (L, (RNG, (LB, (R, (X, (st, (m, (lo, (min_size, (cbs, (ra, (sp, (gp, (t0, (t1, (t2, (s0, (s1, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, fc))))))))))))))))))))))))))))))))))))))))) as _.

  intros ALO ARNG AR ET EB EP BL HF MI ST CEIL LO SP47 GB56 MIN RSTK KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. atop_facts.
  pose proof AR as AR0. (nd_pre AR0 8%nat; intros WF _ _ _ _ HQ HS _; nd_post). cbn [ah_quar ah_sec AHq] in HQ, HS.
  pose proof HQ as HQ0. (nd_pre HQ0 9%nat; intros QC MX TC GL TB IA CP NUM NT; nd_post).
  pose proof CP as CP0. (nd_pre CP0 8%nat; intros LN1 LN2 _ _ NDB BS _ NN; nd_post).
  (pose proof NUM as ndP__; nd_pre ndP__ 3%nat; intros NB1 NB2 NF; nd_post).
  destruct GL as [GH GA].
  set (X0 := combine (a_qglob st) (qr_glob R)).
  assert (EX1 : map fst X0 = a_qglob st) by (subst X0; apply map_fst_combine'; exact LN2).
  assert (EX2 : map snd X0 = qr_glob R) by (subst X0; apply map_snd_combine; exact LN2).
  assert (CH : chain L m X0 0) by (unfold chain; rewrite EX1, EX2; exact GA).
  pose proof (chain_bqlen L m X0 0 CH) as LOK.
  assert (SZ : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0).
  { apply Forall_app in NF. destruct NF as [_ NFg]. rewrite <- EX1 in NFg. clear -NFg. induction X0; [constructor|]. inversion NFg; subst. constructor; [assumption| apply IHX0; assumption]. }
  (* [comment removed for export] *)
  pose proof (recycle_eq st X0 min_size K EX1 NB2 SZ LOK (proj1 MIN)) as ME.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB2, EX1; reflexivity)) as KP.
  destruct (qrec_fun X0 (a_qglob_bytes st) min_size) as [[rest T] bytes2] eqn:EQF.
  (nd_pre KP 5%nat; intros PE PS LOK2 SZ2 EB2; nd_post). rewrite ME. clear ME.
  (* [comment removed for export] *)
  assert (XB : forall x, In x X0 -> exists bb, In bb (x_busy X) /\ xb_st bb = BBatch /\ xb_class bb = K_BATCH_CLASS /\ xb_slot bb = qb_slot (snd x)).
  { intros x Hx. apply (qcoupled_rec_bslot_busy L st X R _ CP). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (GEO : Forall (bgeom L AQ_GCACHE (bv_unsigned sp - 80)) X0).
  { apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
    unfold bgeom, baddr, abatch_addr, AIMG_HI, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. lia. }
  assert (SL0 : Forall (fun x => 0 <= qb_slot (snd x)) X0).
  { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) NN). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (NDX : List.NoDup (bqslots X0)).
  { unfold bqslots. rewrite <- (map_map snd qb_slot), EX2. unfold qr_bslots in NDB. rewrite !map_app in NDB.
    apply NoDup_app_remove_r in NDB. apply NoDup_app_remove_l in NDB. apply NoDup_app_remove_r in NDB. exact NDB. }
  assert (LEN40 : Z.of_nat (length X0) < 2^40).
  { pose proof (nodup_range_len (qr_bslots R) (Z.to_nat 458752) NDB) as LEN.
    assert (HFB : Forall (fun k => 0 <= k < Z.of_nat (Z.to_nat 458752)) (qr_bslots R)).
    { apply Forall_forall. intros k Hk. (nd_pre (proj1 (BS k) Hk) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ KR G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
      unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
    specialize (LEN HFB). unfold qr_bslots in LEN. rewrite length_app, !length_map, !length_app, length_map, <- EX2, length_map in LEN. clear -LEN. lia. }
  assert (RB : Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X0).
  { apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ _ G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3.
    (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _).
    unfold baddr, abatch_addr, Q_BATCH_BYTES. eapply rng_sub; [exact RR1| clear -G1; lia| clear -G2 G3; lia]. }
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.arng_tls _ _ _ ARNG) as RTLS.      (* [comment removed for export] *)
  rewrite <- EX1, <- EX2, length_map, <- tfirst_qfirst, <- tlast_qlast in GH.
  (* [comment removed for export] *)
  unfold aqrec_entry. iprefix. eapply evtF_cut.
  { eapply (QREC L RNG X0 (a_qglob_bytes st) min_size lo); try eassumption; try reflexivity;
      try lazymatch goal with
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => clear -LO; lia
      | |- rw_cells _ _ AQ_MUTEX _ => exact MX
      | |- _ = batches_bytes _ => rewrite EX1; exact NB2
      | |- _ (map _ X0) => first [exact NDX| apply (proj2 (NoDup_ListNoDup (bqslots X0))); exact NDX| apply (proj1 (NoDup_ListNoDup (bqslots X0))); exact NDX]
      end.
    all: match goal with |- ?G => idtac "REMQ" G end. all: fail. }
  cbv beta. intros ms1 PQ. unfold qrec_front_post in PQ. rewrite EQF in PQ.
  (nd_pre PQ 20%nat; intros t0' t1' t2' xs0 xs1 xs2 xs3 xs4 a0' a4' a5' a6' a7' t3' t4' t5' t6' tbw m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MUq WMq MI2 ST2 TH2 SAV2 MX2 GH2 CHr CHt EB2' BLE; nd_post).
  rewrite <- EB2 in *. clear EB2'.
  (* [comment removed for export] *)
  set (R2 := mkQR (qr_loc R) (map snd rest) (qr_ia R) T [] [] (qr_qpend R)).
  set (stD := set_qglob (map fst rest) bytes2 st).
  set (Wq := ([(bv_unsigned sp - 96, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X0)%Z) in *.
  assert (DJQ : forall A n, A + n <= AIMG_HI -> (A + n <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A) -> disjoint_from Wq A n).
  { intros A n H1 H2. subst Wq. apply disjoint_from_app; [| eapply disj_objs_img; [exact GEO| exact H1]].
    cbn [disjoint_from app]. unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE in *. clear -H1 H2 CEIL LO. repeat split; lia. }
  (* [comment removed for export] *)
  assert (DJL : forall q, In q (qr_loc R) -> disjoint_from Wq (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. subst Wq. apply disjoint_from_app.
    - (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
      cbn [disjoint_from app]. unfold abatch_addr, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. repeat split; lia.
    - apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
      assert (NE : qb_slot (snd x) <> qb_slot q).
      { intros E. (nd_pre (in_split _ _ Hq) 3%nat; intros l1 l2 EL; nd_post). pose proof NDB as ND0. unfold qr_bslots in ND0. rewrite EL, !map_app in ND0. cbn [map] in ND0.
        rewrite <- !app_assoc in ND0. cbn [app] in ND0.
        apply (List.NoDup_remove_2 _ _ _ ND0). apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
        rewrite <- E, <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
      pose proof (proj1 (Forall_forall _ _) SL0 x Hx) as S1. pose proof (proj1 (Forall_forall _ _) NN (qb_slot q) ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) as S2.
      cbn beta in S1, S2. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
      destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot q)); [left| right]; nia. }
  (* [comment removed for export] *)
  assert (HQ2 : AQdr R2 0 0 L stD X m2).
  { unfold AQdr. subst R2 stD. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob a_space_beg].
    split. { eapply cells_frame; [exact QC| exact MUq| exact WMq|]. cbn [cells_size csize Nat.add]. apply DJQ; unfold AQ_MAX, AIMG_HI, AQ_MUTEX; clear; lia. }
    split; [exact MX2|].
    split. { eapply (aqcache_frame L Wq m m2 MUq WMq); [exact TC| | exact DJL].
             (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 _ TL4u; nd_post). unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
             subst Wq. apply disjoint_from_app.
             - cbn [disjoint_from app]. unfold aq_tcache, AQ_MUTEX, AQ_GCACHE in *. clear -TL4u TL2 CEIL LO. repeat split; lia.
             - apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
               (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post). (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ G6 G7; nd_post).
               unfold xb_alloc in G6, G7. rewrite Cb, Kb in G6. rewrite Cb, Kb, size_of_class_24 in G7.
               pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTR. unfold baddr, abatch_addr, aq_tcache, Q_BATCH_BYTES. clear -G6 G7 DTR. lia. }
    split. { split; [| exact CHr]. rewrite length_map, <- tfirst_qfirst, <- tlast_qlast. exact GH2. }
    split; [exact CHt|].
    split. { eapply (aintal_frame Wq m m2 MUq WMq); [exact IA| |]; apply DJQ; unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIMG_HI, AQ_MUTEX, AQ_GCACHE; clear; lia. }
    split. { eapply qcoupled_rec_perm; [exact CP| exact LN1| cbn [qr_glob a_qglob set_qglob]; rewrite !length_map; reflexivity| | | reflexivity].      (* [comment removed for export] *)
             - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend a_qloc a_qglob set_qglob]. rewrite ET, EP. cbn [map qentries]. rewrite !List.app_nil_r.
               apply Permutation_app_head. fold (bqentries rest). fold (bqentries T). rewrite <- bqentries_app.
               eapply Permutation_trans; [exact PE|]. unfold bqentries. rewrite EX1, EX2. apply Permutation_refl.
             - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map]. rewrite !List.app_nil_r, !map_app.
               apply Permutation_app_head. rewrite !map_map. change (map (fun x : abatch * qbatchc => qb_slot (snd x)) rest ++ map (fun x => qb_slot (snd x)) T) with (bqslots rest ++ bqslots T).
               rewrite <- bqslots_app. eapply Permutation_trans; [exact PS|]. unfold bqslots. rewrite <- EX2, map_map. apply Permutation_refl. }
    split. { unfold qnumR. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob]. split; [exact NB1|]. split; [first [exact EB2| reflexivity]|].
             apply Forall_app in NF. destruct NF as [NFl _]. apply Forall_app. split; [exact NFl|].
             apply Forall_app in SZ2. destruct SZ2 as [SZr _]. clear -SZr. induction rest as [|y rest' IHr]; [constructor|]. inversion SZr; subst. constructor; [assumption| apply IHr; assumption]. }
    unfold qnum_tmp. apply Forall_app in SZ2. destruct SZ2 as [_ SZt]. clear -SZt. induction T as [|y T' IHt]; [constructor|]. inversion SZt; subst. constructor; [assumption| apply IHt; assumption]. }
  (* [comment removed for export] *)
  assert (QWP : Forall (qwp L X) Wq).
  { subst Wq. apply Forall_app. split.
    - repeat (apply Forall_cons || apply Forall_nil); unfold qwp; cbn [fst snd]; intros _;
        unfold AQ_MUTEX, AQ_GCACHE; [left; clear -CEIL LO; lia| right; left; clear; lia| right; left; clear; lia].
    - apply Forall_map. apply Forall_forall. intros x Hx. unfold qwp. cbn [fst snd]. intros _. right; right.
      (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post). exists bb. split; [exact Hb|]. split; [exact Sb|].
      unfold xb_alloc, baddr, abatch_addr. rewrite Cb, Kb, size_of_class_24. unfold Q_BATCH_BYTES. clear; lia. }
  (* [comment removed for export] *)
  assert (ESX : csx st R = sec_chunks_of st ++ []).
  { unfold csx, inflight, secsT. rewrite ET, EP. reflexivity. }
  assert (PCSX : Permutation (csx st R) (csx stD R2)).
  { rewrite ESX, List.app_nil_r. unfold csx, inflight, secsT. subst R2 stD. cbn [qr_tmp qr_pend]. change (esecs []) with (@nil achunk). rewrite List.app_nil_r.
    unfold sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob set_qglob]. rewrite !flat_map_app_chunks, !filter_is_sec_app, <- !app_assoc.
    apply Permutation_app_head. apply Permutation_app_head.
    rewrite <- EX1, <- (map_fst_bqentries X0 LOK).
    pose proof LOK2 as LOK3. apply Forall_app in LOK3. destruct LOK3 as [LOKr LOKt]. rewrite <- (map_fst_bqentries rest LOKr).
    change (List.filter is_sec (map fst (bqentries X0))) with (esecs (bqentries X0)).
    change (List.filter is_sec (map fst (bqentries rest))) with (esecs (bqentries rest)).
    fold (bqentries T).      (* [comment removed for export] *)
    rewrite <- esecs_app, <- bqentries_app. apply esecs_perm. apply Permutation_sym. exact PE. }
  assert (AR2 : AREP (AHr R2 (csx stD R2)) L stD X m2).
  { unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr.
    pose proof (AREP_frame_qw (AQdr R 0 1) (ASECc (csx st R)) AD AF (HLq R 0 1 (csx st R))
                  (fun L' s X' m' => AQdr R2 0 0 L' (set_qglob (map fst rest) bytes2 s) X' m') L st X m m2 Wq ALO AR MUq WMq QWP HQ2) as A1.
    subst stD. eapply AREP_qglob; [exact A1| exact HQ2| intros HS1; eapply ASECc_perm; [exact PCSX| eapply ASECc_qglob; exact HS1]]. }
  assert (ARNG2 : arng L RNG stD).
  { eapply (arng_sub L RNG st stD); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros ch Hch. assert (IN2 : In ch (csx stD R2)) by (unfold csx; apply in_app_iff; left; exact Hch).
    pose proof (Permutation_in _ (Permutation_sym PCSX) IN2) as IN1. rewrite ESX, List.app_nil_r in IN1. exact IN1. }
  assert (RS2 : RSEC (inflight R2) RNG).
  { pose proof (RSEC_arng L RNG st ARNG) as R0. rewrite <- (List.app_nil_r (sec_chunks_of st)), <- ESX in R0.
    pose proof (RSEC_perm' _ _ _ PCSX R0) as R1. unfold csx in R1. apply (proj1 (RSEC_app _ _ _)) in R1. exact (proj2 R1). }
  assert (BL2 : ablocks L stD X LB) by (eapply ablocks_same; [exact BL| reflexivity| reflexivity]).
  assert (HF2 : AF L LB m2).
  { eapply (hf_frame _ (HL R (csx st R)) L LB m m2 Wq); [exact HF| exact MUq| exact WMq|].
    subst Wq. unfold fake_untouched. apply Forall_app. split.
    - pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD. pose proof atop_range as ATR.   (* [comment removed for export] *)
      assert (SF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + 11571200 / 8 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF in *; clear -OF ATR; Z.div_mod_to_equations; lia).
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold AQ_MUTEX, AQ_GCACHE in *; rewrite ?shlen_div; clear -CEIL LO OF OD SF ATR; repeat split; lia.
    - apply Forall_map. apply Forall_forall. intros x Hx. (nd_pre (XB x Hx) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ _ G1 G2 (G3a & G3 & G3b) _; nd_post). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3, G3a, G3b.
      eapply (wpiece_fake L ATOP ATOP); [exact ALO| apply Z.le_refl|]. unfold wpiece. right; right; right. cbn [fst snd].
      unfold baddr, abatch_addr, Q_BATCH_BYTES, K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      clear -G1 G2 G3 G3a G3b. lia. }
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 3%nat; intros TL1 TL2 _; nd_post).
  (* [comment removed for export] *)
  apply evtF_done.
  set (spD := Z_to_bv 64 (bv_unsigned sp - 80) : word).
  assert (USD : bv_unsigned spD = bv_unsigned sp - 80) by (subst spD; rewrite Z_to_bv_unsigned; apply Z.mod_small; unfold bv_modulus; clear -SPR CEIL LO; lia).
  eapply (adorec ASECc AD AF RSEC HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng
            L lo (bv_unsigned sp - 80) (bv_unsigned sp) LB cbs RNG m2 stD (Z_to_bv 64 aqrec_retpc) spD gp xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 F fc);
    rewrite ?USD;
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- ATOP <= _ => atop_facts; exact CEIL
    | |- lo <= _ => clear -LO; lia
    | |- _ <= 2 ^ 47 => clear -SP47 CEIL LO; lia
    | |- bv_unsigned sp - 80 <= bv_unsigned sp - 80 => apply Z.le_refl
    | |- bv_unsigned sp - 80 + 32 <= bv_unsigned sp => clear; lia
    | |- rng _ lo _ => eapply rng_sub; [exact RSTK| clear; lia| clear; lia]
    | |- rng _ (bv_unsigned sp - 80) _ => eapply rng_sub; [exact RSTK| clear -CEIL LO; lia| clear -CEIL LO; lia]
    | |- arng _ _ _ => exact ARNG2
    | |- AREP _ _ _ _ _ => exact AR2
    | |- ablocks _ _ _ _ => exact BL2
    | |- AF _ _ _ => exact HF2
    | |- RSEC _ _ => exact RS2
    | |- qr_tmp _ = _ => reflexivity
    | |- qr_pendb _ = _ => reflexivity
    | |- qr_pend _ = _ => reflexivity
    | |- mem_inv _ _ => exact MI2
    | |- stk _ _ _ _ => exact ST2
    | |- rw_cells _ _ _ (thdr _ _ _) => unfold thdr; rewrite <- tfirst_qfirst, <- tlast_qlast; exact TH2
    end.
  (* [comment removed for export] *)
  intros st3 X3 RNG3 m3 tb' t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c INV3 ST3 TH3.
  (pose proof INV3 as ndP__; nd_pre ndP__ 11%nat; intros ARNG3 AR3 BL3 HF3 RS3 MI3 ST3' FLE3 MU3 CP3 SK3; nd_post).
  rewrite USD in MU3. unfold thdr in TH3. cbn [length map qfirst qlast qaddrs hd List.last Z.of_nat] in TH3.
  pose proof (cells_frameD _ _ _ _ _ SAV2 MU3 ltac:(cbn [cells_size csize Nat.add disjoint_from]; clear; lia)) as SAV3.
  replace (ret_pc (Z_to_bv 64 aqrec_retpc)) with (Z_to_bv 64 aqrec_retpc : word) by (symmetry; apply ret_pc_even; [unfold aqrec_retpc; lia| reflexivity]).
  unfold aqrec_retpc. subst spD.
  assert (RSTK3 : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FLE3| exact RSTK]).
  assert (FRR : rw_cells asegs m3 (bv_unsigned sp - 80) ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 tb'] ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact TH3|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp - 80 + Z.of_nat 32) with (bv_unsigned sp - 48) by (clear; lia). exact SAV3. }
  clear TH3 SAV3. cbn [app] in FRR.
  iprefix.
  do 6 step.                                  (* [comment removed for export] *)
  zstep.                                      (* [comment removed for export] *)
  setreg 2 sp ltac:(replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
  step.                                       (* [comment removed for export] *)
  release_frame FRR ST3 (bv_unsigned sp).
  apply evtF_done. eapply KONT. unfold aqrec_ret.
  exists t0c, t1c, t2c, a0c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, m3, (qr_done R2).
  split; [reflexivity|].
  split; [intros bb j Hb; apply FLE3, Hb|]. split; [exact ARNG3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact AR3|]. split; [exact BL3|]. split; [exact HF3|]. split; [exact MI3|]. split; [exact ST3|].
  split. { (* [comment removed for export] *)
    eapply munch_trans; [| eapply munch_weaken; [| exact MU3]; unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; split; [clear -Hx; lia| split; [clear -Hx SPR CEIL LO; lia| exact I]]].
    eapply munch_weaken; [| exact MUq]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. subst Wq.
    apply outside_of_In. intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - cbn [In] in Hiv. unfold AQ_MUTEX, AQ_GCACHE in *. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; clear -Hx CEIL LO SPR; lia.
    - apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). cbn [fst snd]. (pose proof (proj1 (Forall_forall _ _) GEO y Hy) as ndP__; nd_pre ndP__ 3%nat; intros G1 G2 _; nd_post).
      unfold AIMG_HI, Q_BATCH_BYTES in *. clear -Hx G1 G2 CEIL LO SPR. lia. }
  split. { (* [comment removed for export] *)
    eapply cpres_trans; [| exact CP3]. eapply cpres_of_munch; [exact MUq|]. subst Wq. apply np_fp_app.
    - intros iv Hiv. cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd].
      + eapply (np_high L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| apply Z.le_refl].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_MUTEX in *; clear -Ha; lia| unfold AQ_MUTEX; clear; lia| unfold AQ_MUTEX, AIMG_HI; clear; lia].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_GCACHE in *; clear -Ha; lia| unfold AQ_GCACHE; clear; lia| unfold AQ_GCACHE, AIMG_HI; clear; lia].
    - intros iv Hiv. apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). cbn [fst snd]. (nd_pre (XB y Hy) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
      (nd_pre (in_split _ _ Hb) 3%nat; intros l1 l2 EXB; nd_post). destruct bb as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
      intros a Ha. eapply (np_slot L st X LB (bv_unsigned sp) BBatch K_BATCH_CLASS (qb_slot (snd y)) bn bb1 bctx l1 l2);
        [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| exact EXB| intros p; discriminate| | | exact Ha];
        unfold baddr, abatch_addr; [apply Z.le_refl| rewrite size_of_class_24; unfold Q_BATCH_BYTES; apply Z.le_refl]. }
  (nd_pre SK3 9%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9; nd_post). subst stD. cbn [a_live a_next a_qloc a_qloc_bytes a_nres a_ptr_array a_space_beg set_qglob] in K1, K2, K3, K4, K5, K6, K7, K8, K9.
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
  cbn [a_qglob_bytes set_qglob] in K6. rewrite K6. exact BLE.
Qed.
End Zd1.
#[using="RSEC AHr HL SREC QREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres ASECc_qglob RSEC_app RSEC_perm' RSEC_mono' RSEC_arng"] Theorem aqrec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint) (LB : list ablock) (R : qrconc) (X : aconc) (st : astate) (m : amem) (lo min_size : Z) (cbs : word)
    (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  alayout_ok L -> arng L RNG st -> AREP (AHq R 0 1 (csx st R)) L st X m ->
  qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  ablocks L st X LB -> AF L LB m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
  ATOP <= lo -> lo <= bv_unsigned sp - AQREC_STACK -> bv_unsigned sp <= 2^47 ->
  a_qglob_bytes st < 2^56 -> 0 <= min_size < 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st1 X1 RNG1 ms', aqrec_ret L RNG LB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st R lo min_size m st1 X1 RNG1 ms' ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (recycle st min_size K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 min_size) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 aqrec_entry) fc None m (seg_rom asegs)).
Proof. exact aqrec__body. Qed.
End QRec.
End CANSEC2.
End TwB.
End AQrecP.

(* [comment removed for export] *)
Module AFreeC_kit_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition AHc (R : qrconc) (mc mr : Z) (cs : list achunk) : aholes := AHq ASECc (ADEPOT DI) AFK R mc mr cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition storeC_post (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms1 = MS (mkR (Z_to_bv 64 0x380d0) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa0) fc None m1 (seg_rom asegs)
    (* [comment removed for export] *)
    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0
    (* [comment removed for export] *)
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353068))
    /\ rw_cells asegs m1 spP csA /\ cells_size csA = 16%nat
    /\ rw_cells asegs m1 (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells asegs m1 (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_back_stmt : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (csA csT : list cell) (junk2 : list byte) (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp - 2128 in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1804c8 \/ 0x5d0510 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv) /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv) /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->
  (* [comment removed for export] *)
  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells asegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353068)) ->
  rw_cells asegs mR spP csA -> cells_size csA = 16%nat ->
  rw_cells asegs mR (spP + 16) csT -> cells_size csT = 2040%nat ->
  rw_cells asegs mR (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x380d0) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS asegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition AHc (R : qrconc) (mc mr : Z) (cs : list achunk) : aholes := AHq ASECc (ADEPOT DI) AFK R mc mr cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition storeC_post (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms1 = MS (mkR (Z_to_bv 64 0x38138) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35b08) fc None m1 (seg_rom asegs)
    (* [comment removed for export] *)
    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0
    (* [comment removed for export] *)
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353172))
    /\ rw_cells asegs m1 spP csA /\ cells_size csA = 16%nat
    /\ rw_cells asegs m1 (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells asegs m1 (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_back_stmt : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (csA csT : list cell) (junk2 : list byte) (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp - 2128 in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1808c8 \/ 0x5d0910 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv) /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv) /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->
  (* [comment removed for export] *)
  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells asegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353172)) ->
  rw_cells asegs mR spP csA -> cells_size csA = 16%nat ->
  rw_cells asegs mR (spP + 16) csT -> cells_size csT = 2040%nat ->
  rw_cells asegs mR (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x38138) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS asegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC1.
End TwB.
End AFreeC_kit_iface.

(* [comment removed for export] *)
Module AFreeBack.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma Q_MIN_lt_MAX : Q_MIN < Q_MAX.
Proof. unfold Q_MIN, Q_MAX. lia. Qed.

#[using="Type"] Theorem afree_back : forall DI AFK CI, afree_back_stmt DI AFK CI.
Proof.
  intros DI AFK CI. unfold afree_back_stmt. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP FRA SZA FRT SZT FRS RIMG RTLS RSTK RET QL0 QLB0.
  (nd_pre RET 18%nat; intros t0 t1 t2 a0 a1 a2 a3' a4 a5 a6 a7 t3 t4 t5 t6 m1 R1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros FPLE1 ARNG1 T1 PB1 PE1 LOC1 AR1 BL1 AF1 MI1 ST MU1 CP1 ELIVE ENEXT EQLOC EQLB ENRES EPA ESB GB1; nd_post).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) = bv_unsigned sp - 2128 - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.
  (* [comment removed for export] *)
  assert (D : forall A n, bv_unsigned sp - 2128 - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 2128 - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  pose proof (cells_frameD _ _ _ _ _ FRA MU1 ltac:(apply D; lia)) as FRA1.
  pose proof (cells_frameD _ _ _ _ _ FRT MU1 ltac:(apply D; lia)) as FRT1.
  pose proof (cells_frameD _ _ _ _ _ FRS MU1 ltac:(apply D; lia)) as FRS1.
  clear FRP FRA FRT FRS.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x380d0)) with (Z_to_bv 64 0x380d0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 2128 - 80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2112) in * by lia.
  replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
  replace (bv_unsigned sp - 72) with (bv_unsigned sp + -72) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.arng_tls _ _ _ ARNG1) as RTLS1.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  try replace (bv_unsigned sp + -2208 + 80) with (bv_unsigned sp + -2128) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp + -2128).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG1 sp gp (Z_to_bv 64 ATP)); [exact ST | atop_facts; lia | lia | exact MI
      | eexists; split; [exact FRA1 | exact SZA]
      | eexists; split; [exact FRT1 | exact SZT]
      | exact FRS1 | exact RIMG1 | exact RTLS1 | exact RSTK1 ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST3|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -2208) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  - (* [comment removed for export] *)
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    (pose proof AR1 as ndP__; nd_pre ndP__ 12%nat; intros A1 A2 A3 A4 A5 HQ HS HD A9 A10 A11 A12; nd_post).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    + (* [comment removed for export] *)
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    + (* [comment removed for export] *)
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma Q_MIN_lt_MAX : Q_MIN < Q_MAX.
Proof. unfold Q_MIN, Q_MAX. lia. Qed.

#[using="Type"] Theorem afree_back : forall DI AFK CI, afree_back_stmt DI AFK CI.
Proof.
  intros DI AFK CI. unfold afree_back_stmt. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP FRA SZA FRT SZT FRS RIMG RTLS RSTK RET QL0 QLB0.
  (nd_pre RET 18%nat; intros t0 t1 t2 a0 a1 a2 a3' a4 a5 a6 a7 t3 t4 t5 t6 m1 R1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros FPLE1 ARNG1 T1 PB1 PE1 LOC1 AR1 BL1 AF1 MI1 ST MU1 CP1 ELIVE ENEXT EQLOC EQLB ENRES EPA ESB GB1; nd_post).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) = bv_unsigned sp - 2128 - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.
  (* [comment removed for export] *)
  assert (D : forall A n, bv_unsigned sp - 2128 - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 2128 - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  pose proof (cells_frameD _ _ _ _ _ FRA MU1 ltac:(apply D; lia)) as FRA1.
  pose proof (cells_frameD _ _ _ _ _ FRT MU1 ltac:(apply D; lia)) as FRT1.
  pose proof (cells_frameD _ _ _ _ _ FRS MU1 ltac:(apply D; lia)) as FRS1.
  clear FRP FRA FRT FRS.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x38138)) with (Z_to_bv 64 0x38138 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 2128 - 80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2112) in * by lia.
  replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
  replace (bv_unsigned sp - 72) with (bv_unsigned sp + -72) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.arng_tls _ _ _ ARNG1) as RTLS1.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  try replace (bv_unsigned sp + -2208 + 80) with (bv_unsigned sp + -2128) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp + -2128).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG1 sp gp (Z_to_bv 64 ATP)); [exact ST | atop_facts; lia | lia | exact MI
      | eexists; split; [exact FRA1 | exact SZA]
      | eexists; split; [exact FRT1 | exact SZT]
      | exact FRS1 | exact RIMG1 | exact RTLS1 | exact RSTK1 ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST3|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -2208) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  - (* [comment removed for export] *)
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    (pose proof AR1 as ndP__; nd_pre ndP__ 12%nat; intros A1 A2 A3 A4 A5 HQ HS HD A9 A10 A11 A12; nd_post).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    + (* [comment removed for export] *)
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    + (* [comment removed for export] *)
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC1.
End TwB.
End AFreeBack.

(* [comment removed for export] *)
Module AFreeStoreC.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab308, 0xab330); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma qnumR_free : forall st p ch,
  qnum st -> 0 <= chunk_size ch ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  qnumR (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st p ch (N1 & N2 & N3 & N4 & N5) NN st1 st2.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st1 ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st1 ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      subst st1. cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. subst st1. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnumR. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_of_q : forall L st X Q, qcoupled L st X Q -> qcoupled_rec L st X (qr_of_q Q).
Proof.
  intros L st X Q (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
  unfold qcoupled_rec, qr_entries, qr_bslots, qr_of_q. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
  rewrite !app_nil_r.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition store_freeC__stmt : Prop := store_freeC_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 24).
Variable p : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 25).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 26).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 30).
Variable A : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 32).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 33).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 34).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 35).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 36).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 37).
Let st1 := set_live (delete p (a_live st)) st.
Let st2 := st_enq st1 (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st1 st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeC__body : ltac:(let T := type of (fun (h : store_freeC__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeC_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 NEWF DRC REC EK DK CEIL LO TP ms' PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (st_enq st1 (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  pose proof (st_enq_bytes st p (CPrim c n) L X Q k24 stj chunks) as SB. cbn [chunk_size] in SB.
  assert (CNT : enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)).
  { intros E. destruct (enq_is_app st) eqn:EA.
    - exfalso. assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF eq_refl)))))))). }
  specialize (SB CNT). fold st1 st2 ek in SB.
  change (set_live (delete p (a_live st)) st) with st1 in SB. change (st_enq st1 (CPrim c n)) with st2 in SB.      (* [comment removed for export] *)
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EA; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (GL : g_lst g = qlast L (q_glob Q)) by reflexivity.
  assert (GLST : dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + ek_delta ek n then qlast L (q_glob Q) else qlast L (q_loc Q))) by reflexivity.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EA E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 33%nat; intros id t0' t1' t2' xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' csA csT junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 24%nat; intros MU WM MI' ST' IDR PUTF CSA CSAL CST CSTL IFR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st1 (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = delete p (a_live st) /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st1 st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st1 _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EA. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence.
      - (pose proof (enq_new_core (CPrim c n) st1) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EA. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA; rewrite CL2'; exact (CLa EA)| intros EA; rewrite CL2'; exact (CLb EA)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfree X (enq_is_app st) c k n b1 ctx l1 l2 k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EA; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF1 : awf L st1 (xquar X c k n b1 ctx l1 l2)) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  assert (WF' : awf L st' X').
  { subst X'. unfold xfree. destruct (enq_is_app st) eqn:EA.
    - apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); [exact ESB| exact EPA| exact ECIN| exact (CLa eq_refl)| exact ELIVE| exact ENEXT].
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
      apply (awf_xbatch L st1 (xquar X c k n b1 ctx l1 l2) k24 (c_count (get_cls st K_BATCH_CLASS)) WF1 eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + rewrite ELIVE; reflexivity. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfree_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EA; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CH | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfree_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC_of AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA. (nd_pre (NEWF EA) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self L st X p K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA E]]; rewrite E; [exact SEPL| right; exact (SEPK EA)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA. (nd_pre (NEWF EA) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfree_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
          assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
            destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (clear; destruct (enq_is_app st); lia).
          destruct D2 as [(EA & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 K_BATCH_CLASS k24 XB WF), EA. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
               destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T1, T2. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EA; cbn [ek_post ek_pre] in EKP, EK.
                ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                   rewrite ELST in LB', LA', LJ' |- *.
                   set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                   replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                     by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                   apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                   +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                   +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                       rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_postC in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                   rewrite GF, GL, <- GQL in GLN.
                   replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                   +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                   +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                       eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                       assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                         destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                         exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                       assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                       { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
          assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
            destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T2.
             destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (enq_is_app st) eqn:EA; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| exact SC| exact (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl)]. }
  assert (BL' : ablocks L st' X' (lb_remove p LB)).
  { subst X'. unfold xfree. destruct (enq_is_app st); [apply (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st' ELIVE BL)| apply (ablocks_xbatch L st X p c k n b1 ctx l1 l2 XB LB st' k24 ELIVE BL)]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  (nd_pre DKP 3%nat; intros MX' GC' GLN; nd_post).
  (pose proof (qnumR_free st p (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia)) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st1 st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QKc' : aquar_consts m').
  { eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (MXr' : aquar_mutex m' 0 1) by exact MX'.
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. replace (AIA_MAP1_LEN / 8) with 32768 in Hj by reflexivity. exact Hj. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : exists R, AQdr R 0 1 L st' X' m' /\ qr_loc R = [] /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []).
  { subst ek. unfold ek_of in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (CPrim c n :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (k :: qb_ks qz)) in *.
      assert (EAPP : enq_app st1 (CPrim c n) = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st1 + n) st1)).
      { unfold enq_app. change (a_qloc st1) with (a_qloc st). rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        cbn [chunk_size]. subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. subst st1. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfree. apply (qcoupled_app L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 l bl ql qz true QL QQ QL2 QG2). }
      subst qz'.
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}])) true [] [] [] (q_pend Q)). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3)).
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      assert (EAPP : enq_app st1 (CPrim c n) = None).
      { destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st1) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst st1 nbt. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite ?FSTE in GC'. rewrite ?FSTE in GLN.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfree. cbv iota beta.
        apply (qcoupled_new L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true eq_refl POS NK24 QL2 QG2). }
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (q_loc Q ++ [qn])) true [] [] [] (q_pend Q)). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3)).
  }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC_of AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA. (nd_pre (NEWF EA) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. exact (DK24 EA). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  (nd_pre HQ' 6%nat; intros R HQR RL RT0 RPB RPD; nd_post).
  assert (DRF : a_qloc st' = [] /\ a_qloc_bytes st' = 0 /\ a_qglob_bytes st' = a_qglob_bytes st2 + a_qloc_bytes st2).
  { (nd_pre (DRN DRC) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post). split; [exact QL3|]. split; [exact QB3| exact QGB3]. }
  (nd_pre DRF 3%nat; intros DRF1 DRF2 DRF3; nd_post).
  exists X', R, m', id, t0', t1', t2', xs0, xs1, xs2, xs3, xs4, xs5, xs6, ps0, ps1, ps2, ps3, ps4, ps5, spv, a3', a4', a5', a6', a7', t3', t4', t5', t6', csA, csT, junk2.
  split; [subst tp; reflexivity|].
  split.
  { (* [comment removed for export] *)
    split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQR|].
    split. { cbn [ah_sec AHc AHq]. unfold csx, inflight, secsT. rewrite RT0, RPD. cbn [map fst snd qentries esecs List.filter app]. rewrite app_nil_r. exact HS'. }
    split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3']. }
  split; [exact RT0|]. split; [exact RPB|]. split; [exact RPD|].
  split. { apply (arng_core L RNG st1 st' SC).
           - eapply Permutation_trans; [apply (sec_chunks_free st p c n st' LIVE ELIVE (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl))|].
             apply Permutation_sym. apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _)).
           - apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _))| exact ARNG]. }
  split; [exact BL'|]. split; [exact HFK'|].
  split. { rewrite DRF3, SB1, SB2. unfold Q_MAX, Q_CACHE in *. clear -NM NC ED0 N65. lia. }
  split; [exact DRF1|]. split; [exact DRF2|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact IDR|].
  split; [exact PUTF|]. split; [exact CSA|]. split; [exact CSAL|]. split; [exact CST|]. split; [exact CSTL| exact IFR].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeC : ltac:(let t := eval cbv delta [store_freeC__stmt] in store_freeC__stmt in exact t).
Proof. exact store_freeC__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab708, 0xab730); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma qnumR_free : forall st p ch,
  qnum st -> 0 <= chunk_size ch ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  qnumR (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st p ch (N1 & N2 & N3 & N4 & N5) NN st1 st2.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st1 ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st1 ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      subst st1. cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. subst st1. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnumR. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_of_q : forall L st X Q, qcoupled L st X Q -> qcoupled_rec L st X (qr_of_q Q).
Proof.
  intros L st X Q (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
  unfold qcoupled_rec, qr_entries, qr_bslots, qr_of_q. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
  rewrite !app_nil_r.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition store_freeC__stmt : Prop := store_freeC_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 24).
Variable p : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 25).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 26).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 30).
Variable A : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 32).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 33).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 34).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 35).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 36).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeC__stmt 37).
Let st1 := set_live (delete p (a_live st)) st.
Let st2 := st_enq st1 (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st1 st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeC__body : ltac:(let T := type of (fun (h : store_freeC__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeC_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 NEWF DRC REC EK DK CEIL LO TP ms' PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (st_enq st1 (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  pose proof (st_enq_bytes st p (CPrim c n) L X Q k24 stj chunks) as SB. cbn [chunk_size] in SB.
  assert (CNT : enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)).
  { intros E. destruct (enq_is_app st) eqn:EA.
    - exfalso. assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF eq_refl)))))))). }
  specialize (SB CNT). fold st1 st2 ek in SB.
  change (set_live (delete p (a_live st)) st) with st1 in SB. change (st_enq st1 (CPrim c n)) with st2 in SB.      (* [comment removed for export] *)
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EA; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (GL : g_lst g = qlast L (q_glob Q)) by reflexivity.
  assert (GLST : dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + ek_delta ek n then qlast L (q_glob Q) else qlast L (q_loc Q))) by reflexivity.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EA E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 33%nat; intros id t0' t1' t2' xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' csA csT junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 24%nat; intros MU WM MI' ST' IDR PUTF CSA CSAL CST CSTL IFR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st1 (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = delete p (a_live st) /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st1 st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st1 _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EA. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence.
      - (pose proof (enq_new_core (CPrim c n) st1) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EA. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA; rewrite CL2'; exact (CLa EA)| intros EA; rewrite CL2'; exact (CLb EA)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfree X (enq_is_app st) c k n b1 ctx l1 l2 k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EA; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF1 : awf L st1 (xquar X c k n b1 ctx l1 l2)) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  assert (WF' : awf L st' X').
  { subst X'. unfold xfree. destruct (enq_is_app st) eqn:EA.
    - apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); [exact ESB| exact EPA| exact ECIN| exact (CLa eq_refl)| exact ELIVE| exact ENEXT].
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
      apply (awf_xbatch L st1 (xquar X c k n b1 ctx l1 l2) k24 (c_count (get_cls st K_BATCH_CLASS)) WF1 eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + rewrite ELIVE; reflexivity. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfree_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EA; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CH | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfree_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC_of AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA. (nd_pre (NEWF EA) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self L st X p K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA E]]; rewrite E; [exact SEPL| right; exact (SEPK EA)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA. (nd_pre (NEWF EA) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfree_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
          assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
            destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (clear; destruct (enq_is_app st); lia).
          destruct D2 as [(EA & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 K_BATCH_CLASS k24 XB WF), EA. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
               destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T1, T2. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EA; cbn [ek_post ek_pre] in EKP, EK.
                ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                   rewrite ELST in LB', LA', LJ' |- *.
                   set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                   replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                     by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                   apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                   +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                   +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                       rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_postC in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                   rewrite GF, GL, <- GQL in GLN.
                   replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                   +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                   +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                       eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                       assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                         destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                         exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                       assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                       { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
          assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
            destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T2.
             destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (enq_is_app st) eqn:EA; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF eq_refl) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| exact SC| exact (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl)]. }
  assert (BL' : ablocks L st' X' (lb_remove p LB)).
  { subst X'. unfold xfree. destruct (enq_is_app st); [apply (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st' ELIVE BL)| apply (ablocks_xbatch L st X p c k n b1 ctx l1 l2 XB LB st' k24 ELIVE BL)]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  (nd_pre DKP 3%nat; intros MX' GC' GLN; nd_post).
  (pose proof (qnumR_free st p (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia)) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st1 st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QKc' : aquar_consts m').
  { eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (MXr' : aquar_mutex m' 0 1) by exact MX'.
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. replace (AIA_MAP1_LEN / 8) with 32768 in Hj by reflexivity. exact Hj. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : exists R, AQdr R 0 1 L st' X' m' /\ qr_loc R = [] /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []).
  { subst ek. unfold ek_of in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (CPrim c n :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (k :: qb_ks qz)) in *.
      assert (EAPP : enq_app st1 (CPrim c n) = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st1 + n) st1)).
      { unfold enq_app. change (a_qloc st1) with (a_qloc st). rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        cbn [chunk_size]. subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. subst st1. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfree. apply (qcoupled_app L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 l bl ql qz true QL QQ QL2 QG2). }
      subst qz'.
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}])) true [] [] [] (q_pend Q)). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3)).
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      assert (EAPP : enq_app st1 (CPrim c n) = None).
      { destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st1) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst st1 nbt. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite ?FSTE in GC'. rewrite ?FSTE in GLN.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfree. cbv iota beta.
        apply (qcoupled_new L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true eq_refl POS NK24 QL2 QG2). }
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (q_loc Q ++ [qn])) true [] [] [] (q_pend Q)). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3)).
  }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC_of AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA. (nd_pre (NEWF EA) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. exact (DK24 EA). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  (nd_pre HQ' 6%nat; intros R HQR RL RT0 RPB RPD; nd_post).
  assert (DRF : a_qloc st' = [] /\ a_qloc_bytes st' = 0 /\ a_qglob_bytes st' = a_qglob_bytes st2 + a_qloc_bytes st2).
  { (nd_pre (DRN DRC) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post). split; [exact QL3|]. split; [exact QB3| exact QGB3]. }
  (nd_pre DRF 3%nat; intros DRF1 DRF2 DRF3; nd_post).
  exists X', R, m', id, t0', t1', t2', xs0, xs1, xs2, xs3, xs4, xs5, xs6, ps0, ps1, ps2, ps3, ps4, ps5, spv, a3', a4', a5', a6', a7', t3', t4', t5', t6', csA, csT, junk2.
  split; [subst tp; reflexivity|].
  split.
  { (* [comment removed for export] *)
    split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQR|].
    split. { cbn [ah_sec AHc AHq]. unfold csx, inflight, secsT. rewrite RT0, RPD. cbn [map fst snd qentries esecs List.filter app]. rewrite app_nil_r. exact HS'. }
    split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3']. }
  split; [exact RT0|]. split; [exact RPB|]. split; [exact RPD|].
  split. { apply (arng_core L RNG st1 st' SC).
           - eapply Permutation_trans; [apply (sec_chunks_free st p c n st' LIVE ELIVE (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl))|].
             apply Permutation_sym. apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _)).
           - apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _))| exact ARNG]. }
  split; [exact BL'|]. split; [exact HFK'|].
  split. { rewrite DRF3, SB1, SB2. unfold Q_MAX, Q_CACHE in *. clear -NM NC ED0 N65. lia. }
  split; [exact DRF1|]. split; [exact DRF2|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact IDR|].
  split; [exact PUTF|]. split; [exact CSA|]. split; [exact CSAL|]. split; [exact CST|]. split; [exact CSTL| exact IFR].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeC : ltac:(let t := eval cbv delta [store_freeC__stmt] in store_freeC__stmt in exact t).
Proof. exact store_freeC__body. Qed.
End S.
End CANSEC1.
End TwB.
End AFreeStoreC.

(* [comment removed for export] *)
Module ADfnC_kit_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Notation AHc := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.AHc DI AFK).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_storeC_post (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let spP := bv_unsigned sp in
    ms1 = MS (mkR (Z_to_bv 64 0x380d0) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa0) fc None m1 (seg_rom asegs)
    (* [comment removed for export] *)
    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0
    (* [comment removed for export] *)
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_store_freeC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    dfn_storeC_post L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_back_stmt : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1804c8 \/ 0x5d0510 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv) /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv) /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->
  (* [comment removed for export] *)
  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells asegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x380d0) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS asegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Notation AHc := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB.AHc DI AFK).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_storeC_post (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let spP := bv_unsigned sp in
    ms1 = MS (mkR (Z_to_bv 64 0x38138) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35b08) fc None m1 (seg_rom asegs)
    (* [comment removed for export] *)
    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0
    (* [comment removed for export] *)
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_store_freeC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    dfn_storeC_post L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_back_stmt : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1808c8 \/ 0x5d0910 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv) /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv) /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->
  (* [comment removed for export] *)
  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells asegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x38138) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS asegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC1.
End TwB.
End ADfnC_kit_iface.

(* [comment removed for export] *)
Module ADfn_back.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

#[using="Type"] Theorem dfn_back : forall DI AFK CI, dfn_back_stmt DI AFK CI.
Proof.
  intros DI AFK CI. unfold dfn_back_stmt. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP RIMG RTLS RSTK RET QL0 QLB0.
  (nd_pre RET 18%nat; intros t0 t1 t2 a0 a1 a2 a3' a4 a5 a6 a7 t3 t4 t5 t6 m1 R1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros FPLE1 ARNG1 T1 PB1 PE1 LOC1 AR1 BL1 AF1 MI1 ST MU1 CP1 ELIVE ENEXT EQLOC EQLB ENRES EPA ESB GB1; nd_post).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.
  (* [comment removed for export] *)
  assert (D : forall A n, bv_unsigned sp - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  clear FRP.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x380d0)) with (Z_to_bv 64 0x380d0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.arng_tls _ _ _ ARNG1) as RTLS1.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp).
  apply evtF_done. pose proof ST as ST3.
  (* [comment removed for export] *)
  unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST3|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -80) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  - (* [comment removed for export] *)
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    (pose proof AR1 as ndP__; nd_pre ndP__ 12%nat; intros A1 A2 A3 A4 A5 HQ HS HD A9 A10 A11 A12; nd_post).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    + (* [comment removed for export] *)
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    + (* [comment removed for export] *)
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

#[using="Type"] Theorem dfn_back : forall DI AFK CI, dfn_back_stmt DI AFK CI.
Proof.
  intros DI AFK CI. unfold dfn_back_stmt. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP RIMG RTLS RSTK RET QL0 QLB0.
  (nd_pre RET 18%nat; intros t0 t1 t2 a0 a1 a2 a3' a4 a5 a6 a7 t3 t4 t5 t6 m1 R1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros FPLE1 ARNG1 T1 PB1 PE1 LOC1 AR1 BL1 AF1 MI1 ST MU1 CP1 ELIVE ENEXT EQLOC EQLB ENRES EPA ESB GB1; nd_post).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.
  (* [comment removed for export] *)
  assert (D : forall A n, bv_unsigned sp - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  clear FRP.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x38138)) with (Z_to_bv 64 0x38138 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.arng_tls _ _ _ ARNG1) as RTLS1.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp).
  apply evtF_done. pose proof ST as ST3.
  (* [comment removed for export] *)
  unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST3|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -80) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  - (* [comment removed for export] *)
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    (pose proof AR1 as ndP__; nd_pre ndP__ 12%nat; intros A1 A2 A3 A4 A5 HQ HS HD A9 A10 A11 A12; nd_post).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    + (* [comment removed for export] *)
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    + (* [comment removed for export] *)
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC1.
End TwB.
End ADfn_back.

(* [comment removed for export] *)
Module ADfnRC_kit_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition dfn_store_freeRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm DI ASEC_of AFK Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition dfn_store_freeRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm DI ASEC_of AFK Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
End TwB.
End ADfnRC_kit_iface.

(* [comment removed for export] *)
Module AFreeRC_kit_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm DI ASEC_of AFK Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm DI ASEC_of AFK Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
End TwB.
End AFreeRC_kit_iface.

(* [comment removed for export] *)
Module AFreeStoreRC.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARecyc1P__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab308, 0xab330); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma qnumR_freeR : forall st ch,
  qnum st -> 0 <= chunk_size ch ->
  let st2 := st_enq st ch in
  qnumR (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st ch NUM NN st2.
  pose proof (qnumR_free st 0%N ch) as H. cbv zeta in H.
  assert (E : st_enq (set_live (delete 0%N (a_live st)) st) ch = set_live (delete 0%N (a_live st)) (st_enq st ch) \/ True) by (right; exact I).
  clear H E.
  (nd_pre NUM 5%nat; intros N1 N2 N3 N4 N5; nd_post).
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnumR. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeRC__stmt : Prop := store_freeRC_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 24).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 25).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 26).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 27).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 28).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 29).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 30).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 31).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 32).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 35).
Let st2 := st_enq st (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeRC__body : ltac:(let T := type of (fun (h : store_freeRC__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q c k n b1 ctx lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (c, (k, (n, (b1, (ctx, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeRC_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK XB N1 [pend PEND] EA NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 DRC REC EK DK CEIL LO TP ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (st_enq st (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk_q L st X m c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 4%nat; intros UJR LH SHA SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EA))))))))).
  assert (EAPP0 : enq_app st (CPrim c n) = None).
  { destruct (enq_app st (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st (CPrim c n))); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EA. cbn [ek_delta]. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; rewrite EA; cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. rewrite EA; cbn [ek_b]. right; split; reflexivity. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA2 E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (GL : g_lst g = qlast L (q_glob Q)) by reflexivity.
  assert (GLST : dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + ek_delta ek n then qlast L (q_glob Q) else qlast L (q_loc Q))) by reflexivity.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EA2 E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 33%nat; intros id t0' t1' t2' xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' csA csT junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 24%nat; intros MU WM MI' ST' IDR PUTF CSA CSAL CST CSTL IFR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. rewrite EAPP0.
      (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
      split; [| intros _; exact C7]. intros EA'. exfalso. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA2; rewrite CL2'; exact (CLa EA2)| intros EA2; rewrite CL2'; exact (CLb EA2)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xbatch X k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. rewrite EA. rewrite (CLb EA), lookup_insert_eq; reflexivity. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
    apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
    + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
    + intros c' NE. rewrite (GCo' c' NE). reflexivity.
    + rewrite GC24, EA. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN, EA. subst X'. rewrite xbatch_cache, Z.eqb_refl.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (CR' & _). (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xbatch_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post] in EKP. (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQm DI ASEC_of AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self_g L st X BQuar K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA2 E]]; rewrite E; [exact SEPL| right; exact (SEPK EA2)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA2. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xbatch_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold aslot_busy, bany. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (rewrite EA; clear; lia).
          destruct D2 as [(EA2 & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xbatch' X k24 K_BATCH_CLASS k24). rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [congruence| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xbatch' X k24 c'' k''), T1. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. rewrite EA in EKP, EK; cbn [ek_post ek_pre] in EKP, EK.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_postC in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                   rewrite GF, GL, <- GQL in GLN.
                   replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                   +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                   +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                       eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                       assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                         destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                         exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                       assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA2). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold slot_shadow_bytes, bany. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xbatch' X k24 c'' k'').
             destruct ((K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - exact (sec_same_core st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl))). }
  assert (BL' : ablocks L st' X' LB) by (subst X'; exact (ablocks_xbatchR L st st' X LB k24 ELIVE BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  (nd_pre DKP 3%nat; intros MX' GC' GLN; nd_post).
  (pose proof (qnumR_freeR st (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia)) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QKc' : aquar_consts m').
  { eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (MXr' : aquar_mutex m' 0 1) by exact MX'.
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. replace (AIA_MAP1_LEN / 8) with 32768 in Hj by reflexivity. exact Hj. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA2) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : exists R, AQdr R 0 1 L st' X' m' /\ qr_loc R = [] /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []).
  { subst ek. unfold ek_of in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    rewrite EA in EKP, EK, GC', GLN, EEB, SB1, GDR, GLST; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre (NEWF EA) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. cbn [chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite ?FSTE in GC'. rewrite ?FSTE in GLN.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend)).
      { subst X' qn nbt.
        apply (qcoupled_new_pend L st X Q c k n b1 ctx l1 l2 st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true pend XB WF CP PEND eq_refl POS NK24 KK24 NIB QL2 QG2). }
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (q_loc Q ++ [qn])) true [] [] [] pend). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz EA) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend) true CP2 QL3 QG3)).
  }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BQuar) by (rewrite Sb; discriminate).
        pose proof (other_key (AHQm DI ASEC_of AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. exact (DK24 EA2). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  (nd_pre HQ' 6%nat; intros R HQR RL RT0 RPB RPD; nd_post).
  assert (DRF : a_qloc st' = [] /\ a_qloc_bytes st' = 0 /\ a_qglob_bytes st' = a_qglob_bytes st2 + a_qloc_bytes st2).
  { (nd_pre (DRN DRC) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post). split; [exact QL3|]. split; [exact QB3| exact QGB3]. }
  (nd_pre DRF 3%nat; intros DRF1 DRF2 DRF3; nd_post).
  exists X', R, m', id, t0', t1', t2', xs0, xs1, xs2, xs3, xs4, xs5, xs6, ps0, ps1, ps2, ps3, ps4, ps5, spv, a3', a4', a5', a6', a7', t3', t4', t5', t6', csA, csT, junk2.
  split; [subst tp; reflexivity|].
  split.
  { (* [comment removed for export] *)
    split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQR|].
    split. { cbn [ah_sec AHc AHq]. unfold csx, inflight, secsT. rewrite RT0, RPD. cbn [map fst snd qentries esecs List.filter app]. rewrite app_nil_r. exact HS'. }
    split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3']. }
  split; [exact RT0|]. split; [exact RPB|]. split; [exact RPD|].
  split; [exact (arng_core L RNG st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl)) ARNG)|].
  split; [exact BL'|]. split; [exact HFK'|].
  split. { rewrite DRF3, SB1, SB2. unfold Q_MAX, Q_CACHE in *. clear -NM NC ED0 N65. lia. }
  split; [exact DRF1|]. split; [exact DRF2|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact IDR|].
  split; [exact PUTF|]. split; [exact CSA|]. split; [exact CSAL|]. split; [exact CST|]. split; [exact CSTL| exact IFR].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeRC : ltac:(let t := eval cbv delta [store_freeRC__stmt] in store_freeRC__stmt in exact t).
Proof. exact store_freeRC__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.F_adorec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AQrecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab708, 0xab730); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma qnumR_freeR : forall st ch,
  qnum st -> 0 <= chunk_size ch ->
  let st2 := st_enq st ch in
  qnumR (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st ch NUM NN st2.
  pose proof (qnumR_free st 0%N ch) as H. cbv zeta in H.
  assert (E : st_enq (set_live (delete 0%N (a_live st)) st) ch = set_live (delete 0%N (a_live st)) (st_enq st ch) \/ True) by (right; exact I).
  clear H E.
  (nd_pre NUM 5%nat; intros N1 N2 N3 N4 N5; nd_post).
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnumR. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeRC__stmt : Prop := store_freeRC_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 24).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 25).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 26).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 27).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 28).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 29).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 30).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 31).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 32).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeRC__stmt 35).
Let st2 := st_enq st (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeRC__body : ltac:(let T := type of (fun (h : store_freeRC__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q c k n b1 ctx lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (c, (k, (n, (b1, (ctx, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeRC_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK XB N1 [pend PEND] EA NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 DRC REC EK DK CEIL LO TP ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (st_enq st (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk_q L st X m c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 4%nat; intros UJR LH SHA SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EA))))))))).
  assert (EAPP0 : enq_app st (CPrim c n) = None).
  { destruct (enq_app st (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st (CPrim c n))); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EA. cbn [ek_delta]. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; rewrite EA; cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. rewrite EA; cbn [ek_b]. right; split; reflexivity. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA2 E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (GL : g_lst g = qlast L (q_glob Q)) by reflexivity.
  assert (GLST : dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + ek_delta ek n then qlast L (q_glob Q) else qlast L (q_loc Q))) by reflexivity.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EA2 E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 33%nat; intros id t0' t1' t2' xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' csA csT junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 24%nat; intros MU WM MI' ST' IDR PUTF CSA CSAL CST CSTL IFR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. rewrite EAPP0.
      (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
      split; [| intros _; exact C7]. intros EA'. exfalso. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA2; rewrite CL2'; exact (CLa EA2)| intros EA2; rewrite CL2'; exact (CLb EA2)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xbatch X k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. rewrite EA. rewrite (CLb EA), lookup_insert_eq; reflexivity. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
    apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
    + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
    + intros c' NE. rewrite (GCo' c' NE). reflexivity.
    + rewrite GC24, EA. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN, EA. subst X'. rewrite xbatch_cache, Z.eqb_refl.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (CR' & _). (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xbatch_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post] in EKP. (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQm DI ASEC_of AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self_g L st X BQuar K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA2 E]]; rewrite E; [exact SEPL| right; exact (SEPK EA2)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA2. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xbatch_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold aslot_busy, bany. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (rewrite EA; clear; lia).
          destruct D2 as [(EA2 & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xbatch' X k24 K_BATCH_CLASS k24). rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [congruence| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xbatch' X k24 c'' k''), T1. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. rewrite EA in EKP, EK; cbn [ek_post ek_pre] in EKP, EK.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_postC in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                   rewrite GF, GL, <- GQL in GLN.
                   replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                   +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                   +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                       eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                       assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                         destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                         exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                       assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA2). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold slot_shadow_bytes, bany. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xbatch' X k24 c'' k'').
             destruct ((K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - exact (sec_same_core st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl))). }
  assert (BL' : ablocks L st' X' LB) by (subst X'; exact (ablocks_xbatchR L st st' X LB k24 ELIVE BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  (nd_pre DKP 3%nat; intros MX' GC' GLN; nd_post).
  (pose proof (qnumR_freeR st (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia)) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QKc' : aquar_consts m').
  { eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (MXr' : aquar_mutex m' 0 1) by exact MX'.
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. replace (AIA_MAP1_LEN / 8) with 32768 in Hj by reflexivity. exact Hj. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA2) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : exists R, AQdr R 0 1 L st' X' m' /\ qr_loc R = [] /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []).
  { subst ek. unfold ek_of in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    rewrite EA in EKP, EK, GC', GLN, EEB, SB1, GDR, GLST; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre (NEWF EA) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. cbn [chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite ?FSTE in GC'. rewrite ?FSTE in GLN.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend)).
      { subst X' qn nbt.
        apply (qcoupled_new_pend L st X Q c k n b1 ctx l1 l2 st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true pend XB WF CP PEND eq_refl POS NK24 KK24 NIB QL2 QG2). }
      pose proof DRC as DR.
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQR [] (q_glob Q ++ (q_loc Q ++ [qn])) true [] [] [] pend). split; [| repeat split; reflexivity].
        unfold AQdr. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QKc'|]. split; [exact MXr'|]. split; [| split; [| split; [exact I| split; [exact IA'| split; [| split; [exact NUM'| constructor]]]]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz EA) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_rec_of_q L st' X' _ (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend) true CP2 QL3 QG3)).
  }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BQuar) by (rewrite Sb; discriminate).
        pose proof (other_key (AHQm DI ASEC_of AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. exact (DK24 EA2). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  (nd_pre HQ' 6%nat; intros R HQR RL RT0 RPB RPD; nd_post).
  assert (DRF : a_qloc st' = [] /\ a_qloc_bytes st' = 0 /\ a_qglob_bytes st' = a_qglob_bytes st2 + a_qloc_bytes st2).
  { (nd_pre (DRN DRC) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post). split; [exact QL3|]. split; [exact QB3| exact QGB3]. }
  (nd_pre DRF 3%nat; intros DRF1 DRF2 DRF3; nd_post).
  exists X', R, m', id, t0', t1', t2', xs0, xs1, xs2, xs3, xs4, xs5, xs6, ps0, ps1, ps2, ps3, ps4, ps5, spv, a3', a4', a5', a6', a7', t3', t4', t5', t6', csA, csT, junk2.
  split; [subst tp; reflexivity|].
  split.
  { (* [comment removed for export] *)
    split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQR|].
    split. { cbn [ah_sec AHc AHq]. unfold csx, inflight, secsT. rewrite RT0, RPD. cbn [map fst snd qentries esecs List.filter app]. rewrite app_nil_r. exact HS'. }
    split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3']. }
  split; [exact RT0|]. split; [exact RPB|]. split; [exact RPD|].
  split; [exact (arng_core L RNG st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl)) ARNG)|].
  split; [exact BL'|]. split; [exact HFK'|].
  split. { rewrite DRF3, SB1, SB2. unfold Q_MAX, Q_CACHE in *. clear -NM NC ED0 N65. lia. }
  split; [exact DRF1|]. split; [exact DRF2|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact IDR|].
  split; [exact PUTF|]. split; [exact CSA|]. split; [exact CSAL|]. split; [exact CST|]. split; [exact CSTL| exact IFR].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeRC : ltac:(let t := eval cbv delta [store_freeRC__stmt] in store_freeRC__stmt in exact t).
Proof. exact store_freeRC__body. Qed.
End S.
End CANSEC1.
End TwB.
End AFreeStoreRC.

(* [comment removed for export] *)
Module ADfnS_C_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition dfn_store_freeSC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
Definition dfn_store_freeSRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm DI AFK cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfnC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition dfn_store_freeSC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
Definition dfn_store_freeSRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm DI AFK cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    dfn_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    dfn_storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
End TwB.
End ADfnS_C_iface.

(* [comment removed for export] *)
Module ASF_C_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeSC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
Definition store_freeSRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm DI AFK cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afreeC_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeSC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
Definition store_freeSRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm DI AFK cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
End TwB.
End ASF_C_iface.
