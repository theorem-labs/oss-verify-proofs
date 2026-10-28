(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The musl heap instance of the ubsan target at vm_limit = target_alloc_limit = 2^39: the invariant hi_heapU (the
   relocated PmHeapInst6 invariant plus the global byte cap and the map-count cap GU), the layout L0U, the lemmas
   that layer over the surviving PmHeapInst6 proofs, and the per-call helpers of the malloc/aligned/free proofs. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require HeapIfaceX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk Scfg ShapeAlg SpinAlg Hoare AgentLib MmapSim AllocSim RefNodes HeapIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP MState Mem Cells Step Frame Exec ITree Nodes Decode Image Tac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog KInv KStep MI_Kit MI_Inv MI_Sim MI_Ledger MI_Contracts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem KLink BrRes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import Embed_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* Values of the blob-defined constants of the instance. *)
Lemma NSEG_val : NSEG = 4.
Proof. vm_compute. reflexivity. Qed.
Lemma KPM_val : KPM = 8.
Proof. reflexivity. Qed.
Lemma K0_val : K0 = 3840.
Proof. vm_compute. reflexivity. Qed.
Lemma BOV_val : BOV = 3609042.
Proof. vm_compute. reflexivity. Qed.

Lemma RESV_live : live_bytes RESV <= RESVMAX.
Proof. rewrite RESV_eq. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* Per-call mapping-count cap of the embedding (CAPK) for credit cr. *)
Definition CAPKU (cr : credit) : Z := K0U + NSEG - fst cr + KPM.

Lemma CAPKU_ok : forall cr, KPM <= fst cr -> CAPKU cr <= CAPKMAX.
Proof. intros cr H. unfold CAPKU. rewrite NSEG_val. unfold K0U, CAPKMAX. lia. Qed.

(* The global conjuncts: live heap mappings plus byte credit under CAPG; mappings plus call credit under
   K0U + NSEG (bounds the count of live mappings for the address-room argument). *)
Definition GU (cr : credit) (VM : VmMaps) : Prop :=
     live_bytes (vm_maps VM) + snd cr <= CAPG
  /\ Z.of_nat (length (vm_reserved VM ++ vm_maps VM)) + fst cr <= K0U + NSEG.

(* A call that only shrinks the mappings (free) keeps GU at unchanged credit. *)
Lemma GU_shrunk : forall cr VM h', GU cr VM -> vm_shrunk VM h' -> GU cr h'.
Proof.
  intros cr VM h' [G1 G2] (S1 & S2 & S3 & S4 & S5 & S6 & S7). split; [lia|].
  rewrite length_app in *. rewrite S1. lia.
Qed.

Section LAYOUTU.
Variable sptop : Z.

(* The layout of the ubsan heap: L0's fields with the initial credit (K0U, B0U). *)
Definition L0U : heap_layout :=
  HL (hl_segs (L0 sptop)) (hl_malloc (L0 sptop)) (hl_free (L0 sptop)) (hl_aligned_alloc (L0 sptop))
     (hl_tp (L0 sptop)) (hl_errno (L0 sptop)) (hl_img_lo (L0 sptop)) (hl_img_hi (L0 sptop))
     (hl_alloc_static (L0 sptop)) (hl_alloc_ro (L0 sptop)) (hl_stack (L0 sptop)) (hl_sptop (L0 sptop))
     (hl_k_per_malloc (L0 sptop)) (hl_b_overhead (L0 sptop)) K0U B0U.

Definition hi_heapU (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps) : Prop :=
  hi_heap0 sptop LB cr M VM /\ GU cr VM.

Definition HIU : heap_iface := {| hi_heap := hi_heapU |}.

Lemma L0U_kpm : hl_k_per_malloc L0U = KPM.
Proof. reflexivity. Qed.
Lemma L0U_bov : hl_b_overhead L0U = BOV.
Proof. reflexivity. Qed.

(* ---- Lemmas layered over the surviving PmHeapInst6 proofs ---- *)

Lemma HIU_wf : heap_blocks_wf L0U HIU.
Proof. intros LB cr M VM [H _]. exact (HI0_wf sptop LB cr M VM H). Qed.

Lemma HIU_perm : heap_perm HIU.
Proof.
  intros LB LB' cr M VM [H G] Hin ND. split; [exact (HI0_perm sptop LB LB' cr M VM H Hin ND) | exact G].
Qed.

Lemma HIU_frame : heap_frame L0U HIU.
Proof.
  intros LB cr M M' VM [H G] Hpriv Hdef. split; [exact (HI0_frame sptop LB cr M M' VM H Hpriv Hdef) | exact G].
Qed.

Theorem hiu_live_fit : forall LB cr M VM A n,
  hi_heap HIU LB cr M VM -> In (A, n) LB -> n <= NONEMAX \/ n <= vm_limit VM.
Proof. intros LB cr M VM A n [H _] Hin. exact (hi0_live_fit sptop LB cr M VM A n H Hin). Qed.

(* The invariant is monotone in the credit. *)
Lemma hi_heap0_cr_le : forall LB k b k' b' M VM,
  hi_heap0 sptop LB (k, b) M VM -> 0 <= k' <= k -> 0 <= b' -> hi_heap0 sptop LB (k', b') M VM.
Proof.
  intros LB k b k' b' M VM
    (RUNp & s & L & LBb & nc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10
     & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19) Hk Hb.
  exists RUNp, s, L, LBb, nc. cbn [fst snd] in *. splits; auto; lia.
Qed.

(* ---- Per-call helpers of the malloc / aligned_alloc proofs ---- *)

(* The embedding invariant at the start of a call of request n with potential PA, from the destructed invariant. *)
Lemma RIU_pre : forall {RUNp : RunP} (L : mled) (pbrk : Z) (VM : VmMaps) (cr : credit) (n PA : Z),
  KL2 RESV IMG_HI L pbrk VM ->
  Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved VM ++ vm_maps VM) ->
  vm_limit VM <= XLIM ->
  Forall (fun p => bv_unsigned (snd p) <= NONEMAX \/ bv_unsigned (snd p) <= vm_limit VM) (vm_maps VM) ->
  GU cr VM -> 0 <= n <= NBU -> n + BOV <= snd cr -> KPM <= fst cr -> PA <= POTMAX + AMC ->
  RI (CAPKU cr) (live_bytes (vm_maps VM) + CALLB n PA) EVM (CALLB n PA) VM.
Proof.
  intros RUNp L pbrk VM cr n PA HK FA LIVE FITM [G1 G2] Hn HB HKc HPA.
  destruct (CALLB_le n PA ltac:(lia) HPA) as [CB0 CB1].
  assert (HSP : sp_window_lo <= bv_unsigned (vm_init_sp VM)) by (eapply KL2_init_sp_window; exact HK).
  assert (HR : vm_reserved VM = RESV) by (eapply k2_resv_img; exact HK).
  pose proof RESV_live as HRL. pose proof BOV_val as HBOV.
  unfold RI, CAPKU. splits.
  - unfold KPM in *. lia.
  - exact FA.
  - lia.
  - exact CB0.
  - exact HSP.
  - exact LIVE.
  - exact FITM.
  - lia.
  - unfold BBMAX, NBU in *. lia.
  - rewrite HR. exact HRL.
Qed.

(* The global conjuncts after the call, from the embedding invariant at its end; also the old count conjunct. *)
Lemma RIU_post : forall (VM h' : VmMaps) (cr : credit) (n PA : Z),
  GU cr VM -> n + BOV <= snd cr -> KPM <= fst cr -> PA <= POTMAX + AMC -> 0 <= n ->
  RI (CAPKU cr) (live_bytes (vm_maps VM) + CALLB n PA) 0 0 h' ->
  GU (debit L0U cr n) h'
  /\ Z.of_nat (length (vm_reserved h' ++ vm_maps h')) + fst (debit L0U cr n) <= K0 + NSEG.
Proof.
  intros VM h' cr n PA [G1 G2] HB HKc HPA Hn (Q1 & Q2 & Q3 & Q4 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  destruct (CALLB_le n PA Hn HPA) as [CB0 CB1].
  pose proof K0_val as HK0. unfold CAPKU in Q1. cbn [Z.of_nat] in Q1.
  unfold debit, GU. rewrite L0U_kpm, L0U_bov. cbn [fst snd]. unfold K0U in *. splits; lia.
Qed.

End LAYOUTU.
