(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad STree Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState RelSpec RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanInv.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AcctCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require SizeHist Gap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanBudget.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanHeap.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad STree Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Record aheap := mkAH {
  ah_st : astate;                   (* [comment removed for export] *)
  ah_resv : list (Z * Z);           (* [comment removed for export] *)
  ah_addr : gmap N Z;               (* [comment removed for export] *)
  ah_frames : list (fframe * Z)     (* [comment removed for export] *)
}.
Definition ah_set_st (v : astate) (h : aheap) : aheap := mkAH v (ah_resv h) (ah_addr h) (ah_frames h).
Definition ah_set_addr (v : gmap N Z) (h : aheap) : aheap := mkAH (ah_st h) (ah_resv h) v (ah_frames h).
Definition ah_set_frames (v : list (fframe * Z)) (h : aheap) : aheap := mkAH (ah_st h) (ah_resv h) (ah_addr h) v.

(* [comment removed for export] *)
Definition aheap_init (space_beg ptr_array : Z) (resv : list (Z * Z)) : aheap :=
  mkAH (ainit space_beg ptr_array) resv ∅ [].

Definition REG_A0 : Z := 10.

Section WithCeil.
Context {CE : CEIL}.

#[local] Abbreviation PS := (PState aheap aptr) (only parsing).
#[local] Abbreviation MP := (@Monad.M (PState aheap aptr)) (only parsing).

(* [comment removed for export] *)
Definition alift {R} (t : AM R) : MP R :=
  fun s => ebind (aembed alloc_ceiling t) (fun r => Ret (Ok (r, s))).

(* [comment removed for export] *)
Definition mpeek (a : Z) : MP Z := msys (NPeek a) (fun r => Some (dec_peek r)).
(* [comment removed for export] *)
Definition mpeek_reg64 (r : Z) : MP Z :=
  b0 <- mpeek (- (1 + 8 * r + 0)) ;; b1 <- mpeek (- (1 + 8 * r + 1)) ;; b2 <- mpeek (- (1 + 8 * r + 2)) ;; b3 <- mpeek (- (1 + 8 * r + 3)) ;;
  b4 <- mpeek (- (1 + 8 * r + 4)) ;; b5 <- mpeek (- (1 + 8 * r + 5)) ;; b6 <- mpeek (- (1 + 8 * r + 6)) ;; b7 <- mpeek (- (1 + 8 * r + 7)) ;;
  mret (b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3 + 2^32 * b4 + 2^40 * b5 + 2^48 * b6 + 2^56 * b7).

(* [comment removed for export] *)
Definition mpeek_reg48 (r : Z) : MP Z :=
  b0 <- mpeek (- (1 + 8 * r + 0)) ;; b1 <- mpeek (- (1 + 8 * r + 1)) ;; b2 <- mpeek (- (1 + 8 * r + 2)) ;; b3 <- mpeek (- (1 + 8 * r + 3)) ;;
  b4 <- mpeek (- (1 + 8 * r + 4)) ;; b5 <- mpeek (- (1 + 8 * r + 5)) ;;
  mret (b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3 + 2^32 * b4 + 2^40 * b5).

(* [comment removed for export] *)
Definition upd_heap (f : aheap -> aheap) : MP unit := mupd (fun s => set_heap (f (ps_heap s)) s).

(* [comment removed for export] *)
Definition ah_alloc_tail (forget : gmap N Z -> gmap N Z) (x : astate * option aptr) : MP (option aptr) :=
  match snd x with
  | None => upd_heap (ah_set_st (fst x)) ;;; mret None
  | Some id =>
      A <- mpeek_reg48 REG_A0 ;;
      upd_heap (fun h => ah_set_addr (<[id := A]> (forget (ah_addr h))) (ah_set_st (fst x) h)) ;;;
      mret (Some id)
  end.

Definition ah_malloc (n : Z) : MP (option aptr) :=
  s <- mget ;;
  x <- alift (amalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) n) ;;
  ah_alloc_tail (fun m => m) x.

Definition ah_calloc (m n : Z) : MP (option aptr) :=
  s <- mget ;;
  x <- alift (acalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) m n) ;;
  ah_alloc_tail (fun m => m) x.

Definition ah_realloc (p : aptr) (n : Z) : MP (option aptr) :=
  s <- mget ;;
  x <- alift (arealloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) p n) ;;
  ah_alloc_tail (delete p) x.

Definition ah_free (p : aptr) : MP unit :=
  s <- mget ;;
  st' <- alift (afree (ah_st (ps_heap s)) (Some p)) ;;
  upd_heap (fun h => ah_set_addr (delete p (ah_addr h)) (ah_set_st st' h)).

Definition ah_addr_of (h : aheap) (p : aptr) : Z := default 0 (ah_addr h !! p).

Definition asan_ops : HeapOps aheap aptr :=
  mkHeapOps aheap aptr ah_malloc ah_calloc ah_realloc ah_free ah_addr_of N.eqb (fun _ h => h).

(* [comment removed for export] *)
Definition fframe_idx (f : fframe) : Z :=
  match f with
  | FF_FOPEN_OFFLINE => 0 | FF_CHECK_HEADER => 1 | FF_NEXT_PACKET => 2 | FF_OFFLINE_READ => 3 | FF_NEXT_EX => 4
  | FF_FMT_ERRMSG => 5 | FF_NG_CHECK_HEADER => 6 | FF_READ_BLOCK => 7 | FF_FUZZ_ONE_INPUT => 8
  end.
Definition fframe_eqb (f g : fframe) : bool := fframe_idx f =? fframe_idx g.
#[using="Type"] Lemma fframe_eqb_eq : forall f g, fframe_eqb f g = true <-> f = g.
Proof. intros f g. unfold fframe_eqb. split; [| intros ->; apply Z.eqb_refl]. destruct f, g; cbn; intros H; try reflexivity; discriminate H. Qed.

Definition ah_frame_base (h : aheap) (f : fframe) : option Z :=
  match List.find (fun e => fframe_eqb (fst e) f) (ah_frames h) with
  | Some e => Some (snd e)
  | None => None
  end.

Definition asan_fo (site_frame : stack_site -> option (fframe * Z)) : FrameOps (H:=aheap) (hptr:=aptr) :=
  mkFO (H:=aheap) (hptr:=aptr)
    (fun A f m => (B <- mpeek_reg48 REG_A0 ;; upd_heap (fun h => ah_set_frames ((f, B) :: ah_frames h) h) ;;; m))
    (fun A f x => (upd_heap (fun h => ah_set_frames (tl (ah_frames h)) h) ;;; mret x))
    (fun s site => match site_frame site with
                   | Some (f, off) => match ah_frame_base (ps_heap s) f with Some B => Some (B + off) | None => None end
                   | None => None
                   end).

End WithCeil.
End AsanHeap.

(* [comment removed for export] *)
Module AsanTotalCore.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Core.
Context {CE : Ceiling.CEIL}.   (* [comment removed for export] *)
Variable atop : Z.    (* [comment removed for export] *)
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
(* [comment removed for export] *)
Variable aok : aev -> Model -> Prop.
Variable apost : aev -> Model -> Z -> Model -> Prop.

(* [comment removed for export] *)
Definition aev_node (e : aev) : option (node * (resp -> option Z)) :=
  match e with
  | AMmap a l p f => Some (NMmap a l p f, adec_mmap atop l p)
  | AMunmap a l => Some (NMunmap a l, adec_munmap a l)
  | AMprotect a l p => Some (NMprotect a l p, adec_mprotect a l)
  | ABrk req => Some (NBrk req, adec_raw)
  | ASetTid _ => Some (NSetTid, adec_raw)
  | AUndef _ => None
  end.

#[using="Type"] Lemma aev_tree_node : forall e,
  aev_tree atop e = match aev_node e with Some (n, d) => enode n d | None => Ret Unr end.
Proof. destruct e; reflexivity. Qed.

(* [comment removed for export] *)
Definition node_sound : Prop :=
  forall e mo, aok e mo ->
    exists n d, aev_node e = Some (n, d)
    /\ (forall rsp mo' evs, step2 n mo rsp mo' evs -> evs = [] /\ exists z, d rsp = Some z /\ apost e mo z mo')
    /\ (exists rsp mo' evs, step2 n mo rsp mo' evs)
    /\ (forall code mo', ~ nexit n mo code mo').

(* [comment removed for export] *)
Fixpoint atotal {R} (t : AM R) (mo : Model) (Post : R -> Model -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post r mo
  | SVis e k => aok e mo /\ forall z mo', apost e mo z mo' -> atotal (k z) mo' Post
  end.

#[using="Type"] Lemma atotal_ret : forall {R} (r : R) mo Post, Post r mo -> atotal (SRet r) mo Post.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma atotal_vis : forall {R} e (k : Z -> AM R) mo Post,
  aok e mo -> (forall z mo', apost e mo z mo' -> atotal (k z) mo' Post) -> atotal (SVis e k) mo Post.
Proof. intros. cbn. auto. Qed.

#[using="Type"] Lemma atotal_mono : forall {R} (t : AM R) mo (P Q : R -> Model -> Prop),
  (forall r mo', P r mo' -> Q r mo') -> atotal t mo P -> atotal t mo Q.
Proof.
  intros R t. induction t as [r|e k IH]; intros mo P Q HPQ H; cbn in *.
  - auto.
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact HPQ| exact (Hk _ _ Hp)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma atotal_sbind : forall {A B} (t : AM A) (f : A -> AM B) mo (P : A -> Model -> Prop) (Q : B -> Model -> Prop),
  atotal t mo P -> (forall a mo', P a mo' -> atotal (f a) mo' Q) -> atotal (sbind t f) mo Q.
Proof.
  intros A B t. induction t as [r|e k IH]; intros f mo P Q Ht Hf; cbn in *.
  - exact (Hf _ _ Ht).
  - destruct Ht as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact (Hk _ _ Hp)| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis NS : node_sound.

Local Notation tpath2 := (tpath (node:=node) step2).
Local Notation texit2 := (texit (node:=node) step2 nexit).

#[using="NS"] Lemma atotal_paths : forall {R} (t : AM R) mo Post tr r mo',
  atotal t mo Post -> tpath2 (aembed atop t) mo tr r mo' ->
  tr = [] /\ exists a, r = Ok a /\ Post a mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr r mo' Ht Hp; cbn in Ht.
  - rewrite aembed_ret in Hp. cbn in Hp. destruct Hp as (<- & <- & ->). split; [reflexivity|]. exists r0; auto.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & _ & _).
    rewrite aembed_vis, aev_tree_node, He in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & z & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. apply tpath_enode in Hp as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z & Hd & _). rewrite Hd in Hr. discriminate.
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (-> & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      cbn [app]. eapply IH; [exact (Hk _ _ Hpost)| exact Hp2].
Qed.

#[using="NS"] Lemma atotal_noexit : forall {R} (t : AM R) mo Post tr,
  atotal t mo Post -> ~ texit2 (aembed atop t) mo tr.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr Ht Hx; cbn in Ht.
  - rewrite aembed_ret in Hx. exact Hx.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & _ & Hne).
    rewrite aembed_vis, aev_tree_node, He in Hx. apply texit_ebind in Hx.
    destruct Hx as [Hx|(tr1 & z & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + apply texit_enode in Hx as (code & mo' & Hx & _). exact (Hne _ _ Hx).
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      exact (IH _ _ _ _ (Hk _ _ Hpost) Hx2).
Qed.

#[using="NS"] Lemma atotal_some : forall {R} (t : AM R) mo Post,
  atotal t mo Post -> exists r mo', tpath2 (aembed atop t) mo [] r mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post Ht; cbn in Ht.
  - exists (Ok r0), mo. rewrite aembed_ret. cbn. auto.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & (rsp & mo1 & evs & Hst) & _).
    destruct (Hall _ _ _ Hst) as (-> & z & Hd & Hpost).
    destruct (IH _ _ _ (Hk _ _ Hpost)) as (r & mo' & Hp).
    exists r, mo'. rewrite aembed_vis, aev_tree_node, He. apply tpath_ebind.
    destruct r as [|a].
    + exfalso. destruct (atotal_paths _ _ _ _ _ _ (Hk _ _ Hpost) Hp) as (_ & ? & E & _). discriminate.
    + right. exists [], z, mo1, []. split; [| split; [exact Hp| reflexivity]].
      apply tpath_enode. exists rsp. rewrite Hd. auto.
Qed.

(* [comment removed for export] *)

End Core.
End AsanTotalCore.

(* [comment removed for export] *)
Module AsanNodeSem.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree RelSpec Nodes Decode RelSpecMm Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanInv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma mmap_len_eq : forall len, 0 <= len < 2^63 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len.
Proof. intros. unfold mmap_len. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma mmap_len_bounds : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.div_mod (l + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096 ltac:(lia)). lia. Qed.
Lemma mmap_len_aligned : forall l, mmap_len l mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. apply Z_mod_mult. Qed.

Lemma prd_le : forall x, page_round_down_Z x <= x.
Proof. intros x. unfold page_round_down_Z, page_size. pose proof (Z.mul_div_le x 4096 ltac:(lia)). lia. Qed.
Lemma prd_ge_aligned : forall z x, z mod 4096 = 0 -> z <= x -> z <= page_round_down_Z x.
Proof.
  intros z x Hz Hzx. unfold page_round_down_Z, page_size.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as E. rewrite Hz in E.
  assert (z / 4096 <= x / 4096) by (apply Z.div_le_mono; lia). lia.
Qed.

Section NodeSem.
Context {CE : CEIL}.
Variable atop : Z.                         (* [comment removed for export] *)
Hypothesis Hatop : atop_ok atop.           (* [comment removed for export] *)
Hypothesis HCE : alloc_ceiling = atop.     (* [comment removed for export] *)

Let atop_lt : atop < 2^47.
Proof. destruct Hatop as [_ H]. unfold ATOP_MAX in H. lia. Qed.

#[using="Hatop"] Lemma band_le_top : forall mo, page_round_down_Z (alloc_top (m_vmmaps mo)) = atop -> band_ceiling <= alloc_top (m_vmmaps mo).
Proof. intros mo H. pose proof (prd_le (alloc_top (m_vmmaps mo))). destruct Hatop as [H1 _]. unfold ACEIL in H1. unfold band_ceiling. lia. Qed.

(* [comment removed for export] *)
#[using="Hatop HCE"] Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> page_round_down_Z (alloc_top (m_vmmaps mo)) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hgap Hst. unfold nstepA in Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  pose proof (nstep_mmap_rw_outcome 0 len PROT_RW F_ANON mo rsp mo' evs eq_refl eq_refl
                ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia) eq_refl (band_le_top mo Htop) Hst) as H.
  cbv zeta in H. rewrite mmap_len_eq in H by lia.
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = false).
  { unfold mmap_grant_refusable. rewrite Hgap. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  rewrite Hnr in H. destruct H as [H | (a & (A1 & A2 & A3 & A4 & A5) & Heq)]; [apply mmap_err_out_false in H; destruct H|].
  apply Ok_inj in Heq as (-> & -> & ->). split; [reflexivity|].
  unfold page_size in A1.
  assert (A3' : bv_unsigned a + mmap_len len <= atop).
  { rewrite <- Htop. apply prd_ge_aligned; [| exact A3]. rewrite Z.add_mod, A1, mmap_len_aligned by lia. reflexivity. }
  exists (bv_unsigned a). rewrite Z_to_bv_bv_unsigned. split.
  - unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap. cbn [core]. rewrite !bv_eqb_refl.
    replace (mmap_addr_ok len [] (bv_unsigned a)) with true; [reflexivity|].
    symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite HCE.
    rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3'). reflexivity.
  - split; [exact A1|]. split; [exact A2|]. split; [exact A3'|]. split; [exact A4|].
    unfold grant_model. rewrite with_mmap_backing_id by reflexivity. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

#[using="Hatop"] Lemma grant_exists : forall len mo,
  0 < len <= 2^40 -> page_round_down_Z (alloc_top (m_vmmaps mo)) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hgap. unfold nstepA.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = false).
  { unfold mmap_grant_refusable. rewrite Hgap. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  destruct (grant_witness _ _ _ (band_le_top mo Htop) Hnr) as (a & A1 & A2 & A3 & A4 & A5).
  eexists (mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))]), _, [].
  split; [reflexivity|]. cbn [node_input]. split.
  - rewrite syscall_spec_222 by reflexivity. cbn [in_arg in_args pure_input nth].
    assert (Hl0 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
    apply (proj2 (mmap_rw_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                    _ mo _ eq_refl eq_refl Hl0 eq_refl)).
    right. exists a. rewrite mmap_len_eq by lia. split; [repeat split; assumption| reflexivity].
  - intros (_ & Hr & _). rewrite refusal_b_222 in Hr. cbn [eff_ret] in Hr.
    rewrite (ret_in_mmap_small a) in Hr; [discriminate|]. eapply grant_not_errno; [| exact A3]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let G_off : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false. Proof. reflexivity. Qed.
Let G_anon : forall flags, (flags = F_ANON \/ flags = F_FIXED \/ flags = F_FIXNORES) -> negb (mmap_anon_b (Z_to_bv 64 flags)) = false.
Proof. intros flags [-> |[-> | ->]]; reflexivity. Qed.

#[using="Type"] Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

Definition mm_input (addr len flags : Z) : SyscallInput :=
  pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 PROT_RW; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0].

(* [comment removed for export] *)
#[using="Hatop atop_lt G_off G_anon"] Lemma fixed_check_grant : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  page_round_down_Z (alloc_top (m_vmmaps mo)) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
             (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)]) mo
  = CheckOk (with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo)) [].
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud.
  unfold check_mmap. rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  pose proof (prd_le (alloc_top (m_vmmaps mo))) as PL.
  rewrite (proj2 (Z.leb_le (addr + mmap_len len) (alloc_top (m_vmmaps mo))) ltac:(lia)). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  replace (errno_ret_in mmap_errnos (Z_to_bv 64 addr)) with false.
  2:{ symmetry. apply errno_ret_in_below; [reflexivity|]. rewrite unsigned_lit by lia. unfold two_pow_64. lia. }
  rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
Qed.

#[using="Hatop HCE atop_lt G_off G_anon"] Lemma fixed_answers : forall addr len flags mo rsp mo' evs,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  page_round_down_Z (alloc_top (m_vmmaps mo)) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs ->
  evs = [] /\ adec_mmap atop len PROT_RW rsp = Some addr
  /\ mo' = with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo).
Proof.
  intros addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud Hst. unfold nstepA in Hst.
  pose proof (fixed_check_grant addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as HG. fold n in HG.
  destruct (nstep_mmap_spec _ _ _ _ _ _ _ _ Hst) as (-> & Hsp & Hns). split; [reflexivity|].
  apply (check_mmap_complete_ok _ _ _ _ _ _ _ _ _ _ _) in Hsp. unfold check_mmap in Hsp.
  rewrite G_off, (G_anon flags ltac:(tauto)) in Hsp.
  rewrite w_is0_lit in Hsp by lia. replace (len =? 0) with false in Hsp by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4 in Hsp. cbv iota beta in Hsp.
  rewrite mmap_len_eq in Hsp by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) in Hsp by lia.
  cbv zeta in Hsp.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hsp by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  pose proof (prd_le (alloc_top (m_vmmaps mo))) as PL.
  rewrite (proj2 (Z.leb_le (addr + mmap_len len) (alloc_top (m_vmmaps mo))) ltac:(lia)) in Hsp. unfold page_size in Hsp. rewrite Hal in Hsp. rewrite (proj2 (Z.ltb_lt _ _) Ha) in Hsp.
  cbn [negb Z.eqb] in Hsp. fold n in Hsp. rewrite Hrf, Hmc in Hsp. cbn [andb] in Hsp.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Eerr.
  - (* [comment removed for export] *)
    exfalso. apply Hns. split; [reflexivity|]. split.
    + rewrite refusal_b_222. cbn [eff_ret]. exact Eerr.
    + eexists _, _, _. split.
      * rewrite syscall_spec_222 by reflexivity. cbn [in_arg in_args pure_input nth].
        apply (check_mmap_sound_ok _ _ _ _ _ _ _ _ _ _ _). exact HG.
      * rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_mmap_small. rewrite unsigned_lit by lia. lia.
  - destruct us; [|discriminate].
    match type of Hsp with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    injection Hsp as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
    split; [|reflexivity].
    unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap. cbn [core]. fold n. rewrite !bv_eqb_refl.
    rewrite unsigned_lit by lia.
    replace (mmap_addr_ok len [] addr) with true; [reflexivity|].
    symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite HCE.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Ha), (proj2 (Z.leb_le _ _) Hce). reflexivity.
Qed.

#[using="Hatop atop_lt G_off G_anon"] Lemma fixed_exists : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  page_round_down_Z (alloc_top (m_vmmaps mo)) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud. unfold nstepA.
  pose proof (fixed_check_grant addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as HG. fold n in HG.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  eexists (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)]), _, [].
  split; [reflexivity|]. cbn [node_input]. split.
  - rewrite syscall_spec_222 by reflexivity. cbn [in_arg in_args pure_input nth].
    apply (check_mmap_sound_ok _ _ _ _ _ _ _ _ _ _ _). exact HG.
  - intros (_ & Hr & _). rewrite refusal_b_222 in Hr. cbn [eff_ret] in Hr.
    rewrite ret_in_mmap_small in Hr; [discriminate|]. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Hatop atop_lt G_off G_anon"] Lemma nsafe_fixed_rw : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  page_round_down_Z (alloc_top (m_vmmaps mo)) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  nsafe (NMmap addr len PROT_RW flags) mo.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud. cbn [nsafe node_input].
  pose proof (fixed_check_grant addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as HG. fold n in HG.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  assert (HSP : syscall_spec (mm_input addr len flags) mo
                  (Monad.Ok (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)])
                     (with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo)) [])).
  { unfold mm_input. rewrite syscall_spec_222 by reflexivity. cbn [in_arg in_args pure_input nth].
    apply (check_mmap_sound_ok _ _ _ _ _ _ _ _ _ _ _). exact HG. }
  split; [split|].
  - intros Hu. unfold mm_input in *. rewrite syscall_spec_222 in Hu by reflexivity. cbn [in_arg in_args pure_input nth] in Hu.
    pose proof (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)]) Hu) as HC.
    rewrite HG in HC. discriminate HC.
  - eexists. exact HSP.
  - intros _. left. eexists _, _, _. split; [exact HSP|].
    unfold mm_input. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_mmap_small. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Hatop atop_lt"] Lemma munmap_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  nstepA (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ adec_munmap addr len rsp = Some 0
  /\ mo' = munmap_model mo addr (mmap_len len).
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hmh Hst. unfold nstepA in Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  destruct Hst as (-> & Hsp & _). split; [reflexivity|]. cbn [node_input] in Hsp.
  rewrite syscall_spec_215 in Hsp by reflexivity. cbn [in_arg in_args pure_input nth] in Hsp.
  apply munmap_exact_outcome in Hsp;
    [| rewrite unsigned_lit by lia; exact Hal
     | rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
     | rewrite !unsigned_lit by lia; fold (mmap_len len); unfold TASK_SIZE; lia
     | rewrite unsigned_lit by lia; exact Hmh ].
  rewrite (unsigned_lit len) in Hsp by lia. fold (mmap_len len) in Hsp. fold n in Hsp.
  apply Ok_inj in Hsp as (-> & -> & _). split.
  - unfold adec_munmap, dec_munmap. cbn [core]. fold n. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb andb]. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model. fold n. subst n. rewrite (unsigned_lit (mmap_len len)) by lia. rewrite (unsigned_lit addr) by lia. reflexivity.
Qed.

#[using="Hatop atop_lt"] Lemma munmap_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh. unfold nstepA.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  eexists _, _, []. split; [reflexivity|]. cbn [node_input]. split.
  - rewrite syscall_spec_215 by reflexivity. cbn [in_arg in_args pure_input nth].
    apply (proj2 (munmap_exact_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) _ mo _
                    ltac:(rewrite unsigned_lit by lia; exact Hal)
                    ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia)
                    ltac:(rewrite !unsigned_lit by lia; fold (mmap_len len); unfold TASK_SIZE; lia)
                    ltac:(rewrite unsigned_lit by lia; exact Hmh))).
    reflexivity.
  - intros (Hoff & _). rewrite family_on_215 in Hoff. discriminate Hoff.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_apart (a n : Z) : Prop := a + n <= LS_LO \/ KHIGH <= a.

Definition ASHM0 : list (Z * Z) := [(LS_LO, LS_SZ); (HS_LO, HS_SZ)].   (* [comment removed for export] *)
#[using="Type"] Lemma sh_apart_apart_sh : forall a n, sh_apart a n -> apart_sh ASHM0 a n.
Proof.
  intros a n H. unfold apart_sh, ASHM0. constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold sh_apart, LS_LO, LS_SZ, HS_LO, HS_SZ, KHIGH in *; lia.
Qed.

Definition aok (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      prot = PROT_RW /\ 0 < len <= 2^40 /\ page_round_down_Z (alloc_top (m_vmmaps mo)) = atop /\
      if addr =? 0 then
        flags = F_ANON /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
        /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = true
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ sh_apart addr (mmap_len len)
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
      /\ sh_apart addr (mmap_len len)
  | _ => False
  end.

Definition apost (e : aev) (mo : Model) (z : Z) (mo' : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      if addr =? 0 then
        z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
        /\ mo' = grant_model mo z (mmap_len len)
      else z = addr /\ mo' = fixed_model mo flags addr (mmap_len len)
  | AMunmap addr len => z = 0 /\ mo' = munmap_model mo addr (mmap_len len)
  | _ => False
  end.

#[using="Hatop HCE atop_lt G_off G_anon"] Theorem asan_node_sound : node_sound atop nstepA aok apost.
Proof.
  intros e mo Hok. destruct e as [t|b|addr len prot flags|addr len|a l p|w]; try (destruct Hok; fail); try contradiction.
  - (* [comment removed for export] *)
    cbn [aok] in Hok. destruct Hok as (-> & Hlen & Htop & Hc).
    exists (NMmap addr len PROT_RW flags), (adec_mmap atop len PROT_RW). split; [reflexivity|].
    destruct (Z.eqb_spec addr 0) as [->|Hnz].
    + destruct Hc as (-> & Hbud & Hgap). split; [|split].
      * intros rsp mo' evs Hst. destruct (grant_answers len mo rsp mo' evs Hlen Htop Hbud Hgap Hst) as (-> & z & Hd & H1 & H2 & H3 & H4 & ->).
        split; [reflexivity|]. exists z. split; [exact Hd|]. cbn [apost]. rewrite Z.eqb_refl. repeat split; auto.
      * apply grant_exists; auto.
      * intros code mo' Hx. exact Hx.
    + destruct Hc as (Hfl & Ha & Hal & Hce & Hrf & Hmc & Hbud & _). split; [|split].
      * intros rsp mo' evs Hst. destruct (fixed_answers addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud Hst) as (-> & Hd & ->).
        split; [reflexivity|]. exists addr. split; [exact Hd|]. cbn [apost]. replace (addr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; reflexivity.
      * apply (fixed_exists addr len flags mo); auto.
      * intros code mo' Hx. exact Hx.
  - (* [comment removed for export] *)
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh & _).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (munmap_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
Qed.

End NodeSem.
End AsanNodeSem.

(* [comment removed for export] *)
Module AsanPlace.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zsizes (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsizes l' end.

Lemma zsizes_app : forall l1 l2, zsizes (l1 ++ l2) = zsizes l1 + zsizes l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma zargmin : forall (l : list (Z * Z)), l <> [] -> exists e, In e l /\ forall e', In e' l -> fst e <= fst e'.
Proof.
  induction l as [|e l IH]; intros Hne; [congruence|].
  destruct l as [|e2 l2].
  - exists e. split; [left; reflexivity|]. intros e' [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as (m & Hm & Hmin).
    destruct (Z_le_gt_dec (fst e) (fst m)).
    + exists e. split; [left; reflexivity|]. intros e' [<-|Hin]; [lia|]. specialize (Hmin e' Hin). lia.
    + exists m. split; [right; exact Hm|]. intros e' [<-|Hin]; [lia|]. apply Hmin. exact Hin.
Qed.

Definition pgup (x : Z) : Z := (x + 4095) / 4096 * 4096.
Lemma pgup_facts : forall x, pgup x mod 4096 = 0 /\ x <= pgup x <= x + 4095.
Proof. intros x. unfold pgup. split; [apply Z_mod_mult|]. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma free_gap : forall (n : nat) (l : list (Z * Z)) (lo hi G : Z),
  length l = n -> 0 <= G -> Forall (fun e => 0 <= snd e) l ->
  (hi - lo) - zsizes l >= (Z.of_nat n + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  induction n as [|n IH]; intros l lo hi G Hlen HG Hpos Hroom.
  - destruct l; [|discriminate]. cbn [zsizes] in Hroom.
    exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
    split; [exact HM|]. split; [lia|]. split; [lia| constructor].
  - destruct l as [|e0 l0]; [discriminate|].
    destruct (zargmin (e0 :: l0) ltac:(discriminate)) as (m & Hm & Hmin).
    apply in_split in Hm as (l1 & l2 & El). rewrite El in *.
    assert (Hlen' : length (l1 ++ l2) = n) by (rewrite length_app in *; cbn in Hlen; lia).
    assert (Hpos' : Forall (fun e => 0 <= snd e) (l1 ++ l2)).
    { apply Forall_app in Hpos as [P1 P2]. apply Forall_cons_iff in P2 as [_ P2]. apply Forall_app. split; assumption. }
    assert (Hm0 : 0 <= snd m). { apply Forall_app in Hpos as [_ P2]. apply Forall_cons_iff in P2 as [P _]. exact P. }
    rewrite zsizes_app in Hroom. cbn [zsizes] in Hroom.
    destruct (Z_le_gt_dec (lo + G + 4095) (fst m)) as [Hfar|Hnear].
    + (* [comment removed for export] *)
      exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
      split; [exact HM|]. split; [lia|].
      assert (ZS : 0 <= zsizes l1 /\ 0 <= zsizes l2).
      { apply Forall_app in Hpos' as [P1 P2]. split; [clear -P1; induction l1 as [|x l1 IH1]| clear -P2; induction l2 as [|x l2 IH1]]; cbn; try lia;
          match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [Hx H]; specialize (IH1 H); lia end. }
      split; [nia|].
      rewrite Forall_forall. intros e' He'. left. specialize (Hmin e' He'). lia.
    + (* [comment removed for export] *)
      set (lo' := Z.max lo (fst m + snd m)).
      destruct (IH (l1 ++ l2) lo' hi G Hlen' HG Hpos') as (g & G1 & G2 & G3 & G4).
      { subst lo'. rewrite zsizes_app. nia. }
      exists g. split; [exact G1|]. split; [lia|]. split; [exact G3|].
      apply Forall_app in G4 as [G4a G4b]. apply Forall_app. split; [exact G4a|]. constructor; [|exact G4b].
      right. lia.
Qed.

(* [comment removed for export] *)
Definition meets (lo hi : Z) (e : Z * Z) : bool := (fst e <? hi) && (lo <? fst e + snd e).

Lemma free_gap_filter : forall (l : list (Z * Z)) (lo hi G N T : Z),
  0 <= G -> Forall (fun e => 0 <= snd e) l ->
  Z.of_nat (length (List.filter (meets lo hi) l)) <= N -> zsizes (List.filter (meets lo hi) l) <= T ->
  0 <= N -> (hi - lo) - T >= (N + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  intros l lo hi G N T HG Hpos HN HT HN0 Hroom.
  destruct (free_gap (length (List.filter (meets lo hi) l)) (List.filter (meets lo hi) l) lo hi G eq_refl HG) as (g & G1 & G2 & G3 & G4).
  - apply Forall_forall. intros e He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) Hpos e He).
  - nia.
  - exists g. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    apply Forall_forall. intros e He.
    destruct (meets lo hi e) eqn:Em.
    + apply (proj1 (Forall_forall _ _) G4). apply filter_In. split; assumption.
    + unfold meets in Em. apply andb_false_iff in Em as [Em|Em]; [apply Z.ltb_ge in Em; left| apply Z.ltb_ge in Em; right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zent (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma region_free_of_clear : forall (maps : list (word * word)) (g G : Z),
  0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) (map zent maps) ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction maps as [|[a sz] maps IH]; intros g G Hg HG Hhi HF; [reflexivity|].
  cbn [map zent fst snd] in HF. apply Forall_cons_iff in HF as [H1 HF].
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia. unfold zent in H1. cbn [fst snd] in H1.
  apply negb_true_iff. apply andb_false_iff.
  destruct H1 as [H1|H1]; [right| left]; apply Z.ltb_ge; lia.
Qed.

End AsanPlace.

(* [comment removed for export] *)
Module AsanTotal.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import SizeHist Gap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanInv AsanBudget. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanBudget OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanPlace.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok ATOP).
Local Notation apost := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

#[using="Type"] Lemma INV_atop : forall pc pb st mo, INV pc pb st mo -> atop_ok ATOP /\ page_round_down_Z (alloc_top (m_vmmaps mo)) = ATOP.
Proof. intros pc pb st mo [_ HM]. exact (AMI_atop _ _ _ HM). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_sub : forall l (a n a' n' : Z),
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  0 <= a -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> a + n < 2^64 ->
  region_free l (Z_to_bv 64 a') (Z_to_bv 64 n') = true.
Proof.
  induction l as [|[b sz] l IH]; intros a n a' n' H Ha Haa Hn Hsub Htop; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H1 H2]. rewrite (IH _ _ _ _ H2 Ha Haa Hn Hsub Htop), andb_true_r.
  unfold iv_overlap in *. rewrite !unsigned_lit in H1 |- * by lia.
  apply negb_true_iff in H1. apply negb_true_iff. apply andb_false_iff in H1. apply andb_false_iff.
  destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; [left|right]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Definition same_but (c : Z) (st st' : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st /\ a_nres st' = a_nres st /\ a_nsec st' = a_nsec st
  /\ a_cinit st' = a_cinit st /\ a_live st' = a_live st /\ a_next st' = a_next st
  /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st
  /\ (forall c', c' <> c -> get_cls st' c' = get_cls st c').

#[using="Type"] Lemma same_but_refl : forall c st, same_but c st st.
Proof. intros. unfold same_but. repeat split; reflexivity. Qed.
#[using="Type"] Lemma same_but_put : forall c st r, same_but c st (put_cls c r st).
Proof. intros. unfold same_but. repeat split; try reflexivity. intros c' Hc'. apply get_put_ne. congruence. Qed.
#[using="Type"] Lemma same_but_trans : forall c st1 st2 st3, same_but c st1 st2 -> same_but c st2 st3 -> same_but c st1 st3.
Proof.
  intros c st1 st2 st3 A B. unfold same_but in *.
  destruct A as (?&?&?&?&?&?&?&?&?&?&?&HA). destruct B as (?&?&?&?&?&?&?&?&?&?&?&HB).
  repeat split; try congruence. intros c' Hc'. rewrite HB, HA; auto.
Qed.

(* [comment removed for export] *)
Definition CLSOK (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) (r : aclass) : Prop :=
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).

#[using="Type"] Lemma AINV_cls : forall pc pb st c, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c (get_cls st c).
Proof. intros pc pb st c (H & _) Hc. exact (H c Hc). Qed.

#[using="Type"] Lemma AINV_put_cls : forall pc pb st c r, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c r -> AINV pc pb (put_cls c r st).
Proof.
  intros pc pb st c r H Hc HR. unfold AINV in *. rewrite !all_chunks_put, !qbatches_put, !CH_put.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
  destruct (Z.eq_dec c' c) as [->|Hne].
  - rewrite get_put_eq. exact HR.
  - rewrite get_put_ne by congruence. exact (HC c' Hc').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma csum_bound : forall f st b, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= b) -> csum f st <= 31 * b.
Proof.
  intros f st b H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= zlen l * b).
  { induction l as [|c l IH]; intros Hl; unfold zlen in *; cbn [fold_right length]; [lia|]. rewrite Nat2Z.inj_succ.
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  specialize (G CLASSES ltac:(intros c Hc; apply In_CLASSES; exact Hc)). change (zlen CLASSES) with 31 in G. exact G.
Qed.
#[using="Type"] Lemma csum_nonneg : forall f st, (forall c, 1 <= c <= 31 -> 0 <= f (get_cls st c)) -> 0 <= csum f st.
Proof.
  intros f st H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> 0 <= fold_right (fun c acc => f (get_cls st c) + acc) 0 l).
  { induction l as [|c l IH]; intros Hl; cbn [fold_right]; [lia|].
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  apply G. intros c Hc; apply In_CLASSES; exact Hc.
Qed.

Definition CBMAX : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + 8 * K_CHUNKS_BLOCK.
#[using="Type"] Lemma commit_bytes_bound : forall pc pb st, AINV pc pb st -> 0 <= commit_bytes st <= CBMAX.
Proof.
  intros pc pb st H. pose proof H as (HC & _ & _ & _ & _ & _ & Hres & _).
  unfold commit_bytes, CBMAX.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX)) as B1.
  pose proof (csum_nonneg cls_mapped_bytes' st) as B0.
  assert (A : forall c, 1 <= c <= 31 -> 0 <= cls_mapped_bytes' (get_cls st c) <= K_FREEARR_OFF + K_FREEARR_MAX).
  { intros c Hc. destruct (HC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold cls_mapped_bytes'. lia. }
  specialize (B1 ltac:(intros c Hc; apply A; exact Hc)). specialize (B0 ltac:(intros c Hc; apply A; exact Hc)).
  unfold K_CHUNKS_BLOCK in *. destruct Hres as [-> | ->]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_len_id : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof.
  intros l Hl Hm. unfold mmap_len, page_round_up_Z, page_size.
  pose proof (Z.div_mod l 4096 ltac:(lia)). rewrite Hm in H.
  replace (l + 4096 - 1) with (l / 4096 * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

#[using="Type"] Lemma region_free_above : forall l (a n : Z) R,
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= R) l -> R <= a -> 0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n R Hf HR Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [H1 Hf]. cbn [region_free]. rewrite (IH a n R Hf HR Ha Han Hn).
  unfold iv_overlap. rewrite !unsigned_lit by lia. cbn [fst snd] in H1.
  replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma CH_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (CH pc pb st).
Proof.
  intros pc pb st (_ & Hwf & _). unfold CH. induction (all_chunks pc pb st) as [|ch l IH]; [constructor|].
  apply Forall_cons_iff in Hwf as [H1 Hwf]. rewrite secs_cons. apply Forall_app. split; [|apply IH; exact Hwf].
  destruct ch as [c n|mb ms n]; cbn [sec_of]; [constructor|]. constructor; [|constructor]. cbn [snd].
  cbn [chunk_wf] in H1. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma INV_backing_bound : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + CBMAX + zsum2 (CH pc pb st).
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)).
  pose proof (commit_bytes_bound _ _ _ HA). rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_fixed_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true -> 0 < a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CH pc pb st) <= 2^35 ->
  sh_apart a len ->     (* [comment removed for export] *)
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Ha0 Hal Hll Hlen HSB HSH.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split; [|split; [| exact HSH]]].
  - exact HR.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_commit_intro; [reflexivity| exact Hwf|].
    rewrite !unsigned_lit by lia. rewrite M2. unfold LIMIT.
    pose proof (INV_backing_bound _ _ _ _ HI).
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + len) M9 HinE ltac:(unfold B; lia) ltac:(unfold B, S; lia) ltac:(lia)).
    unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
Qed.

#[using="Type"] Lemma INV_resv_hi : forall pc pb st mo, INV pc pb st mo ->
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (vm_reserved (m_vmmaps mo)).
Proof. intros pc pb st mo [_ HM]. destruct HM as (_ & _ & M3 & _). exact M3. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_fixed_aok_high : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> KHIGH <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CH pc pb st) <= 2^35 ->
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold ACEIL, ATOP_MAX in T1, T2. unfold B, S in HE1, HE2. unfold KHIGH in HR.
  apply (INV_fixed_aok pc pb st mo E a len HI HinE); unfold B, S; auto; try lia; [| right; unfold KHIGH; lia].
  apply (region_free_above _ a len RES_HI M3); unfold RES_HI in *; lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma INV_munmap_aok : forall pc pb st mo mb ms,
  INV pc pb st mo -> In (mb, ms) (CH pc pb st) ->
  0 < mb -> mb mod 4096 = 0 -> 0 < ms <= 2^31 -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  sh_apart mb ms ->     (* [comment removed for export] *)
  aok (AMunmap mb ms) mo.
Proof.
  intros pc pb st mo mb ms [HA HM] Hin Hmb Hal Hms Hml Hce HSH.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
  assert (ML : mmap_len ms = ms) by (apply mmap_len_id; lia).
  cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact HSH].
  apply map_has_In. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right.
  change (Z_to_bv 64 mb, Z_to_bv 64 ms) with (went (mb, ms)). apply in_map. exact Hin.
Qed.

#[using="Type"] Lemma live_bytes_perm' : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof. intros. rewrite !live_bytes_sum_count. apply sum_count_perm. assumption. Qed.
#[using="Type"] Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. intros. apply BackingAlgebra.live_bytes_app. Qed.

#[using="Type"] Lemma INV_grant_aok : forall pc pb st mo n,
  INV pc pb st mo -> 64512 < n <= 2^30 -> zsum2 (CH pc pb st) <= 2^35 -> zlen (CH pc pb st) <= 16000 ->
  aok (AMmap 0 (sec_map_size n) PROT_RW F_ANON) mo.
Proof.
  intros pc pb st mo n HI Hn HSB HSL.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n).
  { apply mmap_len_id; [lia|]. unfold sec_map_size, rup, PG.
    match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end.
    apply Z_mod_mult. }
  cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok]. rewrite Z.eqb_refl. rewrite ML. split; [reflexivity|]. split; [lia|]. split; [exact T3|]. split; [reflexivity|]. split.
  - rewrite M2. unfold LIMIT. pose proof (INV_backing_bound _ _ _ _ HI). unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
  - apply (vm_gap_available_intro_N _ _ (LEN0 + LEN0 + 16000) (2^30 + 2^20) (RTOT0 + TOT0 + 2^35)); [lia| | | |].
    + (* [comment removed for export] *) pose proof (prd_le (alloc_top (m_vmmaps mo))) as PL__. unfold ACEIL in T1. rewrite CEIL_val. lia.
    + eapply Z.le_trans. { apply inj_le. apply length_filter_le. }
      rewrite length_app, Nat2Z.inj_add. fold (zlen (vm_reserved (m_vmmaps mo))). fold (zlen (vm_maps (m_vmmaps mo))).
      unfold zlen at 2. rewrite (Permutation_length HP). fold (zlen (L0 ++ map went (CH pc pb st))). rewrite zlen_app.
      unfold zlen at 3. rewrite length_map. fold (zlen (CH pc pb st)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & HL & _). lia.
    + rewrite live_bytes_app'. rewrite (live_bytes_perm' _ _ HP).
      rewrite live_bytes_app', (live_bytes_went _ (CH_wf _ _ _ HA)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
    + rewrite CEIL_val, FLOOR_val. unfold LEN0, RTOT0, TOT0. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_prim : forall pc pb st mo, INV pc pb st mo ->
  exists pb0, In (went (pb0, PRIM_SZ)) (vm_maps (m_vmmaps mo)) /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
              /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as ((pb0 & Hin & H1 & H2 & H3 & H4) & _). exists pb0. split; [|repeat split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma INV_ptr : forall pc pb st mo, INV pc pb st mo ->
  In (went (a_ptr_array st, PTR_SZ)) (vm_maps (m_vmmaps mo)) /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & Hin & H1 & H2 & _). split; [|split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
#[using="Type"] Lemma INV_shadows : forall pc pb st mo, INV pc pb st mo ->
  In (went (LS_LO, LS_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (GAP_LO, GAP_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (HS_LO, HS_SZ)) (vm_maps (m_vmmaps mo)).
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & _ & _ & _ & H1 & H2 & H3 & _).
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; left; assumption).
Qed.

#[using="Type"] Lemma AINV_geom : forall pc pb st, AINV pc pb st -> a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st.
Proof. intros pc pb st H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). auto. Qed.

#[using="Type"] Lemma rup_mod : forall x a, 0 < a -> rup x a mod a = 0.
Proof. intros. unfold rup. apply Z_mod_mult. Qed.
#[using="Type"] Lemma rup_ge' : forall x a, 0 < a -> x <= rup x a. Proof. exact rup_ge. Qed.

#[using="Type"] Lemma is_err_small : forall a, 0 <= a <= TWO64 - 4096 -> is_err a = false.
Proof. intros. unfold is_err. apply Z.ltb_ge. lia. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma mod0_divide : forall x m, 0 < m -> x mod m = 0 -> (m | x).
Proof. intros. apply Z.mod_divide; lia. Qed.
#[using="Type"] Lemma divide_mod0 : forall x m, 0 < m -> (m | x) -> x mod m = 0.
Proof. intros. apply Z.mod_divide; [lia| assumption]. Qed.
#[using="Type"] Lemma div4096_of_mod : forall x m, (4096 | m) -> 0 < m -> x mod m = 0 -> (4096 | x).
Proof. intros x m Hm Hp Hx. eapply Z.divide_trans; [exact Hm|]. apply mod0_divide; assumption. Qed.
#[using="Type"] Lemma div_65536 : (4096 | 65536). Proof. exists 16. reflexivity. Qed.
#[using="Type"] Lemma div_262144 : (4096 | 262144). Proof. exists 64. reflexivity. Qed.
#[using="Type"] Lemma div_lit : forall k, (4096 | k * 4096). Proof. intros. exists k. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ensure_ok : forall R (P : R -> Model -> Prop) pc pb st c nf (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 0 <= nf ->
  4 * nf + K_FREEARR_MAP <= K_FREEARR_MAX ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
     c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
     c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     nf * 4 <= c_mapped_free_array (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (ensure_free_array st c nf k) mo P.
Proof.
  intros R P pc pb st c nf k mo HI Hc Hnf Hroom HSB Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  unfold ensure_free_array. cbv zeta.
  destruct (Z.leb_spec (nf * 4) (c_mapped_free_array (get_cls st c))) as [Hle|Hgt].
  { apply (Hk st mo HI (same_but_refl c st)); auto. }
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R1.
  pose proof (rup_le (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R2.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R3.
  destruct (Z.ltb_spec K_FREEARR_MAX (rup (nf * 4) K_FREEARR_MAP)) as [Hbig|Hok]; [lia|].
  set (len := rup (nf * 4) K_FREEARR_MAP - c_mapped_free_array (get_cls st c)).
  set (a := region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)).
  assert (Hlen : 0 < len <= 2^30) by (unfold len, K_FREEARR_MAX in *; lia).
  assert (Dmfa : (4096 | c_mapped_free_array (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in C7; exact C7]).
  assert (Drup : (4096 | rup (nf * 4) K_FREEARR_MAP)) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in *; exact R3]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Hlm : len mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold len. apply Z.divide_sub_r; assumption. }
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION, K_FREEARR_OFF.
    apply Z.divide_add_r; [|exact Dmfa]. apply Z.divide_add_r; [| exists 917504; reflexivity].
    apply Z.divide_add_r; [exact Dsb|]. replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF; lia).
  assert (HE2 : a + len <= pb0 + PRIM_SZ).
  { unfold a, len, region_beg, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, PRIM_SZ in *. lia. }
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia; try (unfold RES_HI, KHIGH in *; lia).
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ in *; lia).
    assert (ML : mmap_len len = len) by (apply mmap_len_id; lia). rewrite ML.
    apply Hk.
    + split.
      * apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count cls_set_mapped_free_array].
        unfold K_FREEARR_MAP in *. repeat split; try lia.
      * rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cbn [c_mapped_user c_mapped_free_array cls_set_mapped_free_array]. unfold len. lia.
    + apply same_but_put.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. cbn [c_mapped_free_array cls_set_mapped_free_array]. lia.
Qed.

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

(* [comment removed for export] *)
#[using="Type"] Lemma populate_ok : forall R (P : R -> Model -> Prop) pc pb st c req (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 32 <= size_of_class c <= 65536 -> 0 < req -> req * size_of_class c <= K_USER_MAP ->
  c_allocated_user (get_cls st c) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     c_num_freed (get_cls st c) + req <= c_num_freed (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (populate_free_array st c req k) mo P.
Proof.
  intros R P pc pb st c req k mo HI Hc Hsz Hreq Hrs Hroom HSB Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  remember (size_of_class c) as size eqn:Hsize.
  (* [comment removed for export] *)
  assert (TAIL : forall st1 mo1,
    INV pc pb st1 mo1 -> same_but c st st1 -> c_count (get_cls st1 c) = c_count (get_cls st c) -> c_num_freed (get_cls st1 c) = c_num_freed (get_cls st c) ->
    c_allocated_user (get_cls st1 c) = c_allocated_user (get_cls st c) ->
    c_allocated_user (get_cls st c) + req * size <= c_mapped_user (get_cls st1 c) -> zsum2 (CH pc pb st1) <= 2^35 ->
    atot (let r1 := get_cls st1 c in
          let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
          let total_freed := c_num_freed r1 + new_cnt in
          ensure_free_array st1 c total_freed (fun st2 ok =>
            if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + new_cnt * size) (cls_set_num_freed total_freed (get_cls st2 c))) st2) true)) mo1 P).
  { intros st1 mo1 HI1 HSB1 Hcnt1 Hnf1 Hal1 Hen1 HSB2. cbv zeta.
    pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite <- Hsize in D10.
    pose proof (carve_facts (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) size ltac:(lia) ltac:(lia)) as (Q0 & Qcv & Qrest).
    pose proof (carve_enough_nomap (c_mapped_user (get_cls st1 c)) (c_allocated_user (get_cls st1 c)) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    set (q := (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) in *. set (cv := q * size) in *.
    assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st1) + nbatch c (qbatches pb st1)).
    { pose proof (cntP_nonneg c (all_chunks pc pb st1)). unfold nbatch. destruct (c =? K_BATCH_CLASS); [pose proof (zlen_nonneg (qbatches pb st1))|]; lia. }
    (* [comment removed for export] *)
    assert (Hnf' : 4 * (c_num_freed (get_cls st1 c) + q) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (H1 : size * (c_num_freed (get_cls st1 c) + q) <= c_mapped_user (get_cls st1 c)).
      { rewrite Z.mul_add_distr_l. replace (size * q) with cv by (unfold cv; lia).
        assert (size * c_num_freed (get_cls st1 c) <= c_allocated_user (get_cls st1 c)); [|lia].
        rewrite D10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (H2 : 32 * (c_num_freed (get_cls st1 c) + q) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size * (c_num_freed (get_cls st1 c) + q)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    assert (Hcv : cv = q * size) by reflexivity. clearbody cv q.
    apply (ensure_ok R P pc pb st1 c (c_num_freed (get_cls st1 c) + q) _ mo1 HI1 Hc ltac:(lia) Hnf' HSB2).
    intros st2 mo2 HI2 HSB12 E1 E2 E3 E4 E5. cproj.
    pose proof HI2 as [HA2 HM2].
    assert (AC : all_chunks pc pb st2 = all_chunks pc pb st1 /\ qbatches pb st2 = qbatches pb st1).
    { destruct HSB12 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. rewrite Hl, Hq1, Hq2. split; reflexivity. }
    destruct AC as [AC1 AC2].
    apply Hk.
    - split.
      + apply AINV_put_cls; [exact HA2| exact Hc|].
        pose proof (AINV_cls _ _ _ _ HA2 Hc) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
        unfold CLSOK. cproj. rewrite <- Hsize. rewrite AC1, AC2. rewrite E1, E2, E3, E4 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact D5|]. split; [exact F6|]. split; [exact F7|].
        split; [lia|]. split; [exact F9|]. rewrite <- Hsize in F10. rewrite AC1, AC2 in F10. rewrite F10, Hcv. ring.
      + rewrite CH_put. apply (AMI_mono _ st2); auto. rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cproj. lia.
    - eapply same_but_trans; [exact HSB1|]. eapply same_but_trans; [exact HSB12| apply same_but_put].
    - rewrite get_put_eq. cproj. congruence.
    - rewrite get_put_eq. cproj. lia. }
  unfold populate_free_array. rewrite <- Hsize. cbv zeta.
  destruct (Z.leb_spec (c_allocated_user (get_cls st c) + req * size) (c_mapped_user (get_cls st c))) as [Hen|Hmap].
  { apply (TAIL st mo HI (same_but_refl c st)); auto. }
  (* [comment removed for export] *)
  assert (Hums : rup (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP = K_USER_MAP).
  { apply rup_small; unfold K_USER_MAP in *; lia. }
  rewrite Hums.
  destruct (Z.ltb_spec K_FREEARR_OFF (c_mapped_user (get_cls st c) + K_USER_MAP)) as [Hex|Hok]; [unfold K_USER_MAP, K_FREEARR_OFF in *; lia|].
  set (a := region_beg st c + c_mapped_user (get_cls st c)).
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Dmu : (4096 | c_mapped_user (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_USER_MAP in C5; exact C5]).
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION. apply Z.divide_add_r; [|exact Dmu]. apply Z.divide_add_r; [exact Dsb|].
    replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION; lia).
  assert (HE2 : a + K_USER_MAP <= pb0 + PRIM_SZ) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF, K_USER_MAP, PRIM_SZ in *; lia).
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia; try (unfold RES_HI, KHIGH in *; lia); try (unfold K_USER_MAP; lia).
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ, K_USER_MAP in *; lia).
    assert (ML : mmap_len K_USER_MAP = K_USER_MAP) by reflexivity. rewrite ML.
    set (st1 := put_cls c (cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) st).
    assert (HI1 : INV pc pb st1 (fixed_model mo F_FIXED a K_USER_MAP)).
    { split.
      + apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cproj. rewrite <- Hsize. repeat split; try (unfold K_USER_MAP in *; lia).
        all: unfold K_USER_MAP in *; rewrite <- Zplus_mod_idemp_l, C5; reflexivity.
      + unfold st1. rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        all: try (unfold K_USER_MAP; lia).
        all: rewrite commit_bytes_put by exact Hc; unfold cls_mapped_bytes'; cproj; unfold K_USER_MAP; lia. }
    assert (Er1 : get_cls st1 c = cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) by (unfold st1; apply get_put_eq).
    apply (TAIL st1 (fixed_model mo F_FIXED a K_USER_MAP) HI1); try (rewrite Er1; cproj; lia).
    + unfold st1. apply same_but_put.
    + unfold st1. rewrite CH_put. exact HSB.
Qed.

#[using="Type"] Lemma max_count_same_but : forall c st1 st2 c', same_but c st1 st2 -> max_count st2 c' = max_count st1 c'.
Proof. intros c st1 st2 c' H. destruct H as (_&_&_&_&Hci&_). unfold max_count. rewrite Hci. reflexivity. Qed.

#[using="Type"] Lemma all_chunks_cons : forall ch pc pb st, all_chunks (ch :: pc) pb st = ch :: all_chunks pc pb st. Proof. reflexivity. Qed.
#[using="Type"] Lemma qbatches_cons : forall b pb st, qbatches (b :: pb) st = b :: qbatches pb st. Proof. reflexivity. Qed.
#[using="Type"] Lemma CH_cons : forall ch pc pb st, CH (ch :: pc) pb st = sec_of ch ++ CH pc pb st. Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CH_repc : forall pc pc' pb st, secs pc' = secs pc -> CH pc' pb st = CH pc pb st.
Proof. intros. unfold CH, all_chunks. rewrite !secs_app, H. reflexivity. Qed.

#[using="Type"] Lemma AINV_repc : forall pc pc' pb st c r',
  AINV pc pb st -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> AINV pc' pb (put_cls c r' st).
Proof.
  intros pc pc' pb st c r' H Hc Hwf Hcnt Hsec HR. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  rewrite (CH_put pc' pb c r' st), (CH_repc pc pc' pb st Hsec).
  split.
  { intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
    destruct (Z.eq_dec c' c) as [->|Hne].
    - rewrite get_put_eq. exact HR.
    - rewrite get_put_ne by congruence. pose proof (HC c' Hc') as X. unfold cls_inv in X.
      unfold all_chunks in *. rewrite !cntP_app in *. rewrite (Hcnt c' Hc' Hne). exact X. }
  split.
  { rewrite all_chunks_put. unfold all_chunks in *. apply Forall_app in H2 as [_ H2]. apply Forall_app. split; assumption. }
  rewrite qbatches_put. repeat (split; [assumption|]). assumption.
Qed.

#[using="Type"] Lemma INV_repc : forall pc pc' pb st c r' mo,
  INV pc pb st mo -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> cls_mapped_bytes' (get_cls st c) <= cls_mapped_bytes' r' ->
  INV pc' pb (put_cls c r' st) mo.
Proof.
  intros pc pc' pb st c r' mo [HA HM] Hc Hwf Hcnt Hsec HR Hmono. split.
  - apply AINV_repc with (pc := pc); assumption.
  - rewrite CH_put, (CH_repc pc pc' pb st Hsec). apply (AMI_mono _ st); auto. rewrite commit_bytes_put by exact Hc. lia.
Qed.

#[using="Type"] Lemma AINV_init_cache : forall pc pb st, AINV pc pb st -> AINV pc pb (init_cache st).
Proof.
  intros pc pb st H. unfold init_cache. destruct (a_cinit st) eqn:E; [exact H|].
  unfold AINV in *. destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_cinit a_cinit] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold max_count in *. cbn [a_cinit set_cinit] in *. rewrite E in X.
  unfold get_cls in *. cbn [a_cls set_cinit] in *.
  unfold all_chunks, qbatches, live_chunks in *. cbn [a_live a_qloc a_qglob set_cinit] in *.
  pose proof (primary_class_facts 0 ltac:(lia) eq_refl) as _.
  assert (0 <= max_cached c) by (unfold max_cached; lia). lia.
Qed.

#[using="Type"] Lemma INV_init_cache : forall pc pb st mo, INV pc pb st mo -> INV pc pb (init_cache st) mo.
Proof.
  intros pc pb st mo [HA HM]. split; [apply AINV_init_cache; exact HA|].
  rewrite CH_init_cache. apply (AMI_mono _ st); auto.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - rewrite commit_bytes_init_cache. lia.
Qed.

#[using="Type"] Lemma same_but_init_cache : forall c st, same_but c (init_cache st) st \/ True. Proof. intros. right. exact I. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n -> is_primary n = true -> c = class_id (needed_size n) ->
  size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     atot (k st' true) mo' P) ->
  atot (cache_alloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hn Hp Hcl Hroom HSB Hk.
  pose proof (primary_class_facts n Hn Hp) as F. cbv zeta in F. rewrite <- Hcl in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Hc : 1 <= c <= 31) by lia.
  assert (Hwf : chunk_wf (CPrim c n)).
  { cbn. split; [|exact Hcl]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [|lia]. rewrite (large_not_primary n Hlt) in Hp. discriminate. }
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (REPC : forall st0 r', INV pc pb st0 mo -> all_chunks pc pb st0 = all_chunks pc pb st -> qbatches pb st0 = qbatches pb st ->
            CLSOK (CPrim c n :: pc) pb st0 c r' -> cls_mapped_bytes' (get_cls st0 c) <= cls_mapped_bytes' r' ->
            INV (CPrim c n :: pc) pb (put_cls c r' st0) mo).
  { intros st0 r' HI0 E1 E2 HR Hm. apply (INV_repc pc); auto.
    - constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
    - intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  unfold cache_alloc. cbv zeta.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [Hpos|Hz].
  - (* [comment removed for export] *)
    apply Hk; [|left; apply same_but_put].
    apply REPC; auto. all: try (unfold cls_mapped_bytes'; cproj; lia).
    unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
  - rewrite max_count_init_cache, get_cls_init_cache.
    assert (Hhalf : 1 <= max_cached c / 2 <= 8 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split. split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia. apply Z.mul_div_le; lia. }
    set (m := max_cached c / 2) in *. clearbody m.
    pose proof (INV_init_cache _ _ _ _ HI) as HI1.
    destruct (Z.leb_spec m (c_num_freed (get_cls st c))) as [Hen|Hlt].
    + (* [comment removed for export] *)
      destruct (Z.ltb_spec (c_num_freed (get_cls st c)) m); [lia|].
      apply Hk; [|right; apply same_but_put].
      apply REPC; auto; rewrite ?all_chunks_init_cache, ?qbatches_init_cache, ?get_cls_init_cache; try reflexivity.
      all: try (unfold cls_mapped_bytes'; cproj; lia).
      unfold CLSOK. cproj. rewrite max_count_init_cache, all_chunks_init_cache, qbatches_init_cache, all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
    + (* [comment removed for export] *)
      apply (populate_ok R P pc pb (init_cache st) c (m - c_num_freed (get_cls st c)) _ mo HI1 Hc ltac:(lia) ltac:(lia)).
      * rewrite get_cls_init_cache || idtac. apply Z.le_trans with (m * size_of_class c); [apply Z.mul_le_mono_nonneg_r; lia| lia].
      * rewrite get_cls_init_cache. rewrite C10.
        assert (size_of_class c * c_num_freed (get_cls st c) <= size_of_class c * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (size_of_class c * c_count (get_cls st c) = 0) by (replace (c_count (get_cls st c)) with 0 by lia; ring).
        nia || lia.
      * rewrite CH_init_cache. exact HSB.
      * intros st2 mo2 HI2 HSB2 Ecnt Enf. rewrite get_cls_init_cache in Ecnt, Enf.
        destruct (Z.ltb_spec (c_num_freed (get_cls st2 c)) m); [lia|].
        pose proof HI2 as [HA2 HM2]. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        assert (AC : all_chunks pc pb st2 = all_chunks pc pb st /\ qbatches pb st2 = qbatches pb st).
        { destruct HSB2 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. unfold init_cache in Hl, Hq1, Hq2.
          destruct (a_cinit st); cbn in Hl, Hq1, Hq2; rewrite Hl, Hq1, Hq2; split; reflexivity. }
        destruct AC as [AC1 AC2].
        apply Hk. 2:{ right. eapply same_but_trans; [exact HSB2| apply same_but_put]. }
        apply (INV_repc pc); auto.
        -- constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
        -- intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
        -- unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. rewrite AC1, AC2 in D10. rewrite AC1, AC2.
           rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *. repeat split; try lia.
        -- unfold cls_mapped_bytes'. cproj. lia.
Qed.

#[using="Type"] Lemma AMI_perm : forall ch ch' st mo, Permutation ch ch' -> AMI ch st mo -> AMI ch' st mo.
Proof.
  intros ch ch' st mo HP H. destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  unfold AsanInv.AMI. repeat (split; [assumption|]). exists L0. split; [|split; assumption].
  eapply Permutation_trans; [exact HPm|]. apply Permutation_app_head. apply Permutation_map. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AINV_live_perm : forall pc pc' pb st lv nx,
  AINV pc pb st ->
  Permutation (all_chunks pc' pb (set_next nx (set_live lv st))) (all_chunks pc pb st) ->
  (forall id ch, lv !! id = Some ch -> (id < nx)%N) ->
  live_budget (set_next nx (set_live lv st)) ->
  AINV pc' pb (set_next nx (set_live lv st)).
Proof.
  intros pc pc' pb st lv nx H HP Hid HLB. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_next set_live a_cinit] in *.
  assert (Hq : qbatches pb (set_next nx (set_live lv st)) = qbatches pb st) by reflexivity.
  assert (HCH : zlen (CH pc' pb (set_next nx (set_live lv st))) = zlen (CH pc pb st)).
  { unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. exact HP. }
  split.
  { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_next set_live] in *.
    rewrite Hq, (cntP_perm c _ _ HP). exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HP| exact H2]. }
  rewrite Hq, HCH. repeat (split; [assumption|]). exact HLB.
Qed.

#[using="Type"] Lemma INV_hand_to_live : forall ch pc pb st mo,
  INV (ch :: pc) pb st mo ->
  live_budget_list (ch :: live_chunks st) ->
  INV pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st)) mo.
Proof.
  intros ch pc pb st mo [HA HM] HLB.
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  pose proof (live_chunks_insert st (a_next st) ch Hnone) as HPl.
  assert (HP : Permutation (all_chunks pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st))) (all_chunks (ch :: pc) pb st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches pb (set_next (N.succ (a_next st)) (set_live (<[a_next st:=ch]> (a_live st)) st))) with (qbatches pb st).
    eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact HPl. }
    rewrite app_comm_cons. apply Permutation_sym. cbn. apply Permutation_middle. }
  split.
  - apply (AINV_live_perm (ch :: pc)); auto.
    + intros id ch0 Hl. destruct (N.eq_dec id (a_next st)) as [->|Hne]; [lia|].
      rewrite lookup_insert_ne in Hl by congruence. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ Hl). lia.
    + apply live_budget_list_iff. unfold live_chunks. cbn [a_live set_next set_live]. unfold live_chunks in HPl. cbn [a_live set_live] in HPl.
      destruct HLB as (B1 & B2 & B3). split; [|split].
      * intros c Hc. rewrite (cntP_perm c _ _ HPl). apply B1. exact Hc.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)). exact B2.
      * assert (E : forall l l', Permutation l l' -> secbytes l = secbytes l').
        { intros l l' P0. induction P0; cbn; try lia. - destruct x; lia. - destruct x, y; lia. }
        rewrite (E _ _ HPl). exact B3.
  - apply (AMI_perm (CH (ch :: pc) pb st)).
    + unfold CH. apply secs_perm. apply Permutation_sym. exact HP.
    + apply (AMI_mono _ st); auto. apply Z.le_refl || (unfold commit_bytes, csum, get_cls; cbn; lia).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_le : forall x a, 0 < a -> rdn x a <= x. Proof. intros. unfold rdn. rewrite Z.mul_comm. apply Z.mul_div_le. lia. Qed.
#[using="Type"] Lemma rdn_mod : forall x a, 0 < a -> rdn x a mod a = 0. Proof. intros. unfold rdn. apply Z_mod_mult. Qed.

#[using="Type"] Lemma poison0_ok : forall R (P : R -> Model -> Prop) pc pb st (k : AM R) mo a s,
  INV pc pb st mo -> 0 <= a -> 0 <= s <= 2^31 ->
  (a + s <= LS_LO \/ (KHIGH <= a /\ a + s <= ATOP)) ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall mo', INV pc pb st mo' -> atot k mo' P) ->
  atot (poison0 a s k) mo P.
Proof.
  intros R P pc pb st k mo a s HI Ha Hs Hrange HSB Hk.
  unfold poison0. apply Hk. exact HI.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma seps_In2 : forall l x y, seps l -> In x l -> In y l -> x <> y -> wsep x y.
Proof.
  intros l x y Hs. induction Hs as [|p l HF Hs IH]; intros Hx Hy Hne; [destruct Hx|].
  rewrite Forall_forall in HF. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - apply HF. exact Hy.
  - apply wsep_sym. apply HF. exact Hx.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma INV_ptr_range : forall pc pb st mo, INV pc pb st mo -> sh_apart (a_ptr_array st) PTR_SZ.
Proof.
  intros pc pb st mo HI. destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS). destruct (INV_ptr _ _ _ _ HI) as (HinP & P2 & _).
  pose proof HI as [HA HM]. pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & M9 & _).
  destruct (AINV_geom _ _ _ HA) as (_ & _ & G3 & G4).
  assert (NE : forall b sz, sz <> PTR_SZ -> 0 <= sz < 2^64 -> went (a_ptr_array st, PTR_SZ) <> went (b, sz)).
  { intros b sz Hsz Hr E. unfold went in E. cbn [fst snd] in E.
    assert (E2 : bv_unsigned (Z_to_bv 64 PTR_SZ) = bv_unsigned (Z_to_bv 64 sz)) by (f_equal; congruence).
    unfold PTR_SZ in *. rewrite !unsigned_lit in E2 by lia. lia. }
  pose proof (seps_In2 _ _ _ M9 HinP HinLS (NE LS_LO LS_SZ ltac:(unfold LS_SZ, PTR_SZ; lia) ltac:(unfold LS_SZ; lia))) as W1.
  pose proof (seps_In2 _ _ _ M9 HinP HinGAP (NE GAP_LO GAP_SZ ltac:(unfold GAP_SZ, PTR_SZ; lia) ltac:(unfold GAP_SZ; lia))) as W2.
  pose proof (seps_In2 _ _ _ M9 HinP HinHS (NE HS_LO HS_SZ ltac:(unfold HS_SZ, PTR_SZ; lia) ltac:(unfold HS_SZ; lia))) as W3.
  unfold wsep, went in W1, W2, W3. cbn [fst snd] in W1, W2, W3. unfold sh_apart.
  unfold LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ, KHIGH, PTR_SZ in *. rewrite !unsigned_lit in W1, W2, W3 by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_range : forall pc pb st mo z n,
  INV pc pb st mo -> 0 < z -> 0 < n -> z + n <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 n) = true ->
  z + n <= LS_LO \/ (KHIGH <= z /\ z + n <= ATOP).
Proof.
  intros pc pb st mo z n HI Hz Hn Hce Hrf.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS).
  rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
  pose proof (region_free_wsep _ _ _ Hrf) as HW. rewrite Forall_forall in HW.
  pose proof (HW _ HinLS) as W1. pose proof (HW _ HinGAP) as W2. pose proof (HW _ HinHS) as W3.
  unfold wsep, went in W1, W2, W3. cbn [fst snd] in W1, W2, W3.
  unfold ACEIL, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ, KHIGH in *. rewrite !unsigned_lit in W1, W2, W3 by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
#[using="Type"] Lemma zsizes_perm : forall l l', Permutation l l' -> zsizes l = zsizes l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.
#[using="Type"] Lemma zsizes_filter_le : forall f l, Forall (fun e => 0 <= snd e) l -> zsizes (List.filter f l) <= zsizes l.
Proof. induction l as [|e l IH]; intros HF; cbn; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF). destruct (f e); cbn; lia. Qed.
#[using="Type"] Lemma filter_none : forall {A} (f : A -> bool) l, Forall (fun x => f x = false) l -> List.filter f l = [].
Proof. induction l as [|x l IH]; intros HF; cbn; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. rewrite Hx. apply IH. exact HF. Qed.
#[using="Type"] Lemma zsizes_zent_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> Forall (fun e => 0 <= fst e < 2^64) ch ->
  zsizes (map zent (map went ch)) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros H1 H2; cbn -[Z_to_bv bv_unsigned Z.pow]; [reflexivity|].
  apply Forall_cons_iff in H1 as [A1 H1]. apply Forall_cons_iff in H2 as [A2 H2]. cbn [fst snd] in A1, A2.
  rewrite unsigned_lit by lia. rewrite (IH H1 H2). reflexivity.
Qed.
(* [comment removed for export] *)

#[using="Type"] Lemma achunks_all_chunks : forall pc pb st ch, In ch (achunks st) -> In ch (all_chunks pc pb st).
Proof.
  intros pc pb st ch Hin. unfold achunks, all_chunks, live_chunks, qchunks, qbatches in *.
  apply in_app_iff. right. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin| right].
  apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map. exists b. split; [|exact Hin]. apply in_app_iff. right. exact Hb.
Qed.

#[using="Type"] Lemma grant_avoids : forall pc pb st mo z len,
  INV pc pb st mo -> 0 < z -> 0 < len -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  avoids_all z len (RESV ++ asec_ranges st) = true.
Proof.
  intros pc pb st mo z len HI Hz Hlen Hce Hrf.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRC).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (ZL : 0 <= z < 2^64 /\ 0 <= len < 2^64) by lia.
  assert (RF : forall e, In e (vm_reserved (m_vmmaps mo) ++ L0 ++ map went (CH pc pb st)) ->
               z + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= z).
  { intros [b sz] He. pose proof (region_free_In _ _ _ b sz Hrf) as X. rewrite !unsigned_lit in X by lia. cbn [fst snd]. apply X.
    apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right].
    eapply Permutation_in; [apply Permutation_sym; exact HPm| exact He]. }
  unfold avoids_all. apply forallb_forall. intros [lo hi] Hin. unfold iv_clear. cbn [fst snd].
  apply in_app_iff in Hin as [Hin|Hin].
  - (* [comment removed for export] *)
    destruct (proj1 (Forall_forall _ _) HRC _ Hin) as (e & He & C1 & C2). cbn [fst snd] in C1, C2.
    specialize (RF e ltac:(rewrite app_assoc; apply in_app_iff; left; exact He)).
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
  - (* [comment removed for export] *)
    unfold asec_ranges in Hin. apply in_flat_map in Hin as (ch & Hch & Hin).
    destruct ch as [c n|mb ms n]; cbn in Hin; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (achunks_all_chunks pc pb st _ Hch) as Hall.
    assert (HinCH : In (mb, ms) (CH pc pb st)).
    { unfold CH, secs. apply in_flat_map. exists (CSec mb ms n). split; [exact Hall| cbn; left; reflexivity]. }
    destruct HA as (_ & HW & _). pose proof (proj1 (Forall_forall _ _) HW _ Hall) as Hwf. cbn in Hwf.
    destruct Hwf as (Hn' & Hms & Hwf). pose proof (sec_map_size_bounds n ltac:(lia)). unfold LS_LO, KHIGH, ACEIL in Hwf.
    specialize (RF (went (mb, ms)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; exact HinCH)).
    unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma large_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st n (k : astate -> option achunk -> AM R) mo,
  INV pc pb st mo -> 64512 < n <= 2^29 ->
  zsum2 (CH pc pb st) + sec_map_size n <= 2^35 -> zlen (CH pc pb st) <= 5330 ->
  (forall st' mo' mb, INV (CSec mb (sec_map_size n) n :: pc) pb st' mo' ->
      (st' = set_nsec (a_nsec st + 1) st \/ st' = set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) ->
      atot (k st' (Some (CSec mb (sec_map_size n) n))) mo' P) ->
  atot (large_alloc ATOP RESV st n k) mo P.
Proof.
  intros R P pc pb st n k mo HI Hn HSB HSL Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_alloc. unfold ev. apply atotal_vis.
  { apply (INV_grant_aok pc pb st mo n HI ltac:(lia)); lia. }
  intros z mo' Hpost. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML in Hpost.
  destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).
  assert (RUP : rup (sec_map_size n) PG = sec_map_size n).
  { unfold rup, PG. pose proof (Z.div_mod (sec_map_size n) 4096 ltac:(lia)) as Hd. rewrite MSA in Hd.
    replace (sec_map_size n + 4096 - 1) with (sec_map_size n / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095/4096) with 0. lia. }
  assert (Hok : mmap_answer_ok ATOP (sec_map_size n) z = true).
  { unfold mmap_answer_ok. rewrite RUP. apply orb_true_iff. right. unfold TWO64, PG.
    rewrite (proj2 (Z.ltb_lt 0 z)) by lia. rewrite Z1. cbn [Z.eqb andb]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hok. cbn [negb]. rewrite is_err_small by (unfold TWO64; lia).
  pose proof (grant_range pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as Hrange.
  (* [comment removed for export] *)
  pose proof (grant_avoids pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as HAV.
  rewrite HAV. cbn [andb negb].
  (* [comment removed for export] *)
  set (ch := CSec z (sec_map_size n) n).
  set (st1 := set_nsec (a_nsec st + 1) st).
  assert (HI1 : INV (ch :: pc) pb st1 (grant_model mo z (sec_map_size n))).
  { destruct HI as [HA HM]. split.
    - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
      unfold st1. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
      rewrite all_chunks_set_nsec, all_chunks_cons.
      change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st).
      change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with (sec_of ch ++ CH pc pb st).
      split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
               rewrite all_chunks_set_nsec, all_chunks_cons, cntP_cons. cbn [is_prim_of]. change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st). rewrite Z.add_0_l. exact X. }
      split. { constructor; [|exact H2]. cbn. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hrange. }
      split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split. { unfold ch. cbn [sec_of app]. rewrite zlen_cons. lia. }
      split; [exact H7|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
    - unfold st1. change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with ((z, sec_map_size n) :: CH pc pb st).
      apply (AMI_mono _ st); try reflexivity; try (unfold commit_bytes, csum, get_cls; cbn; lia).
      apply AMI_grant; auto; lia. }
  destruct (Z.eqb_spec (a_nsec st) (a_nres st)) as [Heq|Hne].
  2:{ apply Hk; [exact HI1| left; reflexivity]. }
  (* [comment removed for export] *)
  destruct HI as [HA HM]. pose proof HA as (_ & _ & _ & _ & _ & Hnsec & Hres & _).
  assert (Hres0 : a_nres st = 0) by (destruct Hres as [?|E]; [assumption|]; rewrite E in Heq; unfold K_CHUNKS_BLOCK in Heq; lia).
  rewrite Hres0 in Hk |- *. destruct (Z.ltb_spec K_PTRARR_RESERVE (8 * (0 + K_CHUNKS_BLOCK))) as [X|_]; [unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK in X; lia|].
  destruct (INV_ptr _ _ _ _ HI1) as (HinP & P2 & PRF). unfold st1 in HinP, P2, PRF. cbn [a_ptr_array set_nsec] in HinP, P2, PRF.
  destruct (AINV_geom _ _ _ HA) as (_ & _ & G3 & G4).
  rewrite Z.mul_0_r, Z.add_0_r.
  assert (HBS : B (went (a_ptr_array st, PTR_SZ)) = a_ptr_array st /\ S (went (a_ptr_array st, PTR_SZ)) = PTR_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PTR_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  apply atotal_vis.
  { apply (INV_fixed_aok _ _ _ _ (went (a_ptr_array st, PTR_SZ)) _ _ HI1); auto; try lia.
    - rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    - (* [comment removed for export] *)
      apply (region_free_sub _ (a_ptr_array st) PTR_SZ); [exact PRF| | | | |]; unfold K_PTRARR_COMMIT, PTR_SZ in *; lia.
    - unfold K_PTRARR_COMMIT. lia.
    - change (CH (ch :: pc) pb st1) with ((z, sec_map_size n) :: CH pc pb st). cbn [zsum2 snd]. lia.
    - pose proof (INV_ptr_range _ _ _ _ HI1) as PR. unfold st1 in PR. cbn [a_ptr_array set_nsec] in PR.
      unfold sh_apart, K_PTRARR_COMMIT, PTR_SZ in *. lia. }
  intros z2 mo2 Hpost2. cbn [apost] in Hpost2.
  assert (Hpz : (a_ptr_array st =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Hpz in Hpost2. destruct Hpost2 as [-> ->].
  rewrite fixed_answer_ok_self. cbn [negb]. rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PTR_SZ in *; lia).
  apply Hk; [| right; reflexivity].
  assert (ML2 : mmap_len K_PTRARR_COMMIT = K_PTRARR_COMMIT) by reflexivity. rewrite ML2.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    unfold st1 in *. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec set_nres a_cinit] in *.
    change (all_chunks (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (all_chunks (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    change (qbatches pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (qbatches pb (set_nsec (a_nsec st + 1) st)).
    change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec set_nres] in *. exact X. }
    repeat (split; [assumption|]). split; [right; lia|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec set_nres] in *. exact H9.
  - change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) st1)) with (CH (ch :: pc) pb st1).
    apply (AMI_commit _ st1 _ _ (went (a_ptr_array st, PTR_SZ))); auto; try lia.
    + rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    + unfold K_PTRARR_COMMIT. lia.
    + unfold st1, commit_bytes, csum, get_cls. cbn. unfold K_CHUNKS_BLOCK, K_PTRARR_COMMIT. lia.
Qed.

(* [comment removed for export] *)
Definition mkch (n mb ms : Z) : achunk := if is_primary n then CPrim (class_id (needed_size n)) n else CSec mb ms n.

(* [comment removed for export] *)
Definition csig (ch : achunk) : Z + Z := match ch with CPrim c _ => inl c | CSec _ _ n => inr n end.
#[using="Type"] Lemma live_budget_list_sig : forall ch ch' L, csig ch = csig ch' -> live_budget_list (ch :: L) -> live_budget_list (ch' :: L).
Proof.
  intros ch ch' L Hs (B1 & B2 & B3). unfold live_budget_list.
  destruct ch as [c n|mb ms n], ch' as [c' n'|mb' ms' n']; cbn in Hs; try discriminate; injection Hs as E; subst.
  - split; [|split; assumption]. intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1.
  - split; [|split]. { intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1. }
    { rewrite secs_cons, zlen_app in *. cbn [sec_of] in *. unfold zlen in *. cbn [length] in *. lia. }
    { cbn [secbytes] in *. lia. }
Qed.

#[using="Type"] Lemma sec_map_size_ge : forall n, 64512 < n -> n + 8192 <= sec_map_size n.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hr.
  pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). unfold PG in *. lia.
Qed.

#[using="Type"] Lemma not_primary_large : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof.
  intros n Hn Hp. destruct (Z_lt_dec 64512 n); [lia|]. rewrite is_primary_iff in Hp by lia. apply Z.leb_gt in Hp. lia.
Qed.

(* [comment removed for export] *)
Definition malloc_post (st : astate) (n : Z) (r : astate * option AsanCtrl.aptr) (mo' : Model) : Prop :=
  exists ch, snd r = Some (a_next st) /\ INV [] [] (fst r) mo' /\ a_live (fst r) = <[a_next st := ch]> (a_live st)
  /\ (a_live st) !! (a_next st) = None /\ chunk_size ch = n
  /\ a_qloc_bytes (fst r) = a_qloc_bytes st /\ a_qglob_bytes (fst r) = a_qglob_bytes st /\ a_qloc (fst r) = a_qloc st /\ a_qglob (fst r) = a_qglob st
  /\ a_next (fst r) = N.succ (a_next st).   (* [comment removed for export] *)

#[using="Type"] Theorem amalloc_core : forall st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^29 ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  atot (amalloc ATOP RESV st n) mo (malloc_post st n).
Proof.
  intros st mo n HI Hql Hqg Hn HLB.
  pose proof HI as [HA HM].
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22).
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hq1 & Hq2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  destruct (CH_bounds [] [] st HA ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [HCL HCS].
  assert (HCL2 : zlen (CH [] [] st) <= 5330).
  { destruct (CH_bounds_gen [] [] st (2^28 + 2^22) HA HQB ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [X _]. lia. }
  assert (Hns : needed_size n <= 2^40).
  { unfold needed_size, needed0, rounded_size. pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
    pose proof (rz_log_range n) as Hrl.
    assert (0 <= rz_size n <= 2048).
    { unfold rz_size. rewrite Z.shiftl_mul_pow2 by lia. change 2048 with (16 * 2^7).
      split. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]. apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]. }
    destruct (is_primary n); lia. }
  unfold amalloc. destruct (Z.ltb_spec (2^40) n); [lia|]. destruct (Z.ltb_spec (2^40) (needed_size n)); [lia|]. cbn [orb].
  destruct (is_primary n) eqn:Hp.
  - (* [comment removed for export] *)
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
    set (c := class_id (needed_size n)) in *.
    apply (cache_alloc_ok _ _ [] [] st c n _ mo HI ltac:(lia) Hp eq_refl).
    + eapply room_of_AINV; eauto; try lia. unfold cntP, zlen. cbn. lia.
    + lia.
    + intros st' mo' HI' HSB'.
      assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
      { destruct HSB' as [X|X]; destruct X as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2&_); [repeat split; assumption|].
        unfold init_cache in *; destruct (a_cinit st); cbn in *; repeat split; assumption. }
      destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
      cbv beta iota. apply atotal_ret. exists (CPrim c n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. specialize (HLB 0 0). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat split; auto.
  - (* [comment removed for export] *)
    pose proof (not_primary_large n ltac:(lia) Hp) as Hbig. pose proof (sec_map_size_bounds n ltac:(lia)) as SB. pose proof (sec_map_size_ge n Hbig) as SG.
    apply (large_alloc_ok _ _ [] [] st n _ mo HI ltac:(lia) ltac:(lia) HCL2).
    intros st' mo' mb HI' Hst'.
    assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
    { destruct Hst' as [-> | ->]; repeat split; reflexivity. }
    destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
    cbv beta iota. cbn [chunk_user_beg].
    pose proof HI' as [HA' HM']. pose proof HA' as (_ & HW' & _). rewrite all_chunks_cons in HW'. apply Forall_cons_iff in HW' as [Hwf _].
    cbn in Hwf. destruct Hwf as (_ & _ & Hal & Hmb & Hrange).
    assert (Hland : 0 <= Z.land n (Z.lnot 7) <= n).
    { rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia. }
    assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
    rewrite Hrz. unfold PG.
    apply (poison0_ok _ _ [CSec mb (sec_map_size n) n] [] st' _ mo'); auto; try lia.
    + rewrite CH_cons. cbn [sec_of app zsum2 snd].
      replace (CH [] [] st') with (CH [] [] st) by (unfold CH, all_chunks, live_chunks, qbatches; rewrite E1, E5, E6; reflexivity). lia.
    + intros mo'' HI''. apply atotal_ret. exists (CSec mb (sec_map_size n) n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI''|]. unfold live_chunks. rewrite E1. specialize (HLB mb (sec_map_size n)). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat split; auto.
Qed.

End WithResv.
End AsanTotal.

(* [comment removed for export] *)
Module AsanFree.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import SizeHist Gap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanInv AsanBudget. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanBudget OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok ATOP).
Local Notation apost := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

(* [comment removed for export] *)
Definition qframe (st st' : astate) : Prop :=
  a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st
  /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st.
#[using="Type"] Lemma qframe_refl : forall st, qframe st st. Proof. intros. unfold qframe. repeat split; reflexivity. Qed.
#[using="Type"] Lemma qframe_trans : forall a b c, qframe a b -> qframe b c -> qframe a c.
Proof. intros a b c (A1&A2&A3&A4&A5&A6&A7&A8) (B1&B2&B3&B4&B5&B6&B7&B8). unfold qframe. repeat split; congruence. Qed.
#[using="Type"] Lemma qframe_same_but : forall c st st', same_but c st st' -> qframe st st'.
Proof. intros c st st' (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12). unfold qframe. repeat split; assumption. Qed.
#[using="Type"] Lemma qframe_init_cache : forall st, qframe st (init_cache st).
Proof. intros. unfold qframe, init_cache. destruct (a_cinit st); repeat split; reflexivity. Qed.
#[using="Type"] Lemma qframe_lists : forall pc pb st st', qframe st st' ->
  all_chunks pc pb st' = all_chunks pc pb st /\ qbatches pb st' = qbatches pb st /\ CH pc pb st' = CH pc pb st.
Proof. intros pc pb st st' (H1&H2&H3&H4&H5&H6&_). unfold CH, all_chunks, qbatches, live_chunks. rewrite H1, H3, H5. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> AM R) mo,
  INV (CPrim c n :: pc) pb st mo -> 1 <= c <= 31 ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (cache_dealloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hc HSB Hk.
  pose proof (INV_init_cache _ _ _ _ HI) as HI1.
  pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  rewrite max_count_init_cache in C9. rewrite all_chunks_cons, cntP_cons in C10. cbn [is_prim_of] in C10. rewrite Z.eqb_refl in C10.
  assert (Hwfpc : Forall chunk_wf pc) by (destruct HA1 as (_ & HW & _); rewrite all_chunks_cons in HW; apply Forall_cons_iff in HW as [_ HW]; unfold all_chunks in HW; apply Forall_app in HW as [X _]; exact X).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb (init_cache st)) /\ 0 <= nbatch c (qbatches pb (init_cache st))).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (F : 32 <= size_of_class c <= 65536 /\ 2 <= max_cached c <= 16).
  { destruct HA1 as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    assert (Hp : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. rewrite <- Hcl in F. lia. }
  destruct F as [Hsz Hmc'].
  unfold cache_dealloc. cbv zeta. rewrite max_count_init_cache.
  destruct (Z.eqb_spec (c_count (get_cls (init_cache st) c)) (max_cached c)) as [Hfull|Hnf].
  - (* [comment removed for export] *)
    assert (Hhalf : 1 <= max_cached c / 2 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split; [apply Z.div_le_lower_bound; lia| apply Z.mul_div_le; lia]. }
    assert (Hm8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
    set (m := max_cached c / 2) in *. clearbody m.
    assert (Hnf8 : 4 * (c_num_freed (get_cls (init_cache st) c) + m) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (size_of_class c * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (c_allocated_user (get_cls (init_cache st) c)); [|lia]. rewrite C10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (32 * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size_of_class c * c_num_freed (get_cls (init_cache st) c)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      assert (m <= 8) by lia.
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    apply (ensure_ok R P (CPrim c n :: pc) pb (init_cache st) c (c_num_freed (get_cls (init_cache st) c) + m) _ mo HI1 Hc ltac:(lia) Hnf8).
    { rewrite CH_cons. cbn [sec_of app]. rewrite CH_init_cache. exact HSB. }
    intros st2 mo2 HI2 HSB2 E1 E2 E3 E4 E5. cbn [negb].
    pose proof HI2 as [HA2 HM2].
    destruct (qframe_lists (CPrim c n :: pc) pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2)) as (AC1 & AC2 & AC3).
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *.
        destruct (qframe_lists pc pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2)) as (AC1' & AC2' & AC3').
        rewrite all_chunks_cons, cntP_cons in D10. cbn [is_prim_of] in D10. rewrite Z.eqb_refl in D10.
        rewrite AC1', AC2' in D10 |- *. rewrite E1, E2, E3, E4 in *. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. eapply qframe_trans; [apply (qframe_same_but c); exact HSB2|]. apply (qframe_same_but c). apply same_but_put.
  - (* [comment removed for export] *)
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. rewrite max_count_init_cache. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. apply (qframe_same_but c). apply same_but_put.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma large_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st mb ms n (k : astate -> AM R) mo,
  INV (CSec mb ms n :: pc) pb st mo ->
  zsum2 (CH (CSec mb ms n :: pc) pb st) <= 2^35 ->
  (forall mo', INV pc pb (set_nsec (a_nsec st - 1) st) mo' -> atot (k (set_nsec (a_nsec st - 1) st)) mo' P) ->
  atot (large_dealloc st mb ms k) mo P.
Proof.
  intros R P pc pb st mb ms n k mo HI HSB Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_dealloc.
  apply (poison0_ok _ _ (CSec mb (sec_map_size n) n :: pc) pb st _ mo mb (sec_map_size n) HI ltac:(lia) ltac:(lia) Hrange HSB).
  intros mo1 HI1. unfold ev. apply atotal_vis.
  { apply (INV_munmap_aok _ _ _ _ mb (sec_map_size n) HI1); try lia.
    - rewrite CH_cons. cbn. left. reflexivity.
    - unfold LS_LO, ACEIL in *. lia.
    - unfold sh_apart. destruct Hrange as [X|[X _]]; [left; exact X| right; exact X]. }
  intros z mo2 Hpost. cbn [apost] in Hpost. destruct Hpost as [-> ->]. rewrite Z.eqb_refl.
  apply Hk.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
    rewrite all_chunks_set_nsec. change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st).
    change (CH pc pb (set_nsec (a_nsec st - 1) st)) with (CH pc pb st).
    rewrite all_chunks_cons in *. rewrite CH_cons in H6. cbn [sec_of app] in H6. rewrite zlen_cons in H6.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
             rewrite all_chunks_set_nsec. rewrite all_chunks_cons, cntP_cons in X. cbn [is_prim_of] in X.
             change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st). rewrite Z.add_0_l in X. exact X. }
    split. { apply Forall_cons_iff in H2 as [_ H2]. exact H2. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [lia|]. split; [exact H7|]. split; [exact H8|].
    unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
  - change (CH pc pb (set_nsec (a_nsec st - 1) st)) with (CH pc pb st).
    rewrite CH_cons in HM1. cbn [sec_of app] in HM1.
    apply (AMI_munmap [] (CH pc pb st) st); auto; try lia; try (unfold LS_LO, ACEIL in *; lia).
    unfold commit_bytes, csum, get_cls. cbn. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_chunk_ok : forall R (P : R -> Model -> Prop) pc pb st ch (k : astate -> AM R) mo,
  INV (ch :: pc) pb st mo -> zsum2 (CH (ch :: pc) pb st) <= 2^35 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (recycle_chunk st ch k) mo P.
Proof.
  intros R P pc pb st ch k mo HI HSB Hk. unfold recycle_chunk. destruct ch as [c n|mb ms n].
  - pose proof HI as [HA _]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    assert (Hp : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. rewrite <- Hcl in F.
    apply (cache_dealloc_ok R P pc pb st c n k mo HI ltac:(lia)).
    + rewrite CH_cons in HSB. cbn [sec_of app] in HSB. exact HSB.
    + exact Hk.
  - apply (large_dealloc_ok R P pc pb st mb ms n k mo HI HSB).
    intros mo' HI'. apply Hk; [exact HI'|]. unfold qframe. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma recycle_chunks_ok : forall R (P : R -> Model -> Prop) l pc pb st (k : astate -> AM R) mo,
  INV (l ++ pc) pb st mo -> zsum2 (CH (l ++ pc) pb st) <= 2^35 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (recycle_chunks st l k) mo P.
Proof.
  intros R P l. induction l as [|ch l IH]; intros pc pb st k mo HI HSB Hk; cbn [recycle_chunks app] in *.
  - apply Hk; [exact HI| apply qframe_refl].
  - apply (recycle_chunk_ok R P (l ++ pc) pb st ch _ mo HI HSB).
    intros st1 mo1 HI1 HQ1. apply (IH pc pb st1 k mo1 HI1).
    + destruct (qframe_lists (l ++ pc) pb st st1 HQ1) as (_ & _ & ->). rewrite CH_cons in HSB. rewrite zsum2_app in HSB.
      assert (0 <= zsum2 (sec_of ch)).
      { destruct HI as [HA _]. destruct HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
        destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct Hwf as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
      lia.
    + intros st2 mo2 HI2 HQ2. apply Hk; [exact HI2|]. eapply qframe_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zsum2_perm : forall l l', Permutation l l' -> zsum2 l = zsum2 l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.

#[using="Type"] Lemma AINV_requeue : forall pc pb pb' st ql lb qg gb,
  AINV pc pb st ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  AINV pc pb' (set_qglob qg gb (set_qloc ql lb st)).
Proof.
  intros pc pb pb' st ql lb qg gb HA HP HL HB Hlb Hgb. unfold AINV in *.
  destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_qglob set_qloc a_cinit] in *.
  assert (Hq : qbatches pb' (set_qglob qg gb (set_qloc ql lb st)) = pb' ++ ql ++ qg) by reflexivity.
  assert (HPa : Permutation (all_chunks pc pb' (set_qglob qg gb (set_qloc ql lb st))) (all_chunks pc pb st)).
  { unfold all_chunks. rewrite Hq. unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. exact HP. }
  rewrite Hq.
  split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_qglob set_qloc] in *.
           rewrite Hq. rewrite (cntP_perm c _ _ HPa). unfold nbatch in *. rewrite HL. exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
  split; [exact HB|]. split; [exact Hlb|]. split; [exact Hgb|].
  split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  unfold live_budget, live_chunks in *. cbn [a_live set_qglob set_qloc]. exact H13.
Qed.

#[using="Type"] Lemma INV_requeue : forall pc pb pb' st ql lb qg gb mo,
  INV pc pb st mo ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  INV pc pb' (set_qglob qg gb (set_qloc ql lb st)) mo.
Proof.
  intros pc pb pb' st ql lb qg gb mo [HA HM] HP HL HB Hlb Hgb. split; [eapply AINV_requeue; eauto|].
  apply (AMI_perm (CH pc pb st)).
  - unfold CH. apply secs_perm. unfold all_chunks. change (qbatches pb' (set_qglob qg gb (set_qloc ql lb st))) with (pb' ++ ql ++ qg).
    unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact HP.
  - apply (AMI_mono _ st); auto. unfold commit_bytes, csum, get_cls. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition shell : achunk := CPrim K_BATCH_CLASS 7000.
#[using="Type"] Lemma shell_class : class_id (needed_size 7000) = K_BATCH_CLASS. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma shell_wf : chunk_wf shell. Proof. cbn -[class_id needed_size]. split; [lia|]. symmetry. exact shell_class. Qed.

#[using="Type"] Lemma INV_open_batch : forall pc b pb st mo,
  INV pc (b :: pb) st mo -> INV (rev (b_chunks b) ++ shell :: pc) pb st mo.
Proof.
  intros pc b pb st mo [HA HM].
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    (* [comment removed for export] *)
    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons. cbn [is_prim_of shell].
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons in X.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true by reflexivity. lia. }
             replace (K_BATCH_CLASS =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa|]. constructor; [apply shell_wf| exact H2]. }
    split. { apply Forall_cons_iff in H3 as [_ H3]. exact H3. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. symmetry. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CH pc (b :: pb) st)); [| exact HM]. unfold CH. etransitivity; [| apply secs_perm; apply Permutation_sym; exact HPa]. cbn. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma do_recycle_ok : forall R (P : R -> Model -> Prop) bs pc st (k : astate -> AM R) mo,
  INV pc bs st mo -> zsum2 (CH pc bs st) <= 2^35 ->
  (forall st' mo', INV pc [] st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (do_recycle st bs k) mo P.
Proof.
  intros R P bs. induction bs as [|b bs IH]; intros pc st k mo HI HSB Hk; cbn [do_recycle].
  - apply Hk; [exact HI| apply qframe_refl].
  - pose proof (INV_open_batch _ _ _ _ _ HI) as HI1.
    assert (HPC : Permutation (CH (rev (b_chunks b) ++ shell :: pc) bs st) (CH pc (b :: bs) st)).
    { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite !secs_app, secs_cons. cbn [sec_of shell]. rewrite app_nil_l. rewrite <- !app_assoc.
      eapply Permutation_trans. { apply Permutation_app_tail. apply secs_perm. apply Permutation_sym. apply Permutation_rev. }
      rewrite (app_assoc (secs pc) (secs (live_chunks st))). rewrite (app_assoc (secs pc) (secs (live_chunks st)) (secs (b_chunks b) ++ _)).
      apply Permutation_app_swap_app. }
    apply (recycle_chunks_ok R P (rev (b_chunks b)) (shell :: pc) bs st _ mo HI1).
    + rewrite (zsum2_perm _ _ HPC). exact HSB.
    + intros st1 mo1 HI2 HQ1. apply (cache_dealloc_ok R P pc bs st1 K_BATCH_CLASS 7000 _ mo1 HI2 ltac:(unfold K_BATCH_CLASS; lia)).
      * destruct (qframe_lists pc bs st st1 HQ1) as (_ & _ & ->).
        pose proof (zsum2_perm _ _ HPC) as E. rewrite CH_cons in E || idtac.
        assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
        { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
          assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
          destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
          apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
          clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
          specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
        lia.
      * intros st2 mo2 HI3 HQ2. apply (IH pc st2 k mo2 HI3).
        -- destruct (qframe_lists pc bs st st2 (qframe_trans _ _ _ HQ1 HQ2)) as (_ & _ & ->).
           pose proof (zsum2_perm _ _ HPC). 
           assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
           { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
             assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
             destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
             apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
             clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
             specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
           lia.
        -- intros st3 mo3 HI4 HQ3. apply Hk; [exact HI4|]. eapply qframe_trans; [exact HQ1|]. eapply qframe_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma merge_batches_spec : forall rest cur,
  Forall batch_wf (cur :: rest) ->
  let '(l, ex, exb) := merge_batches cur rest in
  Permutation (qchunks (l ++ ex)) (qchunks (cur :: rest)) /\ zlen (l ++ ex) = zlen (cur :: rest)
  /\ bsum l + exb = bsum (cur :: rest) /\ bsum ex = exb /\ Forall batch_wf (l ++ ex) /\ 0 <= exb.
Proof.
  induction rest as [|nx rest IH]; intros cur HB.
  - cbn [merge_batches]. rewrite app_nil_r. cbn [bsum]. rewrite zlen_cons, zlen_nil. repeat split; auto; lia.
  - cbn [merge_batches]. apply Forall_cons_iff in HB as [Hc HB]. pose proof HB as HB0. apply Forall_cons_iff in HB as [Hn HB].
    destruct (Z.leb_spec (b_count cur + b_count nx) Q_BATCH) as [Hle|Hgt].
    + set (cur' := mkABatch (b_count cur + b_count nx) (b_size cur + (b_size nx - Q_BATCH_BYTES)) (b_chunks nx ++ b_chunks cur)).
      assert (Hc' : batch_wf cur').
      { destruct Hc as (C1 & C2 & C3 & C4). destruct Hn as (N1 & N2 & N3 & N4). unfold batch_wf, cur'. cbn [b_count b_size b_chunks].
        rewrite zlen_app, zsumc_app. repeat split; try lia. apply Forall_app; split; assumption. }
      specialize (IH cur' ltac:(constructor; assumption)). destruct (merge_batches cur' rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * rewrite !qchunks_app in *. rewrite qchunks_cons. cbn [b_chunks app]. rewrite !qchunks_cons.
        eapply Permutation_trans. { rewrite app_nil_l || idtac. exact I1. }
        rewrite qchunks_cons. unfold cur'. cbn [b_chunks]. rewrite <- app_assoc. eapply Permutation_trans; [apply Permutation_app_swap_app|]. rewrite app_assoc. apply Permutation_refl.
      * rewrite !zlen_app, !zlen_cons in *. lia.
      * cbn [bsum] in *. unfold cur' in I3. cbn [b_size] in I3. lia.
      * cbn [bsum b_size]. lia.
      * apply Forall_app in I5 as [I5a I5b]. apply Forall_app. split; [exact I5a|]. constructor; [|exact I5b].
        unfold batch_wf. cbn. unfold Q_BATCH, Q_BATCH_BYTES. repeat split; try lia. constructor.
      * unfold Q_BATCH_BYTES. lia.
    + specialize (IH nx HB0). destruct (merge_batches nx rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * cbn [app]. rewrite !qchunks_cons. apply Permutation_app_head. exact I1.
      * cbn [app]. rewrite !zlen_cons in *. lia.
      * cbn [bsum] in *. lia.
      * exact I4.
      * cbn [app]. constructor; assumption.
      * exact I6.
Qed.

#[using="Type"] Lemma dequeue_while_spec : forall l bytes mn,
  let '(taken, rest, bytes') := dequeue_while l bytes mn in
  taken ++ rest = l /\ bytes' = bytes - bsum taken /\ (bytes' <= mn \/ rest = []).
Proof.
  induction l as [|b l IH]; intros bytes mn; cbn [dequeue_while].
  - repeat split; auto. cbn. lia.
  - destruct (Z.ltb_spec mn bytes).
    + specialize (IH (bytes - b_size b) mn). destruct (dequeue_while l (bytes - b_size b) mn) as [[taken rest] bytes'].
      destruct IH as (I1 & I2 & I3). cbn [app bsum]. rewrite I1. repeat split; auto. lia.
    + repeat split; auto. cbn. lia.
Qed.

#[using="Type"] Lemma set_qloc_eta : forall st, set_qloc (a_qloc st) (a_qloc_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.
#[using="Type"] Lemma set_qglob_eta : forall st, set_qglob (a_qglob st) (a_qglob_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_pc_perm : forall pc pc' pb st mo, Permutation pc pc' -> INV pc pb st mo -> INV pc' pb st mo.
Proof.
  intros pc pc' pb st mo HP [HA HM].
  assert (HPa : Permutation (all_chunks pc' pb st) (all_chunks pc pb st)) by (unfold all_chunks; apply Permutation_app_tail; apply Permutation_sym; exact HP).
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa). exact X. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
    exact H7.
  - apply (AMI_perm (CH pc pb st)); [| exact HM]. unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_close_batch : forall pc b pb st mo,
  INV (rev (b_chunks b) ++ shell :: pc) pb st mo -> batch_wf b -> INV pc (b :: pb) st mo.
Proof.
  intros pc b pb st mo [HA HM] Hb.
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons in X. cbn [is_prim_of shell] in X.
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true in X by reflexivity. lia. }
             replace (K_BATCH_CLASS =? c) with false in X by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { pose proof (Permutation_Forall HPa H2) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
    split. { constructor; assumption. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CH (rev (b_chunks b) ++ shell :: pc) pb st)); [| exact HM]. unfold CH. etransitivity; [apply secs_perm; exact HPa|]. cbn. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma recycle_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc st = [] -> a_qloc_bytes st = 0 -> bsum (a_qglob st) <= 2^30 ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MIN -> atot (k st') mo' P) ->
  atot (recycle st Q_MIN k) mo P.
Proof.
  intros R P st k mo HI Hql Hqlb HQ Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  assert (Hqb : qbatches [] st = a_qglob st) by (unfold qbatches; rewrite Hql; reflexivity).
  rewrite Hqb in HBW. 
  assert (HWq : Forall chunk_wf (qchunks (a_qglob st))).
  { unfold all_chunks in HW. rewrite Hqb in HW. cbn [app] in HW. apply Forall_app in HW as [_ HW]. exact HW. }
  destruct (quarantine_class_bound 1 (a_qglob st) ltac:(lia) HBW HWq) as (_ & Hov & Hpos).
  unfold recycle. cbv zeta. rewrite Hb2.
  destruct (Z.ltb_spec (bsum (a_qglob st)) (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)))) as [X|_]; [unfold Q_BATCH_BYTES, zlen in *; lia|].
  (* [comment removed for export] *)
  assert (HMB : forall gl ex exb,
    (if (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) <? bsum (a_qglob st)) && (bsum (a_qglob st) * 100 <? Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) * 200)
     then match a_qglob st with [] => ([], [], 0) | b :: rest => merge_batches b rest end
     else (a_qglob st, [], 0)) = (gl, ex, exb) ->
    Permutation (qchunks (gl ++ ex)) (qchunks (a_qglob st)) /\ zlen (gl ++ ex) = zlen (a_qglob st)
    /\ bsum gl + exb = bsum (a_qglob st) /\ bsum ex = exb /\ Forall batch_wf (gl ++ ex) /\ 0 <= exb).
  { intros gl ex exb E. destruct (_ && _).
    - destruct (a_qglob st) as [|b rest] eqn:Eq.
      + injection E as <- <- <-. cbn. repeat split; auto; try lia; try constructor.
      + pose proof (merge_batches_spec rest b HBW) as MS. rewrite E in MS. exact MS.
    - injection E as <- <- <-. rewrite app_nil_r. cbn [bsum]. repeat split; auto; lia. }
  destruct (if _ && _ then _ else _) as [[gl ex] exb] eqn:E. specialize (HMB gl ex exb eq_refl). destruct HMB as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (dequeue_while_spec gl (bsum (a_qglob st) - exb) Q_MIN) as DS.
  destruct (dequeue_while gl (bsum (a_qglob st) - exb) Q_MIN) as [[taken rest] bytes2]. destruct DS as (D1 & D2 & D3).
  assert (Hb2' : bytes2 = bsum rest) by (subst gl; rewrite bsum_app in M3; lia).
  assert (Hrest0 : 0 <= bsum rest).
  { apply Forall_app in M5 as [M5 _]. subst gl. apply Forall_app in M5 as [_ M5].
    clear - M5. induction rest as [|b rest IH]; [cbn; lia|]. apply Forall_cons_iff in M5 as [(B1&B2&B3&B4) M5]. cbn. specialize (IH M5).
    assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia. }
  destruct (Z.ltb_spec Q_MIN bytes2) as [X|_].
  { exfalso. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN in X. lia. }
  (* [comment removed for export] *)
  assert (HI1 : INV [] (ex ++ taken) (set_qglob rest bytes2 st) mo).
  { replace (set_qglob rest bytes2 st) with (set_qglob rest bytes2 (set_qloc (a_qloc st) (a_qloc_bytes st) st)) by (rewrite set_qloc_eta; reflexivity).
    rewrite Hql, Hqlb.
    apply (INV_requeue [] [] (ex ++ taken) st [] 0 rest bytes2 mo HI).
    - rewrite Hqb. cbn [app]. rewrite <- app_assoc. eapply Permutation_trans; [|exact M1].
      rewrite <- D1. rewrite !qchunks_app. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_refl.
    - rewrite Hqb, <- M2, <- D1. cbn [app]. rewrite !zlen_app. lia.
    - cbn [app]. rewrite <- D1 in M5. apply Forall_app in M5 as [M5a M5b]. apply Forall_app in M5a as [M5t M5r].
      apply Forall_app; split; [apply Forall_app; split; assumption| exact M5r].
    - reflexivity.
    - exact Hb2'. }
  apply (do_recycle_ok R P (ex ++ taken) [] (set_qglob rest bytes2 st) k mo HI1).
  - destruct HI1 as [HA1 _]. destruct (CH_bounds2 [] (ex ++ taken) (set_qglob rest bytes2 st) HA1) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia| lia].
    unfold qbatches. cbn [a_qloc a_qglob set_qglob]. rewrite Hql. cbn [app]. rewrite !bsum_app. subst gl. rewrite bsum_app in M3. lia.
  - intros st' mo' HI' HQ'. destruct HQ' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). cbn in Q1, Q2, Q3, Q4, Q5, Q6.
    apply Hk; auto; try congruence. rewrite Q6. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN. lia.
Qed.

#[using="Type"] Lemma bsum_nonneg : forall bs, Forall batch_wf bs -> 0 <= bsum bs.
Proof.
  induction bs as [|b bs IH]; intros HB; [cbn; lia|]. apply Forall_cons_iff in HB as [(B1&B2&B3&B4) HB]. cbn. specialize (IH HB).
  assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma drain_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc_bytes st + a_qglob_bytes st <= 2^30 ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MAX -> atot (k st') mo' P) ->
  atot (drain st k) mo P.
Proof.
  intros R P st k mo HI HQ Hk. pose proof HI as [HA HM]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
  unfold drain. cbv zeta. cbn [a_qglob a_qglob_bytes a_qloc a_qloc_bytes set_qloc].
  set (st1 := set_qglob (a_qglob st ++ a_qloc st) (a_qglob_bytes st + a_qloc_bytes st) (set_qloc [] 0 st)).
  assert (HI1 : INV [] [] st1 mo).
  { unfold st1. apply (INV_requeue [] [] [] st [] 0 _ _ mo HI).
    - unfold qbatches. cbn [app]. rewrite !qchunks_app. apply Permutation_app_comm.
    - unfold qbatches. cbn [app]. rewrite !zlen_app. lia.
    - unfold qbatches in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app; split; assumption.
    - reflexivity.
    - rewrite bsum_app. lia. }
  assert (HBq : 0 <= bsum (a_qglob st) /\ 0 <= bsum (a_qloc st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  change (a_qglob_bytes st1) with (a_qglob_bytes st + a_qloc_bytes st).
  destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st + a_qloc_bytes st)) as [Hbig|Hsmall].
  - apply (recycle_ok R P st1 k mo HI1); try reflexivity.
    + unfold st1. cbn. rewrite bsum_app. lia.
    + intros st' mo' HI' E1 E2 E3 E4 E5. apply Hk; auto. unfold Q_MIN, Q_MAX in *. lia.
  - apply Hk; auto; unfold st1; cbn; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma is_primary_7000 : is_primary 7000 = true. Proof. reflexivity. Qed.

#[using="Type"] Lemma enqueue_ok : forall R (P : R -> Model -> Prop) st ch n (k : astate -> AM R) mo,
  INV [ch] [] st mo -> chunk_size ch = n -> 0 <= n <= Q_MAX ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st ->
     a_qglob_bytes st' = a_qglob_bytes st ->
     a_qloc_bytes st <= a_qloc_bytes st' <= a_qloc_bytes st + n + Q_BATCH_BYTES -> atot (k st') mo' P) ->
  atot (enqueue st ch k) mo P.
Proof.
  intros R P st ch n k mo HI Hsz Hn Hql Hqg Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf HW].
  assert (Hchsz : Forall (fun c => 0 <= chunk_size c <= Q_MAX) [ch]) by (constructor; [rewrite Hsz; lia| constructor]).
  (* [comment removed for export] *)
  assert (NEWB : forall st0, INV [ch] [] st0 mo -> a_live st0 = a_live st -> a_next st0 = a_next st -> a_qloc st0 = a_qloc st -> a_qloc_bytes st0 = a_qloc_bytes st ->
            a_qglob st0 = a_qglob st -> a_qglob_bytes st0 = a_qglob_bytes st ->
            atot (cache_alloc st0 K_BATCH_CLASS (fun st1 ok =>
                     if negb ok then aundef_ USpin (k st1)
                     else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (n + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1))) mo P).
  { intros st0 HI0 E1 E2 E3 E4 E5 E6. pose proof HI0 as [HA0 HM0].
    apply (cache_alloc_ok R P [ch] [] st0 K_BATCH_CLASS 7000 _ mo HI0 ltac:(lia) is_primary_7000 (eq_sym shell_class)).
    - apply (room_of_AINV (ATOP:=ATOP)); auto; [unfold K_BATCH_CLASS; lia | vm_compute; congruence | vm_compute; congruence | |].
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + change (size_of_class K_BATCH_CLASS) with 8192. rewrite cntP_cons, cntP_nil. destruct (is_prim_of K_BATCH_CLASS ch); lia.
    - destruct (CH_bounds [ch] [] st0 HA0) as [_ X]; [| | | lia].
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + destruct ch; cbn; unfold zlen; cbn; lia.
      + destruct ch; cbn in *; lia.
    - intros st1 mo1 HI1 HSB1. cbn [negb].
      assert (F : a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob st1 = a_qglob st /\ a_qglob_bytes st1 = a_qglob_bytes st).
      { destruct HSB1 as [X|X]; destruct X as (_&_&_&_&_&L1&L2&L3&L4&L5&L6&_); [| unfold init_cache in *; destruct (a_cinit st0); cbn in *]; repeat split; congruence. }
      destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
      apply Hk; [| cbn [a_live set_qloc]; congruence| cbn [a_next set_qloc]; congruence| cbn [a_qglob_bytes set_qloc]; congruence| cbn [a_qloc_bytes set_qloc]; rewrite F4; unfold Q_BATCH_BYTES; lia].
      (* [comment removed for export] *)
      set (nb := mkABatch 1 (n + Q_BATCH_BYTES) [ch]).
      assert (Hnb : batch_wf nb).
      { unfold batch_wf, nb. cbn. unfold zlen. cbn. rewrite Hsz. unfold Q_BATCH. repeat split; try lia. exact Hchsz. }
      assert (HI2 : INV [] [nb] st1 mo1).
      { apply INV_close_batch; [|exact Hnb]. unfold nb. cbn [b_chunks rev app]. apply (INV_pc_perm [shell; ch]); [apply perm_swap| exact HI1]. }
      replace (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)
        with (set_qglob (a_qglob st1) (a_qglob_bytes st1) (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)) by (destruct st1; reflexivity).
      apply (INV_requeue [] [nb] [] st1 _ _ _ _ mo1 HI2).
      + unfold qbatches. cbn [app]. rewrite !qchunks_app. cbn. fold (qchunks (a_qloc st1 ++ a_qglob st1)). rewrite qchunks_app.
        eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|]. cbn. apply Permutation_refl.
      + unfold qbatches. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      + destruct HI2 as [(_ & _ & HB2 & _) _]. unfold qbatches in HB2. cbn [app] in *. apply Forall_cons_iff in HB2 as [X Y]. apply Forall_app in Y as [Y1 Y2].
        apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
      + destruct HI2 as [(_ & _ & _ & B1 & _) _]. cbn in B1. rewrite bsum_app, <- B1. cbn. lia.
      + destruct HI2 as [(_ & _ & _ & _ & B2 & _) _]. exact B2. }
  unfold enqueue. rewrite Hsz. cbv zeta.
  destruct (rev (a_qloc st)) as [|b rl] eqn:Hrev.
  - apply NEWB; auto.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [|Hne]; [apply NEWB; auto|].
    (* [comment removed for export] *)
    assert (Hql' : a_qloc st = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc st)), Hrev; reflexivity).
    assert (Hb : batch_wf b).
    { unfold qbatches in HBW. rewrite Hql' in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X _]. apply Forall_app in X as [_ X]. apply Forall_cons_iff in X as [X _]. exact X. }
    set (b' := mkABatch (b_count b + 1) (b_size b + n) (ch :: b_chunks b)).
    assert (Hb' : batch_wf b').
    { destruct Hb as (B1&B2&B3&B4). unfold batch_wf, b'. cbn. rewrite zlen_cons, Hsz. repeat split; try lia. constructor; [rewrite Hsz; lia| exact B4]. }
    apply Hk; [| reflexivity| reflexivity| reflexivity| cbn [a_qloc_bytes set_qloc]; unfold Q_BATCH_BYTES; lia].
    (* [comment removed for export] *)
    assert (HI1 : INV [ch] [b] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply (INV_requeue [ch] [] [b] st); auto.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !qchunks_app. cbn. rewrite app_nil_r. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
        rewrite <- app_assoc. apply Permutation_app_swap_app.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      - unfold qbatches in *. rewrite Hql' in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app in X as [X1 X2]. apply Forall_cons_iff in X2 as [X2 _].
        constructor; [exact X2|]. apply Forall_app; split; assumption.
      - rewrite Hb1, Hql', bsum_app. cbn. lia. }
    pose proof (INV_open_batch _ _ _ _ _ HI1) as HI2.
    assert (HI3 : INV [] [b'] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply INV_close_batch; [|exact Hb']. unfold b'. cbn [b_chunks]. cbn [rev]. rewrite <- app_assoc. cbn [app].
      apply (INV_pc_perm (rev (b_chunks b) ++ [shell; ch])); [| exact HI2].
      apply Permutation_app_head. apply perm_swap. }
    replace (set_qloc (rev (b' :: rl)) (a_qloc_bytes st + n) st)
      with (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl ++ [b']) (a_qloc_bytes st - b_size b + b_size b') (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)))).
    2:{ destruct st; cbn. unfold b', set_qloc, set_qglob. cbn. f_equal. lia. }
    apply (INV_requeue [] [b'] [] _ _ _ _ _ mo HI3).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !qchunks_app. cbn. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
      rewrite app_nil_r. rewrite <- app_assoc. rewrite (app_comm_cons). apply (Permutation_app_swap_app (qchunks (rev rl)) (ch :: b_chunks b)).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
    + destruct HI3 as [(_ & _ & HB3 & _) _]. unfold qbatches in HB3 |- *. cbn [app a_qloc a_qglob set_qglob set_qloc] in *. apply Forall_cons_iff in HB3 as [X Y]. apply Forall_app in Y as [Y1 Y2].
      apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
    + rewrite Hb1, Hql'. rewrite !bsum_app. unfold b'. cbn [bsum b_size]. lia.
    + exact Hb2.
Qed.

#[using="Type"] Lemma size_of_class_nonneg : forall c, 1 <= c <= 31 -> 0 <= size_of_class c.
Proof.
  intros c Hc. destruct (Z_le_dec 3 c); [apply budget_chk_ok; lia|].
  assert (c = 1 \/ c = 2) as [-> | ->] by lia; [change (size_of_class 1) with 32| change (size_of_class 2) with 64]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_live_to_hand : forall st id ch mo,
  INV [] [] st mo -> (a_live st) !! id = Some ch ->
  INV [ch] [] (set_live (delete id (a_live st)) st) mo.
Proof.
  intros st id ch mo [HA HM] Hl. pose proof HA as (_ & HW0 & _).
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  assert (HPa : Permutation (all_chunks [ch] [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) (all_chunks [] [] st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) with (qbatches [] st).
    eapply Permutation_trans. 2:{ apply Permutation_app_tail. apply Permutation_sym. exact HPl. } cbn. apply Permutation_refl. }
  assert (E : set_live (delete id (a_live st)) st = set_next (a_next st) (set_live (delete id (a_live st)) st)) by (destruct st; reflexivity).
  rewrite E. split.
  - apply (AINV_live_perm []); auto.
    + intros id' ch' Hl'. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). apply (Hid id' ch').
      destruct (N.eq_dec id' id) as [->|Hne]; [rewrite lookup_delete_eq in Hl'; discriminate|]. rewrite lookup_delete_ne in Hl' by congruence. exact Hl'.
    + destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB). apply live_budget_list_iff in HLB. apply live_budget_list_iff.
      unfold live_chunks in *. cbn [a_live set_next set_live] in *.
      destruct HLB as (B1 & B2 & B3). unfold live_chunks in B1, B2, B3 |- *. cbn [a_live set_next set_live] in B1, B2, B3 |- *. split; [|split].
      * intros c Hc. specialize (B1 c Hc). rewrite (cntP_perm c _ _ HPl), cntP_cons in B1. pose proof (cntP_nonneg c (map snd (map_to_list (delete id (a_live st))))).
        pose proof (size_of_class_nonneg c Hc). destruct (is_prim_of c ch); nia.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)) in B2. rewrite secs_cons, length_app in B2. lia.
      * assert (EB : forall l l', Permutation l l' -> secbytes l = secbytes l') by (intros l l' P0; induction P0; cbn; try lia; [destruct x; lia| destruct x, y; lia]).
        rewrite (EB _ _ HPl) in B3. cbn in B3. destruct ch; cbn in B3; try lia.
        unfold all_chunks, live_chunks in HW0. cbn [app] in HW0. apply Forall_app in HW0 as [HW0 _].
        pose proof (Permutation_Forall HPl HW0) as X. apply Forall_cons_iff in X as [X _]. cbn in X. lia.
  - apply (AMI_perm (CH [] [] st)).
    + unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
    + apply (AMI_mono _ st); auto. unfold commit_bytes, csum, get_cls. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition free_post (st : astate) (id : AsanCtrl.aptr) (st' : astate) (mo' : Model) : Prop :=
  INV [] [] st' mo' /\ a_live st' = delete id (a_live st) /\ a_next st' = a_next st
  /\ a_qloc_bytes st' <= Q_CACHE /\ a_qglob_bytes st' <= Q_MAX.

#[using="Type"] Theorem afree_core : forall st mo id ch,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> (a_live st) !! id = Some ch ->
  atot (afree st (Some id)) mo (free_post st id).
Proof.
  intros st mo id ch HI Hql Hqg Hl.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  pose proof (INV_live_to_hand st id ch mo HI Hl) as HI1.
  set (st1 := set_live (delete id (a_live st)) st) in *.
  assert (Hwf : chunk_wf ch).
  { destruct HI1 as [HA1 _]. destruct HA1 as (_ & HW1 & _). rewrite all_chunks_cons in HW1. apply Forall_cons_iff in HW1 as [X _]. exact X. }
  assert (Hszb : 0 <= chunk_size ch <= 2^30) by (destruct ch; cbn in Hwf |- *; lia).
  assert (HQB : 0 <= bsum (a_qloc st) /\ 0 <= bsum (a_qglob st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  unfold afree. rewrite Hl. fold st1. cbv zeta.
  (* [comment removed for export] *)
  assert (AFTER : forall st2 mo2, INV [] [] st2 mo2 -> a_live st2 = a_live st1 -> a_next st2 = a_next st1 ->
            0 <= a_qloc_bytes st2 -> a_qloc_bytes st2 + a_qglob_bytes st2 <= 2^30 -> a_qglob_bytes st2 <= Q_MAX ->
            atot (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2) mo2 (free_post st id)).
  { intros st2 mo2 HI2 E1 E2 Hq0 Hq1 Hq2. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [Hbig|Hsmall].
    - apply (drain_ok _ _ st2 _ mo2 HI2 Hq1). intros st3 mo3 HI3 F1 F2 F3 F4 F5. apply atotal_ret. unfold free_post.
      rewrite F1, F2, E1, E2, F4. unfold st1. cbn. unfold Q_CACHE. split; [exact HI3|]. split; [reflexivity|]. split; [reflexivity|]. lia.
    - apply atotal_ret. unfold free_post. rewrite E1, E2. unfold st1. cbn. split; [exact HI2|]. split; [reflexivity|]. split; [reflexivity|]. lia. }
  destruct (Z.leb_spec (chunk_size ch) Q_MAX) as [Hsmall|Hbig].
  - (* [comment removed for export] *)
    apply (enqueue_ok _ _ st1 ch (chunk_size ch) _ mo HI1 eq_refl ltac:(lia)); try (unfold st1; cbn; assumption).
    intros st2 mo2 HI2 E1 E2 E3 E4. unfold st1 in E1, E2, E3, E4. cbn [a_live a_next a_qglob_bytes a_qloc_bytes set_live] in E1, E2, E3, E4.
    apply AFTER; auto; rewrite <- ?Hb1 in E4; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *; lia.
  - (* [comment removed for export] *)
    apply (recycle_chunk_ok _ _ [] [] st1 ch _ mo HI1).
    + destruct HI1 as [HA1 _]. enough (X : zsum2 (CH [ch] [] st1) <= 2^34) by lia. apply (CH_bounds (ATOP:=ATOP)); auto.
      * unfold qbatches, st1. cbn [app a_qloc a_qglob set_live]. rewrite bsum_app. unfold Q_CACHE, Q_MAX in *. lia.
      * destruct ch; cbn; unfold zlen; cbn; lia.
      * destruct ch; cbn in *; lia.
    + intros st2 mo2 HI2 HQ. destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). unfold st1 in Q1, Q2, Q3, Q4, Q5, Q6. cbn [a_live a_next a_qglob_bytes a_qloc_bytes a_qloc a_qglob set_live] in Q1, Q2, Q3, Q4, Q5, Q6.
      apply AFTER; auto; rewrite ?Q4, ?Q6; unfold Q_CACHE, Q_MAX in *; lia.
Qed.

End WithResv.
End AsanFree.

(* [comment removed for export] *)
Module ATsafeEv.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanInv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanFree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Ev.
Variables (SB PA : Z).    (* [comment removed for export] *)

Definition inAP (a n : Z) : Prop :=
  (SB <= a /\ a + n <= SB + K_SPACE_SIZE) \/ (PA <= a /\ a + n <= PA + K_PTRARR_RESERVE).

(* [comment removed for export] *)
Definition covG (G : list (Z * Z)) (a n : Z) : Prop :=
  exists g, In g G /\ 0 <= fst g /\ shad (fst g) <= a /\ a + n <= shad (fst g + snd g).

#[using="Type"] Lemma covG_mono : forall G G' a n, covG G a n -> incl G G' -> covG G' a n.
Proof. intros G G' a n (g & Hin & H) HI. exists g. split; [apply HI; exact Hin| exact H]. Qed.

Fixpoint evq {R} (RP : list (Z * Z) -> R -> Prop) (ga : list Z) (G : list (Z * Z)) (b : Z) (t : AM R) {struct t} : Prop :=
  match t with
  | SRet r => RP G r
  | SVis e k =>
    match e with
    | AUndef _ => True
    | AMmap a len prot flags =>
        prot = PROT_RW /\ 0 < len /\ len mod 4096 = 0 /\
        ((flags = F_ANON /\ a = 0 /\
            match ga with
            | l0 :: ga' => len = l0 /\ len <= b /\ forall z, evq RP ga' ((z, len) :: G) (if is_err z then b else b - len) (k z)
            | [] => False
            end)
         \/ (flags = F_FIXED /\ inAP a len /\ len <= b /\ forall z, evq RP ga G (if is_err z then b else b - len) (k z))
         \/ (flags = F_FIXNORES /\ covG G a len /\ forall z, evq RP ga G b (k z)))
    | AMunmap a len => forall z, evq RP ga G b (k z)
    | _ => False
    end
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma evq_mono : forall {R} (RP RP' : list (Z * Z) -> R -> Prop) (t : AM R) ga G G' b b',
  evq RP ga G b t -> incl G G' -> b <= b' ->
  (forall G1 G1' r, incl G1 G1' -> RP G1 r -> RP' G1' r) ->
  evq RP' ga G' b' t.
Proof.
  intros R RP RP' t. induction t as [r|e k IH]; intros ga G G' b b' H HI Hb HRP; cbn in H |- *.
  - eapply HRP; [exact HI| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact (H z)| | destruct (is_err z); lia| exact HRP].
        intros g [<-|Hg]; [left; reflexivity| right; apply HI; exact Hg].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| exact HI| destruct (is_err z); lia| exact HRP].
      * right; right. split; [exact Hf|]. split; [eapply covG_mono; eauto|]. intros z. eapply IH; [exact (H z)| exact HI| lia| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact HI| exact Hb| exact HRP].
Qed.

#[using="Type"] Lemma evq_mono_b : forall {R} (RP : list (Z * Z) -> R -> Prop) (t : AM R) ga G b b',
  evq RP ga G b t -> b <= b' -> evq RP ga G b' t.
Proof.
  intros R RP t. induction t as [r|e k IH]; intros ga G b b' H Hb; cbn in H |- *.
  - exact H.
  - destruct e as [t0|b0|a len prot flags|a len|a l p|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact (H z)| destruct (is_err z); lia].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| destruct (is_err z); lia].
      * right; right. split; [exact Hf|]. split; [exact Hc|]. intros z. eapply IH; [exact (H z)| lia].
    + intros z. eapply IH; [exact (H z)| exact Hb].
Qed.

#[using="Type"] Lemma evq_aundef : forall {R} RP ga G b w (k : AM R), evq RP ga G b (aundef_ w k).
Proof. intros. cbn. exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chunk_ok (G : list (Z * Z)) (ch : achunk) : Prop :=
  match ch with
  | CPrim c _ => 1 <= c <= 31
  | CSec mb ms n => In (mb, ms) G /\ 0 < mb /\ 0 <= n /\ PG + rz_size n + n <= ms
  end.

#[using="Type"] Lemma chunk_ok_mono : forall G G' ch, chunk_ok G ch -> incl G G' -> chunk_ok G' ch.
Proof. intros G G' [c n|mb ms n] H HI; cbn in *; [exact H|]. destruct H as (H1 & H2). split; [apply HI; exact H1| exact H2]. Qed.

#[using="Type"] Lemma Forall_chunk_ok_mono : forall G G' l, Forall (chunk_ok G) l -> incl G G' -> Forall (chunk_ok G') l.
Proof. intros G G' l H HI. eapply Forall_impl; [|exact H]. intros ch Hc. eapply chunk_ok_mono; eauto. Qed.

Definition CBM : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + K_PTRARR_RESERVE.

Definition cls_lw (r : aclass) : Prop :=
  0 <= c_mapped_user r <= K_FREEARR_OFF /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0.
Definition LW (st : astate) : Prop :=
  a_space_beg st = SB /\ a_ptr_array st = PA /\ 0 <= a_nres st /\ 8 * a_nres st <= K_PTRARR_RESERVE
  /\ forall c, 1 <= c <= 31 -> cls_lw (get_cls st c).

(* [comment removed for export] *)
Definition PHI (st : astate) : Z := CBM - commit_bytes st.

#[using="Type"] Lemma commit_bytes_LW : forall st, LW st -> 0 <= commit_bytes st <= CBM.
Proof.
  intros st (_ & _ & N0 & N1 & HC). unfold commit_bytes, CBM.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX) ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  pose proof (csum_nonneg cls_mapped_bytes' st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  lia.
Qed.
#[using="Type"] Lemma PHI_nonneg : forall st, LW st -> 0 <= PHI st.
Proof. intros st H. pose proof (commit_bytes_LW st H). unfold PHI. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma LW_put : forall st c r, LW st -> 1 <= c <= 31 -> cls_lw r -> LW (put_cls c r st).
Proof.
  intros st c r (S1 & S2 & N0 & N1 & HC) Hc Hr. unfold LW. cbn [a_space_beg a_ptr_array a_nres put_cls set_cls].
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
  - rewrite get_put_eq. exact Hr.
  - rewrite get_put_ne by exact NE. apply HC. exact Hc'.
Qed.
#[using="Type"] Lemma LW_cls : forall st c, LW st -> 1 <= c <= 31 -> cls_lw (get_cls st c).
Proof. intros st c (_ & _ & _ & _ & HC) Hc. apply HC. exact Hc. Qed.
#[using="Type"] Lemma LW_init_cache : forall st, LW st -> LW (init_cache st).
Proof. intros st H. unfold init_cache. destruct (a_cinit st); [exact H|]. exact H. Qed.
#[using="Type"] Lemma LW_set_nsec : forall v st, LW st -> LW (set_nsec v st). Proof. intros v st H. exact H. Qed.
#[using="Type"] Lemma LW_set_live : forall v st, LW st -> LW (set_live v st). Proof. intros v st H. exact H. Qed.
#[using="Type"] Lemma LW_set_next : forall v st, LW st -> LW (set_next v st). Proof. intros v st H. exact H. Qed.
#[using="Type"] Lemma LW_set_qloc : forall l b st, LW st -> LW (set_qloc l b st). Proof. intros l b st H. exact H. Qed.
#[using="Type"] Lemma LW_set_qglob : forall l b st, LW st -> LW (set_qglob l b st). Proof. intros l b st H. exact H. Qed.

#[using="Type"] Lemma PHI_put : forall st c r, 1 <= c <= 31 ->
  PHI (put_cls c r st) = PHI st + cls_mapped_bytes' (get_cls st c) - cls_mapped_bytes' r.
Proof. intros. unfold PHI. rewrite commit_bytes_put by assumption. lia. Qed.
#[using="Type"] Lemma PHI_init_cache : forall st, PHI (init_cache st) = PHI st.
Proof. intros. unfold PHI. rewrite commit_bytes_init_cache. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_nsec : forall v st, PHI (set_nsec v st) = PHI st. Proof. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_live : forall v st, PHI (set_live v st) = PHI st. Proof. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_next : forall v st, PHI (set_next v st) = PHI st. Proof. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_qloc : forall l b st, PHI (set_qloc l b st) = PHI st. Proof. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_qglob : forall l b st, PHI (set_qglob l b st) = PHI st. Proof. reflexivity. Qed.
#[using="Type"] Lemma PHI_set_nres : forall v st, PHI (set_nres v st) = PHI st - 8 * (v - a_nres st).
Proof. intros. unfold PHI, commit_bytes. cbn [a_nres set_nres]. unfold csum. rewrite (fold_csum_ext cls_mapped_bytes' st (set_nres v st)) by (intros; reflexivity). lia. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma all_chunks_same_but : forall c st st', same_but c st st' -> all_chunks [] [] st' = all_chunks [] [] st.
Proof.
  intros c st st' (_&_&_&_&_&HL&_&HQ1&_&HQ2&_&_). unfold all_chunks, live_chunks, qbatches. rewrite HL, HQ1, HQ2. reflexivity.
Qed.
#[using="Type"] Lemma LW_same_but : forall c st st', same_but c st st' -> LW st -> cls_lw (get_cls st' c) -> LW st'.
Proof.
  intros c st st' (E1&E2&E3&_&_&_&_&_&_&_&_&HG) (S1 & S2 & N0 & N1 & HC) Hc'. unfold LW. rewrite E1, E2, E3.
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hr. destruct (Z.eq_dec c' c) as [->|NE]; [exact Hc'|]. rewrite HG by exact NE. apply HC. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mod_sub_mult : forall x y m, 0 < m -> x mod m = 0 -> y mod m = 0 -> (x - y) mod m = 0.
Proof.
  intros x y m Hm Hx Hy. rewrite Zminus_mod, Hx, Hy. reflexivity.
Qed.

#[using="Type"] Lemma evq_poison0 : forall {R} RP ga G b (k : AM R) addr size g,
  In g G -> 0 <= fst g -> fst g <= addr -> 0 <= size -> addr + size <= fst g + snd g ->
  evq RP ga G b k -> evq RP ga G b (poison0 addr size k).
Proof.
  intros R RP ga G b k addr size g Hg Hg0 Ha Hs Hhi Hk. unfold poison0. exact Hk.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma region_in_arena : forall st c x y, LW st -> 1 <= c <= 31 -> 0 <= x -> 0 <= y -> x + y <= K_REGION ->
  inAP (region_beg st c + x) y.
Proof.
  intros st c x y (S1 & _) Hc Hx Hy Hxy. left. unfold region_beg. rewrite S1. unfold K_REGION, K_SPACE_SIZE in *. nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evq_ensure_free_array : forall {R} RP ga G st c nf (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (ensure_free_array st c nf k).
Proof.
  intros R RP ga G st c nf k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold ensure_free_array.
  destruct (nf * 4 <=? _) eqn:E1. { apply (Hk st true HL (same_but_refl c st)). lia. }
  destruct (K_FREEARR_MAX <? _) eqn:E2. { apply evq_aundef. }
  apply Z.leb_gt in E1. apply Z.ltb_ge in E2. assert (Hnf : 0 <= nf) by lia.
  pose proof (rup_freearr_bounds (nf * 4) ltac:(lia)) as RB.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RM.
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RG.
  set (nm := rup (nf * 4) K_FREEARR_MAP) in *.
  assert (D : (4096 | K_FREEARR_MAP)) by (exists 64; reflexivity).
  cbn -[evq Z.sub Z.add Z.mul rup region_beg K_FREEARR_OFF nm get_cls put_cls cls_set_mapped_free_array fixed_answer_ok is_err PHI].
  split; [reflexivity|]. split; [lia|]. split.
  { assert (M1 : nm mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod nm K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact RM]).
    assert (M2 : c_mapped_free_array (get_cls st c) mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod _ K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact F2]).
    apply mod_sub_mult; [lia| exact M1| exact M2]. }
  right; left. split; [reflexivity|]. split.
  { replace (region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)) with (region_beg st c + (K_FREEARR_OFF + c_mapped_free_array (get_cls st c))) by lia.
    apply (region_in_arena st c); auto; unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; lia. }
  set (r' := cls_set_mapped_free_array nm (get_cls st c)).
  assert (Hr' : cls_lw r') by (unfold r', cls_lw; cbn; lia).
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - (nm - c_mapped_free_array (get_cls st c)))
    by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)). lia.
  - replace (PHI st + extra - (nm - c_mapped_free_array (get_cls st c))) with (PHI (put_cls c r' st) + extra) by lia.
    apply Hk; [exact HL'| apply same_but_put| lia].
Qed.

#[using="Type"] Lemma evq_populate : forall {R} RP ga G st c req (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (populate_free_array st c req k).
Proof.
  intros R RP ga G st c req k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold populate_free_array. cbv zeta.
  (* [comment removed for export] *)
  assert (AFTER : forall st1, LW st1 -> same_but c st st1 -> PHI st1 <= PHI st ->
    evq RP ga G (PHI st1 + extra)
      (ensure_free_array st1 c (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c)
         (fun st2 ok => if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c * size_of_class c)
                            (cls_set_num_freed (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c) (get_cls st2 c))) st2) true))).
  { intros st1 HL1 HS1 HP1. apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HS2 HP2. destruct ok; cbn [negb].
    - set (r3 := cls_set_allocated_user _ (cls_set_num_freed _ (get_cls st2 c))).
      assert (Hr3 : cls_lw r3) by (pose proof (LW_cls st2 c HL2 Hc) as X; unfold r3, cls_lw in *; cbn; exact X).
      replace (PHI st2 + extra) with (PHI (put_cls c r3 st2) + extra) by (rewrite PHI_put by exact Hc; unfold r3, cls_mapped_bytes'; cbn; lia).
      apply Hk; [apply LW_put; auto| eapply same_but_trans; [eapply same_but_trans; [exact HS1| exact HS2]| apply same_but_put]|].
      rewrite PHI_put by exact Hc. unfold r3, cls_mapped_bytes'; cbn. lia.
    - apply Hk; [exact HL2| eapply same_but_trans; [exact HS1| exact HS2]| lia]. }
  destruct (_ <=? c_mapped_user (get_cls st c)) eqn:E1. { apply AFTER; [exact HL| apply same_but_refl| lia]. }
  apply Z.leb_gt in E1.
  set (ums := rup _ K_USER_MAP).
  destruct (K_FREEARR_OFF <? _) eqn:E2. { apply evq_aundef. }
  apply Z.ltb_ge in E2.
  pose proof (rup_ge (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RG. fold ums in RG.
  pose proof (rup_mod (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RM. fold ums in RM.
  assert (D : (4096 | K_USER_MAP)) by (exists 64; reflexivity).
  set (r' := cls_set_mapped_user (c_mapped_user (get_cls st c) + ums) (get_cls st c)).
  assert (Hr' : cls_lw r').
  { unfold r', cls_lw; cbn. split; [lia|]. split; [| split; [exact F1| exact F2]].
    rewrite Z.add_mod, U2, RM by (unfold K_USER_MAP; lia). reflexivity. }
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - ums) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  cbn -[evq Z.sub Z.add Z.mul Z.div rup region_beg K_FREEARR_OFF ums get_cls put_cls cls_set_mapped_user cls_set_allocated_user cls_set_num_freed
        fixed_answer_ok is_err PHI ensure_free_array size_of_class].
  split; [reflexivity|]. split; [lia|]. split.
  { apply Znumtheory.Zdivide_mod. apply (div4096_of_mod ums K_USER_MAP); [exact D| unfold K_USER_MAP; lia| exact RM]. }
  right; left. split; [reflexivity|]. split.
  { apply (region_in_arena st c); auto; try lia. unfold K_FREEARR_OFF, K_REGION in *. lia. }
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)). lia.
  - replace (PHI st + extra - ums) with (PHI (put_cls c r' st) + extra) by lia.
    apply AFTER; [exact HL'| apply same_but_put| lia].
Qed.

(* [comment removed for export] *)
Definition frq (st st' : astate) : Prop :=
  a_live st' = a_live st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st /\ a_next st' = a_next st.
#[using="Type"] Lemma frq_refl : forall st, frq st st. Proof. intros. unfold frq. auto. Qed.
#[using="Type"] Lemma frq_trans : forall a b c, frq a b -> frq b c -> frq a c.
Proof. intros a b c (A1&A2&A3&A4) (B1&B2&B3&B4). unfold frq. rewrite B1, B2, B3, B4. auto. Qed.
#[using="Type"] Lemma frq_same_but : forall c st st', same_but c st st' -> frq st st'.
Proof. intros c st st' (_&_&_&_&_&HL&HN&HQ1&_&HQ2&_&_). unfold frq. auto. Qed.
#[using="Type"] Lemma frq_init_cache : forall st, frq st (init_cache st).
Proof. intros. unfold init_cache. destruct (a_cinit st); [apply frq_refl|]. unfold frq. auto. Qed.
#[using="Type"] Lemma frq_put : forall st c r, frq st (put_cls c r st). Proof. intros. unfold frq. auto. Qed.
#[using="Type"] Lemma all_chunks_frq : forall st st', frq st st' -> all_chunks [] [] st' = all_chunks [] [] st.
Proof. intros st st' (A&B&C&_). unfold all_chunks, live_chunks, qbatches. rewrite A, B, C. reflexivity. Qed.

#[using="Type"] Lemma evq_cache_alloc : forall {R} RP ga G st c (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (cache_alloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex Hk. unfold cache_alloc. cbv zeta.
  destruct (0 <? _).
  { set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st c HL Hc) as X; exact X).
    replace (PHI st + extra) with (PHI (put_cls c r' st) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| apply frq_put| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia]. }
  pose proof (LW_init_cache st HL) as HL1.
  assert (TAKE : forall st2, LW st2 -> frq st st2 -> PHI st2 <= PHI st ->
    evq RP ga G (PHI st2 + extra)
      (if c_num_freed (get_cls st2 c) <? max_count (init_cache st) c / 2 then aundef_ (UCheck 229) (k st2 false)
       else k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)).
  { intros st2 HL2 HF2 HP2. destruct (_ <? _); [apply evq_aundef|].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [exact HF2| apply frq_put]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia]. }
  destruct (_ <=? _).
  - rewrite <- (PHI_init_cache st). apply TAKE; [exact HL1| apply frq_init_cache| rewrite PHI_init_cache; lia].
  - rewrite <- (PHI_init_cache st). apply evq_populate; auto.
    intros st2 ok HL2 HS2 HP2. rewrite PHI_init_cache in HP2. destruct ok.
    + apply TAKE; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2].
    + apply Hk; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2].
Qed.

#[using="Type"] Lemma evq_cache_dealloc : forall {R} RP ga G st c (k : astate -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (cache_dealloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex Hk. unfold cache_dealloc. cbv zeta.
  pose proof (LW_init_cache st HL) as HL1.
  destruct (_ =? _).
  - rewrite <- (PHI_init_cache st). apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HS2 HP2. rewrite PHI_init_cache in HP2. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| eapply frq_trans; [eapply frq_same_but; exact HS2| apply frq_put]]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia].
  - set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls (init_cache st) c HL1 Hc) as X; exact X).
    replace (PHI st + extra) with (PHI (put_cls c r' (init_cache st)) + extra) by (rewrite PHI_put by exact Hc; rewrite PHI_init_cache; unfold r', cls_mapped_bytes'; cbn; rewrite get_cls_init_cache; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| apply frq_put]|].
    rewrite PHI_put by exact Hc. rewrite PHI_init_cache. unfold r', cls_mapped_bytes'; cbn. rewrite get_cls_init_cache. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma land_lnot7 : forall n, 0 <= n -> 0 <= Z.land n (Z.lnot 7) <= n.
Proof.
  intros n Hn. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma rz_size_large : forall n, 64512 < n -> rz_size n = 2048.
Proof. intros. unfold rz_size, rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. Qed.
#[using="Type"] Lemma sec_map_size_mod : forall n, sec_map_size n mod 4096 = 0.
Proof. intros. unfold sec_map_size. rewrite Z.add_mod, rup_mod by (unfold PG; lia). reflexivity. Qed.

#[using="Type"] Lemma evq_large_alloc : forall {R} RESV RP G st n (k : astate -> option achunk -> AM R),
  LW st -> 64512 < n <= 2^40 ->
  (forall G' st' och, incl G G' -> LW st' -> frq st st' -> PHI st' <= PHI st ->
     (forall ch, och = Some ch -> chunk_ok G' ch /\ ch = CSec (match ch with CSec mb _ _ => mb | _ => 0 end) (sec_map_size n) n) ->
     evq RP [] G' (PHI st' + 0) (k st' och)) ->
  evq RP [sec_map_size n] G (PHI st + sec_map_size n) (large_alloc ATOP RESV st n k).
Proof.
  intros R RESV RP G st n k HL Hn Hk. pose proof HL as (S1 & S2 & N0 & N1 & HC).
  pose proof (sec_map_size_ge n ltac:(lia)) as SG. pose proof (rz_size_large n ltac:(lia)) as RZ.
  pose proof (PHI_nonneg st HL) as P0.
  unfold large_alloc. cbv zeta. cbn [evq ev].
  split; [reflexivity|]. split; [lia|]. split; [apply sec_map_size_mod|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP _ z)) eqn:E0; [apply evq_aundef|].
  destruct (is_err z) eqn:E1.
  { eapply evq_mono_b; [apply (Hk ((z, sec_map_size n) :: G) st None); auto| lia].
    - intros g Hg; right; exact Hg. - apply frq_refl. - lia. - intros ch H; discriminate. }
  assert (Hz : 0 < z). { unfold mmap_answer_ok in E0. rewrite E1 in E0. cbn [orb] in E0. apply Bool.negb_false_iff in E0.
                         repeat (apply andb_prop in E0 as [E0 ?]). apply Z.ltb_lt in E0. exact E0. }
  destruct (negb (avoids_all z (sec_map_size n) (RESV ++ asec_ranges st))) eqn:E2; [apply evq_aundef|].
  set (ch := CSec z (sec_map_size n) n).
  assert (CH : forall G', In (z, sec_map_size n) G' -> chunk_ok G' ch /\ ch = CSec z (sec_map_size n) n).
  { intros G' HinG. split; [|reflexivity]. unfold ch, chunk_ok. split; [exact HinG|]. split; [lia|]. split; [lia|]. rewrite RZ. unfold PG. lia. }
  destruct (a_nsec st =? a_nres st).
  - destruct (K_PTRARR_RESERVE <? _) eqn:E3; [apply evq_aundef|]. apply Z.ltb_ge in E3.
    cbn [evq ev].
    split; [reflexivity|]. split; [unfold K_PTRARR_COMMIT; lia|]. split; [reflexivity|].
    right; left. split; [reflexivity|]. split.
    { right. rewrite S2. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *. lia. }
    assert (EPn : PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) = PHI st - K_PTRARR_COMMIT).
    { rewrite PHI_set_nres. cbn [a_nres set_nsec]. rewrite PHI_set_nsec. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK. lia. }
    assert (HLn : LW (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))).
    { unfold LW. cbn [a_space_beg a_ptr_array a_nres set_nres set_nsec]. split; [exact S1|]. split; [exact S2|].
      split; [unfold K_CHUNKS_BLOCK; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|]. intros c Hc. apply HC. exact Hc. }
    pose proof (PHI_nonneg _ HLn). split; [lia|].
    intros r. destruct (negb (fixed_answer_ok _ r)); [apply evq_aundef|]. destruct (is_err r); [apply evq_aundef|].
    replace (PHI st + sec_map_size n - sec_map_size n - K_PTRARR_COMMIT) with (PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + 0) by lia.
    apply Hk; [intros g Hg; right; exact Hg| exact HLn| unfold frq; auto| rewrite EPn; unfold K_PTRARR_COMMIT; lia|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
  - replace (PHI st + sec_map_size n - sec_map_size n) with (PHI (set_nsec (a_nsec st + 1) st) + 0) by (rewrite PHI_set_nsec; lia).
    apply Hk; [intros g Hg; right; exact Hg| apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
Qed.

#[using="Type"] Lemma evq_large_dealloc : forall {R} RP ga G st mb ms n (k : astate -> AM R) extra,
  LW st -> chunk_ok G (CSec mb ms n) ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (large_dealloc st mb ms k).
Proof.
  intros R RP ga G st mb ms n k extra HL (Hin & Hmb & Hn & Hms) Hk. unfold large_dealloc. cbv zeta.
  pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply (evq_poison0 RP ga G _ _ mb ms (mb, ms)); auto; cbn [fst snd]; try lia. { unfold PG in Hms. lia. }
  cbn. intros z. destruct (z =? 0).
  - replace (PHI st + extra) with (PHI (set_nsec (a_nsec st - 1) st) + extra) by (rewrite PHI_set_nsec; lia).
    apply Hk; [apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia].
  - destruct (is_err z); apply evq_aundef.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RPst (G : list (Z * Z)) (st' : astate) : Prop := LW st' /\ Forall (chunk_ok G) (all_chunks [] [] st').
Definition RPm (G : list (Z * Z)) (r : astate * option AsanCtrl.aptr) : Prop := let (st', _) := r in RPst G st'.

#[using="Type"] Lemma all_chunks_live_insert : forall G st id ch,
  (a_live st) !! id = None -> chunk_ok G ch -> Forall (chunk_ok G) (all_chunks [] [] st) ->
  Forall (chunk_ok G) (all_chunks [] [] (set_live (<[id := ch]> (a_live st)) st)).
Proof.
  intros G st id ch Hn Hch HF. unfold all_chunks in *. cbn [app] in *.
  apply Forall_app in HF as [HF1 HF2]. apply Forall_app. split.
  - eapply Permutation_Forall; [apply Permutation_sym; apply live_chunks_insert; exact Hn|]. constructor; assumption.
  - unfold qbatches in *. cbn [app a_qloc a_qglob set_live] in *. exact HF2.
Qed.

(* [comment removed for export] *)
Definition next_fresh (st : astate) : Prop := forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N.

#[using="Type"] Lemma evq_amalloc : forall RESV G st n,
  LW st -> Forall (chunk_ok G) (all_chunks [] [] st) -> next_fresh st -> 0 <= n ->
  evq RPm (if is_primary n then [] else [sec_map_size n]) G (PHI st + (if is_primary n then 0 else sec_map_size n)) (amalloc ATOP RESV st n).
Proof.
  intros RESV G st n HL HF HNF Hn. unfold amalloc. cbv zeta.
  destruct (_ || _) eqn:E0.
  { unfold RPm, RPst. split; [exact HL| exact HF]. }
  apply Bool.orb_false_iff in E0 as [E0a E0b]. apply Z.ltb_ge in E0a. apply Z.ltb_ge in E0b.
  (* [comment removed for export] *)
  assert (FIN : forall G' st1 ch b, incl G G' -> LW st1 -> frq st st1 -> chunk_ok G' ch ->
            (forall mb ms n0, ch = CSec mb ms n0 -> n0 = n) ->
            evq RPm [] G' b
              (match ch with
               | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))
               | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1)))
               end)).
  { intros G' st1 ch b HI HL1 HF1 Hch Hchn.
    assert (HNF1 : (a_live st1) !! (a_next st1) = None).
    { destruct HF1 as (EL & _ & _ & EN). destruct ((a_live st1) !! (a_next st1)) as [c0|] eqn:E; [|reflexivity].
      exfalso. rewrite EL, EN in E. pose proof (HNF _ _ E). lia. }
    assert (POST : RPm G' (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))).
    { unfold RPm, RPst. split; [apply LW_set_next, LW_set_live; exact HL1|].
      unfold all_chunks. cbn [app]. apply all_chunks_live_insert; [exact HNF1| exact Hch|].
      rewrite (all_chunks_frq st st1 HF1). eapply Forall_chunk_ok_mono; eauto. }
    destruct ch as [c0 n0|mb ms n0]; [exact POST|].
    cbn in Hch. destruct Hch as (Hin & Hmb & Hn0 & Hms). specialize (Hchn mb ms n0 eq_refl). subst n0.
    pose proof (land_lnot7 n Hn) as LN. pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
    apply (evq_poison0 RPm [] G' b _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia. }
  destruct (is_primary n) eqn:EP.
  - rewrite Z.add_0_r. replace (PHI st) with (PHI st + 0) by lia.
    pose proof (primary_class_facts n Hn EP) as (C1 & _).
    apply evq_cache_alloc; [exact HL| lia| lia|]. intros st1 ok HL1 HF1 HP1. destruct ok.
    + apply (FIN G st1 (CPrim (class_id (needed_size n)) n)); auto. { apply incl_refl. } { cbn. lia. } { intros; discriminate. }
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). exact HF.
  - pose proof (not_primary_large n Hn EP) as NL.
    apply evq_large_alloc; [exact HL| lia|]. intros G' st1 och HI HL1 HF1 HP1 HCH. destruct och as [ch|].
    + destruct (HCH ch eq_refl) as [Hch Ech]. apply (FIN G' st1 ch); auto. intros mb ms n0 E. rewrite E in Ech. congruence.
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). eapply Forall_chunk_ok_mono; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition QOK (G : list (Z * Z)) (st : astate) : Prop := Forall (chunk_ok G) (all_chunks [] [] st).

#[using="Type"] Lemma QOK_frq : forall G st st', frq st st' -> QOK G st -> QOK G st'.
Proof. intros G st st' HF H. unfold QOK. rewrite (all_chunks_frq st st' HF). exact H. Qed.
#[using="Type"] Lemma QOK_mono : forall G G' st, QOK G st -> incl G G' -> QOK G' st.
Proof. intros. eapply Forall_chunk_ok_mono; eauto. Qed.
#[using="Type"] Lemma QOK_parts : forall G st, QOK G st <-> Forall (chunk_ok G) (live_chunks st) /\ Forall (chunk_ok G) (qchunks (a_qloc st)) /\ Forall (chunk_ok G) (qchunks (a_qglob st)).
Proof.
  intros G st. unfold QOK, all_chunks, qbatches. cbn [app]. rewrite qchunks_app, !Forall_app. tauto.
Qed.

#[using="Type"] Lemma evq_recycle_chunk : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> chunk_ok G ch -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunk st ch k).
Proof.
  intros R RP ga G st ch k extra HL Hch Hex Hk. destruct ch as [c n|mb ms n]; cbn [recycle_chunk].
  - cbn in Hch. apply evq_cache_dealloc; auto.
  - eapply evq_large_dealloc; eauto.
Qed.

#[using="Type"] Lemma evq_recycle_chunks : forall {R} RP ga G l st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) l -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunks st l k).
Proof.
  intros R RP ga G l. induction l as [|ch l IH]; intros st k extra HL HF Hex Hk; cbn [recycle_chunks].
  - apply Hk; [exact HL| apply frq_refl| lia].
  - apply Forall_cons_iff in HF as [Hch HF]. eapply evq_recycle_chunk; eauto.
    intros st1 HL1 HF1 HP1. apply IH; auto. intros st2 HL2 HF2 HP2. apply Hk; [exact HL2| eapply frq_trans; eauto| lia].
Qed.

#[using="Type"] Lemma batch_K : 1 <= K_BATCH_CLASS <= 31. Proof. unfold K_BATCH_CLASS. lia. Qed.

#[using="Type"] Lemma evq_do_recycle : forall {R} RP ga G bs st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) (qchunks bs) -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (do_recycle st bs k).
Proof.
  intros R RP ga G bs. induction bs as [|b bs IH]; intros st k extra HL HF Hex Hk; cbn [do_recycle].
  - apply Hk; [exact HL| apply frq_refl| lia].
  - rewrite qchunks_cons in HF. apply Forall_app in HF as [Hb HF].
    apply evq_recycle_chunks; auto. { apply Forall_rev. exact Hb. }
    intros st1 HL1 HF1 HP1. apply evq_cache_dealloc; auto; [apply batch_K|].
    intros st2 HL2 HF2 HP2. apply IH; auto. intros st3 HL3 HF3 HP3.
    apply Hk; [exact HL3| eapply frq_trans; [exact HF1| eapply frq_trans; eauto]| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma in_qchunks_app : forall ch a b, In ch (qchunks (a ++ b)) <-> In ch (qchunks a) \/ In ch (qchunks b).
Proof. intros. rewrite qchunks_app. apply in_app_iff. Qed.
#[using="Type"] Lemma in_qchunks_cons : forall ch b bs, In ch (qchunks (b :: bs)) <-> In ch (b_chunks b) \/ In ch (qchunks bs).
Proof. intros. rewrite qchunks_cons. apply in_app_iff. Qed.

#[using="Type"] Lemma merge_batches_incl : forall rest cur,
  let '(l, ex, exb) := merge_batches cur rest in incl (qchunks (l ++ ex)) (qchunks (cur :: rest)).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches].
  - rewrite app_nil_r. apply incl_refl.
  - destruct (_ <=? _).
    + set (cur' := mkABatch _ _ _). specialize (IH cur'). destruct (merge_batches cur' rest) as [[l ex] exb].
      intros ch Hin. apply in_qchunks_app in Hin as [Hin|Hin].
      * assert (H2 : In ch (qchunks (l ++ ex))) by (apply in_qchunks_app; left; exact Hin). apply IH in H2.
        apply in_qchunks_cons in H2 as [H2|H2].
        -- unfold cur' in H2. cbn [b_chunks] in H2. apply in_app_iff in H2 as [H2|H2].
           ++ apply in_qchunks_cons. right. apply in_qchunks_cons. left. exact H2.
           ++ apply in_qchunks_cons. left. exact H2.
        -- apply in_qchunks_cons. right. apply in_qchunks_cons. right. exact H2.
      * apply in_qchunks_cons in Hin as [Hin|Hin]; [cbn in Hin; destruct Hin|].
        assert (H2 : In ch (qchunks (l ++ ex))) by (apply in_qchunks_app; right; exact Hin). apply IH in H2.
        apply in_qchunks_cons in H2 as [H2|H2].
        -- unfold cur' in H2. cbn [b_chunks] in H2. apply in_app_iff in H2 as [H2|H2].
           ++ apply in_qchunks_cons. right. apply in_qchunks_cons. left. exact H2.
           ++ apply in_qchunks_cons. left. exact H2.
        -- apply in_qchunks_cons. right. apply in_qchunks_cons. right. exact H2.
    + specialize (IH nx). destruct (merge_batches nx rest) as [[l ex] exb].
      intros ch Hin. change ((cur :: l) ++ ex) with (cur :: (l ++ ex)) in Hin. apply in_qchunks_cons in Hin as [H1|H2].
      * apply in_qchunks_cons. left. exact H1.
      * apply in_qchunks_cons. right. apply IH. exact H2.
Qed.

#[using="Type"] Lemma Forall_incl' : forall {A} (P : A -> Prop) l l', Forall P l' -> incl l l' -> Forall P l.
Proof. intros A P l l' H HI. rewrite Forall_forall in *. intros x Hx. apply H, HI, Hx. Qed.

#[using="Type"] Lemma evq_recycle : forall {R} RP ga G st mn (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle st mn k).
Proof.
  intros R RP ga G st mn k extra HL HQ Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold recycle. cbv zeta.
  destruct (_ <? _); [apply evq_aundef|].
  assert (TAIL : forall gl extracted exb, incl (qchunks (gl ++ extracted)) (qchunks (a_qglob st)) ->
    evq RP ga G (PHI st + extra)
      (let '(taken, rest, bytes2) := dequeue_while gl (a_qglob_bytes st - exb) mn in
       if mn <? bytes2 then aundef_ (UCheck 0) (k st) else do_recycle (set_qglob rest bytes2 st) (extracted ++ taken) k)).
  2:{ destruct (_ && _).
      - destruct (a_qglob st) as [|b0 rest0] eqn:EQ.
        + cbv beta iota. apply TAIL. rewrite ?EQ. cbn. intros x Hx; exact Hx.
        + pose proof (merge_batches_incl rest0 b0) as HM. destruct (merge_batches b0 rest0) as [[gl extracted] exb].
          cbv beta iota. apply TAIL. rewrite ?EQ. exact HM.
      - cbv beta iota. apply TAIL. rewrite app_nil_r. apply incl_refl. }
  intros gl extracted exb HM.
  pose proof (dequeue_while_spec gl (a_qglob_bytes st - exb) mn) as HD.
  destruct (dequeue_while gl (a_qglob_bytes st - exb) mn) as [[taken rest] bytes2]. destruct HD as (HD1 & _ & _).
  destruct (mn <? bytes2); [apply evq_aundef|].
  assert (INC : incl (qchunks (extracted ++ taken) ++ qchunks rest) (qchunks (a_qglob st))).
  { intros ch Hin. apply HM. rewrite <- HD1. rewrite !qchunks_app in *. repeat (apply in_app_iff in Hin as [Hin|Hin]); apply in_app_iff; auto.
    - left. apply in_app_iff. auto. - left. apply in_app_iff. auto. }
  rewrite <- (PHI_set_qglob rest bytes2 st). apply evq_do_recycle; auto.
  { eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. left. exact Hin. }
  intros st1 HL1 HF1 HP1. apply Hk; [exact HL1| | rewrite PHI_set_qglob in HP1; exact HP1].
  apply (QOK_frq G (set_qglob rest bytes2 st) st1 HF1). apply QOK_parts. cbn [a_qloc a_qglob set_qglob].
  split; [exact Q1|]. split; [exact Q2|]. eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. right. exact Hin.
Qed.

#[using="Type"] Lemma evq_drain : forall {R} RP ga G st (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (drain st k).
Proof.
  intros R RP ga G st k extra HL HQ Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold drain. cbv zeta. set (st1 := set_qglob _ _ (set_qloc [] 0 st)).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn. split; [exact Q1|]. split; [constructor|]. rewrite qchunks_app. apply Forall_app. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity.
  destruct (Q_MAX <? _).
  - rewrite <- EP. apply evq_recycle; [exact HL1| exact HQ1| lia|]. intros st2 HL2 HQ2 HP2. apply Hk; [exact HL2| exact HQ2| lia].
  - rewrite <- EP. apply Hk; [exact HL1| exact HQ1| lia].
Qed.

#[using="Type"] Lemma qchunks_rev_snoc : forall P rl b,
  Forall P (qchunks (rev (b :: rl))) <-> Forall P (qchunks (rev rl)) /\ Forall P (b_chunks b).
Proof. intros P rl b. cbn [rev]. rewrite qchunks_app, Forall_app, qchunks_cons. cbn. rewrite app_nil_r. tauto. Qed.

#[using="Type"] Lemma evq_enqueue : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> QOK G st -> chunk_ok G ch -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (enqueue st ch k).
Proof.
  intros R RP ga G st ch k extra HL HQ Hch Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold enqueue. cbv zeta.
  assert (NEW : forall st0, LW st0 -> frq st st0 -> PHI st0 <= PHI st ->
    evq RP ga G (PHI st0 + extra)
      (cache_alloc st0 K_BATCH_CLASS (fun st1 ok => if negb ok then aundef_ USpin (k st1)
         else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1)))).
  { intros st0 HL0 HF0 HP0. apply evq_cache_alloc; auto; [apply batch_K|]. intros st1 ok HL1 HF1 HP1. destruct ok; cbn [negb]; [|apply evq_aundef].
    rewrite <- (PHI_set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1).
    apply Hk; [apply LW_set_qloc; exact HL1| | rewrite PHI_set_qloc; lia].
    pose proof (QOK_frq G st st1 (frq_trans _ _ _ HF0 HF1) HQ) as HQ1. apply QOK_parts in HQ1 as (R1 & R2 & R3).
    apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact R1|]. split; [| exact R3].
    rewrite qchunks_app, Forall_app. split; [exact R2|]. rewrite qchunks_cons. cbn. constructor; [exact Hch| constructor]. }
  destruct (rev (a_qloc st)) as [|b rl] eqn:ER.
  - apply NEW; [exact HL| apply frq_refl| lia].
  - destruct (b_count b =? Q_BATCH). { apply NEW; [exact HL| apply frq_refl| lia]. }
    rewrite <- (PHI_set_qloc (rev (mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b) :: rl)) (a_qloc_bytes st + chunk_size ch) st).
    apply Hk; [apply LW_set_qloc; exact HL| | rewrite PHI_set_qloc; lia].
    apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact Q1|]. split; [| exact Q3].
    assert (E : a_qloc st = rev (b :: rl)) by (rewrite <- ER, rev_involutive; reflexivity).
    rewrite E in Q2. apply qchunks_rev_snoc in Q2 as [Q2a Q2b]. apply qchunks_rev_snoc. split; [exact Q2a|]. cbn. constructor; assumption.
Qed.

#[using="Type"] Lemma evq_afree : forall G st id,
  LW st -> QOK G st ->
  evq RPst [] G (PHI st + 0) (afree st (Some id)).
Proof.
  intros G st id HL HQ. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold afree.
  destruct ((a_live st) !! id) as [ch|] eqn:Hl; [|apply evq_aundef]. cbv zeta.
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  pose proof (Permutation_Forall HPl Q1) as Q1'. apply Forall_cons_iff in Q1' as [Hch Q1d].
  set (st1 := set_live (delete id (a_live st)) st).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn [a_qloc a_qglob st1 set_live]. split; [exact Q1d|]. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity.
  assert (AFTER : forall st2, LW st2 -> QOK G st2 -> PHI st2 <= PHI st ->
    evq RPst [] G (PHI st2 + 0) (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 HL2 HQ2 HP2. destruct (Q_CACHE <? _).
    - apply evq_drain; [exact HL2| exact HQ2| lia|]. intros st3 HL3 HQ3 HP3. cbn. split; assumption.
    - cbn. split; assumption. }
  rewrite <- EP. destruct (chunk_size ch <=? Q_MAX).
  - apply evq_enqueue; [exact HL1| exact HQ1| exact Hch| lia|]. intros st2 HL2 HQ2 HP2. apply AFTER; [exact HL2| exact HQ2| lia].
  - apply (evq_recycle_chunk RPst [] G st1 ch); [exact HL1| exact Hch| lia|]. intros st2 HL2 HF2 HP2. apply AFTER; [exact HL2| eapply QOK_frq; eauto| lia].
Qed.

#[using="Type"] Lemma evq_afree_none : forall G st, LW st -> QOK G st -> evq RPst [] G (PHI st + 0) (afree st None).
Proof. intros G st HL HQ. cbn. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma evq_aannotate : forall G st p cap old new ch,
  LW st -> QOK G st -> (a_live st) !! p = Some ch -> cap <= chunk_size ch ->
  evq RPst [] G (PHI st + 0) (aannotate st p cap old new).
Proof.
  intros G st p cap old new ch HL HQ Hl Hcap. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold aannotate. rewrite Hl.
  assert (RET : evq RPst [] G (PHI st + 0) (aret st)) by (cbn; split; assumption).
  destruct (negb _) eqn:E1; [apply evq_aundef|].
  apply Bool.negb_false_iff in E1. repeat (apply andb_prop in E1 as [E1 ?]).
  apply Z.leb_le in E1. apply Z.leb_le in H1. apply Z.leb_le in H0. apply Z.leb_le in H.
  destruct (2 ^ 40 <? cap); [apply evq_aundef|].
  destruct (old =? new); [exact RET|].
  destruct (negb (Z.land cap 7 =? 0) && _); [apply evq_aundef|].
  destruct (old <? new) eqn:E2; [|exact RET]. apply Z.ltb_lt in E2.
  assert (Hch : chunk_ok G ch).
  { pose proof (live_chunks_delete st p ch Hl) as HPl. pose proof (Permutation_Forall HPl Q1) as X. apply Forall_cons_iff in X as [X _]. exact X. }
  destruct ch as [c n|mb ms n]; [exact RET|]. cbv zeta. cbn in Hcap.
  destruct (rdn old 8 <? rdn new 8) eqn:E3; [|exact RET]. apply Z.ltb_lt in E3.
  cbn in Hch. destruct Hch as (Hin & Hmb & Hn & Hms).
  pose proof (rdn_le new 8 ltac:(lia)). pose proof (rdn_le old 8 ltac:(lia)).
  assert (0 <= rdn old 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply (evq_poison0 RPst [] G _ _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia.
Qed.
End Ev.
End CANSEC1.
End ATsafeEv.

(* [comment removed for export] *)
Module AsanOps.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanInv AsanBudget. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanBudget OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation aok := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.aok ATOP).
Local Notation apost := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).

(* [comment removed for export] *)
#[using="Type"] Theorem acalloc_core : forall st mo m n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= m -> 0 <= n -> m * n <= 2^29 ->
  (forall mb ms, live_budget_list (mkch (m * n) mb ms :: live_chunks st)) ->
  atot (acalloc ATOP RESV st m n) mo (malloc_post (RESV:=RESV) (ATOP:=ATOP) st (m * n)).
Proof.
  intros st mo m n HI Hq1 Hq2 Hm Hn Hmn HLB. unfold acalloc.
  replace (m <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (TWO64 <=? m * n) with false by (symmetry; apply Z.leb_gt; unfold TWO64; lia).
  cbn [orb]. apply amalloc_core; auto. split; [apply Z.mul_nonneg_nonneg; lia| lia].
Qed.

(* [comment removed for export] *)
Definition realloc_post (st : astate) (p : AsanCtrl.aptr) (n : Z) (r : astate * option AsanCtrl.aptr) (mo' : Model) : Prop :=
  exists ch, snd r = Some (a_next st) /\ INV [] [] (fst r) mo'
  /\ a_live (fst r) = delete p (<[a_next st := ch]> (a_live st))
  /\ (a_live st) !! (a_next st) = None /\ chunk_size ch = n
  /\ a_next (fst r) = N.succ (a_next st)
  /\ a_qloc_bytes (fst r) <= Q_CACHE /\ a_qglob_bytes (fst r) <= Q_MAX.

#[using="Type"] Theorem arealloc_core : forall st mo p chp n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^29 ->
  (a_live st) !! p = Some chp ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  atot (arealloc ATOP RESV st p n) mo (realloc_post st p n).
Proof.
  intros st mo p chp n HI Hq1 Hq2 Hn Hp HLB. unfold arealloc. rewrite Hp.
  eapply atotal_sbind; [apply (amalloc_core (RESV:=RESV) (ATOP:=ATOP) st mo n HI Hq1 Hq2 Hn HLB)|].
  intros [st1 r1] mo1 (ch & Hr & HI1 & Hlive & Hnone & Hsz & E1 & E2 & E3 & E4 & Hnx). cbn [fst snd] in *. subst r1.
  assert (Hp1 : (a_live st1) !! p = Some chp).
  { rewrite Hlive. destruct (N.eq_dec (a_next st) p) as [E|NE].
    - exfalso. rewrite E in Hnone. assert (X : Some chp = None) by (rewrite <- Hp; exact Hnone). discriminate X.
    - rewrite lookup_insert_ne by exact NE. exact Hp. }
  eapply atotal_sbind; [apply (afree_core (RESV:=RESV) (ATOP:=ATOP) st1 mo1 p chp HI1 ltac:(lia) ltac:(lia) Hp1)|].
  intros st2 mo2 (HI2 & Hlive2 & Hnx2 & Hq1' & Hq2'). apply atotal_ret.
  exists ch. cbn [fst snd]. split; [reflexivity|]. split; [exact HI2|]. split; [rewrite Hlive2, Hlive; reflexivity|].
  split; [exact Hnone|]. split; [exact Hsz|]. split; [rewrite Hnx2; exact Hnx|]. split; assumption.
Qed.
End WithResv.
End AsanOps.
