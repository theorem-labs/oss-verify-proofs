(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Record fheap := mkFH {
  fh_m : mstate;                 (* [comment removed for export] *)
  fh_brk : Z;                    (* [comment removed for export] *)
  fh_next : N;                   (* [comment removed for export] *)
  fh_blk : gmap N (aptr * Z)     (* [comment removed for export] *)
}.

Definition hptr : Type := N.
End WithCeil.

#[local] Abbreviation PS := (PState fheap hptr) (only parsing).
#[local] Abbreviation MP := (Monad.M (PState fheap hptr)) (only parsing).

Section WithCeil.
Context {CE : CEIL}.
(* [comment removed for export] *)
Definition fheap_init (secret : Z) (reserved : list (Z * Z)) : fheap := mkFH (minit secret reserved) 0 0%N ∅.
End WithCeil.


#[export] Instance fheap_AllocSt : AllocSt (PState fheap hptr) := {|
  ps_rest_t := (N * gmap N (aptr * Z) * PState fheap hptr)%type;
  ps_m := fun s => fh_m (ps_heap s);
  ps_brk := fun s => fh_brk (ps_heap s);
  ps_rest := fun s => (fh_next (ps_heap s), fh_blk (ps_heap s), set_heap (fheap_init 0 []) s);
  set_m := fun v s => set_heap (mkFH v (fh_brk (ps_heap s)) (fh_next (ps_heap s)) (fh_blk (ps_heap s))) s;
  set_brk_ps := fun v s => set_heap (mkFH (fh_m (ps_heap s)) v (fh_next (ps_heap s)) (fh_blk (ps_heap s))) s;
  ps_m_set_m := fun v s => eq_refl;
  ps_brk_set_m := fun v s => eq_refl;
  ps_rest_set_m := fun v s => eq_refl;
  ps_m_set_brk := fun v s => eq_refl;
  ps_brk_set_brk := fun v s => eq_refl;
  ps_rest_set_brk := fun v s => eq_refl |}.

(* [comment removed for export] *)
#[warnings="-notation-for-abbreviation"] Notation peekN := (@peekG (PState fheap hptr)) (only parsing).

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma peekN_spec : forall caddr (P : assn PS), mspec P (peekN caddr) (fun v s mo => 0 <= v < 256 /\ P s mo).
Proof. exact (@peekG_spec PS). Qed.

(* [comment removed for export] *)
Definition tok_fresh (p : aptr) (n : Z) : MP hptr :=
  s <- mget ;;
  let h := ps_heap s in
  let k := fh_next h in
  mupd (set_heap (mkFH (fh_m h) (fh_brk h) (N.succ k) (<[k := (p, n)]> (fh_blk h)))) ;;;
  mret k.
Definition tok_drop (k : hptr) : MP unit :=
  mupd (fun s => let h := ps_heap s in set_heap (mkFH (fh_m h) (fh_brk h) (fh_next h) (delete k (fh_blk h))) s).
Definition tok_lookup (k : hptr) : MP (option (aptr * Z)) :=
  s <- mget ;; mret (fh_blk (ps_heap s) !! k).

(* [comment removed for export] *)
Definition hf_malloc (n : Z) : MP (option hptr) :=
  r <- raw_mallocF peekN n ;;
  match r with
  | None => mret None
  | Some p => k <- tok_fresh p n ;; mret (Some k)
  end.

Definition hf_calloc (m n : Z) : MP (option hptr) :=
  r <- raw_callocF peekN m n ;;
  match r with
  | None => mret None
  | Some p => k <- tok_fresh p (m * n) ;; mret (Some k)
  end.

(* [comment removed for export] *)
Definition hf_realloc (k : hptr) (n : Z) : MP (option hptr) :=
  b <- tok_lookup k ;;
  match b with
  | None => munr                                   (* [comment removed for export] *)
  | Some (p, _) =>
      r <- raw_reallocF peekN (Some p) n ;;
      match r with
      | None => mret None
      | Some q => tok_drop k ;;; k' <- tok_fresh q n ;; mret (Some k')
      end
  end.

Definition hf_free (k : hptr) : MP unit :=
  b <- tok_lookup k ;;
  match b with
  | None => munr
  | Some (p, _) => raw_freeF peekN p ;;; tok_drop k
  end.

(* [comment removed for export] *)
Definition hf_addr (h : fheap) (k : hptr) : Z :=
  match fh_blk h !! k with Some (p, _) => conc (fh_m h) p | None => 0 end.

(* [comment removed for export] *)
Definition pin_reserved (r : Z * Z) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) (s_slots st)
          (s_tick st) (s_secret st) (s_reserved st ++ [r]).
Definition hf_pin (tb : Z) (h : fheap) : fheap := mkFH (pin_reserved (tb, 4096) (fh_m h)) (fh_brk h) (fh_next h) (fh_blk h).

#[using="Type"] Lemma hf_pin_init : forall tb secret resv, hf_pin tb (fheap_init secret resv) = fheap_init secret (resv ++ [(tb, 4096)]).
Proof. intros. reflexivity. Qed.

Definition full_ops : HeapOps fheap hptr := mkHeapOps fheap hptr hf_malloc hf_calloc hf_realloc hf_free hf_addr N.eqb hf_pin.

(* [comment removed for export] *)
Definition tok_blocks (h : fheap) : list (aptr * Z) := map snd (map_to_list (fh_blk h)).
Definition blk_ptr (b : blk) : aptr * Z := (aadd (bslot b) (UNIT * boff b), bsize b).

Definition HOWN (G : PS -> Model -> Prop) : assn PS := fun s mo =>
  (exists BL, FOWN BL (fun _ _ => True) s mo /\ Permutation.Permutation (map blk_ptr BL) (tok_blocks (ps_heap s))
              /\ (forall k, fh_blk (ps_heap s) !! k <> None -> (k < fh_next (ps_heap s))%N))
  /\ G s mo.

(* [comment removed for export] *)

End WithCeil.
