(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg RefNodes AsanCeil PureModel VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import MallocLayout.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mstate := MS { ms_mem : word -> option byte; ms_vm : VmMaps; ms_lo : Z; ms_hi : Z }.

(* [comment removed for export] *)
Definition upd (s : mstate) (m : word -> option byte) (h : VmMaps) : mstate :=
  MS m h (ms_lo s) (ms_hi s).

(* [comment removed for export] *)
Definition acc_ok (s : mstate) (a : word) (n : Z) : bool :=
  (bv_unsigned a + n <=? ms_lo s) || ((ms_hi s <=? bv_unsigned a) && (bv_unsigned a + n <=? 2^64)).

(* [comment removed for export] *)
Inductive mmkind := MMrw | MMnone.

Inductive itree (A : Type) : Type :=
| TRet (a : A) (s : mstate)
| TCrash
  (* [comment removed for export] *)
| TBrk (req : word) (vm : VmMaps) (kfail kok : itree A)
  (* [comment removed for export] *)
| TMmap (k : mmkind) (len : word) (vm : VmMaps) (kfail : itree A) (kok : word -> itree A)
  (* [comment removed for export] *)
| TMmapFixed (addr len : word) (kkeep kok kdestroy : itree A)
  (* [comment removed for export] *)
| TMprot (addr len : word) (vm : VmMaps) (kfail kok : itree A).

Arguments TRet {A} a s.
Arguments TCrash {A}.
Arguments TBrk {A} req vm kfail kok.
Arguments TMmap {A} k len vm kfail kok.
Arguments TMmapFixed {A} addr len kkeep kok kdestroy.
Arguments TMprot {A} addr len vm kfail kok.

Definition M (A : Type) : Type := mstate -> itree A.

Fixpoint tbind {A B : Type} (t : itree A) (f : A -> M B) : itree B :=
  match t with
  | TRet a s => f a s
  | TCrash => TCrash
  | TBrk req vm kf ko => TBrk req vm (tbind kf f) (tbind ko f)
  | TMmap k len vm kf ko => TMmap k len vm (tbind kf f) (fun a => tbind (ko a) f)
  | TMmapFixed addr len k1 k2 k3 => TMmapFixed addr len (tbind k1 f) (tbind k2 f) (tbind k3 f)
  | TMprot addr len vm kf ko => TMprot addr len vm (tbind kf f) (tbind ko f)
  end.

Definition mret {A : Type} (a : A) : M A := fun s => TRet a s.
Definition mbind {A B : Type} (m : M A) (f : A -> M B) : M B := fun s => tbind (m s) f.
Definition mcrash {A : Type} : M A := fun _ => TCrash.
Definition mget : M mstate := fun s => TRet s s.
Definition mput (s : mstate) : M unit := fun _ => TRet tt s.
Definition massert (b : bool) : M unit := if b then mret tt else mcrash.

Declare Scope malloc_scope.
Notation "x <- m1 ;; m2" := (mbind m1 (fun x => m2))
  (at level 100, m1 at next level, right associativity) : malloc_scope.
Notation "m1 ;; m2" := (mbind m1 (fun _ => m2))
  (at level 100, right associativity) : malloc_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition le_val (bs : list byte) : word := Z_to_bv 64 (bytes_le_to_Z bs).

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Definition m_rd (n : nat) (a : word) : M (list byte) :=
  fun s => if acc_ok s a (Z.of_nat n)
           then match rdn ml_segs (ms_mem s) a n with Some bs => TRet bs s | None => TCrash end
           else TCrash.
Definition m_lbu (a : word) : M word :=
  bs <- m_rd 1 a ;; match bs with [b] => mret (Z_to_bv 64 (bv_unsigned b)) | _ => mcrash end.
Definition m_lhu (a : word) : M word := bs <- m_rd 2 a ;; mret (le_val bs).
Definition m_lwu (a : word) : M word := bs <- m_rd 4 a ;; mret (le_val bs).
Definition m_lw  (a : word) : M word := bs <- m_rd 4 a ;; mret (v_lw (le_val bs)).
Definition m_ld  (a : word) : M word := bs <- m_rd 8 a ;; mret (le_val bs).

(* [comment removed for export] *)
Definition st_zone (a : word) (n : Z) : bool :=
  let x := bv_unsigned a in
  (x + n <=? IMG_LO) || (IMG_HI <=? x)
  || ((bv_unsigned A_ERRNO <=? x) && (x + n <=? bv_unsigned A_ERRNO + 4))
  || ((bv_unsigned A_CTX <=? x) && (x + n <=? bv_unsigned A_CTX + CTX_SIZE)).

(* [comment removed for export] *)
Definition m_st (n : nat) (a v : word) : M unit :=
  fun s => if acc_ok s a (Z.of_nat n) && st_zone a (Z.of_nat n) && store_ok ml_segs (ms_mem s) a n
           then TRet tt (upd s (wbytes (ms_mem s) a (word_to_le_bytes n v)) (ms_vm s))
           else TCrash.
Definition m_sb (a v : word) : M unit := m_st 1 a v.
Definition m_sh (a v : word) : M unit := m_st 2 a v.
Definition m_sw (a v : word) : M unit := m_st 4 a v.
Definition m_sd (a v : word) : M unit := m_st 8 a v.

(* [comment removed for export] *)
Definition m_stbytes (a : word) (bs : list byte) : M unit :=
  fun s => let n := length bs in
           if acc_ok s a (Z.of_nat n) && st_zone a (Z.of_nat n) && store_ok ml_segs (ms_mem s) a n
           then TRet tt (upd s (wbytes (ms_mem s) a bs) (ms_vm s))
           else TCrash.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MAP_FAILED : word := Z_to_bv 64 (2^64 - 1).

(* [comment removed for export] *)
Definition set_errno (e : Z) : M unit := m_sw A_ERRNO (Z_to_bv 64 e).

(* [comment removed for export] *)
Definition sys_brk_query : M word := fun s => TRet (vm_brk (ms_vm s)) s.

(* [comment removed for export] *)
Definition sys_brk_grow (req : word) : M word :=
  fun s =>
    let h := ms_vm s in
    if (0 <? bv_unsigned (vm_brk h)) && (bv_unsigned (vm_start_brk h) <=? bv_unsigned req)
       && (bv_unsigned (vm_brk h) <? bv_unsigned req)
    then TBrk req h
           (TRet (vm_brk h) s)
           (TRet req (upd s (apply_zeros (ms_mem s) (brk_zeros req req (vm_brk h))) (vm_brk_grow req h)))
    else TCrash.

(* [comment removed for export] *)
Definition sys_mmap (k : mmkind) (len : word) : M word :=
  fun s =>
    let h := ms_vm s in
    if (0 <? bv_unsigned len) && (bv_unsigned len <? 2^62)
    then TMmap k len h
           (tbind (set_errno ENOMEM s) (fun _ s' => TRet MAP_FAILED s'))
           (fun a => let n := page_round_up len in
                     match k with
                     | MMrw   => TRet a (upd s (zfill a n (ms_mem s)) (vm_mmap a n h))
                     | MMnone => TRet a (upd s (unfill a n (ms_mem s)) (vm_noacc a n h))
                     end)
    else TCrash.

(* [comment removed for export] *)
Definition sys_mmap_fixed_none (addr len : word) : M word :=
  fun s =>
    let h := ms_vm s in
    let n := page_round_up len in
    if (0 <? bv_unsigned len) && (bv_unsigned len <? 2^62)
       && (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top h)
       && (bv_unsigned addr mod page_size =? 0) && (0 <? bv_unsigned addr)
       && region_free (vm_reserved h) addr n
       && map_contains (vm_maps h) addr n
    then TMmapFixed addr len
           (tbind (set_errno ENOMEM s) (fun _ s' => TRet MAP_FAILED s'))
           (TRet addr (upd s (unfill addr n (ms_mem s)) (vm_fixed_ok addr n h)))
           (tbind (set_errno ENOMEM (upd s (unfill addr n (ms_mem s)) (vm_fixed_destroy addr n h)))
                  (fun _ s' => TRet MAP_FAILED s'))
    else TCrash.

(* [comment removed for export] *)
Definition sys_mprotect_rw (addr len : word) : M word :=
  fun s =>
    let h := ms_vm s in
    let n := page_round_up len in
    if (0 <? bv_unsigned len) && (bv_unsigned addr mod page_size =? 0)
       && (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top h)
       && map_contains (vm_maps h) addr n
    then if map_contains (vm_noaccess h) addr n
         then TMprot addr len h
                (tbind (set_errno ENOMEM s) (fun _ s' => TRet MAP_FAILED s'))
                (TRet (Z_to_bv 64 0) (upd s (zfill addr n (ms_mem s)) (vm_unprotect addr n h)))
         else if region_free (vm_noaccess h) addr n
              then TRet (Z_to_bv 64 0) s
              else TCrash
    else TCrash.

(* [comment removed for export] *)
Definition sys_munmap (addr len : word) : M word :=
  fun s =>
    let h := ms_vm s in
    let n := page_round_up len in
    if (bv_unsigned addr mod page_size =? 0) && (0 <? bv_unsigned len)
       && (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top h)
       && map_has (vm_maps h) addr n
    then TRet (Z_to_bv 64 0) (upd s (unfill addr n (ms_mem s)) (vm_munmap addr n h))
    else TCrash.

End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_grant_ok (k : mmkind) (vm : VmMaps) (a : word) (n : Z) : bool :=
  match k with MMrw => grant_ok_vm vm a n | MMnone => grant_ok_na_vm vm a n end.

(* [comment removed for export] *)
Definition mmap_refusable_k (k : mmkind) (vm : VmMaps) (n : Z) : bool :=
  match k with MMrw => mmap_refusable_vm vm n | MMnone => mmap_na_refusable_vm vm n end.

Lemma mmap_refusable_k_iff : forall k vm n,
  mmap_refusable_k k vm n = true <-> forall a, mmap_grant_ok k vm a n = false.
Proof. intros [|] vm n; cbn; [apply mmap_refusable_vm_iff | apply mmap_na_refusable_vm_iff]. Qed.

Lemma mmap_refusable_k_false_iff : forall k vm n,
  mmap_refusable_k k vm n = false <-> exists a, mmap_grant_ok k vm a n = true.
Proof. intros [|] vm n; cbn; [apply mmap_refusable_vm_false_iff | apply mmap_na_refusable_vm_false_iff]. Qed.

(* [comment removed for export] *)
Fixpoint tshape {A : Type} (t : itree A) (L : A -> mstate -> TSet) : TSet :=
  match t with
  | TRet a s => L a s
  | TCrash => t_nil
  | TBrk req vm kf ko =>
      fun tr => (brk_grow_ok_vm vm req req = false /\ tshape kf L tr)
                \/ (brk_grow_ok_vm vm req req = true /\ tshape ko L tr)
  | TMmap k len vm kf ko =>
      fun tr => (mmap_refusable_k k vm (page_round_up_Z (bv_unsigned len)) = true /\ tshape kf L tr)
                \/ exists a, mmap_grant_ok k vm a (page_round_up_Z (bv_unsigned len)) = true
                             /\ tshape (ko a) L tr
  | TMmapFixed addr len k1 k2 k3 => tshape k2 L
  | TMprot addr len vm kf ko =>
      fun tr => (mprot_ok_vm vm addr (page_round_up len) = false /\ tshape kf L tr)
                \/ (mprot_ok_vm vm addr (page_round_up len) = true /\ tshape ko L tr)
  end.

(* [comment removed for export] *)
Fixpoint tsafe {A : Type} (t : itree A) (P : A -> mstate -> Prop) : Prop :=
  match t with
  | TRet a s => P a s
  | TCrash => False
  | TBrk req vm kf ko =>
      (brk_grow_ok_vm vm req req = false -> tsafe kf P) /\ (brk_grow_ok_vm vm req req = true -> tsafe ko P)
  | TMmap k len vm kf ko =>
      (mmap_refusable_k k vm (page_round_up_Z (bv_unsigned len)) = true -> tsafe kf P)
      /\ forall a, mmap_grant_ok k vm a (page_round_up_Z (bv_unsigned len)) = true -> tsafe (ko a) P
  | TMmapFixed addr len k1 k2 k3 => tsafe k2 P
  | TMprot addr len vm kf ko =>
      (mprot_ok_vm vm addr (page_round_up len) = false -> tsafe kf P)
      /\ (mprot_ok_vm vm addr (page_round_up len) = true -> tsafe ko P)
  end.

Lemma tsafe_mono : forall {A} (t : itree A) (P Q : A -> mstate -> Prop),
  (forall a s, P a s -> Q a s) -> tsafe t P -> tsafe t Q.
Proof.
  intros A t; induction t; intros P Q HPQ Hs; cbn in *; intuition eauto.
Qed.

Lemma tsafe_bind : forall {A B} (t : itree A) (f : A -> M B) (P : A -> mstate -> Prop) (Q : B -> mstate -> Prop),
  tsafe t P -> (forall a s, P a s -> tsafe (f a s) Q) -> tsafe (tbind t f) Q.
Proof.
  intros A B t; induction t; intros f P Q Hs Hf; cbn in *; intuition eauto.
Qed.

(* [comment removed for export] *)
Lemma tshape_bind : forall {A B} (t : itree A) (f : A -> M B) (L : B -> mstate -> TSet),
  t_eq (tshape (tbind t f) L) (tshape t (fun a s => tshape (f a s) L)).
Proof.
  intros A B t; induction t; intros f L tr; cbn; try tauto.
  - rewrite (IHt1 f L tr), (IHt2 f L tr). tauto.
  - split.
    + intros [[X0 X] | (a & Y & Z)]; [left; split; [exact X0 | apply (IHt f L tr); exact X] | right; exists a; split; [exact Y | apply (H a f L tr); exact Z]].
    + intros [[X0 X] | (a & Y & Z)]; [left; split; [exact X0 | apply (IHt f L tr); exact X] | right; exists a; split; [exact Y | apply (H a f L tr); exact Z]].
  - exact (IHt2 f L tr).
  - rewrite (IHt1 f L tr), (IHt2 f L tr). tauto.
Qed.

(* [comment removed for export] *)
Lemma tshape_const : forall {A} (t : itree A) (S : TSet) (P : A -> mstate -> Prop),
  S [] -> tsafe t P -> t_eq (tshape t (fun _ _ => S)) S.
Proof.
  intros A t; induction t; intros S P HS Hsafe tr; cbn in *; try tauto.
  - destruct Hsafe as [H1 H2]. split.
    + intros [[Y X] | [Y Z]]; [apply (IHt1 S P HS (H1 Y) tr); exact X | apply (IHt2 S P HS (H2 Y) tr); exact Z].
    + intros X. destruct (brk_grow_ok_vm vm req req) eqn:Eg.
      * right. split; [reflexivity | apply (IHt2 S P HS (H2 eq_refl) tr); exact X].
      * left. split; [reflexivity | apply (IHt1 S P HS (H1 eq_refl) tr); exact X].
  - destruct Hsafe as [H1 H2]. split.
    + intros [[Y X] | (a & Y & Z)]; [apply (IHt S P HS (H1 Y) tr); exact X | apply (H a S P HS (H2 a Y) tr); exact Z].
    + intros X. destruct (mmap_refusable_k k vm (page_round_up_Z (bv_unsigned len))) eqn:Er.
      * left. split; [reflexivity | apply (IHt S P HS (H1 eq_refl) tr); exact X].
      * apply mmap_refusable_k_false_iff in Er as [a Ha]. right. exists a. split; [exact Ha|].
        apply (H a S P HS (H2 a Ha) tr). exact X.
  - exact (IHt2 S P HS Hsafe tr).
  - destruct Hsafe as [H1 H2]. split.
    + intros [[Y X] | [Y Z]]; [apply (IHt1 S P HS (H1 Y) tr); exact X | apply (IHt2 S P HS (H2 Y) tr); exact Z].
    + intros X. destruct (mprot_ok_vm vm addr (page_round_up len)) eqn:Eo.
      * right. split; [reflexivity | apply (IHt2 S P HS (H2 eq_refl) tr); exact X].
      * left. split; [reflexivity | apply (IHt1 S P HS (H1 eq_refl) tr); exact X].
Qed.

(* [comment removed for export] *)
Lemma tsafe_ret : forall {A} (a : A) s (P : A -> mstate -> Prop), P a s -> tsafe (mret a s) P.
Proof. intros A a s P H. exact H. Qed.

Lemma tsafe_mbind : forall {A B} (m : M A) (f : A -> M B) s (P : A -> mstate -> Prop) (Q : B -> mstate -> Prop),
  tsafe (m s) P -> (forall a s', P a s' -> tsafe (f a s') Q) -> tsafe (mbind m f s) Q.
Proof. intros A B m f s P Q Hm Hf. unfold mbind. eapply tsafe_bind; eauto. Qed.

Lemma tsafe_massert : forall b s (P : unit -> mstate -> Prop),
  tsafe (massert b s) P <-> (b = true /\ P tt s).
Proof.
  intros b s P. unfold massert, mret, mcrash. destruct b; cbn; intuition congruence.
Qed.
