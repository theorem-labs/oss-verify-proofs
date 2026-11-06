(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling Mem Frame.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition mem := word -> option byte.

(* [comment removed for export] *)
Definition mapped (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) <> None.
(* [comment removed for export] *)
Definition bytes_eq (m m' : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i)).
Definition all_zero (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition MALLOC_STACK : Z := 8192.
Definition FREE_STACK : Z := 8192.
Definition CALLOC_STACK : Z := 8224.
Definition REALLOC_STACK : Z := 8256.

(* [comment removed for export] *)
Definition LIVE_MAX : Z := 2 ^ 31.
Lemma LIVE_MAX_eq : LIVE_MAX = 2 ^ 31. Proof. reflexivity. Qed.
#[global] Opaque LIVE_MAX.
Definition NLIVE_MAX : Z := 2 ^ 6.
Lemma NLIVE_MAX_eq : NLIVE_MAX = 2 ^ 6. Proof. reflexivity. Qed.
#[global] Opaque NLIVE_MAX.
Definition NREQ_CAP : Z := 2 ^ 30.
Lemma NREQ_CAP_eq : NREQ_CAP = 2 ^ 30. Proof. reflexivity. Qed.
#[global] Opaque NREQ_CAP.

(* [comment removed for export] *)
Record AllocLayout := mkLayout {
  al_segs : list Segment;
  al_malloc_pc : word;          (* [comment removed for export] *)
  al_free_pc : word;            (* [comment removed for export] *)
  al_calloc_pc : word;          (* [comment removed for export] *)
  al_realloc_pc : word;         (* [comment removed for export] *)
  al_tp : word;                 (* [comment removed for export] *)
  al_static : Z -> Prop;        (* [comment removed for export] *)
  al_shared : Z -> Prop;        (* [comment removed for export] *)
  al_image_lo : Z;              (* [comment removed for export] *)
  al_rw_lo : Z;                 (* [comment removed for export] *)
  al_image_hi : Z;
}.

Definition al_errno (L : AllocLayout) : Z := bv_unsigned (al_tp L) - 164.
Definition al_rom (L : AllocLayout) : mem := seg_rom (al_segs L).

(* [comment removed for export] *)
Definition md_frame (md md' : Model) : Prop :=
  m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md
  /\ m_lim md' = m_lim md /\ m_time md' = m_time md
  /\ vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)
  /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)
  /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)
  /\ vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)
  /\ m_vm_lazy md' = [] /\ m_halted md' = None.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk (r n : Z) (a : Z) : Prop := r <> 0 /\ r <= a < r + n.
Definition nowhere (a : Z) : Prop := False.

Section WithLayout.
(* [comment removed for export] *)
Context {Clg : Ceiling} (L : AllocLayout).

Let segs := al_segs L.
Let rom := al_rom L.

(* [comment removed for export] *)
Definition in_image (a : Z) : Prop := al_image_lo L <= a < al_image_hi L.
Definition heap_zone (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ in_image a.

(* [comment removed for export] *)
Definition frame_ok (owned owned' : Z -> Prop) (sp win : Z) (victim newb : Z -> Prop) (m m' : mem) : Prop :=
     (forall a, 0 <= a < 2^64 -> ~ owned a -> ~ owned' a -> ~ (sp - win <= a < sp) -> ~ (al_errno L <= a < al_errno L + 4) ->
                ~ victim a -> ~ newb a -> m' (wz a) = m (wz a))
  /\ (forall a, 0 <= a < 2^64 -> ~ in_image a -> m (wz a) <> None -> owned a \/ victim a \/ m' (wz a) <> None)
  /\ mapped m' (sp - win) win
  /\ (forall a, 0 <= a < 2^64 -> newb a -> owned a \/ victim a \/ (m (wz a) = None /\ heap_zone a))
  /\ (forall a, 0 <= a < 2^64 -> owned' a -> owned a \/ victim a \/ (m (wz a) = None /\ heap_zone a))
  /\ (forall a, 0 <= a < 2^64 -> owned a -> ~ owned' a -> newb a \/ m' (wz a) = None)
  /\ (forall a, 0 <= a < 2^64 -> victim a -> owned' a \/ newb a \/ m' (wz a) = None).

(* [comment removed for export] *)
(* [comment removed for export] *)

Class AllocSpec := {
  (* [comment removed for export] *)
  AS : Type;
  (* [comment removed for export] *)
  a_live : AS -> Z -> option Z;
  (* [comment removed for export] *)
  a_livebytes : AS -> Z;
  a_nlive : AS -> Z;
  (* [comment removed for export] *)
  ainv : AS -> mem -> Model -> Prop;
  (* [comment removed for export] *)
  owned : AS -> Z -> Prop;

  (* [comment removed for export] *)
  as_static_owned : forall A a, al_static L a -> owned A a;
  as_static_where : forall a, al_static L a -> al_rw_lo L <= a < al_image_hi L;
  as_shared_where : forall a, al_shared L a -> al_rw_lo L <= a < al_image_hi L;
  as_shared_not_static : forall a, al_shared L a -> ~ al_static L a;
  as_errno_where : al_rw_lo L <= al_errno L /\ al_errno L + 4 <= al_image_hi L;
  as_errno_not_static : forall i, 0 <= i < 4 -> ~ al_static L (al_errno L + i) /\ ~ al_shared L (al_errno L + i);
  as_layout_order : 4096 <= al_image_lo L <= al_rw_lo L /\ al_rw_lo L <= al_image_hi L
                    /\ al_image_hi L + 65536 <= alloc_ceiling;
  (* [comment removed for export] *)
  as_ro_addr_iff : forall a : word, ro_addr segs a = true <-> al_image_lo L <= bv_unsigned a < al_rw_lo L;
  as_seg_rom_outside : forall a : word, ~ in_image (bv_unsigned a) -> seg_rom segs a = None;
  as_find_segment_outside : forall a : word, ~ in_image (bv_unsigned a) -> find_segment segs (bv_unsigned a) 1 = None;
  (* [comment removed for export] *)
  as_owned_where : forall A m md a, ainv A m md -> owned A a ->
      al_static L a \/ heap_zone a;
  (* [comment removed for export] *)
  as_live_ok : forall A m md p n, ainv A m md -> a_live A p = Some n ->
      0 <= n /\ p mod 16 = 0 /\ 4096 <= p /\ p + n <= alloc_ceiling /\
      (p + n <= al_image_lo L \/ al_image_hi L <= p) /\
      mapped m p n /\ (forall i, 0 <= i < n -> ~ owned A (p + i));
  as_live_disjoint : forall A m md p n q k, ainv A m md ->
      a_live A p = Some n -> a_live A q = Some k -> p <> q ->
      p + n <= q \/ q + k <= p;
  as_lazy_nil : forall A m md, ainv A m md -> m_vm_lazy md = [] /\ m_halted md = None;
  (* [comment removed for export] *)
  as_budget_nonneg : forall A m md, ainv A m md -> 0 <= a_livebytes A /\ 0 <= a_nlive A;
  as_live_budget : forall A m md p n, ainv A m md -> a_live A p = Some n -> n <= a_livebytes A /\ 1 <= a_nlive A;
  (* [comment removed for export] *)
  as_frame : forall A m m' md md', ainv A m md ->
      (forall a, owned A a -> m' (wz a) = m (wz a)) ->
      (forall a, al_shared L a -> m' (wz a) = m (wz a)) ->
      (forall p n i, a_live A p = Some n -> 0 <= i < n -> m' (wz (p + i)) <> None) ->
      (forall a, heap_zone a -> m' (wz a) <> None -> m (wz a) <> None) ->
      m_vm md' = m_vm md -> m_halted md' = None ->
      ainv A m' md';

  (* [comment removed for export] *)
  as_malloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (n : Z) (T : TSet),
      ainv A m md -> mem_inv segs m ->
      (exists q k, a_live A q = Some k) ->      (* [comment removed for export] *)
      a0 = wz n -> 0 <= n < 2^32 -> n <= NREQ_CAP ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->
      tp = al_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      alloc_ceiling <= bv_unsigned sp - MALLOC_STACK ->
      mapped m (bv_unsigned sp - MALLOC_STACK) MALLOC_STACK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv segs m' -> md_frame md md' ->
          (* [comment removed for export] *)
          (r <> 0 /\ a_live A r = None /\ a_live A' r = Some n /\
           (forall q, q <> r -> a_live A' q = a_live A q) /\
           a_livebytes A' = a_livebytes A + n /\ a_nlive A' = a_nlive A + 1) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) MALLOC_STACK nowhere (blk r n) m m' ->
          realizes segs (mkCfg (mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' rom) md') T) ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc L) m rom) md) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_free_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (p n0 : Z) (T : TSet),
      ainv A m md -> mem_inv segs m ->
      a0 = wz p -> ((p = 0 /\ n0 = 0) \/ a_live A p = Some n0) ->
      tp = al_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      alloc_ceiling <= bv_unsigned sp - FREE_STACK ->
      mapped m (bv_unsigned sp - FREE_STACK) FREE_STACK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv segs m' -> md_frame md md' ->
          a_live A' p = None -> (forall q, q <> p -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - n0 -> a_nlive A' = a_nlive A - (if Z.eqb p 0 then 0 else 1) ->   (* [comment removed for export] *)
          (forall i, 0 <= i < 4 -> mrd segs m' (wz (al_errno L + i)) = mrd segs m (wz (al_errno L + i))) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) FREE_STACK (blk p n0) nowhere m m' ->
          realizes segs (mkCfg (mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' rom) md') T) ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_free_pc L) m rom) md) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_calloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (cnt sz : Z) (T : TSet),
      ainv A m md -> mem_inv segs m ->
      (exists q k, a_live A q = Some k) ->      (* [comment removed for export] *)
      a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 4076 ->
      a_livebytes A + cnt * sz <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->
      tp = al_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      alloc_ceiling <= bv_unsigned sp - CALLOC_STACK ->
      mapped m (bv_unsigned sp - CALLOC_STACK) CALLOC_STACK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv segs m' -> md_frame md md' ->
          (* [comment removed for export] *)
          (r <> 0 /\ a_live A r = None /\ a_live A' r = Some (cnt * sz) /\
           (forall q, q <> r -> a_live A' q = a_live A q) /\ all_zero m' r (cnt * sz) /\
           a_livebytes A' = a_livebytes A + cnt * sz /\ a_nlive A' = a_nlive A + 1) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) CALLOC_STACK nowhere (blk r (cnt * sz)) m m' ->
          realizes segs (mkCfg (mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' rom) md') T) ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_calloc_pc L) m rom) md) T;

  (* [comment removed for export] *)
  as_realloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (p n old : Z) (T : TSet),
      ainv A m md -> mem_inv segs m ->
      a0 = wz p -> a1 = wz n -> 0 <= n < 2^32 -> p <> 0 -> a_live A p = Some old ->
      n <= NREQ_CAP -> a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      alloc_ceiling <= bv_unsigned sp - REALLOC_STACK ->
      mapped m (bv_unsigned sp - REALLOC_STACK) REALLOC_STACK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv segs m' -> md_frame md md' ->
          (* [comment removed for export] *)
          (r <> 0 /\ a_live A' r = Some n /\ (r = p \/ (a_live A r = None /\ a_live A' p = None)) /\
           (forall q, q <> r -> q <> p -> a_live A' q = a_live A q) /\
           (forall i, 0 <= i < Z.min n old -> m' (wz (r + i)) = m (wz (p + i))) /\
           a_livebytes A' = a_livebytes A + n - old /\ a_nlive A' = a_nlive A /\
           frame_ok (owned A) (owned A') (bv_unsigned sp) REALLOC_STACK (blk p old) (blk r n) m m') ->
          realizes segs (mkCfg (mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' rom) md') T) ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_realloc_pc L) m rom) md) T;

  (* [comment removed for export] *)
  as_realloc_null_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> a0 = wz 0 ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc L) m rom) md) T ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_realloc_pc L) m rom) md) T
}.

End WithLayout.

Arguments AS {Clg L AI} : rename.
Arguments a_live {Clg L AI} : rename.
Arguments a_livebytes {Clg L AI} : rename.
Arguments a_nlive {Clg L AI} : rename.
Arguments ainv {Clg L AI} : rename.
Arguments owned {Clg L AI} : rename.
Arguments as_static_owned {Clg L AI} : rename.
Arguments as_static_where {Clg L AI} : rename.
Arguments as_shared_where {Clg L AI} : rename.
Arguments as_shared_not_static {Clg L AI} : rename.
Arguments as_errno_where {Clg L AI} : rename.
Arguments as_errno_not_static {Clg L AI} : rename.
Arguments as_layout_order {Clg L AI} : rename.
Arguments as_ro_addr_iff {Clg L AI} : rename.
Arguments as_seg_rom_outside {Clg L AI} : rename.
Arguments as_find_segment_outside {Clg L AI} : rename.
Arguments as_owned_where {Clg L AI} : rename.
Arguments as_live_ok {Clg L AI} : rename.
Arguments as_live_disjoint {Clg L AI} : rename.
Arguments as_lazy_nil {Clg L AI} : rename.
Arguments as_budget_nonneg {Clg L AI} : rename.
Arguments as_live_budget {Clg L AI} : rename.
Arguments as_frame {Clg L AI} : rename.
Arguments as_malloc_cps {Clg L AI} : rename.
Arguments as_free_cps {Clg L AI} : rename.
Arguments as_calloc_cps {Clg L AI} : rename.
Arguments as_realloc_cps {Clg L AI} : rename.
Arguments as_realloc_null_cps {Clg L AI} : rename.

(* [comment removed for export] *)
Lemma as_seg_rom_above {Clg : Ceiling} {L} {AI : AllocSpec L} : forall a : word,
  al_image_hi L <= bv_unsigned a -> seg_rom (al_segs L) a = None.
Proof. intros a H. apply as_seg_rom_outside. unfold in_image. lia. Qed.
Lemma as_find_segment_above {Clg : Ceiling} {L} {AI : AllocSpec L} : forall a : word,
  al_image_hi L <= bv_unsigned a -> find_segment (al_segs L) (bv_unsigned a) 1 = None.
Proof. intros a H. apply as_find_segment_outside. unfold in_image. lia. Qed.
