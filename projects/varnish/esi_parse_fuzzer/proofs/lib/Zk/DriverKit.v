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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Record InitLayout := mkInitLayout {
  il_libc : Z;        (* [comment removed for export] *)
  il_static_lo : Z;   (* [comment removed for export] *)
  il_static_hi : Z;   (* [comment removed for export] *)
  il_got : Z;         (* [comment removed for export] *)
  il_guard : Z;       (* [comment removed for export] *)
  il_resv : list (Z * Z)  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition le8 (v : Z) (i : Z) : byte := Z_to_bv 8 ((v / 2 ^ (8 * i)) mod 256).
(* [comment removed for export] *)
Definition cell8 (m : mem) (a v : Z) : Prop := forall i, 0 <= i < 8 -> m (wz (a + i)) = Some (le8 v i).
(* [comment removed for export] *)
Definition cell8_img (m : mem) (rom : mem) (a v : Z) : Prop :=
  forall i, 0 <= i < 8 -> m (wz (a + i)) = Some (le8 v i) \/ (m (wz (a + i)) = None /\ rom (wz (a + i)) = Some (le8 v i)).
(* [comment removed for export] *)
Definition zero_img (m : mem) (rom : mem) (a : Z) : Prop :=
  m (wz a) = Some (Z_to_bv 8 0) \/ (m (wz a) = None /\ (rom (wz a) = Some (Z_to_bv 8 0) \/ rom (wz a) = None)).

Definition AT_RANDOM : Z := 25.

(* [comment removed for export] *)
Definition auxv_at (m : mem) (av rp : Z) : Prop :=
  exists (pairs : list (Z * Z)) (k : nat),
    0 <= av /\ av mod 8 = 0 /\ av + 16 * (Z.of_nat (length pairs) + 1) <= 2^64 /\
    (forall j key val, nth_error pairs j = Some (key, val) ->
        0 < key < 2^64 /\ 0 <= val < 2^64 /\
        cell8 m (av + 16 * Z.of_nat j) key /\ cell8 m (av + 16 * Z.of_nat j + 8) val) /\
    cell8 m (av + 16 * Z.of_nat (length pairs)) 0 /\
    nth_error pairs k = Some (AT_RANDOM, rp) /\
    (forall j key val, (j < k)%nat -> nth_error pairs j = Some (key, val) -> key <> AT_RANDOM) /\
    0 <= rp /\ rp + 16 <= 2^64 /\ (forall i, 0 <= i < 16 -> m (wz (rp + i)) <> None).

Section WithLayouts.
Context {Clg : Ceiling} (L : AllocLayout) (IL : InitLayout).   (* [comment removed for export] *)
Let segs := al_segs L.
Let rom := al_rom L.

(* [comment removed for export] *)
Definition init_ok (lo : Z) (m : mem) (md : Model) : Prop :=
     (* [comment removed for export] *)
     (forall a, il_static_lo IL <= a < il_static_hi IL -> zero_img m rom a)
     (* [comment removed for export] *)
  /\ zero_img m rom (il_libc IL + 3)
  /\ cell8 m (il_libc IL + 48) 4096
     (* [comment removed for export] *)
  /\ (exists av rnd x3 x4 x5 hw x6 x11 x12 x23,
         cell8 m (il_libc IL + 8) av /\ 0 <= av /\ av mod 8 = 0 /\ av + 160 <= 2^64 /\ 0 <= rnd /\ rnd + 16 <= 2^64
      /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= hw < 2^64 /\ 0 <= x6 < 2^64
      /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64
      /\ cell8 m av 3 /\ cell8 m (av + 8) x3 /\ cell8 m (av + 16) 4 /\ cell8 m (av + 24) x4
      /\ cell8 m (av + 32) 5 /\ cell8 m (av + 40) x5 /\ cell8 m (av + 48) 16 /\ cell8 m (av + 56) hw
      /\ cell8 m (av + 64) 6 /\ cell8 m (av + 72) x6
      /\ cell8 m (av + 80) 11 /\ cell8 m (av + 88) x11 /\ cell8 m (av + 96) 12 /\ cell8 m (av + 104) x12
      /\ cell8 m (av + 112) 23 /\ cell8 m (av + 120) x23 /\ cell8 m (av + 128) 25 /\ cell8 m (av + 136) rnd
      /\ cell8 m (av + 144) 0 /\ cell8 m (av + 152) 0
      /\ (forall i, 0 <= i < 16 -> m (wz (rnd + i)) <> None)
      /\ lo <= av /\ lo <= rnd)
     (* [comment removed for export] *)
  /\ cell8_img m rom (il_got IL) (il_guard IL)
  /\ (exists g, 0 <= g < 2^64 /\ cell8 m (il_guard IL) g)
     (* [comment removed for export] *)
  /\ (forall a, heap_zone L a -> m (wz a) = None)
     (* [comment removed for export] *)
  /\ vm_maps (m_vmmaps md) = [] /\ vm_noaccess (m_vmmaps md) = []
  /\ m_vm_lazy md = [] /\ m_vm_materialized md = []
  /\ vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md)
  /\ al_image_hi L <= bv_unsigned (vm_start_brk (m_vmmaps md))
     (* [comment removed for export] *)
  /\ map (fun e => (bv_unsigned (fst e), bv_unsigned (snd e))) (vm_reserved (m_vmmaps md)) = il_resv IL
  /\ bv_unsigned (vm_start_brk (m_vmmaps md)) + 4 * 4096 <= alloc_ceiling
  /\ bv_unsigned (vm_start_brk (m_vmmaps md)) mod 4096 = 0
  /\ bw_limit (vm_limit (m_vmmaps md))   (* [comment removed for export] *)
  /\ m_halted md = None
     (* [comment removed for export] *)
  /\ ceil_ok md.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Class DriverKit {AI : AllocSpec L} := {
  (* [comment removed for export] *)
  dk_init_frame : forall lo m m' md md',
      init_ok lo m md ->
      (forall a, il_static_lo IL <= a < il_static_hi IL -> m' (wz a) = m (wz a)) ->
      (forall a, il_libc IL <= a < il_libc IL + 56 -> m' (wz a) = m (wz a)) ->
      (forall a, il_got IL <= a < il_got IL + 8 -> m' (wz a) = m (wz a)) ->
      (forall a, il_guard IL <= a < il_guard IL + 8 -> m' (wz a) = m (wz a)) ->
      (forall a, lo <= a -> m' (wz a) = m (wz a)) ->
      (forall a, heap_zone L a -> m' (wz a) = None) ->
      m_vm md' = m_vm md -> m_halted md' = None ->
      init_ok lo m' md';

  (* [comment removed for export] *)
  dk_malloc_first_nf :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (lo : Z) (n : Z) (T : TSet),
      init_ok lo m md -> bv_unsigned sp <= lo -> mem_inv segs m ->
      a0 = wz n -> n = 65536 ->
      tp = al_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      alloc_ceiling <= bv_unsigned sp - MALLOC_STACK ->
      mapped m (bv_unsigned sp - MALLOC_STACK) MALLOC_STACK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          r <> 0 ->
          ainv A' m' md' -> mem_inv segs m' -> md_frame md md' ->
          a_live A' r = Some n -> (forall q, q <> r -> a_live A' q = None) ->
          a_livebytes A' = n -> a_nlive A' = 1 ->
          frame_ok L (al_static L) (owned A') (bv_unsigned sp) MALLOC_STACK nowhere (blk r n) m m' ->
          realizes segs (mkCfg (mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' rom) md') T) ->
      realizes segs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc L) m rom) md) T
}.

End WithLayouts.

Arguments dk_init_frame {Clg L IL AI DK} : rename.
Arguments dk_malloc_first_nf {Clg L IL AI DK} : rename.

(* [comment removed for export] *)
Definition InitP0 : InitLayout :=
  {| il_libc := 0x623e8; il_static_lo := 0x62458; il_static_hi := 0x62804; il_got := 0x30428; il_guard := 0x623c8;
     il_resv := [(0x10000, 0x7000); (0x17000, 0x19000); (0x30000, 0x1000); (0x31000, 0x32000)] |}.
Definition InitPU : InitLayout :=
  {| il_libc := 0x62788; il_static_lo := 0x627f8; il_static_hi := 0x62ba4; il_got := 0x307c8; il_guard := 0x62768;
     il_resv := [(0x10000, 0x7000); (0x17000, 0x19000); (0x30000, 0x1000); (0x31000, 0x33000)] |}.

(* [comment removed for export] *)
