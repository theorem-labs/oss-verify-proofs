(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section IC.
Variable P : acc -> Prop.

Definition ic_W (CA : Z) : list (Z * Z) := [(CA + 84, CA + 96); (CA + 164, CA + 176); (CA + 244, CA + 256); (CA + 324, CA + 336); (CA + 404, CA + 416); (CA + 484, CA + 496); (CA + 564, CA + 576); (CA + 644, CA + 656); (CA + 724, CA + 736); (CA + 804, CA + 816); (CA + 884, CA + 896); (CA + 964, CA + 976); (CA + 1044, CA + 1056); (CA + 1124, CA + 1136); (CA + 1204, CA + 1216); (CA + 1284, CA + 1296); (CA + 1364, CA + 1376); (CA + 1444, CA + 1456); (CA + 1524, CA + 1536); (CA + 1604, CA + 1616); (CA + 1684, CA + 1696); (CA + 1764, CA + 1776); (CA + 1844, CA + 1856); (CA + 1924, CA + 1936); (CA + 2004, CA + 2016); (CA + 2084, CA + 2096); (CA + 2164, CA + 2176); (CA + 2244, CA + 2256); (CA + 2324, CA + 2336); (CA + 2404, CA + 2416); (CA + 2484, CA + 2496)].

(* [comment removed for export] *)
Definition ic_mid (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (CA : Z) (cnt : Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (CA + 1368)) a2 (Z_to_bv 64 544) a4 (Z_to_bv 64 1) (Z_to_bv 64 15) (Z_to_bv 64 1024)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x378a0) fc None m' (seg_rom bsegs)
    /\ t0 = Z_to_bv 64 16 /\ t1 = Z_to_bv 64 17 /\ t2 = Z_to_bv 64 512
    /\ munch (ic_W CA) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (CA + 80) [C4 (Z_to_bv 64 (cnt 1)); C4 (Z_to_bv 64 16); C8 (Z_to_bv 64 32)]
    /\ rw_cells bsegs m' (CA + 160) [C4 (Z_to_bv 64 (cnt 2)); C4 (Z_to_bv 64 16); C8 (Z_to_bv 64 64)]
    /\ rw_cells bsegs m' (CA + 240) [C4 (Z_to_bv 64 (cnt 3)); C4 (Z_to_bv 64 16); C8 (Z_to_bv 64 96)]
    /\ rw_cells bsegs m' (CA + 320) [C4 (Z_to_bv 64 (cnt 4)); C4 (Z_to_bv 64 16); C8 (Z_to_bv 64 128)]
    /\ rw_cells bsegs m' (CA + 400) [C4 (Z_to_bv 64 (cnt 5)); C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 160)]
    /\ rw_cells bsegs m' (CA + 480) [C4 (Z_to_bv 64 (cnt 6)); C4 (Z_to_bv 64 10); C8 (Z_to_bv 64 192)]
    /\ rw_cells bsegs m' (CA + 560) [C4 (Z_to_bv 64 (cnt 7)); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 224)]
    /\ rw_cells bsegs m' (CA + 640) [C4 (Z_to_bv 64 (cnt 8)); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 256)]
    /\ rw_cells bsegs m' (CA + 720) [C4 (Z_to_bv 64 (cnt 9)); C4 (Z_to_bv 64 6); C8 (Z_to_bv 64 288)]
    /\ rw_cells bsegs m' (CA + 800) [C4 (Z_to_bv 64 (cnt 10)); C4 (Z_to_bv 64 6); C8 (Z_to_bv 64 320)]
    /\ rw_cells bsegs m' (CA + 880) [C4 (Z_to_bv 64 (cnt 11)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 352)]
    /\ rw_cells bsegs m' (CA + 960) [C4 (Z_to_bv 64 (cnt 12)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 384)]
    /\ rw_cells bsegs m' (CA + 1040) [C4 (Z_to_bv 64 (cnt 13)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 416)]
    /\ rw_cells bsegs m' (CA + 1120) [C4 (Z_to_bv 64 (cnt 14)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 448)]
    /\ rw_cells bsegs m' (CA + 1200) [C4 (Z_to_bv 64 (cnt 15)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 480)]
    /\ rw_cells bsegs m' (CA + 1280) [C4 (Z_to_bv 64 (cnt 16)); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 512)]
    /\ rw_cells bsegs m' (CA + 1360) [C4 (Z_to_bv 64 (cnt 17)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1440) [C4 (Z_to_bv 64 (cnt 18)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1520) [C4 (Z_to_bv 64 (cnt 19)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1600) [C4 (Z_to_bv 64 (cnt 20)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1680) [C4 (Z_to_bv 64 (cnt 21)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1760) [C4 (Z_to_bv 64 (cnt 22)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1840) [C4 (Z_to_bv 64 (cnt 23)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 1920) [C4 (Z_to_bv 64 (cnt 24)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2000) [C4 (Z_to_bv 64 (cnt 25)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2080) [C4 (Z_to_bv 64 (cnt 26)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2160) [C4 (Z_to_bv 64 (cnt 27)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2240) [C4 (Z_to_bv 64 (cnt 28)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2320) [C4 (Z_to_bv 64 (cnt 29)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2400) [C4 (Z_to_bv 64 (cnt 30)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (CA + 2480) [C4 (Z_to_bv 64 (cnt 31)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition initcache_post (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (CA : Z) (cnt : Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a3 a5 a6 a7 t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x378f4) fc None m' (seg_rom bsegs)
    /\ munch (ic_W CA) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (CA + 80) [C4 (Z_to_bv 64 (cnt 1)); C4 (Z_to_bv 64 (max_count 1)); C8 (Z_to_bv 64 (class_size 1))]
    /\ rw_cells bsegs m' (CA + 160) [C4 (Z_to_bv 64 (cnt 2)); C4 (Z_to_bv 64 (max_count 2)); C8 (Z_to_bv 64 (class_size 2))]
    /\ rw_cells bsegs m' (CA + 240) [C4 (Z_to_bv 64 (cnt 3)); C4 (Z_to_bv 64 (max_count 3)); C8 (Z_to_bv 64 (class_size 3))]
    /\ rw_cells bsegs m' (CA + 320) [C4 (Z_to_bv 64 (cnt 4)); C4 (Z_to_bv 64 (max_count 4)); C8 (Z_to_bv 64 (class_size 4))]
    /\ rw_cells bsegs m' (CA + 400) [C4 (Z_to_bv 64 (cnt 5)); C4 (Z_to_bv 64 (max_count 5)); C8 (Z_to_bv 64 (class_size 5))]
    /\ rw_cells bsegs m' (CA + 480) [C4 (Z_to_bv 64 (cnt 6)); C4 (Z_to_bv 64 (max_count 6)); C8 (Z_to_bv 64 (class_size 6))]
    /\ rw_cells bsegs m' (CA + 560) [C4 (Z_to_bv 64 (cnt 7)); C4 (Z_to_bv 64 (max_count 7)); C8 (Z_to_bv 64 (class_size 7))]
    /\ rw_cells bsegs m' (CA + 640) [C4 (Z_to_bv 64 (cnt 8)); C4 (Z_to_bv 64 (max_count 8)); C8 (Z_to_bv 64 (class_size 8))]
    /\ rw_cells bsegs m' (CA + 720) [C4 (Z_to_bv 64 (cnt 9)); C4 (Z_to_bv 64 (max_count 9)); C8 (Z_to_bv 64 (class_size 9))]
    /\ rw_cells bsegs m' (CA + 800) [C4 (Z_to_bv 64 (cnt 10)); C4 (Z_to_bv 64 (max_count 10)); C8 (Z_to_bv 64 (class_size 10))]
    /\ rw_cells bsegs m' (CA + 880) [C4 (Z_to_bv 64 (cnt 11)); C4 (Z_to_bv 64 (max_count 11)); C8 (Z_to_bv 64 (class_size 11))]
    /\ rw_cells bsegs m' (CA + 960) [C4 (Z_to_bv 64 (cnt 12)); C4 (Z_to_bv 64 (max_count 12)); C8 (Z_to_bv 64 (class_size 12))]
    /\ rw_cells bsegs m' (CA + 1040) [C4 (Z_to_bv 64 (cnt 13)); C4 (Z_to_bv 64 (max_count 13)); C8 (Z_to_bv 64 (class_size 13))]
    /\ rw_cells bsegs m' (CA + 1120) [C4 (Z_to_bv 64 (cnt 14)); C4 (Z_to_bv 64 (max_count 14)); C8 (Z_to_bv 64 (class_size 14))]
    /\ rw_cells bsegs m' (CA + 1200) [C4 (Z_to_bv 64 (cnt 15)); C4 (Z_to_bv 64 (max_count 15)); C8 (Z_to_bv 64 (class_size 15))]
    /\ rw_cells bsegs m' (CA + 1280) [C4 (Z_to_bv 64 (cnt 16)); C4 (Z_to_bv 64 (max_count 16)); C8 (Z_to_bv 64 (class_size 16))]
    /\ rw_cells bsegs m' (CA + 1360) [C4 (Z_to_bv 64 (cnt 17)); C4 (Z_to_bv 64 (max_count 17)); C8 (Z_to_bv 64 (class_size 17))]
    /\ rw_cells bsegs m' (CA + 1440) [C4 (Z_to_bv 64 (cnt 18)); C4 (Z_to_bv 64 (max_count 18)); C8 (Z_to_bv 64 (class_size 18))]
    /\ rw_cells bsegs m' (CA + 1520) [C4 (Z_to_bv 64 (cnt 19)); C4 (Z_to_bv 64 (max_count 19)); C8 (Z_to_bv 64 (class_size 19))]
    /\ rw_cells bsegs m' (CA + 1600) [C4 (Z_to_bv 64 (cnt 20)); C4 (Z_to_bv 64 (max_count 20)); C8 (Z_to_bv 64 (class_size 20))]
    /\ rw_cells bsegs m' (CA + 1680) [C4 (Z_to_bv 64 (cnt 21)); C4 (Z_to_bv 64 (max_count 21)); C8 (Z_to_bv 64 (class_size 21))]
    /\ rw_cells bsegs m' (CA + 1760) [C4 (Z_to_bv 64 (cnt 22)); C4 (Z_to_bv 64 (max_count 22)); C8 (Z_to_bv 64 (class_size 22))]
    /\ rw_cells bsegs m' (CA + 1840) [C4 (Z_to_bv 64 (cnt 23)); C4 (Z_to_bv 64 (max_count 23)); C8 (Z_to_bv 64 (class_size 23))]
    /\ rw_cells bsegs m' (CA + 1920) [C4 (Z_to_bv 64 (cnt 24)); C4 (Z_to_bv 64 (max_count 24)); C8 (Z_to_bv 64 (class_size 24))]
    /\ rw_cells bsegs m' (CA + 2000) [C4 (Z_to_bv 64 (cnt 25)); C4 (Z_to_bv 64 (max_count 25)); C8 (Z_to_bv 64 (class_size 25))]
    /\ rw_cells bsegs m' (CA + 2080) [C4 (Z_to_bv 64 (cnt 26)); C4 (Z_to_bv 64 (max_count 26)); C8 (Z_to_bv 64 (class_size 26))]
    /\ rw_cells bsegs m' (CA + 2160) [C4 (Z_to_bv 64 (cnt 27)); C4 (Z_to_bv 64 (max_count 27)); C8 (Z_to_bv 64 (class_size 27))]
    /\ rw_cells bsegs m' (CA + 2240) [C4 (Z_to_bv 64 (cnt 28)); C4 (Z_to_bv 64 (max_count 28)); C8 (Z_to_bv 64 (class_size 28))]
    /\ rw_cells bsegs m' (CA + 2320) [C4 (Z_to_bv 64 (cnt 29)); C4 (Z_to_bv 64 (max_count 29)); C8 (Z_to_bv 64 (class_size 29))]
    /\ rw_cells bsegs m' (CA + 2400) [C4 (Z_to_bv 64 (cnt 30)); C4 (Z_to_bv 64 (max_count 30)); C8 (Z_to_bv 64 (class_size 30))]
    /\ rw_cells bsegs m' (CA + 2480) [C4 (Z_to_bv 64 (cnt 31)); C4 (Z_to_bv 64 16); C8 (Z_to_bv 64 64)].

(* [comment removed for export] *)
Lemma initcache_walk_lo :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (CA : Z) (cnt : Z -> Z),
  mem_inv bsegs m -> (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) -> CA + 2584 <= alloc_ceiling -> CA mod 8 = 0 ->
  (forall i, 0 <= cnt i < 2^32) ->
  rw_cells bsegs m (CA + 80) [C4 (Z_to_bv 64 (cnt 1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 160) [C4 (Z_to_bv 64 (cnt 2)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 240) [C4 (Z_to_bv 64 (cnt 3)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 320) [C4 (Z_to_bv 64 (cnt 4)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 400) [C4 (Z_to_bv 64 (cnt 5)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 480) [C4 (Z_to_bv 64 (cnt 6)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 560) [C4 (Z_to_bv 64 (cnt 7)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 640) [C4 (Z_to_bv 64 (cnt 8)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 720) [C4 (Z_to_bv 64 (cnt 9)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 800) [C4 (Z_to_bv 64 (cnt 10)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 880) [C4 (Z_to_bv 64 (cnt 11)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 960) [C4 (Z_to_bv 64 (cnt 12)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1040) [C4 (Z_to_bv 64 (cnt 13)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1120) [C4 (Z_to_bv 64 (cnt 14)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1200) [C4 (Z_to_bv 64 (cnt 15)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1280) [C4 (Z_to_bv 64 (cnt 16)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1360) [C4 (Z_to_bv 64 (cnt 17)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1440) [C4 (Z_to_bv 64 (cnt 18)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1520) [C4 (Z_to_bv 64 (cnt 19)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1600) [C4 (Z_to_bv 64 (cnt 20)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1680) [C4 (Z_to_bv 64 (cnt 21)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1760) [C4 (Z_to_bv 64 (cnt 22)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1840) [C4 (Z_to_bv 64 (cnt 23)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 1920) [C4 (Z_to_bv 64 (cnt 24)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2000) [C4 (Z_to_bv 64 (cnt 25)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2080) [C4 (Z_to_bv 64 (cnt 26)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2160) [C4 (Z_to_bv 64 (cnt 27)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2240) [C4 (Z_to_bv 64 (cnt 28)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2320) [C4 (Z_to_bv 64 (cnt 29)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2400) [C4 (Z_to_bv 64 (cnt 30)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (CA + 2480) [C4 (Z_to_bv 64 (cnt 31)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  (forall a n, CA <= a -> a + Z.of_nat n <= CA + 2584 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (ic_mid ra sp gp tp s0 s1 (Z_to_bv 64 CA) a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m CA cnt)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37858) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until cnt. intros MI CA1 CA2 CA8 CNT R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 PCA.
  aceil.
  assert (MU : munch (ic_W CA) m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold ic_W in MU.
  Ltac to_head := repeat (lazymatch goal with |- evtA _ _ _ (MS _ _ (Z_to_bv 64 227488) _ _ _ _) => fail | _ => cstep end).
  to_head.             (* [comment removed for export] *)
  do 16 (cstep; to_head).   (* [comment removed for export] *)
  Ltac lit_row H :=
    lazymatch type of H with rw_cells _ _ _ [_; C4 (Z_to_bv 64 ?e); C8 (Z_to_bv 64 ?f)] =>
      let ve := eval vm_compute in e in let vf := eval vm_compute in f in
      replace e with ve in H by (vm_compute; reflexivity); replace f with vf in H by (vm_compute; reflexivity) end.
  lit_row R1. lit_row R2. lit_row R3. lit_row R4. lit_row R5. lit_row R6. lit_row R7. lit_row R8. lit_row R9. lit_row R10.
  lit_row R11. lit_row R12. lit_row R13. lit_row R14. lit_row R15. lit_row R16.
  apply evtA_done. unfold ic_mid. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [lazymatch goal with |- MS ?r _ _ _ _ _ _ = _ => reflexivity end|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try assumption.
  all: lazymatch goal with
       | |- rw_cells _ _ _ [_; C4 (Z_to_bv 64 ?e); C8 (Z_to_bv 64 ?f)] =>
           let ve := eval vm_compute in e in change e with ve; let vf := eval vm_compute in f in change f with vf; assumption
       | |- munch _ _ _ => unfold ic_W; assumption
       end.
Time Qed.
End IC.
End RC__1.
