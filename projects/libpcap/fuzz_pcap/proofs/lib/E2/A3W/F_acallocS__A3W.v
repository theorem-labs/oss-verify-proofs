(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc2s.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W.
From Ltac2 Require Ltac2.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_acallocS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_ammapz OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation CALLOCS_STACK := 512 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition calloc_sec_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      (* [comment removed for export] *)
  ra = Z_to_bv 64 0x33ea8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab020 [CB 32 jstats] ->
  rw_cells asegs m 0xab040 [CB 512 jbsl] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab258 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 2).
Variable K2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 4).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 41).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 47).
Variable sorted : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 48).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 49).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 50).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 51).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 52).
#[using="Type"] Lemma calloc_sec_spec__body : ltac:(let T := type of (fun (h : calloc_sec_spec__stmt) => h RNG R K K2 Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (K2, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (t, (PA, (nres, (nsec, (lo, (sj, (sorted, (jstats, (jbsl, (jglob, jslot))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC DPL RIMG RTLS RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.                                                     (* [comment removed for export] *)
  do 3 zstep.                                                   (* [comment removed for export] *)
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }   (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);   (* [comment removed for export] *)
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0 /\ tclr a (sec_map_size n)) by
      (intros a' Ha'; (nd_pre (FROK a' Ha') 7%nat; intros Y1 Y1' Y2 Y3 Y4 Y5 Y6; nd_post); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|]; split; [| exact Y6];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.
  (* [comment removed for export] *)
  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; (nd_pre LP0 27%nat; intros FPLE BW A0 A1 A2 MUL WML MIL STL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post); unfold AINSTANCE in A2, MUL.
  all: (pose proof (ablk_lin _ _ A1) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post); unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG; apply (rng_fp_le _ _ _ _ FPLE) in RTLS.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x38430)) with (Z_to_bv 64 0x38430 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.                                 (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.                                                (* [comment removed for export] *)
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x33ea8)) with (Z_to_bv 64 0x33ea8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End Zd1.
#[using="Type"] Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      (* [comment removed for export] *)
  ra = Z_to_bv 64 0x33ea8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab020 [CB 32 jstats] ->
  rw_cells asegs m 0xab040 [CB 512 jbsl] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab258 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Proof. exact calloc_sec_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_ammapz.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation CALLOCS_STACK := 512 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition calloc_sec_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      (* [comment removed for export] *)
  ra = Z_to_bv 64 0x33f10 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab420 [CB 32 jstats] ->
  rw_cells asegs m 0xab440 [CB 512 jbsl] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab658 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 2).
Variable K2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 4).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 41).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 47).
Variable sorted : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 48).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 49).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 50).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 51).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'calloc_sec_spec__stmt 52).
#[using="Type"] Lemma calloc_sec_spec__body : ltac:(let T := type of (fun (h : calloc_sec_spec__stmt) => h RNG R K K2 Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (K2, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (t, (PA, (nres, (nsec, (lo, (sj, (sorted, (jstats, (jbsl, (jglob, jslot))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC DPL RIMG RTLS RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.                                                     (* [comment removed for export] *)
  do 3 zstep.                                                   (* [comment removed for export] *)
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }   (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);   (* [comment removed for export] *)
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0 /\ tclr a (sec_map_size n)) by
      (intros a' Ha'; (nd_pre (FROK a' Ha') 7%nat; intros Y1 Y1' Y2 Y3 Y4 Y5 Y6; nd_post); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|]; split; [| exact Y6];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.
  (* [comment removed for export] *)
  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; (nd_pre LP0 27%nat; intros FPLE BW A0 A1 A2 MUL WML MIL STL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post); unfold AINSTANCE in A2, MUL.
  all: (pose proof (ablk_lin _ _ A1) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post); unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG; apply (rng_fp_le _ _ _ _ FPLE) in RTLS.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x38498)) with (Z_to_bv 64 0x38498 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.                                 (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.                                                (* [comment removed for export] *)
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x33f10)) with (Z_to_bv 64 0x33f10 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End Zd1.
#[using="Type"] Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      (* [comment removed for export] *)
  ra = Z_to_bv 64 0x33f10 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab420 [CB 32 jstats] ->
  rw_cells asegs m 0xab440 [CB 512 jbsl] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab658 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Proof. exact calloc_sec_spec__body. Qed.
End CANSEC1.
End TwB.
End F_acallocS.

(* [comment removed for export] *)
Module F_amalloc_tailS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc2s. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc2s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3s.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma premap_cells_frame_b : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI, AIMG_LO in HW.
  assert (D : forall A k, 0 <= k -> 0x10000 <= A -> A + k <= 0x603000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA0 HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.
#[using="Type"] Lemma skipn_repeat {A} (x : A) : forall k n, skipn k (repeat x n) = repeat x (n - k).
Proof. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
#[using="Type"] Lemma firstn_repeat' {A} (x : A) : forall k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros16_hdr : forall m A, fill_at m A 16 0 ->
  rw_cells asegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cut : forall m A len k v, fill_at m A len v -> 0 <= k <= len ->
  fill_at m A k v /\ fill_at m (A + k) (len - k) v.
Proof. intros m A len k v H HK. replace len with (k + (len - k)) in H by lia. apply fill_split in H; [exact H| lia| lia]. Qed.

Section WithDepot.
Variable DI : ADepotIface.
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation mallocS_W L sp t a ms :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 2800, t + 3168); (a + 4096, a + ms); (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_postS (L : alayout) (RNG : footprint) (sp : word) (n t a ms nsec lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) (id : Z) (sj' : list word) : Prop :=
  let AB := a + 4096 in let UB := a + 6144 in
     fp_le RNG RNG'
  /\ munch (mallocS_W L sp t a ms) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ 0 < id < 2^31
  /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)]
  /\ junk_at m' (a + 32) (4096 - 32)
  /\ rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]
  /\ junk_at m' (AB + 16) (2048 - 32)
  /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
  /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]
  /\ junk_at m' (UB + n) (ms - 6144 - n)
  /\ fill_at m' (shad a) 768 0xfa
  /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)]
  /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
  /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

Definition malloc_tail_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t a ms nsec SB lo sz : Z) (fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk asegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= ctx \/ ctx + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                      CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))] ->
  rw_cells asegs m AB [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))] ->
  fill_at m (shad a) 512 0xfa -> fill_at m (shad a + 512) (size / 8) 0 -> fill_at m (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1400c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  (exists sj, u64arr asegs m (t + 2800) sj /\ length sj = 46%nat) ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  tclr a ms ->      (* [comment removed for export] *)
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33bd8)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x56488)] ->
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG' m' id sj' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     malloc_postS L RNG sp n t a ms nsec lo m RNG' m' id sj' ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 8).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 19).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 20).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 21).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 22).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 23).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 24).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 25).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 26).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 27).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 28).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 29).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 30).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 31).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 32).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 33).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 34).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 35).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 36).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 37).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 38).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 39).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 40).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 41).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 42).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 43).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 44).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 45).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 46).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 47).
Variable a : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 48).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 49).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 50).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 51).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 52).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 53).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 54).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 55).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 56).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 57).
#[using="PR"] Lemma malloc_tail_sec__body : ltac:(let T := type of (fun (h : malloc_tail_sec__stmt) => h L RNG R k Q ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m n t a ms nsec SB lo sz fr0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (s0i, (F, (fc, (m, (n, (t, (a, (ms, (nsec, (SB, (lo, (sz, (fr0, (junk2, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS
         HDRP ZB SHF1 SHZ SHF2 PC PMC RELRO PP I32 I64 FLG HK MCS CF34 TI TK T88 TSD CT CX8 TT0 [sj [STATS LSJ]]
         CX0 CX1 CXS T0 T1 TS CT2 DTN DTS DCN DCS XTNO XTST XTA N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RTLS RSTK RCTX RT RNO RST RA RSA NI SI KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, AMALLOC_PC in *.
  word_range sp SPR.
  (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8
               /\ needed_size n / 8 = 512 + granules n
               /\ granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1)
               /\ shlen n = shlen (n - n mod 8)).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. rewrite NSE, RSE.
    repeat split; try (clear -AAL N; Z.div_mod_to_equations; lia).
    all: destruct (Z.eqb_spec (n mod 8) 0) as [E8|E8]; clear -AAL N E8; Z.div_mod_to_equations; lia. }
  (nd_pre SG 9%nat; intros SG1 SG2 SG5 SG6 SG8 SG9 SGN SGG SGS; nd_post).
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1, NI, SI.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).   (* [comment removed for export] *)
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb SHB1 SHB2; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post). (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (MS8 : 9216 <= ms / 8 /\ 6144 + n <= ms) by (clear -MSB MSR NSE RSR; Z.div_mod_to_equations; lia). destruct MS8 as [MS8 MS6].
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2. box DJSB.
  (* [comment removed for export] *)
  pose proof HDRP as HP0. rw_split HP0 4%nat HDR4 PGJ.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)])) with (a + 32) in PGJ by (cbn; lia).
  assert (ZBF : fill_at m (a + 4096) (ms - 4096) 0) by exact ZB. clear ZB.
  destruct (fill_cut m (a + 4096) (ms - 4096) 16 0 ZBF ltac:(clear -MSR NSE RSR N; lia)) as [ZAB Z1].
  destruct (fill_cut m (a + 4096 + 16) (ms - 4096 - 16) 2016 0 Z1 ltac:(clear -MSR NSE RSR N; lia)) as [ZJ1 Z2]. clear Z1.
  replace (a + 4096 + 16 + 2016) with (a + 6128) in Z2 by lia.
  destruct (fill_cut m (a + 6128) (ms - 4096 - 16 - 2016) 16 0 Z2 ltac:(clear -MSR NSE RSR N; lia)) as [ZH Z3]. clear Z2.
  replace (a + 6128 + 16) with (a + 6144) in Z3 by lia.
  destruct (fill_cut m (a + 6144) (ms - 4096 - 16 - 2016 - 16) n 0 Z3 ltac:(clear -MSR NSE RSR N; lia)) as [ZU ZT]. clear Z3.
  replace (ms - 4096 - 16 - 2016 - 16 - n) with (ms - 6144 - n) in ZT by lia.
  pose proof (zeros16_hdr m (a + 6128) ZH) as HDR. clear ZH.
  (nd_pre (c8c8_of_junk m (a + 4096) (fill_is_junk _ _ _ _ ZAB)) 3%nat; intros j1 j2 LH; nd_post).
  (* [comment removed for export] *)
  rewrite SGN in SHZ, SHF2.
  destruct (fill_cut m (shad a + 512) (512 + granules n) 256 0 SHZ ltac:(clear -SG5; lia)) as [SHL S1]. clear SHZ.
  replace (shad a + 512 + 256) with (shad (a + 6144)) in S1 by (rewrite SG2; lia).
  destruct (fill_cut m (shad (a + 6144)) (512 + granules n - 256) (shlen (n - n mod 8)) 0 S1 ltac:(clear -SG5 SG6; lia)) as [SHU S2]. clear S1.
  destruct (fill_cut m (shad (a + 6144) + shlen (n - n mod 8)) (512 + granules n - 256 - shlen (n - n mod 8)) (granules n - shlen (n - n mod 8)) 0 S2
              ltac:(clear -SG5 SG6; lia)) as [SHP S3]. clear S2.
  replace (shad (a + 6144) + shlen (n - n mod 8) + (granules n - shlen (n - n mod 8))) with (shad (a + 6144) + granules n) in S3 by lia.
  assert (SHT : junk_at m (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n)).
  { replace (ms / 8 - 768 - granules n) with ((512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))) + (ms / 8 - 512 - (512 + granules n)))
      by (clear -SG5 SG6; lia).
    apply junk_merge; [apply (fill_is_junk _ _ _ 0); exact S3 | apply (fill_is_junk _ _ _ 0xfa) | clear -SG5 SG6; lia | clear -SG5 SG6 MSE MSM SGN NSE RSE N; Z.div_mod_to_equations; lia].
    replace (shad (a + 6144) + granules n + (512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))))
      with (shad a + 512 + (512 + granules n)) by (rewrite SG2; clear -SG5 SG6; lia). exact SHF2. }
  clear S3 SHF2.
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]).
  { intros NE. apply c1_of_fill; [lia|]. rewrite SGG in SHP. destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [exfalso; exact (NE E)|].
    replace (shlen (n - n mod 8) + 1 - shlen (n - n mod 8)) with 1 in SHP by lia. exact SHP. }
  clear SHP.
  rewrite <- SG1 in SHL.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply (allocBC_sec DI PR L RNG R k Q spA gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n (bv_unsigned sp + -2128) t a ms nsec SB lo sz 353308 tb tr fr0
            (Z_to_bv 64 0x33bd8) s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11).
  all: try lazymatch goal with
       | |- forall _, _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PMC
       | |- ADEPOT _ _ _ => exact DEP
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- u64arr _ _ _ _ => exact TB
       | |- _ \/ _ => first [unboxed DJSB | unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed CT2]
       | |- exists junk, _ => exact SHT
       | |- ~ _ -> _ => exact SHP1
       | |- rw_cells _ _ (shad (_ + 4096)) _ => exact SHL
       | |- rw_cells _ _ (shad (_ + 6144)) _ => exact SHU
       | |- rw_cells _ _ (_ + 6128) _ => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR4
       | |- rng _ _ _ => solve_rng
       | |- is_primary _ = _ => exact PRIM
       | |- _ = sec_map_size _ => exact HMS
       end.
  all: try eassumption.
  all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI SB0 SBH CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 SZB S47 MSB ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
  all: match goal with |- forall _, _ => idtac | |- ?G => idtac "REMBC" G end.
  (* [comment removed for export] *)
  intros RNG' m2 id rax t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b PB IDR.
  unfold allocBC_postS in PB.
  (nd_pre PB 33%nat; intros id_ raB t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s6_ t3_ t4_ t5_ t6_ EMS FPLE MUb WMb MIb STb IDR_ HDRb SHFb SHUb SHPb SHTb DEPb PCb PMCb; nd_post).
  clear EMS IDR id. rename id_ into id. rename IDR_ into IDR.
  rewrite ?HspA in MUb.
  replace (Z_to_bv 64 (a + 6128)) with (Z_to_bv 64 (a + 6144 + -16)) by (f_equal; lia).
  replace (a + 6128) with (a + 6144 + -16) in HDRb by lia.
  pose proof (hdr_b1_mid_range 0 ltac:(lia)) as B1M.
  assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
  assert (RIMG' : rng_aimg RNG') by (eapply rng_fp_le; [exact FPLE| exact RIMG]).
  assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).      (* [comment removed for export] *)
  assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX]).
  assert (RT' : rng RNG' t 4096) by (eapply rng_fp_le; [exact FPLE| exact RT]).
  assert (RA' : rng RNG' a ms) by (eapply rng_fp_le; [exact FPLE| exact RA]).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; first [ solve [ clear -Y Y0 Y1 LSJ T0 T1 CEIL LO SPR TBND TBNDa TBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport TSD MUb WMb ltac:(lia).      (* [comment removed for export] *)
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; first [ solve [ clear -Y Y0 Y1 CX0 CX1 CEIL LO SPR CBND CBNDa CBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport FLG MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia). xport MCS MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport CF34 MUb WMb ltac:(lia).
  pose proof PCb as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  assert (ZU2 : fill_at m2 (a + 6144) n 0).
  { eapply fill_frame; [exact ZU | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  xport FR16 MUb WMb ltac:(lia). xport SS MUb WMb ltac:(lia). xport FRS MUb WMb ltac:(lia).
  xport TB MUb WMb ltac:(rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 (a + 4096) [C8 j1; C8 j2]).
  { intros _. xport LH MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia). exact LH. }
  clear LH.
  (* [comment removed for export] *)
  xport HDR4 MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  xport PGJ MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  assert (ZJ2 : fill_at m2 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (ZT2 : fill_at m2 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT | exact MUb | exact WMb |]. intros Hp. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 Hp SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (SHF12 : fill_at m2 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 N0 R0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI SG1 SG2. dlia. }
  clear ZU ZJ1 ZT SHF1 SHL SHU SHP1 SHT HDR HDRP.
  (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (allocD_sec L RNG' spA gp tp F fc m2 n t (a + 4096) (a + 6144) lo 0 (hdr_b1_mid 0) id (bv_unsigned sp + -2128) sj
              (repeat (Z_to_bv 8 0) (Z.to_nat n)) j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => ub DJT; clear -Y N MSR NSE RSR; lia
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- rw_cells _ _ (_ + 6144) [CB _ _] => exact ZU2
         | |- is_primary _ = _ => exact PRIM
         | |- _ = _ + rz_size _ => rewrite RZ; lia
         | |- _ mod 16 = 0 => clear -AAL; Z.div_mod_to_equations; lia
         end.
    all: try eassumption.
    all: try (eapply ablk_sub; [exact ALO | clear; lia | clear -N MSR NSE RSR MSB; lia]).   (* [comment removed for export] *)
    all: try (eapply tclr_sub; [exact XTA | clear; lia | clear -N MSR NSE RSR MSB; lia]).      (* [comment removed for export] *)
    all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 S47 MSB MSR NSE RSR B1M IDR ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  specialize (LHd ltac:(rewrite RZ; lia)).
  xport FR16 MUd WMd ltac:(lia). xport SS MUd WMd ltac:(lia). xport FRS MUd WMd ltac:(lia). xport TB MUd WMd ltac:(rewrite LTB; lia).
  xport HDR4 MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  xport PGJ MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  assert (ZJ3 : fill_at m3 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ2 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR ALO1. dlia. }
  assert (ZT3 : fill_at m3 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT2 | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Hp ALO1. dlia. }
  assert (SHF13 : fill_at m3 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF12 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SHFb3 : fill_at m3 (shad a + 512) 256 0xfa).
  { eapply fill_frame; [exact SHFb | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SGX : shad (a + 6144) + granules n + (ms / 8 - 768 - granules n) <= 0x10007fff8000 /\ 0 <= ms / 8 - 768 - granules n)
    by (rewrite SG2; clear -SHB2 SG9 MSR NSE RSE N; Z.div_mod_to_equations; lia).
  destruct SGX as [SGX1 SGX2].
  xport SHUb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia). exact SHPb. }
  assert (SHTd : fill_at m3 (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n) 0xfa).
  { eapply fill_frame; [exact SHTb | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 Hp ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx; ub DTN; ub DTS; ub DJN; ub DJS; clear -Y Y0 Y1 Y2 Hx HspA SPR CEIL LO N AAL ALO AHI MSB MS6 T0 TS T1 N0 N1 R0 R1 ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb; lia|]). apply Forall_nil. }
  assert (PCd : poison_cells m3).
  { eapply poison_cells_frame_b; [exact PCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  assert (PMCd : premap_cells m3).
  { eapply premap_cells_frame_b; [exact PMCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  clear SHF12 SHFb ZJ2 ZT2 ZU2 SHPb SHTb DEPb PCb PMCb.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x33bd8)) with (Z_to_bv 64 0x33bd8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG' sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG' | exact RTLS' | solve_rng ]. }
  cbv beta. intros ms5 PCC. (nd_pre PCC 2%nat; intros m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUc WMc MIc STc; nd_post).
  (* [comment removed for export] *)
  xport STATSd MUc WMc ltac:(exact I). xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport LHd MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport PGJ MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I).
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (F5 : forall A l v, fill_at m3 A l v -> fill_at m5 A l v).
  { intros A l v H. eapply fill_frame; [exact H | exact MUc | exact WMc | intros _; exact I]. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PCX5 : poison_cells m5). { eapply poison_cells_frame; [exact PCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PMC5 : premap_cells m5). { eapply premap_cells_frame; [exact PMCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (mallocS_W L sp t a ms) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA MSR NSE RSR N SG9 SG5; lia. }
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  eapply KONT. unfold malloc_postS.
  split; [exact FPLE|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact STATSd|]. split; [exact LSJd|]. split; [exact HDR4|]. split; [eexists; exact PGJ|].
  split; [exact LHd|]. split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZJ3|].
  split. { change 17 with (Z.lor (Z.land (hdr_b1_mid 0) 243) 0). exact HDRd. }
  split. { rewrite skipn_repeat in UFd. exact UFd. }
  split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZT3|].
  split. { change 768 with (512 + 256). apply fill_merge; [apply F5; exact SHF13 | apply F5; exact SHFb3 | lia | lia]. }
  split.
  { unfold block_shadow_bytes. rewrite SGS, SGG.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
    - rewrite app_nil_r, Z.add_0_r. exact SHUb.
    - lazymatch goal with |- rw_cells _ _ _ [CB _ (?l1 ++ ?l2)] =>
        replace (Z.to_nat (shlen (n - n mod 8) + 1)) with (Z.to_nat (shlen (n - n mod 8)) + 1)%nat by (clear -SG5; lia) end.
      apply cb_app2; [exact SHUb|]. rewrite Z2Nat.id by (clear -SG5; lia).
      eapply rw_cells_recast; [exact (SHP5 M0) | cbn; tauto | reflexivity | reflexivity]. }
  split; [apply F5; exact SHTd|].
  split; [exact DEP5| split; [exact PCX5| exact PMC5]].
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="PR"] Lemma malloc_tail_sec : ltac:(let t := eval cbv delta [malloc_tail_sec__stmt] in malloc_tail_sec__stmt in exact t).
Proof. exact malloc_tail_sec__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc2s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3s.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma premap_cells_frame_b : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI, AIMG_LO in HW.
  assert (D : forall A k, 0 <= k -> 0x10000 <= A -> A + k <= 0x604000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA0 HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.
#[using="Type"] Lemma skipn_repeat {A} (x : A) : forall k n, skipn k (repeat x n) = repeat x (n - k).
Proof. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
#[using="Type"] Lemma firstn_repeat' {A} (x : A) : forall k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros16_hdr : forall m A, fill_at m A 16 0 ->
  rw_cells asegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cut : forall m A len k v, fill_at m A len v -> 0 <= k <= len ->
  fill_at m A k v /\ fill_at m (A + k) (len - k) v.
Proof. intros m A len k v H HK. replace len with (k + (len - k)) in H by lia. apply fill_split in H; [exact H| lia| lia]. Qed.

Section WithDepot.
Variable DI : ADepotIface.
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation mallocS_W L sp t a ms :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 2800, t + 3168); (a + 4096, a + ms); (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_postS (L : alayout) (RNG : footprint) (sp : word) (n t a ms nsec lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) (id : Z) (sj' : list word) : Prop :=
  let AB := a + 4096 in let UB := a + 6144 in
     fp_le RNG RNG'
  /\ munch (mallocS_W L sp t a ms) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ 0 < id < 2^31
  /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)]
  /\ junk_at m' (a + 32) (4096 - 32)
  /\ rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]
  /\ junk_at m' (AB + 16) (2048 - 32)
  /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
  /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]
  /\ junk_at m' (UB + n) (ms - 6144 - n)
  /\ fill_at m' (shad a) 768 0xfa
  /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)]
  /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
  /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

Definition malloc_tail_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t a ms nsec SB lo sz : Z) (fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk asegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= ctx \/ ctx + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                      CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))] ->
  rw_cells asegs m AB [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))] ->
  fill_at m (shad a) 512 0xfa -> fill_at m (shad a + 512) (size / 8) 0 -> fill_at m (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1404c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  (exists sj, u64arr asegs m (t + 2800) sj /\ length sj = 46%nat) ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  tclr a ms ->      (* [comment removed for export] *)
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33c40)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x564f0)] ->
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG' m' id sj' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     malloc_postS L RNG sp n t a ms nsec lo m RNG' m' id sj' ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 8).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 19).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 20).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 21).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 22).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 23).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 24).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 25).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 26).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 27).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 28).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 29).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 30).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 31).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 32).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 33).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 34).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 35).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 36).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 37).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 38).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 39).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 40).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 41).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 42).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 43).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 44).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 45).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 46).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 47).
Variable a : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 48).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 49).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 50).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 51).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 52).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 53).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 54).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 55).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 56).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_sec__stmt 57).
#[using="PR"] Lemma malloc_tail_sec__body : ltac:(let T := type of (fun (h : malloc_tail_sec__stmt) => h L RNG R k Q ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m n t a ms nsec SB lo sz fr0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (s0i, (F, (fc, (m, (n, (t, (a, (ms, (nsec, (SB, (lo, (sz, (fr0, (junk2, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS
         HDRP ZB SHF1 SHZ SHF2 PC PMC RELRO PP I32 I64 FLG HK MCS CF34 TI TK T88 TSD CT CX8 TT0 [sj [STATS LSJ]]
         CX0 CX1 CXS T0 T1 TS CT2 DTN DTS DCN DCS XTNO XTST XTA N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RTLS RSTK RCTX RT RNO RST RA RSA NI SI KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, AMALLOC_PC in *.
  word_range sp SPR.
  (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8
               /\ needed_size n / 8 = 512 + granules n
               /\ granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1)
               /\ shlen n = shlen (n - n mod 8)).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. rewrite NSE, RSE.
    repeat split; try (clear -AAL N; Z.div_mod_to_equations; lia).
    all: destruct (Z.eqb_spec (n mod 8) 0) as [E8|E8]; clear -AAL N E8; Z.div_mod_to_equations; lia. }
  (nd_pre SG 9%nat; intros SG1 SG2 SG5 SG6 SG8 SG9 SGN SGG SGS; nd_post).
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1, NI, SI.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).   (* [comment removed for export] *)
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb SHB1 SHB2; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post). (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (MS8 : 9216 <= ms / 8 /\ 6144 + n <= ms) by (clear -MSB MSR NSE RSR; Z.div_mod_to_equations; lia). destruct MS8 as [MS8 MS6].
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2. box DJSB.
  (* [comment removed for export] *)
  pose proof HDRP as HP0. rw_split HP0 4%nat HDR4 PGJ.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)])) with (a + 32) in PGJ by (cbn; lia).
  assert (ZBF : fill_at m (a + 4096) (ms - 4096) 0) by exact ZB. clear ZB.
  destruct (fill_cut m (a + 4096) (ms - 4096) 16 0 ZBF ltac:(clear -MSR NSE RSR N; lia)) as [ZAB Z1].
  destruct (fill_cut m (a + 4096 + 16) (ms - 4096 - 16) 2016 0 Z1 ltac:(clear -MSR NSE RSR N; lia)) as [ZJ1 Z2]. clear Z1.
  replace (a + 4096 + 16 + 2016) with (a + 6128) in Z2 by lia.
  destruct (fill_cut m (a + 6128) (ms - 4096 - 16 - 2016) 16 0 Z2 ltac:(clear -MSR NSE RSR N; lia)) as [ZH Z3]. clear Z2.
  replace (a + 6128 + 16) with (a + 6144) in Z3 by lia.
  destruct (fill_cut m (a + 6144) (ms - 4096 - 16 - 2016 - 16) n 0 Z3 ltac:(clear -MSR NSE RSR N; lia)) as [ZU ZT]. clear Z3.
  replace (ms - 4096 - 16 - 2016 - 16 - n) with (ms - 6144 - n) in ZT by lia.
  pose proof (zeros16_hdr m (a + 6128) ZH) as HDR. clear ZH.
  (nd_pre (c8c8_of_junk m (a + 4096) (fill_is_junk _ _ _ _ ZAB)) 3%nat; intros j1 j2 LH; nd_post).
  (* [comment removed for export] *)
  rewrite SGN in SHZ, SHF2.
  destruct (fill_cut m (shad a + 512) (512 + granules n) 256 0 SHZ ltac:(clear -SG5; lia)) as [SHL S1]. clear SHZ.
  replace (shad a + 512 + 256) with (shad (a + 6144)) in S1 by (rewrite SG2; lia).
  destruct (fill_cut m (shad (a + 6144)) (512 + granules n - 256) (shlen (n - n mod 8)) 0 S1 ltac:(clear -SG5 SG6; lia)) as [SHU S2]. clear S1.
  destruct (fill_cut m (shad (a + 6144) + shlen (n - n mod 8)) (512 + granules n - 256 - shlen (n - n mod 8)) (granules n - shlen (n - n mod 8)) 0 S2
              ltac:(clear -SG5 SG6; lia)) as [SHP S3]. clear S2.
  replace (shad (a + 6144) + shlen (n - n mod 8) + (granules n - shlen (n - n mod 8))) with (shad (a + 6144) + granules n) in S3 by lia.
  assert (SHT : junk_at m (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n)).
  { replace (ms / 8 - 768 - granules n) with ((512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))) + (ms / 8 - 512 - (512 + granules n)))
      by (clear -SG5 SG6; lia).
    apply junk_merge; [apply (fill_is_junk _ _ _ 0); exact S3 | apply (fill_is_junk _ _ _ 0xfa) | clear -SG5 SG6; lia | clear -SG5 SG6 MSE MSM SGN NSE RSE N; Z.div_mod_to_equations; lia].
    replace (shad (a + 6144) + granules n + (512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))))
      with (shad a + 512 + (512 + granules n)) by (rewrite SG2; clear -SG5 SG6; lia). exact SHF2. }
  clear S3 SHF2.
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]).
  { intros NE. apply c1_of_fill; [lia|]. rewrite SGG in SHP. destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [exfalso; exact (NE E)|].
    replace (shlen (n - n mod 8) + 1 - shlen (n - n mod 8)) with 1 in SHP by lia. exact SHP. }
  clear SHP.
  rewrite <- SG1 in SHL.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply (allocBC_sec DI PR L RNG R k Q spA gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n (bv_unsigned sp + -2128) t a ms nsec SB lo sz 353412 tb tr fr0
            (Z_to_bv 64 0x33c40) s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11).
  all: try lazymatch goal with
       | |- forall _, _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PMC
       | |- ADEPOT _ _ _ => exact DEP
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- u64arr _ _ _ _ => exact TB
       | |- _ \/ _ => first [unboxed DJSB | unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed CT2]
       | |- exists junk, _ => exact SHT
       | |- ~ _ -> _ => exact SHP1
       | |- rw_cells _ _ (shad (_ + 4096)) _ => exact SHL
       | |- rw_cells _ _ (shad (_ + 6144)) _ => exact SHU
       | |- rw_cells _ _ (_ + 6128) _ => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR4
       | |- rng _ _ _ => solve_rng
       | |- is_primary _ = _ => exact PRIM
       | |- _ = sec_map_size _ => exact HMS
       end.
  all: try eassumption.
  all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI SB0 SBH CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 SZB S47 MSB ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
  all: match goal with |- forall _, _ => idtac | |- ?G => idtac "REMBC" G end.
  (* [comment removed for export] *)
  intros RNG' m2 id rax t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b PB IDR.
  unfold allocBC_postS in PB.
  (nd_pre PB 33%nat; intros id_ raB t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s6_ t3_ t4_ t5_ t6_ EMS FPLE MUb WMb MIb STb IDR_ HDRb SHFb SHUb SHPb SHTb DEPb PCb PMCb; nd_post).
  clear EMS IDR id. rename id_ into id. rename IDR_ into IDR.
  rewrite ?HspA in MUb.
  replace (Z_to_bv 64 (a + 6128)) with (Z_to_bv 64 (a + 6144 + -16)) by (f_equal; lia).
  replace (a + 6128) with (a + 6144 + -16) in HDRb by lia.
  pose proof (hdr_b1_mid_range 0 ltac:(lia)) as B1M.
  assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
  assert (RIMG' : rng_aimg RNG') by (eapply rng_fp_le; [exact FPLE| exact RIMG]).
  assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).      (* [comment removed for export] *)
  assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX]).
  assert (RT' : rng RNG' t 4096) by (eapply rng_fp_le; [exact FPLE| exact RT]).
  assert (RA' : rng RNG' a ms) by (eapply rng_fp_le; [exact FPLE| exact RA]).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; first [ solve [ clear -Y Y0 Y1 LSJ T0 T1 CEIL LO SPR TBND TBNDa TBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport TSD MUb WMb ltac:(lia).      (* [comment removed for export] *)
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; first [ solve [ clear -Y Y0 Y1 CX0 CX1 CEIL LO SPR CBND CBNDa CBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport FLG MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia). xport MCS MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport CF34 MUb WMb ltac:(lia).
  pose proof PCb as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  assert (ZU2 : fill_at m2 (a + 6144) n 0).
  { eapply fill_frame; [exact ZU | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  xport FR16 MUb WMb ltac:(lia). xport SS MUb WMb ltac:(lia). xport FRS MUb WMb ltac:(lia).
  xport TB MUb WMb ltac:(rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 (a + 4096) [C8 j1; C8 j2]).
  { intros _. xport LH MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia). exact LH. }
  clear LH.
  (* [comment removed for export] *)
  xport HDR4 MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  xport PGJ MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  assert (ZJ2 : fill_at m2 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (ZT2 : fill_at m2 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT | exact MUb | exact WMb |]. intros Hp. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 Hp SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (SHF12 : fill_at m2 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 N0 R0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI SG1 SG2. dlia. }
  clear ZU ZJ1 ZT SHF1 SHL SHU SHP1 SHT HDR HDRP.
  (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (allocD_sec L RNG' spA gp tp F fc m2 n t (a + 4096) (a + 6144) lo 0 (hdr_b1_mid 0) id (bv_unsigned sp + -2128) sj
              (repeat (Z_to_bv 8 0) (Z.to_nat n)) j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => ub DJT; clear -Y N MSR NSE RSR; lia
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- rw_cells _ _ (_ + 6144) [CB _ _] => exact ZU2
         | |- is_primary _ = _ => exact PRIM
         | |- _ = _ + rz_size _ => rewrite RZ; lia
         | |- _ mod 16 = 0 => clear -AAL; Z.div_mod_to_equations; lia
         end.
    all: try eassumption.
    all: try (eapply ablk_sub; [exact ALO | clear; lia | clear -N MSR NSE RSR MSB; lia]).   (* [comment removed for export] *)
    all: try (eapply tclr_sub; [exact XTA | clear; lia | clear -N MSR NSE RSR MSB; lia]).      (* [comment removed for export] *)
    all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 S47 MSB MSR NSE RSR B1M IDR ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  specialize (LHd ltac:(rewrite RZ; lia)).
  xport FR16 MUd WMd ltac:(lia). xport SS MUd WMd ltac:(lia). xport FRS MUd WMd ltac:(lia). xport TB MUd WMd ltac:(rewrite LTB; lia).
  xport HDR4 MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  xport PGJ MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  assert (ZJ3 : fill_at m3 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ2 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR ALO1. dlia. }
  assert (ZT3 : fill_at m3 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT2 | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Hp ALO1. dlia. }
  assert (SHF13 : fill_at m3 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF12 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SHFb3 : fill_at m3 (shad a + 512) 256 0xfa).
  { eapply fill_frame; [exact SHFb | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SGX : shad (a + 6144) + granules n + (ms / 8 - 768 - granules n) <= 0x10007fff8000 /\ 0 <= ms / 8 - 768 - granules n)
    by (rewrite SG2; clear -SHB2 SG9 MSR NSE RSE N; Z.div_mod_to_equations; lia).
  destruct SGX as [SGX1 SGX2].
  xport SHUb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia). exact SHPb. }
  assert (SHTd : fill_at m3 (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n) 0xfa).
  { eapply fill_frame; [exact SHTb | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 Hp ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx; ub DTN; ub DTS; ub DJN; ub DJS; clear -Y Y0 Y1 Y2 Hx HspA SPR CEIL LO N AAL ALO AHI MSB MS6 T0 TS T1 N0 N1 R0 R1 ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb; lia|]). apply Forall_nil. }
  assert (PCd : poison_cells m3).
  { eapply poison_cells_frame_b; [exact PCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  assert (PMCd : premap_cells m3).
  { eapply premap_cells_frame_b; [exact PMCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  clear SHF12 SHFb ZJ2 ZT2 ZU2 SHPb SHTb DEPb PCb PMCb.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x33c40)) with (Z_to_bv 64 0x33c40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG' sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG' | exact RTLS' | solve_rng ]. }
  cbv beta. intros ms5 PCC. (nd_pre PCC 2%nat; intros m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUc WMc MIc STc; nd_post).
  (* [comment removed for export] *)
  xport STATSd MUc WMc ltac:(exact I). xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport LHd MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport PGJ MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I).
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (F5 : forall A l v, fill_at m3 A l v -> fill_at m5 A l v).
  { intros A l v H. eapply fill_frame; [exact H | exact MUc | exact WMc | intros _; exact I]. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PCX5 : poison_cells m5). { eapply poison_cells_frame; [exact PCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PMC5 : premap_cells m5). { eapply premap_cells_frame; [exact PMCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (mallocS_W L sp t a ms) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA MSR NSE RSR N SG9 SG5; lia. }
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  eapply KONT. unfold malloc_postS.
  split; [exact FPLE|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact STATSd|]. split; [exact LSJd|]. split; [exact HDR4|]. split; [eexists; exact PGJ|].
  split; [exact LHd|]. split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZJ3|].
  split. { change 17 with (Z.lor (Z.land (hdr_b1_mid 0) 243) 0). exact HDRd. }
  split. { rewrite skipn_repeat in UFd. exact UFd. }
  split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZT3|].
  split. { change 768 with (512 + 256). apply fill_merge; [apply F5; exact SHF13 | apply F5; exact SHFb3 | lia | lia]. }
  split.
  { unfold block_shadow_bytes. rewrite SGS, SGG.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
    - rewrite app_nil_r, Z.add_0_r. exact SHUb.
    - lazymatch goal with |- rw_cells _ _ _ [CB _ (?l1 ++ ?l2)] =>
        replace (Z.to_nat (shlen (n - n mod 8) + 1)) with (Z.to_nat (shlen (n - n mod 8)) + 1)%nat by (clear -SG5; lia) end.
      apply cb_app2; [exact SHUb|]. rewrite Z2Nat.id by (clear -SG5; lia).
      eapply rw_cells_recast; [exact (SHP5 M0) | cbn; tauto | reflexivity | reflexivity]. }
  split; [apply F5; exact SHTd|].
  split; [exact DEP5| split; [exact PCX5| exact PMC5]].
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="PR"] Lemma malloc_tail_sec : ltac:(let t := eval cbv delta [malloc_tail_sec__stmt] in malloc_tail_sec__stmt in exact t).
Proof. exact malloc_tail_sec__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_amalloc_tailS.

(* [comment removed for export] *)
Module F_aallocfn_tailS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc2s. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc2s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma premap_cells_frame_b : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI, AIMG_LO in HW.
  assert (D : forall A k, 0 <= k -> 0x10000 <= A -> A + k <= 0x603000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA0 HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.
Section WithDepot.
Variable DI : ADepotIface.
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation mallocS_W L sp t a ms :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 2800, t + 3168); (a + 4096, a + ms); (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocfn_tail_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    (raA gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t a ms nsec SB lo sz S pc : Z) (fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  bv_unsigned spA <= S ->
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= ctx \/ ctx + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                      CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))] ->
  rw_cells asegs m AB [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))] ->
  fill_at m (shad a) 512 0xfa -> fill_at m (shad a + 512) (size / 8) 0 -> fill_at m (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1400c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  (exists sj, u64arr asegs m (t + 2800) sj /\ length sj = 46%nat) ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  tclr a ms ->      (* [comment removed for export] *)
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 raA] ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG' m' id sj' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     malloc_postS DI L RNG spA n t a ms nsec lo m RNG' m' id sj' ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR raA spA gp tp t0' t1' t2' s0A s1A (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc raA) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 4).
Variable raA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 7).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 18).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 19).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 20).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 21).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 28).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 29).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 30).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 31).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 32).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 33).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 39).
Variable a : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 41).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 42).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 44).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 45).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 46).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 47).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 48).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 49).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 50).
#[using="PR"] Lemma allocfn_tail_sec__body : ltac:(let T := type of (fun (h : allocfn_tail_sec__stmt) => h L RNG R k Q raA gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A F fc m n t a ms nsec SB lo sz S pc fr0 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (raA, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (F, (fc, (m, (n, (t, (a, (ms, (nsec, (SB, (lo, (sz, (S, (pc, (fr0, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS
         HDRP ZB SHF1 SHZ SHF2 PC PMC RELRO PP I32 I64 FLG HK MCS CF34 TI TK T88 TSD CT CX8 TT0 [sj [STATS LSJ]]
         CX0 CX1 CXS T0 T1 TS CT2 DTN DTS DCN DCS XTNO XTST XTA N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 DEP
         RIMG RTLS RSTK RS RCTX RT RNO RST RA RSA NI SI KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD in *.
  word_range spA SPR.
  (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8
               /\ needed_size n / 8 = 512 + granules n
               /\ granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1)
               /\ shlen n = shlen (n - n mod 8)).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. rewrite NSE, RSE.
    repeat split; try (clear -AAL N; Z.div_mod_to_equations; lia).
    all: destruct (Z.eqb_spec (n mod 8) 0) as [E8|E8]; clear -AAL N E8; Z.div_mod_to_equations; lia. }
  (nd_pre SG 9%nat; intros SG1 SG2 SG5 SG6 SG8 SG9 SGN SGG SGS; nd_post).
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1, NI, SI.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).   (* [comment removed for export] *)
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb SHB1 SHB2; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post). (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (MS8 : 9216 <= ms / 8 /\ 6144 + n <= ms) by (clear -MSB MSR NSE RSR; Z.div_mod_to_equations; lia). destruct MS8 as [MS8 MS6].
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2. box DJSB.
  (* [comment removed for export] *)
  pose proof HDRP as HP0. rw_split HP0 4%nat HDR4 PGJ.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)])) with (a + 32) in PGJ by (cbn; lia).
  assert (ZBF : fill_at m (a + 4096) (ms - 4096) 0) by exact ZB. clear ZB.
  destruct (fill_cut m (a + 4096) (ms - 4096) 16 0 ZBF ltac:(clear -MSR NSE RSR N; lia)) as [ZAB Z1].
  destruct (fill_cut m (a + 4096 + 16) (ms - 4096 - 16) 2016 0 Z1 ltac:(clear -MSR NSE RSR N; lia)) as [ZJ1 Z2]. clear Z1.
  replace (a + 4096 + 16 + 2016) with (a + 6128) in Z2 by lia.
  destruct (fill_cut m (a + 6128) (ms - 4096 - 16 - 2016) 16 0 Z2 ltac:(clear -MSR NSE RSR N; lia)) as [ZH Z3]. clear Z2.
  replace (a + 6128 + 16) with (a + 6144) in Z3 by lia.
  destruct (fill_cut m (a + 6144) (ms - 4096 - 16 - 2016 - 16) n 0 Z3 ltac:(clear -MSR NSE RSR N; lia)) as [ZU ZT]. clear Z3.
  replace (ms - 4096 - 16 - 2016 - 16 - n) with (ms - 6144 - n) in ZT by lia.
  pose proof (zeros16_hdr m (a + 6128) ZH) as HDR. clear ZH.
  (nd_pre (c8c8_of_junk m (a + 4096) (fill_is_junk _ _ _ _ ZAB)) 3%nat; intros j1 j2 LH; nd_post).
  (* [comment removed for export] *)
  rewrite SGN in SHZ, SHF2.
  destruct (fill_cut m (shad a + 512) (512 + granules n) 256 0 SHZ ltac:(clear -SG5; lia)) as [SHL S1]. clear SHZ.
  replace (shad a + 512 + 256) with (shad (a + 6144)) in S1 by (rewrite SG2; lia).
  destruct (fill_cut m (shad (a + 6144)) (512 + granules n - 256) (shlen (n - n mod 8)) 0 S1 ltac:(clear -SG5 SG6; lia)) as [SHU S2]. clear S1.
  destruct (fill_cut m (shad (a + 6144) + shlen (n - n mod 8)) (512 + granules n - 256 - shlen (n - n mod 8)) (granules n - shlen (n - n mod 8)) 0 S2
              ltac:(clear -SG5 SG6; lia)) as [SHP S3]. clear S2.
  replace (shad (a + 6144) + shlen (n - n mod 8) + (granules n - shlen (n - n mod 8))) with (shad (a + 6144) + granules n) in S3 by lia.
  assert (SHT : junk_at m (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n)).
  { replace (ms / 8 - 768 - granules n) with ((512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))) + (ms / 8 - 512 - (512 + granules n)))
      by (clear -SG5 SG6; lia).
    apply junk_merge; [apply (fill_is_junk _ _ _ 0); exact S3 | apply (fill_is_junk _ _ _ 0xfa) | clear -SG5 SG6; lia | clear -SG5 SG6 MSE MSM SGN NSE RSE N; Z.div_mod_to_equations; lia].
    replace (shad (a + 6144) + granules n + (512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))))
      with (shad a + 512 + (512 + granules n)) by (rewrite SG2; clear -SG5 SG6; lia). exact SHF2. }
  clear S3 SHF2.
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]).
  { intros NE. apply c1_of_fill; [lia|]. rewrite SGG in SHP. destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [exfalso; exact (NE E)|].
    replace (shlen (n - n mod 8) + 1 - shlen (n - n mod 8)) with 1 in SHP by lia. exact SHP. }
  clear SHP.
  rewrite <- SG1 in SHL.
  (* [comment removed for export] *)
  eapply (allocBC_sec DI PR L RNG R k Q spA gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t a ms nsec SB lo sz pc tb tr fr0
            raA s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11).
  all: try lazymatch goal with
       | |- forall _, _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PMC
       | |- ADEPOT _ _ _ => exact DEP
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- u64arr _ _ _ _ => exact TB
       | |- _ \/ _ => first [unboxed DJSB | unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed CT2]
       | |- exists junk, _ => exact SHT
       | |- ~ _ -> _ => exact SHP1
       | |- rw_cells _ _ (shad (_ + 4096)) _ => exact SHL
       | |- rw_cells _ _ (shad (_ + 6144)) _ => exact SHU
       | |- rw_cells _ _ (_ + 6128) _ => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR4
       | |- rng _ _ _ => solve_rng
       | |- is_primary _ = _ => exact PRIM
       | |- _ = sec_map_size _ => exact HMS
       end.
  all: try eassumption.
  all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI SB0 SBH CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 SZB S47 MSB ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
  all: match goal with |- forall _, _ => idtac | |- ?G => idtac "REMBC" G end.
  (* [comment removed for export] *)
  intros RNG' m2 id rax t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b PB IDR.
  unfold allocBC_postS in PB.
  (nd_pre PB 33%nat; intros id_ raB t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s6_ t3_ t4_ t5_ t6_ EMS FPLE MUb WMb MIb STb IDR_ HDRb SHFb SHUb SHPb SHTb DEPb PCb PMCb; nd_post).
  clear EMS IDR id. rename id_ into id. rename IDR_ into IDR.
  replace (Z_to_bv 64 (a + 6128)) with (Z_to_bv 64 (a + 6144 + -16)) by (f_equal; lia).
  replace (a + 6128) with (a + 6144 + -16) in HDRb by lia.
  pose proof (hdr_b1_mid_range 0 ltac:(lia)) as B1M.
  assert (RSTK' : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
  assert (RIMG' : rng_aimg RNG') by (eapply rng_fp_le; [exact FPLE| exact RIMG]).
  assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).      (* [comment removed for export] *)
  assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX]).
  assert (RT' : rng RNG' t 4096) by (eapply rng_fp_le; [exact FPLE| exact RT]).
  assert (RA' : rng RNG' a ms) by (eapply rng_fp_le; [exact FPLE| exact RA]).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; first [ solve [ clear -Y Y0 Y1 LSJ T0 T1 CEIL LO SPR TBND TBNDa TBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport TSD MUb WMb ltac:(lia).      (* [comment removed for export] *)
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; first [ solve [ clear -Y Y0 Y1 CX0 CX1 CEIL LO SPR CBND CBNDa CBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport FLG MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia). xport MCS MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport CF34 MUb WMb ltac:(lia).
  pose proof PCb as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  assert (ZU2 : fill_at m2 (a + 6144) n 0).
  { eapply fill_frame; [exact ZU | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
    xport TB MUb WMb ltac:(rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 (a + 4096) [C8 j1; C8 j2]).
  { intros _. xport LH MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia). exact LH. }
  clear LH.
  (* [comment removed for export] *)
  xport HDR4 MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  xport PGJ MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  assert (ZJ2 : fill_at m2 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (ZT2 : fill_at m2 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT | exact MUb | exact WMb |]. intros Hp. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 Hp SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (SHF12 : fill_at m2 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 N0 R0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI SG1 SG2. dlia. }
  clear ZU ZJ1 ZT SHF1 SHL SHU SHP1 SHT HDR HDRP.
  (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (allocD_sec L RNG' spA gp tp F fc m2 n t (a + 4096) (a + 6144) lo 0 (hdr_b1_mid 0) id S sj
              (repeat (Z_to_bv 8 0) (Z.to_nat n)) j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => ub DJT; clear -Y N MSR NSE RSR; lia
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- rw_cells _ _ (_ + 6144) [CB _ _] => exact ZU2
         | |- is_primary _ = _ => exact PRIM
         | |- _ = _ + rz_size _ => rewrite RZ; lia
         | |- _ mod 16 = 0 => clear -AAL; Z.div_mod_to_equations; lia
         end.
    all: try eassumption.
    all: try (eapply ablk_sub; [exact ALO | clear; lia | clear -N MSR NSE RSR MSB; lia]).   (* [comment removed for export] *)
    all: try (eapply tclr_sub; [exact XTA | clear; lia | clear -N MSR NSE RSR MSB; lia]).      (* [comment removed for export] *)
    all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 S47 MSB MSR NSE RSR B1M IDR ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  specialize (LHd ltac:(rewrite RZ; lia)).
    xport HDR4 MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  xport PGJ MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  assert (ZJ3 : fill_at m3 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ2 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR ALO1. dlia. }
  assert (ZT3 : fill_at m3 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT2 | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Hp ALO1. dlia. }
  assert (SHF13 : fill_at m3 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF12 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SHFb3 : fill_at m3 (shad a + 512) 256 0xfa).
  { eapply fill_frame; [exact SHFb | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SGX : shad (a + 6144) + granules n + (ms / 8 - 768 - granules n) <= 0x10007fff8000 /\ 0 <= ms / 8 - 768 - granules n)
    by (rewrite SG2; clear -SHB2 SG9 MSR NSE RSE N; Z.div_mod_to_equations; lia).
  destruct SGX as [SGX1 SGX2].
  xport SHUb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia). exact SHPb. }
  assert (SHTd : fill_at m3 (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n) 0xfa).
  { eapply fill_frame; [exact SHTb | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 Hp ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx; ub DTN; ub DTS; ub DJN; ub DJS; clear -Y Y0 Y1 Y2 Hx HspA SPR CEIL LO N AAL ALO AHI MSB MS6 T0 TS T1 N0 N1 R0 R1 ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb; lia|]). apply Forall_nil. }
  assert (PCd : poison_cells m3).
  { eapply poison_cells_frame_b; [exact PCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  assert (PMCd : premap_cells m3).
  { eapply premap_cells_frame_b; [exact PMCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  clear SHF12 SHFb ZJ2 ZT2 ZU2 SHPb SHTb DEPb PCb PMCb.
  (* [comment removed for export] *)
  apply evtF_done.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MUc. pose proof (wmono_refl asegs m3) as WMc.
  pose proof MId as MIc. pose proof STd as STc.
  (* [comment removed for export] *)
  xport STATSd MUc WMc ltac:(exact I). xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport LHd MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport PGJ MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I).
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (F5 : forall A l v, fill_at m3 A l v -> fill_at m3 A l v).
  { intros A l v H. eapply fill_frame; [exact H | exact MUc | exact WMc | intros _; exact I]. }
  assert (DEP5 : ADEPOT DI L m3). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PCX5 : poison_cells m3). { eapply poison_cells_frame; [exact PCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PMC5 : premap_cells m3). { eapply premap_cells_frame; [exact PMCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (mallocS_W L spA t a ms) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA MSR NSE RSR N SG9 SG5; lia. }
  assert (WM : wmono asegs m m3).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  eapply KONT. unfold malloc_postS.
  split; [exact FPLE|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact STATSd|]. split; [exact LSJd|]. split; [exact HDR4|]. split; [eexists; exact PGJ|].
  split; [exact LHd|]. split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZJ3|].
  split. { change 17 with (Z.lor (Z.land (hdr_b1_mid 0) 243) 0). exact HDRd. }
  split. { rewrite skipn_repeat in UFd. exact UFd. }
  split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZT3|].
  split. { change 768 with (512 + 256). apply fill_merge; [apply F5; exact SHF13 | apply F5; exact SHFb3 | lia | lia]. }
  split.
  { unfold block_shadow_bytes. rewrite SGS, SGG.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
    - rewrite app_nil_r, Z.add_0_r. exact SHUb.
    - lazymatch goal with |- rw_cells _ _ _ [CB _ (?l1 ++ ?l2)] =>
        replace (Z.to_nat (shlen (n - n mod 8) + 1)) with (Z.to_nat (shlen (n - n mod 8)) + 1)%nat by (clear -SG5; lia) end.
      apply cb_app2; [exact SHUb|]. rewrite Z2Nat.id by (clear -SG5; lia).
      eapply rw_cells_recast; [exact (SHP5 M0) | cbn; tauto | reflexivity | reflexivity]. }
  split; [apply F5; exact SHTd|].
  split; [exact DEP5| split; [exact PCX5| exact PMC5]].
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="PR"] Lemma allocfn_tail_sec : ltac:(let t := eval cbv delta [allocfn_tail_sec__stmt] in allocfn_tail_sec__stmt in exact t).
Proof. exact allocfn_tail_sec__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc2s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma premap_cells_frame_b : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI, AIMG_LO in HW.
  assert (D : forall A k, 0 <= k -> 0x10000 <= A -> A + k <= 0x604000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA0 HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.
Section WithDepot.
Variable DI : ADepotIface.
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation mallocS_W L sp t a ms :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 2800, t + 3168); (a + 4096, a + ms); (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocfn_tail_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    (raA gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t a ms nsec SB lo sz S pc : Z) (fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  bv_unsigned spA <= S ->
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= ctx \/ ctx + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                      CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))] ->
  rw_cells asegs m AB [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))] ->
  fill_at m (shad a) 512 0xfa -> fill_at m (shad a + 512) (size / 8) 0 -> fill_at m (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1404c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  (exists sj, u64arr asegs m (t + 2800) sj /\ length sj = 46%nat) ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  tclr a ms ->      (* [comment removed for export] *)
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 raA] ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG' m' id sj' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     malloc_postS DI L RNG spA n t a ms nsec lo m RNG' m' id sj' ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR raA spA gp tp t0' t1' t2' s0A s1A (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc raA) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 4).
Variable raA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 7).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 18).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 19).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 20).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 21).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 28).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 29).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 30).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 31).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 32).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 33).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 39).
Variable a : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 41).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 42).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 44).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 45).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 46).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 47).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 48).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 49).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_sec__stmt 50).
#[using="PR"] Lemma allocfn_tail_sec__body : ltac:(let T := type of (fun (h : allocfn_tail_sec__stmt) => h L RNG R k Q raA gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A F fc m n t a ms nsec SB lo sz S pc fr0 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (raA, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (F, (fc, (m, (n, (t, (a, (ms, (nsec, (SB, (lo, (sz, (S, (pc, (fr0, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS
         HDRP ZB SHF1 SHZ SHF2 PC PMC RELRO PP I32 I64 FLG HK MCS CF34 TI TK T88 TSD CT CX8 TT0 [sj [STATS LSJ]]
         CX0 CX1 CXS T0 T1 TS CT2 DTN DTS DCN DCS XTNO XTST XTA N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 DEP
         RIMG RTLS RSTK RS RCTX RT RNO RST RA RSA NI SI KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD in *.
  word_range spA SPR.
  (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8
               /\ needed_size n / 8 = 512 + granules n
               /\ granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1)
               /\ shlen n = shlen (n - n mod 8)).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. rewrite NSE, RSE.
    repeat split; try (clear -AAL N; Z.div_mod_to_equations; lia).
    all: destruct (Z.eqb_spec (n mod 8) 0) as [E8|E8]; clear -AAL N E8; Z.div_mod_to_equations; lia. }
  (nd_pre SG 9%nat; intros SG1 SG2 SG5 SG6 SG8 SG9 SGN SGG SGS; nd_post).
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1, NI, SI.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).   (* [comment removed for export] *)
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb SHB1 SHB2; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post). (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (MS8 : 9216 <= ms / 8 /\ 6144 + n <= ms) by (clear -MSB MSR NSE RSR; Z.div_mod_to_equations; lia). destruct MS8 as [MS8 MS6].
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2. box DJSB.
  (* [comment removed for export] *)
  pose proof HDRP as HP0. rw_split HP0 4%nat HDR4 PGJ.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)])) with (a + 32) in PGJ by (cbn; lia).
  assert (ZBF : fill_at m (a + 4096) (ms - 4096) 0) by exact ZB. clear ZB.
  destruct (fill_cut m (a + 4096) (ms - 4096) 16 0 ZBF ltac:(clear -MSR NSE RSR N; lia)) as [ZAB Z1].
  destruct (fill_cut m (a + 4096 + 16) (ms - 4096 - 16) 2016 0 Z1 ltac:(clear -MSR NSE RSR N; lia)) as [ZJ1 Z2]. clear Z1.
  replace (a + 4096 + 16 + 2016) with (a + 6128) in Z2 by lia.
  destruct (fill_cut m (a + 6128) (ms - 4096 - 16 - 2016) 16 0 Z2 ltac:(clear -MSR NSE RSR N; lia)) as [ZH Z3]. clear Z2.
  replace (a + 6128 + 16) with (a + 6144) in Z3 by lia.
  destruct (fill_cut m (a + 6144) (ms - 4096 - 16 - 2016 - 16) n 0 Z3 ltac:(clear -MSR NSE RSR N; lia)) as [ZU ZT]. clear Z3.
  replace (ms - 4096 - 16 - 2016 - 16 - n) with (ms - 6144 - n) in ZT by lia.
  pose proof (zeros16_hdr m (a + 6128) ZH) as HDR. clear ZH.
  (nd_pre (c8c8_of_junk m (a + 4096) (fill_is_junk _ _ _ _ ZAB)) 3%nat; intros j1 j2 LH; nd_post).
  (* [comment removed for export] *)
  rewrite SGN in SHZ, SHF2.
  destruct (fill_cut m (shad a + 512) (512 + granules n) 256 0 SHZ ltac:(clear -SG5; lia)) as [SHL S1]. clear SHZ.
  replace (shad a + 512 + 256) with (shad (a + 6144)) in S1 by (rewrite SG2; lia).
  destruct (fill_cut m (shad (a + 6144)) (512 + granules n - 256) (shlen (n - n mod 8)) 0 S1 ltac:(clear -SG5 SG6; lia)) as [SHU S2]. clear S1.
  destruct (fill_cut m (shad (a + 6144) + shlen (n - n mod 8)) (512 + granules n - 256 - shlen (n - n mod 8)) (granules n - shlen (n - n mod 8)) 0 S2
              ltac:(clear -SG5 SG6; lia)) as [SHP S3]. clear S2.
  replace (shad (a + 6144) + shlen (n - n mod 8) + (granules n - shlen (n - n mod 8))) with (shad (a + 6144) + granules n) in S3 by lia.
  assert (SHT : junk_at m (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n)).
  { replace (ms / 8 - 768 - granules n) with ((512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))) + (ms / 8 - 512 - (512 + granules n)))
      by (clear -SG5 SG6; lia).
    apply junk_merge; [apply (fill_is_junk _ _ _ 0); exact S3 | apply (fill_is_junk _ _ _ 0xfa) | clear -SG5 SG6; lia | clear -SG5 SG6 MSE MSM SGN NSE RSE N; Z.div_mod_to_equations; lia].
    replace (shad (a + 6144) + granules n + (512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))))
      with (shad a + 512 + (512 + granules n)) by (rewrite SG2; clear -SG5 SG6; lia). exact SHF2. }
  clear S3 SHF2.
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]).
  { intros NE. apply c1_of_fill; [lia|]. rewrite SGG in SHP. destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [exfalso; exact (NE E)|].
    replace (shlen (n - n mod 8) + 1 - shlen (n - n mod 8)) with 1 in SHP by lia. exact SHP. }
  clear SHP.
  rewrite <- SG1 in SHL.
  (* [comment removed for export] *)
  eapply (allocBC_sec DI PR L RNG R k Q spA gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t a ms nsec SB lo sz pc tb tr fr0
            raA s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11).
  all: try lazymatch goal with
       | |- forall _, _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PMC
       | |- ADEPOT _ _ _ => exact DEP
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- u64arr _ _ _ _ => exact TB
       | |- _ \/ _ => first [unboxed DJSB | unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed CT2]
       | |- exists junk, _ => exact SHT
       | |- ~ _ -> _ => exact SHP1
       | |- rw_cells _ _ (shad (_ + 4096)) _ => exact SHL
       | |- rw_cells _ _ (shad (_ + 6144)) _ => exact SHU
       | |- rw_cells _ _ (_ + 6128) _ => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR4
       | |- rng _ _ _ => solve_rng
       | |- is_primary _ = _ => exact PRIM
       | |- _ = sec_map_size _ => exact HMS
       end.
  all: try eassumption.
  all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI SB0 SBH CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 SZB S47 MSB ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
  all: match goal with |- forall _, _ => idtac | |- ?G => idtac "REMBC" G end.
  (* [comment removed for export] *)
  intros RNG' m2 id rax t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b PB IDR.
  unfold allocBC_postS in PB.
  (nd_pre PB 33%nat; intros id_ raB t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s6_ t3_ t4_ t5_ t6_ EMS FPLE MUb WMb MIb STb IDR_ HDRb SHFb SHUb SHPb SHTb DEPb PCb PMCb; nd_post).
  clear EMS IDR id. rename id_ into id. rename IDR_ into IDR.
  replace (Z_to_bv 64 (a + 6128)) with (Z_to_bv 64 (a + 6144 + -16)) by (f_equal; lia).
  replace (a + 6128) with (a + 6144 + -16) in HDRb by lia.
  pose proof (hdr_b1_mid_range 0 ltac:(lia)) as B1M.
  assert (RSTK' : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
  assert (RIMG' : rng_aimg RNG') by (eapply rng_fp_le; [exact FPLE| exact RIMG]).
  assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).      (* [comment removed for export] *)
  assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX]).
  assert (RT' : rng RNG' t 4096) by (eapply rng_fp_le; [exact FPLE| exact RT]).
  assert (RA' : rng RNG' a ms) by (eapply rng_fp_le; [exact FPLE| exact RA]).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; first [ solve [ clear -Y Y0 Y1 LSJ T0 T1 CEIL LO SPR TBND TBNDa TBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport TSD MUb WMb ltac:(lia).      (* [comment removed for export] *)
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; first [ solve [ clear -Y Y0 Y1 CX0 CX1 CEIL LO SPR CBND CBNDa CBNDb SHB1 SHB2 MSB MS6; lia_relc ] | lia_relc ]).   (* [comment removed for export] *)
  xport FLG MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia). xport MCS MUb WMb ltac:(tclr_int XTA; tclr_int XTNO; tclr_int XTST; lia). xport CF34 MUb WMb ltac:(lia).
  pose proof PCb as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  assert (ZU2 : fill_at m2 (a + 6144) n 0).
  { eapply fill_frame; [exact ZU | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
    xport TB MUb WMb ltac:(rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 (a + 4096) [C8 j1; C8 j2]).
  { intros _. xport LH MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia). exact LH. }
  clear LH.
  (* [comment removed for export] *)
  xport HDR4 MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  xport PGJ MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  assert (ZJ2 : fill_at m2 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (ZT2 : fill_at m2 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT | exact MUb | exact WMb |]. intros Hp. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 Hp SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (SHF12 : fill_at m2 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 N0 R0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI SG1 SG2. dlia. }
  clear ZU ZJ1 ZT SHF1 SHL SHU SHP1 SHT HDR HDRP.
  (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (allocD_sec L RNG' spA gp tp F fc m2 n t (a + 4096) (a + 6144) lo 0 (hdr_b1_mid 0) id S sj
              (repeat (Z_to_bv 8 0) (Z.to_nat n)) j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => ub DJT; clear -Y N MSR NSE RSR; lia
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- rw_cells _ _ (_ + 6144) [CB _ _] => exact ZU2
         | |- is_primary _ = _ => exact PRIM
         | |- _ = _ + rz_size _ => rewrite RZ; lia
         | |- _ mod 16 = 0 => clear -AAL; Z.div_mod_to_equations; lia
         end.
    all: try eassumption.
    all: try (eapply ablk_sub; [exact ALO | clear; lia | clear -N MSR NSE RSR MSB; lia]).   (* [comment removed for export] *)
    all: try (eapply tclr_sub; [exact XTA | clear; lia | clear -N MSR NSE RSR MSB; lia]).      (* [comment removed for export] *)
    all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 S47 MSB MSR NSE RSR B1M IDR ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  specialize (LHd ltac:(rewrite RZ; lia)).
    xport HDR4 MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  xport PGJ MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  assert (ZJ3 : fill_at m3 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ2 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR ALO1. dlia. }
  assert (ZT3 : fill_at m3 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT2 | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Hp ALO1. dlia. }
  assert (SHF13 : fill_at m3 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF12 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SHFb3 : fill_at m3 (shad a + 512) 256 0xfa).
  { eapply fill_frame; [exact SHFb | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SGX : shad (a + 6144) + granules n + (ms / 8 - 768 - granules n) <= 0x10007fff8000 /\ 0 <= ms / 8 - 768 - granules n)
    by (rewrite SG2; clear -SHB2 SG9 MSR NSE RSE N; Z.div_mod_to_equations; lia).
  destruct SGX as [SGX1 SGX2].
  xport SHUb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia). exact SHPb. }
  assert (SHTd : fill_at m3 (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n) 0xfa).
  { eapply fill_frame; [exact SHTb | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 Hp ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx; ub DTN; ub DTS; ub DJN; ub DJS; clear -Y Y0 Y1 Y2 Hx HspA SPR CEIL LO N AAL ALO AHI MSB MS6 T0 TS T1 N0 N1 R0 R1 ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb; lia|]). apply Forall_nil. }
  assert (PCd : poison_cells m3).
  { eapply poison_cells_frame_b; [exact PCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  assert (PMCd : premap_cells m3).
  { eapply premap_cells_frame_b; [exact PMCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  clear SHF12 SHFb ZJ2 ZT2 ZU2 SHPb SHTb DEPb PCb PMCb.
  (* [comment removed for export] *)
  apply evtF_done.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MUc. pose proof (wmono_refl asegs m3) as WMc.
  pose proof MId as MIc. pose proof STd as STc.
  (* [comment removed for export] *)
  xport STATSd MUc WMc ltac:(exact I). xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport LHd MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport PGJ MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I).
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (F5 : forall A l v, fill_at m3 A l v -> fill_at m3 A l v).
  { intros A l v H. eapply fill_frame; [exact H | exact MUc | exact WMc | intros _; exact I]. }
  assert (DEP5 : ADEPOT DI L m3). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PCX5 : poison_cells m3). { eapply poison_cells_frame; [exact PCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PMC5 : premap_cells m3). { eapply premap_cells_frame; [exact PMCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (mallocS_W L spA t a ms) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA MSR NSE RSR N SG9 SG5; lia. }
  assert (WM : wmono asegs m m3).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  eapply KONT. unfold malloc_postS.
  split; [exact FPLE|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact STATSd|]. split; [exact LSJd|]. split; [exact HDR4|]. split; [eexists; exact PGJ|].
  split; [exact LHd|]. split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZJ3|].
  split. { change 17 with (Z.lor (Z.land (hdr_b1_mid 0) 243) 0). exact HDRd. }
  split. { rewrite skipn_repeat in UFd. exact UFd. }
  split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZT3|].
  split. { change 768 with (512 + 256). apply fill_merge; [apply F5; exact SHF13 | apply F5; exact SHFb3 | lia | lia]. }
  split.
  { unfold block_shadow_bytes. rewrite SGS, SGG.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
    - rewrite app_nil_r, Z.add_0_r. exact SHUb.
    - lazymatch goal with |- rw_cells _ _ _ [CB _ (?l1 ++ ?l2)] =>
        replace (Z.to_nat (shlen (n - n mod 8) + 1)) with (Z.to_nat (shlen (n - n mod 8)) + 1)%nat by (clear -SG5; lia) end.
      apply cb_app2; [exact SHUb|]. rewrite Z2Nat.id by (clear -SG5; lia).
      eapply rw_cells_recast; [exact (SHP5 M0) | cbn; tauto | reflexivity | reflexivity]. }
  split; [apply F5; exact SHTd|].
  split; [exact DEP5| split; [exact PCX5| exact PMC5]].
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="PR"] Lemma allocfn_tail_sec : ltac:(let t := eval cbv delta [allocfn_tail_sec__stmt] in allocfn_tail_sec__stmt in exact t).
Proof. exact allocfn_tail_sec__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_aallocfn_tailS.

(* [comment removed for export] *)
Module AInstance.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFAKE.

#[using="Type"] Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of.
Proof. reflexivity. Qed.

#[using="Type"] Theorem AHI_laws : ahole_laws AHI.
Proof.
  constructor; cbn [AHI ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

#[using="Type"] Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof. rewrite <- AHI_eq. exact AHI_laws. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFAKE.

#[using="Type"] Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of.
Proof. reflexivity. Qed.

#[using="Type"] Theorem AHI_laws : ahole_laws AHI.
Proof.
  constructor; cbn [AHI ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

#[using="Type"] Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof. rewrite <- AHI_eq. exact AHI_laws. Qed.
End CANSEC1.
End TwB.
End AInstance.

(* [comment removed for export] *)
Module AMallocS.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_preS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_acallocS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
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
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma premap_of_rt' : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  (nd_pre RT3 17%nat; intros _ _ _ _ _ _ _ _ _ _ R11 R12 R13 R14 R15 R16 R17; nd_post).
  (nd_pre RT2 3%nat; intros _ Q2 _; nd_post).
  pose proof R11 as R11a. rw_split R11a 1%nat R11h R11t.
  unfold premap_cells. split; [exact R11h|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.
#[using="Type"] Lemma poison_cells_of_rt' : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

#[using="Type"] Lemma Z_to_bv8_bv_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition amalloc_sec__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 40).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 41).
Let ms := sec_map_size n.
#[using="HL PR CI_OK CI_OK2 ms"] Lemma amalloc_sec__body : ltac:(let T := type of (fun (h : amalloc_sec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ (kP & OPs & OPsa & OPsb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  (* [comment removed for export] *)
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec_sec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold malloc_pre_postS in P4.
  (nd_pre P4 24%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s0A s1A s2A s3A s4A s5A s0i fr0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 13%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof AR4 as AR0. (nd_pre AR0 12%nat; intros _ RT' INST' THR' _ _ HS' HD' HRO' RT2' _ RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' _ _ _ [sj4 [STATS' LSJ']] _; nd_post).
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (nd_pre HS0 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre INST2 6%nat; intros J80 [srt J128] J136 J168 J681 J704; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  (* [comment removed for export] *)
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  (* [comment removed for export] *)
  assert (MTX : rw_cells asegs m4 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app asegs m4 0xab240 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  (* [comment removed for export] *)
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells asegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  (* [comment removed for export] *)
  (nd_pre RT2' 3%nat; intros Q1' Q2' Q3'; nd_post).
  pose proof RT3' as RT30. (nd_pre RT30 13%nat; intros _ _ _ _ _ _ _ _ _ _ R11' R12' _; nd_post).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells asegs m4 0xaafd8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app asegs m4 0xaafd8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app asegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  (* [comment removed for export] *)
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0 /\ tclr a ms).
  { intros a HF.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *)
    (pose proof (valid_clear L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p _ _ _ _ C_l _; nd_post). fold ms in C_t, C_c, C_p, C_l.      (* [comment removed for export] *)
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|]. split; [| exact C_l].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; Z.div_mod_to_equations; lia].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; Z.div_mod_to_equations; lia| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  (* [comment removed for export] *)
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono asegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk asegs m' lo (bv_unsigned sp - 2272) ->
    implS asegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *) unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. (pose proof VC as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahmx; nd_post).      (* [comment removed for export] *)
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    (nd_pre LP 27%nat; intros FPLE BW _ _ _ MUL WML MIL STL HDRP ZB SHF1 SHZ0 SHF2 RCH RSCH INS SRT JST JBS MTX9 JGL [sj9 [STATS9 LSJ9]] PAS DISJ NRB' LC'; nd_post).
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned sp) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3; unfold AMALLOC_STACK in *; lia). }
    (* [comment removed for export] *)
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (700312 + 112, 700312 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono asegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear. intros q Hq. lia. }
    (* [comment removed for export] *)
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    (nd_pre RT0 28%nat; intros _ _ _ _ LS1L _ _ _ FLGL HPPL _ _ _ _ _ _ _ _ _ HK2L _ _ _ _ _ LS2L CT8L _; nd_post).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    (nd_pre LC' 10%nat; intros _ PCL _ _ TIL TKL T88L TSDL CTL I64L; nd_post).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells asegs m' 0xaafb8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells asegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; lia_relc|]).
      apply Forall_nil. }
    subst WS.
    (* [comment removed for export] *)
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FR16 MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FRS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    (* [comment removed for export] *)
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. 
    assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    (* [comment removed for export] *)
    eapply (malloc_tail_sec DI PR L RNG' _ _ _ ra sp gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ = _ => exact HspA
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP | exact HspA]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => exact C_l
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    (* [comment removed for export] *)
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    (nd_pre PM 21%nat; intros FPLE5 MU5 WM5 MI5 ST5 IDR STATS5 LSJ5 HDR5 PGJ5 MAG5 LCJ5 AHD5 USR5 TLJ5 SHF5 SHU5 SHT5 DEP5 PC5 PMC5; nd_post).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    (* [comment removed for export] *)
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 700448 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 700480 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 701016 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    (* [comment removed for export] *)
    assert (MUW : munch (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB; intros q Hq; lia. }
    assert (WMW : wmono asegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned sp) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO BOT STK3 SP47 IDR NRB'; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ RSRx _ NSEx MSEx _; nd_post). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. Z.div_mod_to_equations. lia. }
    intros _. unfold aptr_addr. (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  (* [comment removed for export] *)
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3   (* [comment removed for export] *)
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1   (* [comment removed for export] *)
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- tclr _ _ => exact (tclr_ptr L ALO)      (* [comment removed for export] *)
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - (* [comment removed for export] *) exact JSL.
  - (* [comment removed for export] *) exact FROK.
  - (* [comment removed for export] *)
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  - (* [comment removed for export] *)
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  - (* [comment removed for export] *)
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    (nd_pre LP0 27%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End Zd1.
#[using="HL PR CI_OK CI_OK2"] Theorem amalloc_sec : ltac:(let t := eval cbv delta [amalloc_sec__stmt] in amalloc_sec__stmt in exact t).
Proof. exact amalloc_sec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_preS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_acallocS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
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
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma premap_of_rt' : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  (nd_pre RT3 17%nat; intros _ _ _ _ _ _ _ _ _ _ R11 R12 R13 R14 R15 R16 R17; nd_post).
  (nd_pre RT2 3%nat; intros _ Q2 _; nd_post).
  pose proof R11 as R11a. rw_split R11a 1%nat R11h R11t.
  unfold premap_cells. split; [exact R11h|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.
#[using="Type"] Lemma poison_cells_of_rt' : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

#[using="Type"] Lemma Z_to_bv8_bv_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition amalloc_sec__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 40).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'amalloc_sec__stmt 41).
Let ms := sec_map_size n.
#[using="HL PR CI_OK CI_OK2 ms"] Lemma amalloc_sec__body : ltac:(let T := type of (fun (h : amalloc_sec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ (kP & OPs & OPsa & OPsb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  (* [comment removed for export] *)
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec_sec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold malloc_pre_postS in P4.
  (nd_pre P4 24%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s0A s1A s2A s3A s4A s5A s0i fr0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 13%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof AR4 as AR0. (nd_pre AR0 12%nat; intros _ RT' INST' THR' _ _ HS' HD' HRO' RT2' _ RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' _ _ _ [sj4 [STATS' LSJ']] _; nd_post).
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (nd_pre HS0 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre INST2 6%nat; intros J80 [srt J128] J136 J168 J681 J704; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  (* [comment removed for export] *)
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  (* [comment removed for export] *)
  assert (MTX : rw_cells asegs m4 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app asegs m4 0xab640 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  (* [comment removed for export] *)
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells asegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  (* [comment removed for export] *)
  (nd_pre RT2' 3%nat; intros Q1' Q2' Q3'; nd_post).
  pose proof RT3' as RT30. (nd_pre RT30 13%nat; intros _ _ _ _ _ _ _ _ _ _ R11' R12' _; nd_post).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells asegs m4 0xab3d8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app asegs m4 0xab3d8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app asegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  (* [comment removed for export] *)
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0 /\ tclr a ms).
  { intros a HF.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *)
    (pose proof (valid_clear L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p _ _ _ _ C_l _; nd_post). fold ms in C_t, C_c, C_p, C_l.      (* [comment removed for export] *)
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|]. split; [| exact C_l].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; Z.div_mod_to_equations; lia].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; Z.div_mod_to_equations; lia| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  (* [comment removed for export] *)
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono asegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk asegs m' lo (bv_unsigned sp - 2272) ->
    implS asegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *) unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. (pose proof VC as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahmx; nd_post).      (* [comment removed for export] *)
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    (nd_pre LP 27%nat; intros FPLE BW _ _ _ MUL WML MIL STL HDRP ZB SHF1 SHZ0 SHF2 RCH RSCH INS SRT JST JBS MTX9 JGL [sj9 [STATS9 LSJ9]] PAS DISJ NRB' LC'; nd_post).
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned sp) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3; unfold AMALLOC_STACK in *; lia). }
    (* [comment removed for export] *)
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (701336 + 112, 701336 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono asegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear. intros q Hq. lia. }
    (* [comment removed for export] *)
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    (nd_pre RT0 28%nat; intros _ _ _ _ LS1L _ _ _ FLGL HPPL _ _ _ _ _ _ _ _ _ HK2L _ _ _ _ _ LS2L CT8L _; nd_post).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    (nd_pre LC' 10%nat; intros _ PCL _ _ TIL TKL T88L TSDL CTL I64L; nd_post).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells asegs m' 0xab3b8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells asegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; lia_relc|]).
      apply Forall_nil. }
    subst WS.
    (* [comment removed for export] *)
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FR16 MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FRS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    (* [comment removed for export] *)
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. 
    assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    (* [comment removed for export] *)
    eapply (malloc_tail_sec DI PR L RNG' _ _ _ ra sp gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ = _ => exact HspA
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP | exact HspA]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => exact C_l
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    (* [comment removed for export] *)
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    (nd_pre PM 21%nat; intros FPLE5 MU5 WM5 MI5 ST5 IDR STATS5 LSJ5 HDR5 PGJ5 MAG5 LCJ5 AHD5 USR5 TLJ5 SHF5 SHU5 SHT5 DEP5 PC5 PMC5; nd_post).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    (* [comment removed for export] *)
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 701472 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 701504 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 702040 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    (* [comment removed for export] *)
    assert (MUW : munch (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB; intros q Hq; lia. }
    assert (WMW : wmono asegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned sp) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO BOT STK3 SP47 IDR NRB'; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ RSRx _ NSEx MSEx _; nd_post). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. Z.div_mod_to_equations. lia. }
    intros _. unfold aptr_addr. (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  (* [comment removed for export] *)
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3   (* [comment removed for export] *)
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1   (* [comment removed for export] *)
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- tclr _ _ => exact (tclr_ptr L ALO)      (* [comment removed for export] *)
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - (* [comment removed for export] *) exact JSL.
  - (* [comment removed for export] *) exact FROK.
  - (* [comment removed for export] *)
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  - (* [comment removed for export] *)
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  - (* [comment removed for export] *)
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    (nd_pre LP0 27%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End Zd1.
#[using="HL PR CI_OK CI_OK2"] Theorem amalloc_sec : ltac:(let t := eval cbv delta [amalloc_sec__stmt] in amalloc_sec__stmt in exact t).
Proof. exact amalloc_sec__body. Qed.
End S.
End CANSEC1.
End TwB.
End AMallocS.

(* [comment removed for export] *)
Module AAllocFnS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_alarge. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_preS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_acallocS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_aallocfn_tailS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
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
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition allocfn_sec__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned spA - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 2).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 39).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 40).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 43).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 44).
Let ms := sec_map_size n.
#[using="HL PR CI_OK CI_OK2 ms"] Lemma allocfn_sec__body : ltac:(let T := type of (fun (h : allocfn_sec__stmt) => h L RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo SO pc trc tb RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (spA, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (SO, (pc, (trc, (tb, RESV))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SGE S47 SPV SS0 TB0 LTB TRF0 TRU LTRC RSTKA RS ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  (* [comment removed for export] *)
  word_range spA SPRA.
  pose (sp := Z_to_bv 64 (bv_unsigned spA + 2144)).
  assert (HspA : bv_unsigned spA = bv_unsigned sp - 2144) by (subst sp; rewrite unsigned_lit by (clear -SPRA SPV; lia); clear; lia).
  clearbody sp.
  assert (LO : lo <= bv_unsigned sp - AMALLOC_STACK) by (clear -LOA HspA; unfold AMALLOC_STACK in *; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ (kP & OPs & OPsa & OPsb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  (* [comment removed for export] *)
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec_sec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LOA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 SGE SPRA S47;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_postS in P4.
  (nd_pre P4 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MU4' WM4 MI4 ST4 [fr0 FRa]; nd_post).
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).
  assert (MU4 : munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2144); (al_t L + 3168, al_t L + 3169)]%Z m m4)
    by (eapply munch_weaken; [| exact MU4']; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA; lia).
  (* [comment removed for export] *)
  pose proof SS0 as SS. pose proof TB0 as TB. pose proof TRF0 as TRF.
  xport SS MU4' WM4 ltac:(clear -SGE; lia). xport TB MU4' WM4 ltac:(rewrite LTB; clear -SGE; lia).
  pose proof UNW as UW4. xport UW4 MU4' WM4 ltac:(clear -LOA BOT TL2; unfold AMALLOC_STACK in *; lia).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3 LOA SPRA HspA; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof AR4 as AR0. (nd_pre AR0 12%nat; intros _ RT' INST' THR' _ _ HS' HD' HRO' RT2' _ RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' _ _ _ [sj4 [STATS' LSJ']] _; nd_post).
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (nd_pre HS0 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre INST2 6%nat; intros J80 [srt J128] J136 J168 J681 J704; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  (* [comment removed for export] *)
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  (* [comment removed for export] *)
  assert (MTX : rw_cells asegs m4 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app asegs m4 0xab240 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  (* [comment removed for export] *)
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells asegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  (* [comment removed for export] *)
  (nd_pre RT2' 3%nat; intros Q1' Q2' Q3'; nd_post).
  pose proof RT3' as RT30. (nd_pre RT30 13%nat; intros _ _ _ _ _ _ _ _ _ _ R11' R12' _; nd_post).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells asegs m4 0xaafd8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app asegs m4 0xaafd8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app asegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  (* [comment removed for export] *)
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0 /\ tclr a ms).
  { intros a HF.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *)
    (pose proof (valid_clear L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p _ _ _ _ C_l _; nd_post). fold ms in C_t, C_c, C_p, C_l.      (* [comment removed for export] *)
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|]. split; [| exact C_l].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; Z.div_mod_to_equations; lia].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; Z.div_mod_to_equations; lia| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  (* [comment removed for export] *)
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono asegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk asegs m' lo (bv_unsigned sp - 2272) ->
    implS asegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 SO) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x33ea8) fc None m' (seg_rom asegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *) unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. (pose proof VC as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahmx; nd_post).      (* [comment removed for export] *)
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    (nd_pre LP 27%nat; intros FPLE BW _ _ _ MUL WML MIL STL HDRP ZB SHF1 SHZ0 SHF2 RCH RSCH INS SRT JST JBS MTX9 JGL [sj9 [STATS9 LSJ9]] PAS DISJ NRB' LC'; nd_post).
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3 LOA SPRA HspA; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned spA) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3 LOA SPRA HspA; unfold AMALLOC_STACK in *; lia). }
    (* [comment removed for export] *)
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (700312 + 112, 700312 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono asegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned spA) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear -HspA. intros q Hq. lia. }
    (* [comment removed for export] *)
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    (nd_pre RT0 28%nat; intros _ _ _ _ LS1L _ _ _ FLGL HPPL _ _ _ _ _ _ _ _ _ HK2L _ _ _ _ _ LS2L CT8L _; nd_post).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    (nd_pre LC' 10%nat; intros _ PCL _ _ TIL TKL T88L TSDL CTL I64L; nd_post).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells asegs m' 0xaafb8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells asegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; lia_relc|]).
      apply Forall_nil. }
    subst WS.
    (* [comment removed for export] *)
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SGE S47 HspA SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SGE S47 HspA SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    (* [comment removed for export] *)
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. 
    assert (RSTK' : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTKA]).
    assert (RS' : rng RNG' SO 2056) by (eapply rng_fp_le; [exact FPLE| exact RS]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    (* [comment removed for export] *)
    replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in STc, FRa by (clear -HspA; lia).
    eapply (allocfn_tail_sec DI PR L RNG' _ _ _ ra gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) SO pc fr0 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ <= _ => exact SGE
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => exact C_l
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO LOA HspA SGE S47 SPRA BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    (* [comment removed for export] *)
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    (nd_pre PM 21%nat; intros FPLE5 MU5 WM5 MI5 ST5 IDR STATS5 LSJ5 HDR5 PGJ5 MAG5 LCJ5 AHD5 USR5 TLJ5 SHF5 SHU5 SHT5 DEP5 PC5 PMC5; nd_post).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    (* [comment removed for export] *)
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 700448 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 700480 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 701016 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    (* [comment removed for export] *)
    assert (MUW : munch (WT L (bv_unsigned spA) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB HspA; intros q Hq; lia. }
    assert (WMW : wmono asegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned spA) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO LOA HspA BOT STK3 SP47 IDR NRB' SPRA; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ RSRx _ NSEx MSEx _; nd_post). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. Z.div_mod_to_equations. lia. }
    intros _. unfold aptr_addr. (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  (* [comment removed for export] *)
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3   (* [comment removed for export] *)
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1   (* [comment removed for export] *)
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- tclr _ _ => exact (tclr_ptr L ALO)      (* [comment removed for export] *)
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTKA|]; clear -LO LOA HspA SP47 BOT STK3 SPRA; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi LOA SPRA; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - (* [comment removed for export] *) exact JSL.
  - (* [comment removed for export] *) exact FROK.
  - (* [comment removed for export] *)
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  - (* [comment removed for export] *)
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  - (* [comment removed for export] *)
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    (nd_pre LP0 27%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End Zd1.
#[using="HL PR CI_OK CI_OK2"] Theorem allocfn_sec : ltac:(let t := eval cbv delta [allocfn_sec__stmt] in allocfn_sec__stmt in exact t).
Proof. exact allocfn_sec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_preS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_alarge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_acallocS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_amalloc_tailS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.F_aallocfn_tailS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
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
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition allocfn_sec__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned spA - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 2).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 39).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 40).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 43).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'allocfn_sec__stmt 44).
Let ms := sec_map_size n.
#[using="HL PR CI_OK CI_OK2 ms"] Lemma allocfn_sec__body : ltac:(let T := type of (fun (h : allocfn_sec__stmt) => h L RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo SO pc trc tb RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (spA, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (SO, (pc, (trc, (tb, RESV))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SGE S47 SPV SS0 TB0 LTB TRF0 TRU LTRC RSTKA RS ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  (* [comment removed for export] *)
  word_range spA SPRA.
  pose (sp := Z_to_bv 64 (bv_unsigned spA + 2144)).
  assert (HspA : bv_unsigned spA = bv_unsigned sp - 2144) by (subst sp; rewrite unsigned_lit by (clear -SPRA SPV; lia); clear; lia).
  clearbody sp.
  assert (LO : lo <= bv_unsigned sp - AMALLOC_STACK) by (clear -LOA HspA; unfold AMALLOC_STACK in *; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ (kP & OPs & OPsa & OPsb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  (* [comment removed for export] *)
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec_sec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LOA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 SGE SPRA S47;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_postS in P4.
  (nd_pre P4 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MU4' WM4 MI4 ST4 [fr0 FRa]; nd_post).
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).
  assert (MU4 : munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2144); (al_t L + 3168, al_t L + 3169)]%Z m m4)
    by (eapply munch_weaken; [| exact MU4']; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA; lia).
  (* [comment removed for export] *)
  pose proof SS0 as SS. pose proof TB0 as TB. pose proof TRF0 as TRF.
  xport SS MU4' WM4 ltac:(clear -SGE; lia). xport TB MU4' WM4 ltac:(rewrite LTB; clear -SGE; lia).
  pose proof UNW as UW4. xport UW4 MU4' WM4 ltac:(clear -LOA BOT TL2; unfold AMALLOC_STACK in *; lia).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3 LOA SPRA HspA; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof AR4 as AR0. (nd_pre AR0 12%nat; intros _ RT' INST' THR' _ _ HS' HD' HRO' RT2' _ RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' _ _ _ [sj4 [STATS' LSJ']] _; nd_post).
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (nd_pre HS0 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre INST2 6%nat; intros J80 [srt J128] J136 J168 J681 J704; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  (* [comment removed for export] *)
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  (* [comment removed for export] *)
  assert (MTX : rw_cells asegs m4 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app asegs m4 0xab640 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  (* [comment removed for export] *)
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells asegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  (* [comment removed for export] *)
  (nd_pre RT2' 3%nat; intros Q1' Q2' Q3'; nd_post).
  pose proof RT3' as RT30. (nd_pre RT30 13%nat; intros _ _ _ _ _ _ _ _ _ _ R11' R12' _; nd_post).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells asegs m4 0xab3d8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app asegs m4 0xab3d8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app asegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  (* [comment removed for export] *)
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0 /\ tclr a ms).
  { intros a HF.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *)
    (pose proof (valid_clear L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p _ _ _ _ C_l _; nd_post). fold ms in C_t, C_c, C_p, C_l.      (* [comment removed for export] *)
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|]. split; [| exact C_l].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; Z.div_mod_to_equations; lia].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; Z.div_mod_to_equations; lia| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  (* [comment removed for export] *)
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono asegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk asegs m' lo (bv_unsigned sp - 2272) ->
    implS asegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 SO) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x33f10) fc None m' (seg_rom asegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    (pose proof (valid_geo L RESV st n a N PRIM HF ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
    (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post). (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSBx; nd_post). fold ms in MSBx.   (* [comment removed for export] *)
    (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) 6%nat; intros kS ASD ASDa ASDb SA1 SA3; nd_post).   (* [comment removed for export] *) unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. (pose proof VC as ndP__; nd_pre ndP__ 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahmx; nd_post).      (* [comment removed for export] *)
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    (nd_pre LP 27%nat; intros FPLE BW _ _ _ MUL WML MIL STL HDRP ZB SHF1 SHZ0 SHF2 RCH RSCH INS SRT JST JBS MTX9 JGL [sj9 [STATS9 LSJ9]] PAS DISJ NRB' LC'; nd_post).
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3 LOA SPRA HspA; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned spA) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3 LOA SPRA HspA; unfold AMALLOC_STACK in *; lia). }
    (* [comment removed for export] *)
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (701336 + 112, 701336 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono asegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned spA) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear -HspA. intros q Hq. lia. }
    (* [comment removed for export] *)
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    (nd_pre RT0 28%nat; intros _ _ _ _ LS1L _ _ _ FLGL HPPL _ _ _ _ _ _ _ _ _ HK2L _ _ _ _ _ LS2L CT8L _; nd_post).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    (nd_pre LC' 10%nat; intros _ PCL _ _ TIL TKL T88L TSDL CTL I64L; nd_post).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells asegs m' 0xab3b8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells asegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; lia_relc|]).
      apply Forall_nil. }
    subst WS.
    (* [comment removed for export] *)
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SGE S47 HspA SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SGE S47 HspA SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    (* [comment removed for export] *)
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. 
    assert (RSTK' : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTKA]).
    assert (RS' : rng RNG' SO 2056) by (eapply rng_fp_le; [exact FPLE| exact RS]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    (* [comment removed for export] *)
    replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in STc, FRa by (clear -HspA; lia).
    eapply (allocfn_tail_sec DI PR L RNG' _ _ _ ra gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) SO pc fr0 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ <= _ => exact SGE
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => exact C_l
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO LOA HspA SGE S47 SPRA BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    (* [comment removed for export] *)
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    (nd_pre PM 21%nat; intros FPLE5 MU5 WM5 MI5 ST5 IDR STATS5 LSJ5 HDR5 PGJ5 MAG5 LCJ5 AHD5 USR5 TLJ5 SHF5 SHU5 SHT5 DEP5 PC5 PMC5; nd_post).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    (* [comment removed for export] *)
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 701472 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 701504 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 702040 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb LOA SPRA HspA; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    (* [comment removed for export] *)
    assert (MUW : munch (WT L (bv_unsigned spA) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB HspA; intros q Hq; lia. }
    assert (WMW : wmono asegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned spA) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO LOA HspA BOT STK3 SP47 IDR NRB' SPRA; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ RSRx _ NSEx MSEx _; nd_post). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. Z.div_mod_to_equations. lia. }
    intros _. unfold aptr_addr. (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  (* [comment removed for export] *)
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3   (* [comment removed for export] *)
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1   (* [comment removed for export] *)
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- tclr _ _ => exact (tclr_ptr L ALO)      (* [comment removed for export] *)
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTKA|]; clear -LO LOA HspA SP47 BOT STK3 SPRA; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi LOA SPRA; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - (* [comment removed for export] *) exact JSL.
  - (* [comment removed for export] *) exact FROK.
  - (* [comment removed for export] *)
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  - (* [comment removed for export] *)
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  - (* [comment removed for export] *)
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3 LOA SPRA; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    (nd_pre LP0 27%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NRB' _; nd_post).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End Zd1.
#[using="HL PR CI_OK CI_OK2"] Theorem allocfn_sec : ltac:(let t := eval cbv delta [allocfn_sec__stmt] in allocfn_sec__stmt in exact t).
Proof. exact allocfn_sec__body. Qed.
End S.
End CANSEC1.
End TwB.
End AAllocFnS.

(* [comment removed for export] *)
Module AInstanceM.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation AHEAP_I := (AHEAP_P AHI).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma AHI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG' st LB m.
Proof.
  intros L RNG RNG' st LB m LE (ALO & ARNG & XB & HFK). split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.

#[using="Type"] Lemma hb_ids_perm : forall LB LB', Permutation LB LB' -> Permutation (hb_ids LB) (hb_ids LB').
Proof.
  intros LB LB' P. unfold hb_ids. induction P; cbn.
  - constructor.
  - apply Permutation_app_head. exact IHP.
  - rewrite !app_assoc. apply Permutation_app_tail. destruct (ab_kind y), (ab_kind x); cbn; try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

#[using="Type"] Lemma AHI_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHI ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

#[using="Type"] Lemma AHI_blocks_nodup : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup LB.
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & _ & B4)]] & _). exact B4. Qed.
#[using="Type"] Lemma AHI_hb_ids : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup (hb_ids LB).
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & B3 & _)]] & _). exact B3. Qed.

#[using="Type"] Lemma AHI_layout : forall L RNG st LB m, AHEAP_I L RNG st LB m ->
  al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096)
  /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
  /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP.
Proof.
  intros L RNG st LB m (ALO & _ & [X [AR _]] & _).
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof (ao_U L ALO) as U. pose proof (ao_fake L ALO) as FK.
  pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
  unfold aobj, AIMG_HI in *.
  destruct AR as ((SBE & _) & _).
  repeat lazymatch goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

#[using="Type"] Lemma AHI_relro : forall L RNG st LB m, AHEAP_I L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros L RNG st LB m H. eapply AHEAP_P_relro. exact H. Qed.

#[using="Type"] Lemma AHI_rtcells : forall L RNG st LB m, AHEAP_I L RNG st LB m -> artcells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _).
  (nd_pre AR 12%nat; intros _ RT _ _ _ _ _ _ _ RT2 _ RT3; nd_post).
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  (nd_pre RT2 3%nat; intros Q1 Q2 Q3; nd_post).
  (nd_pre RT3 17%nat; intros S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17; nd_post).
  unfold artcells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma hb_cases : forall L st X LB m p A n,
  alayout_ok L -> AREP AHI L st X m -> ablocks L st X LB -> In (HB p A n) LB ->
  (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_user L b = A /\ xb_n b = n
      /\ 1 <= xb_class b < K_NUM_CLASSES /\ 1 <= n <= AREQMAX /\ rounded_size n + rz_size n <= size_of_class (xb_class b)
      /\ (a_live st) !! p = Some (CPrim (xb_class b) n) /\ is_primary n = true
      /\ 0 <= xb_slot b < ndist st (xb_class b)
      /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
      /\ al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104)
  \/ (exists mb ms, (a_live st) !! p = Some (CSec mb ms n) /\ A = mb + SEC_UOFF /\ sec_wf1 L (CSec mb ms n) /\ is_primary n = false
      /\ In (CSec mb ms n) (sec_chunks_of st)).
Proof.
  intros L st X LB m p A n ALO AR BL Hin.
  pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  - left. exists b. destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 6%nat; intros N0 FIT _ _ _ LV; nd_post).
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    pose proof (ao_space L ALO) as RSP. subst n.
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear -CLB N0 KB; lia).
    all: try (unfold is_primary, needed0, K_MAX_SIZE; apply Z.leb_le; clear -FIT QS; lia).
    all: unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *; clear -P5 P4 Q1 Q2 CLB RSP; lia.
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros _ _ _ _ _ G6 _; nd_post).
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
    apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
Qed.

#[using="Type"] Lemma AHI_block_bounds : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros L RNG st LB m b AH Hin. destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - (pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 R4; nd_post). apply ablk_lin in R1. unfold AIMG_HI in *. clear -R1 R2 R3. lia.   (* [comment removed for export] *)
  - (nd_pre AH 4%nat; intros ALO _ [X [_ (_ & BF & _)]] _; nd_post). (nd_pre (BF cls A n Hin) 3%nat; intros K1 K2 K3; nd_post).
    pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
    unfold aobj, AIMG_HI in *. clear -K1 K2 K3 FK FKI. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nodup_map_inj : forall {A B} (f : A -> B) (l : list A) x y,
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | |].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma nodup_filter_map_inj : forall {A B} (g : B -> bool) (f : A -> B) (l : list A) x y,
  List.NoDup (List.filter g (map f l)) -> In x l -> In y l -> f x = f y -> g (f x) = true -> x = y.
Proof.
  intros A B g f l. induction l as [|a l IH]; intros x y ND Hx Hy E G; [destruct Hx|].
  cbn in ND.
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
  - subst. reflexivity.
  - subst a. exfalso. rewrite G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [rewrite E; apply in_map; exact Hy| exact G].
  - subst a. exfalso. rewrite <- E, G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [apply in_map; exact Hx| exact G].
  - apply IH; try assumption. destruct (g (f a)); [inversion ND; assumption| exact ND].
Qed.

#[using="Type"] Lemma AHI_blocks_disjoint : forall L RNG st LB m b1 b2,
  AHEAP_I L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
Proof.
  intros L RNG st LB m b1 b2 AH H1 H2 NE.
  (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D_f_res. unfold aobj, adisj in ORS, OFK, D_f_res.
  destruct b1 as [[p1|c1] A1 n1]; destruct b2 as [[p2|c2] A2 n2]; cbn [ab_addr ab_size].
  - (* [comment removed for export] *)
    assert (NEP : p1 <> p2).
    { intros <-. (pose proof BL as ndP__; nd_pre ndP__ 4%nat; intros _ _ NDI _; nd_post).
      assert (E : HB p1 A1 n1 = HB p1 A2 n2).
      { apply (nodup_filter_map_inj (fun k => match k with ABHeap _ => true | _ => false end) ab_kind LB); try assumption; try reflexivity.
        unfold hb_ids in NDI. clear -NDI. induction LB as [|b LB IH]; cbn; [constructor|]. cbn in NDI.
        destruct b as [[q|c] B k]; cbn in NDI |- *; [| apply IH; exact NDI]. inversion NDI as [|q' l' NI ND']; subst. constructor; [| apply IH; exact ND'].
        intros Hin. apply NI. apply List.filter_In in Hin. destruct Hin as [Hin _]. apply in_map_iff in Hin. (nd_pre Hin 3%nat; intros b' Eb Hb'; nd_post).
        apply in_flat_map. exists b'. split; [exact Hb'|]. destruct b' as [[q''|c''] B' k']; cbn in Eb |- *; [| discriminate]. injection Eb as ->. left; reflexivity. }
      exact (NE E). }
    destruct (hb_cases L st X LB m p1 A1 n1 ALO AR BL H1) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & _ & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & _ & INC)];
    destruct (hb_cases L st X LB m p2 A2 n2 ALO AR BL H2) as [(b' & Hb' & Sb' & Ub' & Nb' & CLB' & NB' & FIT' & LV' & _ & KB' & P5' & P4' & R1' & R2')|(mb' & ms' & Lp' & EA' & G' & _ & INC')].
    + (* [comment removed for export] *)
      destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
      assert (NEB : b <> b') by (intros <-; apply NEP; rewrite Sb in Sb'; injection Sb' as E; exact E).
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      pose proof (rounded_size_ge (xb_n b')) as RG'. pose proof (rz_size_ge16 (xb_n b')) as RZ'.
      pose proof (size_of_class_facts (xb_class b) CLB) as [QS _]. pose proof (size_of_class_facts (xb_class b') CLB') as [QS' _].
      assert (SL : xb_alloc L b + size_of_class (xb_class b) <= xb_alloc L b' \/ xb_alloc L b' + size_of_class (xb_class b') <= xb_alloc L b).
      { destruct (Z.eq_dec (xb_class b) (xb_class b')) as [EC|NC].
        - (* [comment removed for export] *)
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 _ _ _ _ _ _ _ _ _ ND _; nd_post).
          assert (NK : xb_slot b <> xb_slot b').
          { intros EK. apply NEB. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X))).
            - apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. exact ND.
            - apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
            - apply List.filter_In. split; [exact Hb'| rewrite EC; apply Z.eqb_refl].
            - exact EK. }
          unfold xb_alloc. rewrite <- EC. apply slots_disjoint; [clear -KB; lia| clear -KB'; lia| exact NK| clear -QS; lia].
        - (* [comment removed for export] *)
          (nd_pre (PERC (xb_class b) CLB) 3%nat; intros Q1 Q2 _; nd_post). (nd_pre (PERC (xb_class b') CLB') 3%nat; intros Q1' Q2' _; nd_post).
          unfold K_FREEARR_OFF in Q2, Q2'.
          destruct (Z.lt_ge_cases (xb_class b) (xb_class b')) as [LT|GE].
          + left. pose proof (regions_sep L (xb_class b) (xb_class b') LT) as RS. unfold K_REGION in RS. clear -RS P4 P5' Q1 Q2. lia.
          + right. pose proof (regions_sep L (xb_class b') (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS P4' P5 Q1' Q2'. lia. }
      subst A1 n1 A2 n2. unfold xb_user. clear -SL FIT FIT' RG RZ RG' RZ' NB NB'. lia.
    + cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros G1 G2 G3 G4 G5 G6 (_ & _ & Cr & _); nd_post).
      pose proof (sec_facts n2 ltac:(clear -G5; lia) G6) as SF. subst A2. unfold SEC_UOFF, xb_user in *. subst A1 n1.
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      clear -R1 R2 FIT RG RZ Cr G3 G4 G5 SF NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 (_ & _ & Cr & _); nd_post).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. subst A1. unfold SEC_UOFF, xb_user in *. subst A2 n2.
      pose proof (rounded_size_ge (xb_n b')) as RG. pose proof (rz_size_ge16 (xb_n b')) as RZ.
      clear -R1' R2' FIT' RG RZ Cr G3 G4 G5 SF NB'. lia.
    + (* [comment removed for export] *)
      (nd_pre AR 8%nat; intros WF _ _ _ _ _ HS _; nd_post). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS.
      destruct HS as ((_ & _ & _ & _ & _ & _ & [ND PW]) & _).
      cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post). cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros G1' G2' G3' G4' G5' G6' _; nd_post).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. pose proof (sec_facts n2 ltac:(clear -G5'; lia) G6') as SF'.
      assert (NEC : CSec mb ms n1 <> CSec mb' ms' n2).
      { intros EC. apply NEP.
        assert (E : (p1, CSec mb ms n1) = (p2, CSec mb' ms' n2)); [| injection E as E1 _ _ _; exact E1].
        apply (nodup_filter_map_inj is_sec snd (map_to_list (a_live st))).
        - unfold sec_chunks_of, achunks in ND. rewrite filter_is_sec_app in ND. apply List.NoDup_app_remove_r in ND. exact ND.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp'.
        - cbn. exact EC.
        - reflexivity. }
      pose proof (PW _ _ INC INC' NEC) as D. cbn [sec_mb sec_ms] in D. subst A1 A2. unfold SEC_UOFF. clear -D G4 G4' G5 G5' SF SF'. lia.
  - (* [comment removed for export] *)
    pose proof (AHEAP_P_hb_fake _ L RNG st LB m p1 A1 n1 AH H1) as D1.
    (nd_pre (afake_lb L LB m c2 A2 n2 HFK H2) 7%nat; intros _ _ K3 _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -D1 K3 K5 K6. lia.
  - pose proof (AHEAP_P_hb_fake _ L RNG st LB m p2 A2 n2 AH H2) as D2.
    (nd_pre (afake_lb L LB m c1 A1 n1 HFK H1) 7%nat; intros _ _ K3 _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -D2 K3 K5 K6. lia.
  - (* [comment removed for export] *) eapply afake_lb_disjoint; [exact HFK| exact H1| exact H2| exact NE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_join : forall m A a b, wr_at asegs m A a -> wr_at asegs m (A + a) b -> 0 <= a -> 0 <= b -> wr_at asegs m A (a + b).
Proof.
  intros m A a b (W0 & W1 & W) (V0 & V1 & V) Ha Hb. split; [exact W0|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i a) as [L|G]; [apply W; lia|]. replace (A + i) with (A + a + (i - a)) by lia. apply V. lia.
Qed.
#[using="Type"] Lemma wr_at_nil : forall m A, 0 <= A <= 2^64 -> wr_at asegs m A 0.
Proof. intros m A H. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.
#[using="Type"] Lemma wr_of_cells : forall m A cs, rw_cells asegs m A cs -> wr_at asegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ W]. exact W. Qed.
#[using="Type"] Lemma wr_of_junk : forall m A n, 0 <= n -> junk_at m A n -> wr_at asegs m A n.
Proof. intros m A n Hn [bs H]. pose proof (wr_of_cells _ _ _ H) as W. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by exact Hn. exact W. Qed.
#[using="Type"] Lemma wr_of_fill : forall m A n v, 0 <= n -> fill_at m A n v -> wr_at asegs m A n.
Proof. intros m A n v Hn H. apply (wr_of_junk m A n Hn). eapply fill_is_junk. exact H. Qed.
#[using="Type"] Lemma wr_of_azero : forall m A n, azero m A n -> wr_at asegs m A n.
Proof. intros m A n [_ W]. exact W. Qed.

Definition region_shadow_wr__stmt : Prop := forall L st X m c,
  AREP AHI L st X m -> 1 <= c < K_NUM_CLASSES -> wr_at asegs m (shad (aregion L c)) (shlen K_REGION).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 2).
Variable m : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 3).
Variable c : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 4).
Let r := get_cls st c.
Let S := size_of_class c.
#[using="r S"] Lemma region_shadow_wr__body : ltac:(let T := type of (fun (h : region_shadow_wr__stmt) => h L st X m c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (m, c))))) as _.
  intros AR Hc.
  (pose proof AR as ndP__; nd_pre ndP__ 12%nat; intros (SBE & PAE & SAL & SLO & SHI & PERC & _) _ _ _ CLS _ _ _ _ _ AVL _; nd_post).
  (nd_pre (CLS c Hc) 4%nat; intros _ (_ & _ & FAS) _ [SSH SFILL]; nd_post). destruct (AVL c Hc) as [AZ1 AZ2].
  (nd_pre (PERC c Hc) 8%nat; intros A1 A2 A3 A4 A5 A6 A7 _; nd_post).
  pose proof (size_of_class_facts c Hc) as [QS QS16].
  chg (get_cls st c) r. chg (size_of_class c) S.
  pose proof (aregion_mod L c SAL) as RM.
  assert (AL8 : c_allocated_user r mod 8 = 0) by (apply (mod16_of_class _ S); [exact A3| exact QS16| clear -QS; lia]).
  (* [comment removed for export] *)
  assert (SL : forall k : nat, Z.of_nat k <= ndist st c -> wr_at asegs m (shad (aregion L c)) (shlen (Z.of_nat k * S))).
  { induction k as [|k IH]; intros Hk.
    - cbn [Z.of_nat]. rewrite Z.mul_0_l. unfold shlen; cbn. apply wr_at_nil. rewrite shad_div. unfold ASHOFF. pose proof (alayout_space L) as _.
      unfold aregion, K_REGION. unfold K_NUM_CLASSES in Hc. clear -SLO SHI Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. Z.div_mod_to_equations. nia.
    - replace (shlen (Z.of_nat (Datatypes.S k) * S)) with (shlen (Z.of_nat k * S) + shlen S)
        by (rewrite !shlen_div; clear -QS16 QS; Z.div_mod_to_equations; nia).
      apply wr_at_join; [apply IH; lia| | rewrite shlen_div; clear -QS; Z.div_mod_to_equations; nia| rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia].
      pose proof (SSH (Z.of_nat k) ltac:(lia)) as CK. apply wr_of_cells in CK. cbn [cells_size csize] in CK. rewrite Nat.add_0_r, Z2Nat.id in CK by (rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia).
      replace (shad (aregion L c) + shlen (Z.of_nat k * S)) with (shad (aslot_addr L c (Z.of_nat k))); [exact CK|].
      unfold aslot_addr. fold S. rewrite shad_add_shlen; [reflexivity|]. clear -RM. Z.div_mod_to_equations. lia. }
  assert (ND : Z.of_nat (Z.to_nat (ndist st c)) = ndist st c /\ ndist st c * S = c_allocated_user r).
  { unfold ndist. fold r S. split; [| clear -A1 A3 QS; Z.div_mod_to_equations; nia]. apply Z2Nat.id. apply Z.div_pos; clear -A1 QS; lia. }
  destruct ND as [ND1 ND2].
  pose proof (SL (Z.to_nat (ndist st c)) ltac:(rewrite ND1; lia)) as W1. rewrite ND1, ND2 in W1. clear SL.
  (* [comment removed for export] *)
  pose proof SFILL as W2. apply wr_of_fill in W2; [| apply shlen_nonneg; clear -A1; lia].
  pose proof (wr_of_azero _ _ _ AZ1) as W3. pose proof FAS as W4. apply wr_of_junk in W4; [| apply shlen_nonneg; clear -A5 A6; lia]. pose proof (wr_of_azero _ _ _ AZ2) as W5.
  fold r in W2, W3, W4, W5.
  assert (E2 : shad (aregion L c + c_allocated_user r) = shad (aregion L c) + shlen (c_allocated_user r)) by (apply shad_add_shlen; clear -RM; Z.div_mod_to_equations; lia).
  assert (E3 : shad (aregion L c + c_mapped_user r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r))).
  { rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. clear -AL8 A4. unfold K_USER_MAP in A4. Z.div_mod_to_equations. lia. }
  assert (E4 : shad (afreearr L c) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r))).
  { unfold afreearr. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP in *. clear -AL8 A4. Z.div_mod_to_equations. lia. }
  assert (E5 : shad (afreearr L c + c_mapped_free_array r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r))).
  { unfold afreearr. rewrite <- Z.add_assoc. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAP in *. clear -AL8 A4 A7. Z.div_mod_to_equations. lia. }
  replace (shlen K_REGION) with (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r) + shlen (K_FREEARR_MAX - c_mapped_free_array r))
    by (rewrite !shlen_div; unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP in *; clear -AL8 A4 A7; Z.div_mod_to_equations; lia).
  apply wr_at_join; [| rewrite <- E5; exact W5| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2 A5 A6; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A6; unfold K_FREEARR_MAX in *; lia].
  apply wr_at_join; [| rewrite <- E4; exact W4| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A5 A6; lia].
  apply wr_at_join; [| rewrite <- E3; exact W3| rewrite !shlen_div; clear -A1; Z.div_mod_to_equations; lia| apply shlen_nonneg; unfold K_FREEARR_OFF in *; clear -A2; lia].
  apply wr_at_join; [exact W1| rewrite <- E2; exact W2| apply shlen_nonneg; clear -A1; lia| apply shlen_nonneg; clear -A1; lia].
Qed.
End Zd1.
#[using="Type"] Lemma region_shadow_wr : ltac:(let t := eval cbv delta [region_shadow_wr__stmt] in region_shadow_wr__stmt in exact t).
Proof. exact region_shadow_wr__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma busy_of_of_In : forall L st X b, awf L st X -> In b (x_busy X) -> busy_of X (xb_class b) (xb_slot b) = Some b.
Proof.
  intros L st X b WF Hb. (pose proof WF as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ PERC _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [CLB _]. (nd_pre (PERC (xb_class b) CLB) 12%nat; intros _ _ _ _ _ _ _ _ _ _ ND _; nd_post).
  apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. unfold busy_slots in ND.
  unfold busy_of. destruct (List.find (fun b0 => (xb_class b0 =? xb_class b) && (xb_slot b0 =? xb_slot b)) (x_busy X)) as [b'|] eqn:E.
  - apply find_some in E. destruct E as [HIn HP]. apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
    f_equal. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X)) b' b ND).
    + apply List.filter_In. split; [exact HIn| rewrite HP1; apply Z.eqb_refl].
    + apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
    + exact HP2.
  - exfalso. pose proof (find_none _ _ E b Hb) as F. cbn beta in F. rewrite !Z.eqb_refl in F. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  assert (S0 : 0x603000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  (nd_pre DB 4%nat; intros D1 D2 D3 D6; nd_post). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  - (* [comment removed for export] *)
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read asegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    (* [comment removed for export] *)
    rewrite ov_rdn in R. cbn [Lib.PropExec.rdn] in R. unfold mrd.
    destruct (match m (wa (shad A + n / 8)) with Some b => Some b | None => seg_rom asegs (wa (shad A + n / 8)) end) as [b|] eqn:E; [| discriminate R].
    injection R as ->. rewrite <- D6. reflexivity.
Qed.

#[using="Type"] Lemma block_shadow_of_cb : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH H.
  assert (LB : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
  assert (GE : granules n = n / 8 + (if n mod 8 =? 0 then 0 else 1)).
  { rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.granules_eq n) by lia. rewrite shlen_div. reflexivity. }
  unfold block_shadow_bytes in H. rewrite shlen_div in H.
  destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
  - rewrite app_nil_r in H. rewrite GE, Z.add_0_r in H. eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H|].
    intros NE. exfalso. exact (NE M0).
  - rewrite GE in H. replace (Z.to_nat (n / 8 + 1)) with (Z.to_nat (n / 8) + 1)%nat in H by (Z.div_mod_to_equations; lia).
    destruct (cb_take m (shad A) (n / 8 + 1) (n / 8) _ ltac:(rewrite Z2Nat.inj_add by (Z.div_mod_to_equations; lia); cbn [Z.to_nat Pos.to_nat]; exact H) ltac:(Z.div_mod_to_equations; lia)) as [H1 H2].
    rewrite firstn_app, repeat_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H1 by (rewrite repeat_length; lia).
    rewrite skipn_app, repeat_length, Nat.sub_diag, skipn_O, skipn_all2 in H2 by (rewrite repeat_length; lia). cbn [app] in H2.
    replace (n / 8 + 1 - n / 8) with 1 in H2 by lia.
    eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H1|].
    intros _. eapply rw_cells_recast; [exact H2| cbn; tauto| reflexivity| reflexivity].
Qed.

Definition AHI_block__stmt : Prop := forall L RNG st LB m p A n,
  AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
  /\ wr_at asegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 4).
Variable p : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 5).
Variable A : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 6).
Variable n : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 7).
#[using="Type"] Lemma AHI_block__body : ltac:(let T := type of (fun (h : AHI_block__stmt) => h L RNG st LB m p A n) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (p, (A, n)))))))) as _.
  intros AH Hin.
  pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as BR.
  (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof AR as ndP__; nd_pre ndP__ 8%nat; intros WF _ _ _ CLS _ HS _; nd_post). (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros SBE PAE SAL SLO SHI PERC _; nd_post).
  cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. (pose proof HS as ndP__; nd_pre ndP__ 5%nat; intros (_ & _ & _ & _ & _ & WF1 & _) (order & PO & _ & _ & PER) _ PZ _; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (* [comment removed for export] *)
    set (c := xb_class b) in *. set (k := xb_slot b) in *. set (S := size_of_class c) in *.
    pose proof (size_of_class_facts c CLB) as [QS QS16].
    (nd_pre (PERC c CLB) 5%nat; intros A1 A2 A3 A4 _; nd_post). (nd_pre (RCLS c CLB) 3%nat; intros RREG RSREG _; nd_post). cbv zeta in RREG, RSREG.
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ16. pose proof (rz_size_facts n ltac:(clear -NB; lia)) as [_ RZM].
    pose proof (aregion_mod L c SAL) as RM. pose proof (slot_aligned L c k SAL ltac:(exact CLB)) as AL16.
    assert (EAB : xb_alloc L b = aslot_addr L c k) by reflexivity.
    subst A. unfold xb_user in *. rewrite EAB in *. rewrite Nb in *.
    assert (A8 : (aslot_addr L c k + rz_size n) mod 8 = 0) by (clear -AL16 RZM; Z.div_mod_to_equations; lia).
    unfold K_FREEARR_OFF, K_NUM_CLASSES in *.
    split; [exact NB|]. split; [exact BR|].
    split. { eapply rng_sub'; [exact RREG|]. clear -P5 P4 A1 FIT RG RZ16. lia. }
    split. { eapply rng_sub'; [exact RSREG|]. rewrite !shad_div, !shlen_div. unfold K_USER_MAP in A4. clear -P5 P4 A1 FIT RG RZ16 RM A4 A8. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    (nd_pre (CLS c CLB) 4%nat; intros _ _ [SL _] [SSH _]; nd_post).
    assert (EBK : busy_of X c k = Some b) by (exact (busy_of_of_In L st X b WF Hb)).
    pose proof (SSH k KB) as SH. rewrite EBK in SH. cbn [slot_shadow_bytes] in SH. rewrite Sb, Nb in SH. fold S in SH.
    (pose proof (chunk_shadow_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GEq G0 GF _; nd_post).
    pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
    assert (LBS : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
    replace (Z.to_nat (shlen S)) with (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen (rz_size n) - granules n))%nat in SH
      by (generalize SRZ SG7 GF; subst S; clear; unfold granules; intros; lia).
    (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LBS ltac:(apply repeat_length) SH) 3%nat; intros _ SHU _; nd_post).
    rewrite Z2Nat.id in SHU by lia. rewrite <- SE in SHU.
    split. { eapply block_shadow_of_cb; [clear -NB; lia| exact A8| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| (nd_pre BR 4%nat; intros _ _ B3 _; nd_post); clear -B3; lia| exact SHU]. }
    (* [comment removed for export] *)
    pose proof (SL k KB) as SLK. rewrite EBK in SLK. unfold aslot_busy in SLK. cbv zeta in SLK. rewrite Sb in SLK.
    (nd_pre SLK 3%nat; intros _ _ UJ; nd_post). rewrite EAB, Nb in UJ. fold S in UJ.
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (S - rz_size n)); [clear -FIT RG NB; lia| exact UJ]| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| clear; lia| clear -FIT RG NB; lia]. }
    split. { exists (CPrim c n). split; [exact LV|]. split; [reflexivity|]. intros P. rewrite PRIM in P. discriminate. }
    (* [comment removed for export] *)
    exists (aregion L (c - 1)), (aregion L (c + 1)).
    assert (GEO : aregion L (c - 1) + K_REGION = aregion L c /\ aregion L c + K_REGION = aregion L (c + 1) /\ aregion L 0 = al_space_beg L
                  /\ aregion L (c - 1) mod 4096 = 0 /\ 0 <= aregion L (c - 1)).
    { unfold aregion, K_REGION. unfold K_ALIGN in SAL. clear -SAL SP1 CLB. repeat split; first [nia | Z.div_mod_to_equations; nia]. }
    (nd_pre GEO 5%nat; intros GE1 GE2 GE0 GAL GNN; nd_post). unfold K_REGION in GE1, GE2. change (2 ^ 32) with 4294967296 in GE1, GE2.
    split; [exact GAL|]. split; [rewrite <- GE2, <- GE1; clear -GAL; Z.div_mod_to_equations; lia|].
    split; [clear -GE1 P5 RZ16; lia|]. split; [clear -GE2 P4 A1 A2 FIT RG; lia|].
    rewrite <- GE2, <- GE1. replace (aregion L (c - 1) + 4294967296 + 4294967296 - aregion L (c - 1)) with (4294967296 + 4294967296) by (clear; lia).
    split.
    + eapply rng_sub'; [exact RPSH|]. rewrite !shad_div, !shlen_div. unfold K_SPACE_SIZE. unfold aregion, K_REGION in *.
      clear -CLB SP3. unfold K_ALIGN in SP3. Z.div_mod_to_equations. nia.
    + replace (shlen (4294967296 + 4294967296)) with (shlen K_REGION + shlen K_REGION) by reflexivity.
      apply wr_at_join; [| | apply shlen_nonneg; unfold K_REGION; clear; lia| apply shlen_nonneg; unfold K_REGION; clear; lia].
      * destruct (Z.eq_dec c 1) as [C1|C1].
        { rewrite C1. change (1 - 1) with 0. rewrite GE0. exact (wr_of_azero _ _ _ PZ). }
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; clear -CLB C1; lia].
      * rewrite <- shad_add_shlen by (rewrite <- GAL; clear -GAL; Z.div_mod_to_equations; lia). unfold K_REGION. change (2 ^ 32) with 4294967296. rewrite GE1.
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; exact CLB].
  - (* [comment removed for export] *)
    pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
    apply ablk_lin in G2.   (* [comment removed for export] *)
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros NBg RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- G4 in MSE, MSR, MSM, MSB.
    pose proof (proj1 (Forall_forall _ _) RSECS _ INC) as [RC RSC]. cbn [sec_mb sec_ms] in RC, RSC.
    (* [comment removed for export] *)
    pose proof (Permutation_in _ (Permutation_sym PO) INC) as INO. apply In_nth_error in INO. destruct INO as [i Hi].
    (nd_pre (PER i _ Hi) 3%nat; intros lv LVE CH; nd_post).
    assert (LVT : lv = true) by (apply (proj2 LVE); exists p; exact Lp). subst lv.
    cbn [asec_chunk] in CH. (nd_pre CH 9%nat; intros _ _ _ _ _ UJ SF1 SU SF2; nd_post). unfold SEC_UOFF, K_HIGH_MEM in *. subst A.
    assert (SG : shad (mb + 6144) = shad mb + 768 /\ shad mb + ms / 8 = shad (mb + ms) /\ 768 + granules n <= ms / 8 /\ 0 <= granules n /\ shlen ms = ms / 8
                 /\ (mb + 6144) mod 8 = 0 /\ 0 <= shad mb).
    { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -G1 G2 NBg RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
    (nd_pre SG 7%nat; intros SG1 SG2 SG3 SG4 SG5 SG6 SG7; nd_post).
    split; [clear -G5; lia|]. split; [exact BR|].
    split; [eapply rng_sub'; [exact RC|]; clear -NSE RSR MSR NBg; lia|].
    split; [eapply rng_sub'; [exact RSC|]; rewrite !shad_div, !shlen_div; rewrite shad_div in SG2; unfold ASHOFF in *; clear -G1 NSE RSR MSR NBg; Z.div_mod_to_equations; lia|].
    split. { eapply block_shadow_of_cb; [clear -NBg; lia| exact SG6| clear -G2; lia| clear -G3 NSE RSR MSR NBg; lia| unfold sec_user_shadow in SU; exact SU]. }
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (ms - 6144)); [clear -MSR NSE RSR NBg; lia| exact UJ]| clear -G2; lia| clear; lia| clear -MSR NSE RSR NBg; lia]. }
    split. { exists (CSec mb ms n). split; [exact Lp|]. split; [reflexivity|]. intros _. cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
    exists mb, (mb + ms). split; [exact G1|]. split; [clear -G1 MSM; Z.div_mod_to_equations; lia|]. split; [clear; lia|]. split; [clear -MSR NSE RSR NBg; lia|].
    replace (mb + ms - mb) with ms by (clear; lia). rewrite SG5.
    split; [exact RSC|].
    pose proof SF1 as W1. apply wr_of_fill in W1; [| clear; lia].
    pose proof SF2 as W3. apply wr_of_fill in W3; [| clear -SG3 SG4; lia].
    pose proof (wr_of_cells _ _ _ SU) as W2. cbn [cells_size csize] in W2. rewrite Nat.add_0_r, Z2Nat.id in W2 by exact SG4.
    replace (ms / 8) with (768 + (granules n + (ms / 8 - 768 - granules n))) by (clear -SG3; lia).
    apply wr_at_join; [exact W1| | clear; lia| clear -SG3 SG4; lia].
    rewrite <- SG1. apply wr_at_join; [exact W2| exact W3| exact SG4| clear -SG3 SG4; lia].
Qed.
End Zd2.
#[using="Type"] Theorem AHI_block : ltac:(let t := eval cbv delta [AHI_block__stmt] in AHI_block__stmt in exact t).
Proof. exact AHI_block__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_block_tls : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= ATPv + -200 \/ ATPv + 312 <= ab_addr b.
Proof.
  intros L RNG st LB m b AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ad_tls_res L ALO) as TR. pose proof (ad_tls_fake L ALO) as TF. unfold adisj in TR, TF.
  destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(xb & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
    + pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. unfold xb_user in Ub. subst A. rewrite Nb in *.
      clear -TR R1 R2 FIT RG RZ NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & _ & _ & _ & _ & _ & _ & Ctls); nd_post).
      (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR. subst A. unfold SEC_UOFF.
      clear -Ctls RSR NSE MSR G5. lia.
  - (nd_pre (afake_lb L LB m cls A n HFK Hin) 7%nat; intros _ _ NP _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -TF K5 K6 NP. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_block_ahm : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= AAHMv \/ AAHMv + AAHM_SZ <= ab_addr b.
Proof.
  intros L RNG st LB m b AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ad_ahm_res L ALO) as TR. pose proof (ad_ahm_fake L ALO) as TF. unfold adisj in TR, TF. rewrite <- (ao_ahm_eq L ALO). unfold AAHM_SZ.
  destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(xb & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
    + pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. unfold xb_user in Ub. subst A. rewrite Nb in *.
      clear -TR R1 R2 FIT RG RZ NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cahm); nd_post).
      (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR. subst A. unfold SEC_UOFF.
      clear -Cahm RSR NSE MSR G5. lia.
  - (nd_pre (afake_lb L LB m cls A n HFK Hin) 7%nat; intros _ _ NP _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -TF K5 K6 NP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma AHI_premap : forall L RNG st LB m, AHEAP_I L RNG st LB m -> premap_cells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). (nd_pre AR 12%nat; intros _ RT _ _ _ _ _ _ _ RT2 _ RT3; nd_post).
  eapply premap_of_rt'; [exact RT| exact RT2| exact RT3].
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation AHEAP_I := (AHEAP_P AHI).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma AHI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG' st LB m.
Proof.
  intros L RNG RNG' st LB m LE (ALO & ARNG & XB & HFK). split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.

#[using="Type"] Lemma hb_ids_perm : forall LB LB', Permutation LB LB' -> Permutation (hb_ids LB) (hb_ids LB').
Proof.
  intros LB LB' P. unfold hb_ids. induction P; cbn.
  - constructor.
  - apply Permutation_app_head. exact IHP.
  - rewrite !app_assoc. apply Permutation_app_tail. destruct (ab_kind y), (ab_kind x); cbn; try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

#[using="Type"] Lemma AHI_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHI ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

#[using="Type"] Lemma AHI_blocks_nodup : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup LB.
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & _ & B4)]] & _). exact B4. Qed.
#[using="Type"] Lemma AHI_hb_ids : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup (hb_ids LB).
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & B3 & _)]] & _). exact B3. Qed.

#[using="Type"] Lemma AHI_layout : forall L RNG st LB m, AHEAP_I L RNG st LB m ->
  al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096)
  /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
  /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP.
Proof.
  intros L RNG st LB m (ALO & _ & [X [AR _]] & _).
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof (ao_U L ALO) as U. pose proof (ao_fake L ALO) as FK.
  pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
  unfold aobj, AIMG_HI in *.
  destruct AR as ((SBE & _) & _).
  repeat lazymatch goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

#[using="Type"] Lemma AHI_relro : forall L RNG st LB m, AHEAP_I L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros L RNG st LB m H. eapply AHEAP_P_relro. exact H. Qed.

#[using="Type"] Lemma AHI_rtcells : forall L RNG st LB m, AHEAP_I L RNG st LB m -> artcells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _).
  (nd_pre AR 12%nat; intros _ RT _ _ _ _ _ _ _ RT2 _ RT3; nd_post).
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  (nd_pre RT2 3%nat; intros Q1 Q2 Q3; nd_post).
  (nd_pre RT3 17%nat; intros S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17; nd_post).
  unfold artcells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma hb_cases : forall L st X LB m p A n,
  alayout_ok L -> AREP AHI L st X m -> ablocks L st X LB -> In (HB p A n) LB ->
  (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_user L b = A /\ xb_n b = n
      /\ 1 <= xb_class b < K_NUM_CLASSES /\ 1 <= n <= AREQMAX /\ rounded_size n + rz_size n <= size_of_class (xb_class b)
      /\ (a_live st) !! p = Some (CPrim (xb_class b) n) /\ is_primary n = true
      /\ 0 <= xb_slot b < ndist st (xb_class b)
      /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
      /\ al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104)
  \/ (exists mb ms, (a_live st) !! p = Some (CSec mb ms n) /\ A = mb + SEC_UOFF /\ sec_wf1 L (CSec mb ms n) /\ is_primary n = false
      /\ In (CSec mb ms n) (sec_chunks_of st)).
Proof.
  intros L st X LB m p A n ALO AR BL Hin.
  pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  - left. exists b. destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 6%nat; intros N0 FIT _ _ _ LV; nd_post).
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    pose proof (ao_space L ALO) as RSP. subst n.
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear -CLB N0 KB; lia).
    all: try (unfold is_primary, needed0, K_MAX_SIZE; apply Z.leb_le; clear -FIT QS; lia).
    all: unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *; clear -P5 P4 Q1 Q2 CLB RSP; lia.
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros _ _ _ _ _ G6 _; nd_post).
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
    apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
Qed.

#[using="Type"] Lemma AHI_block_bounds : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros L RNG st LB m b AH Hin. destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - (pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 R4; nd_post). apply ablk_lin in R1. unfold AIMG_HI in *. clear -R1 R2 R3. lia.   (* [comment removed for export] *)
  - (nd_pre AH 4%nat; intros ALO _ [X [_ (_ & BF & _)]] _; nd_post). (nd_pre (BF cls A n Hin) 3%nat; intros K1 K2 K3; nd_post).
    pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
    unfold aobj, AIMG_HI in *. clear -K1 K2 K3 FK FKI. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nodup_map_inj : forall {A B} (f : A -> B) (l : list A) x y,
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | |].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma nodup_filter_map_inj : forall {A B} (g : B -> bool) (f : A -> B) (l : list A) x y,
  List.NoDup (List.filter g (map f l)) -> In x l -> In y l -> f x = f y -> g (f x) = true -> x = y.
Proof.
  intros A B g f l. induction l as [|a l IH]; intros x y ND Hx Hy E G; [destruct Hx|].
  cbn in ND.
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
  - subst. reflexivity.
  - subst a. exfalso. rewrite G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [rewrite E; apply in_map; exact Hy| exact G].
  - subst a. exfalso. rewrite <- E, G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [apply in_map; exact Hx| exact G].
  - apply IH; try assumption. destruct (g (f a)); [inversion ND; assumption| exact ND].
Qed.

#[using="Type"] Lemma AHI_blocks_disjoint : forall L RNG st LB m b1 b2,
  AHEAP_I L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
Proof.
  intros L RNG st LB m b1 b2 AH H1 H2 NE.
  (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D_f_res. unfold aobj, adisj in ORS, OFK, D_f_res.
  destruct b1 as [[p1|c1] A1 n1]; destruct b2 as [[p2|c2] A2 n2]; cbn [ab_addr ab_size].
  - (* [comment removed for export] *)
    assert (NEP : p1 <> p2).
    { intros <-. (pose proof BL as ndP__; nd_pre ndP__ 4%nat; intros _ _ NDI _; nd_post).
      assert (E : HB p1 A1 n1 = HB p1 A2 n2).
      { apply (nodup_filter_map_inj (fun k => match k with ABHeap _ => true | _ => false end) ab_kind LB); try assumption; try reflexivity.
        unfold hb_ids in NDI. clear -NDI. induction LB as [|b LB IH]; cbn; [constructor|]. cbn in NDI.
        destruct b as [[q|c] B k]; cbn in NDI |- *; [| apply IH; exact NDI]. inversion NDI as [|q' l' NI ND']; subst. constructor; [| apply IH; exact ND'].
        intros Hin. apply NI. apply List.filter_In in Hin. destruct Hin as [Hin _]. apply in_map_iff in Hin. (nd_pre Hin 3%nat; intros b' Eb Hb'; nd_post).
        apply in_flat_map. exists b'. split; [exact Hb'|]. destruct b' as [[q''|c''] B' k']; cbn in Eb |- *; [| discriminate]. injection Eb as ->. left; reflexivity. }
      exact (NE E). }
    destruct (hb_cases L st X LB m p1 A1 n1 ALO AR BL H1) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & _ & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & _ & INC)];
    destruct (hb_cases L st X LB m p2 A2 n2 ALO AR BL H2) as [(b' & Hb' & Sb' & Ub' & Nb' & CLB' & NB' & FIT' & LV' & _ & KB' & P5' & P4' & R1' & R2')|(mb' & ms' & Lp' & EA' & G' & _ & INC')].
    + (* [comment removed for export] *)
      destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
      assert (NEB : b <> b') by (intros <-; apply NEP; rewrite Sb in Sb'; injection Sb' as E; exact E).
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      pose proof (rounded_size_ge (xb_n b')) as RG'. pose proof (rz_size_ge16 (xb_n b')) as RZ'.
      pose proof (size_of_class_facts (xb_class b) CLB) as [QS _]. pose proof (size_of_class_facts (xb_class b') CLB') as [QS' _].
      assert (SL : xb_alloc L b + size_of_class (xb_class b) <= xb_alloc L b' \/ xb_alloc L b' + size_of_class (xb_class b') <= xb_alloc L b).
      { destruct (Z.eq_dec (xb_class b) (xb_class b')) as [EC|NC].
        - (* [comment removed for export] *)
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 _ _ _ _ _ _ _ _ _ ND _; nd_post).
          assert (NK : xb_slot b <> xb_slot b').
          { intros EK. apply NEB. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X))).
            - apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. exact ND.
            - apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
            - apply List.filter_In. split; [exact Hb'| rewrite EC; apply Z.eqb_refl].
            - exact EK. }
          unfold xb_alloc. rewrite <- EC. apply slots_disjoint; [clear -KB; lia| clear -KB'; lia| exact NK| clear -QS; lia].
        - (* [comment removed for export] *)
          (nd_pre (PERC (xb_class b) CLB) 3%nat; intros Q1 Q2 _; nd_post). (nd_pre (PERC (xb_class b') CLB') 3%nat; intros Q1' Q2' _; nd_post).
          unfold K_FREEARR_OFF in Q2, Q2'.
          destruct (Z.lt_ge_cases (xb_class b) (xb_class b')) as [LT|GE].
          + left. pose proof (regions_sep L (xb_class b) (xb_class b') LT) as RS. unfold K_REGION in RS. clear -RS P4 P5' Q1 Q2. lia.
          + right. pose proof (regions_sep L (xb_class b') (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS P4' P5 Q1' Q2'. lia. }
      subst A1 n1 A2 n2. unfold xb_user. clear -SL FIT FIT' RG RZ RG' RZ' NB NB'. lia.
    + cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros G1 G2 G3 G4 G5 G6 (_ & _ & Cr & _); nd_post).
      pose proof (sec_facts n2 ltac:(clear -G5; lia) G6) as SF. subst A2. unfold SEC_UOFF, xb_user in *. subst A1 n1.
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      clear -R1 R2 FIT RG RZ Cr G3 G4 G5 SF NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 (_ & _ & Cr & _); nd_post).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. subst A1. unfold SEC_UOFF, xb_user in *. subst A2 n2.
      pose proof (rounded_size_ge (xb_n b')) as RG. pose proof (rz_size_ge16 (xb_n b')) as RZ.
      clear -R1' R2' FIT' RG RZ Cr G3 G4 G5 SF NB'. lia.
    + (* [comment removed for export] *)
      (nd_pre AR 8%nat; intros WF _ _ _ _ _ HS _; nd_post). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS.
      destruct HS as ((_ & _ & _ & _ & _ & _ & [ND PW]) & _).
      cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post). cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros G1' G2' G3' G4' G5' G6' _; nd_post).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. pose proof (sec_facts n2 ltac:(clear -G5'; lia) G6') as SF'.
      assert (NEC : CSec mb ms n1 <> CSec mb' ms' n2).
      { intros EC. apply NEP.
        assert (E : (p1, CSec mb ms n1) = (p2, CSec mb' ms' n2)); [| injection E as E1 _ _ _; exact E1].
        apply (nodup_filter_map_inj is_sec snd (map_to_list (a_live st))).
        - unfold sec_chunks_of, achunks in ND. rewrite filter_is_sec_app in ND. apply List.NoDup_app_remove_r in ND. exact ND.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp'.
        - cbn. exact EC.
        - reflexivity. }
      pose proof (PW _ _ INC INC' NEC) as D. cbn [sec_mb sec_ms] in D. subst A1 A2. unfold SEC_UOFF. clear -D G4 G4' G5 G5' SF SF'. lia.
  - (* [comment removed for export] *)
    pose proof (AHEAP_P_hb_fake _ L RNG st LB m p1 A1 n1 AH H1) as D1.
    (nd_pre (afake_lb L LB m c2 A2 n2 HFK H2) 7%nat; intros _ _ K3 _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -D1 K3 K5 K6. lia.
  - pose proof (AHEAP_P_hb_fake _ L RNG st LB m p2 A2 n2 AH H2) as D2.
    (nd_pre (afake_lb L LB m c1 A1 n1 HFK H1) 7%nat; intros _ _ K3 _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -D2 K3 K5 K6. lia.
  - (* [comment removed for export] *) eapply afake_lb_disjoint; [exact HFK| exact H1| exact H2| exact NE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_join : forall m A a b, wr_at asegs m A a -> wr_at asegs m (A + a) b -> 0 <= a -> 0 <= b -> wr_at asegs m A (a + b).
Proof.
  intros m A a b (W0 & W1 & W) (V0 & V1 & V) Ha Hb. split; [exact W0|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i a) as [L|G]; [apply W; lia|]. replace (A + i) with (A + a + (i - a)) by lia. apply V. lia.
Qed.
#[using="Type"] Lemma wr_at_nil : forall m A, 0 <= A <= 2^64 -> wr_at asegs m A 0.
Proof. intros m A H. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.
#[using="Type"] Lemma wr_of_cells : forall m A cs, rw_cells asegs m A cs -> wr_at asegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ W]. exact W. Qed.
#[using="Type"] Lemma wr_of_junk : forall m A n, 0 <= n -> junk_at m A n -> wr_at asegs m A n.
Proof. intros m A n Hn [bs H]. pose proof (wr_of_cells _ _ _ H) as W. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by exact Hn. exact W. Qed.
#[using="Type"] Lemma wr_of_fill : forall m A n v, 0 <= n -> fill_at m A n v -> wr_at asegs m A n.
Proof. intros m A n v Hn H. apply (wr_of_junk m A n Hn). eapply fill_is_junk. exact H. Qed.
#[using="Type"] Lemma wr_of_azero : forall m A n, azero m A n -> wr_at asegs m A n.
Proof. intros m A n [_ W]. exact W. Qed.

Definition region_shadow_wr__stmt : Prop := forall L st X m c,
  AREP AHI L st X m -> 1 <= c < K_NUM_CLASSES -> wr_at asegs m (shad (aregion L c)) (shlen K_REGION).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 2).
Variable m : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 3).
Variable c : ltac2:(SecDietF.SzSecF.ty 'region_shadow_wr__stmt 4).
Let r := get_cls st c.
Let S := size_of_class c.
#[using="r S"] Lemma region_shadow_wr__body : ltac:(let T := type of (fun (h : region_shadow_wr__stmt) => h L st X m c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (m, c))))) as _.
  intros AR Hc.
  (pose proof AR as ndP__; nd_pre ndP__ 12%nat; intros (SBE & PAE & SAL & SLO & SHI & PERC & _) _ _ _ CLS _ _ _ _ _ AVL _; nd_post).
  (nd_pre (CLS c Hc) 4%nat; intros _ (_ & _ & FAS) _ [SSH SFILL]; nd_post). destruct (AVL c Hc) as [AZ1 AZ2].
  (nd_pre (PERC c Hc) 8%nat; intros A1 A2 A3 A4 A5 A6 A7 _; nd_post).
  pose proof (size_of_class_facts c Hc) as [QS QS16].
  chg (get_cls st c) r. chg (size_of_class c) S.
  pose proof (aregion_mod L c SAL) as RM.
  assert (AL8 : c_allocated_user r mod 8 = 0) by (apply (mod16_of_class _ S); [exact A3| exact QS16| clear -QS; lia]).
  (* [comment removed for export] *)
  assert (SL : forall k : nat, Z.of_nat k <= ndist st c -> wr_at asegs m (shad (aregion L c)) (shlen (Z.of_nat k * S))).
  { induction k as [|k IH]; intros Hk.
    - cbn [Z.of_nat]. rewrite Z.mul_0_l. unfold shlen; cbn. apply wr_at_nil. rewrite shad_div. unfold ASHOFF. pose proof (alayout_space L) as _.
      unfold aregion, K_REGION. unfold K_NUM_CLASSES in Hc. clear -SLO SHI Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. Z.div_mod_to_equations. nia.
    - replace (shlen (Z.of_nat (Datatypes.S k) * S)) with (shlen (Z.of_nat k * S) + shlen S)
        by (rewrite !shlen_div; clear -QS16 QS; Z.div_mod_to_equations; nia).
      apply wr_at_join; [apply IH; lia| | rewrite shlen_div; clear -QS; Z.div_mod_to_equations; nia| rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia].
      pose proof (SSH (Z.of_nat k) ltac:(lia)) as CK. apply wr_of_cells in CK. cbn [cells_size csize] in CK. rewrite Nat.add_0_r, Z2Nat.id in CK by (rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia).
      replace (shad (aregion L c) + shlen (Z.of_nat k * S)) with (shad (aslot_addr L c (Z.of_nat k))); [exact CK|].
      unfold aslot_addr. fold S. rewrite shad_add_shlen; [reflexivity|]. clear -RM. Z.div_mod_to_equations. lia. }
  assert (ND : Z.of_nat (Z.to_nat (ndist st c)) = ndist st c /\ ndist st c * S = c_allocated_user r).
  { unfold ndist. fold r S. split; [| clear -A1 A3 QS; Z.div_mod_to_equations; nia]. apply Z2Nat.id. apply Z.div_pos; clear -A1 QS; lia. }
  destruct ND as [ND1 ND2].
  pose proof (SL (Z.to_nat (ndist st c)) ltac:(rewrite ND1; lia)) as W1. rewrite ND1, ND2 in W1. clear SL.
  (* [comment removed for export] *)
  pose proof SFILL as W2. apply wr_of_fill in W2; [| apply shlen_nonneg; clear -A1; lia].
  pose proof (wr_of_azero _ _ _ AZ1) as W3. pose proof FAS as W4. apply wr_of_junk in W4; [| apply shlen_nonneg; clear -A5 A6; lia]. pose proof (wr_of_azero _ _ _ AZ2) as W5.
  fold r in W2, W3, W4, W5.
  assert (E2 : shad (aregion L c + c_allocated_user r) = shad (aregion L c) + shlen (c_allocated_user r)) by (apply shad_add_shlen; clear -RM; Z.div_mod_to_equations; lia).
  assert (E3 : shad (aregion L c + c_mapped_user r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r))).
  { rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. clear -AL8 A4. unfold K_USER_MAP in A4. Z.div_mod_to_equations. lia. }
  assert (E4 : shad (afreearr L c) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r))).
  { unfold afreearr. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP in *. clear -AL8 A4. Z.div_mod_to_equations. lia. }
  assert (E5 : shad (afreearr L c + c_mapped_free_array r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r))).
  { unfold afreearr. rewrite <- Z.add_assoc. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAP in *. clear -AL8 A4 A7. Z.div_mod_to_equations. lia. }
  replace (shlen K_REGION) with (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r) + shlen (K_FREEARR_MAX - c_mapped_free_array r))
    by (rewrite !shlen_div; unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP in *; clear -AL8 A4 A7; Z.div_mod_to_equations; lia).
  apply wr_at_join; [| rewrite <- E5; exact W5| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2 A5 A6; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A6; unfold K_FREEARR_MAX in *; lia].
  apply wr_at_join; [| rewrite <- E4; exact W4| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A5 A6; lia].
  apply wr_at_join; [| rewrite <- E3; exact W3| rewrite !shlen_div; clear -A1; Z.div_mod_to_equations; lia| apply shlen_nonneg; unfold K_FREEARR_OFF in *; clear -A2; lia].
  apply wr_at_join; [exact W1| rewrite <- E2; exact W2| apply shlen_nonneg; clear -A1; lia| apply shlen_nonneg; clear -A1; lia].
Qed.
End Zd1.
#[using="Type"] Lemma region_shadow_wr : ltac:(let t := eval cbv delta [region_shadow_wr__stmt] in region_shadow_wr__stmt in exact t).
Proof. exact region_shadow_wr__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma busy_of_of_In : forall L st X b, awf L st X -> In b (x_busy X) -> busy_of X (xb_class b) (xb_slot b) = Some b.
Proof.
  intros L st X b WF Hb. (pose proof WF as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ PERC _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [CLB _]. (nd_pre (PERC (xb_class b) CLB) 12%nat; intros _ _ _ _ _ _ _ _ _ _ ND _; nd_post).
  apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. unfold busy_slots in ND.
  unfold busy_of. destruct (List.find (fun b0 => (xb_class b0 =? xb_class b) && (xb_slot b0 =? xb_slot b)) (x_busy X)) as [b'|] eqn:E.
  - apply find_some in E. destruct E as [HIn HP]. apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
    f_equal. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X)) b' b ND).
    + apply List.filter_In. split; [exact HIn| rewrite HP1; apply Z.eqb_refl].
    + apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
    + exact HP2.
  - exfalso. pose proof (find_none _ _ E b Hb) as F. cbn beta in F. rewrite !Z.eqb_refl in F. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  assert (S0 : 0x604000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  (nd_pre DB 4%nat; intros D1 D2 D3 D6; nd_post). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  - (* [comment removed for export] *)
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read asegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    (* [comment removed for export] *)
    rewrite ov_rdn in R. cbn [Lib.PropExec.rdn] in R. unfold mrd.
    destruct (match m (wa (shad A + n / 8)) with Some b => Some b | None => seg_rom asegs (wa (shad A + n / 8)) end) as [b|] eqn:E; [| discriminate R].
    injection R as ->. rewrite <- D6. reflexivity.
Qed.

#[using="Type"] Lemma block_shadow_of_cb : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH H.
  assert (LB : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
  assert (GE : granules n = n / 8 + (if n mod 8 =? 0 then 0 else 1)).
  { rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB.granules_eq n) by lia. rewrite shlen_div. reflexivity. }
  unfold block_shadow_bytes in H. rewrite shlen_div in H.
  destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
  - rewrite app_nil_r in H. rewrite GE, Z.add_0_r in H. eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H|].
    intros NE. exfalso. exact (NE M0).
  - rewrite GE in H. replace (Z.to_nat (n / 8 + 1)) with (Z.to_nat (n / 8) + 1)%nat in H by (Z.div_mod_to_equations; lia).
    destruct (cb_take m (shad A) (n / 8 + 1) (n / 8) _ ltac:(rewrite Z2Nat.inj_add by (Z.div_mod_to_equations; lia); cbn [Z.to_nat Pos.to_nat]; exact H) ltac:(Z.div_mod_to_equations; lia)) as [H1 H2].
    rewrite firstn_app, repeat_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H1 by (rewrite repeat_length; lia).
    rewrite skipn_app, repeat_length, Nat.sub_diag, skipn_O, skipn_all2 in H2 by (rewrite repeat_length; lia). cbn [app] in H2.
    replace (n / 8 + 1 - n / 8) with 1 in H2 by lia.
    eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H1|].
    intros _. eapply rw_cells_recast; [exact H2| cbn; tauto| reflexivity| reflexivity].
Qed.

Definition AHI_block__stmt : Prop := forall L RNG st LB m p A n,
  AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
  /\ wr_at asegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 4).
Variable p : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 5).
Variable A : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 6).
Variable n : ltac2:(SecDietF.SzSecF.ty 'AHI_block__stmt 7).
#[using="Type"] Lemma AHI_block__body : ltac:(let T := type of (fun (h : AHI_block__stmt) => h L RNG st LB m p A n) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (p, (A, n)))))))) as _.
  intros AH Hin.
  pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as BR.
  (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof AR as ndP__; nd_pre ndP__ 8%nat; intros WF _ _ _ CLS _ HS _; nd_post). (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros SBE PAE SAL SLO SHI PERC _; nd_post).
  cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. (pose proof HS as ndP__; nd_pre ndP__ 5%nat; intros (_ & _ & _ & _ & _ & WF1 & _) (order & PO & _ & _ & PER) _ PZ _; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (* [comment removed for export] *)
    set (c := xb_class b) in *. set (k := xb_slot b) in *. set (S := size_of_class c) in *.
    pose proof (size_of_class_facts c CLB) as [QS QS16].
    (nd_pre (PERC c CLB) 5%nat; intros A1 A2 A3 A4 _; nd_post). (nd_pre (RCLS c CLB) 3%nat; intros RREG RSREG _; nd_post). cbv zeta in RREG, RSREG.
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ16. pose proof (rz_size_facts n ltac:(clear -NB; lia)) as [_ RZM].
    pose proof (aregion_mod L c SAL) as RM. pose proof (slot_aligned L c k SAL ltac:(exact CLB)) as AL16.
    assert (EAB : xb_alloc L b = aslot_addr L c k) by reflexivity.
    subst A. unfold xb_user in *. rewrite EAB in *. rewrite Nb in *.
    assert (A8 : (aslot_addr L c k + rz_size n) mod 8 = 0) by (clear -AL16 RZM; Z.div_mod_to_equations; lia).
    unfold K_FREEARR_OFF, K_NUM_CLASSES in *.
    split; [exact NB|]. split; [exact BR|].
    split. { eapply rng_sub'; [exact RREG|]. clear -P5 P4 A1 FIT RG RZ16. lia. }
    split. { eapply rng_sub'; [exact RSREG|]. rewrite !shad_div, !shlen_div. unfold K_USER_MAP in A4. clear -P5 P4 A1 FIT RG RZ16 RM A4 A8. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    (nd_pre (CLS c CLB) 4%nat; intros _ _ [SL _] [SSH _]; nd_post).
    assert (EBK : busy_of X c k = Some b) by (exact (busy_of_of_In L st X b WF Hb)).
    pose proof (SSH k KB) as SH. rewrite EBK in SH. cbn [slot_shadow_bytes] in SH. rewrite Sb, Nb in SH. fold S in SH.
    (pose proof (chunk_shadow_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GEq G0 GF _; nd_post).
    pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
    assert (LBS : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
    replace (Z.to_nat (shlen S)) with (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen (rz_size n) - granules n))%nat in SH
      by (generalize SRZ SG7 GF; subst S; clear; unfold granules; intros; lia).
    (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LBS ltac:(apply repeat_length) SH) 3%nat; intros _ SHU _; nd_post).
    rewrite Z2Nat.id in SHU by lia. rewrite <- SE in SHU.
    split. { eapply block_shadow_of_cb; [clear -NB; lia| exact A8| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| (nd_pre BR 4%nat; intros _ _ B3 _; nd_post); clear -B3; lia| exact SHU]. }
    (* [comment removed for export] *)
    pose proof (SL k KB) as SLK. rewrite EBK in SLK. unfold aslot_busy in SLK. cbv zeta in SLK. rewrite Sb in SLK.
    (nd_pre SLK 3%nat; intros _ _ UJ; nd_post). rewrite EAB, Nb in UJ. fold S in UJ.
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (S - rz_size n)); [clear -FIT RG NB; lia| exact UJ]| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| clear; lia| clear -FIT RG NB; lia]. }
    split. { exists (CPrim c n). split; [exact LV|]. split; [reflexivity|]. intros P. rewrite PRIM in P. discriminate. }
    (* [comment removed for export] *)
    exists (aregion L (c - 1)), (aregion L (c + 1)).
    assert (GEO : aregion L (c - 1) + K_REGION = aregion L c /\ aregion L c + K_REGION = aregion L (c + 1) /\ aregion L 0 = al_space_beg L
                  /\ aregion L (c - 1) mod 4096 = 0 /\ 0 <= aregion L (c - 1)).
    { unfold aregion, K_REGION. unfold K_ALIGN in SAL. clear -SAL SP1 CLB. repeat split; first [nia | Z.div_mod_to_equations; nia]. }
    (nd_pre GEO 5%nat; intros GE1 GE2 GE0 GAL GNN; nd_post). unfold K_REGION in GE1, GE2. change (2 ^ 32) with 4294967296 in GE1, GE2.
    split; [exact GAL|]. split; [rewrite <- GE2, <- GE1; clear -GAL; Z.div_mod_to_equations; lia|].
    split; [clear -GE1 P5 RZ16; lia|]. split; [clear -GE2 P4 A1 A2 FIT RG; lia|].
    rewrite <- GE2, <- GE1. replace (aregion L (c - 1) + 4294967296 + 4294967296 - aregion L (c - 1)) with (4294967296 + 4294967296) by (clear; lia).
    split.
    + eapply rng_sub'; [exact RPSH|]. rewrite !shad_div, !shlen_div. unfold K_SPACE_SIZE. unfold aregion, K_REGION in *.
      clear -CLB SP3. unfold K_ALIGN in SP3. Z.div_mod_to_equations. nia.
    + replace (shlen (4294967296 + 4294967296)) with (shlen K_REGION + shlen K_REGION) by reflexivity.
      apply wr_at_join; [| | apply shlen_nonneg; unfold K_REGION; clear; lia| apply shlen_nonneg; unfold K_REGION; clear; lia].
      * destruct (Z.eq_dec c 1) as [C1|C1].
        { rewrite C1. change (1 - 1) with 0. rewrite GE0. exact (wr_of_azero _ _ _ PZ). }
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; clear -CLB C1; lia].
      * rewrite <- shad_add_shlen by (rewrite <- GAL; clear -GAL; Z.div_mod_to_equations; lia). unfold K_REGION. change (2 ^ 32) with 4294967296. rewrite GE1.
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; exact CLB].
  - (* [comment removed for export] *)
    pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
    apply ablk_lin in G2.   (* [comment removed for export] *)
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros NBg RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- G4 in MSE, MSR, MSM, MSB.
    pose proof (proj1 (Forall_forall _ _) RSECS _ INC) as [RC RSC]. cbn [sec_mb sec_ms] in RC, RSC.
    (* [comment removed for export] *)
    pose proof (Permutation_in _ (Permutation_sym PO) INC) as INO. apply In_nth_error in INO. destruct INO as [i Hi].
    (nd_pre (PER i _ Hi) 3%nat; intros lv LVE CH; nd_post).
    assert (LVT : lv = true) by (apply (proj2 LVE); exists p; exact Lp). subst lv.
    cbn [asec_chunk] in CH. (nd_pre CH 9%nat; intros _ _ _ _ _ UJ SF1 SU SF2; nd_post). unfold SEC_UOFF, K_HIGH_MEM in *. subst A.
    assert (SG : shad (mb + 6144) = shad mb + 768 /\ shad mb + ms / 8 = shad (mb + ms) /\ 768 + granules n <= ms / 8 /\ 0 <= granules n /\ shlen ms = ms / 8
                 /\ (mb + 6144) mod 8 = 0 /\ 0 <= shad mb).
    { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -G1 G2 NBg RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
    (nd_pre SG 7%nat; intros SG1 SG2 SG3 SG4 SG5 SG6 SG7; nd_post).
    split; [clear -G5; lia|]. split; [exact BR|].
    split; [eapply rng_sub'; [exact RC|]; clear -NSE RSR MSR NBg; lia|].
    split; [eapply rng_sub'; [exact RSC|]; rewrite !shad_div, !shlen_div; rewrite shad_div in SG2; unfold ASHOFF in *; clear -G1 NSE RSR MSR NBg; Z.div_mod_to_equations; lia|].
    split. { eapply block_shadow_of_cb; [clear -NBg; lia| exact SG6| clear -G2; lia| clear -G3 NSE RSR MSR NBg; lia| unfold sec_user_shadow in SU; exact SU]. }
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (ms - 6144)); [clear -MSR NSE RSR NBg; lia| exact UJ]| clear -G2; lia| clear; lia| clear -MSR NSE RSR NBg; lia]. }
    split. { exists (CSec mb ms n). split; [exact Lp|]. split; [reflexivity|]. intros _. cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
    exists mb, (mb + ms). split; [exact G1|]. split; [clear -G1 MSM; Z.div_mod_to_equations; lia|]. split; [clear; lia|]. split; [clear -MSR NSE RSR NBg; lia|].
    replace (mb + ms - mb) with ms by (clear; lia). rewrite SG5.
    split; [exact RSC|].
    pose proof SF1 as W1. apply wr_of_fill in W1; [| clear; lia].
    pose proof SF2 as W3. apply wr_of_fill in W3; [| clear -SG3 SG4; lia].
    pose proof (wr_of_cells _ _ _ SU) as W2. cbn [cells_size csize] in W2. rewrite Nat.add_0_r, Z2Nat.id in W2 by exact SG4.
    replace (ms / 8) with (768 + (granules n + (ms / 8 - 768 - granules n))) by (clear -SG3; lia).
    apply wr_at_join; [exact W1| | clear; lia| clear -SG3 SG4; lia].
    rewrite <- SG1. apply wr_at_join; [exact W2| exact W3| exact SG4| clear -SG3 SG4; lia].
Qed.
End Zd2.
#[using="Type"] Theorem AHI_block : ltac:(let t := eval cbv delta [AHI_block__stmt] in AHI_block__stmt in exact t).
Proof. exact AHI_block__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_block_tls : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= ATPv + -200 \/ ATPv + 312 <= ab_addr b.
Proof.
  intros L RNG st LB m b AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ad_tls_res L ALO) as TR. pose proof (ad_tls_fake L ALO) as TF. unfold adisj in TR, TF.
  destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(xb & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
    + pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. unfold xb_user in Ub. subst A. rewrite Nb in *.
      clear -TR R1 R2 FIT RG RZ NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & _ & _ & _ & _ & _ & _ & Ctls); nd_post).
      (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR. subst A. unfold SEC_UOFF.
      clear -Ctls RSR NSE MSR G5. lia.
  - (nd_pre (afake_lb L LB m cls A n HFK Hin) 7%nat; intros _ _ NP _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -TF K5 K6 NP. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_block_ahm : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= AAHMv \/ AAHMv + AAHM_SZ <= ab_addr b.
Proof.
  intros L RNG st LB m b AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO _ [X [AR BL]] HFK; nd_post). cbn [AHI ah_fake] in HFK.
  pose proof (ad_ahm_res L ALO) as TR. pose proof (ad_ahm_fake L ALO) as TF. unfold adisj in TR, TF. rewrite <- (ao_ahm_eq L ALO). unfold AAHM_SZ.
  destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(xb & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
    + pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. unfold xb_user in Ub. subst A. rewrite Nb in *.
      clear -TR R1 R2 FIT RG RZ NB. lia.
    + cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cahm); nd_post).
      (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR. subst A. unfold SEC_UOFF.
      clear -Cahm RSR NSE MSR G5. lia.
  - (nd_pre (afake_lb L LB m cls A n HFK Hin) 7%nat; intros _ _ NP _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -TF K5 K6 NP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma AHI_premap : forall L RNG st LB m, AHEAP_I L RNG st LB m -> premap_cells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). (nd_pre AR 12%nat; intros _ RT _ _ _ _ _ _ _ RT2 _ RT3; nd_post).
  eapply premap_of_rt'; [exact RT| exact RT2| exact RT3].
Qed.
End CANSEC2.
End TwB.
End AInstanceM.
