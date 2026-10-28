(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation SREC_STACK := 1024 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Section Iface.
(* [comment removed for export] *)
Variable ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop.
(* [comment removed for export] *)
Variable RSEC : list achunk -> footprint -> Prop.

(* [comment removed for export] *)
Definition AHS (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop) : aholes :=
  mkAHoles AQ (ASECc cs) AD AF.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record srec_holes_ok (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) : Prop := mkSHO {
  sho_quar : forall L st st' X X' m m' W,
      AQ L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> AQ L st' X' m';
  sho_depot : forall L m m' W,
      AD L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x18c1c8 <= a < 0x5dc210) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      AD L m'
}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srec_W (L : alayout) (sp : Z) (mb ms : Z) (nres : Z) : list (Z * Z) :=
  [(sp - SREC_STACK, sp); (al_t L + 2800, al_t L + 3168); (AINSTANCE + 64, AINSTANCE + 728);
   (al_ptr_array L, al_ptr_array L + 8 * nres); (mb, mb + ms); (shad mb, shad mb + shlen ms)].
(* [comment removed for export] *)
Definition srec_hl_ok (L : alayout) (hl : Z) : Prop :=
  ablk hl (hl + 8) /\ hl + 8 <= ATOP /\ sec_clear L hl 8.

(* [comment removed for export] *)
Definition srec_ret (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs1 cs2 : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (mb ms : Z) (lo : Z) (m : amem)
    (st' : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' hl,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ st' = set_nsec (a_nsec st - 1) st
    /\ srec_hl_ok L hl
    (* [comment removed for export] *)
    /\ ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) (cs1 ++ cs2) /\ sec_wf1 L (CSec (hl - 24) lms ln)))
    /\ munch (srec_W L (bv_unsigned sp) mb ms (a_nres st) ++ [(hl, hl + 8)]) m m' /\ mem_inv bsegs m'   (* [comment removed for export] *)
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AREP (AHS AQ (cs1 ++ cs2) AD AF) L st' X m'
    (* [comment removed for export] *)
    /\ fstepS (NMunmap mb ms) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 ms)] [] []) RNG RNG'
    /\ arng L RNG' st' /\ RSEC (cs1 ++ cs2) RNG'.

(* [comment removed for export] *)
Definition srec_stmt : Prop :=
  forall (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
         (cs1 cs2 : list achunk) {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (mb ms n CBA lo : Z),
  srec_holes_ok AQ AD ->
  alayout_ok L -> arng L RNG st -> RSEC (cs1 ++ CSec mb ms n :: cs2) RNG ->
  AREP (AHS AQ (cs1 ++ CSec mb ms n :: cs2) AD AF) L st X m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC_STACK -> bv_unsigned sp <= 2^47 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + PG + rz_size n - 16) ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st' RNG' ms', srec_ret AQ cs1 cs2 AD AF L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X mb ms lo m st' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k st')) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x33900) fc None m (seg_rom bsegs)).
End Iface.
End CANSEC1.
