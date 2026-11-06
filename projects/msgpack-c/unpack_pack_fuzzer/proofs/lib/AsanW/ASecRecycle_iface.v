(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Notation SREC_STACK := 1024 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Iface.

Variable ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop.

Variable RSEC : list achunk -> footprint -> Prop.

Definition AHS (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop) : aholes :=
  mkAHoles AQ (ASECc cs) AD AF.

Record srec_holes_ok (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) : Prop := mkSHO {
  sho_quar : forall L st st' X X' m m' W,
      AQ L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> AQ L st' X' m';
  sho_depot : forall L m m' W,
      AD L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1ab988 <= a < 0x5fb9d0) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      AD L m'
}.

Definition srec_W (L : alayout) (sp : Z) (mb ms : Z) (nres : Z) : list (Z * Z) :=
  [(sp - SREC_STACK, sp); (al_t L + 2800, al_t L + 3168); (AINSTANCE + 64, AINSTANCE + 728);
   (al_ptr_array L, al_ptr_array L + 8 * nres); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

Definition srec_hl_ok (L : alayout) (hl : Z) : Prop :=
  ablk hl (hl + 8) /\ hl + 8 <= ATOP /\ sec_clear L hl 8.

Definition srec_ret (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs1 cs2 : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (mb ms : Z) (lo : Z) (m : amem)
    (st' : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' hl,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ st' = set_nsec (a_nsec st - 1) st
    /\ srec_hl_ok L hl

    /\ ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) (cs1 ++ cs2) /\ sec_wf1 L (CSec (hl - 24) lms ln)))
    /\ munch (srec_W L (bv_unsigned sp) mb ms (a_nres st) ++ [(hl, hl + 8)]) m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP (AHS AQ (cs1 ++ cs2) AD AF) L st' X m'

    /\ fstepS (NMunmap mb ms) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 ms)] [] []) RNG RNG'
    /\ arng L RNG' st' /\ RSEC (cs1 ++ cs2) RNG'.

Definition srec_stmt : Prop :=
  forall (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
         (cs1 cs2 : list achunk) {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (mb ms n CBA lo : Z),
  srec_holes_ok AQ AD ->
  alayout_ok L -> arng L RNG st -> RSEC (cs1 ++ CSec mb ms n :: cs2) RNG ->
  AREP (AHS AQ (cs1 ++ CSec mb ms n :: cs2) AD AF) L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC_STACK -> bv_unsigned sp <= 2^47 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + PG + rz_size n - 16) ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->

  (forall st' RNG' ms', srec_ret AQ cs1 cs2 AD AF L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X mb ms lo m st' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k st')) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3efd8) fc None m (seg_rom asegs)).
End Iface.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Notation SREC_STACK := 1024 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Iface.

Variable ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop.

Variable RSEC : list achunk -> footprint -> Prop.

Definition AHS (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop) : aholes :=
  mkAHoles AQ (ASECc cs) AD AF.

Record srec_holes_ok (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) : Prop := mkSHO {
  sho_quar : forall L st st' X X' m m' W,
      AQ L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> AQ L st' X' m';
  sho_depot : forall L m m' W,
      AD L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1adb48 <= a < 0x5fdb90) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      AD L m'
}.

Definition srec_W (L : alayout) (sp : Z) (mb ms : Z) (nres : Z) : list (Z * Z) :=
  [(sp - SREC_STACK, sp); (al_t L + 2800, al_t L + 3168); (AINSTANCE + 64, AINSTANCE + 728);
   (al_ptr_array L, al_ptr_array L + 8 * nres); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

Definition srec_hl_ok (L : alayout) (hl : Z) : Prop :=
  ablk hl (hl + 8) /\ hl + 8 <= ATOP /\ sec_clear L hl 8.

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

    /\ ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) (cs1 ++ cs2) /\ sec_wf1 L (CSec (hl - 24) lms ln)))
    /\ munch (srec_W L (bv_unsigned sp) mb ms (a_nres st) ++ [(hl, hl + 8)]) m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AREP (AHS AQ (cs1 ++ cs2) AD AF) L st' X m'

    /\ fstepS (NMunmap mb ms) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 ms)] [] []) RNG RNG'
    /\ arng L RNG' st' /\ RSEC (cs1 ++ cs2) RNG'.

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

  (forall st' RNG' ms', srec_ret AQ cs1 cs2 AD AF L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X mb ms lo m st' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k st')) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3f968) fc None m (seg_rom bsegs)).
End Iface.
End CANSEC1.
End TwinB.
