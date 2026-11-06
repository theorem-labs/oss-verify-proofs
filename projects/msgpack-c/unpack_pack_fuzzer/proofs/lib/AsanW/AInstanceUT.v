(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ARep AHeapP ARepExt FsKit AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFake_tlsP F_adepot ARepQ ARepQP ASec AInstance AInstanceM AInstanceF AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Definition tlsgaU_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m'
    /\ aheap_pres aci_I LB (bv_unsigned sp) m m'
    /\ AHEAPu L RNG st LB m'.

Definition tlsgaU_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAPu L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF asegs RNG (tlsgaU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).

Theorem AHU_tlsga : tlsgaU_stmt.
Proof.
  unfold tlsgaU_stmt. intros until A. intros [g AH] MI ST BOT LO TP A0 ABV DESC RSTK RA.
  eapply evtF_mono.
  - eapply (tlsga_P adepot_iface AQUAR ASEC_of g (AH_laws (gb:=g)) aci_I aci_ok1); eassumption.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & MU & WM & PR & AH').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MU|]. split; [exact WM|]. split; [exact PR|]. exists g; exact AH'.
Qed.

End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import RtCells.TwinB AProto.TwinB ABase.TwinB ABytes.TwinB AMalloc_iface.TwinB ARep.TwinB AHeapP.TwinB ARepExt.TwinB FsKit.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import AFake_tlsP.TwinB F_adepot.TwinB ARepQ.TwinB ARepQP.TwinB ASec.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AInstanceU.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Definition tlsgaU_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m'
    /\ aheap_pres aci_I LB (bv_unsigned sp) m m'
    /\ AHEAPu L RNG st LB m'.

Definition tlsgaU_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAPu L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF bsegs RNG (tlsgaU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom bsegs)).

Theorem AHU_tlsga : tlsgaU_stmt.
Proof.
  unfold tlsgaU_stmt. intros until A. intros [g AH] MI ST BOT LO TP A0 ABV DESC RSTK RA.
  eapply evtF_mono.
  - eapply (tlsga_P adepot_iface AQUAR ASEC_of g (AH_laws (gb:=g)) aci_I aci_ok1); eassumption.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & MU & WM & PR & AH').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MU|]. split; [exact WM|]. split; [exact PR|]. exists g; exact AH'.
Qed.

End CANSEC1.
End TwinB.
