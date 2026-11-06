(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

Definition soc_post (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (c : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 0x21e7e) (Z_to_bv 64 4096) (Z_to_bv 64 c) (Z_to_bv 64 (size_of_class c))
                           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x422d4) fc None m (seg_rom asegs).

Lemma soc_seg : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (c : Z),
  1 <= c < K_NUM_CLASSES ->
  evtF asegs RNG (soc_post ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
        (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42264) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros Hc. unfold K_NUM_CLASSES in Hc.
  assert (D : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  Ltac soc_fin := apply evtF_done; unfold soc_post; reflexivity.
  Ltac soc_small := step; step; step; if_lit; step; step; if_lit; zstep; step; step; zstep; zstep; soc_fin.
  Ltac soc_big := step; step; step; if_lit; step; step; if_lit; zstep; step; zstep; zstep; zstep; zstep; zstep; zstep; zstep; step; zstep; zstep; soc_fin.
  Ltac soc_31 := step; step; step; if_lit; step; step; step; zstep; zstep; soc_fin.
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  subst c. soc_31.
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ABytes.TwinB AFrameD.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

Definition soc_post (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (c : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 0x21f1c) (Z_to_bv 64 4096) (Z_to_bv 64 c) (Z_to_bv 64 (size_of_class c))
                           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x42c64) fc None m (seg_rom bsegs).

Lemma soc_seg : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (c : Z),
  1 <= c < K_NUM_CLASSES ->
  evtF bsegs RNG (soc_post ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
        (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42bf4) fc None m (seg_rom bsegs)).
Proof.
  intros until c. intros Hc. unfold K_NUM_CLASSES in Hc.
  assert (D : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  Ltac soc_fin := apply evtF_done; unfold soc_post; reflexivity.
  Ltac soc_small := step; step; step; if_lit; step; step; if_lit; zstep; step; step; zstep; zstep; soc_fin.
  Ltac soc_big := step; step; step; if_lit; step; step; if_lit; zstep; step; zstep; zstep; zstep; zstep; zstep; zstep; zstep; step; zstep; zstep; soc_fin.
  Ltac soc_31 := step; step; step; if_lit; step; step; step; zstep; zstep; soc_fin.
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_small. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  destruct D as [->|D]. { soc_big. }
  subst c. soc_31.
Qed.
End CANSEC2.
End TwinB.
