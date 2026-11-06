(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AALIGNED_SYM : Z := 0x5e420.
Definition AALIGNED_PC : Z := 0x5ebf8.

Definition icptA16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (al n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5ec0c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x5ebf8) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 al) (Z_to_bv 64 0x5ebf8) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5ec50) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma icptA16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (al n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 al -> a1 = Z_to_bv 64 n -> 0 <= n < 2^64 -> 0 <= al < 2^64 ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                             C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptA16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc al n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NR ALR MCS GOT CF34 RIMG RSTK. atop_facts. unfold AALIGNED_SYM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.
  carve_frame 2144%nat ST.

  apply (rw_cells_split_CB asegs _ _ [] 2144%nat _ [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]. cbn [app mk_CB_cells] in FR.
  rw_split FR 1%nat FRp FR1. rw_split FR1 1%nat FRa FR2. rw_split FR2 1%nat FRt FRs.
  do 9 step.
  zstep. zstep. step. step. step.
  zstep. zstep. zstep. zstep. zstep.
  step. sstep. step.
  step. step. lstep. step. step.
  step. step. if_lit.
  step. step. step.
  step. step. lstep. step.
  step. step. lstep. step. step.
  step. zstep. zstep. zstep. step.
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.
  step. if_lit.
  zstep. zstep. step. step. step. step.
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA16_post. do 10 eexists. do 3 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.

Definition icptB16_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x5ec68) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 16)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 16) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  (Z_to_bv 64 16) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3d8a4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp - 2144)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2176)
    /\ rw_cells asegs m' (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5ec68)].

Lemma icptB16_spec : forall RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv asegs m ->
  0 <= n < 2^64 -> n mod 16 = 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptB16_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 16) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5ec54) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI NR N16 RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp - 2144)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. zstep. zstep.
  step. if_lit.
  zstep.
  replace (Z.land n 15) with 0 by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; change (2^4) with 16; lia).
  step. if_lit.
  do 6 step.
  apply evtF_done. unfold icptB16_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.

Lemma icptC16_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s0i s1i s2i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2176) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2176) [C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x5ec68)] ->
  (exists csP, rw_cells asegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x3d8a8) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d8a8) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR32 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 6 step.
  zstep. do 8 step. zstep. step.
  release_frame FR32 ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget asegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  release_frame FRP' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import AProto.TwinB ABase.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AALIGNED_SYM : Z := 0x5edb0.
Definition AALIGNED_PC : Z := 0x5f588.

Definition icptA16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (al n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5f59c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x5f588) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 al) (Z_to_bv 64 0x5f588) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5f5e0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma icptA16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (al n lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 - 16 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 al -> a1 = Z_to_bv 64 n -> 0 <= n < 2^64 -> 0 <= al < 2^64 ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                             C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (icptA16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc al n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NR ALR MCS GOT CF34 RIMG RSTK. atop_facts. unfold AALIGNED_SYM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step.
  carve_frame 2144%nat ST.

  apply (rw_cells_split_CB bsegs _ _ [] 2144%nat _ [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]. cbn [app mk_CB_cells] in FR.
  rw_split FR 1%nat FRp FR1. rw_split FR1 1%nat FRa FR2. rw_split FR2 1%nat FRt FRs.
  do 9 step.
  zstep. zstep. step. step. step.
  zstep. zstep. zstep. zstep. zstep.
  step. sstep. step.
  step. step. lstep. step. step.
  step. step. if_lit.
  step. step. step.
  step. step. lstep. step.
  step. step. lstep. step. step.
  step. zstep. zstep. zstep. step.
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.
  step. if_lit.
  zstep. zstep. step. step. step. step.
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA16_post. do 10 eexists. do 3 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.

Definition icptB16_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x5f5f8) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 16)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 16) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  (Z_to_bv 64 16) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3e234) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp - 2144)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2176)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5f5f8)].

Lemma icptB16_spec : forall RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk bsegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv bsegs m ->
  0 <= n < 2^64 -> n mod 16 = 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (icptB16_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 16) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5f5e4) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI NR N16 RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp - 2144)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. step. step. step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. zstep. zstep.
  step. if_lit.
  zstep.
  replace (Z.land n 15) with 0 by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; change (2^4) with 16; lia).
  step. if_lit.
  do 6 step.
  apply evtF_done. unfold icptB16_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.

Lemma icptC16_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s0i s1i s2i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk bsegs m lo (bv_unsigned sp + -2176) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv bsegs m ->
  0 < UB < 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + -2176) [C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x5f5f8)] ->
  (exists csP, rw_cells bsegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x3e238) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e238) fc None m (seg_rom bsegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR32 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 6 step.
  zstep. do 8 step. zstep. step.
  release_frame FR32 ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget bsegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  release_frame FRP' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.
End CANSEC1.
End TwinB.
