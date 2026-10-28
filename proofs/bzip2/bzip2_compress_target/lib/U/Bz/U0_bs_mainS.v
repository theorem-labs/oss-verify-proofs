(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs4 CmpMsKit.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation E := (me_E X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Definition WMAIN : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (p, p + 4904)]%Z.

  Definition U_bs_main_spec : Prop :=
    forall (a1 a2 ft bd ro : zarr) (j0 jce jcs jnx jsd jhi jlo : list byte)
      (w24 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
       w232 w240 w248 w256 w264 w272 w280 w288 w296 : word)
      (x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word)
      (me m : word -> option byte),
    (417792 <= A1)%Z -> (417792 <= A2)%Z -> (417792 <= FT)%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) -> (0 <= n * budget_q < 2147483648)%Z ->
    (forall (cs ce nl nh nd : zarr) (k : nat), (0 + Z.of_nat k <= 255)%Z ->
       let s' := ms_bigs k ro qo n 0 (MSS a1 a2 ft bd cs ce (n * budget_q) 0 (MQL znew znew znew nl nh nd) false) in
       s_exit s' = false -> bigF qo n ro (0 + Z.of_nat k) s') ->
    (forall (cs ce nl nh nd : zarr) (k : nat), (0 + Z.of_nat k <= 255)%Z ->
       let s' := ms_bigs k ro qo n 0 (MSS a1 a2 ft bd cs ce (n * budget_q) 0 (MQL znew znew znew nl nh nd) false) in
       s_exit s' = false ->
       forall j, (j < 256)%nat -> let s'' := ms_step1 j qo n (zget ro (0 + Z.of_nat k)) 0 s' in s_exit s'' = false ->
       (0 <= s_nqs s'' /\ s_nqs s'' + n <= 2147483647)%Z) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    rw_cells s0segs m p [CB 8 j0] ->
    rw_cells s0segs m (p + 8) [C8 (Z_to_bv 64 (n * budget_q)); C8 (Z_to_bv 64 E); C8 w24; C8 (Z_to_bv 64 (n - 1));
                               C8 w40; C8 w48; C8 (Z_to_bv 64 0); C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112] ->
    rw_cells s0segs m (p + 120) [C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184;
                                 C8 w192; C8 w200; C8 w208; C8 w216; C8 (Z_to_bv 64 (18446744073709551615 - A2)); C8 w232; C8 w240; C8 w248; C8 w256;
                                 C8 w264; C8 w272; C8 w280; C8 w288; C8 w296;
                                 C8 (Z_to_bv 64 FT); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 (18446744073709551615 - FT))] ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 (n * budget_q))] ->
    rw_cells s0segs m (p + 340) [CB 1024 jce] -> rw_cells s0segs m (p + 1364) [CB 1024 jcs] ->
    u8arr s0segs m (p + 2388) (zb8 bd 256) -> u32arr s0segs m (p + 2644) (zw32 ro 256) ->
    rw_cells s0segs m (p + 3668) [CB 36 jnx] -> rw_cells s0segs m (p + 3704) [CB 400 jsd] ->
    rw_cells s0segs m (p + 4104) [CB 400 jhi] -> rw_cells s0segs m (p + 4504) [CB 400 jlo] ->
    rw_cells s0segs m (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> cimg_mem S0C m (me_sv X) ->
    mem_inv s0segs m -> munch WMAIN me m -> wmono s0segs me m ->
    (forall m' (a1' a2' ft' bd' cs' ce' CSJ CEJ : zarr) (b' nqs' : Z) (L' : mqloc)
            (y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_bigs 256 ro qo n 0 (MSS a1 a2 ft bd CSJ CEJ (n * budget_q) 0 (MQL znew znew znew znew znew znew) false)
        = MSS a1' a2' ft' bd' cs' ce' b' nqs' L' false ->
      (0 <= b')%Z -> zbok a1' -> zbok a2' ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      stk s0segs m' p (p + 4904) ->
      rw_cells s0segs m' (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> cimg_mem S0C m' (me_sv X) ->
      mem_inv s0segs m' -> munch WMAIN me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 (Z_to_bv 64 E) y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 139568) fc None m' (seg_rom s0segs))) ->
    (forall m' (a1' a2' ft' bd' cs' ce' CSJ CEJ : zarr) (b' nqs' : Z) (L' : mqloc)
            (y0 y4 y5 y6 y7 y14 y15 y16 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_bigs 256 ro qo n 0 (MSS a1 a2 ft bd CSJ CEJ (n * budget_q) 0 (MQL znew znew znew znew znew znew) false)
        = MSS a1' a2' ft' bd' cs' ce' b' nqs' L' true ->
      (b' < 0)%Z -> zbok a1' -> zbok a2' ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      stk s0segs m' p (p + 4904) ->
      rw_cells s0segs m' (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> cimg_mem S0C m' (me_sv X) ->
      mem_inv s0segs m' -> munch WMAIN me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 (Z_to_bv 64 E)
                            (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 n) (Z_to_bv 64 0) y14 y15 y16
                            (Z_to_bv 64 A1) y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 132112) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 134436) fc None m (seg_rom s0segs)).
End S0MS.

End ACeilS1.
