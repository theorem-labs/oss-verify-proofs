(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small D_kit X_xdefs X_unregi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation UNREG_W :=
  [(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6a9960%Z, 0x6a9961%Z); (0x6a9961%Z, 0x6a996b%Z)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (o1' o2' o3' o4' o5' o6' o7' o8' o9' o10' o11' : byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x208c68) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 0x173a50) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
                  (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 0)
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x67c80) fc None m' (seg_rom bsegs)
    /\ munch UNREG_W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' XS1_LO XS1_HI /\ stk bsegs m' XS2_LO XS2_HI /\ stk bsegs m' XS3_LO XS3_HI
    /\ rw_cells bsegs m' 0x6a9960 [C1 o1'] /\ rw_cells bsegs m' 0x6a9961 [C1 o2'] /\ rw_cells bsegs m' 0x6a9962 [C1 o3'] /\ rw_cells bsegs m' 0x6a9963 [C1 o4'] /\ rw_cells bsegs m' 0x6a9964 [C1 o5'] /\ rw_cells bsegs m' 0x6a9965 [C1 o6'] /\ rw_cells bsegs m' 0x6a9966 [C1 o7'] /\ rw_cells bsegs m' 0x6a9967 [C1 o8'] /\ rw_cells bsegs m' 0x6a9968 [C1 o9'] /\ rw_cells bsegs m' 0x6a9969 [C1 o10'] /\ rw_cells bsegs m' 0x6a996a [C1 o11'].

Lemma unreg_loop : forall (gs : list gdesc) (K : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte),
  Forall (fun g => gd_okb g = true) gs -> Z.of_nat (length gs) = K -> 1 <= K <= 39 ->
  gds_at m (0x173a50 - 64 * K) gs ->
  rw_cells bsegs m 0x177e18 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x17699c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x174950 [C4 (Z_to_bv 64 1)] ->
  ro_cells bsegs m 0x177138 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x208ce0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x1701e0 [C8 (Z_to_bv 64 0x160c88)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  rw_cells bsegs m 0x6a9960 [C1 o1] -> rw_cells bsegs m 0x6a9961 [C1 o2] -> rw_cells bsegs m 0x6a9962 [C1 o3] -> rw_cells bsegs m 0x6a9963 [C1 o4] -> rw_cells bsegs m 0x6a9964 [C1 o5] -> rw_cells bsegs m 0x6a9965 [C1 o6] -> rw_cells bsegs m 0x6a9966 [C1 o7] -> rw_cells bsegs m 0x6a9967 [C1 o8] -> rw_cells bsegs m 0x6a9968 [C1 o9] -> rw_cells bsegs m 0x6a9969 [C1 o10] -> rw_cells bsegs m 0x6a996a [C1 o11] ->
  mem_inv bsegs m ->
  evt bsegs (unreg_loop_post sp gp tp F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x208c68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 (0x173a50 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
             (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a7c) fc None m (seg_rom bsegs)).
Proof.
  induction gs as [|g gs IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11
    OK LEN HK GDS AI CP RG SHC THR RMS SC1 SC2 SC3 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  { cbn in LEN. lia. }
  inversion OK as [|g0 gs0 OKg OKgs]. subst g0 gs0.
  destruct GDS as (REC & GDS).
  destruct (gd_okb_spec g OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR & Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [length] in LEN.
  destruct g as [beg size srz name modn dyn loc odr]. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in *.
  unfold gd_cells in REC. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in REC.
  pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
  unfold SHB in INS.
  call (unreg_iter_head (0x173a50 - 64 * K) K beg srz); [exact REC| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
        | exact SC1| exact SC2| exact SC3| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact MI|].
  call (unreg_iter_tail (0x173a50 - 64 * K) K odr); [exact REC| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| exact ODR| lia| lia| lia| assumption|].
  destruct (Z.eqb_spec K 1) as [EK|NK].
  - assert (GS0 : gs = []) by (destruct gs; [reflexivity| cbn [length] in LEN; lia]). subst gs.
    rewrite EK in *.
    apply evt_done. unfold unreg_loop_post.
    do 18 eexists. do 11 eexists. split; [reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
    repeat (split; [eassumption|]). eassumption.
  - replace (0x173a50 - 64 * K + 64) with (0x173a50 - 64 * (K - 1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      replace pc with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
    eapply evt_cut.
    + eapply (IH (K - 1)); try eassumption; try lia.
      replace (0x173a50 - 64 * (K - 1)) with (0x173a50 - 64 * K + 64) by lia.
      apply (gds_at_agree gs m _ _ GDS). apply (agree_of_munch _ _ _ _ MU0). intros xa Hxa. cbn [outside]. lia.
    + intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
      destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      o1' & o2' & o3' & o4' & o5' & o6' & o7' & o8' & o9' & o10' & o11' & E & MU' & WM' & MI' & R).
      exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', o1', o2', o3', o4', o5', o6', o7', o8', o9', o10', o11'.
      split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
      * eapply munch_trans; [exact MU0| exact MU'].
      * eapply wmono_trans; [exact WM0| exact WM'].
Qed.
