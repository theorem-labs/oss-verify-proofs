(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 97 of its 113 lines of code are new or changed and 129 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_scene_struct reac_ctrl_scene_build_c memset_c memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.

Ltac refuse_path FR ST sp :=
  do 4 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish; repeat (first [reflexivity | assumption | split]).

Theorem reac_ctrl_scene_build_holds : memset_contract -> memcpy_contract -> reac_ctrl_scene_build_contract.
Proof.
  intros MEMS MEMC. unfold reac_ctrl_scene_build_contract, REAC_CTRL_SCENE_BUILD, REAC_CTRL_SCENE_BUILD_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo junk macb HMI ST LO HOK.
  norm_nat_lits.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 8904)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (scene_ok a0 a1 a2) eqn:EOK.
  - destruct (HOK eq_refl) as (HB & HM & HL & D1 & D2 & D3). clear HOK.
    destruct (scene_ok_true _ _ _ EOK) as (O1 & O2 & O3).
    assert (HBd : bv_unsigned a0 + 8904 <= 2^64)
      by (destruct (rw_cells_bound _ _ _ _ HB) as [_ X]; exact X).
    assert (HS : rw_cells rsegs m (bv_unsigned a0) ([CB 4 (firstn 4 junk)] ++ [CB 8900 (skipn 4 junk)])).
    { eapply rw_cells_cb_split with (k := 0%nat) (n := 4%nat); [exact HB | reflexivity | reflexivity]. }
    clear HB.
    destruct (rw_cells_split2 m (bv_unsigned a0) (bv_unsigned a0 + 4) _ _ HS
                ltac:(cbn [cells_size csize Nat.add]; lia)) as [HA HB].
    clear HS. norm_nat_lits.
    carve_frame 32%nat ST.
    do 7 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    do 4 zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    do 5 zstep.
    assert (UD4 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 4)) = bv_unsigned a0 + 4) by (apply unsigned_lit; lia).
    assert (U8900 : bv_unsigned (Z_to_bv 64 8900) = 8900) by reflexivity.
    call MEMS.
    { rewrite UD4, U8900. exact HB. }
    { exact HMI. }
    match goal with
    | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 4))) _ |- _ =>
        rewrite UD4 in P;
        assert (P2 : rw_cells rsegs mm (bv_unsigned a0 + 4) scene_mid_cells)
          by (eapply rw_cells_rebytes; [exact P | exact scene_mid_wf | rewrite scene_mid_bytes; vm_compute; reflexivity]);
        clear P
    end.
    destruct (rw_cells_split2 _ (bv_unsigned a0 + 4) (bv_unsigned a0 + 832) [CB 828 (repeat zb 828)]
                ([CB 6 (repeat zb 6)] ++ scene_tail_cells) P2 ltac:(cbn [cells_size csize Nat.add]; lia)) as [HL1 P3].
    destruct (rw_cells_split2 _ (bv_unsigned a0 + 832) (bv_unsigned a0 + 838) [CB 6 (repeat zb 6)]
                scene_tail_cells P3 ltac:(cbn [cells_size csize Nat.add]; lia)) as [Hm HL3].
    clear P2 P3. unfold scene_tail_cells in HL3. norm_nat_lits.
    do 10 zstep.
    if_cases T1; [exfalso; zify_cond T1; lia|].
    do 9 zstep.
    if_cases T2; [exfalso; zify_cond T2; lia|].
    do 9 zstep.
    if_cases T3; [exfalso; zify_cond T3; lia|].
    do 4 zstep.
    assert (UD832 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 832)) = bv_unsigned a0 + 832)
      by (apply unsigned_lit; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    call MEMC.
    { exact HM. }
    { rewrite HL. reflexivity. }
    { rewrite UD832, U6. exact Hm. }
    { rewrite UD832, U6. lia. }
    { exact MI. }
    do 5 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: try reflexivity.
    match goal with
    | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 832))) _ |- _ =>
        rewrite UD832, U6 in P; change (Z.to_nat 6) with 6%nat in P;
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 838) _ _ P ltac:(cbn [cells_size csize Nat.add]; lia) HL3) as J1;
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 832) _ _ HL1 ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2;
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 4) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3
    end.
    eapply rw_cells_rebytes; [exact J3 | |].
    { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene0. rewrite !length_app, HL. reflexivity. }
    { cbn [cells_bytes cbytes app]. rewrite !app_nil_r. unfold scene0. cbn [app]. reflexivity. }
  - clear HOK. pose proof (scene_ok_false _ _ _ EOK) as O.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU0.
    carve_frame 32%nat ST.
    do 7 zstep.
    if_cases K1; zify_cond K1.
    + refuse_path FR ST sp.
    + do 4 zstep. if_cases K2; zify_cond K2.
      * refuse_path FR ST sp.
      * zstep. if_cases K3; zify_cond K3.
        -- refuse_path FR ST sp.
        -- exfalso; lia.
Qed.
