From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_scene_struct reac_ctrl_scene_set_mac_c memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.

Ltac ok_tac :=
  unfold scene_ok, REAC_SCENE_BYTES;
  repeat match goal with
  | H : bv_unsigned ?x <> ?c |- context [bv_unsigned ?x =? ?c] => rewrite (proj2 (Z.eqb_neq _ _) H)
  | H : bv_unsigned ?x = ?c |- context [bv_unsigned ?x =? ?c] => rewrite (proj2 (Z.eqb_eq _ _) H)
  end;
  cbn [andb negb]; reflexivity.

Ltac refuse_tac :=
  finish;
  lazymatch goal with
  | |- context [scene_ok ?x ?y ?z] =>
      let E := fresh "E" in
      assert (E : scene_ok x y z = false) by ok_tac; rewrite E; split; reflexivity
  end.

Theorem reac_ctrl_scene_set_mac_holds : memcpy_contract -> reac_ctrl_scene_set_mac_contract.
Proof.
  intros MEMC. unfold reac_ctrl_scene_set_mac_contract, REAC_CTRL_SCENE_SET_MAC, REAC_CTRL_SCENE_SET_MAC_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo bs macb HMI ST LO HOK.
  norm_nat_lits.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0 + 832, bv_unsigned a0 + 838)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  zstep. zstep. zstep. zstep. zstep.
  if_cases K1.
  - zify_cond K1. zstep. zstep. refuse_tac.
  - zify_cond K1. zstep.
    if_cases K2.
    + zify_cond K2. zstep. zstep. refuse_tac.
    + zify_cond K2. zstep.
      if_cases K3.
      * zify_cond K3. zstep. zstep. refuse_tac.
      * zify_cond K3.
        assert (EOK : scene_ok a0 a1 a2 = true) by ok_tac.
        destruct (HOK EOK) as (HB & HM & HL & D1 & D2 & D3).
        assert (HBd : bv_unsigned a0 + 8904 <= 2^64)
          by (destruct (rw_cells_bound _ _ _ _ HB) as [_ X]; exact X).
        assert (Hlen : length bs = 8904%nat) by (destruct HB as [[[Wl _] _] _]; exact Wl).
        assert (HS : rw_cells rsegs m (bv_unsigned a0)
                       ([CB 832 (firstn 832 bs)] ++ [CB 6 (firstn 6 (skipn 832 bs))] ++ [CB 8066 (skipn 838 bs)])).
        { eapply rw_cells_cb_split with (k := 832%nat) (n := 6%nat); [exact HB | reflexivity | reflexivity]. }
        clear HB. norm_nat_lits.
        destruct (rw_cells_split2 m (bv_unsigned a0) (bv_unsigned a0 + 832) _ _ HS
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H1 HR].
        destruct (rw_cells_split2 m (bv_unsigned a0 + 832) (bv_unsigned a0 + 838) _ _ HR
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2 H3].
        clear HS HR.
        zstep. zstep.
        if_cases T1; [exfalso; zify_cond T1; lia |].
        carve_frame 16%nat ST.
        zstep. zstep. zstep. zstep. zstep. zstep.
        assert (UD : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 832)) = bv_unsigned a0 + 832)
          by (apply unsigned_lit; lia).
        assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
        call MEMC.
        { exact HM. }
        { rewrite HL. reflexivity. }
        { rewrite UD, U6. exact H2. }
        { rewrite UD, U6. lia. }
        { exact HMI. }
        zstep. zstep. zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep. zstep.
        finish.
        rewrite EOK. split; [reflexivity|].
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 832))) _ |- _ =>
            rewrite UD, U6 in P;
            pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 838) _ _ P ltac:(cbn [cells_size csize Nat.add]; lia) H3) as P2;
            pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 832) _ _ H1 ltac:(cbn [cells_size csize Nat.add]; lia) P2) as P3
        end.
        eapply rw_cells_rebytes; [exact P3 | |].
        { cbn [cells_wf cell_wf]. split; [|exact I].
          rewrite !length_app, length_firstn, length_skipn, HL, Hlen. reflexivity. }
        { cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity. }
Qed.
