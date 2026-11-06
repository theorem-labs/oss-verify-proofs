(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 344 of its 365 lines of code are new or changed and 124 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Image ZBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcModel RcFin.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_scene_struct reac_ctrl_build_scene_step_c
  memset_c memcpy_c reac_ctrl_block_cksum_stamp_c.
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

Ltac refute T := exfalso; zify_cond T; repeat (rewrite Z.mod_small in T by lia); lia.

Ltac to_cb32 H H' :=
  lazymatch type of H with
  | rw_cells ?s ?mm ?A ?cs =>
      let bs := eval cbn [cells_bytes cbytes app map firstn skipn repeat] in (cells_bytes cs) in
      assert (H' : rw_cells s mm A [CB 32 bs])
        by (eapply rw_cells_rebytes; [exact H | cbn [cells_wf cell_wf]; split; [reflexivity | exact I] | reflexivity])
  end.

Lemma scene_step_ok_true : forall blk body n st, scene_step_ok blk body n st = true ->
  bv_unsigned blk <> 0 /\ bv_unsigned body <> 0 /\ bv_unsigned n = 8904 /\ bv_unsigned st <= 342.
Proof.
  intros blk body n st. unfold scene_step_ok.
  destruct (Z.eqb_spec (bv_unsigned blk) 0); destruct (Z.eqb_spec (bv_unsigned body) 0);
    destruct (Z.eqb_spec (bv_unsigned n) 8904); destruct (Z.leb_spec (bv_unsigned st) 342);
    cbn; intro HH; try discriminate; lia.
Qed.

Lemma scene_step_ok_false : forall blk body n st, scene_step_ok blk body n st = false ->
  bv_unsigned blk = 0 \/ bv_unsigned body = 0 \/ bv_unsigned n <> 8904 \/ 342 < bv_unsigned st.
Proof.
  intros blk body n st. unfold scene_step_ok.
  destruct (Z.eqb_spec (bv_unsigned blk) 0); destruct (Z.eqb_spec (bv_unsigned body) 0);
    destruct (Z.eqb_spec (bv_unsigned n) 8904); destruct (Z.leb_spec (bv_unsigned st) 342);
    cbn; intro HH; try discriminate; lia.
Qed.

Lemma swrap_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma byte_ea : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-22))) = Z_to_bv 8 234.
Proof. apply Z_to_bv8_mod. reflexivity. Qed.

Lemma payload0 : forall b, scene_payload b 0 = [Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b.
Proof. reflexivity. Qed.

Lemma payload342 : forall b, scene_payload b 342 = firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer.
Proof. reflexivity. Qed.

Lemma payloadK : forall b K, K <> 0 -> K <> 342 ->
  scene_payload b K = firstn 26 (skipn (Z.to_nat (24 + 26 * (K - 1))) b).
Proof.
  intros b K H0 H1. unfold scene_payload, scene_off.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma segK : forall K, K <> 0 -> K <> 342 -> scene_seg K = 0.
Proof. intros K H0 H1. unfold scene_seg. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma lenK : forall K, K <> 0 -> K <> 342 -> scene_len K = 26.
Proof. intros K H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma fold_sum_init : forall (l : list byte) (c : Z),
  fold_right (fun (x : byte) s => bv_unsigned x + s) c l = fold_right (fun (x : byte) s => bv_unsigned x + s) 0 l + c.
Proof. induction l as [|x l IH]; intros c; cbn; [lia | rewrite IH; lia]. Qed.

Lemma psum_app : forall l r, psum (l ++ r) (length l) = byte_sum l.
Proof.
  induction l as [|x l IH] using rev_ind; intros r; [reflexivity|].
  rewrite length_app. cbn [length]. rewrite Nat.add_1_r. cbn [psum].
  rewrite <- app_assoc. cbn [app]. rewrite IH, nth_middle.
  unfold byte_sum. rewrite fold_right_app. symmetry. rewrite fold_sum_init. cbn [fold_right]. lia.
Qed.

Lemma stamp32_last : forall bs, length bs = 32%nat ->
  stamp32 bs = firstn 31 bs ++ [Z_to_bv 8 ((256 - byte_sum (firstn 31 bs) mod 256) mod 256)].
Proof.
  intros bs H. unfold stamp32, upd_bytes.
  pose proof (psum_app (firstn 31 bs) (skipn 31 bs)) as P.
  rewrite firstn_skipn, length_firstn in P. replace (Nat.min 31 (length bs)) with 31%nat in P by lia.
  rewrite P. cbn [length]. rewrite (skipn_all2 bs) by lia. rewrite app_nil_r.
  f_equal. f_equal. apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

Ltac refuse_path FR ST sp :=
  do 5 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish; repeat (first [reflexivity | assumption | split]).

Theorem reac_ctrl_build_scene_step_holds :
  memset_contract -> memcpy_contract -> reac_ctrl_block_cksum_stamp_contract -> reac_ctrl_build_scene_step_contract.
Proof.
  intros MEMS MEMC STAMP.
  unfold reac_ctrl_build_scene_step_contract, REAC_CTRL_BUILD_SCENE_STEP, REAC_CTRL_BUILD_SCENE_STEP_FRAME.
  unfold reac_ctrl_block_cksum_stamp_contract, REAC_CTRL_BLOCK_CKSUM_STAMP in STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo bj b HMI ST LO HOK.
  norm_nat_lits.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  unfold bv_modulus in Rsp, Ra0, Ra1, Ra3.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 34)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (scene_step_ok a0 a1 a2 a3) eqn:EOK.
  - destruct (HOK eq_refl) as (HB & HBb & Hlb & D1 & D2 & D3 & D4). clear HOK.
    destruct (scene_step_ok_true _ _ _ _ EOK) as (O1 & O2 & O3 & O4).
    unfold TAIL_TRAILER_AT in D4.
    assert (HBd : bv_unsigned a0 + 34 <= 2^64)
      by (destruct (rw_cells_bound _ _ _ _ HB) as [_ X]; exact X).
    assert (Hbd : bv_unsigned a1 + 8904 <= 2^64)
      by (destruct (bytes_at_bound _ _ _ _ HBb) as [_ X]; rewrite Hlb in X; exact X).
    carve_frame 32%nat ST.
    do 8 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    do 2 zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    do 3 zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    do 3 zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    do 4 zstep.
    assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
    call MEMS.
    { rewrite U34. exact HB. }
    { exact HMI. }
    match goal with
    | P : rw_cells rsegs ?mm (bv_unsigned a0) [CB _ _] |- _ =>
        apply (rw_cells_rebytes _ _ _ ([CB 2 (repeat zb 2)] ++ [CB 32 (repeat zb 32)])) in P;
        [| cbn; repeat split | vm_compute; reflexivity];
        destruct (rw_cells_split2 _ (bv_unsigned a0) (bv_unsigned a0 + 2) _ _ P
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [HA HZ];
        clear P
    end.
    do 4 zstep. if_cases T0; [refute T0|].
    do 5 zstep.
    rewrite byte_ea in HA.
    if_cases K5; zify_cond K5.
    + apply (rw_cells_rebytes _ _ _ ([CB 5 (repeat zb 5)] ++ [CB 14 (repeat zb 14)] ++ [CB 12 (repeat zb 12)] ++ [CB 1 [zb]])) in HZ;
        [| cbn; repeat split | vm_compute; reflexivity].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 7) _ _ HZ
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 7) (bv_unsigned a0 + 21) _ _ HR
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H7 HR2].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 21) (bv_unsigned a0 + 33) _ _ HR2
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H21 H33].
      clear HZ HR HR2.
      zstep. if_cases T1; [refute T1|].
      do 4 zstep. if_cases T2; [refute T2|].
      do 5 zstep. if_cases T3; [refute T3|].
      do 4 zstep. if_cases T4; [refute T4|].
      do 3 zstep. if_cases T5; [refute T5|].
      do 7 zstep.
      assert (UD7 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7)) = bv_unsigned a0 + 7) by (apply unsigned_lit; lia).
      assert (U14 : bv_unsigned (Z_to_bv 64 14) = 14) by reflexivity.
      assert (UB : bv_unsigned (Z_to_bv 64 (bv_unsigned a1 + 8890)) = bv_unsigned a1 + 8890) by (apply unsigned_lit; lia).
      pose proof (bytes_at_slice _ _ _ (Z.to_nat 8890) 14 HBb ltac:(rewrite Hlb; apply Nat.leb_le; reflexivity)) as HS1.
      change (Z.of_nat (Z.to_nat 8890)) with 8890 in HS1.
      call MEMC.
      { rewrite UB. exact HS1. }
      { rewrite length_firstn, length_skipn, Hlb. reflexivity. }
      { rewrite UD7, U14. exact H7. }
      { rewrite UD7, U14, UB. lia. }
      { assumption. }
      match goal with
      | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7))) _ |- _ =>
          rewrite UD7, U14 in P; change (Z.to_nat 14) with 14%nat in P; rename P into H7'
      end.
      do 2 zstep. if_cases T6; [refute T6|].
      do 2 zstep. if_cases T7; [refute T7|].
      do 6 zstep.
      assert (UD21 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 21)) = bv_unsigned a0 + 21) by (apply unsigned_lit; lia).
      assert (U12 : bv_unsigned (Z_to_bv 64 12) = 12) by reflexivity.
      assert (UT : bv_unsigned (Z_to_bv 64 66516) = 66516) by reflexivity.
      match goal with HMI' : mem_inv rsegs ?mm |- _ =>
        assert (HT : bytes_at rsegs mm 66516 scene_trailer)
          by (destruct (ro_cells_image rsegs mm 66516 scene_trailer HMI' ltac:(vm_compute; reflexivity)
                          ltac:(lia) ltac:(cbn; lia)) as [_ X];
              cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X)
      end.
      call MEMC.
      { rewrite UT. exact HT. }
      { reflexivity. }
      { rewrite UD21, U12. exact H21. }
      { rewrite UD21, U12, UT. lia. }
      { assumption. }
      match goal with
      | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 21))) _ |- _ =>
          rewrite UD21, U12 in P; change (Z.to_nat 12) with 12%nat in P; unfold scene_trailer in P;
          cbn [map] in P; rename P into H21'
      end.
      remember (firstn 14 (skipn (Z.to_nat 8890) b)) as pl eqn:Epl in H7'.
      assert (Lpl : length pl = 14%nat) by (rewrite Epl, length_firstn, length_skipn, Hlb; reflexivity).
      do 14 (destruct pl as [|? pl]; [discriminate Lpl|]).
      destruct pl; [|discriminate Lpl].
      pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 33) _ _ H21' ltac:(cbn [cells_size csize Nat.add]; lia) H33) as J1.
      pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 21) _ _ H7' ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
      pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 7) _ _ H2a ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
      clear J1 J2 H21' H7' H2a H33.
      rewrite K5.
      to_cb32 J3 J32. clear J3.
      do 2 zstep. if_cases TS; [refute TS|].
      do 2 zstep.
      lazymatch goal with HM : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (KEEP : True /\ mem_inv rsegs mm) by (split; [exact I | exact HM])
      end.
      lazymatch type of J32 with
      | rw_cells _ _ _ [CB 32 ?BS] =>
          call (STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned a0 + 2) BS); [lia | lia | reflexivity | exact J32 | ]
      end.
      lazymatch goal with H : mem_inv rsegs ?mo -> mem_inv rsegs ?mn |- _ =>
        pose proof (H (proj2 KEEP)) as HMIf; clear H KEEP
      end.
      do 6 zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      finish.
      all: try reflexivity.
      lazymatch goal with HS : rw_cells rsegs ?mm (bv_unsigned a0 + 2) [CB 32 (stamp32 _)] |- _ =>
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) HS) as JF
      end.
      eapply rw_cells_rebytes; [exact JF | |].
      { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields. rewrite payload342, <- Epl. reflexivity. }
      { unfold scene_block, scene_fields. rewrite payload342, <- Epl. unfold scene_trailer. rewrite stamp32_last by reflexivity.
        cbn [cells_bytes cbytes app map firstn skipn repeat]. reflexivity. }
    + zstep. if_cases K6; zify_cond K6.
      * apply (rw_cells_rebytes _ _ _ ([CB 5 (repeat zb 5)] ++ [CB 26 (repeat zb 26)] ++ [CB 1 [zb]])) in HZ;
          [| cbn; repeat split | vm_compute; reflexivity].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 7) _ _ HZ
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 7) (bv_unsigned a0 + 33) _ _ HR
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H7 H33].
        clear HZ HR.
        assert (KK : 1 <= bv_unsigned a3 <= 341) by lia.
        assert (EW : bv_swrap 32 (bv_unsigned a3 + -1) = bv_unsigned a3 - 1) by (rewrite swrap_small by lia; lia).
        zstep. if_cases T1; [refute T1|].
        do 5 zstep. if_cases T2; [refute T2|].
        do 4 zstep. if_cases T3; [refute T3|].
        do 6 zstep.
        if_cases T4.
        { exfalso. zify_cond T4. rewrite zb_lxor_ones in T4 by lia. rewrite EW in T4. lia. }
        do 4 zstep.
        assert (UBm : bv_unsigned (Z_to_bv 64 (bv_unsigned a1 + (bv_swrap 32 (bv_unsigned a3 + -1) * 26 + 24)))
                      = bv_unsigned a1 + Z.of_nat (Z.to_nat (24 + 26 * (bv_unsigned a3 - 1)))).
        { rewrite EW, Z2Nat.id by lia. rewrite unsigned_lit by lia. lia. }
        assert (UD7 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7)) = bv_unsigned a0 + 7) by (apply unsigned_lit; lia).
        assert (U26 : bv_unsigned (Z_to_bv 64 26) = 26) by reflexivity.
        pose proof (bytes_at_slice _ _ _ (Z.to_nat (24 + 26 * (bv_unsigned a3 - 1))) 26 HBb
                      ltac:(rewrite Hlb; lia)) as HSm.
        call MEMC.
        { rewrite UBm. exact HSm. }
        { rewrite length_firstn, length_skipn, Hlb, U26. lia. }
        { rewrite UD7, U26. exact H7. }
        { rewrite UD7, U26, UBm, Z2Nat.id by lia. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7))) _ |- _ =>
            rewrite UD7, U26 in P; change (Z.to_nat 26) with 26%nat in P; rename P into H7'
        end.
        remember (firstn 26 (skipn (Z.to_nat (24 + 26 * (bv_unsigned a3 - 1))) b)) as pl eqn:Epl in H7'.
        assert (Lpl : length pl = 26%nat) by (rewrite Epl, length_firstn, length_skipn, Hlb; lia).
        do 26 (destruct pl as [|? pl]; [discriminate Lpl|]).
        destruct pl; [|discriminate Lpl].
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 33) _ _ H7' ltac:(cbn [cells_size csize Nat.add]; lia) H33) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 7) _ _ H2a ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J3.
        clear J1 H7' H2a H33.
        to_cb32 J3 J32. clear J3.
        do 2 zstep. if_cases TS; [refute TS|].
        do 2 zstep.
        lazymatch goal with HM : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (KEEP : True /\ mem_inv rsegs mm) by (split; [exact I | exact HM])
        end.
        lazymatch type of J32 with
        | rw_cells _ _ _ [CB 32 ?BS] =>
            call (STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned a0 + 2) BS); [lia | lia | reflexivity | exact J32 | ]
        end.
        lazymatch goal with H : mem_inv rsegs ?mo -> mem_inv rsegs ?mn |- _ =>
          pose proof (H (proj2 KEEP)) as HMIf; clear H KEEP
        end.
        do 6 zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.
        all: try reflexivity.
        lazymatch goal with HS : rw_cells rsegs ?mm (bv_unsigned a0 + 2) [CB 32 (stamp32 _)] |- _ =>
          pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) HS) as JF
        end.
        eapply rw_cells_rebytes; [exact JF | |].
        { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields. rewrite (payloadK b _ K6 K5), <- Epl. reflexivity. }
        { unfold scene_block, scene_fields. rewrite (payloadK b _ K6 K5), (segK _ K6 K5), (lenK _ K6 K5), <- Epl. rewrite stamp32_last by reflexivity.
          cbn [cells_bytes cbytes app map firstn skipn repeat]. reflexivity. }
      * apply (rw_cells_rebytes _ _ _ ([CB 7 (repeat zb 7)] ++ [CB 24 (repeat zb 24)] ++ [CB 1 [zb]])) in HZ;
          [| cbn; repeat split | vm_compute; reflexivity].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 9) _ _ HZ
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 9) (bv_unsigned a0 + 33) _ _ HR
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H9 H33].
        clear HZ HR.
        zstep. if_cases T1; [refute T1|].
        do 4 zstep. if_cases T2; [refute T2|].
        do 4 zstep. if_cases T3; [refute T3|].
        do 4 zstep. if_cases T4; [refute T4|].
        do 4 zstep. if_cases T5; [refute T5|].
        do 4 zstep. if_cases T6; [refute T6|].
        do 3 zstep. if_cases T7; [refute T7|].
        do 5 zstep.
        assert (UD9 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 9)) = bv_unsigned a0 + 9) by (apply unsigned_lit; lia).
        assert (U24 : bv_unsigned (Z_to_bv 64 24) = 24) by reflexivity.
        pose proof (bytes_at_slice _ _ _ 0 24 HBb ltac:(rewrite Hlb; apply Nat.leb_le; reflexivity)) as HS0.
        change (Z.of_nat 0) with 0 in HS0. rewrite Z.add_0_r in HS0. change (skipn 0 b) with b in HS0.
        call MEMC.
        { exact HS0. }
        { rewrite length_firstn, Hlb. reflexivity. }
        { rewrite UD9, U24. exact H9. }
        { rewrite UD9, U24. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 9))) _ |- _ =>
            rewrite UD9, U24 in P; change (Z.to_nat 24) with 24%nat in P; rename P into H9'
        end.
        remember (firstn 24 b) as pl eqn:Epl in H9'.
        assert (Lpl : length pl = 24%nat) by (rewrite Epl, length_firstn, Hlb; reflexivity).
        do 24 (destruct pl as [|? pl]; [discriminate Lpl|]).
        destruct pl; [|discriminate Lpl].
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 33) _ _ H9' ltac:(cbn [cells_size csize Nat.add]; lia) H33) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 9) _ _ H2a ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J3.
        clear J1 H9' H2a H33.
        rewrite K6.
        to_cb32 J3 J32. clear J3.
        do 2 zstep. if_cases TS; [refute TS|].
        do 2 zstep.
        lazymatch goal with HM : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (KEEP : True /\ mem_inv rsegs mm) by (split; [exact I | exact HM])
        end.
        lazymatch type of J32 with
        | rw_cells _ _ _ [CB 32 ?BS] =>
            call (STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned a0 + 2) BS); [lia | lia | reflexivity | exact J32 | ]
        end.
        lazymatch goal with H : mem_inv rsegs ?mo -> mem_inv rsegs ?mn |- _ =>
          pose proof (H (proj2 KEEP)) as HMIf; clear H KEEP
        end.
        do 6 zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.
        all: try reflexivity.
        lazymatch goal with HS : rw_cells rsegs ?mm (bv_unsigned a0 + 2) [CB 32 (stamp32 _)] |- _ =>
          pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) HS) as JF
        end.
        eapply rw_cells_rebytes; [exact JF | |].
        { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields. rewrite payload0, <- Epl. reflexivity. }
        { unfold scene_block, scene_fields. rewrite payload0, <- Epl. rewrite stamp32_last by reflexivity.
          cbn [cells_bytes cbytes app map firstn skipn repeat]. reflexivity. }
  - clear HOK. pose proof (scene_step_ok_false _ _ _ _ EOK) as O.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU0.
    carve_frame 32%nat ST.
    do 8 zstep.
    if_cases K1; zify_cond K1; [refuse_path FR ST sp|].
    do 2 zstep. if_cases K2; zify_cond K2; [refuse_path FR ST sp|].
    do 3 zstep. if_cases K3; zify_cond K3; [refuse_path FR ST sp|].
    do 3 zstep. if_cases K4; zify_cond K4; [refuse_path FR ST sp|].
    exfalso; lia.
Qed.
