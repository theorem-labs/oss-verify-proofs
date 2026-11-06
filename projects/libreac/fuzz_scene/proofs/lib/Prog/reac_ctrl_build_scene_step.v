(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 301 of its 321 lines of code are new or changed and 125 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct reac_ctrl_build_scene_step_c memset_c memcpy_c.
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

Ltac loop_turn := zstep; zstep; zstep; zstep; let K := fresh "K" in if_cases K; [clear K | zify_cond K; exfalso; lia].
Ltac loop_last := zstep; zstep; zstep; zstep; let K := fresh "K" in if_cases K; [zify_cond K; exfalso; lia | clear K].

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

Lemma cks_eq : forall S T, S = T ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - S mod 18446744073709551616)))) =
  Z_to_bv 8 ((256 - T mod 256) mod 256).
Proof.
  intros S T ->. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cksum_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32 z : byte) (Q : machine_state -> Prop),
  bv_unsigned s0 + 34 <= 2^64 ->
  s1 = Z_to_bv 64 (bv_unsigned s0 + 2) ->
  rw_cells rsegs m (bv_unsigned s0) [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15; C1 y16; C1 y17; C1 y18; C1 y19; C1 y20; C1 y21; C1 y22; C1 y23; C1 y24; C1 y25; C1 y26; C1 y27; C1 y28; C1 y29; C1 y30; C1 y31; C1 y32; C1 z] ->
  mem_inv rsegs m ->
  (forall (a1' a2' s1' : word) (m' : word -> option byte),
     rw_cells rsegs m' (bv_unsigned s0)
       [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15; C1 y16; C1 y17; C1 y18; C1 y19; C1 y20; C1 y21; C1 y22; C1 y23; C1 y24; C1 y25; C1 y26; C1 y27; C1 y28; C1 y29; C1 y30; C1 y31; C1 y32; C1 (Z_to_bv 8 ((256 - byte_sum [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] mod 256) mod 256))] ->
     munch [(bv_unsigned s0 + 33, bv_unsigned s0 + 34)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1' (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15730) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1570c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32 z Q HB HS1 HC HMI CONT.
  subst s1.
  pose proof (munch_refl [(bv_unsigned s0 + 33, bv_unsigned s0 + 34)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s0) as Rs0.
  zstep. zstep.
  do 30 loop_turn.
  loop_last.
  zstep. zstep. zstep.
  match type of HC with
  | context [bv_swrap 32 (0 - ?S mod 18446744073709551616)] =>
      assert (ES : S = byte_sum [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) by (cbn [byte_sum fold_right]; lia);
      rewrite (cks_eq S _ ES) in HC
  end.
  eapply CONT; [exact HC | exact MU | exact WM | exact HMI].
Qed.

Ltac join_tail FR ST sp :=
  intros ? ? ? ?m' ?J' ?MU' ?WM' ?MI';
  lazymatch goal with
  | MU' : munch _ ?mo ?mn, WM' : wmono _ ?mo ?mn |- _ => transport_after_call rsegs mo mn MU' WM'
  end;
  do 7 zstep;
  release_frame FR ST (bv_unsigned sp);
  zstep;
  finish;
  try reflexivity.

Ltac refuse_path FR ST sp :=
  do 7 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish; repeat (first [reflexivity | assumption | split]).

Theorem reac_ctrl_build_scene_step_holds : memset_contract -> memcpy_contract -> reac_ctrl_build_scene_step_contract.
Proof.
  intros MEMS MEMC. unfold reac_ctrl_build_scene_step_contract, REAC_CTRL_BUILD_SCENE_STEP, REAC_CTRL_BUILD_SCENE_STEP_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo bj b HMI ST LO HOK.
  norm_nat_lits.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 34)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (scene_step_ok a0 a1 a2 a3) eqn:EOK.
  - destruct (HOK eq_refl) as (HB & HBb & Hlb & D1 & D2 & D3 & D4). clear HOK.
    destruct (scene_step_ok_true _ _ _ _ EOK) as (O1 & O2 & O3 & O4).
    unfold TAIL_TRAILER_AT in D4.
    assert (HBd : bv_unsigned a0 + 34 <= 2^64)
      by (destruct (rw_cells_bound _ _ _ _ HB) as [_ X]; exact X).
    assert (Hbd : bv_unsigned a1 + 8904 <= 2^64)
      by (destruct (bytes_at_bound _ _ _ _ HBb) as [_ X]; rewrite Hlb in X; exact X).
    assert (HS : rw_cells rsegs m (bv_unsigned a0) ([CB 2 (firstn 2 bj)] ++ [CB 32 (skipn 2 bj)])).
    { eapply rw_cells_cb_split with (k := 0%nat) (n := 2%nat); [exact HB | reflexivity | reflexivity]. }
    clear HB.
    destruct (rw_cells_split2 m (bv_unsigned a0) (bv_unsigned a0 + 2) _ _ HS
                ltac:(cbn [cells_size csize Nat.add]; lia)) as [HA H2].
    clear HS.
    carve_frame 48%nat ST.
    do 10 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. zstep. zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    do 5 zstep.
    assert (UD2 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 2)) = bv_unsigned a0 + 2) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    call MEMS.
    { rewrite UD2, U32. exact H2. }
    { exact HMI. }
    match goal with
    | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 2))) _ |- _ =>
        rewrite UD2, U32 in P; rename P into HZ
    end.
    do 4 zstep.
    rewrite byte_ea in HA.
    zstep. if_cases K5; zify_cond K5.
    + apply (rw_cells_rebytes _ _ _ ([CB 5 (repeat zb 5)] ++ [CB 14 (repeat zb 14)] ++ [CB 12 (repeat zb 12)] ++ [CB 1 [zb]])) in HZ;
        [| cbn; repeat split | vm_compute; reflexivity].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 7) _ _ HZ
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 7) (bv_unsigned a0 + 21) _ _ HR
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H7 HR2].
      destruct (rw_cells_split2 _ (bv_unsigned a0 + 21) (bv_unsigned a0 + 33) _ _ HR2
                  ltac:(cbn [cells_size csize Nat.add]; lia)) as [H21 H33].
      clear HZ HR HR2.
      do 13 zstep.
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
      do 6 zstep.
      assert (UD21 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 21)) = bv_unsigned a0 + 21) by (apply unsigned_lit; lia).
      assert (U12 : bv_unsigned (Z_to_bv 64 12) = 12) by reflexivity.
      assert (UT : bv_unsigned (Z_to_bv 64 66466) = 66466) by reflexivity.
      match goal with HMI' : mem_inv rsegs ?mm |- _ =>
        assert (HT : bytes_at rsegs mm 66466 scene_trailer)
          by (destruct (ro_cells_image rsegs mm 66466 scene_trailer HMI' ltac:(vm_compute; reflexivity)
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
      pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) J3) as J4.
      apply rw_cells_C1 in J4. cbn [cells_bytes cbytes app map firstn skipn repeat] in J4.
      eapply cksum_tail; [exact HBd | reflexivity | exact J4 | assumption | ].
      join_tail FR ST sp.
      rewrite K5.
      match goal with J' : rw_cells rsegs ?mm (bv_unsigned a0) (C1 _ :: _) |- _ =>
        eapply rw_cells_rebytes; [exact J' | |] end.
      { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields. rewrite payload342, <- Epl. reflexivity. }
      { unfold scene_block, scene_fields. rewrite payload342, <- Epl. unfold scene_trailer.
        cbn [cells_bytes cbytes app map]. reflexivity. }
    + zstep. if_cases K6; zify_cond K6.
      * apply (rw_cells_rebytes _ _ _ ([CB 5 (repeat zb 5)] ++ [CB 26 (repeat zb 26)] ++ [CB 1 [zb]])) in HZ;
          [| cbn; repeat split | vm_compute; reflexivity].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 7) _ _ HZ
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 7) (bv_unsigned a0 + 33) _ _ HR
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H7 H33].
        clear HZ HR.
        do 12 zstep.
        assert (KK : 1 <= bv_unsigned a3 <= 341) by lia.
        assert (EW : bv_swrap 32 (bv_unsigned a3 + -1) = bv_unsigned a3 - 1) by (rewrite swrap_small by lia; lia).
        assert (UBm : bv_unsigned (Z_to_bv 64 (bv_unsigned a1 + bv_swrap 32 (bv_unsigned a3 + -1) mod 18446744073709551616 * 26 + 24))
                      = bv_unsigned a1 + Z.of_nat (Z.to_nat (24 + 26 * (bv_unsigned a3 - 1)))).
        { rewrite EW, (Z.mod_small (bv_unsigned a3 - 1)) by lia. rewrite Z2Nat.id by lia. rewrite unsigned_lit by lia. lia. }
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
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 7) _ _ H2a ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        apply rw_cells_C1 in J3. cbn [cells_bytes cbytes app map firstn skipn repeat] in J3.
        eapply cksum_tail; [exact HBd | reflexivity | exact J3 | assumption | ].
        join_tail FR ST sp.
        match goal with J' : rw_cells rsegs ?mm (bv_unsigned a0) (C1 _ :: _) |- _ =>
          eapply rw_cells_rebytes; [exact J' | |] end.
        { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields.
          rewrite (payloadK b _ K6 K5), <- Epl. reflexivity. }
        { unfold scene_block, scene_fields.
          rewrite (payloadK b _ K6 K5), (segK _ K6 K5), (lenK _ K6 K5), <- Epl.
          cbn [cells_bytes cbytes app]. reflexivity. }
      * apply (rw_cells_rebytes _ _ _ ([CB 7 (repeat zb 7)] ++ [CB 24 (repeat zb 24)] ++ [CB 1 [zb]])) in HZ;
          [| cbn; repeat split | vm_compute; reflexivity].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 2) (bv_unsigned a0 + 9) _ _ HZ
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H2a HR].
        destruct (rw_cells_split2 _ (bv_unsigned a0 + 9) (bv_unsigned a0 + 33) _ _ HR
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as [H9 H33].
        clear HZ HR.
        do 15 zstep.
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
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 9) _ _ H2a ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned a0 + 2) _ _ HA ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        apply rw_cells_C1 in J3. cbn [cells_bytes cbytes app map firstn skipn repeat] in J3.
        eapply cksum_tail; [exact HBd | reflexivity | exact J3 | assumption | ].
        join_tail FR ST sp.
        rewrite K6.
        match goal with J' : rw_cells rsegs ?mm (bv_unsigned a0) (C1 _ :: _) |- _ =>
          eapply rw_cells_rebytes; [exact J' | |] end.
        { cbn [cells_wf cell_wf]. split; [|exact I]. unfold scene_block, scene_fields. rewrite payload0, <- Epl. reflexivity. }
        { unfold scene_block, scene_fields. rewrite payload0, <- Epl. cbn [cells_bytes cbytes app]. reflexivity. }
  - clear HOK. pose proof (scene_step_ok_false _ _ _ _ EOK) as O.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU0.
    carve_frame 48%nat ST.
    do 10 zstep.
    if_cases K1; zify_cond K1; [refuse_path FR ST sp|].
    zstep. zstep. if_cases K2; zify_cond K2; [refuse_path FR ST sp|].
    zstep. zstep. zstep. if_cases K3; zify_cond K3; [refuse_path FR ST sp|].
    zstep. zstep. zstep. if_cases K4; zify_cond K4; [refuse_path FR ST sp|].
    exfalso; lia.
Qed.
