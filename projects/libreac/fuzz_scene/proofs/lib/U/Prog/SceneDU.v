(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtRepP/W_err_clear_error.v, with its module paths and module names changed; 383 of its 405 lines of code are new or changed and 724 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_scene_struct SceneTacU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import memcpy_c memset_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_ctrl_scene_set_mac_c reac_ctrl_scene_build_c.
Import ListNotations.
Open Scope Z_scope.

Definition QD (sp gp tp body before : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo S nb : Z) (sv : list byte) (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16928) fc None m' (seg_rom rsegs) /\
    x1 = Z_to_bv 64 0x15450 /\ x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = body /\ x10 = before /\
    munch [(S - 9104, S); (bv_unsigned body, bv_unsigned body + nb); (bv_unsigned before, bv_unsigned before + nb)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S /\ bytes_at rsegs m' (S - 104) sv.

Lemma sd_mcm_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma sd_bytes_take : forall m A l k, bytes_at rsegs m A l -> bytes_at rsegs m A (firstn k l).
Proof.
  intros m A l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma sd_bytes_drop : forall m A l k, bytes_at rsegs m A l -> (k <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (skipn k l).
Proof.
  intros m A l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H.
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact (proj2 H).
Qed.

Lemma sd_cb_bytes : forall m A n l, rw_cells rsegs m A [CB n l] -> bytes_at rsegs m A l.
Proof. intros m A n l [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma sd_cb_len : forall m A n l, rw_cells rsegs m A [CB n l] -> length l = n.
Proof. intros m A n l [[H _] _]. cbn in H. tauto. Qed.

Lemma sd_cb_cut : forall m A N l k, rw_cells rsegs m A [CB N l] -> (k <= N)%nat ->
  rw_cells rsegs m A [CB k (firstn k l)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (N - k) (skipn k l)].
Proof.
  intros m A N l k H Hk. pose proof (sd_cb_len _ _ _ _ H) as L.
  apply (rw_cells_rebytes m A _ [CB k (firstn k l); CB (N - k) (skipn k l)]) in H.
  - apply (rw_cells_split2 m A (A + Z.of_nat k) [CB k (firstn k l)] [CB (N - k) (skipn k l)]) in H; [exact H|].
    cbn [cells_size csize]. lia.
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. split; [lia|split; [lia|exact I]].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma sd_carve_at : forall m lo A hi (k : Z), stk rsegs m lo hi -> A = hi - k -> 0 <= k -> lo <= A ->
  stk rsegs m lo A /\ exists junk, rw_cells rsegs m A [CB (Z.to_nat k) junk].
Proof.
  intros m lo A hi k ST -> Hk Hlo.
  destruct (stk_carve rsegs m lo hi (Z.to_nat k) ST ltac:(lia)) as [S1 [j FR]].
  rewrite Z2Nat.id in S1, FR by lia. split; [exact S1 | exists j; exact FR].
Qed.

Lemma sd_lxor_ne : forall n, 0 <= n -> n <> 8904 -> (Z.lxor n 8904 <? 1) = false.
Proof.
  intros n Hn Hne. apply Z.ltb_ge.
  assert (0 <= Z.lxor n 8904) by (apply (proj2 (Z.lxor_nonneg n 8904)); split; intros; lia).
  assert (Z.lxor n 8904 <> 0) by (intro E; apply Z.lxor_eq in E; lia).
  lia.
Qed.

Lemma sd_ok_intro : forall b n mac, bv_unsigned n = 8904 -> bv_unsigned b <> 0 -> bv_unsigned mac <> 0 ->
  scene_ok b n mac = true.
Proof.
  intros b n mac H1 H2 H3. unfold scene_ok, REAC_SCENE_BYTES. rewrite H1.
  rewrite (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.

Lemma sd_ok_elim : forall b n mac, bv_unsigned n <> 8904 -> scene_ok b n mac = false.
Proof. intros b n mac H. unfold scene_ok, REAC_SCENE_BYTES. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Definition sd_exp_head_cells : list cell :=
  [CB 34 (repeat zb 34); CB 4 (repeat zb 4); CB 16 (repeat zb 16); CB 4 (repeat zb 4)].

Definition sd_exp_mid_cells : list cell :=
  [CB 828 (repeat zb 828); CB 6 (repeat zb 6)] ++ sd_exp_head_cells ++ [CB 8008 (repeat zb 8008)].

Lemma sd_exp_mid_bytes : cells_bytes sd_exp_mid_cells = repeat zb 8900.
Proof. vm_compute. reflexivity. Qed.

Lemma sd_exp_mid_wf : cells_wf sd_exp_mid_cells.
Proof. vm_compute. repeat split. Qed.

Ltac sd_bytes_eq :=
  unfold le4; cbn [Z_to_le_bytes];
  repeat match goal with
  | |- Z_to_bv 8 _ :: _ = Z_to_bv 8 _ :: _ =>
      apply (f_equal2 (@cons byte)); [apply Z_to_bv8_mod; reflexivity | ]
  end;
  reflexivity.

Lemma sd_le4_a : le4 (Z_to_bv 64 875770417) = [Z_to_bv 8 0x31; Z_to_bv 8 0x32; Z_to_bv 8 0x33; Z_to_bv 8 0x34].
Proof. sd_bytes_eq. Qed.
Lemma sd_le4_b : le4 (Z_to_bv 64 1347639635) = [Z_to_bv 8 0x53; Z_to_bv 8 0x59; Z_to_bv 8 0x53; Z_to_bv 8 0x50].
Proof. sd_bytes_eq. Qed.
Lemma sd_le4_c : le4 (Z_to_bv 64 1313162067) = [Z_to_bv 8 0x53; Z_to_bv 8 0x43; Z_to_bv 8 0x45; Z_to_bv 8 0x4e].
Proof. sd_bytes_eq. Qed.

Lemma sd_exp_bytes : forall macb : list byte,
  le4 (Z_to_bv 64 875770417) ++ repeat zb 828 ++ macb ++ repeat zb 34 ++ le4 (Z_to_bv 64 1347639635) ++
  repeat zb 16 ++ le4 (Z_to_bv 64 1313162067) ++ repeat zb 8008 = scene0 macb.
Proof. intros macb. rewrite sd_le4_a, sd_le4_b, sd_le4_c. unfold scene0. reflexivity. Qed.

Lemma sd_scene0_len : forall macb : list byte, length macb = 6%nat -> length (scene0 macb) = Z.to_nat 8904.
Proof. intros macb H. unfold scene0. rewrite !length_app, !repeat_length, H. reflexivity. Qed.

Ltac sd_closed_vm := lazymatch goal with |- ?G => sclosed G end; vm_compute; reflexivity.

Ltac sd_zn_lits H :=
  repeat match type of H with
  | context [Nat.of_num_uint ?u] =>
      let z := eval vm_compute in (Z.of_nat (Nat.of_num_uint u)) in
      change (Nat.of_num_uint u) with (Z.to_nat z) in H
  end.

Ltac sd_rel FR ST hi :=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  lazymatch type of ST with
  | stk _ _ _ (?A + Z.of_nat (cells_size ?cs)) =>
      let k := eval cbv [cells_size csize] in (cells_size cs) in
      sclosed k;
      let z := eval vm_compute in (Z.of_nat k) in
      change (Z.of_nat (cells_size cs)) with z in ST;
      replace (A + z) with hi in ST by lia
  end.

Ltac sd_postc :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?mo ?mn =>
      transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
      try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac sd_fix_ret :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac sd_ok_true H :=
  match type of H with context [scene_ok ?x ?y ?z] =>
    let EOK := fresh "EOK" in
    assert (EOK : scene_ok x y z = true) by (apply sd_ok_intro; lia);
    rewrite EOK in H; cbv iota in H; clear EOK
  end.

Lemma sd_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma scene_D_x : forall (ra sp gp tp t0 t1 t2 s0 body before a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                          (lo S n nb : Z) (bb jb macb sv : list byte),
  memcpy_contract -> memset_contract -> bcmp_contract ->
  reac_ctrl_scene_set_mac_contract -> reac_ctrl_scene_build_contract ->
  bv_unsigned sp = S - 9072 -> stk rsegs m lo S -> lo + 9104 <= S ->
  bv_unsigned before <> 0 -> bv_unsigned body <> 0 ->
  bv_unsigned s0 = n -> 0 <= n < 65536 -> nb = (if n =? 0 then 1 else n) ->
  mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned body) [CB (Z.to_nat nb) bb] ->
  rw_cells rsegs m (bv_unsigned before) [CB (Z.to_nat nb) jb] ->
  bytes_at rsegs m (S - 110) macb -> length macb = 6%nat ->
  bytes_at rsegs m (S - 104) sv -> length sv = 104%nat ->
  (bv_unsigned body + nb <= bv_unsigned before \/ bv_unsigned before + nb <= bv_unsigned body) ->
  (bv_unsigned body + nb <= lo \/ S <= bv_unsigned body) ->
  (bv_unsigned before + nb <= lo \/ S <= bv_unsigned before) ->
  evt rsegs (QD sp gp tp body before F fc m lo S nb sv)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 body before a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 body before a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo S n nb bb jb macb sv MEMC MEMS BCMPc SETMAC SBUILD HSP ST LO HBF HBD HS0 Hn Hnb HMI HBB HJB
         HMAC LMAC HSV LSV D1 D2 D3.
  unfold reac_ctrl_scene_set_mac_contract, REAC_CTRL_SCENE_SET_MAC, REAC_CTRL_SCENE_SET_MAC_FRAME in SETMAC.
  unfold reac_ctrl_scene_build_contract, REAC_CTRL_SCENE_BUILD, REAC_CTRL_SCENE_BUILD_FRAME in SBUILD.
  assert (ES : S = bv_unsigned sp + 9072) by lia. subst S.
  assert (E0 : s0 = Z_to_bv 64 n) by (apply bv_eq; rewrite HS0, unsigned_lit by lia; reflexivity). subst s0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 body) as Rbo.
  pose proof (bv_unsigned_in_range 64 before) as Rbe. unfold bv_modulus in Rsp, Rbo, Rbe.
  replace (bv_unsigned sp + 9072 - 110) with (bv_unsigned sp + 8962) in HMAC by lia.
  replace (bv_unsigned sp + 9072 - 104) with (bv_unsigned sp + 8968) in HSV by lia.
  pose proof (munch_refl [(bv_unsigned sp + 9072 - 9104, bv_unsigned sp + 9072);
                          (bv_unsigned body, bv_unsigned body + nb); (bv_unsigned before, bv_unsigned before + nb)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof ST as (Lo0 & Hi64 & _).
  assert (U8962 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 8962)) = bv_unsigned sp + 8962) by (apply unsigned_lit; lia).
  pose proof (sd_cb_len _ _ _ _ HBB) as LBB.
  destruct (Z.eq_dec n 8904) as [EN|EN].
  - subst n. cbn in Hnb. subst nb.
    assert (U8904 : bv_unsigned (Z_to_bv 64 8904) = 8904) by reflexivity.
    pose proof (rw_cells_bound _ _ _ _ HBB) as BDb. pose proof (rw_cells_bound _ _ _ _ HJB) as BDe.
    cbn [cells_size csize] in BDb, BDe.
    destruct (stk_split rsegs m lo (bv_unsigned sp + 8928) (bv_unsigned sp + 9072) ST ltac:(lia)) as [ST1 STt].
    clear ST.
    destruct (sd_carve_at m lo (bv_unsigned sp + 28) (bv_unsigned sp + 8928) 8900 ST1 ltac:(lia) ltac:(lia) ltac:(lia))
      as [ST2 [jz FRz]].
    clear ST1.
    destruct (sd_carve_at m lo (bv_unsigned sp + 24) (bv_unsigned sp + 28) 4 ST2 ltac:(lia) ltac:(lia) ltac:(lia))
      as [ST3 [jh FRh]].
    clear ST2. change (Z.to_nat 4) with 4%nat in FRh.
    destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + 24) ST3 ltac:(lia)) as [STa STb].
    clear ST3.
    zstep. sres_if.
    zr_until 0x1d8d8.
    eapply evt_cut; [eapply MEMC | ].
    { exact (sd_cb_bytes _ _ _ _ HBB). }
    { rewrite LBB, U8904. reflexivity. }
    { rewrite U8904. exact HJB. }
    { rewrite U8904. lia. }
    { assumption. }
    sd_postc.
    rename PC into HJB2. clear POST.
    zr_until 0x159e4.
    eapply evt_cut; [eapply SETMAC | ].
    { assumption. }
    { exact STa. }
    { lia. }
    { intros _. rewrite U8962. split; [exact HBB|]. split; [exact HMAC|]. split; [exact LMAC|].
      split; [lia|]. split; lia. }
    sd_postc.
    rename PC into STa2.
    sd_ok_true POST.
    destruct POST as [A0 HB2].
    match type of A0 with ?a = _ => subst a end.
    sd_zn_lits HB2.
    zr_until 0x1d8a4.
    pose proof (sd_cb_bytes _ _ _ _ HB2) as B2.
    assert (L832 : length (firstn 832 bb) = 832%nat) by (rewrite length_firstn, LBB; reflexivity).
    apply bytes_at_app in B2. destruct B2 as [B2a B2r]. apply bytes_at_app in B2r. destruct B2r as [B2m B2t].
    rewrite L832 in B2m, B2t. rewrite LMAC in B2t.
    change (Z.of_nat 832) with 832 in B2m, B2t. change (Z.of_nat 6) with 6 in B2t.
    replace (bv_unsigned body + 832 + 6) with (bv_unsigned body + 838) in B2t by lia.
    assert (UB832 : bv_unsigned (Z_to_bv 64 (bv_unsigned body + 832)) = bv_unsigned body + 832)
      by (apply unsigned_lit; lia).
    eapply evt_cut; [eapply BCMPc | ].
    { rewrite UB832. exact B2m. }
    { rewrite U8962. exact HMAC. }
    { apply sd_mcm_refl. rewrite LMAC. apply Nat.leb_le. reflexivity. }
    { assumption. }
    sd_postc. clear PC POST.
    zr_until 0x1d8a4.
    eapply evt_cut; [eapply BCMPc | ].
    { exact B2a. }
    { exact (sd_bytes_take _ _ _ 832 (sd_cb_bytes _ _ _ _ HJB2)). }
    { apply sd_mcm_refl. rewrite L832. apply Nat.leb_le. reflexivity. }
    { assumption. }
    sd_postc. clear PC POST.
    zr_until 0x1d8a4.
    assert (UB838 : bv_unsigned (Z_to_bv 64 (bv_unsigned body + 838)) = bv_unsigned body + 838)
      by (apply unsigned_lit; lia).
    assert (UE838 : bv_unsigned (Z_to_bv 64 (bv_unsigned before + 838)) = bv_unsigned before + 838)
      by (apply unsigned_lit; lia).
    pose proof (sd_bytes_drop _ _ _ 838 (sd_cb_bytes _ _ _ _ HJB2)
                  ltac:(rewrite LBB; apply Nat.leb_le; reflexivity)) as BE838.
    change (Z.of_nat 838) with 838 in BE838.
    eapply evt_cut; [eapply BCMPc | ].
    { rewrite UB838. exact B2t. }
    { rewrite UE838. exact BE838. }
    { apply sd_mcm_refl. rewrite length_skipn, LBB. apply Nat.leb_le. reflexivity. }
    { assumption. }
    sd_postc. clear PC POST.
    zr_until 0x15a38.
    eapply evt_cut; [eapply SBUILD | ].
    { assumption. }
    { exact STa2. }
    { lia. }
    { intros _. rewrite U8962. split; [exact HB2|]. split; [exact HMAC|]. split; [exact LMAC|].
      split; [lia|]. split; lia. }
    sd_postc.
    rename PC into STa3.
    sd_ok_true POST.
    destruct POST as [A0 HB3].
    match type of A0 with ?a = _ => subst a end.
    sd_zn_lits HB3.
    zr_until 0x1dcdc.
    assert (U28 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 28)) = bv_unsigned sp + 28) by (apply unsigned_lit; lia).
    assert (U8900 : bv_unsigned (Z_to_bv 64 8900) = 8900) by reflexivity.
    eapply evt_cut; [eapply MEMS | ].
    { rewrite U28, U8900. exact FRz. }
    { assumption. }
    sd_postc.
    rewrite U28 in POST.
    match type of POST with rw_cells _ ?mm _ _ =>
      assert (P2 : rw_cells rsegs mm (bv_unsigned sp + 28) sd_exp_mid_cells)
        by (eapply rw_cells_rebytes; [exact POST | exact sd_exp_mid_wf | rewrite sd_exp_mid_bytes; sd_closed_vm])
    end.
    clear POST.
    destruct (rw_cells_split2 _ (bv_unsigned sp + 28) (bv_unsigned sp + 856) [CB 828 (repeat zb 828)]
                ([CB 6 (repeat zb 6)] ++ sd_exp_head_cells ++ [CB 8008 (repeat zb 8008)]) P2
                ltac:(simpl_sizes; lia)) as [HZ1 P3].
    destruct (rw_cells_split2 _ (bv_unsigned sp + 856) (bv_unsigned sp + 862) [CB 6 (repeat zb 6)]
                (sd_exp_head_cells ++ [CB 8008 (repeat zb 8008)]) P3 ltac:(simpl_sizes; lia)) as [HZ2 P4].
    destruct (rw_cells_split2 _ (bv_unsigned sp + 862) (bv_unsigned sp + 920) sd_exp_head_cells
                [CB 8008 (repeat zb 8008)] P4 ltac:(unfold sd_exp_head_cells; simpl_sizes; lia)) as [HZ3 HZ4].
    clear P2 P3 P4. unfold sd_exp_head_cells in HZ3. sd_zn_lits HZ4.
    zr_until 0x1d8d8.
    assert (U856 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 856)) = bv_unsigned sp + 856)
      by (apply unsigned_lit; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    eapply evt_cut; [eapply MEMC | ].
    { rewrite U8962. exact HMAC. }
    { rewrite LMAC, U6. reflexivity. }
    { rewrite U856, U6. exact HZ2. }
    { rewrite U856, U8962, U6. lia. }
    { assumption. }
    sd_postc.
    rename PC into HZ2m. clear POST.
    rewrite U856, U6 in HZ2m. change (Z.to_nat 6) with 6%nat in HZ2m.
    zr_until 0x1d8a4.
    pose proof (rw_cells_join2 _ (bv_unsigned sp + 862) (bv_unsigned sp + 920) _ _ HZ3 ltac:(simpl_sizes; lia) HZ4)
      as J1.
    pose proof (rw_cells_join2 _ (bv_unsigned sp + 856) (bv_unsigned sp + 862) _ _ HZ2m ltac:(simpl_sizes; lia) J1)
      as J2.
    pose proof (rw_cells_join2 _ (bv_unsigned sp + 28) (bv_unsigned sp + 856) _ _ HZ1 ltac:(simpl_sizes; lia) J2)
      as J3.
    pose proof (rw_cells_join2 _ (bv_unsigned sp + 24) (bv_unsigned sp + 28) _ _ FRh ltac:(simpl_sizes; lia) J3)
      as J4.
    pose proof (sd_cells_bytes _ _ _ J4) as BJ. clear J1 J2 J3 J4.
    cbn [cells_bytes cbytes app] in BJ. rewrite app_nil_r in BJ.
    match type of BJ with bytes_at _ ?mm _ _ =>
      assert (BJ' : bytes_at rsegs mm (bv_unsigned sp + 24) (scene0 macb)) by (rewrite <- sd_exp_bytes; exact BJ)
    end.
    clear BJ.
    assert (U24 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 24)) = bv_unsigned sp + 24) by (apply unsigned_lit; lia).
    eapply evt_cut; [eapply BCMPc | ].
    { exact (sd_cb_bytes _ _ _ _ HB3). }
    { rewrite U24. exact BJ'. }
    { apply sd_mcm_refl. rewrite (sd_scene0_len macb LMAC). apply Nat.leb_le. reflexivity. }
    { assumption. }
    sd_postc. clear PC POST.
    zr_until 0x16928.
    sd_rel FRh STb (bv_unsigned sp + 28).
    sd_rel HZ1 STb (bv_unsigned sp + 856).
    sd_rel HZ2m STb (bv_unsigned sp + 862).
    sd_rel HZ3 STb (bv_unsigned sp + 920).
    sd_rel HZ4 STb (bv_unsigned sp + 8928).
    pose proof (stk_merge rsegs _ _ _ _ STb STt ltac:(lia)) as STc.
    pose proof (stk_merge rsegs _ lo (bv_unsigned sp) _ STa3 STc ltac:(lia)) as STF.
    replace (bv_unsigned sp + 8968) with (bv_unsigned sp + 9072 - 104) in HSV by lia.
    unfold QD. finish.
    all: try reflexivity.
  - assert (LX : (Z.lxor n 8904 <? 1) = false) by (apply sd_lxor_ne; lia).
    assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    assert (NB : n <= nb /\ 1 <= nb /\ nb < 65536) by (subst nb; destruct (Z.eqb_spec n 0); lia).
    pose proof (sd_cb_bytes _ _ _ _ HBB) as BB.
    assert (LF : length (firstn (Z.to_nat n) bb) = Z.to_nat n) by (rewrite length_firstn; lia).
    destruct (sd_cb_cut m (bv_unsigned before) (Z.to_nat nb) jb (Z.to_nat n) HJB ltac:(lia)) as [HJ1 _].
    clear HJB HBB.
    destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + 9072) ST ltac:(lia)) as [STa STb].
    clear ST.
    zstep. sres_if.
    zr_until 0x1d8d8.
    rewrite LX.
    eapply evt_cut; [eapply MEMC | ].
    { exact (sd_bytes_take _ _ _ (Z.to_nat n) BB). }
    { rewrite Un, length_firstn. lia. }
    { rewrite Un. exact HJ1. }
    { rewrite Un. lia. }
    { exact HMI. }
    sd_postc.
    rename PC into HJ1m. rename POST into BBn.
    zr_until 0x159e4.
    eapply evt_cut; [eapply SETMAC with (bs := @nil byte) (macb := @nil byte) | ].
    { assumption. }
    { exact STa. }
    { lia. }
    { intros K. exfalso. apply scene_ok_true in K. rewrite Un in K. lia. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc [STc PO]]]]]. subst ms'.
    rewrite sd_ok_elim in PO by (rewrite Un; exact EN). cbv iota in PO.
    destruct PO as [A0 EM].
    match type of EM with ?a = _ => subst a end.
    match type of A0 with ?a = _ => subst a end.
    clear MUc WMc MIc STc.
    sd_fix_ret.
    zr_until 0x1d8a4.
    eapply evt_cut; [eapply BCMPc | ].
    { exact BBn. }
    { exact (sd_cb_bytes _ _ _ _ HJ1m). }
    { apply sd_mcm_refl. rewrite Un, length_firstn. lia. }
    { assumption. }
    sd_postc.
    zr_until 0x15a38.
    eapply evt_cut; [eapply SBUILD with (junk := @nil byte) (macb := @nil byte) | ].
    { assumption. }
    { exact STa. }
    { lia. }
    { intros K. exfalso. apply scene_ok_true in K. rewrite Un in K. lia. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc [STc PO]]]]]. subst ms'.
    rewrite sd_ok_elim in PO by (rewrite Un; exact EN). cbv iota in PO.
    destruct PO as [A0 MU2].
    match type of A0 with ?a = _ => subst a end.
    clear MUc.
    lazymatch type of MU2 with munch _ ?mo ?mn =>
      transport_after_call rsegs mo mn MU2 WMc; clear MU2 WMc;
      try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
    end.
    sd_fix_ret.
    zr_until 0x1d8a4.
    eapply evt_cut; [eapply BCMPc | ].
    { exact BBn. }
    { exact (sd_cb_bytes _ _ _ _ HJ1m). }
    { apply sd_mcm_refl. rewrite Un, length_firstn. lia. }
    { assumption. }
    sd_postc.
    zr_until 0x16928.
    pose proof (stk_merge rsegs _ lo (bv_unsigned sp) (bv_unsigned sp + 9072) STc STb ltac:(lia)) as STF.
    replace (bv_unsigned sp + 8968) with (bv_unsigned sp + 9072 - 104) in HSV by lia.
    unfold QD. finish.
    all: try reflexivity.
Qed.
