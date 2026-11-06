From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel RgLemmas RgNeeds_c
  reac_ctrl_stamp_headamp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma legalb_spec : forall p v, legalb p v = true <-> (p < 2 /\ v <= 1) \/ (p = 2 /\ v <= 55).
Proof.
  intros. unfold legalb. rewrite orb_true_iff, !andb_true_iff, Z.ltb_lt, !Z.leb_le, Z.eqb_eq. reflexivity.
Qed.

Ltac byte_store := rewrite ?store_bytes_1'; rewrite ?le1_byte; mem_after_store.

Ltac row_now HROW :=
  eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia].

Ltac stamp_fail FR ST sp HROW MU :=
  zstep; zstep; zstep; zstep;
  release_frame FR ST (bv_unsigned sp);
  zstep; finish; try reflexivity;
  try (eapply row_keep; [exact HROW | exact MU | cbn [disjoint_from]; repeat split; lia]).

Theorem reac_ctrl_stamp_headamp_holds :
  ctrl_lay_block_need -> ctrl_finish_need -> reac_ctrl_stamp_headamp_contract.
Proof.
  intros LAY FIN.
  unfold reac_ctrl_stamp_headamp_contract, REAC_CTRL_STAMP_HEADAMP, REAC_CTRL_STAMP_HEADAMP_FRAME,
    REAC_CTRL_STAMP_HEADAMP_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f ch p v lo junk -> -> -> -> HC HP HV HMI ST LO HM16 HROW HROWD HO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (row_at m) in HROW.
  assert (Hlo : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  destruct (legalb p v) eqn:HL.
  - destruct (HO eq_refl) as (HRW & Hf & HD & HDR). clear HO.
    apply (rw_cells_split_CB rsegs m (f + 16) [] 34 junk [] [2%nat; 32%nat]) in HRW; [|reflexivity].
    cbn [app mk_CB_cells] in HRW.
    apply (proj1 (rw_cells_app m (f + 16) [CB 2 (firstn 2 junk)] [CB 32 (firstn 32 (skipn 2 junk))])) in HRW.
    destruct HRW as [HR1 HR2].
    replace (f + 16 + Z.of_nat (cells_size [CB 2 (firstn 2 junk)])) with (f + 18) in HR2 by (cbn; lia).
    pose proof (rw_cells_bound rsegs m _ _ HR1) as BF. cbn [cells_size csize] in BF.
    pose proof (rw_cells_bound rsegs m _ _ HR2) as BF2. cbn [cells_size csize] in BF2.
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (f + 16, f + 50)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 5 zstep. zstep. byte_store. zstep. byte_store. zstep. byte_store.
    zstep. zstep. zstep.
    if_cases HC1; zify_cond HC1.
    + zstep. if_cases HC2; zify_cond HC2.
      * exfalso. apply legalb_spec in HL. lia.
      * zstep. zstep. if_cases HC3; zify_cond HC3.
        -- exfalso. apply legalb_spec in HL. lia.
        -- zstep. zstep.
           zstep. byte_store. zstep. byte_store.
           zstep. zstep. zstep. zstep. zstep. zstep. zstep.
           assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
             by (rewrite unsigned_lit by lia; lia).
           assert (UA : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -27)) = bv_unsigned sp + -27)
             by (rewrite unsigned_lit by lia; lia).
           assert (ULS : CTRL_LAY_BLOCK_STACK = 240) by reflexivity.
           call (LAY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f lo ch p v _).
           { reflexivity. }
           { reflexivity. }
           { reflexivity. }
           { lia. }
           { lia. }
           { rewrite UA. lia. }
           { rewrite USP. replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia.
             rewrite Z_mod_plus_full. exact HM16. }
           { lia. }
           { lia. }
           { lia. }
           { rewrite UA. replace (bv_unsigned sp + -27) with (bv_unsigned sp + -32 + Z.of_nat 5) by lia.
             pose proof FR as FRc. destruct FRc as [[Hwf Hb] _].
             eapply bytes_at_ext; [apply (bytes_at_sub _ _ _ 5 3 Hb); rewrite cells_bytes_length by exact Hwf; cbn; lia|].
             cbn [cells_wf cell_wf] in Hwf. cbn [cells_bytes cbytes].
             rewrite (skipn_app_len _ _ 5) by exact (proj1 Hwf). reflexivity. }
           { exact HR2. }
           { assumption. }
           { rewrite USP. exact ST. }
           { unfold CTRL_LAY_BLOCK_STACK. rewrite USP. lia. }
           { rewrite USP. lia. }
           { rewrite UA, USP. lia. }
           { rewrite UA. lia. }
           { row_now HROW. }
           { rewrite ULS, USP. lia. }
           { lia. }
           rewrite USP in PC.
           zstep. zstep. zstep.
           call (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _).
           { reflexivity. }
           { reflexivity. }
           { lia. }
           { lia. }
           { match goal with H : rw_cells _ _ (f + 18) [CB 32 (bl (lay_z ch p v))] |- _ => exact H end. }
           { assumption. }
           { assumption. }
           { lia. }
           zstep. zstep. zstep. zstep. zstep.
           release_frame FR PC (bv_unsigned sp).
           zstep. finish.
           all: try (match goal with |- bytes_at _ _ CTRL_ROW CTRL_ROW_BYTES => assumption end).
           { reflexivity. }
           rewrite <- (stamp_bytes ch p v HC HP HV).
           replace (bl [0xcd; 0xea] ++ finish_bytes (bl (lay_z ch p v)))
             with (Z_to_bv 8 205 :: Z_to_bv 8 (-22) :: finish_bytes (bl (lay_z ch p v))).
           2:{ cbn [bl map app]. f_equal. f_equal. apply Z_to_bv8_mod. reflexivity. }
           apply rw_cells_join2; [exact HR1 |]. replace (f + 16 + 2) with (f + 18) by lia.
           match goal with H : rw_cells _ _ (f + 18) [CB 32 (finish_bytes _)] |- _ => exact H end.
    + zstep. zstep. if_cases HC2; zify_cond HC2.
      * zstep. zstep.
        zstep. byte_store. zstep. byte_store.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
          by (rewrite unsigned_lit by lia; lia).
        assert (UA : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -27)) = bv_unsigned sp + -27)
          by (rewrite unsigned_lit by lia; lia).
        assert (ULS : CTRL_LAY_BLOCK_STACK = 240) by reflexivity.
        call (LAY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f lo ch p v _).
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { rewrite UA. lia. }
        { rewrite USP. replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia.
          rewrite Z_mod_plus_full. exact HM16. }
        { lia. }
        { lia. }
        { lia. }
        { rewrite UA. replace (bv_unsigned sp + -27) with (bv_unsigned sp + -32 + Z.of_nat 5) by lia.
          pose proof FR as FRc. destruct FRc as [[Hwf Hb] _].
          eapply bytes_at_ext; [apply (bytes_at_sub _ _ _ 5 3 Hb); rewrite cells_bytes_length by exact Hwf; cbn; lia|].
          cbn [cells_wf cell_wf] in Hwf. cbn [cells_bytes cbytes].
          rewrite (skipn_app_len _ _ 5) by exact (proj1 Hwf). reflexivity. }
        { exact HR2. }
        { assumption. }
        { rewrite USP. exact ST. }
        { unfold CTRL_LAY_BLOCK_STACK. rewrite USP. lia. }
        { rewrite USP. lia. }
        { rewrite UA, USP. lia. }
        { rewrite UA. lia. }
        { row_now HROW. }
        { rewrite ULS, USP. lia. }
        { lia. }
        rewrite USP in PC.
        zstep. zstep. zstep.
        call (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _).
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { match goal with H : rw_cells _ _ (f + 18) [CB 32 (bl (lay_z ch p v))] |- _ => exact H end. }
        { assumption. }
        { assumption. }
        { lia. }
        zstep. zstep. zstep. zstep. zstep.
        release_frame FR PC (bv_unsigned sp).
        zstep. finish.
        all: try (match goal with |- bytes_at _ _ CTRL_ROW CTRL_ROW_BYTES => assumption end).
        { reflexivity. }
        rewrite <- (stamp_bytes ch p v HC HP HV).
        replace (bl [0xcd; 0xea] ++ finish_bytes (bl (lay_z ch p v)))
          with (Z_to_bv 8 205 :: Z_to_bv 8 (-22) :: finish_bytes (bl (lay_z ch p v))).
        2:{ cbn [bl map app]. f_equal. f_equal. apply Z_to_bv8_mod. reflexivity. }
        apply rw_cells_join2; [exact HR1 |]. replace (f + 16 + 2) with (f + 18) by lia.
        match goal with H : rw_cells _ _ (f + 18) [CB 32 (finish_bytes _)] |- _ => exact H end.
      * exfalso. apply legalb_spec in HL. lia.
  - clear HO.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (f + 16, f + 50)] m) as MU2.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 5 zstep. zstep. byte_store. zstep. byte_store. zstep. byte_store.
    zstep. zstep. zstep.
    if_cases HC1; zify_cond HC1.
    + zstep. if_cases HC2; zify_cond HC2.
      * stamp_fail FR ST sp HROW MU.
      * zstep. zstep. if_cases HC3; zify_cond HC3.
        -- stamp_fail FR ST sp HROW MU.
        -- exfalso. assert (legalb p v = true) by (apply legalb_spec; lia). congruence.
    + zstep. zstep. if_cases HC2; zify_cond HC2.
      * exfalso. assert (legalb p v = true) by (apply legalb_spec; lia). congruence.
      * zstep. stamp_fail FR ST sp HROW MU.
Qed.
