(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_prod_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit frame_kit_res.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section U32R.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 16.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis MM : 0 <= mn <= mx.
  Hypothesis MX : mx < 2^31.
  Hypothesis PNZ : 0 < P.  Hypothesis PAL : P mod 8 = 0.  Hypothesis DNZ : 0 < D.

  Notation W := [(P + 8, P + 16); (SP - 16, SP)].
  Notation POST := (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).
  Notation range := (mx - mn).

  Definition INV (m1 : fmem) (sz : Z) : Prop :=
    rw_cells usegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
    /\ bytes_at usegs m1 D (map (Z_to_bv 8) pl)
    /\ (exists junk8, rw_cells usegs m1 (SP + -16) [CB 8 junk8; C8 ra])
    /\ stk usegs m1 lo (SP + -16)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Notation STpc pc mm x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 mn) x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
    split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].

  Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

  Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
  Proof. intros [|f] sz result; reflexivity. Qed.

  Lemma wrap32_zsx32 : forall v, 0 <= v < 4294967296 -> bv_wrap 32 (zsx32 v) = v.
  Proof.
    intros v Hv. rewrite wrap32_eq. unfold zsx32. destruct (v <? 2147483648); [apply Z.mod_small; lia|].
    replace (v + 18446744069414584320) with (v + 4294967295 * 4294967296) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u32r_tail : forall m1 result sz (x5 x13 x14 x15 x16 x17 : word),
    0 <= result < 2^32 -> INV m1 sz ->
    (result, sz) = draw_loop 4 pl size range 0 ->
    evt usegs POST (STpc 0x2d73c m1 x5 (Z_to_bv 64 (zsx32 result)) (Z_to_bv 64 range) x13 x14 x15 x16 x17).
  Proof.
    intros m1 result sz x5 x13 x14 x15 x16 x17 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
    change (2^32) with 4294967296 in RR. change (2^31) with 2147483648 in MX.
    pose proof (zsx32_range result RR) as RZ.
    zstep. zstep. unfold v_remuw. zsimp.
    rewrite (wrap32_small (range + 1)) by lia. rewrite (wrap32_zsx32 result) by lia.
    replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
    rewrite swrap32_small by lia.
    zstep. rewrite swrap32_small by lia.
    zstep. zstep. zstep.
    release_frame FR1 ST1 SP.
    apply evt_done. unfold prod_u32r_post, uint32Range.
    rewrite (u32_id range) by (change (2^32) with 4294967296; lia). rewrite <- DL.
    replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; change (2^32) with 4294967296; lia).
    cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by (change (2^32) with 4294967296; lia).
    replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
    do 14 eexists. exists m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
  Qed.


  Lemma pl_nth : forall i, 0 <= i < zlen pl ->
    nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
  Proof.
    intros i Hi. destruct PL as [_ PLR]. unfold Znth.
    assert (L : (Z.to_nat i < length pl)%nat) by lia.
    split.
    - rewrite nth_error_map. rewrite (nth_error_nth' pl 0 L). reflexivity.
    - apply (proj1 (Forall_forall _ _) PLR). apply nth_In. exact L.
  Qed.

  (* [comment removed for export] *)
  Lemma u32r_loop : forall f sz rolling result m1 (x5 x14 x17 : word),
    0 < rolling < 2^(8 * Z.of_nat f) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
    0 <= sz <= zlen pl -> x14 = Z_to_bv 64 sz -> INV m1 sz ->
    (forall m2 (y5 y14 y16 y17 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
       0 <= fst (draw_loop f pl sz rolling result) < 2^32 ->
       evt usegs POST (STpc 0x2d72c m2 y5 (Z_to_bv 64 (zsx32 (fst (draw_loop f pl sz rolling result)))) (Z_to_bv 64 range) (Z_to_bv 64 P) y14 (Z_to_bv 64 1) y16 y17)) ->
    evt usegs POST (STpc 0x2d6f4 m1 x5 (Z_to_bv 64 result) (Z_to_bv 64 range) (Z_to_bv 64 P) x14 (Z_to_bv 64 1) (Z_to_bv 64 rolling) x17).
  Proof.
    induction f as [|f IH]; intros sz rolling result m1 x5 x14 x17 RO RE F4 SZ1 -> (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
    { exfalso. cbn in RO. lia. }
    pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    assert (P8 : 2^(8 * Z.of_nat (S f)) = 256 * 2^(8 * Z.of_nat f)).
    { replace (8 * Z.of_nat (S f)) with (8 + 8 * Z.of_nat f) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
    { replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
    assert (P32 : 2^(8 * Z.of_nat (S f)) <= 2^32) by (apply Z.pow_le_mono_r; lia).
    assert (P0 : 0 < 2^(8 * Z.of_nat f)) by (apply Z.pow_pos_nonneg; lia).
    assert (Q0 : 0 < 2^(32 - 8 * Z.of_nat (S f))) by (apply Z.pow_pos_nonneg; lia).
    cbn [draw_loop] in K. change (2^8) with 256 in K.
    replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
    change (2^24) with 16777216 in Q24. change (2^32) with 4294967296 in *.
    zstep. if_cases B; zify_cond B.
    - (* [comment removed for export] *)
      assert (sz = 0) by (Z.div_mod_to_equations; lia). subst sz.
      replace (0 <? 0) with false in K by reflexivity. cbn [fst snd] in K.
      rewrite (zsx32_small result) in K by lia.
      apply K; [| lia].
      inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
    - assert (SZP : 0 < sz) by (Z.div_mod_to_equations; lia).
      replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
      destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
      zstep. zstep. zstep. fck. zstep. fck. zstep. fck. zstep. fck.
      assert (RD : ov_read_bytes usegs m1 (Z_to_bv 64 (sz + D + -1)) 1 = Some [Z_to_bv 8 (Znth (sz - 1) pl)]).
      { eapply (u8ro_read usegs m1 D _ (sz - 1)); [exact PL1| exact NTH| lia| unfold wa; f_equal; lia]. }
      zstep. cbv beta. rewrite byte_lit by exact NR.
      zstep. zstep.
      zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
      assert (SWZ : Z_to_bv 64 (bv_swrap 32 (result * 256)) = Z_to_bv 64 (zsx32 (result * 256))).
      { apply Z_to_bv_eqm. rewrite swrap32_eq. unfold zsx32. destruct (Z.ltb_spec (result * 256) 2147483648) as [L|L].
        - rewrite Z.mod_small by lia. f_equal. lia.
        - replace ((result * 256 + 2147483648) mod 4294967296) with (result * 256 - 2147483648)
            by (apply (Z.mod_unique _ _ 1); lia).
          change (2^64) with 18446744073709551616.
          replace (result * 256 + 18446744069414584320) with (result * 256 - 2147483648 - 2147483648 + 1 * 18446744073709551616) by lia.
          rewrite Z.mod_add by lia. reflexivity. }
      rewrite SWZ. clear SWZ.
      pose proof (zsx32_range (result * 256) ltac:(lia)) as RZS.
      zstep. rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
      assert (RD8 : 0 <= rolling / 256 < 2^(8 * Z.of_nat f)).
      { split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
      rewrite swrap32_small by lia.
      zstep.
      set (bt := Znth (sz - 1) pl) in *.
      assert (LORZ : Z.lor (zsx32 (result * 256)) bt = zsx32 (result * 256 + bt)).
      { rewrite (lor_add_disj 8); [ | lia | change (2^8) with 256; lia | ].
        - unfold zsx32. destruct (Z.ltb_spec (result * 256) 2147483648) as [L|L]; destruct (Z.ltb_spec (result * 256 + bt) 2147483648) as [L2|L2]; lia.
        - change (2^8) with 256. unfold zsx32. destruct (result * 256 <? 2147483648); [apply Z_mod_mult|].
          replace (result * 256 + 18446744069414584320) with ((result + 72057594021150720) * 256) by lia. apply Z_mod_mult. }
      rewrite LORZ. clear LORZ.
      rewrite (u32_id (result * 256)) in K by (change (2^32) with 4294967296; lia).
      assert (LOR : Z.lor (result * 256) bt = result * 256 + bt) by (apply (lor_byte result); lia).
      rewrite LOR in K.
      zstep.
      if_cases B2; zify_cond B2.
      + (* [comment removed for export] *)
        assert (F1 : (1 <= f)%nat). { destruct f; [exfalso; cbn in RD8; lia| lia]. }
        assert (Q24' : 2^(32 - 8 * Z.of_nat f) <= 2^24) by (apply Z.pow_le_mono_r; lia).
        change (2^24) with 16777216 in Q24'.
        rewrite (zsx32_small (result * 256 + bt)) by lia.
        eapply (IH (sz - 1) (rolling / 256) (result * 256 + bt)); try lia.
        * f_equal; try lia.
        * replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
        * exact K.
      + (* [comment removed for export] *)
        assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K. cbn [fst snd] in K.
        apply K; [| lia].
        replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
  Qed.

  Lemma u32r_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_U32R) fc None m (seg_rom usegs)).
  Proof.
    pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    change (2^31) with 2147483648 in MX.
    carve_frame 16%nat ST.
    zstep. zstep. zstep.
    if_cases K; zify_cond K. { exfalso. lia. }
    zstep. rewrite swrap32_small by lia. zstep.
    if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (zsx32 0)) by reflexivity.
      eapply (u32r_tail _ 0 size); [change (2^32) with 4294967296; lia| | ].
      + inv_close PR0 PLB FR ST MU WM MI.
      + rewrite K2. reflexivity.
    - assert (K2' : 0 < range) by (Z.div_mod_to_equations; lia).
      zstep. zstep. fck. zstep. zstep. fck. zstep. zstep. zstep.
      try replace (Z.land P 7) with 0 by (rewrite fk_land7_mod8; lia).
      eapply (u32r_loop 4 size range 0);
        [ change (2^(8 * Z.of_nat 4)) with 4294967296; lia | cbn; lia | lia | lia | reflexivity | | ].
      + inv_close PR0 PLB FR ST MU WM MI.
      + intros m2 y5 y14 y16 y17 I2 R2.
        zstep. zstep. if_cases K3; zify_cond K3.
        * eapply u32r_tail; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
        * exfalso. Z.div_mod_to_equations; lia.
  Qed.
End U32R.

Lemma zd_u32r_proof : zd_u32r_stmt.
Proof.
  intros until lo. intros PR PL SZ PNZ PAL DNZ ST LO RSP PLO DLO DP MI MM MX -> -> ->.
  eapply u32r_body; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RESERVE.
  Hypothesis U32R : zd_u32r_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis SZ31 : size < 2^31.
  Hypothesis P0 : 0 < P.  Hypothesis P8 : P mod 8 = 0.  Hypothesis D0 : 0 < D.  Hypothesis DE : D + zlen pl < 2^64.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 32.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(P, P + 16); (SP - 32, SP)].
  Notation POST := (zd_reserve_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size lo m).

  (* [comment removed for export] *)
  Lemma le8_small_split : forall v, 0 <= v < 4294967296 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
  Proof.
    intros v Hv. rewrite <- store_bytes_8'. unfold le4.
    assert (E : bv_unsigned (Z_to_bv 64 v) = v) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    rewrite E. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
    assert (Z0 : forall k, 32 <= k -> v ≫ k = 0) by (intros k Hk; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; split; [lia|];
                                                      apply Z.lt_le_trans with (2^32); [change (2^32) with 4294967296; lia| apply Z.pow_le_mono_r; lia]).
    rewrite (Z0 (8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8 + 8 + 8)) by lia.
    rewrite !Z.shiftr_0_l. reflexivity.
  Qed.

  Lemma reserve_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_RESERVE) fc None m (seg_rom usegs)).
  Proof.
    pose proof PR as PR0. unfold prod_at in PR0. pose proof PL as [PLB PLR].
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    change (2^31) with 2147483648 in SZ31.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. fck. zstep. zstep. zstep. fck.
    assert (PR4 : rw_cells usegs m1 P [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_recell; [exact PR0 | cbn; tauto |]. cbn [cells_bytes cbytes]. rewrite (le8_small_split size) by lia. rewrite <- app_assoc. reflexivity. }
    zstep. rewrite sx32w_small by lia. clear PR4.
    zstep. zstep. zstep.
    call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -16) P D pl size 0 size lo);
      [ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST | lia | lia | exact PLO | exact DLO | exact DP
      | exact MI | lia | change (2^31) with 2147483648; lia | reflexivity | reflexivity | reflexivity | ].
    pose proof (uint32Range_range pl size 0 size ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as UR.
    unfold zd_reserve_post, reserve_data_prefix.
    destruct (uint32Range pl size 0 size) as [slice size1]. cbn [fst snd] in *. destruct UR as [RSL RS1].
    unfold prod_at in POST.
    zstep. zstep.
    try rewrite (Z.mod_small slice) by lia.
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR PC SP.
    call (zd_reserve_tail_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P D size1 slice);
      [ exact POST | exact P0 | exact P8 | exact D0 | lia | lia | lia | eassumption | ].
    apply evt_done.
    do 14 eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold prod_at. eassumption.
  Qed.
End RESERVE.

Theorem zd_reserve_proof : zd_u32r_stmt -> zd_reserve_stmt.
Proof.
  intros U32R. unfold zd_reserve_stmt. intros until lo.
  intros PR PL SZ SZ31 P0 P8 D0 DE ST LO RSP PLO DLO DP MI ->.
  eapply reserve_body; eassumption.
Qed.
