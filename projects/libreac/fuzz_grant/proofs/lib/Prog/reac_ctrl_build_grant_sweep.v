From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel RgLemmas
  memcpy_c memset_c reac_ctrl_stamp_headamp_c reac_ctrl_build_grant_sweep_c BgsTurn BgsLoop.
Import ListNotations.
Open Scope Z_scope.

Ltac bgs_refuse sp FR0 SCR FRS ST MU WM :=
  eapply evt_mono;
  [ eapply bgs_exit;
    [ lia
    | eapply (proj2 (rw_cells_app _ _ _ _)); split;
      [ exact FR0
      | cbn [cells_size csize Nat.add];
        replace (bv_unsigned sp + -1616 + Z.of_nat 20) with (bv_unsigned sp + -1596) by lia; exact SCR ]
    | reflexivity
    | exact FRS
    | exact ST
    | lia ]
  | let ms' := fresh "ms'" in let H := fresh "H" in
    intros ms' H;
    destruct H as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST2);
    do 15 eexists; eexists; split; [reflexivity|];
    split; [exact WM|]; split; [assumption|]; split; [exact ST2|];
    split; [ match goal with HR : row_at _ |- _ =>
               eapply row_keep; [exact HR | exact MU | cbn [disjoint_from]; repeat split; lia] end |];
    match goal with HK : sweep_ok _ _ _ _ _ = false |- _ => rewrite HK end;
    split; [reflexivity | exact MU] ].

Lemma int32_pos : forall w, int32 w ->
  ((0 <? w mod 18446744073709551616) && (w mod 18446744073709551616 <? 9223372036854775808)) = (0 <? w).
Proof.
  unfold int32. intros w Hw. change (2^31) with 2147483648 in Hw.
  destruct (Z_lt_le_dec w 0).
  - rewrite <- (Z.mod_add w 1 18446744073709551616) by lia. rewrite Z.mod_small by lia.
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite (proj2 (Z.ltb_ge 0 w)) by lia. reflexivity.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec 0 w); cbn [andb].
    + apply Z.ltb_lt. lia.
    + reflexivity.
Qed.

Lemma ltu48_swrap : forall z, 0 <= z < 2147483648 + 256 ->
  bv_ltu (Z_to_bv 64 48) (Z_to_bv 64 (bv_swrap 32 z)) = false -> z <= 48.
Proof.
  intros z Hz H. rewrite bv_ltu_Z in H. rewrite (unsigned_lit 48) in H by lia.
  destruct (Z_lt_le_dec z 2147483648).
  - rewrite swrap32_id in H by lia. rewrite unsigned_lit in H by lia. apply Z.ltb_ge in H. lia.
  - exfalso. assert (E : bv_swrap 32 z = z - 4294967296).
    { unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296.
      change (bv_half_modulus 32) with 2147483648. Z.div_mod_to_equations. lia. }
    rewrite E in H. rewrite unsigned_lit_wrap in H. change (2^64) with 18446744073709551616 in H.
    assert (E2 : (z - 4294967296) mod 18446744073709551616 = z - 4294967296 + 18446744073709551616).
    { rewrite <- (Z.mod_add (z - 4294967296) 1 18446744073709551616) by lia. apply Z.mod_small. lia. }
    rewrite E2 in H. apply Z.ltb_ge in H. lia.
Qed.

Lemma lts_small : forall M z, int32 M -> -2147483648 <= z < 2147483648 ->
  bv_lts (Z_to_bv 64 M) (Z_to_bv 64 z) = (M <? z).
Proof.
  unfold int32. intros M z HM Hz. change (2^31) with 2147483648 in HM. unfold bv_lts.
  rewrite !signed64_small by lia. reflexivity.
Qed.

Theorem reac_ctrl_build_grant_sweep_holds :
  memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract -> reac_ctrl_build_grant_sweep_contract.
Proof.
  intros MEMC MEMS STAMP.
  unfold reac_ctrl_build_grant_sweep_contract, REAC_CTRL_BUILD_GRANT_SWEEP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m M base w lo junk vl -> -> -> HM HW HB HMI ST LO HM16 HROW HROWD HO.
  unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK in LO, HROWD.
  change (row_at m) in HROW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a4) as Ra4. unfold bv_modulus in Ra4.
  assert (Hlo : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  pose proof (wmono_refl rsegs m) as WM.
  destruct (sweep_ok a0 a4 M base w) eqn:HOK.
  - destruct (HO eq_refl) as (ROWS & HV & HLEN & HLEG & D1 & D2 & D3 & HROWR). clear HO.
    pose proof (proj1 (sweep_ok_spec _ _ _ _ _) HOK) as (Hsw & Hvals & Hw1 & Hbw & HMw).
    pose proof (bytes_at_bound rsegs _ _ _ HV) as BV. rewrite HLEN, Z2Nat.id in BV by lia.
    pose proof (rw_cells_bound rsegs _ _ _ ROWS) as BR. cbn [cells_size csize] in BR.
    rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
    assert (D2' : bv_unsigned a4 + Z.of_nat (length vl) <= lo \/ bv_unsigned sp <= bv_unsigned a4)
      by (rewrite HLEN, Z2Nat.id by lia; exact D2).
    assert (D3' : bv_unsigned a4 + Z.of_nat (length vl) <= bv_unsigned a0 \/
                  bv_unsigned a0 + 34 * (8 + 3 * w) <= bv_unsigned a4)
      by (rewrite HLEN, Z2Nat.id by lia; exact D3).
    replace (34 * (8 + 3 * w)) with (34 + 34 * (7 + 3 * w)) in ROWS by lia.
    apply rw_cells_cb_split in ROWS; [|lia|lia]. destruct ROWS as [R0 RREST].
    assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
    assert (U204 : bv_unsigned (Z_to_bv 64 204) = 204) by reflexivity.
    assert (U136 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 136)) = bv_unsigned a0 + 136)
      by (rewrite unsigned_lit by lia; lia).
    assert (U170 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 170)) = bv_unsigned a0 + 170)
      by (rewrite unsigned_lit by lia; lia).
    pose proof (munch_refl [(bv_unsigned sp - 1888, bv_unsigned sp);
                            (bv_unsigned a0, bv_unsigned a0 + 34 * (8 + 3 * w))] m) as MU.
    carve_frame 1616%nat ST.
    zstep. do 13 zstep.
    apply (proj1 (rw_cells_app _ _ [CB 1512 _] _)) in FR. destruct FR as [FRA FRS].
    cbn [cells_size csize Nat.add] in FRS.
    replace (bv_unsigned sp + -1616 + Z.of_nat 1512) with (bv_unsigned sp + -104) in FRS by lia.
    apply (rw_cells_split_CB rsegs _ _ [] 1512 _ [] [20%nat; 1492%nat]) in FRA; [|reflexivity].
    cbn [app mk_CB_cells] in FRA.
    apply (proj1 (rw_cells_app _ _ [CB 20 _] _)) in FRA. destruct FRA as [FR0 SCR].
    cbn [cells_size csize Nat.add] in SCR.
    replace (bv_unsigned sp + -1616 + Z.of_nat 20) with (bv_unsigned sp + -1596) in SCR by lia.
    zstep. zstep.
    if_cases TA; zify_cond TA.
    + exfalso.
      first [ rewrite (int32_pos w HW) in TA; apply Z.ltb_ge in TA; lia
            | rewrite (proj2 (Z.ltb_lt 0 w)), (proj2 (Z.ltb_lt w 9223372036854775808)) in TA by lia; discriminate ].
    + zstep. zstep. if_cases TB; zify_cond TB.
      * exfalso. lia.
      * zstep. zstep. if_cases TC; zify_cond TC.
        -- exfalso. lia.
        -- zstep. zstep. zstep. zstep. zstep. if_cases TD.
           ++ exfalso. rewrite swrap32_id in TD by lia. rewrite bv_ltu_Z in TD.
              rewrite !unsigned_lit in TD by lia. apply Z.ltb_lt in TD. lia.
           ++ zstep. zstep. zstep. zstep. if_cases TE.
              ** exfalso. rewrite Z.shiftl_mul_pow2 in TE by lia. change (2 ^ 1) with 2 in TE.
                 rewrite (Z.mod_small (w * 2 + w)) in TE by lia. rewrite swrap32_id in TE by lia.
                 rewrite lts_small in TE by (unfold int32 in *; lia).
                 apply Z.ltb_lt in TE. lia.
              ** zstep. zstep. zstep. zstep. zstep.
                 call MEMC.
                 { rewrite unsigned_lit by lia.
                   apply (ro_bytes_at rsegs _ 0x1057c HEAD_ACK34); [exact HMI | lia | cbn; lia | exact img_ack]. }
                 { reflexivity. }
                 { exact R0. }
                 { match type of R0 with rw_cells _ ?mm _ _ =>
                     pose proof (rw_ro_disj mm _ 34 _ _ _ ltac:(assumption) R0 img_ack ltac:(lia) ltac:(lia)
                                   ltac:(reflexivity)) as DJ end.
                   rewrite !unsigned_lit by lia. lia. }
                 { exact HMI. }
                 match goal with H : rw_cells _ _ (bv_unsigned a0) [CB _ HEAD_ACK34] |- _ => rename H into NR0 end.
                 zstep. zstep. zstep. zstep. zstep.
                 eapply evt_cut.
                 { eapply (turnA MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                             m sp a4 base 0 lo 1 (7 + 3 * w) (8 + 3 * w) vl _ HEAD_ACK34 _ _ _).
                   { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
                   { lia. } { lia. } { lia. } { lia. } { lia. }
                   { rewrite unsigned_lit by lia. lia. }
                   { lia. }
                   { rewrite HLEN. lia. }
                   { exact (legal_at w vl 0 0 HLEG ltac:(lia) ltac:(lia) ltac:(lia)). }
                   { exact LO. } { exact Hlo. } { exact HM16. } { assumption. } { exact FR0. } { reflexivity. }
                   { exact SCR. } { exact FRS. } { reflexivity. } { exact NR0. }
                   { replace (bv_unsigned a0 + 34 * 1) with (bv_unsigned a0 + 34) by lia. exact RREST. }
                   { assumption. } { assumption. } { exact D1. } { exact D2'. } { exact D3'. }
                   { assumption. } { assumption. } { exact HROW. } { exact HROWD. } { exact HROWR. } }
                 intros ms' Hp.
                 destruct Hp as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15
                                 & m1 & y1 & -> & HV1 & FR01 & SCR1 & FRS1 & DONE1 & REST1 & HMI1 & ST1 & MU1 & WM1).
                 zstep. zstep. zstep. zstep. if_true.
                 eapply evt_cut.
                 { eapply (turnA MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                             m sp a4 base 1 lo (1 + 1) (7 + 3 * w - 1) (8 + 3 * w) vl _ _ _ _ _).
                   { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
                   { lia. } { lia. } { lia. } { lia. } { lia. }
                   { rewrite unsigned_lit by lia. lia. }
                   { rewrite unsigned_lit by lia. lia. }
                   { rewrite HLEN. lia. }
                   { exact (legal_at w vl 0 1 HLEG ltac:(lia) ltac:(lia) ltac:(lia)). }
                   { exact LO. } { exact Hlo. } { exact HM16. } { exact HV1. } { exact FR01. } { reflexivity. }
                   { exact SCR1. } { exact FRS1. } { reflexivity. } { exact DONE1. } { exact REST1. }
                   { exact HMI1. } { exact ST1. } { exact D1. } { exact D2'. } { exact D3'. }
                   { exact MU1. } { exact WM1. } { exact HROW. } { exact HROWD. } { exact HROWR. } }
                 intros ms' Hp.
                 destruct Hp as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15
                                 & m2 & y2 & -> & HV2 & FR02 & SCR2 & FRS2 & DONE2 & REST2 & HMI2 & ST2 & MU2 & WM2).
                 zstep. zstep. zstep. zstep. if_true.
                 eapply evt_cut.
                 { eapply (turnA MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                             m sp a4 base 2 lo (1 + 1 + 1) (7 + 3 * w - 1 - 1) (8 + 3 * w) vl _ _ _ _ _).
                   { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
                   { lia. } { lia. } { lia. } { lia. } { lia. }
                   { rewrite unsigned_lit by lia. lia. }
                   { rewrite unsigned_lit by lia. lia. }
                   { rewrite HLEN. lia. }
                   { exact (legal_at w vl 0 2 HLEG ltac:(lia) ltac:(lia) ltac:(lia)). }
                   { exact LO. } { exact Hlo. } { exact HM16. } { exact HV2. } { exact FR02. } { reflexivity. }
                   { exact SCR2. } { exact FRS2. } { reflexivity. } { exact DONE2. } { exact REST2. }
                   { exact HMI2. } { exact ST2. } { exact D1. } { exact D2'. } { exact D3'. }
                   { exact MU2. } { exact WM2. } { exact HROW. } { exact HROWD. } { exact HROWR. } }
                 intros ms' Hp.
                 destruct Hp as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & e14 & e15
                                 & m3 & y3 & -> & HV3 & FR03 & SCR3 & FRS3 & DONE3 & REST3 & HMI3 & ST3 & MU3 & WM3).
                 zstep. zstep. zstep. zstep. if_false.
                 replace (34 * (7 + 3 * w - 1 - 1 - 1)) with (34 + 34 * (3 + 3 * w)) in REST3 by lia.
                 apply rw_cells_cb_split in REST3; [|lia|lia]. destruct REST3 as [R4 RR4].
                 replace (34 * (3 + 3 * w)) with (204 + 34 * (3 * w - 3)) in RR4 by lia.
                 apply rw_cells_cb_split in RR4; [|lia|lia]. destruct RR4 as [R5 RR5].
                 zstep. zstep. zstep. zstep. zstep. zstep.
                 call MEMC.
                 { rewrite unsigned_lit by lia.
                   apply (ro_bytes_at rsegs _ 0x1059e HEAD_MARK34); [exact HMI3 | lia | cbn; lia | exact img_mark]. }
                 { reflexivity. }
                 { rewrite unsigned_lit by lia.
                   replace (bv_unsigned a0 + 136) with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1)) by lia. exact R4. }
                 { match type of R4 with rw_cells _ ?mm _ _ =>
                     pose proof (rw_ro_disj mm _ 34 _ _ _ ltac:(assumption) R4 img_mark ltac:(lia) ltac:(lia)
                                   ltac:(reflexivity)) as DJ end.
                   rewrite !unsigned_lit by lia. lia. }
                 { exact HMI3. }
                 match goal with H : rw_cells _ _ _ [CB _ HEAD_MARK34] |- _ =>
                   rewrite unsigned_lit in H by lia; rename H into NR4 end.
                 replace (bv_unsigned a0 + 136) with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1)) in NR4 by lia.
                 pose proof (rw_cells_cb_join _ _ (34 * (1 + 1 + 1 + 1)) 34 _ _ ltac:(lia) ltac:(lia) DONE3 NR4) as DONE4.
                 zstep. zstep. zstep. zstep. zstep.
                 call MEMC.
                 { rewrite unsigned_lit by lia.
                   apply (ro_bytes_at rsegs _ 0x10470 GBall); [assumption | lia | cbn; lia | exact img_gb]. }
                 { reflexivity. }
                 { rewrite unsigned_lit by lia.
                   replace (bv_unsigned a0 + 170) with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1) + 34) by lia. exact R5. }
                 { match type of R5 with rw_cells _ ?mm _ _ =>
                     pose proof (rw_ro_disj mm _ 204 _ _ _ ltac:(assumption) R5 img_gb ltac:(lia) ltac:(lia)
                                   ltac:(reflexivity)) as DJ end.
                   rewrite !unsigned_lit by lia. lia. }
                 { assumption. }
                 match goal with H : rw_cells _ _ _ [CB _ GBall] |- _ =>
                   rewrite unsigned_lit in H by lia; rename H into NR5 end.
                 replace (bv_unsigned a0 + 170) with (bv_unsigned a0 + (34 * (1 + 1 + 1 + 1) + 34)) in NR5 by lia.
                 pose proof (rw_cells_cb_join _ _ (34 * (1 + 1 + 1 + 1) + 34) 204 _ _ ltac:(lia) ltac:(lia) DONE4 NR5)
                   as DONE5.
                 change (Z.to_nat 0) with 0%nat in DONE5. change (Z.to_nat 1) with 1%nat in DONE5.
                 change (Z.to_nat 2) with 2%nat in DONE5.
                 rewrite <- (prefixB1 base vl HB) in DONE5.
                 zstep. zstep. if_cases TW; rewrite lts_small in TW by (unfold int32 in *; lia).
                 --- apply Z.ltb_lt in TW. assert (w = 1) by lia. subst w.
                     zstep.
                     eapply evt_mono.
                     { eapply bgs_exit.
                       { lia. }
                       { eapply (proj2 (rw_cells_app _ _ _ _)). split; [eassumption|].
                         cbn [cells_size csize Nat.add].
                         replace (bv_unsigned sp + -1616 + Z.of_nat 20) with (bv_unsigned sp + -1596) by lia.
                         eassumption. }
                       { reflexivity. }
                       { eassumption. }
                       { eassumption. }
                       { lia. } }
                     intros ms' Hx.
                     destruct Hx as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & -> & STF).
                     unfold bgs_post. rewrite HOK.
                     do 15 eexists. eexists. split; [reflexivity|].
                     split; [assumption|]. split; [assumption|]. split; [exact STF|].
                     split; [eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]|].
                     split; [reflexivity|]. split.
                     { unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK. assumption. }
                     rewrite <- prefixB_SWEEP. exact DONE5.
                 --- apply Z.ltb_ge in TW. zstep. zstep. zstep. zstep. zstep.
                     eapply evt_mono.
                     { eapply (bgs_loopB MEMC MEMS STAMP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a0 a4
                                 M base w lo vl HOK HB HW LO Hlo HM16 HLEN HLEG D1 D2 D3 HROW HROWD HROWR
                                 (Z.to_nat (w - 1)) 1).
                       { lia. } { lia. } { lia. }
                       { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
                       { reflexivity. }
                       { rewrite unsigned_lit by lia. lia. }
                       { reflexivity. }
                       { eassumption. }
                       { eassumption. }
                       { eassumption. }
                       { eassumption. }
                       { exact DONE5. }
                       { replace (bv_unsigned a0 + 34 * (8 + 3 * 1))
                           with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1) + 34 + 204) by lia.
                         replace (34 * (3 * w - 3 * 1)) with (34 * (3 * w - 3)) by lia. eassumption. }
                       { assumption. }
                       { assumption. }
                       { assumption. }
                       { assumption. } }
                     intros ms' Hx. exact Hx.
  - clear HO.
    unfold bgs_post, REAC_CTRL_BUILD_GRANT_SWEEP_FRAME, REAC_CTRL_BUILD_GRANT_SWEEP_STACK.
    pose proof (munch_refl [(bv_unsigned sp - 1616, bv_unsigned sp)] m) as MU.
    carve_frame 1616%nat ST.
    zstep. do 13 zstep.
    apply (proj1 (rw_cells_app _ _ [CB 1512 _] _)) in FR. destruct FR as [FRA FRS].
    cbn [cells_size csize Nat.add] in FRS.
    replace (bv_unsigned sp + -1616 + Z.of_nat 1512) with (bv_unsigned sp + -104) in FRS by lia.
    apply (rw_cells_split_CB rsegs _ _ [] 1512 _ [] [20%nat; 1492%nat]) in FRA; [|reflexivity].
    cbn [app mk_CB_cells] in FRA.
    apply (proj1 (rw_cells_app _ _ [CB 20 _] _)) in FRA. destruct FRA as [FR0 SCR].
    cbn [cells_size csize Nat.add] in SCR.
    replace (bv_unsigned sp + -1616 + Z.of_nat 20) with (bv_unsigned sp + -1596) in SCR by lia.
    zstep. zstep.
    if_cases TA; zify_cond TA.
    + bgs_refuse sp FR0 SCR FRS ST MU WM.
    + assert (Hw1 : 0 < w).
      { rewrite <- Z.ltb_lt, <- (int32_pos w HW), andb_true_iff, !Z.ltb_lt. split; assumption. }
      zstep. zstep. if_cases TB; zify_cond TB.
      * bgs_refuse sp FR0 SCR FRS ST MU WM.
      * zstep. zstep. if_cases TC; zify_cond TC.
        -- bgs_refuse sp FR0 SCR FRS ST MU WM.
        -- zstep. zstep. zstep. zstep. zstep. if_cases TD.
           ++ bgs_refuse sp FR0 SCR FRS ST MU WM.
           ++ unfold int32 in HW. change (2^31) with 2147483648 in HW.
              rewrite (Z.mod_small w) in TD by lia.
              apply ltu48_swrap in TD; [|lia].
              zstep. zstep. zstep. zstep. if_cases TE.
              ** bgs_refuse sp FR0 SCR FRS ST MU WM.
              ** exfalso.
                 rewrite Z.shiftl_mul_pow2 in TE by lia.
                 change (2 ^ 1) with 2 in TE. rewrite (Z.mod_small (w * 2 + w)) in TE by lia.
                 rewrite swrap32_id in TE by lia. rewrite lts_small in TE by (unfold int32 in *; lia).
                 apply Z.ltb_ge in TE.
                 assert (sweep_ok a0 a4 M base w = true) by (apply sweep_ok_spec; repeat split; lia).
                 congruence.
Qed.
