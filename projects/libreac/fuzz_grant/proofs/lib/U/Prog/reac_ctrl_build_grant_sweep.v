From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel RgLemmas
  memcpy_c memset_c reac_ctrl_stamp_headamp_c reac_ctrl_build_grant_sweep_c BgsTurn BgsLoop.
Import ListNotations.
Open Scope Z_scope.

(* A hypothesis lia does not look into: disjunctions kept here do not multiply every lia call. *)
Definition bgs_hide (P : Prop) : Prop := P.
Lemma bgs_hide_in : forall P : Prop, P -> bgs_hide P.
Proof. intros P H. exact H. Qed.

Lemma int32_mod64 : forall w, int32 w ->
  (0 <= w /\ w mod 18446744073709551616 = w) \/
  (w < 0 /\ w mod 18446744073709551616 = w + 18446744073709551616).
Proof.
  unfold int32. intros w Hw. change (2^31) with 2147483648 in Hw.
  destruct (Z_lt_le_dec w 0).
  - right. split; [lia|]. rewrite <- (Z.mod_add w 1 18446744073709551616) by lia. apply Z.mod_small. lia.
  - left. split; [lia|]. apply Z.mod_small. lia.
Qed.

(* The branch at the current pc is not taken: the taken side (the first goal of if_cases) contradicts the
   context. zify_cond may split the condition into two hypotheses, so H may be gone after it. *)
Ltac br_off :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "BR" in
      if_cases H; [ zify_cond H; try zsimpl_hyp H; exfalso; lia | clear H ]
  | _ => idtac
  end.

Ltac bgs_refuse sp FR0 SCR FRS ST MU WM :=
  eapply evt_mono;
  [ eapply bgs_exit;
    [ lia
    | eapply (proj2 (rw_cells_app _ _ _ _)); split;
      [ exact FR0
      | cbn [cells_size csize Nat.add];
        replace (bv_unsigned sp + -1632 + Z.of_nat 36) with (bv_unsigned sp + -1596) by lia; exact SCR ]
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

(* Side goals of a turnA call left after the reflexivity/eassumption pass. *)
Ltac turnA_side w vl HLEG HLEN HROW HID :=
  first [ solve [apply not_val]
        | solve [apply (legal_at w vl 0 _ HLEG); lia]
        | solve [rewrite HLEN; lia]
        | exact HROW
        | exact (proj1 (proj2 (proj2 HID)))
        | exact (proj2 (proj2 (proj2 HID)))
        | solve [f_equal; unlits; lia]
        | solve [f_equal; unlits; zsimpl_goal; lia]
        | solve [unlits; lia]
        | solve [lia] ].

Theorem reac_ctrl_build_grant_sweep_holds :
  memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract -> reac_ctrl_build_grant_sweep_contract.
Proof.
  intros MEMC MEMS STAMP.
  unfold reac_ctrl_build_grant_sweep_contract, REAC_CTRL_BUILD_GRANT_SWEEP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m M base w lo junk vl -> -> -> HM HW HB HS14 HMI ST LO HM16 HROW HROWD HO.
  unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK in LO, HROWD.
  change (row_at m) in HROW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a4) as Ra4. unfold bv_modulus in Ra4.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp, Ra0, Ra4.
  assert (Hlo : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  pose proof HM as HM'. pose proof HW as HW'. unfold int32 in HM', HW'.
  change (2^31) with 2147483648 in HM', HW'.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (sweep_ok a0 a4 M base w) eqn:HOK.
  - destruct (HO eq_refl) as (ROWS & HV & HLEN & HLEG & D1 & D2 & D3 & HROWR). clear HO HS14.
    pose proof (proj1 (sweep_ok_spec _ _ _ _ _) HOK) as (Hsw & Hvals & Hw1 & Hbw & HMw).
    pose proof (bytes_at_bound rsegs _ _ _ HV) as BV. rewrite HLEN, Z2Nat.id in BV by lia.
    pose proof (rw_cells_bound rsegs _ _ _ ROWS) as BR. cbn [cells_size csize] in BR.
    rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
    assert (D2' : bv_unsigned a4 + Z.of_nat (length vl) <= lo \/ bv_unsigned sp <= bv_unsigned a4)
      by (rewrite HLEN, Z2Nat.id by lia; exact D2).
    assert (D3' : bv_unsigned a4 + Z.of_nat (length vl) <= bv_unsigned a0 \/
                  bv_unsigned a0 + 34 * (8 + 3 * w) <= bv_unsigned a4)
      by (rewrite HLEN, Z2Nat.id by lia; exact D3).
    pose proof (bgs_hide_in _ (conj D2 (conj D3 (conj HROWD HROWR)))) as HID. clear D2 D3 HROWD HROWR.
    assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
    assert (U136 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 136)) = bv_unsigned a0 + 136)
      by (rewrite unsigned_lit by lia; lia).
    replace (34 * (8 + 3 * w)) with (34 + 34 * (7 + 3 * w)) in ROWS by lia.
    apply rw_cells_cb_split in ROWS; [|lia|lia]. destruct ROWS as [R0 RREST].
    pose proof (munch_refl [(bv_unsigned sp - 1856, bv_unsigned sp);
                            (bv_unsigned a0, bv_unsigned a0 + 34 * (8 + 3 * w))] m) as MU.
    carve_frame 1632%nat ST.
    zstep. do 13 zstep.
    apply (proj1 (rw_cells_app _ _ [CB 1528 _] _)) in FR. destruct FR as [FRA FRS].
    cbn [cells_size csize Nat.add] in FRS.
    replace (bv_unsigned sp + -1632 + Z.of_nat 1528) with (bv_unsigned sp + -104) in FRS by lia.
    apply (rw_cells_split_CB rsegs _ _ [] 1528 _ [] [36%nat; 1492%nat]) in FRA; [|reflexivity].
    cbn [app mk_CB_cells] in FRA.
    apply (proj1 (rw_cells_app _ _ [CB 36 _] _)) in FRA. destruct FRA as [FR0 SCR].
    cbn [cells_size csize Nat.add] in SCR.
    replace (bv_unsigned sp + -1632 + Z.of_nat 36) with (bv_unsigned sp + -1596) in SCR by lia.
    (* 0x14524: li s5; beqz a0; mv s1; blez a3; mv s0; beqz a4 *)
    zstep.
    zstep. br_off.
    zstep. zstep. br_off.
    zstep. zstep. br_off.
    (* base + width: the UBSan overflow check, then the 48-channel bound *)
    zstep. zstep. zstep. zstep. zstep. trap_off.
    zstep. zstep. zstep. br_off.
    (* 3 * width and 8 + 3 * width: UBSan overflow checks, then max < n *)
    zstep. zstep. zstep. zstep. trap_off.
    zstep. zstep. zstep. trap_off.
    zstep. br_off.
    (* memcpy(sweep[0], GRANT_HEAD_ACK, 34) *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    call MEMC.
    { rewrite unsigned_lit by lia.
      apply (ro_bytes_at rsegs _ 0x105b4 HEAD_ACK34); [exact HMI | lia | cbn; lia | exact img_ack]. }
    { reflexivity. }
    { exact R0. }
    { match type of R0 with rw_cells _ ?mm _ _ =>
        pose proof (rw_ro_disj mm _ 34 _ _ _ ltac:(assumption) R0 img_ack ltac:(lia) ltac:(lia)
                      ltac:(reflexivity)) as DJ end.
      rewrite !unsigned_lit by lia. lia. }
    { exact HMI. }
    match goal with H : rw_cells _ _ (bv_unsigned a0) [CB _ HEAD_ACK34] |- _ => rename H into NR0 end.
    zstep. zstep. zstep. zstep. zstep.
    (* group A of the first channel: three turns *)
    eapply evt_cut.
    { eapply (turnA MEMC MEMS STAMP) with (m0 := m) (spo := sp) (base := base) (p := 0) (lo := lo) (k := 1)
        (r := 7 + 3 * w) (n := 8 + 3 * w) (vl := vl) (dn := HEAD_ACK34);
        first [ reflexivity | eassumption | idtac ].
      all: turnA_side w vl HLEG HLEN HROW HID. }
    intros ms' Hp.
    destruct Hp as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15
                    & m1 & y1 & -> & HV1 & FR01 & SCR1 & FRS1 & DONE1 & REST1 & HMI1 & ST1 & MU1 & WM1).
    zstep. zstep. zstep. first [ if_true | idtac ].
    eapply evt_cut.
    { eapply (turnA MEMC MEMS STAMP) with (m0 := m) (spo := sp) (base := base) (p := 1) (lo := lo) (k := 1 + 1)
        (r := 7 + 3 * w - 1) (n := 8 + 3 * w) (vl := vl);
        first [ reflexivity | eassumption | idtac ].
      all: turnA_side w vl HLEG HLEN HROW HID. }
    intros ms' Hp.
    destruct Hp as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15
                    & m2 & y2 & -> & HV2 & FR02 & SCR2 & FRS2 & DONE2 & REST2 & HMI2 & ST2 & MU2 & WM2).
    zstep. zstep. zstep. first [ if_true | idtac ].
    eapply evt_cut.
    { eapply (turnA MEMC MEMS STAMP) with (m0 := m) (spo := sp) (base := base) (p := 2) (lo := lo)
        (k := 1 + 1 + 1) (r := 7 + 3 * w - 1 - 1) (n := 8 + 3 * w) (vl := vl);
        first [ reflexivity | eassumption | idtac ].
      all: turnA_side w vl HLEG HLEN HROW HID. }
    intros ms' Hp.
    destruct Hp as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & e14 & e15
                    & m3 & y3 & -> & HV3 & FR03 & SCR3 & FRS3 & DONE3 & REST3 & HMI3 & ST3 & MU3 & WM3).
    zstep. zstep. zstep. first [ if_false | idtac ].
    replace (34 * (7 + 3 * w - 1 - 1 - 1)) with (34 + 34 * (3 + 3 * w)) in REST3 by lia.
    apply rw_cells_cb_split in REST3; [|lia|lia]. destruct REST3 as [R4 RR4].
    replace (34 * (3 + 3 * w)) with (204 + 34 * (3 * w - 3)) in RR4 by lia.
    apply rw_cells_cb_split in RR4; [|lia|lia]. destruct RR4 as [R5 RR5].
    (* sweep + 136: UBSan pointer-overflow check, then memcpy(sweep[4], GRANT_HEAD_MARK, 34) *)
    zstep. zstep. trap_off.
    zstep. zstep. zstep. zstep. zstep.
    call MEMC.
    { rewrite unsigned_lit by lia.
      apply (ro_bytes_at rsegs _ 0x105d6 HEAD_MARK34); [exact HMI3 | lia | cbn; lia | exact img_mark]. }
    { reflexivity. }
    { first [ rewrite U136 | rewrite unsigned_lit by lia ].
      replace (bv_unsigned a0 + 136) with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1)) by lia. exact R4. }
    { match type of R4 with rw_cells _ ?mm _ _ =>
        pose proof (rw_ro_disj mm _ 34 _ _ _ ltac:(assumption) R4 img_mark ltac:(lia) ltac:(lia)
                      ltac:(reflexivity)) as DJ end.
      rewrite !unsigned_lit by lia. lia. }
    { exact HMI3. }
    match goal with H : rw_cells _ _ _ [CB _ HEAD_MARK34] |- _ =>
      first [ rewrite U136 in H | rewrite unsigned_lit in H by lia ]; rename H into NR4 end.
    replace (bv_unsigned a0 + 136) with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1)) in NR4 by lia.
    pose proof (rw_cells_cb_join _ _ (34 * (1 + 1 + 1 + 1)) 34 _ _ ltac:(lia) ltac:(lia) DONE3 NR4) as DONE4.
    (* group B: six memcpy's of 34 bytes *)
    zstep. zstep. zstep. zstep.
    replace (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1) + 34) with (bv_unsigned a0 + 170) in R5 by lia.
    change (Z.to_nat 204) with (Z.to_nat (0 + 204)) in R5.
    apply rw_cells_cb_split in R5; [|lia|lia]. destruct R5 as [G0 R5].
    call (grp_loop MEMC 6%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _).
    { reflexivity. }
    { lia. }
    { first [ reflexivity | f_equal; lia ]. }
    { first [ reflexivity | f_equal; lia ]. }
    { reflexivity. }
    { apply not_val. }
    { assumption. }
    { exact G0. }
    { exact R5. }
    match goal with H : rw_cells _ _ _ [CB _ GBall] |- _ => rename H into NR5 end.
    replace (bv_unsigned a0 + 170) with (bv_unsigned a0 + (34 * (1 + 1 + 1 + 1) + 34)) in NR5 by lia.
    pose proof (rw_cells_cb_join _ _ (34 * (1 + 1 + 1 + 1) + 34) 204 _ _ ltac:(lia) ltac:(lia) DONE4 NR5)
      as DONE5.
    change (Z.to_nat 0) with 0%nat in DONE5. change (Z.to_nat 1) with 1%nat in DONE5.
    change (Z.to_nat 2) with 2%nat in DONE5.
    rewrite <- (prefixB1 base vl HB) in DONE5.
    (* width < 2: return 11 *)
    zstep. zstep. zstep. if_cases TW; zify_cond TW; try zsimpl_hyp TW.
    + assert (w = 1) by lia. try clear TW. subst w.
      eapply evt_mono.
      { eapply bgs_exit.
        { lia. }
        { eapply (proj2 (rw_cells_app _ _ _ _)). split; [eassumption|].
          cbn [cells_size csize Nat.add].
          replace (bv_unsigned sp + -1632 + Z.of_nat 36) with (bv_unsigned sp + -1596) by lia.
          eassumption. }
        { reflexivity. }
        { eassumption. }
        { eassumption. }
        { lia. } }
      intros ms' Hx.
      destruct Hx as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & -> & STF).
      unfold bgs_post. rewrite HOK. destruct HID as (D2 & D3 & HROWD & HROWR).
      do 15 eexists. eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
      split; [eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]|].
      split; [reflexivity|]. split.
      { unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK. eassumption. }
      rewrite <- prefixB_SWEEP. exact DONE5.
    + assert (Hw2 : 2 <= w) by lia. try clear TW.
      (* li a2,1; lui; li a1,34; addiw; sd a0,24(sp): the countdown of the overflow check *)
      zstep. zstep. zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (bv_unsigned sp + -1632) [CB 24 _; C8 ?v; CB 4 _] |- _ =>
        replace v with (Z_to_bv 64 (2147483639 - 3 * 1)) in H by (vm_compute; reflexivity) end.
      destruct HID as (D2 & D3 & HROWD & HROWR). clear D2' D3'.
      eapply evt_mono.
      { eapply (bgs_loopB MEMC MEMS STAMP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a0 a4
                  M base w lo vl HOK HB HW LO Hlo HM16 HLEN HLEG D1 D2 D3 HROW HROWD HROWR
                  (Z.to_nat (w - 1)) 1);
          first [ reflexivity | eassumption | idtac ].
        all: first [ solve [exact DONE5]
                   | solve [replace (bv_unsigned a0 + 34 * (8 + 3 * 1))
                              with (bv_unsigned a0 + 34 * (1 + 1 + 1 + 1) + 34 + 204) by lia;
                            replace (34 * (3 * w - 3 * 1)) with (34 * (3 * w - 3)) by lia; eassumption]
                   | solve [lia] ]. }
      intros ms' Hx. exact Hx.
  - clear HO.
    unfold bgs_post, REAC_CTRL_BUILD_GRANT_SWEEP_FRAME, REAC_CTRL_BUILD_GRANT_SWEEP_STACK.
    pose proof (munch_refl [(bv_unsigned sp - 1632, bv_unsigned sp)] m) as MU.
    carve_frame 1632%nat ST.
    zstep. do 13 zstep.
    apply (proj1 (rw_cells_app _ _ [CB 1528 _] _)) in FR. destruct FR as [FRA FRS].
    cbn [cells_size csize Nat.add] in FRS.
    replace (bv_unsigned sp + -1632 + Z.of_nat 1528) with (bv_unsigned sp + -104) in FRS by lia.
    apply (rw_cells_split_CB rsegs _ _ [] 1528 _ [] [36%nat; 1492%nat]) in FRA; [|reflexivity].
    cbn [app mk_CB_cells] in FRA.
    apply (proj1 (rw_cells_app _ _ [CB 36 _] _)) in FRA. destruct FRA as [FR0 SCR].
    cbn [cells_size csize Nat.add] in SCR.
    replace (bv_unsigned sp + -1632 + Z.of_nat 36) with (bv_unsigned sp + -1596) in SCR by lia.
    zstep.
    zstep. if_cases TA.
    + clear TA. bgs_refuse sp FR0 SCR FRS ST MU WM.
    + zify_cond TA. assert (Ha0 : bv_unsigned a0 <> 0) by lia. try clear TA.
      zstep. zstep. if_cases TB.
      * clear TB. bgs_refuse sp FR0 SCR FRS ST MU WM.
      * zify_cond TB; try zsimpl_hyp TB.
        assert (Hw1 : 0 < w) by (pose proof (int32_mod64 w HW); lia).
        repeat match goal with H : context [w mod 18446744073709551616] |- _ => clear H end.
        try clear TB.
        zstep. zstep. if_cases TC.
        -- clear TC. bgs_refuse sp FR0 SCR FRS ST MU WM.
        -- zify_cond TC. assert (Ha4 : bv_unsigned a4 <> 0) by lia. try clear TC.
           pose proof (HS14 Ha0 Ha4 ltac:(lia)) as Hbw31. clear HS14.
           change (2^31) with 2147483648 in Hbw31.
           zstep. zstep. zstep. zstep. zstep. trap_off.
           zstep. zstep. zstep. if_cases TD.
           ++ clear TD. bgs_refuse sp FR0 SCR FRS ST MU WM.
           ++ zify_cond TD; try zsimpl_hyp TD.
              assert (Hbw : base + w <= 48) by lia. try clear TD.
              zstep. zstep. zstep. zstep. trap_off.
              zstep. zstep. zstep. trap_off.
              zstep. if_cases TE.
              ** clear TE. bgs_refuse sp FR0 SCR FRS ST MU WM.
              ** zify_cond TE; try zsimpl_hyp TE. exfalso.
                 assert (sweep_ok a0 a4 M base w = true) by (apply sweep_ok_spec; repeat split; lia).
                 congruence.
Qed.
