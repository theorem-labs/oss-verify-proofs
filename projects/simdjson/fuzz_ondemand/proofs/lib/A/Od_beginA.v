(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_plusA Od_headA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Lemma land7_eq : forall a r, (a mod 8 = r)%Z -> Z.land a 7 = r.
Proof. intros a r H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b r IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2 ^ 8)%Z.
    rewrite <- Z.land_ones by lia.
    apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lor_spec.
    destruct (Z.ltb_spec k 8) as [L|G].
    + rewrite Z.ones_spec_low by lia. rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (change (2 ^ 8)%Z with 256%Z; lia).
      apply Z.mod_pow2_bits_high. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. change (8 - 8)%Z with 0%Z. rewrite Z.shiftl_0_r.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by (change (2 ^ 8)%Z with 256%Z; lia).
    rewrite Z.lor_0_l. exact IH.
Qed.
Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : Z, le8 (Z_to_bv 64 v) = bs.
Proof.
  intros bs H. exists (bytes_le_to_Z bs). unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ (8 * Z.of_nat 8))%Z.
  rewrite Z_to_le_bytes_mod by lia. rewrite <- H at 1. apply Z_to_le_bytes_of_bytes.
Qed.
Lemma od_le8_err28 : le8 (Z_to_bv 64 28) = le4 (Z_to_bv 64 28) ++ le4 (Z_to_bv 64 0).
Proof.
  rewrite <- store_bytes_8'. unfold le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  repeat (apply (f_equal2 (@cons byte)); [apply bv_eq; vm_compute; reflexivity|]). reflexivity.
Qed.

Definition OD_PRE (E : oaenv) (m1 : mem) : Prop :=
  (exists j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j192 j224 j232 j248 j256 j264 j272 j280 j288 j296 j304 j312 j320 j328 j336 j344, rw_cells asegs m1 (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (wz (o_act E)); CB 8 j192; C8 (wz (oa_F E)); C8 (wz (oa_F E + 96)); C8 (wz (oa_F E + 104)); CB 8 j224; CB 8 j232; C8 (wz (oa_F E / 8 + 2147450880)); CB 8 j248; CB 8 j256; CB 8 j264; CB 8 j272; CB 8 j280; CB 8 j288; CB 8 j296; CB 8 j304; CB 8 j312; CB 8 j320; CB 8 j328; CB 8 j336; CB 8 j344]) /\
  (exists junk, rw_cells asegs m1 (oa_F E + 192) [CB 64 junk]) /\
  rw_cells asegs m1 (oa_F E + 96) (od_parser_cells E) /\
  rw_cells asegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr asegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at asegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at asegs m1 (o_SB E) (o_CAP E) /\
  ro_cells asegs m1 OD_DPI_VT od_vt_cells /\
  ro_cells asegs m1 OD_GOT_TABS od_got_cells /\
  mem_inv asegs m1 /\
  stk asegs m1 (o_lo E) (oa_S1 E).

Section Begin.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition low_cells (vs6 v v248 v312 : Z) (j0 j8 j16 j24 j104 j112 j120 j176 j344 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] ++ fr_k32 vs6 ++ [CB 8 j104; CB 8 j112; CB 8 j120] ++ fr_k128 E ++ [CB 8 j176]
    ++ [C8 (wz (o_act E)); C8 (wz (oa_F E)); C8 (wz (oa_F E)); C8 (wz (oa_F E + 96)); C8 (wz (oa_F E + 104)); C8 (wz (v - 1));
        C8 (wz 0x1100000000); C8 (wz (oa_F E / 8 + 2147450880)); C8 (wz v248);
        C8 (wz 0xa01); C8 (wz 0xffff0000ffff); C8 (wz 0x271000000001); C8 (wz 100000000); C8 (wz 0x640001); C8 (wz 0x6c6c756e);
        C8 (wz v); C8 (wz v312); C8 (wz ((vs6 + 16) / 8 + 2147450880)); C8 (wz v); C8 (wz ((vs6 + 32) / 8 + 2147450880)); CB 8 j344].

  Definition consts_post (vs6 v v248 v312 : Z) (xs0 xs4 xs11 : word) (xF : bvmap 5 word) (xfc : bv 32) (m : mem)
      (j0 j8 j16 j24 j104 j112 j120 j176 j344 : list byte) : machine_state -> Prop :=
    fun ms' => exists xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xt3 xt4 (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                    xs0 (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    xs2 (Z_to_bv 64 2147450880) xs4 (Z_to_bv 64 ((vs6 + 8) / 8 + 2147450880)) (Z_to_bv 64 vs6)
                    (Z_to_bv 64 ((vs6 + 36) / 8 + 2147450880)) (Z_to_bv 64 (vs6 + 8)) xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 v312) (Z_to_bv 64 v))
               xF (Z_to_bv 64 OD_HEAD) xfc None m' (seg_rom asegs)
      /\ munch [(oa_S1 E, oa_S1 E + 352)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (oa_S1 E) (low_cells vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344).

  Lemma od_consts : forall vs6 v v248 v312 xra xt0 xt1 xt2 xs0 xa0 xa1 xa6 xa7 xs2 xs4 xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j224 j232 j256 j264 j272 j280 j288 j296 j304 j320 j328 j336 j344,
    mem_inv asegs m1 -> (0 <= v <= 1)%Z -> (0 <= v312 <= 1)%Z -> (vs6 mod 8 = 0)%Z -> (0 <= vs6 < 2^47)%Z ->
    rw_cells asegs m1 (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (o_COPY E)); CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E + 96)); C8 (Z_to_bv 64 (oa_F E + 104)); CB 8 j224; CB 8 j232; C8 (Z_to_bv 64 (oa_F E / 8 + 2147450880)); C8 (Z_to_bv 64 v248); CB 8 j256; CB 8 j264; CB 8 j272; CB 8 j280; CB 8 j288; CB 8 j296; CB 8 j304; C8 (Z_to_bv 64 v312); CB 8 j320; CB 8 j328; CB 8 j336; CB 8 j344] ->
    evt asegs (consts_post vs6 v v248 v312 xs0 xs4 xs11 xF xfc m1 j0 j8 j16 j24 j104 j112 j120 j176 j344)
      (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (oa_S1 E))
               xa0 xa1 (Z_to_bv 64 (vs6 + 36)) (Z_to_bv 64 v) (Z_to_bv 64 (vs6 + 16)) (Z_to_bv 64 (vs6 + 32)) xa6 xa7
               xs2 (Z_to_bv 64 2147450880) xs4 xs5 (Z_to_bv 64 vs6) xs7 (Z_to_bv 64 (vs6 + 8)) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          xF (Z_to_bv 64 0x971b8) xfc None m1 (seg_rom asegs)).
  Proof using OK.
    intros until j344. intros MI VV V312 VS8 VSR FRL.
    od_env OK.
    pose proof (munch_refl [(oa_S1 E, oa_S1 E + 352)%Z] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    set (mm0 := m1) in MU at 1, WM at 1 |- * at 1.
    assert (L36 : Z.land (vs6 + 36) 7 = 4%Z) by (apply land7_eq; lia).
    assert (L32 : Z.land (vs6 + 32) 7 = 0%Z) by (apply land7_eq; lia).
    assert (LV : Z.land v 1 = v) by (assert (C : v = 0%Z \/ v = 1%Z) by lia; destruct C as [-> | ->]; reflexivity).

    ostep. ostep. ostep. ostep. ostep. ostep. rewrite ?L36. ostep. ostep. ostep. rewrite ?L32. ostep. ostep. ostep.

    do 15 zstep.

    ostep. ostep. lstep. ostep. ostep. ostep. lstep. ostep. ostep. ostep.

    ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. ostep.

    ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep.

    ostep. ostep. lstep. ostep. lstep. ostep. ostep. lstep. ostep. ostep. ostep. ostep. rewrite ?LV. ostep.
    apply evt_done. unfold consts_post. do 17 eexists.
    split; [unfold OD_HEAD; od_st_eq|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    eapply rw_cells_eq; [eassumption|]. unfold low_cells, fr_k32, fr_k128. cbn [app]. od_cells_eq.
  Qed.

  Lemma od_low_intro : forall (m : mem) vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344,
    rw_cells asegs m (oa_S1 E) (low_cells vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344) ->
    exists v344,
      (exists j0 j8 j16 j24, rw_cells asegs m (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]) /\
      rw_cells asegs m (oa_S1 E + 32) (fr_k32 vs6) /\
      (exists j104 j112 j120, rw_cells asegs m (oa_S1 E + 104) [CB 8 j104; CB 8 j112; CB 8 j120]) /\
      rw_cells asegs m (oa_S1 E + 128) (fr_k128 E) /\
      (exists j176, rw_cells asegs m (oa_S1 E + 176) [CB 8 j176]) /\
      rw_cells asegs m (oa_S1 E + 184) (fr_k184 E vs6 (v - 1) v248 v v312 v v344).
  Proof.
    intros m vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344 H.
    pose proof H as [[W _] _].
    unfold low_cells, fr_k32, fr_k128 in W. cbn [app cells_wf cell_wf] in W.
    assert (L344 : length j344 = 8%nat) by tauto.
    destruct (le8_surj j344 L344) as [v344 EV]. exists v344.
    assert (H' : rw_cells asegs m (oa_S1 E)
                   ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] ++ fr_k32 vs6 ++ [CB 8 j104; CB 8 j112; CB 8 j120] ++ fr_k128 E ++ [CB 8 j176]
                    ++ fr_k184 E vs6 (v - 1) v248 v v312 v v344)).
    { eapply rw_cells_recell; [exact H| | |].
      - unfold fr_k32, fr_k128, fr_k184. cbn [app cells_wf cell_wf]. tauto.
      - unfold low_cells, fr_k32, fr_k128, fr_k184, wz. cbn [app cells_bytes cbytes]. rewrite EV. reflexivity.
      - unfold low_cells, fr_k32, fr_k128, fr_k184. cbn [app cells_size csize]. reflexivity. }
    clear H. rename H' into H.
    apply rw_cells_app in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add] in H.
    replace (oa_S1 E + Z.of_nat 32)%Z with (oa_S1 E + 32)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H1 H]. unfold fr_k32 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (oa_S1 E + 32 + Z.of_nat 72)%Z with (oa_S1 E + 104)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H2 H]. cbn [cells_size csize Nat.add] in H.
    replace (oa_S1 E + 104 + Z.of_nat 24)%Z with (oa_S1 E + 128)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H3 H]. unfold fr_k128 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (oa_S1 E + 128 + Z.of_nat 48)%Z with (oa_S1 E + 176)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H4 H]. cbn [cells_size csize Nat.add] in H.
    replace (oa_S1 E + 176 + Z.of_nat 8)%Z with (oa_S1 E + 184)%Z in H by lia.
    split; [do 4 eexists; exact H0|]. split; [exact H1|]. split; [do 3 eexists; exact H2|]. split; [exact H3|]. split; [eexists; exact H4| exact H].
  Qed.

  Definition OD_REST (m1 : mem) : Prop :=
    rw_cells asegs m1 (oa_F E + 96) (od_parser_cells E) /\
    rw_cells asegs m1 (o_IMPL E) (dpi_cells E) /\
    (exists ws, u32arr asegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
    bytes_at asegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
    wr_at asegs m1 (o_SB E) (o_CAP E) /\
    ro_cells asegs m1 OD_DPI_VT od_vt_cells /\
    ro_cells asegs m1 OD_GOT_TABS od_got_cells /\
    mem_inv asegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono asegs (o_m0 E) m1 /\
    stk asegs m1 (o_lo E) (oa_S1 E).

  Ltac rest_open H :=
    let ws := fresh "ws" in
    destruct H as (PARS & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & VT & GOT & MI & MU & WM & ST);
    unfold od_parser_cells in PARS; unfold dpi_cells in DPI; unfold od_vt_cells, OD_DPI_VT in VT; unfold od_got_cells, OD_GOT_TABS in GOT; unfold od_W in MU;
    unfold wz in PARS, DPI;
    lazymatch type of BUFRO with
    | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
    end.
  Ltac rest_close :=
    unfold OD_REST, od_parser_cells, dpi_cells, od_vt_cells, od_got_cells, od_W, OD_DPI_VT, OD_GOT_TABS, idx_ok;
    split; [eassumption|]; split; [eassumption|];
    split; [ eexists; split; [eassumption| split; eassumption] | ];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; eassumption.

  Lemma ODINVg_intro : forall (m : mem) st vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344 j241 j252,
    rw_cells asegs m (oa_S1 E) (low_cells vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344) ->
    rw_cells asegs m (oa_F E + 192) (iter_cells E st j241 j252) ->
    OD_REST m ->
    exists v344, ODINVg E vs6 (v - 1) v248 v v312 v v344 st m.
  Proof.
    intros m st vs6 v v248 v312 j0 j8 j16 j24 j104 j112 j120 j176 j344 j241 j252 LOW ITER REST.
    destruct (od_low_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ LOW) as (v344 & H0 & H1 & H2 & H3 & H4 & H5). exists v344.
    destruct REST as (PARS & DPI & IDX & BUFRO & SBW & VT & GOT & MI & MU & WM & ST).
    unfold ODINVg.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [do 2 eexists; exact ITER|].
    split; [exact PARS|]. split; [exact DPI|]. split; [exact IDX|]. split; [exact BUFRO|]. split; [exact SBW|].
    split; [exact VT|]. split; [exact GOT|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
  Qed.

  Lemma od_invalid : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa6 xa7 xs2 xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j224 j232 j256 j264 j272 j280 j288 j296 j304 j320 j328 j336 j344 j241 j252,
    rw_cells asegs m1 (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (o_COPY E)); CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E + 96)); C8 (Z_to_bv 64 (oa_F E + 104)); CB 8 j224; CB 8 j232; C8 (Z_to_bv 64 (oa_F E / 8 + 2147450880)); C8 (Z_to_bv 64 1); CB 8 j256; CB 8 j264; CB 8 j272; CB 8 j280; CB 8 j288; CB 8 j296; CB 8 j304; C8 (Z_to_bv 64 0); CB 8 j320; CB 8 j328; CB 8 j336; CB 8 j344] ->
    rw_cells asegs m1 (oa_F E + 192) (iter_cells E st j241 j252) ->
    OD_REST m1 -> frm0 xfc -> od_exit_k E Q ->
    evt asegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                         xa0 xa1 (Z_to_bv 64 36) (Z_to_bv 64 0) (Z_to_bv 64 16) (Z_to_bv 64 32) xa6 xa7
                         xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) xs5 (Z_to_bv 64 0) xs7 (Z_to_bv 64 8) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x971b8) xfc None m1 (seg_rom asegs)).
  Proof using OK.
    intros until j252. intros LOW ITER REST FRM KX.
    od_env OK. pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    assert (SEP1 : (oa_F E + 512 <= oa_S1 E)%Z) by lia. assert (SEP2 : (0 <= oa_F E)%Z) by lia.
    pose proof REST as (_ & _ & _ & _ & _ & _ & _ & MI0 & MU0 & WM0 & _).
    unfold iter_cells in ITER. unfold wz in ITER.

    eapply evt_cut.
    { eapply evt_eq; [| eapply (od_consts 0 0 1 0 xra xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) xa0 xa1 xa6 xa7 xs2 (Z_to_bv 64 (oa_F E + 32)) xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1); [exact MI0| lia| lia| reflexivity| lia| exact LOW]].
      od_st_eq. }
    cbv beta. intros ms' P. unfold consts_post in P.
    destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q18 & q25 & q26 & q28 & q29 & m3 & -> & MUc & WMc & MIc & LOWc).
    clear LOW MI0 MU0 WM0.
    assert (REST3 : OD_REST m3).
    { rest_open REST. lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call asegs m m3 MUc WMc end. rest_close. }
    lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call asegs m m3 MUc WMc end.
    clear MUc WMc REST.
    assert (ITER' : rw_cells asegs m3 (oa_F E + 192) (iter_cells E st j241 j252)) by (unfold iter_cells, wz; exact ITER).
    destruct (ODINVg_intro m3 st 0 0 1 0 _ _ _ _ _ _ _ _ _ j241 j252 LOWc ITER' REST3) as [v344 INVH]. clear ITER'.
    clear LOWc ITER REST3 MIc.
    od_open_inv INVH. unfold OD_HEAD.

    zstep. if_true. zstep. zstep. if_true. zstep. lstep. zstep. zstep. zstep.
    od_cur_mem ltac:(fun mm => assert (INVA : ODINVg E 0 (-1) 1 0 0 0 0 st mm) by od_close_inv).
    eapply evt_eq; [| eapply (od_disp_err E OK Q st 0%Z (-1)%Z 1%Z 0%Z 0%Z 0%Z 0%Z); [exact FRM| exact INVA| intros xa0' xa1' xa2' xa3' xa4' xa5' xs11' m' INV']]; [unfold OD_DISP; od_st_eq|].
    unfold OD_PLUS.
    clear - INV' FRM KX0 OK.
    od_open_inv INV'. od_env OK.

    zstep. zstep. zstep. if_false. zstep. zstep. lstep. zstep. if_true. zstep. zstep. if_false. zstep.
    eapply evt_eq; [| eapply (KX0 st 0%Z (-1)%Z 1%Z 0%Z 0%Z 1%Z 0%Z); [exact FRM| od_close_inv]]. od_st_eq.
  Qed.

  Theorem od_iterate : forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    (tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET -> od_head_k E Q od_init) ->
    evt asegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (oa_F E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 96)) (Z_to_bv 64 (oa_F E + 192))
                         (Z_to_bv 64 (o_COPY E)) xs8 (Z_to_bv 64 (o_BUF E)) xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom asegs)).
  Proof using OK.
    intros Q xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 PRE FRM EM0 KX KH.
    destruct PRE as ((j0 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & j88 & j96 & j104 & j112 & j120 & j128 & j136 & j144 & j152 & j160 & j168 & j176 & j192 & j224 & j232 & j248 & j256 & j264 & j272 & j280 & j288 & j296 & j304 & j312 & j320 & j328 & j336 & j344 & FRL) & (junk & ITJ) & PARS & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & VT & GOT & MI & ST).
    od_env OK. unfold OD_ITER. unfold wz in FRL.
    unfold od_parser_cells in PARS. unfold dpi_cells in DPI. unfold od_vt_cells, OD_DPI_VT in VT. unfold od_got_cells, OD_GOT_TABS in GOT.
    unfold wz in PARS, DPI.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (od_W E) m1) as MU. pose proof (wmono_refl asegs m1) as WM. unfold od_W in MU.
    rewrite <- EM0 in MU at 1. rewrite <- EM0 in WM at 1.
    apply (rw_cells_split_CB asegs m1 _ [] 64 junk [] [8;8;8;8;8;8;1;7;4;4]%nat) in ITJ; [|reflexivity].
    cbn [mk_CB_cells app] in ITJ.
    repeat match type of ITJ with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in ITJ; clearbody j end.
    rename ITJ into ITER.

    ostep. ostep. ostep. ochkn. ostep. ostep.

    ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_false.

    ostep. ostep. ostep. ostep. lstep. ostep. lstep. lstep. ostep.

    ostep. odnorm. ostep. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true.

    pose proof (od_tokI_range E S1 0 ltac:(lia)) as TR0. pose proof (od_tokT_range E BOK 0) as CR0.
    pose proof (od_tokI_range E S1 (n + -1) ltac:(lia)) as TRL. pose proof (od_tokT_range E BOK (n + -1)) as CRL.
    pose proof (od_tokI_range E S1 n ltac:(lia)) as TRN.
    pose proof (od_tokI_range E S1 1 ltac:(lia)) as TR1. pose proof (od_tokT_range E BOK 1) as CR1.
    pose proof (tokT_n bs idxs S1) as TN0.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws 0 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI0;
                               pose proof (tokB_read mm E (tokI bs idxs 0) BUFRO ltac:(lia)) as RDB0).
    replace (o_IDX E + 4 * 0)%Z with (o_IDX E) in RDI0 by lia.
    fold (tokT bs idxs 0) in RDB0.
    set (c0 := tokT bs idxs 0) in *. set (off0 := tokI bs idxs 0) in *.

    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. ostep.
    if_cases K0; zify_cond K0.
    {
      ostep. ostep. lstep. ostep. lstep. ostep. ostep. ostep. ostep. ostep.
      apply (rw_cells_C8_C4 asegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 0) (Z_to_bv 64 1)) in ITER; [| exact od_le8_err_depth]. cbn [app] in ITER.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 0 1 0 true 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }

    ostep. ostep. ostep. ostep. if_true.

    ostep. ostep. ochk. ostep. ostep. ochk. ostep. ochk. ostep. odnorm. ostep. ostep. ostep. ostep.
    rewrite ?(Z.mod_small (n + -1) 4294967296) by lia.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (n + -1) IDXA (conj IDXL IDXF) ltac:(lia)) as RDIL;
                               pose proof (tokB_read mm E (tokI bs idxs (n + -1)) BUFRO ltac:(lia)) as RDBL;
                               pose proof (tokI_read mm E ws n IDXA (conj IDXL IDXF) ltac:(lia)) as RDIN;
                               pose proof (tokB_read mm E (tokI bs idxs n) BUFRO ltac:(lia)) as RDBN;
                               pose proof (tokI_read mm E ws 1 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI1;
                               pose proof (tokB_read mm E (tokI bs idxs 1) BUFRO ltac:(lia)) as RDB1).
    fold (tokT bs idxs (n + -1)) in RDBL. fold (tokT bs idxs n) in RDBN. fold (tokT bs idxs 1) in RDB1. rewrite TN0 in RDBN.
    replace (o_IDX E + 4 * 1)%Z with (o_IDX E + 4)%Z in RDI1 by lia.
    set (cl := tokT bs idxs (n + -1)) in *. set (offl := tokI bs idxs (n + -1)) in *.
    set (c1 := tokT bs idxs 1) in *. set (off1 := tokI bs idxs 1) in *. set (offn := tokI bs idxs n) in *.

    ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. ostep.
    if_cases KL; zify_cond KL.
    {
      ostep. lstep. ostep. ostep. lstep. ostep. ostep. ostep. lstep. lstep. ostep. ostep.
      apply (rw_cells_C8_C4 asegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 28) (Z_to_bv 64 0)) in ITER; [| exact od_le8_err28]. cbn [app] in ITER.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 1 0 28 false 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }
    assert (HLAST : tokT bs idxs (n - 1) = C_RBRACKET) by (replace (n - 1)%Z with (n + -1)%Z by lia; unfold C_RBRACKET; fold cl; lia).

    ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. ostep. if_true.

    ostep. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. lstep. ostep. ostep. ostep.
    assert (N2 : (2 <= n)%Z).
    { destruct (Z.eq_dec n 1) as [N1|N1]; [|lia]. exfalso.
      assert (EQ : cl = c0) by (unfold cl, c0; f_equal; lia). lia. }
    apply (rw_cells_C8_C4 asegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 0) (Z_to_bv 64 1)) in ITER; [| exact od_le8_err_depth]. cbn [app] in ITER.

    assert (K_FIN : forall st ya0 ya2 ya3 ya4 ya5 mm j241' j252' k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k128 k136 k144 k152 k168 k176 k224 k232 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344,
              (st = mkO 1 2 0 true 0 \/ (st = mkO 2 0 0 true 0 /\ c1 = 93%Z)) ->
              rw_cells asegs mm (oa_S1 E) [CB 8 k0; CB 8 k8; CB 8 k16; CB 8 k24; CB 8 k32; CB 8 k40; CB 8 k48; CB 8 k56; CB 8 k64; CB 8 k72; CB 8 k80; CB 8 k88; CB 8 k96; CB 8 k104; CB 8 k112; CB 8 k120; CB 8 k128; CB 8 k136; CB 8 k144; CB 8 k152; C8 (Z_to_bv 64 (o_COPY E)); CB 8 k168; CB 8 k176; C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E + 96)); C8 (Z_to_bv 64 (oa_F E + 104)); CB 8 k224; CB 8 k232; C8 (Z_to_bv 64 (oa_F E / 8 + 2147450880)); C8 (Z_to_bv 64 2); CB 8 k256; CB 8 k264; CB 8 k272; CB 8 k280; CB 8 k288; CB 8 k296; CB 8 k304; CB 8 k312; CB 8 k320; CB 8 k328; CB 8 k336; CB 8 k344] ->
              rw_cells asegs mm (oa_F E + 192)
                [C8 (Z_to_bv 64 (o_BUF E)); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)); C8 (Z_to_bv 64 (oa_F E + 96)); C8 (Z_to_bv 64 (o_SB E));
                 C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j241'; C4 (Z_to_bv 64 0); CB 4 j252'] ->
              OD_REST mm ->
              evt asegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                                   ya0 (Z_to_bv 64 (o_depth st)) ya2 ya3 ya4 ya5 xa6 xa7
                                   (Z_to_bv 64 (oa_F E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 96)) (Z_to_bv 64 (oa_F E + 192))
                                   (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (o_BUF E)) xs10 xs11 xt3 xt4 xt5 xt6)
                              xF (Z_to_bv 64 0x97044) xfc None mm (seg_rom asegs))).
    { intros st ya0 ya2 ya3 ya4 ya5 mm j241' j252' k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k128 k136 k144 k152 k168 k176 k224 k232 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 HST LOW2 ITER2 REST2.
      clear FRL ITER PARS DPI IDXA IDXL IDXF BUFRO SBW VT GOT MI MU WM ST RDI0 RDB0 RDIL RDBL RDIN RDBN RDI1 RDB1.
      rest_open REST2.
      assert (DR : (0 <= o_depth st <= 2)%Z) by (destruct HST as [->|[-> _]]; cbn; lia).
      assert (SEP1 : (oa_F E + 512 <= oa_S1 E)%Z) by lia. assert (SEP2 : (0 <= oa_F E)%Z) by lia.

      ostep. ostep. ostep. ostep. ostep. ostep. lstep. ostep.
      od_cur_mem ltac:(fun mm' => assert (REST3 : OD_REST mm') by rest_close).
      eapply evt_cut.
      { od_cur_mem ltac:(fun mm' => eapply evt_eq; [| eapply (od_consts (oa_F E + 192) 1 2 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm'); [assumption| lia| lia| lia| lia| eassumption]]).
        od_st_eq. }
      cbv beta. intros ms' P. unfold consts_post in P.
      destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q18 & q25 & q26 & q28 & q29 & mc3 & -> & MUc & WMc & MIc & LOWc).
      clear LOW2.
      clear REST3.
      lazymatch type of ITER2 with rw_cells _ ?m _ _ => transport_after_call asegs m mc3 MUc WMc end.
      clear MUc WMc.
      assert (REST4 : OD_REST mc3) by rest_close.
      assert (ITER3 : rw_cells asegs mc3 (oa_F E + 192) (iter_cells E st j241' j252')).
      { eapply rw_cells_eq; [exact ITER2|]. unfold iter_cells. destruct HST as [->|[-> _]]; od_cells_eq. }
      destruct (ODINVg_intro mc3 st (oa_F E + 192) 1 2 1 _ _ _ _ _ _ _ _ _ j241' j252' LOWc ITER3 REST4) as [v344 INVH].
      eapply evt_eq; [| eapply (KH HLAST st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc3); [| exact FRM| exact INVH]]; [od_st_eq|].
      left. unfold od_next_ok, od_head_ok, sbo_ok, od_init.
      pose proof (od_tokI_range E S1 (Z.min 1 n) ltac:(lia)). pose proof (od_tokI_range E S1 (Z.min 2 n) ltac:(lia)).
      destruct HST as [->|[-> HC1]]; cbn [o_pos o_depth o_err o_alive o_sbo].
      + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
        right; right. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| fold bs idxs; lia].
      + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
        right; left. split; [reflexivity|]. split; [reflexivity| lia]. }
    if_cases K1; zify_cond K1.
    -
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_FIN (mkO 1 2 0 true 0)); [left; reflexivity| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
    -
      ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_FIN (mkO 2 0 0 true 0)); [right; split; [reflexivity| lia]| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
  Qed.
End Begin.
