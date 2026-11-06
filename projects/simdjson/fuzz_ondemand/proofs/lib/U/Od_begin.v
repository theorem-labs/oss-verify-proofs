(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_plus Od_head Od_loop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition OD_PRE (E : odenv) (m1 : mem) : Prop :=
  (exists junk, rw_cells usegs m1 (FR E) [CB 288 junk]) /\
  rw_cells usegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells usegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr usegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at usegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at usegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells usegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells usegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x147c0); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv usegs m1 /\
  stk usegs m1 (o_lo E) (FR E).

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

Lemma od_shl32_shr32 : forall x, (0 <= x < 4294967296)%Z -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^32)%Z with 4294967296%Z.
  apply Z.div_mul. lia.
Qed.

Section Begin.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition low_cells (v144 v176 v184 v200 v208 : Z) (j24 j32 j40 j48 j88 j168 j216 : list byte) : list cell :=
    fr_k0 ++ [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] ++ fr_k56 ++ [CB 8 j88] ++ fr_k96 v144 ++ [CB 8 j168]
    ++ [C8 (wz v176); C8 (wz v184); C8 (wz 0x6c6c756e); C8 (wz v200); C8 (wz v208); CB 8 j216].

  Definition consts_post (xra : word) (vs2 vs5 vs6 vs7 : Z) (xs0 xs4 xs10 xs11 xt6 : word) (xF : bvmap 5 word) (xfc : bv 32) (m : mem)
      (j24 j32 j40 j48 j88 j168 j216 : list byte) : machine_state -> Prop :=
    fun ms' => exists xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 (m' : mem),
      ms' = MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                    xs0 (Z_to_bv 64 10) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 vs2) (Z_to_bv 64 18446744073709551615) xs4 (Z_to_bv 64 vs5) (Z_to_bv 64 vs6) (Z_to_bv 64 vs7) (Z_to_bv 64 122)
                    (Z_to_bv 64 4) xs10 xs11 xt3 xt4 xt5 xt6)
               xF (Z_to_bv 64 OD_HEAD) xfc None m' (seg_rom usegs)
      /\ munch [(FR E, bv_unsigned (o_sp E) + -272)%Z] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rw_cells usegs m' (FR E) (low_cells (vs6 - 1) (vs6 + 1) vs2 vs7 vs6 j24 j32 j40 j48 j88 j168 j216).

  Lemma od_consts : forall xra vs2 vs5 vs6 vs7 xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216,
    mem_inv usegs m1 -> (0 <= vs6 <= 1)%Z -> (0 <= vs2 <= 1)%Z -> (0 <= vs7 < 2^63)%Z ->
    rw_cells usegs m1 (FR E)
      [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104;
       CB 8 j112; CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 0); CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200;
       CB 8 j208; CB 8 j216] ->
    evt usegs (consts_post xra vs2 vs5 vs6 vs7 xs0 xs4 xs10 xs11 xt6 xF xfc m1 j24 j32 j40 j48 j88 j168 j216)
      (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 vs2) xs3 xs4 (Z_to_bv 64 vs5) (Z_to_bv 64 vs6) (Z_to_bv 64 vs7) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          xF (Z_to_bv 64 0x27708) xfc None m1 (seg_rom usegs)).
  Proof using OK.
    intros until j216. intros MI VS6 VS2 VS7 FRL.
    od_env OK.
    pose proof (munch_refl [(FR E, bv_unsigned (o_sp E) + -272)%Z] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    set (mm0 := m1) in MU at 1, WM at 1 |- * at 1.

    zstep. zstep. zstep. zstep. zstep. zstep.

    do 14 zstep.

    zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. zstep.

    zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep.

    zstep. zstep. lstep. zstep. lstep. zstep. zstep. rewrite wz_m1. zstep. zstep. lstep.

    zstep. zstep. zstep.
    apply evt_done. unfold consts_post. do 15 eexists.
    split; [unfold OD_HEAD; cbv delta [mkR]; reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    eapply rw_cells_eq; [eassumption|]. unfold low_cells, fr_k0, fr_k56, fr_k96, K104, K112. cbn [app]. od_cells_eq.
  Qed.

  Lemma od_low_split : forall (m : mem) v144 v176 v184 v200 v208 v216 j24 j32 j40 j48 j88 j168,
    rw_cells usegs m (FR E)
      (fr_k0 ++ [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] ++ fr_k56 ++ [CB 8 j88] ++ fr_k96 v144 ++ [CB 8 j168] ++ fr_k176 v176 v184 v200 v208 v216) ->
    rw_cells usegs m (FR E) fr_k0 /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -472)%Z [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -440)%Z fr_k56 /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -408)%Z [CB 8 j88] /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -400)%Z (fr_k96 v144) /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -328)%Z [CB 8 j168] /\
    rw_cells usegs m (bv_unsigned (o_sp E) + -320)%Z (fr_k176 v176 v184 v200 v208 v216).
  Proof.
    intros m v144 v176 v184 v200 v208 v216 j24 j32 j40 j48 j88 j168 H.
    apply rw_cells_app in H. destruct H as [H0 H]. unfold fr_k0 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (FR E + Z.of_nat 24)%Z with (bv_unsigned (o_sp E) + -472)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -472 + Z.of_nat 32)%Z with (bv_unsigned (o_sp E) + -440)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H2 H]. unfold fr_k56 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -440 + Z.of_nat 32)%Z with (bv_unsigned (o_sp E) + -408)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H3 H]. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -408 + Z.of_nat 8)%Z with (bv_unsigned (o_sp E) + -400)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H4 H]. unfold fr_k96 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -400 + Z.of_nat 72)%Z with (bv_unsigned (o_sp E) + -328)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H5 H]. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -328 + Z.of_nat 8)%Z with (bv_unsigned (o_sp E) + -320)%Z in H by lia.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| exact H].
  Qed.

  Lemma od_low_216 : forall (m : mem) v144 v176 v184 v200 v208 j24 j32 j40 j48 j88 j168 j216,
    rw_cells usegs m (FR E) (low_cells v144 v176 v184 v200 v208 j24 j32 j40 j48 j88 j168 j216) ->
    exists v216, rw_cells usegs m (FR E)
      (fr_k0 ++ [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] ++ fr_k56 ++ [CB 8 j88] ++ fr_k96 v144 ++ [CB 8 j168] ++ fr_k176 v176 v184 v200 v208 v216).
  Proof.
    intros m v144 v176 v184 v200 v208 j24 j32 j40 j48 j88 j168 j216 H.
    pose proof H as [[W _] _].
    unfold low_cells, fr_k0, fr_k56, fr_k96 in W. cbn [app cells_wf cell_wf] in W.
    assert (L216 : length j216 = 8%nat) by tauto.
    destruct (le8_surj j216 L216) as [v EV]. exists v.
    eapply rw_cells_recell; [exact H| | |].
    - unfold low_cells, fr_k0, fr_k56, fr_k96, fr_k176. cbn [app cells_wf cell_wf]. tauto.
    - unfold low_cells, fr_k0, fr_k56, fr_k96, fr_k176, wz. cbn [app cells_bytes cbytes]. rewrite EV. reflexivity.
    - unfold low_cells, fr_k0, fr_k56, fr_k96, fr_k176. cbn [app cells_size csize]. reflexivity.
  Qed.

  Definition OD_REST (m1 : mem) : Prop :=
    rw_cells usegs m1 (FR_PA E) (od_parser_cells E) /\
    rw_cells usegs m1 (bv_unsigned (o_sp E) + -152)%Z (o_hi E) /\
    rw_cells usegs m1 (o_IMPL E) (dpi_cells E) /\
    (exists ws, u32arr usegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
    bytes_at usegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
    wr_at usegs m1 (o_SB E) (o_CAP E) /\
    (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells usegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
    rw_cells usegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x147c0); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
    mem_inv usegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono usegs (o_m0 E) m1 /\
    stk usegs m1 (o_lo E) (FR E).

  Ltac rest_open H :=
    let ws := fresh "ws" in
    let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
    let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
    destruct H as (PARS & FRHI & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
    unfold od_parser_cells in PARS; unfold dpi_cells in DPI; unfold od_vt_cells, OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT; unfold od_W in MU;
    unfold wz in PARS, DPI, VT, GOT;
    lazymatch type of BUFRO with
    | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
    end.
  Ltac rest_close :=
    unfold OD_REST, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [ eexists; split; [eassumption| split; eassumption] | ];
    split; [eassumption|]; split; [eassumption|];
    split; [ do 9 eexists; eassumption | ];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

  Lemma ODINVg_intro : forall (m : mem) st v144 v176 v184 v200 v208 v216 j24 j32 j40 j48 j88 j168 j273 j284,
    rw_cells usegs m (FR E)
      (fr_k0 ++ [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] ++ fr_k56 ++ [CB 8 j88] ++ fr_k96 v144 ++ [CB 8 j168] ++ fr_k176 v176 v184 v200 v208 v216) ->
    rw_cells usegs m (FR_IT E) (iter_cells E st j273 j284) ->
    OD_REST m ->
    ODINVg E v144 v176 v184 v200 v208 v216 st m.
  Proof.
    intros m st v144 v176 v184 v200 v208 v216 j24 j32 j40 j48 j88 j168 j273 j284 LOW ITER REST.
    apply od_low_split in LOW. destruct LOW as (H0 & H1 & H2 & H3 & H4 & H5 & H6).
    destruct REST as (PARS & FRHI & DPI & IDX & BUFRO & SBW & VT & GOT & MI & MU & WM & ST).
    unfold ODINVg.
    split; [exact H0|]. split; [do 4 eexists; exact H1|]. split; [exact H2|]. split; [eexists; exact H3|]. split; [exact H4|].
    split; [eexists; exact H5|]. split; [exact H6|]. split; [do 2 eexists; exact ITER|].
    split; [exact PARS|]. split; [exact FRHI|]. split; [exact DPI|]. split; [exact IDX|]. split; [exact BUFRO|]. split; [exact SBW|].
    split; [exact VT|]. split; [exact GOT|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
  Qed.

  Ltac gok := first [ if_true | uok ].
  Ltac gtrap := first [ if_false | utrap ].

  Lemma od_invalid : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216 j273 j284,
    rw_cells usegs m1 (FR E)
      [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104;
       CB 8 j112; CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 0); CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200;
       CB 8 j208; CB 8 j216] ->
    rw_cells usegs m1 (FR_IT E) (iter_cells E st j273 j284) ->
    OD_REST m1 -> frm0 xfc -> od_exit_k E Q ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 0) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x27708) xfc None m1 (seg_rom usegs)).
  Proof using OK.
    intros until j284. intros LOW ITER REST FRM KX.
    od_env OK. pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    rest_open REST. unfold iter_cells in ITER. unfold wz in ITER.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).

    eapply evt_cut.
    { od_cur_mem ltac:(fun mm => eapply (od_consts xra 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm); [assumption| lia| lia| lia| eassumption]). }
    cbv beta. intros ms' P. unfold consts_post in P.
    destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & m3 & -> & MUc & WMc & MIc & LOWc).
    clear LOW.
    lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call usegs m m3 MUc WMc end.
    clear MUc WMc.
    unfold low_cells, fr_k0, fr_k56, fr_k96, wz in LOWc. cbn [app] in LOWc. unfold OD_HEAD.

    zstep. if_true. zstep. zstep. if_true. lstep. zstep. zstep. zstep.

    od_cur_mem ltac:(fun mm => assert (INVA : ODINVg E (-1) 1 0 0 0 0 st mm)).
    { eapply ODINVg_intro; [| unfold iter_cells, wz; eassumption| rest_close].
      eapply rw_cells_eq; [eassumption|]. unfold fr_k0, fr_k56, fr_k96, fr_k176, K104, K112. cbn [app]. od_cells_eq. }
    eapply evt_eq; [| eapply (od_disp_err E OK Q st (-1)%Z 1%Z 0%Z 0%Z 0%Z 0%Z); [exact FRM| exact INVA| intros xa0' xa1' xa2' xs11' m' INV']]; [unfold OD_DISP; od_st_eq|].
    unfold OD_PLUS.
    clear - INV' FRM KX0 OK.
    od_open_inv INV'.

    zstep. zstep. zstep. zstep. if_true. zstep. if_true. zstep. zstep. if_false. zstep.
    eapply evt_eq; [| eapply (KX0 st (-1)%Z 1%Z 0%Z 0%Z 0%Z 0%Z); [exact FRM| od_close_inv]]. od_st_eq.
  Qed.

  Hypothesis ARM_STR  : arm_stmt E 0x27ab4.
  Hypothesis ARM_BOOL : arm_stmt E 0x27af4.
  Hypothesis ARM_ARR  : arm_stmt E 0x27884.
  Hypothesis ARM_I64  : arm_stmt E 0x27a74.
  Hypothesis ARM_DBL  : arm_stmt E 0x279b0.
  Hypothesis ARM_OBJ  : arm_stmt E 0x27a00.
  Hypothesis ARM_U64  : arm_stmt E 0x27b34.
  Hypothesis ARM_RAW  : arm_stmt E 0x27b74.
  Hypothesis ARM_NULL : arm_stmt E 0x27bb4.
  Hypothesis ARM_NEST : arm_stmt E 0x2793c.

  Ltac cells_split_at H k :=
    lazymatch type of H with
    | rw_cells _ _ _ ?cs =>
        let l1 := eval cbv beta iota delta [firstn] in (firstn k cs) in
        let l2 := eval cbv beta iota delta [skipn] in (skipn k cs) in
        change cs with (l1 ++ l2) in H
    end.

  Theorem od_iterate : forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (o_len E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_BUF E)) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom usegs)).
  Proof using OK OKU ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 PRE FRM EM0 KX.
    destruct PRE as ((junk & FRJ) & PARS & FRHI & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & ST).
    od_env OK. od_envu OKU. unfold OD_ITER.
    destruct UIDX as [UIDX0 UIDX4]. destruct UIMPL as [UIMPL0 UIMPL8].
    pose proof (od_al_pa E OKU) as A8p.
    unfold od_parser_cells in PARS. unfold dpi_cells in DPI. unfold od_vt_cells, OD_DPI_VPTR in VT. unfold OD_GOT_TABS in GOT.
    unfold wz in PARS, DPI, VT, GOT.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (od_W E) m1) as MU. pose proof (wmono_refl usegs m1) as WM. unfold od_W in MU.
    rewrite <- EM0 in MU at 1. rewrite <- EM0 in WM at 1.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).

    apply (rw_cells_split_CB usegs m1 _ [] 288 junk []
             [8;8;8; 8;8;8;8; 8;8;8;8; 8; 8;8;8;8;8;8;8;8;8; 8; 8;8;8;8;8;8; 8;8;8;8; 8; 8; 1;7; 4;4]%nat) in FRJ; [|reflexivity].
    cbn [mk_CB_cells app] in FRJ.
    repeat match type of FRJ with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRJ; clearbody j end.

    zstep. zstep. gok. zstep. ual. zstep. gok.
    zstep. zstep. gok. zstep. ual. zstep. gok. zstep. zstep. gok.

    zstep. zstep. zstep. zstep.

    zstep. zstep. zstep. zstep. lstep. zstep. lstep. lstep.

    cells_split_at FRJ 28%nat. apply rw_cells_app in FRJ. destruct FRJ as [LOW ITER]. cbn [cells_size csize Nat.add] in ITER.
    replace (FR E + Z.of_nat 224)%Z with (FR_IT E) in ITER by lia.
    apply (rw_cells_C8_C4 usegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 0) (Z_to_bv 64 1)) in ITER; [| exact od_le8_err_depth]. cbn [app] in ITER.

    pose proof (od_tokI_range E S1 0 ltac:(lia)) as TR0. pose proof (od_tokT_range E BOK 0) as CR0.
    pose proof (od_tokI_range E S1 (n - 1) ltac:(lia)) as TRL. pose proof (od_tokT_range E BOK (n - 1)) as CRL.
    pose proof (od_tokI_range E S1 n ltac:(lia)) as TRN.
    pose proof (od_tokI_range E S1 1 ltac:(lia)) as TR1. pose proof (od_tokT_range E BOK 1) as CR1.
    pose proof (tokT_n bs idxs S1) as TN0.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws 0 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI0;
                               pose proof (tokB_read mm E (tokI bs idxs 0) BUFRO ltac:(lia)) as RDB0).
    replace (o_IDX E + 4 * 0)%Z with (o_IDX E) in RDI0 by lia.
    fold (tokT bs idxs 0) in RDB0.
    set (c0 := tokT bs idxs 0) in *. set (off0 := tokI bs idxs 0) in *.

    zstep. odnorm. zstep. zstep. gok. zstep. zstep. zstep. unz. zstep. gok. zstep. gok.
    zstep. odnorm. zstep. lstep. zstep.
    od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
    if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply (od_invalid Q (mkO 0 1 0 true 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }
    clear REST.

    zstep. gok. zstep. zstep. gok. zstep. zstep. zstep. zstep. gok. zstep. ual. zstep. gok.
    zstep. odnorm. zstep. gok.

    zstep. zstep. zstep. zstep.
    rewrite (Z.mod_small (n + -1) 4294967296) by lia.
    zstep.
    eapply evt_eq; [| eapply (od_opidx E OK OKU Q (n - 1) 0x27558); [exact DPI| lia| lia| reflexivity| intros xa1' xa2' xa3' xa4']]; [unfold OD_OPIDX_; od_st_eq|].
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (n - 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RDIL;
                               pose proof (tokB_read mm E (tokI bs idxs (n - 1)) BUFRO ltac:(lia)) as RDBL;
                               pose proof (tokI_read mm E ws n IDXA (conj IDXL IDXF) ltac:(lia)) as RDIN;
                               pose proof (tokB_read mm E (tokI bs idxs n) BUFRO ltac:(lia)) as RDBN;
                               pose proof (tokI_read mm E ws 1 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI1;
                               pose proof (tokB_read mm E (tokI bs idxs 1) BUFRO ltac:(lia)) as RDB1).
    fold (tokT bs idxs (n - 1)) in RDBL. fold (tokT bs idxs n) in RDBN. fold (tokT bs idxs 1) in RDB1. rewrite TN0 in RDBN.
    replace (o_IDX E + 4 * 1)%Z with (o_IDX E + 4)%Z in RDI1 by lia.
    set (cl := tokT bs idxs (n - 1)) in *. set (offl := tokI bs idxs (n - 1)) in *.
    set (c1 := tokT bs idxs 1) in *. set (off1 := tokI bs idxs 1) in *. set (offn := tokI bs idxs n) in *.

    zstep. zstep. odnorm. zstep. zstep. gok. zstep. zstep. zstep. unz. zstep. gok. zstep. gok.
    zstep. odnorm. zstep. zstep.
    if_cases KL; zify_cond KL.
    {
      zstep. zstep. lstep. lstep. zstep. gok. zstep. zstep. zstep. zstep. zstep. lstep. zstep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 1 0 28 false 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }
    assert (HLAST : tokT bs idxs (n - 1) = C_RBRACKET) by (unfold C_RBRACKET; fold cl; lia).

    zstep. zstep. gok. zstep. ual. zstep. gok.
    zstep. zstep. gok. zstep. ual. zstep. gok.
    zstep. odnorm. zstep. zstep.
    eapply evt_eq; [| eapply (od_opidx E OK OKU Q n 0x275d0); [exact DPI| lia| lia| reflexivity| intros xa1'' xa2'' xa3'' xa4'']]; [unfold OD_OPIDX_; od_st_eq|].

    zstep. zstep. odnorm. zstep. zstep. gok. zstep. zstep. zstep. unz. zstep. gok. zstep. gok.
    zstep. odnorm. zstep. zstep. if_true.

    zstep. zstep. gok. zstep. zstep. gok. zstep. odnorm. zstep. zstep. gok.

    zstep. zstep. odnorm. zstep. zstep. gok. zstep. zstep. zstep. unz. zstep. gok. zstep. gok.
    zstep. odnorm. zstep. zstep.
    assert (N2 : (2 <= n)%Z).
    { destruct (Z.eq_dec n 1) as [N1|N1]; [|lia]. exfalso.
      assert (EQ : cl = c0) by (unfold cl, c0; f_equal; lia). lia. }

    assert (K_C4 : forall st ya0 ya2 ya3 ya4 yra mm j273' j284' jj0 jj8 jj16 jj24 jj32 jj40 jj48 jj56 jj64 jj72 jj80 jj88 jj96 jj104 jj112 jj120 jj128 jj144 jj152 jj160 jj168
                            jj176 jj184 jj192 jj200 jj208 jj216,
              (st = mkO 1 2 0 true 0 \/ (st = mkO 2 0 0 true 0 /\ c1 = 93%Z)) ->
              rw_cells usegs mm (FR E)
                [CB 8 jj0; CB 8 jj8; CB 8 jj16; CB 8 jj24; CB 8 jj32; CB 8 jj40; CB 8 jj48; CB 8 jj56; CB 8 jj64; CB 8 jj72; CB 8 jj80; CB 8 jj88; CB 8 jj96; CB 8 jj104;
                 CB 8 jj112; CB 8 jj120; CB 8 jj128; C8 (Z_to_bv 64 0); CB 8 jj144; CB 8 jj152; CB 8 jj160; CB 8 jj168; CB 8 jj176; CB 8 jj184; CB 8 jj192; CB 8 jj200;
                 CB 8 jj208; CB 8 jj216] ->
              rw_cells usegs mm (FR_IT E)
                [C8 (Z_to_bv 64 (o_BUF E)); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)); C8 (Z_to_bv 64 (FR_PA E)); C8 (Z_to_bv 64 (o_SB E));
                 C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j273'; C4 (Z_to_bv 64 0); CB 4 j284'] ->
              OD_REST mm ->
              evt usegs Q (MS (mkR yra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (o_IDX E + 4))
                                   ya0 (Z_to_bv 64 (o_depth st)) ya2 ya3 ya4 xa5 xa6 xa7
                                   (Z_to_bv 64 (o_BUF E)) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) xs6 (Z_to_bv 64 (o_IDX E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                              xF (Z_to_bv 64 0x276f8) xfc None mm (seg_rom usegs))).
    { intros st ya0 ya2 ya3 ya4 yra mm j273' j284' jj0 jj8 jj16 jj24 jj32 jj40 jj48 jj56 jj64 jj72 jj80 jj88 jj96 jj104 jj112 jj120 jj128 jj144 jj152 jj160 jj168
             jj176 jj184 jj192 jj200 jj208 jj216 HST LOW2 ITER2 REST2.
      clear LOW ITER PARS FRHI DPI IDXA IDXL IDXF BUFRO SBW VT GOT MI MU WM ST RDI0 RDB0 RDIL RDBL RDIN RDBN RDI1 RDB1.
      rest_open REST2.
      assert (DR : (0 <= o_depth st <= 2)%Z) by (destruct HST as [->|[-> _]]; cbn; lia).

      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { od_cur_mem ltac:(fun mm' => eapply evt_eq; [| eapply (od_consts yra 1 (FR_IT E) 1 (o_IDX E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm'); [assumption| lia| lia| lia| eassumption]]).
        od_st_eq. }
      cbv beta. intros ms' P. unfold consts_post in P.
      destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & mc3 & -> & MUc & WMc & MIc & LOWc).
      clear LOW2.
      lazymatch type of ITER2 with rw_cells _ ?m _ _ => transport_after_call usegs m mc3 MUc WMc end.
      clear MUc WMc.
      destruct (od_low_216 _ _ _ _ _ _ _ _ _ _ _ _ _ LOWc) as [v216 LOWd]. clear LOWc.

      eapply evt_eq; [| eapply (od_loop E OK OKU HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST Q KX
                                        (Z.to_nat (n + 1)) od_init st v216)]; [od_st_eq| | | exact FRM|].
      - unfold o_left. destruct HST as [->|[-> _]]; cbn [o_pos]; lia.
      - left. unfold od_next_ok, od_head_ok, sbo_ok, od_init.
        pose proof (od_tokI_range E S1 (Z.min 1 n) ltac:(lia)). pose proof (od_tokI_range E S1 (Z.min 2 n) ltac:(lia)).
        destruct HST as [->|[-> HC1]]; cbn [o_pos o_depth o_err o_alive o_sbo].
        + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
          right; right. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| fold bs idxs; lia].
        + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
          right; left. split; [reflexivity|]. split; [reflexivity| lia].
      - eapply ODINVg_intro; [| | rest_close].
        + eapply rw_cells_eq; [exact LOWd|]. replace (1 - 1)%Z with 0%Z by lia. replace (1 + 1)%Z with 2%Z by lia. reflexivity.
        + eapply rw_cells_eq; [eassumption|]. unfold iter_cells. destruct HST as [->|[-> _]]; od_cells_eq. }
    if_cases K1; zify_cond K1.
    -
      zstep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_C4 (mkO 1 2 0 true 0)); [left; reflexivity| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
    -
      zstep. zstep. gok. zstep. gok. zstep. zstep. gok. zstep. zstep. zstep. zstep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_C4 (mkO 2 0 0 true 0)); [right; split; [reflexivity| lia]| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
  Qed.
End Begin.
