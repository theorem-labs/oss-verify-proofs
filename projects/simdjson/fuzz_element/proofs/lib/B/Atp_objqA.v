(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem
     Sj_num_aframe I_lkit Atp_defsA Atp_kitA Atp_arrlA Atp_elemA Atp_elemxA Atp_objdA Atp_objfA Atp_objpA Atp_objkA Atp_objsA Atp_objuA Atp_objkwA Atp_objkyA
     Atp_arrA Atp_objbA Atp_objgA Atp_objxA Atp_objmA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma cb8_c8 : forall (m : mem) A pre post bs, rw_cells bsegs m A (pre ++ CB 8 bs :: post) -> rw_cells bsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. intros. apply num_cb8_c8. assumption. Qed.

Lemma loc72_of_raw : forall (m : mem) b (j0 : list byte) (f out : Z) rest,
  rw_cells bsegs m b (CB 40 j0 :: C8 (Z_to_bv 64 f) :: C8 (Z_to_bv 64 out) :: C8 (Z_to_bv 64 f) :: C8 (Z_to_bv 64 f) :: rest) ->
  exists (j0' : list byte) (w24 w32 : word), rw_cells bsegs m b (obj_loc72 j0' w24 w32 f out ++ rest).
Proof.
  intros m b j0 f out rest H.
  apply (rw_cells_split_CB bsegs _ _ [] 40 j0 _ [24; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ (CB 24 ?ja :: CB 8 ?jb :: CB 8 ?jc :: _) =>
    apply (cb8_c8 m b [CB 24 ja] _ jb) in H; cbn [app] in H; apply (cb8_c8 m b [CB 24 ja; C8 (le_bytes_to_word jb)] _ jc) in H; cbn [app] in H;
    exists ja, (le_bytes_to_word jb), (le_bytes_to_word jc) end.
  unfold obj_loc72. cbn [app]. exact H.
Qed.
Lemma zeros16_words : repeat (Z_to_bv 8 0) 16 = le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).
Proof. reflexivity. Qed.

Lemma obj_node_elem : forall (T S : Z -> Z) (sn : Z) (d : nat) (i e c : Z),
  ttype (T i) = t_obj -> tnext (T i) = e + 1 -> T e = tword t_obj_end i -> tiles (field T S sn (elem T S sn ck_any d)) (i + 1) e c -> 0 <= T i ->
  elem T S sn ck_any (Datatypes.S d) i (e + 1).
Proof.
  intros T S sn d i e c TY NXT CLOSE TILES W0.
  apply (elem_object T S sn ck_any d i e c (tcount (T i))); [| rewrite <- NXT; exact (tword_decomp _ _ W0 TY)| exact CLOSE| exact TILES].
  unfold ck_any, tcount, CNT_MAX. change (2 ^ 24) with 16777216. pose proof (Z.mod_pos_bound (T i / 2 ^ 32) 16777216 ltac:(lia)). lia.
Qed.

Ltac xport_coreX H AG tac :=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of AG with agree_on _ _ ?m' =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m')
        by (eapply agree_sub; [exact AG|]; intros ? Hx;
            cbn [cells_size csize Nat.add length obj_hdrB obj_saved obj_loc72 obj_locB obj_sh pz obj_shF obj_hdrR atkey_frame atkey_saved app] in Hx; cbv beta; tac Hx);
      apply (fun X => rw_cells_agree_nw bsegs m m' A cs X Q) in H; clear Q
    end end.
Tactic Notation "xportx_stack" hyp(H) constr(AG) :=
  xport_coreX H AG ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| flia]).
Tactic Notation "xportx_frame" hyp(H) constr(AG) constr(HinF) :=
  xport_coreX H AG ltac:(fun Hx => split; [right; right; right; left; eexists _, 1%nat; split; [exact HinF| rewrite fs1; flia]| flia]).
Tactic Notation "xportx_shadow" hyp(H) constr(AG) constr(HinF) :=
  xport_coreX H AG ltac:(fun Hx => split; [right; right; right; right; eexists _, 1%nat; split; [exact HinF| rewrite fs1s; flia]| flia]).
Ltac mportx H MU WM :=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of MU with munch ?W m ?m' =>
      let H2 := fresh "MP" in
      pose proof (rw_cells_transport bsegs W m m' A cs H MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_hdrB obj_saved obj_loc72 obj_locB obj_sh pz obj_shF obj_hdrR atkey_frame atkey_saved app fst snd];
                          unfold shad, SHB, atkey_W in *; flia)) as H2;
      clear H; rename H2 into H
    end end.

Section ObjQ.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Hypothesis FIN : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 : Z) (js4 j0 : list byte) (cM : list cell),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) -> rw_cells bsegs m (oi_b I + 72) cM -> cells_size cM = 80%nat ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> out_recA E m (oi_out I) ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb8bc0) fc None m (seg_rom bsegs)).
  Hypothesis NOESC : forall (m : mem) (x5 x6 x7 xa4 xa5 a6 a7 y7 y8 y9 y10 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl Lk L0 L : Z) (rest : list Z) (v4 v5 v6 : Z) (js4 jo j0 jC j2 : list byte) (w24 w32 : word),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl = 18446744073709551615 /\ Lk = L0) \/ (0 <= sl < L0 /\ Lk = sl)) ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) [CB 24 jC] ->
    rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) ->
    rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR (wz 0xb8904) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (oi_b I + 72)) (wz (oi_node I)) (wz (oi_P I + 1)) (wz Lk) xa4 xa5 a6 a7
               (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) (wz L) (wz (oi_P I)) y7 y8 y9 y10 (wz 2147450880) x28 x29 x30 x31)
          F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs)).
  Hypothesis HSSO : esc_sso_stmt RT E d PMc Σ Σ1 I.
  Hypothesis HHEAP : esc_heap_stmt RT E d PMc Σ Σ1 I.

  Lemma obj_mid : forall (m : mem) (x5 x6 x7 xa1 xa2 xa3 xa4 xa5 a6 a7 y7 y8 y9 y10 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl L0 L : Z) (rest : list Z) (js4 jo j0 jB jF : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_locB j0 jB (oi_f I) (oi_out I) (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 L0)) ->
    rw_cells bsegs m (oi_f I + 24) [CB 96 jF] -> rw_cells bsegs m (shad (oi_f I)) (obj_sh (-8) (-8) (-8) js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR (wz 0xb87f8) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz sl) xa1 xa2 xa3 xa4 xa5 a6 a7
               (wz (oi_out I)) (wz (shad (oi_f I))) (wz (oi_node I)) (wz L) (wz (oi_P I)) y7 y8 y9 y10 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb87f8) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM FIN NOESC HSSO HHEAP.
    intros until jF. intros OB FRM EPTR ZL0 SLR NODE LOC FREST SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 432 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    assert (EL1i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL1; auto).
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    assert (NE : ptr <> []) by (rewrite EPTR; discriminate).
    pose proof (lvl_ptr_range E OK P ptr PAT NE) as (PB0 & PB1 & PB2 & PB3).
    pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT NE) as INPB.
    rewrite EPTR, zlength_cons in PB2. pose proof (zlength_nonneg rest) as ZLN.
    assert (PR47 : 0 < P /\ P + 1 + L0 < 2^47) by (clear - PB0 PB1 PB2 PB3 ZL0 ZLN LOW HL HT; ul).

    assert (FPW : fp_ok RT Σ1 (ae_lo E) (obj_WL b)) by (unfold obj_WL; constructor; [left; cbn [fst snd]; ul| constructor]).
    assert (ARTW : forall m1 m', ART RT Σ1 m1 -> munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> ART RT Σ1 m').
    { intros m1 m' A1 MU WM. exact (art_of_munch RT AF Σ1 m1 m' (ae_lo E) _ A1 ltac:(rewrite ES1; exact LWIN) FPW MU WM). }
    assert (SHBW : forall m1, ART RT Σ1 m1 -> forall m', munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> shb_cells m')
      by (intros m1 A1 m' MU WM; exact (shb_cells_of_art RT AF Σ1 m' (ARTW m1 m' A1 MU WM))).
    assert (SHZLW : forall m1, ART RT Σ1 m1 -> forall m', munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> shz m' b 152).
    { intros m1 A1 m' MU WM. apply (shz_stack RT AF Σ1 m' b 152 (ARTW m1 m' A1 MU WM)); [rewrite ES1; ul| ul| clear - B32; Z.div_mod_to_equations; lia| reflexivity| lia]. }
    assert (LKX : exists Lk, (sl = 18446744073709551615 /\ Lk = L0) \/ (0 <= sl < L0 /\ Lk = sl))
      by (destruct SLR as [S1|S1]; [exists L0; left| exists sl; right]; lia).
    destruct LKX as (Lk & SL).
    assert (LKR : 0 <= Lk <= L0) by (clear - SL ZLN ZL0; lia).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p3 E OK _ m F fc q b out node P f (P + 1) L0 sl Lk L);
      [exact MI| exact ST| exact LO| flia| flia| exact B32| exact QHI| flia| clear - PB0 PB1; lia| clear - ZLN ZL0; lia| clear - PB0 PB1 PB2 PB3 ZL0 LOW HL HT; ul| exact SL| exact LOC
      | exact (SHBW m ART0)| exact (SHZLW m ART0)|].
    intros m1 ya3 ya4 ya5 jB' MU1 WM1 MI1 ST1 LOC1. apply evt_done.
    pose proof (ARTW m m1 ART0 MU1 WM1) as ART1.
    assert (OW1 : Forall (ownW I) (obj_WL b)) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 (proj1 OB0) EF1 EL1i ES1 MU1 WM1 MI1 OW1) as OBK1.
    unfold obj_WL in MU1.
    mportx NODE MU1 WM1. mportx SH MU1 WM1. mportx OUT MU1 WM1.
    pose proof (rw_cells_transport bsegs _ m m1 _ _ FREST MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; flia)) as FREST1. clear FREST. rename FREST1 into FREST.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m1 b ES1 ST1 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK1. fold b in COK1.

    pose proof LOC1 as CH.
    apply (proj1 (rw_cells_app bsegs m1 _ [_; _; _; _; _] _)) in CH. destruct CH as [_ CH]. cbn [cells_size csize Nat.add] in CH.
    replace (b + Z.of_nat 72) with (b + 72) in CH by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 48 jB' _ [24; 16; 8]%nat) in CH; [| reflexivity]. cbn [mk_CB_cells app] in CH.
    apply (proj1 (rw_cells_app bsegs m1 _ [_] _)) in CH. destruct CH as [_ CH]. cbn [cells_size csize Nat.add] in CH.
    replace (b + 72 + Z.of_nat 24) with (b + 96) in CH by lia.
    apply (proj1 (rw_cells_app bsegs m1 _ [_; _] _)) in CH. destruct CH as [CH _]. cbn [cells_size csize Nat.add] in CH.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (b + 96) 16 (Z_to_bv 8 0) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART1| exact MI1| exact COK1|].
    { apply (checked_dst_stack RT AF Σ1 m1 _ (b + 96) 16 ART1); [rewrite ES1; ul| ul| rewrite EU; lia|].
      apply (wr_at_sub m1 (b + 96) 24 (b + 96) 16 (proj2 CH)); lia. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. rewrite (ret_pc_even 0xb8824) by lia. change (Z.to_nat 16) with 16%nat in BY2.
    assert (NCL2 : forall a, b + 96 <= a < b + 96 + 16 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24).
    { intros a Ha Hc. exfalso. destruct (obj_split RT AF E d Σ Σ1 I CTX Σ1 m1 a ART1 EF1 EL1i ES1 Hc); flia. }
    pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 b (b + 96) 16 m1 m2 OBK1 EF1 EL1i ES1 ART2 MI2 ltac:(unfold oi_b; lia) PR2 NCL2
                  ltac:(left; unfold oi_b; flia) ltac:(right; left; unfold oi_b; flia)) as OBK2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (b + 96 <= x < b + 96 + 16)) PR2 (fun x H => H)) as AG.
    clear CH. xportx_stack NODE AG. xportx_frame FREST AG HinF. xportx_shadow SH AG HinF. xportx_stack OUT AG.

    assert (LOC2 : exists (jC j2 : list byte), rw_cells bsegs m2 b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 (repeat (Z_to_bv 8 0) 16); CB 8 j2;
                           C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)]).
    { apply (rw_cells_split_CB bsegs _ _ [_; _; _; _; _] 48 jB' _ [24; 16; 8]%nat) in LOC1; [| reflexivity]. cbn [mk_CB_cells app] in LOC1.
      lazymatch type of LOC1 with rw_cells _ _ _ [_; _; _; _; _; CB 24 ?ja; CB 16 ?jb; CB 8 ?jc; _; _; _; _] => exists ja, jc end.
      lazymatch type of LOC1 with rw_cells _ _ _ ?cs =>
        change cs with ([CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 (firstn 24 jB')] ++ [CB 16 (firstn 16 (skipn 24 jB'))] ++
                        [CB 8 (firstn 8 (skipn 16 (skipn 24 jB'))); C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)]) in LOC1 end.
      apply Sj_stage1_kit.rw_cells_app in LOC1. destruct LOC1 as [LA LOC1]. apply Sj_stage1_kit.rw_cells_app in LOC1. destruct LOC1 as [LB LC].
      cbn [cells_size csize Nat.add] in LA, LB, LC.
      lazymatch goal with |- rw_cells _ _ _ ?cs =>
        lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] =>
          change cs with ([c0; c1; c2; c3; c4; c5] ++ [c6] ++ [c7; c8; c9; c10; c11]) end end.
      apply Sj_stage1_kit.rw_cells_app. split.
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ LA). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR2). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
        split; [left; unfold USTACK_TOP in *; flia| flia]. }
      apply Sj_stage1_kit.rw_cells_app. cbn [cells_size csize Nat.add]. split.
      { pose proof (proj2 LB) as WLB. cbn [cells_size csize Nat.add] in WLB. replace (b + Z.of_nat 96) with (b + 96) in WLB |- * by lia.
        apply rw_cells_CB_intro; [exact BY2|]. cbn [length repeat]. exact (wr_at_transport bsegs m1 m2 _ _ WLB WM2). }
      apply (rw_cells_agree_nw bsegs m1 m2 _ _ LC). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR2). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [left; unfold USTACK_TOP in *; flia| flia]. }
    clear LOC1. destruct LOC2 as (jC & j2 & LOC2).

    assert (PIECES : forall (mX : mem) (j2x : list byte),
      rw_cells bsegs mX b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 12); CB 4 j2x;
                         C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)] ->
      exists (j0' : list byte) (w24 w32 : word),
        rw_cells bsegs mX b (obj_loc72 j0' w24 w32 f out) /\ rw_cells bsegs mX (b + 72) [CB 24 jC]
        /\ rw_cells bsegs mX (b + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2x]
        /\ rw_cells bsegs mX (b + 120) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)]).
    { intros mX j2x H. destruct (loc72_of_raw mX b j0 f out _ H) as (j0' & w24 & w32 & H'). exists j0', w24, w32.
      apply Sj_stage1_kit.rw_cells_app in H'. destruct H' as [H1 H']. split; [exact H1|].
      unfold obj_loc72 in H'. cbn [cells_size csize Nat.add] in H'. replace (b + Z.of_nat 72) with (b + 72) in H' by lia.
      lazymatch type of H' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0] ++ [c1; c2; c3] ++ rest) in H' end.
      apply Sj_stage1_kit.rw_cells_app in H'. destruct H' as [H2 H']. split; [exact H2|].
      apply Sj_stage1_kit.rw_cells_app in H'. destruct H' as [H3 H4]. cbn [cells_size csize Nat.add length repeat] in H3, H4.
      replace (b + 72 + Z.of_nat 24) with (b + 96) in H3, H4 by lia. replace (b + 96 + Z.of_nat 24) with (b + 120) in H4 by lia.
      split; [| exact H4]. apply rec_node16. rewrite <- zeros16_words. exact H3. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p4 E OK _ m2 F' fc q b out node P f (P + 1) L0 sl Lk L);
      [exact MI2| exact ST2| exact LO| flia| flia| exact B32| exact QHI| flia| clear - PB0 PB1; lia| clear - LKR; lia| clear - PB0 PB1 PB2 PB3 ZL0 LKR LOW HL HT; ul
      | clear - SLR ZLN PB0 PB1 PB2 PB3 ZL0 LOW HL HT; unfold USTACK_TOP in *; lia| exact LOC2| exact (SHBW m2 ART2)| exact (SHZLW m2 ART2)| |].
    -
      intros m3 ya1 ya2 yb4 yb5 j2' LK0 MU3 WM3 MI3 ST3 LOC3.
      pose proof (ARTW m2 m3 ART2 MU3 WM3) as ART3.
      assert (OW3 : Forall (ownW I) (obj_WL b)) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OBK2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OBK3.
      unfold obj_WL in MU3. mportx NODE MU3 WM3. mportx SH MU3 WM3. mportx OUT MU3 WM3. clear FREST.
      eapply (obj_p5a E OK _ m3 F' fc q b out node P f (P + 1) L0 sl Lk 18446744073709551615 L); [exact MI3| flia| flia| exact QHI| left; reflexivity| exact LOC3| |].
      + intros _. apply evt_done.
        destruct (PIECES m3 j2' LOC3) as (j0' & w24 & w32 & L72 & REC3 & CHILD3 & SV3). clear LOC3.
        eapply (NOESC m3); [exact (obase_of_K RT E Σ I Σ1 m3 OBK3 ST3)| exact FRM| exact EPTR| exact ZL0| exact SL| exact NODE| exact L72| exact REC3| exact CHILD3| exact SV3| exact SH| exact OUT].
      + intros ABS. exfalso. clear - ABS LK0. lia.
    -
      intros m3 yc3 yc4 yc5 j2' LKP MU3 WM3 MI3 ST3 FR3 LOC3. apply evt_done.
      pose proof (ARTW m2 m3 ART2 MU3 WM3) as ART3.
      assert (OW3 : Forall (ownW I) (obj_WL b)) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OBK2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OBK3.
      pose proof OBK3 as (_ & _ & AI3 & _).
      unfold obj_WL in MU3. mportx NODE MU3 WM3. mportx SH MU3 WM3. mportx OUT MU3 WM3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ FREST MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; flia)) as FREST3. clear FREST. rename FREST3 into FREST.
      assert (EU16 : bv_unsigned (Z_to_bv 64 (b + -16)) = b + -16) by (apply unsigned_lit; ul).
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m3 (b + -16) ES1 ST3 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK3. fold b in COK3.

      pose proof (ptr_atA_facts E P ptr m3 OK PAT (proj1 (proj2 (proj2 AI3)))) as (PTRB & PTRF & _ & _ & PL).
      rewrite EPTR in PTRB. rewrite EPTR, zlength_cons in PL. pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
      change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
      pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
      set (kb := firstn (Z.to_nat Lk) rest) in *.
      assert (ZKB : zlength kb = Lk) by (subst kb; unfold zlength; rewrite firstn_length_le; [lia| unfold zlength in ZL0; lia]).
      eapply (aevt_memchrP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m3 (P + 1) 126 Lk (map (Z_to_bv 8) kb) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| clear - PB0 PB1 PB2 PB3 ZL0 ZLN LKR LOW HL HT; ul| lia| clear - LKR ZL0 ZLN PL; lia| exact KEYL| rewrite <- ZKB; apply memchr_ok_all
        | left; rewrite length_map; unfold zlength in ZKB; clear - ZKB LKR PB1 PB2 PB3 ZL0; lia| | exact ART3| exact MI3| exact COK3|].
      { pose proof (memchr_chk_le 126 Lk (map (Z_to_bv 8) kb) ltac:(lia)). pose proof (memchr_chk_nonneg 126 Lk (map (Z_to_bv 8) kb) ltac:(lia)).
        apply (checked_src_live RT AF Σ1 m3 _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART3 INPB); [lia| lia| rewrite ES1; exact LWIN]. }
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m4 (ART4 & MI4 & WM4 & ST4) PR4.
      rewrite EU16 in ST4, PR4. rewrite (ret_pc_even 0xb915c) by lia.
      assert (NCL4 : forall a, 0 <= a < 0 + 0 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) by (intros a Ha; lia).
      pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 (b + -16) 0 0 m3 m4 OBK3 EF1 EL1i ES1 ART4 MI4 ltac:(unfold oi_b; lia) PR4 NCL4
                    ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBK4.
      pose proof (agree_of_pres_ex _ _ _ _ _ m3 m4 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -16) x /\ ~ (0 <= x < 0 + 0)) PR4 (fun x H => H)) as AG4.
      clear KEYB KEYL PTRB. xportx_stack NODE AG4. xportx_stack LOC3 AG4. xportx_stack FR3 AG4. xportx_frame FREST AG4 HinF. xportx_shadow SH AG4 HinF. xportx_stack OUT AG4.

      apply (aevt_evt RT AF PMc MST).
      destruct (find_byte 126 (firstn (Z.to_nat Lk) (map (Z_to_bv 8) kb))) as [ix|] eqn:FB.
      +
        pose proof (find_byte_Some _ _ _ FB) as (IXL & _). rewrite length_firstn, length_map in IXL.
        assert (IXK : Z.of_nat ix < Lk) by (unfold zlength in ZKB; clear - IXL ZKB; lia).
        eapply (svfind_post E OK _ m4 F'' fc b (P + 1) (memchr_res (P + 1) 126 Lk (map (Z_to_bv 8) kb)) (Z.of_nat ix) 0xb883c);
          [exact FR3| exact ST4| exact MI4| flia| clear - PR47 ZLN ZL0; lia
          | right; unfold memchr_res; rewrite FB; clear - IXK LKR PR47 ZLN ZL0; split; lia| lia| reflexivity|].
        intros xb1 STb.
        pose proof (obase_of_K RT E Σ I Σ1 m4 OBK4 STb) as OB4.
        destruct (PIECES m4 j2' LOC3) as (j0' & w24 & w32 & L72 & REC4 & CHILD4 & SV4).

        apply (rw_cells_split_CB bsegs _ _ [] 96 jF [] [8; 24; 64]%nat) in FREST; [| reflexivity]. cbn [mk_CB_cells app] in FREST.
        apply (proj1 (rw_cells_app bsegs m4 _ [_] _)) in FREST. destruct FREST as [_ FREST]. cbn [cells_size csize Nat.add] in FREST.
        replace (f + 24 + Z.of_nat 8) with (f + 32) in FREST by lia.
        apply (proj1 (rw_cells_app bsegs m4 _ [_] _)) in FREST. destruct FREST as [STR R56]. cbn [cells_size csize Nat.add] in R56.
        replace (f + 32 + Z.of_nat 24) with (f + 56) in R56 by lia.
        apply (aevt_evt RT AF PMc MST).
        eapply (obj_p5a E OK _ m4 F'' fc q b out node P f (P + 1) L0 sl Lk (Z.of_nat ix) L); [exact MI4| flia| flia| exact QHI| right; clear - IXK LKR PR47 ZLN ZL0; split; lia| exact LOC3| |].
        * intros ABS. exfalso. clear - ABS IXK LKR PR47. lia.
        * intros _. apply evt_done.
          eapply (obj_esc RT AF E OK d PMc FDO MST Σ Σ1 I CTX HSSO HHEAP m4);
            [exact OB4| exact FRM| exact EPTR| exact ZL0| exact SL| exact IXK| | exact NODE| exact L72| exact REC4| exact CHILD4| exact SV4| exact SH| exact STR| exact R56| exact OUT].
          unfold kb in FB. rewrite <- firstn_map, firstn_firstn, Nat.min_id in FB. rewrite firstn_map in FB. exact FB.
      +
        eapply (svfind_post E OK _ m4 F'' fc b (P + 1) (memchr_res (P + 1) 126 Lk (map (Z_to_bv 8) kb)) 18446744073709551615 0xb883c);
          [exact FR3| exact ST4| exact MI4| flia| clear - PR47 ZLN ZL0; lia| left; unfold memchr_res; rewrite FB; split; reflexivity| lia| reflexivity|].
        intros xb1 STb.
        destruct (PIECES m4 j2' LOC3) as (j0' & w24 & w32 & L72 & REC4 & CHILD4 & SV4).
        apply (aevt_evt RT AF PMc MST).
        eapply (obj_p5a E OK _ m4 F'' fc q b out node P f (P + 1) L0 sl Lk 18446744073709551615 L); [exact MI4| flia| flia| exact QHI| left; reflexivity| exact LOC3| |].
        * intros _. apply evt_done.
          eapply (NOESC m4); [exact (obase_of_K RT E Σ I Σ1 m4 OBK4 STb)| exact FRM| exact EPTR| exact ZL0| exact SL| exact NODE| exact L72| exact REC4| exact CHILD4| exact SV4| exact SH| exact OUT].
        * intros ABS. exfalso. clear - ABS LKR PR47. lia.
  Qed.

  Lemma obj_top : forall (m : mem) (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 a6 a7 y7 y8 y9 y10 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (js4 jo j0 jB jF : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_locB j0 jB (oi_f I) (oi_out I) (Z_to_bv 64 (oi_P I)) (Z_to_bv 64 (oi_L I))) ->
    rw_cells bsegs m (oi_f I + 24) [CB 96 jF] -> rw_cells bsegs m (shad (oi_f I)) (obj_sh (-8) (-8) (-8) js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR (wz OBJ_SM1_RA) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) xa0 xa1 xa2 xa3 xa4 (wz (oi_f I)) a6 a7
               (wz (oi_out I)) (wz (shad (oi_f I))) (wz (oi_node I)) (wz (oi_L I)) (wz (oi_P I)) y7 y8 y9 y10 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb87a8) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM FIN NOESC HSSO HHEAP.
    intros until jF. intros OB FRM NODE LOC FREST SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 432 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    assert (EL1i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL1; auto).
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (zlength_nonneg ptr) as ZLN.
    assert (CST : 1 <= obj_costA d (zlength ptr)) by (unfold obj_costA, LVL_C1, DCOST; lia).
    assert (FPW : fp_ok RT Σ1 (ae_lo E) (obj_WL b)) by (unfold obj_WL; constructor; [left; cbn [fst snd]; ul| constructor]).
    assert (ARTW : forall m1 m', ART RT Σ1 m1 -> munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> ART RT Σ1 m').
    { intros m1 m' A1 MU WM. exact (art_of_munch RT AF Σ1 m1 m' (ae_lo E) _ A1 ltac:(rewrite ES1; exact LWIN) FPW MU WM). }
    assert (SHBW : forall m1, ART RT Σ1 m1 -> forall m', munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> shb_cells m')
      by (intros m1 A1 m' MU WM; exact (shb_cells_of_art RT AF Σ1 m' (ARTW m1 m' A1 MU WM))).
    assert (SHZLW : forall m1, ART RT Σ1 m1 -> forall m', munch (obj_WL b) m1 m' -> wmono bsegs m1 m' -> shz m' b 152).
    { intros m1 A1 m' MU WM. apply (shz_stack RT AF Σ1 m' b 152 (ARTW m1 m' A1 MU WM)); [rewrite ES1; ul| ul| clear - B32; Z.div_mod_to_equations; lia| reflexivity| lia]. }

    assert (FINW : forall (mX : mem) (jBx : list byte) (pv lv : word), rw_cells bsegs mX b (obj_locB j0 jBx f out pv lv) ->
      exists (j0' : list byte) (w24 w32 : word) (cM : list cell), rw_cells bsegs mX b (obj_loc72 j0' w24 w32 f out) /\ rw_cells bsegs mX (b + 72) cM /\ cells_size cM = 80%nat).
    { intros mX jBx pv lv H. unfold obj_locB in H. destruct (loc72_of_raw mX b j0 f out _ H) as (j0' & w24 & w32 & H').
      apply Sj_stage1_kit.rw_cells_app in H'. destruct H' as [H1 H2]. unfold obj_loc72 in H2. cbn [cells_size csize Nat.add] in H2.
      replace (b + Z.of_nat 72) with (b + 72) in H2 by lia. exists j0', w24, w32, [CB 64 jBx; C8 pv; C8 lv]. split; [exact H1|]. split; [exact H2| reflexivity]. }
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p2b E OK _ m F fc q b out node P f ptr); [exact MI| exact ST| exact LO| flia| flia| exact B32| exact QHI| flia| exact OB'| flia| ul| exact PAT| exact AI| | | exact (SHBW m ART0)| exact (SHZLW m ART0)| | | |].
    { intros NE. exact (lvl_acc_ptr RT AF E Σ1 m P ptr ART0 LV1 PAT NE). }
    { unfold oi_L in LOC. exact LOC. }
    -
      intros ya3 ya4 EP. apply evt_done.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m b ES1 ST ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK. fold b in COK.
      pose proof (rw_cells_bytes_at bsegs m _ _ NODE) as NB16. cbn [cells_bytes cbytes app] in NB16. rewrite app_nil_r in NB16.
      set (nbs := le8 (wz (ae_DOC E)) ++ le8 (wz i)) in NB16.
      assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out node nbs (ae_lo E));
        [reflexivity| reflexivity| rewrite LNB; reflexivity| ul| ul| rewrite LNB; cbn; lia| exact NB16| | | rewrite LNB; cbn; lia| exact ART0| exact MI| exact COK|].
      { rewrite LNB. apply (checked_src_stack RT AF Σ1 m _ (ae_lo E) node 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia]. }
      { rewrite LNB. apply (checked_dst_stack RT AF Σ1 m _ out 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
      rewrite EU in ST2, PR2. rewrite LNB in PR2. change (Z.of_nat 16) with 16 in PR2. rewrite (ret_pc_even 0xb88a0) by lia.
      pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 b out 16 m m2 (proj1 OB0) EF1 EL1i ES1 ART2 MI2 ltac:(unfold oi_b; lia) PR2 ltac:(intros a Ha _; clear - Ha; lia)
                    ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OBK2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
      lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
      pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC nbs _ _ _ OUT eq_refl eq_refl BY2 LNB WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT NB16.
      xportx_stack LOC AG. xportx_shadow SH AG HinF.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_xcpy E OK _ q b out); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ1 m2 out 24 ART2 LV1 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))| exact OUT2|].
      intros m3 xa1' MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OBK2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OBK3.
      mportx LOC MU3 WM3. mportx SH MU3 WM3.
      pose proof (stk_transport_disjoint bsegs _ m2 m3 (ae_lo E) b ST2 MU3 WM3 ltac:(cbn; flia)) as ST3.
      destruct (FINW m3 _ _ _ LOC) as (j0' & w24 & w32 & cM & L72 & CM & SZM).
      assert (OUTR : out_recA E m3 out).
      { pose proof TY as TY'. unfold ty in TY'. pose proof (ttype_range _ _ TY' ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.
        apply (out_recA_ok E m3 out i joC (Datatypes.S d) (e + 1)); [| exact (obj_node_elem (ae_T E) (ae_S E) (ae_sn E) d i e c TY' NXT TEND TILES ltac:(clear - TIR; lia))| exact I0| clear - EN; lia].
        apply rec_node16. subst nbs. exact OUT3. }
      eapply (FIN Σ1 m3); [exact (obase_of_K RT E Σ I Σ1 m3 OBK3 ST3)| exact FRM| exact EF1| exact EL1| exact ES1| rewrite EC1; unfold oi_L; fold ptr; clear - CST; lia
        | exact L72| exact CM| exact SZM| exact SH| exact OUTR].
    -
      intros ya3 ya4 c0 ptr0 EP NE47. apply evt_done.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m b ES1 ST ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK. fold b in COK.
      eapply (aevt_memsetP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out 16 (Z_to_bv 8 0) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART0| exact MI| exact COK|].
      { apply (checked_dst_stack RT AF Σ1 m _ out 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
      rewrite EU in ST2, PR2. change (Z.to_nat 16) with 16%nat in BY2. rewrite (ret_pc_even 0xb88d4) by lia.
      pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 b out 16 m m2 (proj1 OB0) EF1 EL1i ES1 ART2 MI2 ltac:(unfold oi_b; lia) PR2 ltac:(intros a Ha _; clear - Ha; lia)
                    ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OBK2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
      lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
      pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT eq_refl eq_refl BY2 eq_refl WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT.
      xportx_stack LOC AG. xportx_shadow SH AG HinF.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_xset E OK _ q b out); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ1 m2 out 24 ART2 LV1 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))| exact OUT2|].
      intros m3 MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OBK2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OBK3.
      mportx LOC MU3 WM3. mportx SH MU3 WM3.
      pose proof (stk_transport_disjoint bsegs _ m2 m3 (ae_lo E) b ST2 MU3 WM3 ltac:(cbn; flia)) as ST3.
      destruct (FINW m3 _ _ _ LOC) as (j0' & w24 & w32 & cM & L72 & CM & SZM).
      assert (OUTR : out_recA E m3 out).
      { apply (out_recA_err E m3 out (Z_to_bv 64 0) 0 22 joC); [| lia]. apply rec_node16. rewrite <- zeros16_words. exact OUT3. }
      eapply (FIN Σ1 m3); [exact (obase_of_K RT E Σ I Σ1 m3 OBK3 ST3)| exact FRM| exact EF1| exact EL1| exact ES1| rewrite EC1; unfold oi_L; fold ptr; clear - CST; lia
        | exact L72| exact CM| exact SZM| exact SH| exact OUTR].
    -
      intros m1 ya1 ya2 ya4 ya5 EP MU1 WM1 MI1 ST1 LOC1. apply evt_done.
      pose proof (ARTW m m1 ART0 MU1 WM1) as ART1.
      assert (OW1 : Forall (ownW I) (obj_WL b)) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 (proj1 OB0) EF1 EL1i ES1 MU1 WM1 MI1 OW1) as OBK1.
      unfold obj_WL in MU1. mportx NODE MU1 WM1. mportx SH MU1 WM1. mportx OUT MU1 WM1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ FREST MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; flia)) as FREST1.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv64_eqm; reflexivity).
      eapply (obj_mid m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc 18446744073709551615 0 _ []);
        [exact (obase_of_K RT E Σ I Σ1 m1 OBK1 ST1)| exact FRM| exact EP| reflexivity| left; reflexivity| exact NODE| exact LOC1| exact FREST1| exact SH| exact OUT].
    -
      intros m1 ya3 ya4 ya5 c1 ptr1 EP MU1 WM1 MI1 ST1 FR1 LOC1. apply evt_done.
      pose proof (ARTW m m1 ART0 MU1 WM1) as ART1.
      assert (OW1 : Forall (ownW I) (obj_WL b)) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 (proj1 OB0) EF1 EL1i ES1 MU1 WM1 MI1 OW1) as OBK1.
      pose proof OBK1 as (_ & _ & AI1 & _).
      unfold obj_WL in MU1. mportx NODE MU1 WM1. mportx SH MU1 WM1. mportx OUT MU1 WM1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ FREST MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; flia)) as FREST1. clear FREST.
      assert (EU16 : bv_unsigned (Z_to_bv 64 (b + -16)) = b + -16) by (apply unsigned_lit; ul).
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m1 (b + -16) ES1 ST1 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK1. fold b in COK1.
      assert (NE : ptr <> []) by (rewrite EP; discriminate).
      pose proof (lvl_ptr_range E OK P ptr PAT NE) as (PB0 & PB1 & PB2 & PB3).
      pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT NE) as INPB.
      pose proof (ptr_atA_facts E P ptr m1 OK PAT (proj1 (proj2 (proj2 AI1)))) as (PTRB1 & _).
      rewrite EP in PTRB1, PB2, PL. rewrite !zlength_cons in PB2, PL. pose proof (zlength_nonneg ptr1) as ZL1N.
      pose proof (bytes_at_skipn _ _ _ 1 PTRB1 ltac:(cbn; lia)) as KEYB.
      change (skipn 1 (map (Z_to_bv 8) (47 :: c1 :: ptr1))) with (map (Z_to_bv 8) (c1 :: ptr1)) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
      assert (PTRF0 : Forall (fun c => 0 <= c < 256) (c1 :: ptr1)) by (rewrite EP in PTRF; inversion PTRF; assumption).
      assert (ZL01 : zlength (c1 :: ptr1) = zlength ptr1 + 1) by apply zlength_cons.
      eapply (aevt_memchrP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (P + 1) 47 (zlength ptr1 + 1) (map (Z_to_bv 8) (c1 :: ptr1)) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| clear - PB0 PB1 PB2 PB3 ZL1N LOW HL HT; ul| lia| clear - PL ZL1N; lia| exact KEYB| rewrite <- ZL01; apply memchr_ok_all
        | left; rewrite length_map; unfold zlength in *; cbn [length] in *; clear - PB1 PB2 PB3 ZL1N; lia| | exact ART1| exact MI1| exact COK1|].
      { pose proof (memchr_chk_le 47 (zlength ptr1 + 1) (map (Z_to_bv 8) (c1 :: ptr1)) ltac:(lia)). pose proof (memchr_chk_nonneg 47 (zlength ptr1 + 1) (map (Z_to_bv 8) (c1 :: ptr1)) ltac:(lia)).
        apply (checked_src_live RT AF Σ1 m1 _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART1 INPB); [lia| lia| rewrite ES1; exact LWIN]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2.
      rewrite EU16 in ST2, PR2. rewrite (ret_pc_even 0xb915c) by lia.
      assert (NCL2 : forall a, 0 <= a < 0 + 0 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) by (intros a Ha; lia).
      pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 (b + -16) 0 0 m1 m2 OBK1 EF1 EL1i ES1 ART2 MI2 ltac:(unfold oi_b; lia) PR2 NCL2
                    ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBK2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -16) x /\ ~ (0 <= x < 0 + 0)) PR2 (fun x H => H)) as AG.
      clear KEYB PTRB1. xportx_stack NODE AG. xportx_stack LOC1 AG. xportx_stack FR1 AG. xportx_frame FREST1 AG HinF. xportx_shadow SH AG HinF. xportx_stack OUT AG.
      apply (aevt_evt RT AF PMc MST).
      destruct (find_byte 47 (firstn (Z.to_nat (zlength ptr1 + 1)) (map (Z_to_bv 8) (c1 :: ptr1)))) as [ix|] eqn:FB.
      + pose proof (find_byte_Some _ _ _ FB) as (IXL & _). rewrite length_firstn, length_map in IXL. cbn [length] in IXL.
        assert (IXK : Z.of_nat ix < zlength ptr1 + 1) by (unfold zlength in *; clear - IXL; lia).
        eapply (svfind_post E OK _ m2 F' fc b (P + 1) (memchr_res (P + 1) 47 (zlength ptr1 + 1) (map (Z_to_bv 8) (c1 :: ptr1))) (Z.of_nat ix) 0xb87f8);
          [exact FR1| exact ST2| exact MI2| flia| clear - PB0 PB1 PB2 PB3 ZL1N LOW HL HT; ul
          | right; unfold memchr_res; rewrite FB; clear - IXK PB0 PB1 PB2 PB3 ZL1N LOW HL HT; split; [unfold USTACK_TOP in *; lia| lia]| lia| reflexivity|].
        intros xb1 STb.
        eapply (obj_mid m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc (Z.of_nat ix) (zlength ptr1 + 1) _ (c1 :: ptr1));
          [exact (obase_of_K RT E Σ I Σ1 m2 OBK2 STb)| exact FRM| exact EP| exact ZL01| right; lia| exact NODE| exact LOC1| exact FREST1| exact SH| exact OUT].
      + eapply (svfind_post E OK _ m2 F' fc b (P + 1) (memchr_res (P + 1) 47 (zlength ptr1 + 1) (map (Z_to_bv 8) (c1 :: ptr1))) 18446744073709551615 0xb87f8);
          [exact FR1| exact ST2| exact MI2| flia| clear - PB0 PB1 PB2 PB3 ZL1N LOW HL HT; ul| left; unfold memchr_res; rewrite FB; split; reflexivity| lia| reflexivity|].
        intros xb1 STb.
        eapply (obj_mid m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc 18446744073709551615 (zlength ptr1 + 1) _ (c1 :: ptr1));
          [exact (obase_of_K RT E Σ I Σ1 m2 OBK2 STb)| exact FRM| exact EP| exact ZL01| left; reflexivity| exact NODE| exact LOC1| exact FREST1| exact SH| exact OUT].
  Qed.
End ObjQ.
