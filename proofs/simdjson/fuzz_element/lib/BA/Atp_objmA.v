(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma cb8_c8 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. intros. apply num_cb8_c8. assumption. Qed.

Ltac cb8_step H :=
  cbn [app] in H;
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let rec go pre l :=
      lazymatch l with
      | CB 8 ?bs :: ?post => apply (cb8_c8 m A pre post bs) in H; cbn [app] in H
      | ?c :: ?l' => go constr:(pre ++ [c]) l'
      end in go constr:(@nil cell) cs
  end.
Lemma locA_of_raw : forall (m : mem) b (jA1 jA2 : list byte) (a o nd f : word),
  rw_cells asegs m b [CB 80 jA1; C8 a; CB 24 jA2; C8 o; C8 nd; C8 f] ->
  exists (j0 : list byte) (w24 w32 w40 w48 w56 w64 w72 w88 w96 w104 : word),
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 a w88 w96 w104 o nd f).
Proof.
  intros m b jA1 jA2 a o nd f H.
  apply (rw_cells_split_CB asegs _ _ [] 80 jA1 _ [24; 8; 8; 8; 8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: CB 24 jA2 :: ?rest) =>
    apply (rw_cells_split_CB asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8] 24 jA2 rest [8; 8; 8]%nat) in H; [| reflexivity] end.
  cbn [mk_CB_cells app] in H.
  repeat match type of H with context [CB 8 ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in H; clearbody j end.
  lazymatch type of H with context [CB 24 ?t] => set (j0 := t) in H; clearbody j0 end.
  do 10 (cb8_step H).
  unfold obj_locA. do 11 eexists. exact H.
Qed.

Lemma zeros16_words : repeat (Z_to_bv 8 0) 16 = le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).
Proof. reflexivity. Qed.

Section ObjM.
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
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Definition esc_sso_stmt : Prop :=
    forall (m : mem) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
           (sl Lk L0 : Z) (ix : nat) (rest : list Z) (js4 jo j0 jco jt jS' jR : list byte) (w24 w32 w40 w48 w56 w88 w96 w104 w128 : word),
      obase RT E Σ I Σ1 m -> frm0 fc ->
      oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl < L0 /\ Lk = sl) \/ (L0 <= sl /\ Lk = L0)) -> (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
      0 < Lk < 23 -> find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix ->
      rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
      rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
      rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
      rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) ->
      rw_cells asegs m (oi_f I + 32) [C1 (Z_to_bv 8 (2 * Lk)); CB 23 jS'] -> rw_cells asegs m (oi_f I + 56) [CB 64 jR] ->
      rw_cells asegs m (oi_out I) [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR (wz 0xb6058) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
                 (wz (oi_f I)) (wz (shad (oi_f I))) (wz (oi_L I)) (wz (oi_P I + 1)) (wz (oi_f I + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) (wz (oi_f I + 33)) (wz 2147450880) x28 x29 x30 x31)
            F (wz 0xb637c) fc None m (seg_rom asegs)).

  Definition esc_heap_stmt : Prop :=
    forall (m : mem) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
           (sl Lk L0 : Z) (ix : nat) (rest : list Z) (js4 jo j0 jco jt jS jR : list byte) (w24 w32 w40 w48 w56 w88 w96 w104 w128 : word),
      obase RT E Σ I Σ1 m -> frm0 fc ->
      oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl < L0 /\ Lk = sl) \/ (L0 <= sl /\ Lk = L0)) -> (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
      23 <= Lk -> find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix ->
      rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
      rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
      rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
      rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) ->
      rw_cells asegs m (oi_f I + 32) [CB 24 jS] -> rw_cells asegs m (oi_f I + 56) [CB 64 jR] ->
      rw_cells asegs m (oi_out I) [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR (wz 0xb6368) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (str_sz Lk)) x11 x12 x13 x14 x15 x16 x17
                 (wz (oi_f I)) (wz (shad (oi_f I))) (wz (str_sz Lk)) (wz (oi_P I + 1)) (wz (oi_f I + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) x26 (wz 2147450880) x28 x29 x30 x31)
            F (wz OPNEW_A) fc None m (seg_rom asegs)).

  Hypothesis HSSO : esc_sso_stmt.
  Hypothesis HHEAP : esc_heap_stmt.

  Lemma obj_j94 : forall (m : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl Lk L0 : Z) (rest : list Z) (js4 jo jA jB2 jF : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl < L0 /\ Lk = sl) \/ (L0 <= sl /\ Lk = L0)) -> (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) [CB 112 jA; C8 (Z_to_bv 64 (oi_out I)); C8 (Z_to_bv 64 (oi_node I)); C8 (Z_to_bv 64 (oi_f I)); CB 48 jB2] ->
    rw_cells asegs m (oi_f I + 24) [CB 96 jF] -> rw_cells asegs m (shad (oi_f I)) (obj_sh (-8) (-8) (-8) js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz sl) x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) (wz (oi_L I)) (wz (oi_P I + 1)) (wz (oi_f I)) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb601c) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM HSSO HHEAP.
    intros until jF. intros OB FRM EPTR ZL0 MIN SLR NODE LOC FREST SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [WF SBS P1F P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (zlength_nonneg rest) as ZLN.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & PTRF & _ & _ & PL).
    rewrite EPTR, zlength_cons, ZL0 in PB2, PL. rewrite EPTR in PTRF.
    assert (ZL : zlength ptr = L0 + 1) by (rewrite EPTR, zlength_cons; lia).
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT ltac:(rewrite EPTR; discriminate)) as INPB.
    assert (LKR : 0 <= Lk <= L0) by (clear - MIN SLR ZLN ZL0 PL; lia).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p3b E OK _ b out node f sl L0 Lk); [exact MI| ul| ul| clear - SLR ZLN ZL0 PL; lia| ul| exact MIN| exact LOC|].
    intros m1 jA1 jA2 MU1 WM1 MI1 LOC1.
    assert (OW1 : Forall (ownW I) [(b, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 OB0 EF1 ltac:(rewrite EL1; auto) ES1 MU1 WM1 MI1 OW1) as OB1.
    pose proof OB1 as (_ & ART1 & ST1 & AI1 & _).
    mport NODE MU1 WM1. mport FREST MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1. clear LOC.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m1 ES1 ST1) as COK1. fold b in COK1.
    apply (proj1 (rw_cells_app asegs m1 _ [_; _; _; _; _; _] _)) in LOC1. destruct LOC1 as [LOCA CREC]. cbn [cells_size csize Nat.add] in CREC.
    replace (b + Z.of_nat 136) with (b + 136) in CREC by lia.
    apply (rw_cells_split_CB asegs _ _ [] 48 jB2 [] [24; 16; 4; 4]%nat) in CREC; [| reflexivity]. cbn [mk_CB_cells app] in CREC.
    repeat match type of CREC with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jr" in set (j := t) in CREC; clearbody j end.
    apply (proj1 (rw_cells_app asegs m1 _ [_] _)) in CREC. destruct CREC as [COUT REC]. cbn [cells_size csize Nat.add] in REC.
    replace (b + 136 + Z.of_nat 24) with (b + 160) in REC by lia.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (b + 160) 16 (Z_to_bv 8 0) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART1| exact MI1| exact COK1|].
    { apply (checked_dst_stack RT AF Σ1 m1 _ (b + 160) 16 ART1); [rewrite ES1; ul| ul| rewrite EU; lia|].
      apply (wr_at_sub m1 (b + 160) 24 (b + 160) 16 (proj2 REC)); lia. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. rewrite (ret_pc_even 0xb603c) by lia.
    assert (EL1i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL1; auto).
    assert (NCL2 : forall a, b + 160 <= a < b + 160 + 16 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24).
    { intros a Ha Hc. exfalso. destruct (obj_split RT AF E d Σ Σ1 I CTX Σ1 m1 a ART1 EF1 EL1i ES1 Hc); flia. }
    pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ1 (b + 160) 16 m1 m2 OB1 EF1 EL1i ES1 ART2 MI2 ST2 PR2 NCL2
                  ltac:(left; unfold oi_b; flia) ltac:(right; left; unfold oi_b; flia)) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (b + 160 <= x < b + 160 + 16)) PR2 (fun x H => H)) as AG.
    pose proof (proj2 REC) as WREC. cbn [cells_size csize Nat.add] in WREC. pose proof REC as RECt.
    apply (proj1 (rw_cells_app asegs m1 _ [_] _)) in RECt. destruct RECt as [_ RECt]. cbn [cells_size csize Nat.add] in RECt. clear REC.
    xport_stack NODE AG. xport_stack LOCA AG. xport_stack COUT AG. xport_stack RECt AG. xport_frame FREST AG HinF. xport_shadow SH AG HinF. xport_stack OUT AG.
    assert (REC2 : rw_cells asegs m2 (b + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 4 jr1; CB 4 jr2]).
    { apply rec_node16. rewrite <- zeros16_words. change 16%nat with (length (repeat (Z_to_bv 8 0) 16)) at 1.
      change (CB (length (repeat (Z_to_bv 8 0) 16)) (repeat (Z_to_bv 8 0) 16) :: ?r) with ([CB (length (repeat (Z_to_bv 8 0) 16)) (repeat (Z_to_bv 8 0) 16)] ++ r).
      apply (proj2 (rw_cells_app asegs m2 _ [_] _)). split.
      - apply rw_cells_CB_intro; [exact BY2| cbn [length repeat]; exact (wr_at_transport asegs m1 m2 _ _ ltac:(exact (wr_at_sub m1 (b + 160) 24 (b + 160) 16 WREC ltac:(lia) ltac:(lia) ltac:(lia))) WM2)].
      - cbn [cells_size csize Nat.add length repeat]. replace (b + 160 + Z.of_nat 16) with (b + 160 + 16) by lia. exact RECt. }
    clear RECt BY2.
    destruct (locA_of_raw m2 b jA1 jA2 _ _ _ _ LOCA) as (j0 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w88 & w96 & w104 & LOCA2). clear LOCA.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p4 E OK _ q b P _ L0 Lk f); [exact MI2| exact LO| lia| lia| lia| ul| exact REC2| |].
    -
      intros m3 LK0 MU3 WM3 MI3 REC3.
      assert (OW3 : Forall (ownW I) [(b + 160, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OB2 EF1 ltac:(rewrite EL1; auto) ES1 MU3 WM3 MI3 OW3) as OB3.
      mport NODE MU3 WM3. mport LOCA2 MU3 WM3. mport COUT MU3 WM3. mport SH MU3 WM3. mport OUT MU3 WM3.
      eapply (obj_noesc RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX m3); [exact OB3| exact FRM| exact EPTR| exact ZL0| exact SLR| exact LKR| exact NODE| | exact COUT| exact REC3| exact SH| exact OUT].
      exact LOCA2.
    -
      intros m3 LKP MU3 WM3 MI3 REC3.
      assert (OW3 : Forall (ownW I) [(b + 160, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OB2 EF1 ltac:(rewrite EL1; auto) ES1 MU3 WM3 MI3 OW3) as OB3.
      pose proof OB3 as (_ & ART3 & ST3 & AI3 & _).
      mport NODE MU3 WM3. mport LOCA2 MU3 WM3. mport COUT MU3 WM3. mport FREST MU3 WM3. mport SH MU3 WM3. mport OUT MU3 WM3.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m3 ES1 ST3) as COK3. fold b in COK3.
      pose proof (ptr_atA_facts E P ptr m3 OK PAT (proj1 (proj2 (proj2 AI3)))) as (PTRB & _).
      rewrite EPTR in PTRB. pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
      change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
      pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
      set (kb := firstn (Z.to_nat Lk) rest) in *.
      assert (ZKB : zlength kb = Lk) by (subst kb; unfold zlength; rewrite firstn_length_le; [lia| unfold zlength in ZL0; lia]).
      eapply (aevt_memchrP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m3 (P + 1) 126 Lk (map (Z_to_bv 8) kb) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| ul| exact KEYL| rewrite <- ZKB; apply memchr_ok_all| left; rewrite length_map; unfold zlength in ZKB; flia| | exact ART3| exact MI3| exact COK3|].
      { pose proof (memchr_chk_le 126 Lk (map (Z_to_bv 8) kb) ltac:(lia)). pose proof (memchr_chk_nonneg 126 Lk (map (Z_to_bv 8) kb) ltac:(lia)).
        apply (checked_src_live RT AF Σ1 m3 _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART3 INPB); [lia| lia| rewrite ES1; exact LWIN]. }
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m4 (ART4 & MI4 & WM4 & ST4) PR4.
      rewrite EU in ST4, PR4. rewrite (ret_pc_even 0xb6058) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ1 0 0 m3 m4 OB3 EF1 ltac:(rewrite EL1; auto) ES1 ART4 MI4 ST4 PR4 ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OB4.
      pose proof (agree_of_pres_ex _ _ _ _ _ m3 m4 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) PR4 (fun x H => H)) as AG4.
      clear KEYB KEYL PTRB. xport_stack NODE AG4. xport_stack LOCA2 AG4. xport_stack COUT AG4. xport_stack REC3 AG4. xport_frame FREST AG4 HinF. xport_shadow SH AG4 HinF. xport_stack OUT AG4.

      apply (rw_cells_split_CB asegs _ _ [] 96 jF [] [8; 24; 64]%nat) in FREST; [| reflexivity]. cbn [mk_CB_cells app] in FREST.
      apply (proj1 (rw_cells_app asegs m4 _ [_] _)) in FREST. destruct FREST as [_ FREST]. cbn [cells_size csize Nat.add] in FREST.
      replace (f + 24 + Z.of_nat 8) with (f + 32) in FREST by lia.
      apply (proj1 (rw_cells_app asegs m4 _ [_] _)) in FREST. destruct FREST as [STR FR2]. cbn [cells_size csize Nat.add] in FR2.
      replace (f + 32 + Z.of_nat 24) with (f + 56) in FR2 by lia.
      pose proof MI4 as MI4'.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_p5 E OK _ q b P _ L0 Lk f _ (-8) (-8) (-8) (map (Z_to_bv 8) kb)); [exact MI4| exact LO| lia| lia| lia| lia| lia| ul| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia
        | rewrite length_map; unfold zlength in ZKB; lia| reflexivity| exact LOCA2| | exact STR| | |].
      {   exact SH. }
      +
        intros FBN.
        eapply (obj_noesc RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX m4); [exact OB4| exact FRM| exact EPTR| exact ZL0| exact SLR| exact LKR| exact NODE| | exact COUT| exact REC3| exact SH| exact OUT].
        exact LOCA2.
      +
        intros m5 ix xa0 jS' FB LK23 MU5 WM5 MI5 LOC5 SH5 STR5.
        assert (OW5 : Forall (ownW I) [(b, b + 136); (shad f, shad f + 16); (f + 32, f + 56)]).
        { constructor; [left; unfold oi_b; cbn; lia|]. constructor; [right; right; left; cbn; fold f; lia|]. constructor; [right; left; cbn; fold f; lia| constructor]. }
        pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m4 m5 OB4 EF1 ltac:(rewrite EL1; auto) ES1 MU5 WM5 MI5 OW5) as OB5.
        mport NODE MU5 WM5. mport COUT MU5 WM5. mport REC3 MU5 WM5. mport OUT MU5 WM5.
        lazymatch type of FR2 with rw_cells _ _ _ ?cs => assert (AGF : agree_on (fun x => f + 56 <= x < f + 56 + Z.of_nat (cells_size cs)) m4 m5) end.
        { apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn in Hx. cbn [outside]. clear - Hx FSH FHI LO DDR. lia. }
        apply (fun X => rw_cells_agree asegs m4 m5 _ _ X AGF WM5) in FR2. clear AGF.
        unfold kb in FB.
        eapply (HSSO m5); [exact OB5| exact FRM| exact EPTR| exact ZL0| exact MIN| exact SLR| lia| exact FB| exact NODE| exact LOC5| exact COUT| exact REC3| exact SH5| exact STR5| exact FR2| exact OUT].
      +
        intros m5 ix FB LK23 MU5 WM5 MI5 LOC5 SH5 STR5.
        assert (OW5 : Forall (ownW I) [(b, b + 136); (shad f, shad f + 16); (f + 32, f + 56)]).
        { constructor; [left; unfold oi_b; cbn; lia|]. constructor; [right; right; left; cbn; fold f; lia|]. constructor; [right; left; cbn; fold f; lia| constructor]. }
        pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m4 m5 OB4 EF1 ltac:(rewrite EL1; auto) ES1 MU5 WM5 MI5 OW5) as OB5.
        mport NODE MU5 WM5. mport COUT MU5 WM5. mport REC3 MU5 WM5. mport OUT MU5 WM5.
        lazymatch type of FR2 with rw_cells _ _ _ ?cs => assert (AGF : agree_on (fun x => f + 56 <= x < f + 56 + Z.of_nat (cells_size cs)) m4 m5) end.
        { apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn in Hx. cbn [outside]. clear - Hx FSH FHI LO DDR. lia. }
        apply (fun X => rw_cells_agree asegs m4 m5 _ _ X AGF WM5) in FR2. clear AGF.
        unfold kb in FB.
        eapply (HHEAP m5); [exact OB5| exact FRM| exact EPTR| exact ZL0| exact MIN| exact SLR| lia| exact FB| exact NODE| exact LOC5| exact COUT| exact REC3| exact SH5| exact STR5| exact FR2| exact OUT].
  Qed.

End ObjM.
