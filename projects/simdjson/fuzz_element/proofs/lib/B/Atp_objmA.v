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
     I_lkit Atp_defsA Atp_kitA Atp_arrlA Atp_objdA Atp_objfA Atp_objpA Atp_objkA Atp_objsA Atp_objuA Atp_objkwA Atp_objkyA Atp_objbA Atp_objgA Atp_objxA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

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
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.

  Definition esc_sso_stmt : Prop :=
    forall (m : mem) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
           (sl Lk L0 L : Z) (ix : nat) (rest : list Z) (js4 jo j0 jC j2 jS' jR : list byte) (w24 w32 : word),
      obase RT E Σ I Σ1 m -> frm0 fc ->
      oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl = 18446744073709551615 /\ Lk = L0) \/ (0 <= sl < L0 /\ Lk = sl)) ->
      0 < Lk < 23 -> find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix ->
      rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
      rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
      rw_cells bsegs m (oi_b I + 72) [CB 24 jC] ->
      rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
      rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
      rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) ->
      rw_cells bsegs m (oi_f I + 32) [C1 (Z_to_bv 8 (2 * Lk)); CB 23 jS'] -> rw_cells bsegs m (oi_f I + 56) [CB 64 jR] ->
      rw_cells bsegs m (oi_out I) [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (2 * Lk)) (wz (oi_f I)) x12 x13 x14 x15 x16 x17
                 (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) (wz L) (wz (oi_f I + 32)) (wz (Z.of_nat ix)) (wz Lk) (wz (oi_P I + 1)) (wz (oi_f I + 33)) (wz 2147450880) x28 x29 x30 x31)
            F (wz 0xb895c) fc None m (seg_rom bsegs)).

  Definition esc_heap_stmt : Prop :=
    forall (m : mem) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
           (sl Lk L0 : Z) (ix : nat) (rest : list Z) (js4 jo j0 jC j2 jS jR : list byte) (w24 w32 : word),
      obase RT E Σ I Σ1 m -> frm0 fc ->
      oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl = 18446744073709551615 /\ Lk = L0) \/ (0 <= sl < L0 /\ Lk = sl)) ->
      23 <= Lk -> find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix ->
      rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
      rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
      rw_cells bsegs m (oi_b I + 72) [CB 24 jC] ->
      rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
      rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
      rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) ->
      rw_cells bsegs m (oi_f I + 32) [CB 24 jS] -> rw_cells bsegs m (oi_f I + 56) [CB 64 jR] ->
      rw_cells bsegs m (oi_out I) [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR (wz 0xb8948) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (str_sz Lk)) (wz (oi_f I)) x12 x13 x14 x15 x16 x17
                 (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) (wz (str_sz Lk)) (wz (oi_f I + 32)) (wz (Z.of_nat ix)) (wz Lk) (wz (oi_P I + 1)) x26 (wz 2147450880) x28 x29 x30 x31)
            F (wz OPNEW_A) fc None m (seg_rom bsegs)).

  Hypothesis HSSO : esc_sso_stmt.
  Hypothesis HHEAP : esc_heap_stmt.

  Lemma obj_esc : forall (m : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y7 y8 y9 y10 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl Lk L0 L : Z) (ix : nat) (rest : list Z) (v4 v5 v6 : Z) (js4 jo j0 jC j2 jS jR : list byte) (w24 w32 : word),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> ((sl = 18446744073709551615 /\ Lk = L0) \/ (0 <= sl < L0 /\ Lk = sl)) ->
    (Z.of_nat ix < Lk) -> find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) [CB 24 jC] ->
    rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) ->
    rw_cells bsegs m (oi_f I + 32) [CB 24 jS] -> rw_cells bsegs m (oi_f I + 56) [CB 64 jR] ->
    rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (Z.of_nat ix)) x11 x12 x13 x14 x15 x16 x17
               (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) (wz L) (wz (oi_P I)) y7 y8 y9 y10 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb8844) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK HSSO HHEAP.
    intros until w32. intros OB FRM EPTR ZL0 SL IXL FB NODE LOC REC CHILD SV4 SH STR R56 OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (LO : ae_lo E + 432 <= q) by ul.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    rewrite EPTR, zlength_cons in PB2. pose proof (zlength_nonneg rest) as ZLN.
    assert (LKR : 0 < Lk <= L0) by (clear - SL IXL ZLN ZL0; lia).
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_e0 E OK _ q b out node P L f (P + 1) Lk sl (Z.of_nat ix) v4 v5 v6);
      [exact MI| ul| flia| flia| exact QHI| clear - LKR PB0 PB1 PB2 PB3 ZL0 LOW HL HT; ul| clear - PB0 PB1; lia| clear - LKR PB0 PB1 PB2 PB3 ZL0 HL HT; ul
      | exact FLO| exact FHI| clear - FSH; lia| exact S0| flia| exact LOC| | exact SH| exact STR| |].
    {
      apply (proj1 (rw_cells_app bsegs m _ [_; _] _)) in SV4. destruct SV4 as [KSV _]. exact KSV. }
    -
      intros m1 jS' LK23 MU1 WM1 MI1 SH1 STR1.
      assert (FP1 : fp_ok RT Σ1 (ae_lo E) [(shad f, shad f + 16); (f + 32, f + 56)]).
      { constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; right; right. exists f, 1%nat. split; [exact HinF|]. rewrite fs1s. flia.
        - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; flia]. }
      pose proof (art_of_munch RT AF Σ1 m m1 (ae_lo E) _ ART0 ltac:(rewrite ES1; exact LWIN) FP1 MU1 WM1) as ART1.
      mport SAVED MU1 WM1. mport HIGH MU1 WM1. mport NODE MU1 WM1. mport LOC MU1 WM1. mport REC MU1 WM1. mport CHILD MU1 WM1. mport SV4 MU1 WM1. mport OUT MU1 WM1.

      pose proof (rw_cells_transport bsegs _ m m1 _ _ HDR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_hdrB app fst snd]; unfold shad, SHB in *; clear - FSH; lia)) as HDR1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ R56 MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; unfold shad, SHB in *; clear - FSH; lia)) as R561.
      clear HDR R56. rename HDR1 into HDR. rename R561 into R56.
      pose proof (stk_transport_disjoint bsegs _ m m1 (ae_lo E) b ST MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as ST1.
      assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + fs_size 1) /\ ~ (shad f <= a < shad (f + fs_size 1))).
      { intros a Ha. exact (newframe_apart RT AF Σ Σ1 m f 1%nat q a ART0 EF1 EL1 ES1 ltac:(flia) Ha). }
      rewrite fs1s, fs1 in NEWF.
      assert (AG1 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m m1).
      { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (NEWF x Hx) as [N1 N2]. unfold shad in *. cbn [outside]. flia. }
      eapply (HSSO m1); [| exact FRM| exact EPTR| exact ZL0| exact SL| clear - LKR LK23; lia| exact FB| exact NODE| exact LOC| exact REC| exact CHILD| exact SV4| exact SH1| exact STR1| exact R56| exact OUT].
      split; [| exact ST1]. split; [exact MI1|]. split; [exact ART1|]. split.
      { apply (AINV_A_agree E m m1 AI). intros x Hx. exact (AG1 _ (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx)). }
      split; [exact SAVED|]. split; [exact HIGH|]. split; [exact HDR|].
      eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha _. exact (AG1 _ Ha).
    -
      intros m1 LK23 MU1 WM1 MI1 SH1 STR1.
      assert (FP1 : fp_ok RT Σ1 (ae_lo E) [(shad f, shad f + 16); (f + 32, f + 56)]).
      { constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; right; right. exists f, 1%nat. split; [exact HinF|]. rewrite fs1s. flia.
        - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; flia]. }
      pose proof (art_of_munch RT AF Σ1 m m1 (ae_lo E) _ ART0 ltac:(rewrite ES1; exact LWIN) FP1 MU1 WM1) as ART1.
      mport SAVED MU1 WM1. mport HIGH MU1 WM1. mport NODE MU1 WM1. mport LOC MU1 WM1. mport REC MU1 WM1. mport CHILD MU1 WM1. mport SV4 MU1 WM1. mport OUT MU1 WM1.

      pose proof (rw_cells_transport bsegs _ m m1 _ _ HDR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_hdrB app fst snd]; unfold shad, SHB in *; clear - FSH; lia)) as HDR1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ R56 MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length app fst snd]; unfold shad, SHB in *; clear - FSH; lia)) as R561.
      clear HDR R56. rename HDR1 into HDR. rename R561 into R56.
      pose proof (stk_transport_disjoint bsegs _ m m1 (ae_lo E) b ST MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as ST1.
      assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + fs_size 1) /\ ~ (shad f <= a < shad (f + fs_size 1))).
      { intros a Ha. exact (newframe_apart RT AF Σ Σ1 m f 1%nat q a ART0 EF1 EL1 ES1 ltac:(flia) Ha). }
      rewrite fs1s, fs1 in NEWF.
      assert (AG1 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m m1).
      { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (NEWF x Hx) as [N1 N2]. unfold shad in *. cbn [outside]. flia. }
      eapply (HHEAP m1); [| exact FRM| exact EPTR| exact ZL0| exact SL| exact LK23| exact FB| exact NODE| exact LOC| exact REC| exact CHILD| exact SV4| exact SH1| exact STR1| exact R56| exact OUT].
      split; [| exact ST1]. split; [exact MI1|]. split; [exact ART1|]. split.
      { apply (AINV_A_agree E m m1 AI). intros x Hx. exact (AG1 _ (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx)). }
      split; [exact SAVED|]. split; [exact HIGH|]. split; [exact HDR|].
      eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha _. exact (AG1 _ Ha).
  Qed.
End ObjM.
