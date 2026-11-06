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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit
     Atp_defsA Atp_kitA Atp_arrlA Atp_objdA Atp_objfA Atp_objpA Atp_objkA Atp_objsA Atp_objuA Atp_objkwA Atp_objkyA Atp_objbA Atp_objgA Atp_objxA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac xport_core H AG tac ::=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of AG with agree_on _ _ ?m' =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m')
        by (eapply agree_sub; [exact AG|]; intros ? Hx;
            cbn [cells_size csize Nat.add length obj_hdrB obj_saved atkey_frame atkey_saved obj_loc72 obj_sh pz obj_hdr obj_hdrR obj_shF app] in Hx; cbv beta; tac Hx);
      apply (fun X => rw_cells_agree_nw bsegs m m' A cs X Q) in H; clear Q
    end end.
Local Ltac mport H MU WM ::=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of MU with munch ?W m ?m' =>
      let H2 := fresh "MP" in
      pose proof (rw_cells_transport bsegs W m m' A cs H MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_hdrB obj_saved atkey_frame atkey_saved obj_loc72 obj_sh pz obj_hdr obj_hdrR obj_shF app fst snd];
                          unfold shad, SHB, atkey_W in *; flia)) as H2;
      clear H; rename H2 into H
    end end.

Section ObjCW.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_w78 : forall (K : machine_state -> Prop) (q b f out : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv bsegs m -> ae_lo E + 272 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= out < 2^64 -> 0 <= f < 2^64 ->
    rw_cells bsegs m b (obj_loc72 j0 w24 w32 f out) ->
    K (MS (mkR (wz 0xb8bc0) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz out) (wz (b + 96)) (wz 24) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8bb0) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH OUTR FR LOC HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memcpy in *.
    unfold obj_loc72 in LOC.

    astep. astep. step. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_w00 : forall (K : machine_state -> Prop) (q b code sl : Z)
      (gp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    272 <= q -> q + -272 <= b -> b <= q + -256 -> q < 2^47 -> 0 <= code < 64 -> 0 <= sl < 2^64 ->
    (code <> 0 \/ sl = 18446744073709551615 ->
       forall xa0 : word,
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) xa0 x11 x12 x13 x14 x15 x16 x17
                  (wz sl) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8bb0) fc None m (seg_rom bsegs))) ->
    (code = 0 -> sl <> 18446744073709551615 ->
       K (MS (mkR (wz 0xb8b54) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 136)) (wz sl) (wz 18446744073709551615) x13 x14 x15 x16 x17
                  (wz sl) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz ATP_SUBSTR_A) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz code) x11 x12 x13 x14 x15 x16 x17
                       (wz sl) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8b38) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros QL B0 B1 QH CODE SLR KOUT KSUB. unfold ATP_SUBSTR_A in *.

    step. if_cases K0; zify_cond K0.
    { eapply evt_eq; [| apply evt_done; apply (KOUT ltac:(left; rewrite ?unsigned_lit in K0 by lia; lia))]. atp_st_eq. }
    assert (C0 : code = 0) by (rewrite ?unsigned_lit in K0 by lia; lia). clear K0.

    astep. step. if_cases K1; zify_cond K1.
    { eapply evt_eq; [| apply evt_done; apply (KOUT ltac:(right; rewrite ?unsigned_lit, ?unsigned_lit_land in K1 by lia; revert K1; cbn; intros K1; lia))]. atp_st_eq. }
    assert (SNP : sl <> 18446744073709551615) by (intros ->; apply K1; reflexivity). clear K1.

    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply (KSUB C0 SNP)]. atp_st_eq.
  Qed.

  Lemma obj_w1c : forall (K : machine_state -> Prop) (q b P' L' : Z) (r0 r1 : word)
      (gp x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jc : list byte),
    mem_inv bsegs m -> ae_lo E + 272 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= P' < 2^64 -> 0 <= L' < 2^64 ->
    rw_cells bsegs m (b + 96) [C8 r0; C8 r1; C4 (Z_to_bv 64 0); CB 4 jc] ->
    K (MS (mkR (wz 0xb8b90) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 72)) (wz (b + 96)) (wz P') (wz L') x14 x15 x16 x17
               (wz 0) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz ATP_ELEM_A) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz P') (wz L') x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8b54) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jc. intros MI LO B0 B1 QH PR LR CHILD HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold ATP_ELEM_A in *.

    astep. step. rewrite ?a_sx32_small by lia. astep.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small, ?unsigned_lit in K0 by lia; clear - K0; lia| clear K0].
    step. if_true.

    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_w58 : forall (K : machine_state -> Prop) (q b : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    272 <= q -> q + -272 <= b -> b <= q + -256 -> q < 2^47 ->
    K (MS (mkR (wz 0xb8ba0) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 96)) (wz (b + 72)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8b90) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros QL B0 B1 QH HK. unfold e_asan_memcpy in *.
    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_w68 : forall (K : machine_state -> Prop) (q b code : Z) (r0 r1 cw : word)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (rb jt jc : list byte),
    mem_inv bsegs m -> ae_lo E + 272 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= code < 64 ->
    rw_cells bsegs m (b + 72) [C8 r0; C8 r1; C4 (Z_to_bv 64 code); CB 4 jt] ->
    rw_cells bsegs m (b + 96) [CB 16 rb; C4 cw; CB 4 jc] ->
    (forall (m1 : mem), munch [(b + 112, b + 116)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (b + 96) [CB 16 rb; C4 (Z_to_bv 64 code); CB 4 jc] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz code) (wz 64) x12 x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8bb0) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8ba0) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jc. intros MI LO B0 B1 QH CODE REC CHILD HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(b + 112, b + 116)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. rewrite ?a_sx32_small by lia. astep.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small, ?unsigned_lit in K0 by lia; clear - K0 CODE; lia| clear K0].
    step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| ]].
    - atp_st_eq_goal.
    - lazymatch goal with H : rw_cells bsegs m1 (b + 96) _ |- _ => exact H end.
  Qed.
End ObjCW.

Section ObjC.
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

  Local Ltac ul := unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; flia.

  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.

  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Lemma obj_fin : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 : word)
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
  Proof using AF CTX FDO MST OK.
    intros until cM. intros OB FRM EF EL ES CR LOC CM SZM SH OUTR.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    destruct OUTR as (r0 & rj & code & jn & OUT & C64 & HOK).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).

    pose proof CM as CM'. change (b + 72) with (b + Z.of_nat (cells_size (obj_loc72 j0 w24 w32 f out))) in CM'.
    pose proof (proj2 (rw_cells_app bsegs m b (obj_loc72 j0 w24 w32 f out) cM) (conj LOC CM')) as LOCM. clear CM'.
    assert (SZL : cells_size (obj_loc72 j0 w24 w32 f out ++ cM) = 152%nat) by (cbn [cells_size csize app obj_loc72 length]; rewrite SZM; reflexivity).
    set (cL := obj_loc72 j0 w24 w32 f out ++ cM) in LOCM, SZL. clearbody cL.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_rel1 E OK _ q b f out v4 v5 v6 gp x1);
      [exact MI| exact F64| exact FLO| exact FHI| clear - FSH; lia| exact S0| clear - SHI; lia| ul| flia| exact QHI| exact LOC| exact HDR| exact SH|].
    intros m1 MU1 WM1 MI1 HDR1 SH1.
    assert (FP1 : fp_ok RT Σc (ae_lo E) [(f, f + 8); (shad f, shad f + 16)]).
    { constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; flia].
      - right; right; right. exists f, 1%nat. split; [exact HinF|]. rewrite fs1s. flia. }
    pose proof (art_of_munch RT AF Σc m m1 (ae_lo E) _ ART0 ltac:(rewrite ES; exact LWIN) FP1 MU1 WM1) as ART1.

    clear LOC CM. mport SAVED MU1 WM1. mport HIGH MU1 WM1. mport LOCM MU1 WM1. mport OUT MU1 WM1.
    pose proof (stk_transport_disjoint bsegs _ m m1 (ae_lo E) b ST MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as ST1.

    assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + fs_size 1) /\ ~ (shad f <= a < shad (f + fs_size 1))).
    { intros a Ha. exact (newframe_apart RT AF Σ Σc m f 1%nat q a ART0 EF EL ES ltac:(flia) Ha). }
    rewrite fs1s, fs1 in NEWF.
    assert (AG1 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (NEWF x Hx) as [N1 N2]. unfold shad in *. cbn [outside]. flia. }

    destruct (af_frame_release RT AF Σc m1 f 1%nat (rt_frames RT Σ) ART1 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST & REL).
    rewrite fs1 in LAST. replace (f + 128 - 8) with (f + 120) in LAST by flia. rewrite ES in FL1.
    assert (FLQ : fl < ae_lo E) by ul.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_rel2 _ q b f fl gp x1); [exact MI1| exact FLO| ul| exact FL0| ul| exact LAST| exact FLAG|].
    intros m2 MU2 WM2 MI2 FLAG2.
    destruct (REL m2 MU2 WM2 FLAG2) as (ART2 & EF2 & EL2 & ES2 & EC2 & EA2 & EM2).
    apply (aevt_switch RT PMc Σc Σ2 _ _ EA2 EM2).

    assert (NFL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> a <> fl).
    { intros a Ha ->. apply NAC. rewrite EL, EF. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
      - exfalso. ul.
      - right; left. exact Ha.
      - right; right; left. exact Ha.
      - right; right; right; left. destruct Ha as (f1 & k1 & Hin & Hr). exists f1, k1. split; [right; exact Hin| exact Hr].
      - right; right; right; right. destruct Ha as (f1 & k1 & Hin & Hr). exists f1, k1. split; [right; exact Hin| exact Hr]. }
    assert (AG2 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. pose proof (NFL x Hx). cbn [outside]. flia. }
    mport SAVED MU2 WM2. mport HIGH MU2 WM2. mport LOCM MU2 WM2. mport OUT MU2 WM2.
    pose proof (stk_transport_disjoint bsegs _ m1 m2 (ae_lo E) b ST1 MU2 WM2 ltac:(cbn; flia)) as ST2.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_epi E OK _ q b dd ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
      [exact MI2| ul| exact QHI| exact Hdd| reflexivity| exact ST2| exact LOCM| exact SZL| exact HIGH| exact SAVED|].
    intros STQ. apply (aevt_done RT PMc). intros cf Hc. split.
    2:{ apply (cfrm0_of_asta RT Σ2 PMc _ cf Hc). intros ms <-. exact FRM. }
    eapply (lvl_postA_intro RT E Σ Σ2 PMc cf); [exact Hc| exact ART2| exact MI2| exact STQ| | | | rewrite EL2; exact EL| exact EF2| rewrite ES2; exact ES| rewrite EC2; exact CR].
    - eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha _. rewrite (AG2 _ Ha). exact (AG1 _ Ha).
    - exists r0, rj, code, jn. split; [exact OUT|]. split; [exact C64| exact HOK].
    - apply (AINV_A_agree E m m2 AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX. rewrite (AG2 _ CX). exact (AG1 _ CX).
  Qed.

  Lemma obj_copyout : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 : Z) (js4 jo j0 : list byte) (cR cK : list cell),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cR -> cells_size cR = 24%nat -> out_recA E m (oi_b I + 96) ->
    rw_cells bsegs m (oi_b I + 120) cK -> cells_size cK = 32%nat ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb8bb0) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2.
    intros until cK. intros OB FRM EF EL ES CR LOC CRR SZR RECO CK SZK SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    destruct RECO as (r0 & rj & code & jn & REC & C64 & HOK).
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σc m (oi_b I) ES ST ltac:(lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK.

    destruct (rw_cells_forget _ _ _ _ CRR) as [j1 CR1]. rewrite SZR in CR1. destruct (rw_cells_forget _ _ _ _ CK) as [j3 CK3]. rewrite SZK in CK3. clear CRR CK.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w78 E OK _ q b f out); [exact MI| ul| flia| flia| exact QHI| ul| ul| exact LOC|].
    pose proof (rw_cells_bytes_at bsegs m _ _ REC) as RB. set (rbs := cells_bytes _) in RB.
    assert (LRB : length rbs = 24%nat) by (subst rbs; exact (cells_bytes_length _ (proj1 (proj1 REC)))).
    eapply (aevt_memcpyP RT RC PMc FDO MST Σc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out (b + 96) rbs (ae_lo E));
      [reflexivity| reflexivity| rewrite LRB; reflexivity| ul| ul| rewrite LRB; cbn; flia| exact RB| | | rewrite LRB; cbn; flia| exact ART0| exact MI| exact COK|].
    { rewrite LRB. apply (checked_src_stack RT AF Σc m _ (ae_lo E) (b + 96) 24 ART0); [ul| ul| rewrite EU; flia]. }
    { rewrite LRB. apply (checked_dst_stack RT AF Σc m _ out 24 ART0); [ul| ul| rewrite EU; flia| exact (proj2 OUT)]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PR' BY'.
    rewrite EU in ST', PR'. rewrite LRB in PR'. change (Z.of_nat 24) with 24 in PR'.
    rewrite (ret_pc_even 0xb8bc0) by flia.

    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σc) (rt_frames RT Σc) b x /\ ~ (out <= x < out + 24)) PR' (fun x H => H)) as AG.
    clear RB. pose proof (proj2 OUT) as WOUT. clear OUT. cbn [cells_size csize Nat.add] in WOUT.
    xport_stack LOC AG. xport_stack CR1 AG. xport_stack REC AG. xport_stack CK3 AG. xport_shadow SH AG HinF.
    assert (OUT' : rw_cells bsegs m' out [CB 24 rbs]).
    { rewrite <- LRB. apply rw_cells_CB_intro; [exact BY'|]. rewrite LRB. exact (wr_at_transport bsegs m m' _ _ WOUT WM'). }
    assert (OUTR' : out_recA E m' out).
    { exists r0, rj, code, jn. split; [| split; [exact C64| exact HOK]].
      eapply rw_cells_recastA; [exact OUT'| exact (proj1 (proj1 REC))|].
      change (cells_bytes [CB 24 rbs]) with (rbs ++ []). rewrite app_nil_r. subst rbs. reflexivity. }
    assert (OBK' : obaseK RT E Σ I Σc m').
    { apply (obaseK_call RT AF E OK d Σ Σ1 I CTX Σc b out 24 m m');
        [exact (proj1 OB0)| exact EF| rewrite EL; auto| exact ES| exact ART'| exact MI'| olia| exact PR'| intros a Ha _; exact Ha| right; left; olia| right; left; olia]. }
    assert (CM' : rw_cells bsegs m' (b + 72) ([CB 24 j1] ++ ([C8 r0; C8 (Z_to_bv 64 rj); C4 (Z_to_bv 64 code); CB 4 jn] ++ [CB 32 j3]))).
    { apply (proj2 (rw_cells_app bsegs m' _ _ _)). split; [exact CR1|]. cbn [cells_size csize Nat.add]. replace (b + 72 + Z.of_nat 24) with (b + 96) by lia.
      apply (proj2 (rw_cells_app bsegs m' _ _ _)). split; [exact REC|]. cbn [cells_size csize Nat.add]. replace (b + 96 + Z.of_nat 24) with (b + 120) by lia. exact CK3. }
    cbn [app] in CM'.
    eapply (obj_fin Σc m'); [exact (conj OBK' ST')| exact FRM| exact EF| exact EL| exact ES| exact CR| exact LOC| exact CM'| reflexivity| exact SH| exact OUTR'].
  Qed.

  Lemma obj_tails : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 r0 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 code sl L0 vj : Z) (rest : list Z) (js4 jo j0 jc : list byte) (cR cK : list cell),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> 0 <= sl < 2^64 -> 0 <= code < 64 ->
    (code = 0 -> r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= vj /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ j' <= ae_n E - 1) ->
    ( ((code <> 0 \/ sl = 18446744073709551615) /\ rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc)
      \/ (code = 0 /\ 0 <= sl < L0 /\ rt_credit RT Σ - obj_costA d (oi_L I) + elem_costA d (L0 - sl) <= rt_credit RT Σc) ) ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cR -> cells_size cR = 24%nat ->
    rw_cells bsegs m (oi_b I + 96) [C8 r0; C8 (Z_to_bv 64 vj); C4 (Z_to_bv 64 code); CB 4 jc] ->
    rw_cells bsegs m (oi_b I + 120) cK -> cells_size cK = 16%nat ->
    rw_cells bsegs m (oi_b I + 136) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz code) x11 x12 x13 x14 x15 x16 x17
               (wz sl) (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb8b38) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until cK. intros OB FRM EF EL ES EPTR ZL0 SL64 HC HERR CRD LOC CRR SZR REC CK0 SZK SV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    pose proof (fun a => obj_split RT AF E d Σ Σ1 I CTX Σc m a ART0 EF ltac:(rewrite EL; auto) ES) as SPLIT.
    pose proof (fun sp a => obj_mono RT Σ I Σc sp a EF ltac:(rewrite EL; auto)) as MONO.

    destruct (rw_cells_forget _ _ _ _ CRR) as [jco CR72]. rewrite SZR in CR72. destruct (rw_cells_forget _ _ _ _ CK0) as [jk CK]. rewrite SZK in CK. clear CRR CK0 SZR SZK.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ P1F _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    rewrite EPTR in PL, PB2. rewrite zlength_cons in PL, PB2. pose proof (zlength_nonneg rest) as ZLN.
    pose proof (a_live_mono RT Σ Σc E LV ltac:(rewrite EL; auto) ltac:(rewrite EF; intros x Hx; right; exact Hx) ES) as LVc.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w00 _ q b code sl); [ul| flia| flia| ul| exact HC| exact SL64| |].
    {
      intros HX xa0.
      assert (CR1 : rt_credit RT Σ - obj_costA d (zlength ptr) <= rt_credit RT Σc)
        by (destruct CRD as [[_ X]|(_ & Y & X)]; [exact X| unfold elem_costA, obj_costA, LVL_C1, DCOST in *; flia]).
      pose proof SV as SV'. replace (b + 136) with (b + 120 + Z.of_nat (cells_size [CB 16 jk])) in SV' by (cbn; lia).
      pose proof (proj2 (rw_cells_app bsegs m (b + 120) [CB 16 jk] _) (conj CK SV')) as CKV. cbn [app] in CKV.
      eapply (obj_copyout Σc m); [exact OB0| exact FRM| exact EF| exact EL| exact ES| exact CR1| exact LOC| exact CR72| reflexivity| | exact CKV| reflexivity| exact SH| exact OUT].
      exists r0, vj, code, jc. split; [exact REC|]. split; [exact HC|]. intros C0. destruct (HERR C0) as (R0 & VJ0 & j' & ELV & JN).
      split; [exact R0|]. split; [exact VJ0|]. exists d, j'. split; [exact ELV| exact JN]. }

    intros C0 SNP. destruct (HERR C0) as (R0 & VJ0 & j' & ELV & JN).
    destruct CRD as [[[X|X] _]|(_ & SLR' & CR)]; [exfalso; exact (X C0)| exfalso; exact (SNP X)|]. clear HERR. subst r0. subst code.
    assert (CST : 0 <= elem_costA d (L0 - sl) /\ 0 <= rt_credit RT Σ - obj_costA d (zlength ptr)) by (unfold elem_costA, obj_costA, LVL_C1, DCOST in *; flia).

    apply (aevt_evt RT AF PMc MST).
    assert (FPW : fp_client RT Σc (ae_lo E) [(b + -16, b)]) by (apply fp_client_stack1; ul).
    assert (SHZS : forall m', munch [(b + -16, b)] m m' -> wmono bsegs m m' -> shz m' (b + 136) 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σc m' (b + 136) 16 (lvl_art_munch RT AF E Σc _ m m' ART0 LVc FPW MU WM) LVc);
        first [ul| reflexivity| clear - B32; Z.div_mod_to_equations; lia]. }
    pose proof (shb_cells_of_art RT AF Σc m ART0) as SHBC.
    eapply (substr_cps E OK _ m F fc b (b + 136) (P + 1) L0 sl 18446744073709551615 (L0 - sl) 0xb8b54);
      [exact SV| flia| ul| clear - B32; Z.div_mod_to_equations; lia| flia| flia| ul| left; split; reflexivity| exact SHBC| exact SHZS
      | exact ST| ul| ul| exact B16| exact MI| flia| reflexivity|].
    clear SHZS SHBC FPW. intros m2 xa2 xa3 xa4 xa5 MU12 WM12 MI2 ST2.
    assert (OW2 : Forall (ownW I) [(b + -16, b)]) by (constructor; [left; cbn [fst snd]; olia| constructor]).
    pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σc _ m m2 (proj1 OB0) EF ltac:(rewrite EL; auto) ES MU12 WM12 MI2 OW2) as OBK2.
    pose proof (proj1 (proj2 OBK2)) as ART2. pose proof (proj1 (proj2 (proj2 OBK2))) as AI2.
    mport LOC MU12 WM12. mport CR72 MU12 WM12. mport REC MU12 WM12. mport CK MU12 WM12. mport SV MU12 WM12. mport SH MU12 WM12. mport OUT MU12 WM12.
    clear MI ST MU12 WM12 OW2.

    eapply (obj_w1c E OK _ q b (P + 1 + sl) (L0 - sl) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 vj)); [exact MI2| ul| flia| flia| exact QHI| ul| ul| exact REC|]. cbv beta.

    set (ptr' := skipn (S (Z.to_nat sl)) ptr).
    assert (ZL' : zlength ptr' = L0 - sl).
    { subst ptr'. rewrite zlength_skipn by (rewrite EPTR; cbn [length]; unfold zlength in ZL0; flia). rewrite EPTR, zlength_cons. flia. }
    assert (PAT' : ptr_atA E (P + 1 + sl) ptr').
    { subst ptr'. replace (P + 1 + sl) with (P + Z.of_nat (S (Z.to_nat sl))) by flia. apply ptr_atA_skip; [exact PAT|].
      rewrite EPTR. cbn [length]. unfold zlength in ZL0. flia. }
    apply (proj1 (rw_cells_app bsegs m2 _ [_; _] _)) in REC. destruct REC as [RECN RECE]. cbn [cells_size csize Nat.add] in RECE.
    replace (b + 96 + Z.of_nat 16) with (b + 112) in RECE by flia.
    assert (PRE' : lvl_pre RT E Σc m2 b (b + 72) (b + 96) vj jco (elem_needA d) (elem_costA d (zlength ptr')) d).
    { unfold lvl_pre. rewrite ZL', EF, EL. split; [exact RECN|]. split; [flia|]. split; [ul|]. split; [clear - B32; Z.div_mod_to_equations; lia|].
      split; [exact CR72|]. split; [flia|]. split; [ul|]. split; [clear - B32; Z.div_mod_to_equations; lia|]. split; [right; flia|].
      split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [ul|]. split; [exact B16|].
      split; [cbn [length]; flia|]. split; [flia| exact LVB]. }
    eapply (aevt_rt RT PMc Σc _ _ _); [| exact FRM|].
    { rewrite <- ZL'. exact (HELEM Σc PMc ptr' vj j' b (b + 72) (b + 96) (P + 1 + sl) (wz 0xb8b90) gp x5 x6 x7 (wz q) (wz b) xa4 xa5 x16 x17
                                    (wz 0) (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31 F fc m2 jco
                                    FDO MST LVc AI2 PAT' ELV VJ0 JN PRE' FRM). }
    intros cf (Σ' & HA & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HA|].
    intros ms' (v & m' & RS & (ART' & MI' & ST') & PFP & OUTR' & AI') FRM'.
    destruct RS as (u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & F' & fc' & ->). cbn in FRM'.
    rewrite (ret_pc_even 0xb8b90) by flia. rewrite ZL' in E4.

    assert (AG : agree_on (fun x => aclient (rt_live RT Σc) (rt_frames RT Σc) b x /\ ~ (b + 72 <= x < b + 96)) m2 m').
    { intros a [Ha Hn]. apply PFP; [exact Ha|]. cbn [outside]. split; [flia| exact Logic.I]. }

    clear SAVED HIGH HDR PRES. destruct OBK2 as (_ & _ & _ & SAVED & HIGH & HDR & PRES2). unfold oi_b in HIGH. fold q dd in HIGH. fold b in HIGH.
    xport_stack SAVED AG. xport_stack HIGH AG. xport_frame HDR AG HinF.
    assert (PRES' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m0 m').
    { eapply rt_pres_fp_trans; [exact PRES2|]. intros a Ha Ho. apply PFP; [exact (MONO b _ ltac:(flia) Ha)|].
      cbn [outside]. split; [| exact Logic.I]. destruct (SPLIT _ Ha); flia. }
    assert (OBK' : obaseK RT E Σ I Σ' m') by exact (conj MI' (conj ART' (conj AI' (conj SAVED (conj HIGH (conj HDR PRES')))))).
    clear CR72 PFP PRES2. xport_stack LOC AG. xport_stack RECN AG. xport_stack RECE AG. xport_stack CK AG. xport_stack SV AG. xport_shadow SH AG HinF. xport_stack OUT AG.
    clear AG ART2 AI2 MI2 ST2.

    destruct OUTR' as (cw0 & cj & ccode & cjn & R72 & CC64 & CHOK).
    apply (aevt_evt RT AF PMc MST).
    apply (obj_w58 _ q b); [ul| flia| flia| ul|].
    pose proof R72 as CO16. apply (proj1 (rw_cells_app bsegs m' _ [_; _] _)) in CO16. destruct CO16 as [CO16 _].
    pose proof (rw_cells_bytes_at bsegs m' _ _ CO16) as RB. set (rb := cells_bytes _) in RB.
    assert (LRB : length rb = 16%nat) by (subst rb; exact (cells_bytes_length _ (proj1 (proj1 CO16)))).
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ' m' b ltac:(rewrite E3; exact ES) ST' ltac:(olia) B16) as COK'.
    assert (HinF' : In (f, 1%nat) (rt_frames RT Σ')) by (rewrite E2; exact HinF).
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' (b + 96) (b + 72) rb (ae_lo E));
      [reflexivity| reflexivity| rewrite LRB; reflexivity| ul| ul| rewrite LRB; cbn; flia| exact RB| | | rewrite LRB; cbn; flia| exact ART'| exact MI'| exact COK'|].
    { rewrite LRB. apply (checked_src_stack RT AF Σ' m' _ (ae_lo E) (b + 72) 16 ART'); [rewrite E3; ul| ul| rewrite EU; flia]. }
    { rewrite LRB. apply (checked_dst_stack RT AF Σ' m' _ (b + 96) 16 ART'); [rewrite E3; ul| ul| rewrite EU; flia| exact (proj2 RECN)]. }
    intros t0' t1' t2' b1' b2' b3' b4' b5' b6' b7' t3' t4' t5' t6' F2 m3 (ART3 & MI3 & WM3 & ST3) PR3 BY3.
    rewrite EU in ST3, PR3. rewrite LRB in PR3. change (Z.of_nat 16) with 16 in PR3.
    rewrite (ret_pc_even 0xb8ba0) by flia.
    pose proof (agree_of_pres_ex _ _ _ _ _ m' m3 (fun x => aclient (rt_live RT Σ') (rt_frames RT Σ') b x /\ ~ (b + 96 <= x < b + 96 + 16)) PR3 (fun x H => H)) as AG3.
    clear RB CO16. pose proof (proj2 RECN) as WREC. clear RECN. cbn [cells_size csize Nat.add] in WREC.
    xport_stack LOC AG3. xport_stack R72 AG3. xport_stack RECE AG3. xport_stack CK AG3. xport_stack SV AG3. xport_shadow SH AG3 HinF'. xport_stack OUT AG3.
    assert (REC3 : rw_cells bsegs m3 (b + 96) [CB 16 rb; C4 (Z_to_bv 64 0); CB 4 jc]).
    { change [CB 16 rb; C4 (Z_to_bv 64 0); CB 4 jc] with ([CB 16 rb] ++ [C4 (Z_to_bv 64 0); CB 4 jc]).
      apply (proj2 (rw_cells_app bsegs m3 _ [CB 16 rb] _)). split.
      - rewrite <- LRB. apply rw_cells_CB_intro; [exact BY3|]. rewrite LRB. exact (wr_at_transport bsegs m' m3 _ _ WREC WM3).
      - cbn [cells_size csize Nat.add]. replace (b + 96 + Z.of_nat 16) with (b + 112) by flia. exact RECE. }
    assert (OBK3 : obaseK RT E Σ I Σ' m3).
    { apply (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ' b (b + 96) 16 m' m3);
        [exact OBK'| rewrite E2; exact EF| rewrite E1, EL; auto| rewrite E3; exact ES| exact ART3| exact MI3| olia| exact PR3
        | intros a Ha Hc; exfalso; destruct (SPLIT a Hc); olia| left; olia| right; left; olia]. }
    clear AG3 PR3 BY3 RECE WREC WM3 OBK' ART' MI' ST'.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w68 E OK _ q b ccode cw0 (Z_to_bv 64 cj) (Z_to_bv 64 0)); [exact MI3| ul| flia| flia| exact QHI| exact CC64| exact R72| exact REC3|].
    intros m4 MU4 WM4 MI4 REC4.
    assert (OW4 : Forall (ownW I) [(b + 112, b + 116)]) by (constructor; [left; cbn [fst snd]; olia| constructor]).
    pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ' _ m3 m4 OBK3 ltac:(rewrite E2; exact EF) ltac:(rewrite E1, EL; auto) ltac:(rewrite E3; exact ES) MU4 WM4 MI4 OW4) as OBK4.
    pose proof (stk_transport_disjoint bsegs _ m3 m4 (ae_lo E) b ST3 MU4 WM4 ltac:(cbn; flia)) as ST4.
    clear REC3. mport LOC MU4 WM4. mport R72 MU4 WM4. mport CK MU4 WM4. mport SV MU4 WM4. mport SH MU4 WM4. mport OUT MU4 WM4.

    destruct (rw_cells_forget _ _ _ _ R72) as [jr R72']. cbn [cells_size csize Nat.add] in R72'.
    pose proof SV as SV'. replace (b + 136) with (b + 120 + Z.of_nat (cells_size [CB 16 jk])) in SV' by (cbn; lia).
    pose proof (proj2 (rw_cells_app bsegs m4 (b + 120) [CB 16 jk] _) (conj CK SV')) as CKV. cbn [app] in CKV.
    eapply (obj_copyout Σ' m4); [exact (conj OBK4 ST4)| exact FRM'| rewrite E2; exact EF| rewrite E1; exact EL| rewrite E3; exact ES| olia
      | exact LOC| exact R72'| reflexivity| | exact CKV| reflexivity| exact SH| exact OUT].
    exists cw0, cj, ccode, jc. split; [| split; [exact CC64| exact CHOK]].
    replace rb with (le8 cw0 ++ le8 (Z_to_bv 64 cj)) in REC4 by (subst rb; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity).
    exact (rec_node16 m4 _ _ _ _ REC4).
  Qed.
End ObjC.
