(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow Zcn.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Zq3
     Zqc Zqd Zqb I_lkit Z45 Z5k Z5q Z6b Z60 Z5o Z5w
     Z61 Z6e Z6h Z5s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma sso_az : forall (m : mem) f js4, f mod 64 = 0 -> 0 <= f -> rw_cells bsegs m (shad f) (obj_sh 0 0 0 js4) -> acc bsegs m (f + 32) 24 /\ shz m (f + 32) 24.
Proof.
  intros m f js4 F64 F0 SH.
  pose proof (rw_cells_bytes_at bsegs m _ _ SH) as B. unfold obj_sh, pz in B. cbn [cells_bytes cbytes app] in B.
  assert (B3 : bytes_at bsegs m (shad (f + 32)) (repeat z8 3)).
  { assert (ES : shad (f + 32) = shad f + Z.of_nat 4) by (unfold shad; replace (f + 32) with (f + 4 * 8) by lia; rewrite Z.div_add by lia; lia). rewrite ES.
    pose proof (bytes_at_firstn _ _ _ 3 (bytes_at_skipn _ _ _ 4 B ltac:(cbn; lia))) as X. cbn [firstn skipn le1] in X.
    rewrite (a_u64_small 0) in X by lia. exact X. }
  assert (A8 : (f + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  split; [exact (acc_zero_run bsegs m (f + 32) 3 A8 ltac:(lia) B3)|].
  pose proof (shz_of_zero_run m (f + 32) 3 A8 ltac:(lia) B3) as S. exact S.
Qed.

Section ObjES.
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
  Hypothesis LPOS : forall p n, In (p, n) (rt_live RT Σ) -> exists n', In (p, n') (rt_live RT Σ) /\ 0 < n'.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.

  Definition atkey_stmtB : Prop :=
    forall (Σc : rts RT) (m : mem) (K : config -> Prop) (x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
           (Kp Lk' slv : Z) (kb : list byte) (cS : list cell),
      obase RT E Σ I Σc m -> frm0 fc ->
      rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
      rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
      rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat ->
      bytes_at bsegs m Kp kb -> Z.of_nat (length kb) = Lk' -> 0 <= Lk' < 2^26 -> 0 < Kp -> Kp + Lk' <= ae_lo E ->
      (forall m', ART RT Σc m' -> agree_on (PK RT Σc (oi_b I)) m m' -> checked_src RT Σc m' (wz (oi_b I + -144)) (ae_lo E) Kp Lk') ->
      (forall a, Kp <= a < Kp + Lk' -> aclient (rt_live RT Σc) (rt_frames RT Σc) (oi_b I + -144) a) ->
      (forall (m' : mem) (rd ri code : Z) (jt : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (F' : bvmap 5 word),
         obase RT E Σ I Σc m' -> mem_inv bsegs m' ->
         (forall a : word, aclient (rt_live RT Σc) (rt_frames RT Σc) (oi_b I) (bv_unsigned a) -> ~ (oi_b I + 72 <= bv_unsigned a < oi_b I + 96) -> m' a = m a) ->
         rw_cells bsegs m' (oi_b I + 72) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 code); CB 4 jt] -> 0 <= code < 64 ->
         (code = 20 \/ (code = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
         aevt RT PMc Σc K
           (MS (mkR (wz 0x99ed4) (wz (oi_b I)) (oi_gp I) (wz TPV) y5 y6 y7 (wz (oi_q I)) (wz (oi_b I)) y10 y11 y12 y13 y14 y15 y16 y17
                    (wz slv) (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) y28 y29 y30 y31)
               F' (wz 0x99ed4) fc None m' (seg_rom bsegs))) ->
      aevt RT PMc Σc K
        (MS (mkR (wz 0x99ed4) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (oi_b I + 72)) (wz (oi_node I)) (wz Kp) (wz Lk') x14 x15 x16 x17
                 (wz slv) (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
            F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs)).
  Hypothesis HATK : atkey_stmtB.
  Hypothesis HFIN : fin_stmtB RT E d PMc Σ I.

  Section SCtx.
  Variables (lg : bool) (D cap Lk sl L0 : Z) (rest : list Z) (Σ2 : rts RT).
  Hypothesis SC : sctx RT Σ Σ1 I lg D cap Lk sl L0 rest Σ2.
  Local Notation SCNUM := (sc_num RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCCLS := (sc_cls RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCEL := (sc_el RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).

  Lemma str_az : forall (m : mem) js4, ART RT Σ2 m -> rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> acc bsegs m D cap /\ shz m D (Lk + 1).
  Proof using SC CTX AF OK.
    intros m js4 ART2 SH. pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 F64 _ _ _ _ _ _].
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    destruct lg eqn:LG.
    - destruct (sc_long _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (EL & ECAP & LK23 & D16 & _).
      split; [exact (proj2 (af_acc_live RT AF Σ2 m D cap ART2 (IND eq_refl)))|].
      pose proof (shz_live RT AF Σ2 m D cap ART2 (IND eq_refl) ltac:(clear - D16; Z.div_mod_to_equations; lia)) as X.
      apply (shz_sub m D (8 * (cap / 8))); [exact X| lia|].
      rewrite ECAP. unfold str_sz. destruct (Z.eqb_spec Lk 23) as [->|NE]; [cbn; lia|]. rewrite (lor7_eqB Lk) by lia.
      clear - NE LKR. Z.div_mod_to_equations. lia.
    - destruct (sc_short _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (ED & ECAP & LK23 & _).
      unfold obj_sh, pz in SH. destruct (sso_az m (oi_f I) js4 F64 ltac:(lia) SH) as [A S]. rewrite ED, ECAP.
      split; [apply (acc_sub bsegs m (oi_f I + 32) 24); [exact A| lia| lia]| apply (shz_sub m (oi_f I + 32) 24); [exact S| lia| lia]].
  Qed.

  Hypothesis HTAILS : tails_stmtB RT E d PMc Σ I Lk sl L0.

  Lemma esc_afterB : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (sz : Z) (js4 jo j0 j2 : list byte) (cS : list cell),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> sz <= Lk ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 (oi_node I)) (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat ->
    rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz LIT_SLASH_A) (wz (shad (oi_f I))) (wz LIT_TILDE_A) (wz 49) (wz (oi_f I + 32)) (wz 18446744073709551615) (wz (oi_f I + 33)) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99e44) fc None m (seg_rom bsegs)).
  Proof using SC AF CTX FDO MST OK RC2 LPOS HATK HTAILS.
    intros until cS. intros OB FRM LS SZK NODE LOC SRET SZS CHILD SV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2. pose proof (sc_slr _ _ _ _ _ _ _ _ _ _ _ _ SC) as SLR.
    destruct (str_az m js4 ART0 SH) as [ACC _].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof LS as (SZ0 & SZC & _ & _ & _ & (bs & BS & LBS & NUL) & _).
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_v1B E OK _ q b out node f D cap sz sl lg); [exact MI| ul| exact R2| exact R3| exact QHI| clear - SLR L0R; lia| clear - QN NB HT HL R1 LOW; ul| exact FLO| exact FHI| exact LS| unfold obj_loc72; exact LOC|].
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat sz) (proj1 BS)) as KEYL.
    eapply (HATK Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc D sz sl (firstn (Z.to_nat sz) bs) cS);
      [exact OB0| exact FRM| exact EF2| exact EL2| exact ES2| exact NODE| exact SRET| exact SZS| exact KEYL| rewrite firstn_length_le by lia; lia| lia| exact D0| lia| | |].
    {
      intros m' ART' AG'. split; [| left; clear - DLO LKC SZK SZ0; lia]. intros SZP.
      assert (SH' : rw_cells bsegs m' (shad f) (obj_sh 0 0 0 js4)).
      { unfold obj_sh, pz. apply (rw_cells_agree_nw bsegs m m' _ _ SH). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG'. unfold PK. unfold oi_b. fold q dd b.
        split; [| clear - Ha SHI R1 R2 R3 DDR; lia]. right; right; right; right. exists f, 1%nat. split; [exact HinF| rewrite fs1s; clear - Ha; lia]. }
      destruct (str_az m' js4 ART' SH') as [ACC' _].
      split; [apply (acc_sub bsegs m' D cap); [exact ACC'| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ2 D cap); [exact CLD| lia| lia]]. }
    { intros a Ha. apply (lstr_cls_client RT Σ2 _ D cap a CLD). lia. }
    intros m1 rd ri code jt y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 F' OB1 MI1 AGK SRET1 CODE HERR.
    unfold oi_b in SRET1, AGK. fold q in SRET1, AGK. fold dd in SRET1, AGK. fold b in SRET1, AGK.
    pose proof OB1 as [(_ & ART1 & _) ST1].
    assert (AG1 : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (b + 72 <= x < b + 96)) m m1) by (intros a [Ha Hn]; exact (AGK a Ha Hn)).
    clear KEYL. xport_stack LOC AG1. xport_stack CHILD AG1. xport_stack SV AG1. xport_shadow SH AG1 HinF. xport_stack OUT AG1.
    assert (LS1 : lstrA m1 (f + 32) lg D cap sz).
    { apply (lstrA_agree m m1 _ _ _ _ _ LS). intros a Ha. apply AG1. split; [| clear - Ha DLO FHI R1 R2 R3 DDR; lia].
      destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w94B _ q b); [exact R2| exact R3| ul| ul|].
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m1 b ES2 ST1 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK1.
    pose proof (rw_cells_bytes_at bsegs m1 _ _ SRET1) as SB. cbn [cells_bytes cbytes] in SB.
    rewrite (app_assoc (le8 (Z_to_bv 64 rd)) (le8 (Z_to_bv 64 ri))) in SB. apply bytes_at_app in SB. destruct SB as [SB16 _].
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m1 (b + 96) (b + 72) (le8 (Z_to_bv 64 rd) ++ le8 (Z_to_bv 64 ri)) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| ul| cbn; lia| exact SB16| | | cbn; lia| exact ART1| exact MI1| exact COK1|].
    { apply (checked_src_stack RT AF Σ2 m1 _ (ae_lo E) (b + 72) _ ART1); [rewrite ES2; ul| cbn; ul| rewrite EU; cbn; lia]. }
    { apply (checked_dst_stack RT AF Σ2 m1 _ (b + 96) _ ART1); [rewrite ES2; ul| cbn; ul| rewrite EU; cbn; lia| cbn; exact (wr_at_sub m1 (b + 96) 24 (b + 96) 16 (proj2 CHILD) ltac:(lia) ltac:(lia) ltac:(lia))]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. cbn [length app le8 Nat.add] in PR2. rewrite (ret_pc_even 0x99ee4) by lia.
    assert (NCL2 : forall a, b + 96 <= a < b + 96 + 16 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24).
    { intros a Ha Hc. exfalso. destruct (obj_split RT AF E d Σ Σ1 I CTX Σ2 m1 a ART1 EF2 EL2 ES2 Hc); clear - H Ha R1 R2 R3 DDR; unfold oi_b in *; lia. }
    pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ2 b (b + 96) 16 m1 m2 (proj1 OB1) EF2 EL2 ES2 ART2 MI2 ltac:(unfold oi_b; lia) PR2 NCL2 ltac:(left; unfold oi_b; clear - R2 R3; lia) ltac:(right; left; clear - FHI R1 R2 R3 DDR; lia)) as OBK2.
    pose proof (obase_of_K RT E Σ I Σ2 m2 OBK2 ST2) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (b + 96 <= x < b + 96 + 16)) PR2 (fun x H => H)) as AG2.
    pose proof (rec_copy16 m1 m2 (b + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] (C4 (Z_to_bv 64 12)) j2 (le8 (Z_to_bv 64 rd) ++ le8 (Z_to_bv 64 ri)) _ _ _ CHILD eq_refl eq_refl BY2 eq_refl WM2 PR2 ltac:(lia) ltac:(ul)) as CHILD2.
    clear CHILD. xport_stack LOC AG2. xport_stack SRET1 AG2. xport_stack SV AG2. xport_shadow SH AG2 HinF. xport_stack OUT AG2.
    assert (LS2 : lstrA m2 (f + 32) lg D cap sz).
    { apply (lstrA_agree m1 m2 _ _ _ _ _ LS1). intros a Ha. apply AG2. split; [| clear - Ha DLO FHI R1 R2 R3 DDR; lia].
      destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }
    eapply (esc_recB RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX LPOS lg D cap Lk sl L0 rest Σ2 SC HTAILS m2);
      [exact OB2| exact FRM| exact LS2| exact CODE| exact HERR| unfold obj_loc72; exact LOC| exact SRET1| exact CHILD2| exact SV| unfold obj_sh, pz; exact SH| exact OUT].
  Qed.

  Lemma esc_unesc : forall (n : nat) (m : mem) (sz esc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (js4 jo j0 j2 : list byte) (cS : list cell),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> sz <= Lk -> 0 <= esc < sz -> sz - esc <= Z.of_nat n ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 (oi_node I)) (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat ->
    rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz LIT_SLASH_A) (wz (shad (oi_f I))) (wz LIT_TILDE_A) (wz 49) (wz (oi_f I + 32)) (wz esc) (wz (oi_f I + 33)) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99db8) fc None m (seg_rom bsegs)).
  Proof using SC AF CTX FDO MST OK RC2 LPOS HATK HTAILS HFIN.
    induction n as [|n IH]; intros until cS; intros OB FRM LS SZK ESC FUEL NODE LOC SRET SZS CHILD SV SH OUT; [lia|].
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    pose proof (sh_apart RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHAP.
    pose proof (str_apart RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as STAP.
    destruct (str_az m js4 ART0 SH) as [ACC SHZ].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (FHI' : f + 120 < 2^47) by ul.
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u1B E OK _ q b f D cap sz esc (Lk + 1) lg); [exact MI| exact FLO| exact FHI'| exact LS| exact ESC| exact SHZ| lia| |].
    {
      intros cc xa2 N48 N49.
      eapply (esc_badB RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX LPOS lg D cap Lk sl L0 rest Σ2 SC HFIN m);
        [exact OB0| exact FRM| exact LS| unfold obj_loc72; exact LOC| exact SRET| exact SZS| exact CHILD| reflexivity| exact SV| reflexivity| unfold obj_sh, pz; exact SH| exact OUT]. }

    intros lit LIT E2.
    assert (LIT' : lit = 0x23120 \/ lit = 0x23140) by (unfold LIT_SLASH_A, LIT_TILDE_A in LIT; exact LIT).
    eapply (aevt_str_replace RT AF RC RC2 PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (f + 32) lg D cap sz esc lit (ae_lo E));
      [exact LS| exact CLD| exact CLS| exact ACC| replace (f + 32 + 24) with (f + 56) by lia; exact SEP| lia| exact E2| exact LIT'| exact ART0| exact MI| exact ST| rewrite ES2; exact LWIN| ul| ul| clear - B32; Z.div_mod_to_equations; lia|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 LS2 ACC2 ART2 MI2 ST2 WM2 AG2. rewrite (ret_pc_even 0x99e1c) by lia.
    assert (DAP : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m a ART0 Hc)) Hd)).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m2 a = m a).
    { intros a Ha N1 N2. apply AG2; [| clear - N1; lia| exact N2]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL2| auto| lia]. }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC Σ2 Σ2 m m2 OB0 EF2 EL2 ES2 ART2 MI2 ST2 AGB DAP) as OB2.
    assert (AGS : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ (~ (f + 24 <= x < f + 120) /\ ~ (D <= x < D + cap))) m m2).
    { intros a (Ha & N1 & N2). apply AG2; [exact Ha| clear - N1; lia| exact N2]. }
    assert (SH2 : rw_cells bsegs m2 (shad f) [pz (-15); pz (-15); pz (-15); pz (-15); pz 0; pz 0; pz 0; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); CB 4 js4]).
    { unfold pz. apply (rw_cells_agree_nw bsegs m m2 _ _ SH). intros a Ha. cbn [cells_size csize Nat.add length] in Ha.
      destruct (SHAP (bv_unsigned a) ltac:(clear - Ha; lia)) as [N1 N2].
      apply AG2; [right; right; right; right; exists f, 1%nat; split; [exact HinF| rewrite fs1s; clear - Ha; lia]| clear - N1; lia| exact N2]. }
    clear SH. unfold pz in SH2. xport_stack NODE AGS. xport_stack LOC AGS. xport_stack SRET AGS sz SZS. xport_stack CHILD AGS. xport_stack SV AGS. xport_stack OUT AGS.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u2B _ q b f esc); [lia| lia| exact FLO| exact FHI'|].
    eapply (aevt_str_find RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m2 b (f + 32) lg D cap (sz - 1) (esc + 1) (ae_lo E));
      [exact LS2| exact CLD| exact CLS| exact ACC2| lia| exact ART2| exact MI2| exact ST2| rewrite ES2; exact LWIN| ul| ul| clear - B32; Z.div_mod_to_equations; lia|].
    intros r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m3 HR LS3 ACC3 ART3 MI3 ST3 WM3 PR3. rewrite (ret_pc_even 0x99e2c) by lia.
    pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ2 b 0 0 m2 m3 (proj1 OB2) EF2 EL2 ES2 ART3 MI3 ltac:(unfold oi_b; lia) PR3 ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBK3.
    pose proof (obase_of_K RT E Σ I Σ2 m3 OBK3 ST3) as OB3.
    pose proof (agree_of_pres_ex _ _ _ _ _ m2 m3 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (0 <= x < 0 + 0)) PR3 (fun x H => H)) as AG3.
    xport_stack NODE AG3. xport_stack LOC AG3. xport_stack SRET AG3 sz SZS. xport_stack CHILD AG3. xport_stack SV AG3. xport_shadow SH2 AG3 HinF. xport_stack OUT AG3.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u3B _ q b f esc r); [clear - HR ESC SZK LKR L0R; lia| exact FLO| exact FHI'| |].
    -
      intros NR. assert (RR : esc + 1 <= r < sz - 1) by (clear - HR NR; lia).
      eapply (IH m3 (sz - 1) r); [exact OB3| exact FRM| exact LS3| lia| lia| lia| exact NODE| unfold obj_loc72; exact LOC| exact SRET| exact SZS| exact CHILD| exact SV| exact SH2| exact OUT].
    -
      intros ->.
      eapply (esc_afterB m3); [exact OB3| exact FRM| exact LS3| lia| exact NODE| unfold obj_loc72; exact LOC| exact SRET| exact SZS| exact CHILD| exact SV| exact SH2| exact OUT].
  Qed.

  Definition shdrX (m : mem) (sz : Z) : Prop :=
    if lg then rw_cells bsegs m (oi_f I + 32) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 D)] /\ cap mod 2 = 0
    else rw_cells bsegs m (oi_f I + 32) [C1 (Z_to_bv 8 (2 * sz))] /\ D = oi_f I + 32 + 1 /\ cap = 23.
  Lemma shdrX_xfer : forall (mA mB : mem) sz, shdrX mA sz -> (forall a : word, oi_f I + 32 <= bv_unsigned a < (if lg then oi_f I + 56 else oi_f I + 33) -> mB a = mA a) -> shdrX mB sz.
  Proof.
    intros mA mB sz H AG. unfold shdrX in *. destruct lg.
    - destruct H as [H EV]. split; [| exact EV]. apply (rw_cells_agree_nw bsegs mA mB _ _ H). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG. lia.
    - destruct H as (H & ED & EC). split; [| split; assumption]. apply (rw_cells_agree_nw bsegs mA mB _ _ H). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG. lia.
  Qed.

  Lemma esc_common : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) (w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (ix : nat) (js4 jo j0 j2 jD : list byte) (cS : list cell),
    obase RT E Σ I Σ2 m -> frm0 fc ->
    find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix -> shdrX m Lk ->
    rw_cells bsegs m D [CB (Z.to_nat cap) jD] ->
    rw_cells bsegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat ->
    rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) x21 (wz (oi_f I + 32)) (wz (Z.of_nat ix)) (wz Lk) (wz (oi_P I + 1)) (wz D) (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99d64) fc None m (seg_rom bsegs)).
  Proof using SC AF CTX FDO MST OK RC2 LPOS HATK HTAILS HFIN.
    intros until cS. intros OB FRM FB HDRS DATA NODE LOC SRET SZS CHILD SV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    pose proof (sc_eptr _ _ _ _ _ _ _ _ _ _ _ _ SC) as EPTR. pose proof (sc_zl0 _ _ _ _ _ _ _ _ _ _ _ _ SC) as ZL0. pose proof (sc_slr _ _ _ _ _ _ _ _ _ _ _ _ SC) as SLR.
    pose proof (sh_apart RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHAP. pose proof (sh_apartI RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHDI.
    pose proof (str_apart RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as STAP.
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia). fold f in SHDI.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (FHI' : f + 120 < 2^47) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.
    pose proof (lvl_live_ptr RT E Σ2 P ptr LV2 PAT ltac:(rewrite EPTR; discriminate)) as INPB.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3). rewrite EPTR, zlength_cons, ZL0 in PB2.
    pose proof (find_byte_Some _ _ _ FB) as (IXL & _). rewrite length_map, firstn_length_le in IXL by (unfold zlength in ZL0; lia).
    pose proof (proj2 DATA) as WRD. cbn [cells_size csize Nat.add] in WRD. rewrite Nat.add_0_r, Z2Nat.id in WRD by lia.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m b ES2 ST ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK.
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.

    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & _).
    rewrite EPTR in PTRB. pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
    change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
    set (kb := firstn (Z.to_nat Lk) rest) in *.
    assert (LKB : length (map (Z_to_bv 8) kb) = Z.to_nat Lk) by (subst kb; rewrite length_map, firstn_length_le; [reflexivity| unfold zlength in ZL0; lia]).

    apply (rw_cells_split_CB bsegs _ _ [] (Z.to_nat cap) jD [] [Z.to_nat Lk; 1; Z.to_nat (cap - Lk - 1)]%nat) in DATA; [| cbn; lia]. cbn [mk_CB_cells app] in DATA.
    lazymatch type of DATA with rw_cells _ _ _ [CB _ ?xa; CB 1 ?xb; CB _ ?xc] => set (jK := xa) in DATA; set (jn := xb) in DATA; set (jr := xc) in DATA end. clearbody jK jn jr.
    apply (proj1 (rw_cells_app bsegs m _ [_] _)) in DATA. destruct DATA as [DK DATA]. cbn [cells_size csize Nat.add] in DATA.
    rewrite Nat.add_0_r in DATA. replace (D + Z.of_nat (Z.to_nat Lk)) with (D + Lk) in DATA by lia.
    apply (proj1 (rw_cells_app bsegs m _ [_] _)) in DATA. destruct DATA as [DN D2]. cbn [cells_size csize Nat.add] in D2.
    replace (D + Lk + Z.of_nat 1) with (D + Lk + 1) in D2 by lia.
    destruct (str_az m js4 ART0 ltac:(unfold obj_sh, pz; exact SH)) as [ACC0 _].

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p6bB E OK _ q b node f (P + 1) Lk sl (Z.of_nat ix) D); [exact FLO| exact FHI|].
    eapply (aevt_memmoveP RT RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m D (P + 1) (map (Z_to_bv 8) kb) (ae_lo E));
      [reflexivity| reflexivity| rewrite LKB, Z2Nat.id by lia; reflexivity| ul| ul| rewrite LKB; lia| exact KEYL| | | exact ART0| exact MI| exact COK|].
    { rewrite LKB, Z2Nat.id by lia. apply (checked_src_live RT AF Σ2 m _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART0 INPB); [lia| lia| rewrite ES2; exact LWIN]. }
    { rewrite LKB, Z2Nat.id by lia. split; [| split; [intros i0 Hi0; rewrite EU; apply (lstr_cls_client RT Σ2 b D cap (D + i0) CLD); lia| exact (wr_at_sub m D cap D Lk WRD ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros _. split; [apply (acc_sub bsegs m D cap); [exact ACC0| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ2 D cap); [exact CLD| lia| lia]]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. rewrite LKB, Z2Nat.id in PR2 by lia. rewrite (ret_pc_even 0x99d74) by lia.
    assert (DAP0 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m a ART0 Hc)) Hd)).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m2 a = m a).
    { intros a Ha N1 N2. apply PR2; [| clear - N2 LKC LKR; lia]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL2| auto| lia]. }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC Σ2 Σ2 m m2 OB0 EF2 EL2 ES2 ART2 MI2 ST2 AGB DAP0) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (D <= x < D + Lk)) PR2 (fun x H => H)) as AGD.
    clear KEYB KEYL PTRB. xport_stack NODE AGD. xport_stack LOC AGD. xport_stack SRET AGD sz SZS. xport_stack CHILD AGD. xport_stack SV AGD. xport_stack OUT AGD.
    assert (SH2 : rw_cells bsegs m2 (shad f) [pz (-15); pz (-15); pz (-15); pz (-15); pz 0; pz 0; pz 0; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); CB 4 js4]).
    { unfold pz. apply (rw_cells_agree_nw bsegs m m2 _ _ SH). intros a Ha. cbn [cells_size csize Nat.add length] in Ha.
      destruct (SHAP (bv_unsigned a) ltac:(clear - Ha; lia)) as [N1 N2].
      apply AGD. split; [right; right; right; right; exists f, 1%nat; split; [exact HinF| rewrite fs1s; clear - Ha; lia]| clear - N2 LKC; lia]. }
    clear SH.
    assert (HDRS2 : shdrX m2 Lk).
    { apply (shdrX_xfer m m2 Lk HDRS). intros a Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b _ _ _ CLS); destruct lg; cbn in Ha; fold f in Ha; clear - Ha; lia|].
      pose proof HDRS as HX. unfold shdrX in HX. destruct lg; cbn in Ha, HX; fold f in Ha, HX; [destruct SEP as [X|X]; [discriminate X| clear - Ha X LKR LKC; lia]| destruct HX as (_ & ED & _); clear - Ha ED LKR; lia]. }
    assert (DN2 : rw_cells bsegs m2 (D + Lk) [CB 1 jn]).
    { apply (rw_cells_agree_nw bsegs m m2 _ _ DN). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b D cap _ CLD); lia| lia]. }
    assert (D22 : rw_cells bsegs m2 (D + Lk + 1) [CB (Z.to_nat (cap - Lk - 1)) jr]).
    { apply (rw_cells_agree_nw bsegs m m2 _ _ D2). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b D cap _ CLD); lia| lia]. }
    clear DN D2 DK HDRS.

    assert (FPW : fp_ok RT Σ2 (ae_lo E) [(b + 24, b + 40); (D + Lk, D + Lk + 1)]).
    { constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor]. cbn [fst snd].
      destruct CLD as [(f' & k' & Hin' & Q1 & Q2)|(p' & k' & Hin' & Q1 & Q2)].
      - right; right; left. exists f', k'. split; [exact Hin'| clear - Q1 Q2 LKC LKR; lia].
      - right; left. exists p', k'. split; [exact Hin'| clear - Q1 Q2 LKC LKR; lia]. }
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p7B E OK _ q b out node f (P + 1) Lk sl (Z.of_nat ix) D D (Lk + 1));
      [exact MI2| ul| exact R2| exact R3| exact QHI| clear - SLR L0R; lia| clear - QN NB HT HL R1 LOW; ul| exact D0| lia| lia| exact FLO| exact FHI'| | lia| unfold obj_loc72; exact LOC| exact DN2|].
    { intros m' MU' WM'. pose proof (art_of_munch RT AF Σ2 m2 m' (ae_lo E) _ ART2 ltac:(rewrite ES2; exact LWIN) FPW MU' WM') as ART'.
      pose proof (rw_cells_transport bsegs _ m2 m' _ _ SH2 MU' WM' ltac:(cbn [disjoint_from cells_size csize Nat.add length pz fst snd]; clear - SHDI LKC LKR SHI R1 R2 R3 DDR; lia)) as SH'.
      exact (proj2 (str_az m' js4 ART' ltac:(unfold obj_sh; exact SH'))). }
    intros m3 MU3 WM3 MI3 LOC3 NUL3.
    pose proof (art_of_munch RT AF Σ2 m2 m3 (ae_lo E) _ ART2 ltac:(rewrite ES2; exact LWIN) FPW MU3 WM3) as ART3.
    assert (ST3 : stk bsegs m3 (ae_lo E) b).
    { apply (stk_transport_disjoint _ _ m2 m3 (ae_lo E) b ST2 MU3 WM3). cbn [disjoint_from fst snd]. clear - DLO LKC LKR R1 R2 R3 DDR; lia. }
    assert (DAP2 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m2 a ART2 Hc)) Hd)).
    assert (HAPD : forall a, f <= a < f + 24 -> ~ (D + Lk <= a < D + Lk + 1)).
    { intros a Ha. destruct lg; [destruct (sc_long _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (_ & _ & _ & _ & _ & _ & _ & DSEP & _); fold f in DSEP; clear - Ha DSEP LKC LKR; lia
        | destruct (sc_short _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (ED & _); fold f in ED; clear - Ha ED LKR; lia]. }
    assert (OB3 : obase RT E Σ I Σ2 m3).
    { destruct OB2 as [(_ & _ & AI2 & SAVED2 & HIGH2 & HDR2 & PRES2) _].
      assert (AGC : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m2 m3).
      { intros a [Ha _]. pose proof (obj_split RT AF E d Σ Σ1 I CTX Σ2 m2 (bv_unsigned a) ART2 EF2 EL2 ES2 Ha) as SPL.
        apply MU3. cbn [outside]. split; [clear - SPL R1 R2 R3 DDR; lia|]. split; [| exact Logic.I]. intros Hin. apply (DAP2 (bv_unsigned a)); [clear - Hin LKC LKR; lia| exact Ha]. }
      split; [| exact ST3]. split; [exact MI3|]. split; [exact ART3|].
      split. { apply (AINV_A_agree E m2 m3 AI2). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
               pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AGC. split; [exact CX| clear - H QO R1; lia]. }
      split. { exact (rw_cells_transport bsegs _ m2 m3 _ _ SAVED2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_saved fst snd]; clear - DLO LKC LKR R1 R2 R3 DDR; lia)). }
      split. { exact (rw_cells_transport bsegs _ m2 m3 _ _ HIGH2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold oi_b; rewrite Nat.add_0_r, Z2Nat.id by (clear - DDR; lia); clear - DLO LKC LKR R1 R2 R3 DDR; lia)). }
      split. { apply (rw_cells_agree_nw bsegs m2 m3 _ _ HDR2). intros a Ha. cbn [cells_size csize Nat.add length obj_hdrB] in Ha. apply MU3. cbn [outside].
               split; [clear - Ha FHI R1 R2 R3 DDR; lia|]. split; [exact (HAPD (bv_unsigned a) ltac:(clear - Ha; lia))| exact Logic.I]. }
      eapply rt_pres_fp_trans; [exact PRES2|]. intros a Ha Ho. apply AGC. cbn [outside] in Ho. split; [exact Ha| clear - Ho; lia]. }
    unfold obj_loc72 in LOC3. clear LOC.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ NODE MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QN DLO LKC LKR R1 R2 R3 DDR; lia)) as NODE3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SRET MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZS; clear - DLO LKC LKR R1 R2 R3 DDR; lia)) as SRET3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ CHILD MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - DLO LKC LKR R1 R2 R3 DDR; lia)) as CHILD3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SV MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - DLO LKC LKR R1 R2 R3 DDR; lia)) as SV3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ OUT MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QO DLO LKC LKR R1 R2 R3 DDR; lia)) as OUT3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SH2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length pz fst snd]; clear - SHDI LKC LKR SHI R1 R2 R3 DDR; lia)) as SH3.
    assert (HDRS3 : shdrX m3 Lk).
    { apply (shdrX_xfer m2 m3 Lk HDRS2). intros a Ha. apply MU3. cbn [outside]. split; [destruct lg; cbn in Ha; fold f in Ha; clear - Ha FHI R1 R2 R3 DDR; lia|]. split; [| exact Logic.I].
      pose proof HDRS2 as HX. unfold shdrX in HX. destruct lg; cbn in Ha, HX; fold f in Ha, HX; [destruct SEP as [X|X]; [discriminate X| clear - Ha X LKR LKC; lia]| destruct HX as (_ & ED & _); clear - Ha ED LKR; lia]. }
    assert (BY3 : bytes_at bsegs m3 D (map (Z_to_bv 8) kb)).
    { apply (bytes_at_agree bsegs m2 m3 _ _ BY2). intros a Ha. rewrite LKB in Ha. apply MU3. cbn [outside]. split; [clear - Ha DLO R1 R2 R3 DDR LKC; lia|]. split; [lia| exact Logic.I]. }
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ D22 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - DLO LKC LKR R1 R2 R3 DDR; lia)) as D23.

    assert (LS3 : lstrA m3 (f + 32) lg D cap Lk).
    { split; [lia|]. split; [exact LKC|]. split; [lia|]. split; [exact D0|]. split; [ul|]. split; [| exact HDRS3].
      exists (map (Z_to_bv 8) kb ++ [Z_to_bv 8 0] ++ jr). split; [split|].
      - apply (proj2 (bytes_at_app bsegs m3 D _ _)). split; [exact BY3|]. rewrite LKB, Z2Nat.id by lia.
        apply (proj2 (bytes_at_app bsegs m3 (D + Lk) _ _)). split.
        + pose proof (rw_cells_bytes_at bsegs m3 _ _ NUL3) as X. cbn [cells_bytes cbytes app le1] in X. rewrite ?app_nil_r in X. exact X.
        + cbn [length Z.of_nat Pos.of_succ_nat]. pose proof (rw_cells_bytes_at bsegs m3 _ _ D23) as X. cbn [cells_bytes cbytes app] in X. rewrite ?app_nil_r in X. exact X.
      - rewrite !length_app, LKB. cbn [length]. pose proof (proj1 (proj1 D23)) as WF. cbn [cells_wf cell_wf] in WF.
        replace (Z.of_nat (Z.to_nat Lk + (1 + length jr))) with cap by (destruct WF; lia).
        exact (wr_at_transport bsegs m m3 _ _ WRD (wmono_trans _ _ _ _ WM2 WM3)).
      - split.
        + rewrite !length_app, LKB. cbn [length]. pose proof (proj1 (proj1 D23)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF; lia.
        + rewrite app_nth2 by (rewrite LKB; lia). rewrite LKB, Nat.sub_diag. reflexivity. }
    eapply (esc_unesc (S (Z.to_nat Lk)) m3 Lk (Z.of_nat ix)); [exact OB3| exact FRM| exact LS3| lia| lia| lia| exact NODE3| unfold obj_loc72; exact LOC3| exact SRET3| exact SZS| exact CHILD3| exact SV3| unfold obj_sh; exact SH3| exact OUT3].
  Qed.
  End SCtx.
End ObjES.
