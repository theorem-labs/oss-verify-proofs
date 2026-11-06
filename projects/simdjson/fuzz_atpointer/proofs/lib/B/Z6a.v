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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Zq3 Zqc Zqd Zqb I_lkit
     Z45 Z5k Z3v Z5q Z5v Z6b Z60 Z6e Z6h Z63 Z65 Z62 Z64 Z5o Z5w Z61
     Z6k Z5p.
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

Lemma zeros16_le8 : repeat (Z_to_bv 8 0) 16 = le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).
Proof. reflexivity. Qed.

Section ObjNW.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_wcc : forall (K : machine_state -> Prop) (q b : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    272 <= q -> q + -272 <= b -> b <= q + -256 -> q < 2^47 ->
    K (MS (mkR (wz 0x99d1c) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 96)) (wz (b + 72)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x99d0c) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros QL B0 B1 QH HK. unfold e_asan_memcpy in *.

    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_wdc : forall (K : machine_state -> Prop) (q b code : Z) (r0 r1 cw : word)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (rb jt jc : list byte),
    mem_inv bsegs m -> ae_lo E + 272 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= code < 64 ->
    rw_cells bsegs m (b + 72) [C8 r0; C8 r1; C4 (Z_to_bv 64 code); CB 4 jt] ->
    rw_cells bsegs m (b + 96) [CB 16 rb; C4 cw; CB 4 jc] ->
    (forall (m1 : mem), munch [(b + 112, b + 116)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (b + 96) [CB 16 rb; C4 (Z_to_bv 64 code); CB 4 jc] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz code) (wz 64) x12 x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0x99f40) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x99d1c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jc. intros MI LO B0 B1 QH CODE REC CHILD HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(b + 112, b + 116)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. rewrite ?a_sx32_small by lia. astep.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small, ?unsigned_lit in K0 by lia; clear - K0 CODE; lia| clear K0].
    step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| ]].
    - atp_st_eq_goal.
    - lazymatch goal with H : rw_cells bsegs m1 (b + 96) _ |- _ => exact H end.
  Qed.
End ObjNW.

Section ObjN.
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

  Lemma obj_retk : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 r0 cw : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 code sl Lk L0 vj : Z) (rest : list Z) (js4 jo j0 od jn j2 : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> (sl = 18446744073709551615 \/ 0 <= sl < L0) -> 0 <= code < 64 ->
    (code = 0 -> r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= vj /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ j' <= ae_n E - 1) ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) [C8 r0; C8 (Z_to_bv 64 vj); C4 (Z_to_bv 64 code); CB 4 od] ->
    rw_cells bsegs m (oi_b I + 96) [CB 16 jn; C4 cw; CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz sl) (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99d0c) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until j2. intros OB FRM EPTR ZL0 SLR HC HERR LOC R72 REC KV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    pose proof (fun a => obj_split RT AF E d Σ Σ1 I CTX Σ1 m a ART0 EF1 ltac:(rewrite EL1; auto) ES1) as SPLIT.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & _ & _ & _ & PL).
    rewrite EPTR in PL. rewrite zlength_cons in PL. pose proof (zlength_nonneg rest) as ZLN.
    assert (ZL : zlength ptr = L0 + 1) by (rewrite EPTR, zlength_cons; lia).

    apply (aevt_evt RT AF PMc MST).
    apply (obj_wcc _ q b); [ul| flia| flia| ul|].
    pose proof R72 as CO16. apply (proj1 (rw_cells_app bsegs m _ [_; _] _)) in CO16. destruct CO16 as [CO16 _].
    pose proof (rw_cells_bytes_at bsegs m _ _ CO16) as RB. set (rb := cells_bytes _) in RB.
    assert (LRB : length rb = 16%nat) by (subst rb; exact (cells_bytes_length _ (proj1 (proj1 CO16)))).
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m b ES1 ST ltac:(olia) B16) as COK.
    apply (proj1 (rw_cells_app bsegs m _ [_] _)) in REC. destruct REC as [RECN RECE]. cbn [cells_size csize Nat.add] in RECE.
    replace (b + 96 + Z.of_nat 16) with (b + 112) in RECE by flia.
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (b + 96) (b + 72) rb (ae_lo E));
      [reflexivity| reflexivity| rewrite LRB; reflexivity| ul| ul| rewrite LRB; cbn; flia| exact RB| | | rewrite LRB; cbn; flia| exact ART0| exact MI| exact COK|].
    { rewrite LRB. apply (checked_src_stack RT AF Σ1 m _ (ae_lo E) (b + 72) 16 ART0); [rewrite ES1; ul| ul| rewrite EU; flia]. }
    { rewrite LRB. apply (checked_dst_stack RT AF Σ1 m _ (b + 96) 16 ART0); [rewrite ES1; ul| ul| rewrite EU; flia| exact (proj2 RECN)]. }
    intros t0' t1' t2' b1' b2' b3' b4' b5' b6' b7' t3' t4' t5' t6' F2 m3 (ART3 & MI3 & WM3 & ST3) PR3 BY3.
    rewrite EU in ST3, PR3. rewrite LRB in PR3. change (Z.of_nat 16) with 16 in PR3.
    rewrite (ret_pc_even 0x99d1c) by flia.
    pose proof (agree_of_pres_ex _ _ _ _ _ m m3 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (b + 96 <= x < b + 96 + 16)) PR3 (fun x H => H)) as AG3.
    clear RB CO16. pose proof (proj2 RECN) as WREC. clear RECN. cbn [cells_size csize Nat.add] in WREC.
    xport_stack LOC AG3. xport_stack R72 AG3. xport_stack RECE AG3. xport_stack KV AG3. xport_shadow SH AG3 HinF. xport_stack OUT AG3.
    assert (REC3 : rw_cells bsegs m3 (b + 96) [CB 16 rb; C4 cw; CB 4 j2]).
    { change [CB 16 rb; C4 cw; CB 4 j2] with ([CB 16 rb] ++ [C4 cw; CB 4 j2]).
      apply (proj2 (rw_cells_app bsegs m3 _ [CB 16 rb] _)). split.
      - rewrite <- LRB. apply rw_cells_CB_intro; [exact BY3|]. rewrite LRB. exact (wr_at_transport bsegs m m3 _ _ WREC WM3).
      - cbn [cells_size csize Nat.add]. replace (b + 96 + Z.of_nat 16) with (b + 112) by flia. exact RECE. }
    assert (OBK3 : obaseK RT E Σ I Σ1 m3).
    { apply (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ1 b (b + 96) 16 m m3);
        [exact (proj1 OB0)| exact EF1| rewrite EL1; auto| exact ES1| exact ART3| exact MI3| olia| exact PR3
        | intros a Ha Hc; exfalso; destruct (SPLIT a Hc); olia| left; olia| right; left; olia]. }
    clear AG3 PR3 BY3 RECE WREC WM3 MI ST ART0 COK.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_wdc E OK _ q b code r0 (Z_to_bv 64 vj) cw); [exact MI3| ul| flia| flia| exact QHI| exact HC| exact R72| exact REC3|].
    intros m4 MU4 WM4 MI4 REC4.
    assert (OW4 : Forall (ownW I) [(b + 112, b + 116)]) by (constructor; [left; cbn [fst snd]; olia| constructor]).
    pose proof (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m3 m4 OBK3 EF1 ltac:(rewrite EL1; auto) ES1 MU4 WM4 MI4 OW4) as OBK4.
    pose proof (stk_transport_disjoint bsegs _ m3 m4 (ae_lo E) b ST3 MU4 WM4 ltac:(cbn; flia)) as ST4.
    clear REC3. mport LOC MU4 WM4. mport R72 MU4 WM4. mport KV MU4 WM4. mport SH MU4 WM4. mport OUT MU4 WM4.

    replace rb with (le8 r0 ++ le8 (Z_to_bv 64 vj)) in REC4 by (subst rb; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity).
    apply rec_node16 in REC4.
    apply (proj1 (rw_cells_app bsegs m4 _ [_; _] _)) in KV. destruct KV as [KV1 KV2]. cbn [cells_size csize Nat.add] in KV2.
    replace (b + 120 + Z.of_nat 16) with (b + 136) in KV2 by flia.
    eapply (obj_tails RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX Σ1 m4);
      [exact (conj OBK4 ST4)| exact FRM| exact EF1| exact EL1| exact ES1| exact EPTR| exact ZL0| clear - SLR PL ZLN ZL0; lia| exact HC| exact HERR|
      | exact LOC| exact R72| reflexivity| exact REC4| exact KV1| reflexivity| exact KV2| exact SH| exact OUT].

    unfold oi_L. fold ptr. rewrite ZL, EC1. rewrite ZL in CRB.
    destruct (Z.eq_dec code 0) as [C0|CNZ].
    - destruct SLR as [X|X].
      + left. split; [right; exact X|]. unfold obj_costA, LVL_C1, DCOST in *. clear - CRB ZLN ZL0. lia.
      + right. split; [exact C0|]. split; [exact X|]. unfold elem_costA, obj_costA, LVL_C1, DCOST in *. clear - CRB ZLN ZL0 X. lia.
    - left. split; [left; exact CNZ|]. unfold obj_costA, LVL_C1, DCOST in *. clear - CRB ZLN ZL0. lia.
  Qed.

  Lemma obj_noesc : forall (m : mem) (x5 x6 x7 xa4 xa5 a6 a7 y7 y8 y9 y10 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
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
      (MS (mkR (wz 0x99d0c) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz (oi_b I + 72)) (wz (oi_node I)) (wz (oi_P I + 1)) (wz Lk) xa4 xa5 a6 a7
               (wz sl) (wz (shad (oi_f I))) (wz (oi_node I)) (wz L) (wz (oi_P I)) y7 y8 y9 y10 (wz 2147450880) x28 x29 x30 x31)
          F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until w32. intros OB FRM EPTR ZL0 SLK NODE LOC C72 REC KV SH OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    pose proof OB as OB0. destruct OB as ((MI & ART0 & AI & SAVED & HIGH & HDR & PRES) & ST).
    pose proof (fun a => obj_split RT AF E d Σ Σ1 I CTX Σ1 m a ART0 EF1 ltac:(rewrite EL1; auto) ES1) as SPLIT.
    pose proof (fun sp a => obj_mono RT Σ I Σ1 sp a EF1 ltac:(rewrite EL1; auto)) as MONO.

    apply (rw_cells_split_CB bsegs _ _ [] 24 jC [] [8; 8; 4; 4]%nat) in C72; [| reflexivity]. cbn [mk_CB_cells app] in C72.
    repeat match type of C72 with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "oj" in set (j := t) in C72; clearbody j end.
    lazymatch type of C72 with rw_cells _ _ _ [CB 8 ?xa; CB 8 ?xb; CB 4 ?xc; CB 4 ?xd] =>
      rename xd into od; pose proof C72 as OUT0 end.

    assert (REC' : exists jn, rw_cells bsegs m (oi_b I + 96) [CB 16 jn; C4 (Z_to_bv 64 12); CB 4 j2]).
    { apply (proj1 (rw_cells_app bsegs m _ [_; _] _)) in REC. destruct REC as [RA RB]. destruct (rw_cells_forget _ _ _ _ RA) as [jn RA'].
      exists jn. change [CB 16 jn; C4 (Z_to_bv 64 12); CB 4 j2] with ([CB 16 jn] ++ [C4 (Z_to_bv 64 12); CB 4 j2]).
      apply (proj2 (rw_cells_app bsegs m _ [CB 16 jn] _)). exact (conj RA' RB). }
    clear REC. destruct REC' as [jn REC].
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT ltac:(rewrite EPTR; discriminate)) as INPB.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & _ & _ & _ & PL).
    rewrite EPTR in PTRB, PB2. rewrite EPTR, zlength_cons in PL. rewrite zlength_cons in PB2. pose proof (zlength_nonneg rest) as ZLN.
    assert (SLR : sl = 18446744073709551615 \/ 0 <= sl < L0) by (clear - SLK; lia).
    assert (LK : 0 <= Lk <= L0) by (clear - SLK ZLN ZL0; lia).

    pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
    change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
    assert (LKB : Z.of_nat (length (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest))) = Lk) by (rewrite length_map, firstn_length_le; [clear - LK; lia| unfold zlength in ZL0; clear - LK ZL0; lia]).

    eapply (obj_atkeyB RT AF RC2 E OK d PMc FDO MST Σ1 _ m fc q b node i e c (P + 1) Lk 0x99d0c (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest))
              gp (wz q) (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) y7 y8 y9 y10 od);
      [exact LV1| exact TY| exact NXT| exact TILES| exact I0| exact EN| ul| flia| exact QN| exact NB| exact N8| exact B32| exact LKB| flia| flia| ul
      | intros m' HA _; apply (checked_src_live RT AF Σ1 m' _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) Lk HA INPB); [flia| flia| rewrite ES1; exact LWIN]
      | intros a Ha; right; right; left; exists (ae_PB E), (ae_NPB E); split; [exact INPB| flia]
      | flia| reflexivity| | | exact ART0| exact MI| exact ST| exact AI| exact NODE| exact OUT0| exact KEYL].
    -
      intros m' F' it j' y5 y6 z7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' STR ELV ITLO JE R72.
      clear KEYB KEYL PTRB OUT0 C72. unfold PK in AGK.
      xport_stack SAVED AGK. xport_stack HIGH AGK. xport_frame HDR AGK HinF. xport_stack LOC AGK. xport_stack REC AGK. xport_stack KV AGK. xport_shadow SH AGK HinF. xport_stack OUT AGK.
      assert (PRES' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m0 m').
      { eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AGK. split; [exact (MONO b _ ltac:(flia) Ha)|].
        destruct (SPLIT _ Ha); flia. }
      assert (HC0 : 0 <= 0 < 64) by (clear; lia).
      assert (HERR0 : 0 = 0 -> Z_to_bv 64 (ae_DOC E) = Z_to_bv 64 (ae_DOC E) /\ 0 <= it + 1 /\ exists j'', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j'' /\ j'' <= ae_n E - 1).
      { intros _. split; [reflexivity|]. split; [clear - ITLO I0; olia|]. exists j'. split; [exact ELV| clear - JE EN; olia]. }
      eapply (obj_retk m'); [| exact FRM| exact EPTR| exact ZL0| exact SLR| exact HC0| exact HERR0| exact LOC| exact R72| exact REC| exact KV| exact SH| exact OUT].
      exact (conj (conj MI' (conj ART' (conj AI' (conj SAVED (conj HIGH (conj HDR PRES')))))) ST').
    -
      intros m' F' y5 y6 z7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AGK NODE' R72.
      clear KEYB KEYL PTRB OUT0 C72. unfold PK in AGK.
      xport_stack SAVED AGK. xport_stack HIGH AGK. xport_frame HDR AGK HinF. xport_stack LOC AGK. xport_stack REC AGK. xport_stack KV AGK. xport_shadow SH AGK HinF. xport_stack OUT AGK.
      assert (PRES' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m0 m').
      { eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AGK. split; [exact (MONO b _ ltac:(flia) Ha)|].
        destruct (SPLIT _ Ha); flia. }
      rewrite zeros16_le8 in R72. apply rec_node16 in R72.
      assert (HC20 : 0 <= 20 < 64) by (clear; lia).
      assert (HERR20 : 20 = 0 -> Z_to_bv 64 0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= 0 /\ exists j'', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d 0 j'' /\ j'' <= ae_n E - 1)
        by (intros X; exfalso; clear - X; lia).
      eapply (obj_retk m'); [| exact FRM| exact EPTR| exact ZL0| exact SLR| exact HC20| exact HERR20| exact LOC| exact R72| exact REC| exact KV| exact SH| exact OUT].
      exact (conj (conj MI' (conj ART' (conj AI' (conj SAVED (conj HIGH (conj HDR PRES')))))) ST').
  Qed.
End ObjN.
