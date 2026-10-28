(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx Sj_num_akit Sj_acps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation mem := (word -> option byte).

Definition EL_CXA_ALLOC_XA : Z := 0x10654c.
Definition EL_ALSTUB_XA : Z := 0x82e84.
Definition XA_RET1 : Z := 0x106c8c.
Definition XA_RET2 : Z := 0x10656c.
Definition XA_RET3 : Z := 0x106584.

Lemma cxa_pro_walkA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 48 -> 64 <= usp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = entry_st (wz XA_RET1) (wz (usp + -48)) gp tp t0 t1 t2 (wz EXC_SIZE) s1 (wz 16) (wz EXC_SIZE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_aligned_alloc m1
      /\ munch [(usp - 48, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -48)
      /\ rw_cells asegs m1 (usp + -48) [C8 (wz EXC_SIZE); C8 (wz XA_RET2); CB 8 j; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz EL_CXA_ALLOC_XA) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UR MI.
  unfold entry_st, EL_CXA_ALLOC_XA, e_aligned_alloc, XA_RET1, XA_RET2, EXC_SIZE.
  pose proof (munch_refl [(usp - 48, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 48%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep.

  zstep. zstep. zstep. zstep.

  zstep. zstep. change (Z_to_le_bytes 8 1074540) with (le8 (Z_to_bv 64 1074540)). mem_after_store.
  zstep. change (Z_to_le_bytes 8 144) with (le8 (Z_to_bv 64 144)). mem_after_store.
  zstep. zstep. change (144 + Z.b2z (144 <? 1)) with 144.
  zstep. zstep. change (Z.land ((144 + 15) mod 18446744073709551616) 18446744073709551600) with 144.
  zstep. zstep. if_cases K; [exfalso; clear - K; vm_compute in K; discriminate| clear K].
  zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma cxa_mid_walkA : forall (usp lo p : Z) (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1o s0o rao : word) (j : list byte) F fc (m : mem),
  stk asegs m lo (usp + -48) -> lo <= usp - 48 -> 64 <= usp < 2^63 -> 0 < p < 2^64 ->
  rw_cells asegs m (usp + -48) [C8 (wz EXC_SIZE); C8 (wz XA_RET2); CB 8 j; C8 s1o; C8 s0o; C8 rao] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = entry_st (wz XA_RET3) (wz (usp + -32)) gp tp t0 t1 t2 (wz EXC_SIZE) (wz p) (wz p) (wz 0) (wz EXC_SIZE) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memset m
      /\ stk asegs m lo (usp + -32) /\ rw_cells asegs m (usp + -32) [CB 8 j; C8 s1o; C8 s0o; C8 rao])
    (MS (mkR (wz XA_RET1) (wz (usp + -48)) gp tp t0 t1 t2 (wz EXC_SIZE) s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz XA_RET1)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UR P FR MI.
  unfold entry_st, XA_RET1, XA_RET2, XA_RET3, EXC_SIZE, e_memset in *. rewrite (ret_pc_even 0x106c8c) by lia.
  destruct (proj1 (rw_cells_app asegs m _ [C8 (wz 144); C8 (wz 0x10656c)] [CB 8 j; C8 s1o; C8 s0o; C8 rao]) FR) as [FRi FRo].
  cbn [cells_size csize Nat.add] in FRo. replace (usp + -48 + Z.of_nat 16) with (usp + -32) in FRo by lia.

  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  zstep. zstep. zstep.
  pose proof (stk_release asegs m lo _ _ ST FRi ltac:(lia)) as ST2. cbn [cells_size csize Nat.add] in ST2. replace (usp + -48 + Z.of_nat 16) with (usp + -32) in ST2 by lia.
  clear ST FRi FR. zstep.

  zstep. zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
  zstep. zstep. zstep. zstep.
  apply evt_done. split; [cbv delta [mkR]; reflexivity|]. split; [exact ST2| exact FRo].
Qed.

Lemma cxa_epi_walkA : forall (usp lo p : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1o s0o : word) (j : list byte) F fc (m : mem) (RA : Z),
  stk asegs m lo (usp + -32) -> lo <= usp - 48 -> 64 <= usp < 2^63 -> 0 < p -> p + 144 < 2^63 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  rw_cells asegs m (usp + -32) [CB 8 j; C8 s1o; C8 s0o; C8 (wz RA)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (mkR (wz RA) (wz usp) gp tp t0 t1 t2 s0o s1o (wz (p + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA) fc None m (seg_rom asegs)
      /\ stk asegs m lo usp)
    (MS (mkR (wz XA_RET3) (wz (usp + -32)) gp tp t0 t1 t2 (wz EXC_SIZE) (wz p) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz XA_RET3)) fc None m (seg_rom asegs)).
Proof.
  intros until RA. intros ST LO UR P0 P1 RAR RAE FR MI.
  unfold XA_RET3, EXC_SIZE in *. rewrite (ret_pc_even 0x106584) by lia.

  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep. zstep.
  apply evt_done. rewrite (ret_pc_even RA) by lia. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Section CxaA.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis ALC : aligned_alloc_contract RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Lemma aevt_call2x : forall (Σ : rts RT) K ms (Q : config -> Prop),
    cps asegs (ASTA RT Σ PMc (eq ms)) Q ->
    (forall c, Q c -> exists (Σ' : rts RT) (Pm : machine_state -> Prop), ASTA RT Σ' PMc Pm c /\ forall ms', Pm ms' -> aevt RT PMc Σ' K ms') ->
    aevt RT PMc Σ K ms.
  Proof.
    intros Σ K ms Q H HQ T c Hc Hk. apply (H T c Hc). intros c' Hq.
    destruct (HQ c' Hq) as (Σ' & Pm & HA & HP). destruct (ASTA_unpack RT Σ' PMc Pm c' HA) as (ms' & HPm & Hc'). exact (HP ms' HPm T c' Hc' Hk).
  Qed.

  Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, EXC_SIZE in *; lia.

  Theorem aevt_cxa_allocA : forall (Σ : rts RT) K (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      F fc (m : mem) (usp lo RA : Z),
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost EXC_SIZE <= rt_credit RT Σ ->
    ART RT Σ m -> mem_inv asegs m ->
    stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 48 + RT_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
    (forall (Σ' : rts RT) (p : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
       ART RT Σ' m' -> mem_inv asegs m' -> wmono asegs m m' -> stk asegs m' lo usp ->
       rt_pres (rt_live RT Σ) (rt_frames RT Σ) usp m m' ->
       rw_cells asegs m' p [CB 128 (repeat z8 128); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
       rt_live RT Σ' = (p, EXC_SIZE) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
       rt_credit RT Σ' = rt_credit RT Σ - mcost EXC_SIZE -> 0 < p -> p mod 16 = 0 -> p + EXC_SIZE < USTACK_TOP ->
       aevt RT PMc Σ' K (MS (mkR (wz RA) (wz usp) gp (wz 0x6a7e68) t0' t1' t2' s0 s1 (wz (p + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F' (wz RA) fc None m' (seg_rom asegs))) ->
    aevt RT PMc Σ K (MS (mkR (wz RA) (wz usp) gp (wz 0x6a7e68) t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz EL_CXA_ALLOC_XA) fc None m (seg_rom asegs)).
  Proof using AF RC ALC FDO MST.
    intros until RA. intros RAR RAE LV CR ART0 MI0 ST0 LOR SPT SPA SP16 HK.
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.

    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [apply (cxa_pro_walkA usp lo (wz RA) gp (wz 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0); [ul| ul| exact MI0]|].
    cbv beta. intros ms (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (ART1 : ART RT Σ m1).
    { apply (art_client_write RT AF Σ m m1 (usp - 48) ART0 ltac:(ul)); [| exact WM1].
      intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
    assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; ul).
    assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).

    assert (COK : call_ok RT Σ m1 (wz (usp + -48)) lo).
    { unfold call_ok. rewrite EU48. split; [exact ST1|]. split; [exact LOR|]. split; [ul|]. split; [ul|].
      replace (usp + -48) with (usp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact SP16. }
    assert (UOK : unwind_ok (wz XA_RET1) (wz EXC_SIZE) (wz (usp + -48))).
    { left. rewrite EU48. unfold EXC_SIZE. rewrite unsigned_lit by lia. ul. }
    apply (aevt_call2x Σ K _ _ (ALC Σ PMc (wz XA_RET1) (wz (usp + -48)) gp (wz 0x6a7e68) t0 t1 t2 (wz EXC_SIZE) s1 (wz 16) (wz EXC_SIZE) a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST eq_refl eq_refl eq_refl LV CR ART1 MI1 COK UOK)).
    intros c2 (Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP). exists Σ1. eexists. split; [exact Hc2|].
    intros ms2 (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2).
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU48 in ST2, PRES2.
    assert (FR2 : rw_cells asegs m2 (usp + -48) [C8 (wz EXC_SIZE); C8 (wz XA_RET2); CB 8 j; C8 s1; C8 s0; C8 (wz RA)]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [apply (cxa_mid_walkA usp lo p gp (wz 0x6a7e68) u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s1 s0 (wz RA) j F2 fc m2 ST2);
                       [ul| ul| ul| exact FR2| exact MI2]|].
    cbv beta. intros ms (-> & ST2' & FR2').
    assert (INP : In (p, EXC_SIZE) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    assert (COK2 : call_ok RT Σ1 m2 (wz (usp + -32)) lo).
    { unfold call_ok. rewrite EU32, SP1. split; [exact ST2'|]. split; [exact LOR|]. split; [ul|]. split; [ul|].
      replace (usp + -32) with (usp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact SP16. }
    assert (CD : checked_dst RT Σ1 m2 (wz (usp + -32)) p EXC_SIZE).
    { split; [| split; [| exact WR2]].
      - intros _. split; [exact ACC2|]. left. exists p, EXC_SIZE. split; [exact INP| lia].
      - intros i Hi. right; right; left. exists p, EXC_SIZE. split; [exact INP| lia]. }
    apply (aevt_call2x Σ1 K _ _ (rc_memset RT RC Σ1 PMc (wz XA_RET3) (wz (usp + -32)) gp (wz 0x6a7e68) u0 u1 u2 (wz EXC_SIZE) (wz p) (wz p) (wz 0) (wz EXC_SIZE) b3 b4 b5 b6 b7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc m2 p EXC_SIZE z8 lo FDO MST eq_refl ltac:(reflexivity) eq_refl
                                     ltac:(ul) ltac:(ul) CD ART2 MI2 COK2)).
    intros c3 Hc3. exists Σ1. eexists. split; [exact Hc3|].
    intros ms3 (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & ZB3).
    destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & ->).
    rewrite EU32 in ST3, PRES3.
    assert (FR3 : rw_cells asegs m3 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 (wz RA)]).
    { apply (rw_cells_agree asegs m2 m3 _ _ FR2'); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (af_live_range RT AF Σ1 m2 p EXC_SIZE ART2 INP). split; [left; ul| ul]. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [apply (cxa_epi_walkA usp lo p gp (wz 0x6a7e68) v0 v1 v2 (wz p) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 s1 s0 j F3 fc m3 RA ST3);
                       [ul| ul| ul| ul| exact RAR| exact RAE| exact FR3| exact MI3]|].
    cbv beta. intros ms (-> & ST4).

    apply (HK Σ1 p v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 F3 m3 ART3 MI3 (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)) ST4); try assumption.
    -
      intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (NB : ~ (p <= bv_unsigned a < p + EXC_SIZE)).
      { intros Hb. destruct Ha as [S|[CS|[LVa|[FRa|FSa]]]].
        - pose proof (af_live_range RT AF Σ1 m2 p EXC_SIZE ART2 INP). ul.
        - pose proof (client_static_range _ CS). destruct (af_live_range RT AF Σ1 m2 p EXC_SIZE ART2 INP) as (_ & _ & [X|X]); ul.
        - destruct LVa as (q & n & HIn & Hq).
          pose proof (af_live_disj RT AF Σ1 m2 p EXC_SIZE q n [] (rt_live RT Σ) ART2 ltac:(rewrite LV1; reflexivity) HIn). lia.
        - destruct FRa as (f & k & HIn & Hf). rewrite <- FRS1 in HIn. destruct (af_frames_range RT AF Σ1 m2 f k ART2 HIn) as (_ & _ & _ & DJ). pose proof (DJ p EXC_SIZE INP). lia.
        - destruct FSa as (f & k & HIn & Hf). rewrite <- FRS1 in HIn. destruct (af_fshadow_apart RT AF Σ1 m2 f k ART2 HIn) as [DJ _]. pose proof (DJ p EXC_SIZE INP). lia. }
      rewrite (PRES3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      + cbn [outside]. split; [ul| exact I].
      + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      + rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; right; exact He| auto| lia].
      + exact NB.
    -
      split.
      + split; [cbn; repeat split; reflexivity|]. exact ZB3.
      + cbn [cells_size csize Nat.add length]. destruct WR2 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|].
        intros i Hi. apply WM3. exact (W3 i Hi).
  Qed.
End CxaA.
