(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits
  Sj_num_lm_pro Sj_num_lm_enter Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_a Sj_num_lm_b Sj_num_lm_tkit Sj_num_lm_top Sj_num_lm_top2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section LMTOP3.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g len0 : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := B_P5LARGE.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6cd000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6cd000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis L0 : (0 <= len0 <= 62)%Z.

  Hypothesis HK : big_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo 1 (lmb_G len0).
  Collection TOPH := AF RTF FDO MST ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP L0 HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d spq f).
  Notation TKA := (RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP) (only parsing).

  Notation T1 L := (L RT AF RTF PMc FDO MST Σ0 Σ1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g len0 kg me ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP L0 HK) (only parsing).
  Notation lm_ctx := (lm_ctx RT Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X d spq f me).

  Ltac top_env :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5;
    pose proof (proj1 XG) as HinG0; pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2;
    assert (HinG : In (g, kg) (rt_frames RT Σ1)) by (rewrite EF; right; exact HinG0);
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof L0 as L0'.

  Notation EVA L F fc ybs YL mb HA := (L sp gp tp F fc X lo d spq f len0 ybs mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP YL
                               ((T1 top_shpy) mb HA) ((T1 top_bcp) mb HA) L0) (only parsing).

  Lemma top_binv : forall (mb : mem) ybs a0 a8 a16 a24 a56 a72 a96 a104 bs zibs jzl jzi,
    rw_cells bsegs mb spq (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) ->
    u8arr bsegs mb X bs -> length bs = 496%nat -> rw_cells bsegs mb (X + 496) [C2 (Z_to_bv 64 len0)] ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    u8arr bsegs mb (f + 608) zibs -> length zibs = 496%nat ->
    rw_cells bsegs mb (f + 1104) [CB 2 jzl] ->
    rw_cells bsegs mb (f / 8 + 2147450956) [CB 63 jzi] ->
    bytes_at bsegs mb Y ybs -> mem_inv bsegs mb -> stk bsegs mb lo spq ->
    lm_inv X spq f lo ybs mb (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) jzi (le_bytes_to_word jzl) mb len0 False.
  Proof using TOPH.
    intros until jzi. intros SPILL XA XL XN ZR ZIA ZIL ZIC ZSH YB MI ST.
    unfold lm_inv. split; [exact SPILL|]. split; [exists bs; split; [exact XA| split; [exact XL| intros HF; exact (False_ind _ HF)]]|].
    split; [exact XN|]. split; [exact L0|]. split; [exact ZR|]. split; [exists zibs; split; [exact ZIA| exact ZIL]|].
    split; [exact (cb2_c2 mb _ jzl ZIC)|]. split; [exact ZSH|]. split; [exact YB|]. split; [exact MI|].
    split; [apply munch_refl|]. split; [apply wmono_refl| exact ST].
  Qed.

  Lemma lm_body : forall xt0 xt2 xa7 xt3 xt4 xt5 xt6 F fc ja jb jm jh h jz jzi jd bs (mb mm : mem),
    frm0 fc -> ART RT Σ1 mb -> wmono bsegs me mb -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me mb ->
    rw_cells bsegs mm spq [CB 40 ja; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f); CB 32 jb; C8 (Z_to_bv 64 5); CB 24 jm] ->
    rw_cells bsegs mm (spq + 120) [CB (Z.to_nat d) jh] ->
    rw_cells bsegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs mm f [CB 32 h] ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    rw_cells bsegs mm (f / 8 + 2147450956) [CB 63 jzi] ->
    rw_cells bsegs mm (f + 32) [CB 2008 jd] ->
    u8arr bsegs mm X bs -> length bs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len0)] ->
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    mem_inv bsegs mm -> munch [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] mb mm -> wmono bsegs mb mm ->
    stk bsegs mm lo spq ->
    aevt RT PMc Σ1 K
      (MS (mkR (Z_to_bv 64 0xecd50) (Z_to_bv 64 spq) gp tp xt0 (Z_to_bv 64 5) xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-14))
               (Z_to_bv 64 92762) (Z_to_bv 64 969940) (Z_to_bv 64 f) xa7 s2 (Z_to_bv 64 S) (Z_to_bv 64 X) (Z_to_bv 64 ((X + 496) / 8)) s6
               (Z_to_bv 64 2147450880) (Z_to_bv 64 B_P5LARGE) s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xed024) fc None mm (seg_rom bsegs)).
  Proof using TOPH.
    intros until mm. intros FRM ARTb WMb PRb SPILL HIGHc SAVED HDR SHZ SHZI FDAT XA XL XN ZR MI MU2 WM2 ST.
    top_env.

    assert (HW2 : tk_wf sp X lo f [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)])
      by (unfold tk_wf; constructor; [left; cbn [fst snd]; lia|]; constructor; [right; left; cbn [fst snd]; lia|]; constructor; [right; right; left; cbn [fst snd]; lia| constructor]).
    pose proof ((T1 top_art) _ mb mm HW2 ARTb MU2 WM2) as ARTm.
    pose proof ((T1 top_mrel) _ mb mm HW2 ARTb (conj WMb PRb) MU2 WM2) as MRm.
    clear MU2 WM2 HW2 ARTb WMb PRb.

    apply (rw_cells_split_CB bsegs mm _ [CB 40 ja; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f); CB 32 jb; C8 (Z_to_bv 64 5)] 24 jm _ [8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.
    apply (rw_cells_split_CB bsegs mm _ [CB 40 ja; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f)] 32 jb _ [8;8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.
    apply (rw_cells_split_CB bsegs mm _ [] 40 ja _ [8;8;8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.
    apply (rw_cells_split_CB bsegs mm _ [] 2008 jd [] [496; 2; 78; 496; 2; 934]%nat) in FDAT; [| reflexivity]. cbn [mk_CB_cells app] in FDAT.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 496 _] _) FDAT) as [ZAc FD1]. clear FDAT. cbn [cells_size csize Nat.add] in FD1. change (Z.of_nat 496) with 496%Z in FD1.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 2 _] _) FD1) as [ZLENc FD2]. clear FD1. cbn [cells_size csize Nat.add] in FD2. change (Z.of_nat 2) with 2%Z in FD2.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 78 _] _) FD2) as [_ FD3]. clear FD2. cbn [cells_size csize Nat.add] in FD3. change (Z.of_nat 78) with 78%Z in FD3.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 496 _] _) FD3) as [ZIAc FD4]. clear FD3. cbn [cells_size csize Nat.add] in FD4. change (Z.of_nat 496) with 496%Z in FD4.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 2 _] _) FD4) as [ZICc _]. clear FD4.
    replace (f + 32 + 496)%Z with (f + 528)%Z in * by lia. replace (f + 528 + 2 + 78)%Z with (f + 608)%Z in * by lia. replace (f + 608 + 496)%Z with (f + 1104)%Z in * by lia.
    lazymatch type of ZAc with rw_cells _ _ _ [CB _ ?jj] => assert (ZL : length jj = 496%nat) by exact (proj1 (proj1 (proj1 ZAc))) end.
    pose proof (u8arr_of_rw_cells bsegs mm _ _ _ ZAc) as ZA. clear ZAc.
    lazymatch type of ZIAc with rw_cells _ _ _ [CB _ ?jj] => assert (ZIL : length jj = 496%nat) by exact (proj1 (proj1 (proj1 ZIAc))) end.
    pose proof (u8arr_of_rw_cells bsegs mm _ _ _ ZIAc) as ZIA. clear ZIAc.
    lazymatch type of ZA with u8arr _ _ _ ?jj => rename jj into zbs end.
    lazymatch type of ZIA with u8arr _ _ _ ?jj => rename jj into zibs end.
    lazymatch type of ZICc with rw_cells _ _ _ [CB 2 ?jj] => rename jj into jzl end.

    assert (TR : forall (mm1 : mem), munch [(spq, spq + 120); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z mm mm1 -> wmono bsegs mm mm1 ->
              u8arr bsegs mm1 X bs /\ u8arr bsegs mm1 (f + 32) zbs /\ u8arr bsegs mm1 (f + 608) zibs /\ rw_cells bsegs mm1 (f + 1104) [CB 2 jzl]
              /\ rw_cells bsegs mm1 (f / 8 + 2147450956) [CB 63 jzi] /\ rw_cells bsegs mm1 (spq + 120) [CB (Z.to_nat d) jh]
              /\ rw_cells bsegs mm1 (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ rw_cells bsegs mm1 f [CB 32 h] /\ stk bsegs mm1 lo spq).
    { intros mm1 MU1 WM1. clear SPILL XN ZR SHZ ZLENc MI. unfold LM_SAVED in *. transport_after_call bsegs mm mm1 MU1 WM1.
      repeat (split; [assumption|]). assumption. }

    assert (CTXA : forall (mm1 : mem), munch [(spq, spq + 120); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z mm mm1 -> wmono bsegs mm mm1 ->
              ART RT Σ1 mm1 /\ MREL mm1).
    { intros mm1 MU1 WM1. split; [exact ((T1 top_art) _ mm mm1 (T1 top_wfWA) ARTm MU1 WM1)| exact ((T1 top_mrel) _ mm mm1 (T1 top_wfWA) ARTm MRm MU1 WM1)]. }

    assert (K100 : lm_a_100_k sp gp tp F fc X spq f mm Q len0).
    { unfold lm_a_100_k. intros until mm0. intros (SPILL1 & XN1 & ZR1 & SHZ1 & ZLEN1 & MI1 & MU1 & WM1) Hn0.
      destruct (TR mm0 MU1 WM1) as (XA1 & ZA1 & ZIA1 & ZIC1 & ZSHI1 & HIGH1 & SAVED1 & HDR1 & ST1).
      destruct (CTXA mm0 MU1 WM1) as (ART1 & MR1).
      assert (CTX1 : lm_ctx fc mm0).
      { split; [exact FRM|]. split; [exact ART1|]. split; [exact MR1|]. split; [exists jh; exact HIGH1|]. split; [exact SAVED1|].
        split; [exists h; exact HDR1|]. split; [exists zbs; split; [exact ZA1| exact ZL]| exact SHZ1]. }
      apply evt_done.
      destruct (image_readable_b bsegs mm0 40 Y ltac:(vm_compute; reflexivity) ltac:(unfold B_P5LARGE; lia) ltac:(unfold B_P5LARGE; cbn; lia)) as (ybs & YL & YB).
      apply (aevt_evt RT AF PMc MST).
      eapply (EVA lm_b F fc ybs YL mm0 ART1 Q ((T1 lm_kexit) F fc mm0 CTX1) ((T1 lm_kcpy2) 4%nat F fc mm0 ybs CTX1 YL));
        [eapply (top_binv mm0 ybs); [exact SPILL1 | exact XA1 | exact XL | exact XN1 | exact ZR1 | exact ZIA1 | exact ZIL | exact ZIC1 | exact ZSHI1 | exact YB | exact MI1 | exact ST1]
        | exact ZLEN1]. }

    assert (KCPY : lm_a_cpy_k sp gp tp F fc X spq f mm Q len0).
    { unfold lm_a_cpy_k. intros until mm0. intros (SPILL1 & XN1 & ZR1 & SHZ1 & ZLEN1 & MI1 & MU1 & WM1) Hn.
      destruct (TR mm0 MU1 WM1) as (XA1 & ZA1 & ZIA1 & ZIC1 & ZSHI1 & HIGH1 & SAVED1 & HDR1 & ST1).
      destruct (CTXA mm0 MU1 WM1) as (ART1 & MR1).
      clear TR CTXA K100 SPILL XN ZR SHZ ZLENc MI ZA ZIA ZICc SHZI HIGHc SAVED HDR ST XA MU1 WM1.
      apply evt_done.
      assert (ZRU : bytes_at bsegs mm0 ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)).
      { replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; rewrite (f64_div f 4 N1); lia).
        exact (zero_run_of_CB mm0 _ 63 SHZ1). }
      assert (UFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length zbs) <= f0 + fs_size c - 8)%Z)
        by (exists f, 5%nat; split; [exact HinF| rewrite ZL; lia]).
      assert (VFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= X)%Z /\ (X + Z.of_nat (length bs) <= f0 + fs_size c - 8)%Z)
        by (exists g, kg; split; [exact HinG| rewrite XL; lia]).
      eapply (aevt_memcpy_u8 RT AF RTF PMc FDO MST Σ1 K mm0 lo (Z_to_bv 64 spq)
                (f + 32)%Z zbs 63 ZA1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite ZL; lia) ltac:(rewrite ZL; lia) ltac:(rewrite ZL; lia) ZRU UFR
                X bs 63 XA1 X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia) ZR1 VFR
                ART1 MI1 ((T1 top_cok) mm0 ST1)) with (nz := (8 * len0)%Z);
        [reflexivity | reflexivity | reflexivity | lia | rewrite ZL; lia | rewrite XL; lia | lia | lia | exact FRM | ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' zbs' FRM' RA PR ZA' ZL'.
      rewrite ?unsigned_lit in RA, PR by lia.
      pose proof (lm_mrel_ex RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP mm0 m' _ _ ART1 MR1 (proj1 (proj2 (proj2 RA))) PR ltac:(left; lia)) as MR'.
      destruct RA as (ART' & MI' & WM' & ST').
      pose proof (agree_of_pres_ex _ _ _ _ _ mm0 m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (f + 32 <= x < f + 32 + 8 * len0)%Z) PR (fun x H => H)) as AG.
      clear ZA1 ZRU ST1 MI1. unfold LM_SAVED in SAVED1. unfold lm_spillB in SPILL1.
      rt_transport_with mm0 m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL, ?ZIL in Hx; cbv beta; split; [aclient_tac| lia]).
      assert (CTX' : lm_ctx fc' m').
      { split; [exact FRM'|]. split; [exact ART'|]. split; [exact MR'|]. split; [exists jh; exact HIGH1|]. split; [exact SAVED1|].
        split; [exists h; exact HDR1|]. split; [exists zbs'; split; [exact ZA'| lia]| exact SHZ1]. }
      destruct (image_readable_b bsegs m' 40 Y ltac:(vm_compute; reflexivity) ltac:(unfold B_P5LARGE; lia) ltac:(unfold B_P5LARGE; cbn; lia)) as (ybs & YL & YB).
      apply (aevt_evt RT AF PMc MST). num_ret_pc.
      eapply (EVA lm_0f4 F' fc' ybs YL m' ART' Q ((T1 lm_kexit) F' fc' m' CTX') ((T1 lm_kcpy2) 4%nat F' fc' m' ybs CTX' YL));
        [eapply (top_binv m' ybs); [exact SPILL1 | exact XA1 | exact XL | exact XN1 | exact ZR1 | exact ZIA1 | exact ZIL | exact ZIC1 | exact ZSHI1 | exact YB | exact MI' | exact ST']
        | exact ZLEN1]. }
    apply (aevt_evt RT AF PMc MST).
    eapply (lm_a sp gp tp F fc X lo d spq f mm (T1 top_spq) ROOM TOP N1 (conj N2 N3) N4 (conj N5 N6) X8 (conj Q1 Q2) Q3 (conj Q4 Q5) SEP Q len0 KCPY K100);
      [exact SPILL | exact XN | exact L0 | exact ZR | exact SHZ | exact ZLENc | exact MI | apply munch_refl | apply wmono_refl].
  Qed.
End LMTOP3.

Theorem lmb_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> lmb_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST. unfold lmb_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X lo bs len ETP FRM FRL CR ART0 MI ST LOR ROOM TOP SP16 BB HK.
  pose proof (bbig_abig RT Σ m X bs len BB) as AB.
  destruct BB as (FO & XL & XA & XN & LEN).
  destruct (abig_elim RT _ _ _ AB) as (bs1 & n1 & RAW1).
  pose proof (abig_facts RT AF Σ m X bs1 n1 lo ART0 LOR RAW1) as XNUM.
  destruct RAW1 as (_ & _ & _ & _ & ZR & X8 & XFR).
  assert (RAW : abig_raw RT Σ m X bs len) by (split; [exact XA|]; split; [exact XL|]; split; [exact XN|]; split; [exact LEN|]; split; [exact ZR|]; split; [exact X8| exact XFR]).
  eapply (lm_enter RT AF RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X lo bs len);
    [exact ETP | exact FRM | exact FRL | exact CR | exact ART0 | exact MI | exact ST | exact LOR | exact ROOM | exact TOP | exact SP16 | exact RAW |].
  unfold lm_body_k.
  intros Σ' d spq f xt0 xt2 xa7 xt3 xt4 xt5 xt6 F' fc' ja jb jm jh h jz jzi jd mb mm
    EF EL ES EC FRM' ART' WMb PRb SPQ SPILL HIGHc SAVED HDR SHZ SHZI FDAT RAW' MI' MU2 WM2 ST' NF SEP.
  destruct RAW' as (XA' & XL' & XN' & LEN' & ZR' & _ & (g & kg & XG)).
  eapply (lm_body RT AF RTF PMc FDO MST Σ Σ' K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g len kg m ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP LEN HK
            xt0 xt2 xa7 xt3 xt4 xt5 xt6 F' fc' ja jb jm jh h jz jzi jd bs mb mm); eassumption.
Qed.
