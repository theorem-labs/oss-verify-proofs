(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro Sj_num_lm_enter Sj_num_lm_leave
  Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_tkit Sj_num_lm_a Sj_num_lm_b Sj_num_lm_c1 Sj_num_lm_c2 Sj_num_lm_c3 Sj_num_lm_top Sj_num_lm_top2 Sj_num_lm_top2b Sj_num_pow5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis NLA : num_lits_acc RT.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := 0x2b3e0%Z.
  Hypothesis ETP : tp = Z_to_bv 64 0x69ec68.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6c1000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6c1000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - 1 <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST NLA ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).

  Notation T1 L := (L RT AF RTF PMc FDO MST NLA Σ0 Σ1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg me
                      ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK) (only parsing).
  Notation lm_ctx := (Sj_num_lm_top.lm_ctx RT Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f me).
  Notation EVA L F fc ybs YL mb := (L sp gp tp F fc X lo d spq f Y ybs mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP (T1 top_yr) YL) (only parsing).
  Notation LMS F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac top_env :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF) as HinF; pose proof (T1 top_f8) as F8; pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5;
    pose proof (proj1 XG) as HinG0; pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2;
    assert (HinG : In (g, kg) (rt_frames RT Σ1)) by (rewrite EF; right; exact HinG0);
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.

  Lemma top_b : forall F fc (mb : mem) ybs (n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs11 xt3 xt6
      a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 xbs zibs jzl jzi,
    lm_ctx fc mb -> length ybs = 40%nat ->
    rw_cells asegs mb (spq + 16) [CB 8 a16; CB 8 a24; CB 8 a32; CB 8 a40; CB 8 a48; CB 8 a56; CB 8 a64; C8 (Z_to_bv 64 f); CB 8 a80; CB 8 a88;
                                  C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 X);
                                  CB 8 a128; CB 8 a136; C8 (Z_to_bv 64 f)] ->
    u8arr asegs mb X xbs -> length xbs = 496%nat ->
    rw_cells asegs mb (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells asegs mb (f + 528) [C2 (Z_to_bv 64 0)] ->
    u8arr asegs mb (f + 608) zibs -> length zibs = 496%nat ->
    rw_cells asegs mb (f + 1104) [CB 2 jzl] ->
    rw_cells asegs mb (f / 8 + 2147450956) [CB 63 jzi] ->
    bytes_at asegs mb Y ybs -> mem_inv asegs mb ->
    aevt RT PMc Σ1 K (LMS F fc 0xe12ac xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 Y) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3
                          (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xt6 mb).
  Proof using TOPH.
    intros until jzi. intros CTX YL SPILL XA XL XN LEN ZR ZLENc ZIA ZIL ZIC ZSH YB MI.
    apply (aevt_evt RT AF PMc MST).
    eapply (EVA lm_b F fc ybs YL mb (T1 top_shpy mb (proj1 (proj2 CTX))) Q (T1 lm_khead 4%nat (T1 lm_loop 4%nat) F fc mb ybs CTX YL) (T1 lm_kexit F fc mb CTX) n);
      [exact SPILL | exact XA | exact XL | exact XN | exact LEN | exact ZR | exact ZLENc | exact ZIA | exact ZIL | exact ZIC | exact ZSH | exact YB | exact MI
      | apply munch_refl | apply wmono_refl].
  Qed.

  Lemma lm_body : forall xra xt0 xt1 xt2 xa4 xa5 xa7 xs4 xs6 xs7 xs8 xs11 xt3 xt5 xt6 F fc ja0 ja1 jb0 jb1 jb2 jl jh h jz jzi jd bs n (mb mm : mem),
    frm0 fc -> ART RT Σ1 mb -> wmono asegs me mb -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me mb ->
    rw_cells asegs mm spq [CB 16 jl] ->
    rw_cells asegs mm (spq + 16) [CB 56 ja0; C8 (Z_to_bv 64 f); CB 40 ja1; C8 (Z_to_bv 64 X); CB 8 jb0; CB 8 jb1; CB 8 jb2] ->
    rw_cells asegs mm (spq + 152) [CB (Z.to_nat d) jh] ->
    rw_cells asegs mm (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs mm f [CB 32 h] ->
    rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz) ->
    rw_cells asegs mm (f / 8 + 2147450956) (mk_CB_cells (repeat 1%nat 63) jzi) ->
    rw_cells asegs mm (f + 32) [CB 2008 jd] ->
    u8arr asegs mm X bs -> length bs = 496%nat -> rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    mem_inv asegs mm -> munch [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] mb mm -> wmono asegs mb mm ->
    stk asegs mm lo spq ->
    aevt RT PMc Σ1 K
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-13)) (Z_to_bv 64 ((X + 496) / 8)) (Z_to_bv 64 (-14))
               xa4 xa5 (Z_to_bv 64 (-8)) xa7 (Z_to_bv 64 f) (Z_to_bv 64 S) xs4 (Z_to_bv 64 Y) xs6 xs7 xs8 (Z_to_bv 64 5) (Z_to_bv 64 2147450880) xs11
               xt3 (Z_to_bv 64 X) xt5 xt6)
          F (Z_to_bv 64 0xe1164) fc None mm (seg_rom asegs)).
  Proof using TOPH.
    intros until mm. intros FRM ARTb WMb PRb LOWc SPILL HIGHc SAVED HDR SHZ SHZI FDAT XA XL XN LEN ZR MI MU2 WM2 ST.
    top_env.

    assert (HW2 : tk_wf sp X lo f [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)])
      by (unfold tk_wf; repeat constructor; cbn [fst snd]; lia).
    pose proof (T1 top_art _ mb mm HW2 ARTb MU2 WM2) as ARTm.
    pose proof (T1 top_mrel _ mb mm HW2 ARTb (conj WMb PRb) MU2 WM2) as MRm.
    clear MU2 WM2 HW2 ARTb WMb PRb.

    apply (rw_cells_split_CB asegs mm _ [CB 56 ja0; C8 (Z_to_bv 64 f)] 40 ja1 _ [8;8;8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.
    apply (rw_cells_split_CB asegs mm _ [] 56 ja0 _ [8;8;8;8;8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.
    destruct (rw_cells_forget asegs _ _ _ SHZ) as [jz' SHZ']. rewrite mk_CB_cells_size in SHZ'. cbn [sum_nat repeat Nat.add] in SHZ'. clear SHZ.
    destruct (rw_cells_forget asegs _ _ _ SHZI) as [jzi' SHZI']. rewrite mk_CB_cells_size in SHZI'. cbn [sum_nat repeat Nat.add] in SHZI'. clear SHZI.
    apply (rw_cells_split_CB asegs mm _ [] 2008 jd [] [496; 2; 78; 496; 2; 934]%nat) in FDAT; [| reflexivity]. cbn [mk_CB_cells app] in FDAT.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 496 _] _) FDAT) as [ZAc FD1]. clear FDAT. cbn [cells_size csize Nat.add] in FD1. change (Z.of_nat 496) with 496%Z in FD1.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 2 _] _) FD1) as [ZLENc FD2]. clear FD1. cbn [cells_size csize Nat.add] in FD2. change (Z.of_nat 2) with 2%Z in FD2.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 78 _] _) FD2) as [_ FD3]. clear FD2. cbn [cells_size csize Nat.add] in FD3. change (Z.of_nat 78) with 78%Z in FD3.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 496 _] _) FD3) as [ZIAc FD4]. clear FD3. cbn [cells_size csize Nat.add] in FD4. change (Z.of_nat 496) with 496%Z in FD4.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 2 _] _) FD4) as [ZICc _]. clear FD4.
    replace (f + 32 + 496)%Z with (f + 528)%Z in * by lia. replace (f + 528 + 2 + 78)%Z with (f + 608)%Z in * by lia. replace (f + 608 + 496)%Z with (f + 1104)%Z in * by lia.
    assert (ZL : length j = 496%nat) by exact (proj1 (proj1 (proj1 ZAc))).
    pose proof (u8arr_of_rw_cells asegs mm _ _ _ ZAc) as ZA. clear ZAc.
    lazymatch type of ZIAc with rw_cells _ _ _ [CB _ ?jj] => assert (ZIL : length jj = 496%nat) by exact (proj1 (proj1 (proj1 ZIAc))) end.
    pose proof (u8arr_of_rw_cells asegs mm _ _ _ ZIAc) as ZIA. clear ZIAc.
    lazymatch type of ZA with u8arr _ _ _ ?jj => rename jj into zbs end.
    lazymatch type of ZIA with u8arr _ _ _ ?jj => rename jj into zibs end.
    lazymatch type of ZICc with rw_cells _ _ _ [CB 2 ?jj] => rename jj into jzl end.

    assert (TR : forall (mm1 : mem), munch [(spq + 16, spq + 152); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z mm mm1 -> wmono asegs mm mm1 ->
              u8arr asegs mm1 X bs /\ u8arr asegs mm1 (f + 32) zbs /\ u8arr asegs mm1 (f + 608) zibs /\ rw_cells asegs mm1 (f + 1104) [CB 2 jzl]
              /\ rw_cells asegs mm1 (f / 8 + 2147450956) [CB 63 jzi'] /\ rw_cells asegs mm1 spq [CB 16 jl] /\ rw_cells asegs mm1 (spq + 152) [CB (Z.to_nat d) jh]
              /\ rw_cells asegs mm1 (SP + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ rw_cells asegs mm1 f [CB 32 h] /\ stk asegs mm1 lo spq).
    { intros mm1 MU1 WM1. clear SPILL XN ZR SHZ' ZLENc MI. unfold LM_SAVED in *. transport_after_call asegs mm mm1 MU1 WM1.
      repeat (split; [assumption|]). assumption. }

    assert (CTXA : forall (mm1 : mem), munch [(spq + 16, spq + 152); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z mm mm1 -> wmono asegs mm mm1 ->
              ART RT Σ1 mm1 /\ MREL mm1).
    { intros mm1 MU1 WM1. split; [exact (T1 top_art _ mm mm1 (T1 top_wfWA) ARTm MU1 WM1)| exact (T1 top_mrel _ mm mm1 (T1 top_wfWA) ARTm MRm MU1 WM1)]. }

    assert (KD7C : lm_a_d7c_k sp gp tp F fc X spq f mm Q).
    { unfold lm_a_d7c_k. intros until mm0. intros (SPILL1 & XN1 & ZR1 & SHZ1 & ZLEN1 & MI1 & MU1 & WM1).
      destruct (TR mm0 MU1 WM1) as (XA1 & ZA1 & ZIA1 & ZIC1 & ZSHI1 & LOW1 & HIGH1 & SAVED1 & HDR1 & ST1).
      destruct (CTXA mm0 MU1 WM1) as (ART1 & MR1).
      assert (CTX1 : lm_ctx fc mm0).
      { split; [exact FRM|]. split; [exact ART1|]. split; [exact MR1|]. split; [exists jl; exact LOW1|]. split; [exists jh; exact HIGH1|]. split; [exact SAVED1|].
        split; [exists h; exact HDR1|]. split; [exists zbs; split; [exact ZA1| exact ZL]|]. split; [exact SHZ1| exact ST1]. }
      apply evt_done.
      destruct (image_readable_b asegs mm0 40 Y ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (ybs & YL & YB).
      eapply (top_b F fc mm0 ybs 0%Z); [exact CTX1 | exact YL | exact SPILL1 | exact XA1 | exact XL | exact XN1 | lia | exact ZR1 | exact ZLEN1 | exact ZIA1 | exact ZIL
                                      | exact ZIC1 | exact ZSHI1 | exact YB | exact MI1]. }

    assert (KCPY : lm_a_cpy_k sp gp tp F fc X spq f mm Q).
    { unfold lm_a_cpy_k. intros until mm0. intros (SPILL1 & XN1 & ZR1 & SHZ1 & ZLEN1 & MI1 & MU1 & WM1) Hn.
      destruct (TR mm0 MU1 WM1) as (XA1 & ZA1 & ZIA1 & ZIC1 & ZSHI1 & LOW1 & HIGH1 & SAVED1 & HDR1 & ST1).
      destruct (CTXA mm0 MU1 WM1) as (ART1 & MR1).
      clear TR CTXA KD7C SPILL XN ZR SHZ' ZLENc MI ZA ZIA ZICc SHZI' LOWc HIGHc SAVED HDR ST XA MU1 WM1.
      apply evt_done.
      assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact N1).
      assert (ZRU : bytes_at asegs mm0 ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63))
        by (replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm0 _ 63 SHZ1)).
      assert (UFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length zbs) <= f0 + fs_size c - 8)%Z)
        by (exists f, 5%nat; split; [exact HinF| rewrite ZL; lia]).
      assert (VFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= X)%Z /\ (X + Z.of_nat (length bs) <= f0 + fs_size c - 8)%Z)
        by (exists g, kg; split; [exact HinG| rewrite XL; lia]).
      eapply (aevt_memcpy_u8 RT AF RTF PMc FDO MST Σ1 K mm0 lo (Z_to_bv 64 spq)
                (f + 32)%Z zbs 63 ZA1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite ZL; lia) ltac:(rewrite ZL; lia) ltac:(rewrite ZL; lia) ZRU UFR
                X bs 63 XA1 X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia) ZR1 VFR
                ART1 MI1 (T1 top_cok mm0 ST1)) with (nz := (8 * n0)%Z);
        [reflexivity | reflexivity | reflexivity | lia | rewrite ZL; lia | rewrite XL; lia | lia | lia | exact FRM | ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' zbs' FRM' RA PR ZA' ZL'.
      rewrite ?unsigned_lit in RA, PR by lia.
      pose proof (lm_mrel_ex RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP mm0 m' _ _ ART1 MR1 (proj1 (proj2 (proj2 RA))) PR ltac:(left; lia)) as MR'.
      destruct RA as (ART' & MI' & WM' & ST').
      pose proof (agree_of_pres_ex _ _ _ _ _ mm0 m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (f + 32 <= x < f + 32 + 8 * n0)%Z) PR (fun x H => H)) as AG.
      clear ZA1 ZRU ST1 MI1. unfold LM_SAVED in SAVED1.
      rt_transport_with mm0 m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL, ?ZIL in Hx; cbv beta; split; [aclient_tac| lia]).
      assert (CTX' : lm_ctx fc' m').
      { split; [exact FRM'|]. split; [exact ART'|]. split; [exact MR'|]. split; [exists jl; exact LOW1|]. split; [exists jh; exact HIGH1|]. split; [exact SAVED1|].
        split; [exists h; exact HDR1|]. split; [exists zbs'; split; [exact ZA'| lia]|]. split; [exact SHZ1| exact ST']. }
      destruct (image_readable_b asegs m' 40 Y ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (ybs & YL & YB).
      apply (aevt_evt RT AF PMc MST). num_ret_pc.
      astep. astep. apply evt_done.
      eapply (top_b F' fc' m' ybs n0); [exact CTX' | exact YL | exact SPILL1 | exact XA1 | exact XL | exact XN1 | lia | exact ZR1 | exact ZLEN1 | exact ZIA1 | exact ZIL
                                       | exact ZIC1 | exact ZSHI1 | exact YB | exact MI']. }
    apply (aevt_evt RT AF PMc MST).
    eapply (lm_a sp gp tp F fc X lo d spq f mm (T1 top_spq) ROOM TOP N1 (conj N2 N3) N4 (conj N5 N6) X8 (conj Q1 Q2) Q3 (conj Q4 Q5) SEP Q KCPY KD7C n);
      [exact SPILL | exact XN | exact LEN | exact ZR | exact SHZ' | exact ZLENc | exact MI | apply munch_refl | apply wmono_refl].
  Qed.
End LMTOP.

Theorem lma_ok : forall RT, art_facts RT -> rt_contracts_f RT -> num_lits_acc RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> lma_stmt RT PMc.
Proof.
  intros RT AF RTF NLA PMc FDO MST. unfold lma_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X lo ETP FRM FRL CR ART0 MI ST LOR ROOM TOP SP16 AB HK.
  destruct (abig_elim RT _ _ _ AB) as (bs & n & RAW).
  pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as XNUM.
  eapply (lm_enter RT AF RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X lo bs n);
    [exact ETP | exact FRM | exact FRL | exact CR | exact ART0 | exact MI | exact ST | exact LOR | exact ROOM | exact TOP | exact SP16 | exact RAW |].
  unfold lm_body_k.
  intros Σ' d spq f xra xt0 xt1 xt2 xa4 xa5 xa7 xt3 xt5 xt6 F' fc' ja0 ja1 jb0 jb1 jb2 jl jh h jz jzi jd bs' n' mb mm
    EF EL ES EC FRM' ART' WMb PRb SPQ LOWc SPILL HIGHc SAVED HDR SHZ SHZI FDAT RAW' MI' MU2 WM2 ST' NF SEP.
  destruct RAW' as (XA & XL & XN & LEN & ZR & X8 & (g & kg & XG)).
  eapply (lm_body RT AF RTF PMc FDO MST NLA Σ Σ' K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg m ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK
            xra xt0 xt1 xt2 xa4 xa5 xa7 s4 s6 s7 s8 s11 xt3 xt5 xt6 F' fc' ja0 ja1 jb0 jb1 jb2 jl jh h jz jzi jd bs' n' mb mm); eassumption.
Qed.

Theorem p5a_closed : forall RT, art_facts RT -> rt_contracts_f RT -> num_lits_acc RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> p5a_stmt RT PMc.
Proof. intros RT AF RTF NLA PMc FDO MST. exact (p5a_ok RT AF RTF NLA PMc FDO MST (lma_ok RT AF RTF NLA PMc FDO MST)). Qed.
