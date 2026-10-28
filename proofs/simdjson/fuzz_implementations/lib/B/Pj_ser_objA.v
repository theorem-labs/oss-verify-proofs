(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit D_rlkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA
     Pj_ser_ckitA Pj_ser_arrA Pj_ser_objkA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap Z.b2z]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac ul := unfold SEGTOP_A in *; lia.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat z8 8.
Proof. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sh16_of_zeros : forall (m : mem) a, rw_cells bsegs m a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m a (sh16 (repeat z8 16)).
Proof.
  intros m a [[W B] R]. split; [split|].
  - cbn. repeat split; exact Logic.I.
  - cbn [cells_bytes cbytes app] in B. rewrite le8_zero in B. cbn [repeat app] in B. unfold sh16, z8. cbn [repeat map cells_bytes cbytes app]. exact B.
  - exact R.
Qed.

Definition obj_shpatN : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; -8; -14; -14; -14; -8; -13; -13; -13; 0; 0; 0; 0].
Lemma obj_shpatN_eq : obj_shpatN = obj_shpatA.
Proof. unfold obj_shpatN, obj_shpatA. cbn [map]. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

Lemma oland_m32d : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists dd, (dd = 0 \/ dd = 16) /\ Z.land x 18446744073709551584 = x - dd /\ (x - dd) mod 32 = 0.
Proof.
  intros x Hx X16. exists (x - 32 * (x / 32)). rewrite (land_m32 x Hx).
  split; [Z.div_mod_to_equations; lia|]. split; [lia| Z.div_mod_to_equations; lia].
Qed.

Definition osavedA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma obj_pro1 : forall (q lo SB DOC i : Z) (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo + 368 <= q -> 0x6e0000 <= lo -> q + 16 <= USTACK_TOP -> q mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (dd : Z) (a1' a2' : word),
      (dd = 0 \/ dd = 16) /\ (q - 352 - dd) mod 32 = 0 /\
      ms = MS (mkR (wz 0xbb930) (wz (q - 352 - dd)) gp (wz TPV_A) t0 t1 t2 (wz q) (wz (q - 352 - dd)) (wz 96) a1' a2' a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 (wz DOC) (wz 2147450880) (wz i) s10 (wz SB) t3 t4 t5 t6) F (wz e_stack_malloc_1) fc None m1 (seg_rom bsegs)
      /\ munch [(q - 352, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (q - 104) /\ rw_cells bsegs m1 (q - 104) (osavedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SB) (wz DOC) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PJ_APPEND_OBJ_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO QT Q16 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold PJ_APPEND_OBJ_A, e_stack_malloc_1, TPV_A, USTACK_TOP, osavedA in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 352, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep.
  carve_frame 352%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 352 _ [] [8; 240; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  lstep. do 13 zstep. zstep. zstep.
  destruct (oland_m32d (q + -352) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (dd & DD & ELAND & B32). rewrite ELAND.

  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  pose proof (stk_of_rw_cells bsegs _ _ _ FRl) as STl. cbn [cells_size csize Nat.add] in STl.
  pose proof (stk_merge bsegs _ _ _ _ ST STl ltac:(lia)) as ST2.
  replace (q + -352 + Z.of_nat 248) with (q - 104) in FRs, ST2 by lia.
  replace (q + -352 - dd) with (q - 352 - dd) by lia. replace (q + -352 + 352) with q by lia.
  apply evt_done. eexists. exists dd. eexists. eexists. split; [exact DD|]. split; [lia|]. split; [cbv delta [mkR]; reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  split; [exact WM|]. split; [eassumption|]. split; [exact ST2| exact FRs].
Qed.

Section SM1.
Variable RT : rt_sig.
Hypothesis SM1Z : stack_malloc1z_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma aevt_smalloc1z : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 TPV_A ->
  (length (rt_frames RT Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  rt_frames RT Σ <> [] ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 1 - 8) -> wr_at bsegs m' (shad f) (fs_size 1 / 8) -> rw_cells bsegs m' (shad f) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
     rt_frames RT Σ' = (f, 1%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 1 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_stack_malloc_1) fc None m (seg_rom bsegs)).
Proof using SM1Z FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK NE HK.
  eapply aevt_icall.
  - exact (SM1Z Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST ETP FRL CR ART0 MI0 COK NE).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2 & W3).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 W3 E1 E2 E3 E4 F1 F2 F3).
Qed.
End SM1.

Lemma obj_pro2 : forall (q b f lo SB DOC i : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s10 t3 t4 t5 t6 : word) (h : list byte) F fc (m : mem),
  0 < f -> f + 128 <= lo -> f / 8 + 2147450880 + 16 <= lo -> 8 * (f / 8) = f ->
  (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0x6e0000 <= lo -> lo <= b -> b + 352 <= q -> q + 16 <= USTACK_TOP -> 0 <= SB -> SB + 96 <= lo -> 0 <= i < 2^32 ->
  stk bsegs m b (q - 104) ->
  rw_cells bsegs m f [CB 24 h] -> stk bsegs m (f + 24) (f + 120) -> rw_cells bsegs m (f / 8 + 2147450880) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (w : owA) (ra' t0' a0' a2' a4' a5' a6' : word),
      ms = MS (mkR ra' (wz b) gp (wz TPV_A) t0' t1 t2 (wz q) (wz b) a0' (wz ((SB + 80) / 8 + 2147450880)) a2' (wz (f / 8 + 2147450880)) a4' a5' a6' a7
                   (wz f) s3 (wz f) s5 s6 (wz DOC) (wz 2147450880) (wz i) s10 (wz SB) t3 t4 t5 t6)
              F (wz 0xbb9e4) fc None m1 (seg_rom bsegs)
      /\ munch [(b, b + 248); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ ow208 w = wz (SB + 80) /\ ow168 w = wz (f / 8 + 2147450880) /\ ow200 w = wz ((SB + 80) / 8 + 2147450880)
      /\ stk bsegs m1 b (b + 8) /\ rw_cells bsegs m1 (b + 8) (obj_slotsA w) /\ stk bsegs m1 (b + 248) (q - 104)
      /\ rw_cells bsegs m1 f obj_hdrA /\ stk bsegs m1 (f + 24) (f + 120) /\ rw_cells bsegs m1 (f / 8 + 2147450880) (sh16 obj_shpatA))
    (MS (mkR (wz 0xbb930) (wz b) gp (wz TPV_A) t0 t1 t2 (wz q) (wz b) (wz f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz DOC) (wz 2147450880) (wz i) s10 (wz SB) t3 t4 t5 t6)
        F (wz 0xbb930) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SFL Ef SHf GLO LOB BQ QT SB0 SBR IR STF FH F1S SHC MI.
  unfold TPV_A, USTACK_TOP in *.
  pose proof (munch_refl [(b, b + 248); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  destruct (stk_split bsegs m _ (b + 8) _ STF ltac:(lia)) as [FR0 ST1].
  destruct (stk_split bsegs m _ (b + 248) _ ST1 ltac:(lia)) as [STs GAP].
  destruct (stk_CB bsegs m _ _ STs ltac:(lia)) as (js & FR). replace (Z.to_nat (b + 248 - (b + 8))) with 240%nat in FR by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 240 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FR; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH; [| reflexivity]. cbn [mk_CB_cells app] in FH.
  repeat match type of FH with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "h" in set (j := tt) in FH; clearbody j end.

  apply sh16_of_zeros in SHC. unfold sh16, z8 in SHC. cbn [repeat map] in SHC.
  clear STF ST1 STs js.
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).

  zstep. step. zstep. step. if_cases K0; zify_cond K0; [clear K0| exfalso; pjnorm_in K0; lia].

  zstep. step. step. zstep. pjnorm. zstep. zstep. zstep. zstep. zstep. zstep. lstep. lstep. lstep.

  zstep. zstep. ls. ls. ls. ls. zstep. ls. ls. ls. ls. step. zstep. pjnorm. ls. ls. ls. step. ls. zstep. step.
  apply rw_cells_c8ify in FR. cbn [map c8c Nat.eqb] in FR.
  apply evt_done.
  eexists. eexists (mkOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). do 7 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact FR0|]. split; [exact FR|]. split; [exact GAP|]. split; [exact FH|]. split; [exact F1S|].
  rewrite <- obj_shpatN_eq. unfold obj_shpatN, sh16. cbn [map]. exact SHC.
Qed.

Lemma obj_epi2 : forall (q b f fl lo : Z) (gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xra : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FRC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0x6e0000 <= lo -> lo <= b -> cells_size FRC = 240%nat -> b + 352 <= q -> q + 16 <= USTACK_TOP -> b + 248 <= q - 104 ->
  stk bsegs m lo b -> stk bsegs m b (b + 8) -> rw_cells bsegs m (b + 8) FRC -> stk bsegs m (b + 248) (q - 104) ->
  rw_cells bsegs m (q - 104) (osavedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ro_cells bsegs m (f + 120) [C8 (wz fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st ra (wz q) gp (wz TPV_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz fl) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR xra (wz b) gp (wz TPV_A) xt0 xt1 xt2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (wz f) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz 0xbca38) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LOB SZ BQ QT GB ST FR0 FR GAP FS FW FLC MI.
  unfold TPV_A, USTACK_TOP, osavedA in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep. ls. step. zstep.
  replace (q - 104) with (q + -104) in FS by lia.

  do 13 zstep. zstep.
  replace (q + -104) with (q - 104) in FS by lia.
  pose proof (stk_merge bsegs _ _ _ _ ST FR0 ltac:(lia)) as ST0.
  pose proof (stk_release bsegs _ _ _ _ ST0 FR ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 240%nat) with 240 in ST1.
  replace (b + 8 + 240) with (b + 248) in ST1 by lia.
  pose proof (stk_merge bsegs _ _ _ _ ST1 GAP ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (q - 104 + Z.of_nat 104) with q in ST3 by lia. replace (q + -352 + 352) with q by lia.

  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Section Obj.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Variables (E : pjenvA) (D : nat) (C : conI) (f : Z) (K : config -> Prop).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : cctxA E D C.
Hypothesis OX : octxA E C f.
Hypothesis SER : ser_cpsA RT PMc D.
Hypothesis OKEY1 : okey1_stmtA RT PMc.
Hypothesis OKEY2 : okey2_stmtA RT PMc.

Variable n0 : Z. Variable c0 : Z.
Hypothesis HTY : ty (pa_T E) (ci_i C) = t_obj.
Hypothesis HNX : tnext (pa_T E (ci_i C)) = ci_e C + 1.
Hypothesis HT : tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) true D) (ci_i C + 1) (ci_e C) n0 c0 (ci_c' C).
Hypothesis HC0 : 0 <= c0.

Hypothesis KFIN : forall (Σ' : rts RT) (st' : sbA) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
  frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) (ci_q C) ->
  SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' (ci_e C + 1) (ci_c' C) -> pa_live RT Σ' E st' ->
  rt_frames RT Σ' = ci_fr0 C -> rt_sp0 RT Σ' = ci_sp0 C -> ci_R C + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
  rt_pres_fp (pa_L E) (ci_fr0 C) (ci_q C) [(pa_SB E, pa_SB E + 88)] (ci_m0 C) m' ->
  aevt RT PMc Σ' K (MS (mkR (ci_ra C) (wz (ci_q C)) (ci_gp C) (wz TPV_A) t0' t1' t2' (ci_s0 C) (ci_s1 C) a0' a1' a2' a3' a4' a5' a6' a7'
                         (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) t3' t4' t5' t6')
                    F' (ret_pc (ci_ra C)) fc' None m' (seg_rom bsegs)).
Notation aevt := (aevt RT PMc).
Notation e := (ci_e C).
Notation FIELD := (itemS (pa_T E) (pa_S E) (pa_sn E) true D).
Notation OFRP w := (obj_frp E C f w obj_shpatA).
Notation SH72 := ((pa_SB E + 72) / 8 + 2147450880).
Notation SH64 := ((pa_SB E + 64) / 8 + 2147450880).
Notation SH80 := ((pa_SB E + 80) / 8 + 2147450880).
Notation SHDf := (f / 8 + 2147450880).
Notation SHD8 := ((pa_DOC E + 8) / 8 + 2147450880).
Notation NOT65 := (18446744073709551615 - (f + 65)).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k Z.b2z]; lia.

Local Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].

Local Ltac guards3 := gtrap; zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gtrap; gtrap.
Local Ltac guards3j := gok; zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gok; gok.

Local Ltac out_facts APB y A1 A2 A3 A4 A5 :=
  let H := fresh in pose proof (APB y) as H;
  let A0 := fresh in
  destruct H as (A0 & A2 & A3); [|
  assert (A1 : ~ (ci_b C <= y < ci_q C)) by (intros H'; apply A0; exists (ci_b C), (ci_q C); split; [left; reflexivity| exact H']);
  assert (A4 : ~ (f <= y < f + 120)) by (intros H'; apply A0; exists f, (f + 120); split; [right; rewrite (oc_R E C f OX); left; reflexivity| exact H']);
  assert (A5 : ~ (SHDf <= y < SHDf + 16))
    by (intros H'; apply A0; exists SHDf, (f / 8 + 2147450896); split; [right; rewrite (oc_R E C f OX); right; left; reflexivity| clear - H'; lia]);
  clear A0 ].

Local Ltac tref_call HSMc HSMn Hidx :=
  step;
  eapply evt_cut; [eapply (cont_trefA RT AF E D C); [exact OK| exact CX| apply obj_frp_local; exact OX| exact HSMc| Hidx]|];
  cbv beta; let m1 := fresh "m" in let ya := fresh "ya4" in intros ? (m1 & ya & -> & HSMn); clear HSMc;
  rewrite ret_pc_even by (clear; lia); obj_open HSMn OK CX OX.

Lemma obj_fieldA : forall x x' cx cx', FIELD x x' cx cx' -> 1 <= x -> x' <= e ->
  exists l c1, pa_T E x = tword t_str cx /\ str_at (pa_S E) (pa_sn E) cx l /\ c1 = cx + l + 5
    /\ elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D (x + 1) x' c1 cx' /\ x + 1 < x' /\ cx + 5 <= c1 /\ c1 <= cx' /\ 0 <= l.
Proof using OK CX.
  intros x x' cx cx' HF HX HXE. unfold itemS, fieldS in HF. destruct HF as (c1 & (l & HTx & HS & EC) & HEL).
  pose proof HS as (_ & L0 & _).
  exists l, c1. split; [exact HTx|]. split; [exact HS|]. split; [exact EC|]. split; [exact HEL|].
  split; [exact (elemS_lt _ _ _ _ _ _ _ _ _ HEL)|]. split; [lia|]. split; [exact (proj1 (elemS_cur _ _ _ _ _ _ _ _ _ HEL))| exact L0].
Qed.

Lemma obj_close_byteA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (w : owA)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  ow168 w = wz SHDf ->
  CERMA RT E C (OFRP w) Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * e + 6 * ci_c' C + 2 -> CCREDA RT E C Σ 0 st ->
  aevt Σ K (OST E C 0xbc9d8 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz f) (wz f) xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX OX KFIN.
  intros Σ st m F fc w xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 E168 HSM FRM SZ1 ACC CR.
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2). pose proof (cc_sp0 E D C CX) as (W1 & W2).
  pose proof (oc_fr E C f OX) as EFR. pose proof (cc_F4 E D C CX) as IN4.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST).
  pose proof (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM) as INV0. pose proof (pa_live_of_CERMA RT E D C _ Σ _ m CX HSM) as PL0.
  obj_open HSM OK CX OX.
  cbn [ow168] in E168. rewrite E168 in FR.
  pose proof HREF as (ART0 & LV & FRx & SP & _).
  pose proof (buf_factsC RT AF E D C OK CX Σ _ _ HREF) as (BLb & _ & _ & CLB & APB). cbn [sa_buf sa_cap] in BLb, CLB, APB.
  out_facts APB (buf + (size - 1)) A1 A2 A3 A4 A5; [clear - SZ1 SZ; lia|].
  assert (EU : bv_unsigned (wz (ci_b C)) = ci_b C) by (apply unsigned_lit; clear - LB QT OBQ LO; lia).

  step. step. pj_store_done.

  unbox FSB; unbox SHf; unbox SHSB.
  zstep. zstep. lstep. step. if_cases K0; zify_cond K0; [exfalso; pjnorm_in K0; clear - K0 F0; lia| clear K0].
  zstep. step. do 16 ls. box_disj.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := omuc OX in pose proof (CREFA_munch RT AF E D C Σ _ m mm size OK CX HREF MUc WM) as HREF2 end.
  pose proof HREF2 as (ART2 & _ & _ & _ & DR2 & SBSH2 & PU2 & PRES2). unfold sb_sized in DR2, SBSH2, PU2, PRES2. cbn [sa_buf sa_size sa_cap sa_heap sa_k] in PRES2, SBSH2, PU2.
  assert (FRSeq : rt_frames RT Σ = (f, 1%nat) :: ci_fr0 C) by (rewrite FRx; exact EFR).
  destruct (af_frame_release RT AF Σ _ f 1%nat (ci_fr0 C) ART2 FRSeq) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  rewrite fs1 in FW. replace (f + 128 - 8) with (f + 120) in FW by (clear; lia). rewrite SP in FLW.
  lazymatch type of FR with rw_cells _ _ _ ?cs =>
  eapply evt_cut; [eapply (obj_epi2 (ci_q C) (ci_b C) f fl (pa_lo E) (ci_gp C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xs7 _ xs9 xs10 xs11 _ _ _ _ _
                             (ci_ra C) (ci_s0 C) (ci_s1 C) (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) cs F fc);
                   [exact F0| exact FLO| exact FL0| clear - FLW W1; lia| clear - LO; lia| clear - LB; lia| reflexivity| clear - OBQ; lia| clear - QT; unfold USTACK_TOP; lia
                   | clear - OBQ; lia| exact ST| exact FR0| exact FR| exact GAP| exact FS| exact FW| exact FLC| assumption]|] end.
  cbv beta. intros ms3 (m3 & RS3 & FC3 & MU3 & WM3 & MI3 & ST3 & FLC3).
  destruct (REL m3 MU3 WM3 FLC3) as (ART3 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3).
  apply evt_done. apply (aevt_switch RT PMc Σ Σ5 K ms3 AL3 AM3).
  revert FC3. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 ms3 (fun ms => ms_fcsr ms = fc -> aevt Σ5 K ms) RS3).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc) in FC5. subst fc5.

  assert (NFL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (ci_b C) a -> ~ (fl <= a < fl + 1)).
  { intros a Ha Hin. replace a with fl in Ha by (clear - Hin; lia).
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLW W1 LB; lia| apply NAC..]; [right; left| right; right; left| right; right; right; left| right; right; right; right]; exact H. }
  lazymatch type of MU3 with munch _ ?m2 _ =>
  assert (AG3 : forall P : Z -> Prop, (forall y, P y -> aclient (rt_live RT Σ) (rt_frames RT Σ) (ci_b C) y) -> agree_on P m2 m3)
    by (intros P HP a Ha; first [apply MU3| symmetry; apply MU3]; cbn [outside]; split; [exact (NFL _ (HP _ Ha))| exact Logic.I]) end.
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & B32 & F64 & FS' & B1 & B2 & D1 & D2 & FL & _).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FRSeq; right; exact IN4).
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
  apply (KFIN Σ5 (mkSbA buf size cap hp kk) q0 q1 q2 (wz fl) q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc m3 FRM ART3 MI3 ST3).
  -
    unfold SBINVA. cbn [sa_buf sa_size sa_cap sa_heap sa_k]. split; [| split; [clear - SZ SZ1; lia| split; [| split; [| split; [| exact PU2]]]]].
    + eapply rw_cells_agree_nw; [exact SV|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy.
      right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy B1 B2; lia].
    + destruct (stk_CB bsegs _ _ _ BUFS ltac:(clear - R1; lia)) as (bs & HBS). exists bs. replace (buf + cap - buf) with cap in HBS by (clear; lia).
      eapply rw_cells_agree_nw; [exact HBS|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply CLB. clear - Hy R1; lia.
    + destruct (stk_CB bsegs _ _ _ INLS ltac:(clear; lia)) as (bs & HBS). exists bs. replace (Z.to_nat (pa_SB E + 64 - pa_SB E)) with 64%nat in HBS by (clear; lia).
      eapply rw_cells_agree_nw; [exact HBS|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy.
      right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy B1 B2; lia].
    + eapply bytes_at_agree; [exact SBSH2|]. apply AG3. intros y Hy. rewrite repeat_length in Hy.
      right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. clear - Hy D1 D2 D8 B1 B2 B32 F64 EFS QF1. dlia.
  - eapply DOCREPA_agree; [exact DR2|]. apply AG3. intros y Hy.
    unfold docrep_rng in Hy. pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
    destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    + right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy D1 D2; lia].
    + right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. clear - Hy D1 D2 D8 F64 EFS QF1. dlia.
    + right; right; left. exists (pa_TAPE E), (pa_NT E). split; [rewrite LV; apply in_or_app; right; exact INT| clear - Hy TN; lia].
    + right; right; left. exists (pa_SBUF E), (pa_NS E). split; [rewrite LV; apply in_or_app; right; exact INS| clear - Hy SN; lia].
  - unfold sb_accA. cbn [sa_size]. clear - ACC; lia.
  - destruct PL0 as (LVE & _ & SPLO). split; [rewrite LV3; exact LVE| split; [rewrite FRS3; exact IN4| rewrite SP3; exact SPLO]].
  - exact FRS3.
  - rewrite SP3. exact SP.
  - rewrite CR3. unfold CCREDA in CR. clear - CR. lia.
  - intros a CA OUT. rewrite <- (PRES2 a CA OUT). first [apply MU3| symmetry; apply MU3]. cbn [outside]. split; [| exact Logic.I]. apply NFL.
    destruct (cc_fr E D C CX) as (top & EFR0).
    eapply aclient_mono; [exact CA| rewrite LV; intros x Hx; apply in_or_app; right; exact Hx| rewrite FRx, EFR0; intros x Hx; apply in_or_app; right; exact Hx| clear - BQ; lia].
Qed.

Lemma obj_tailA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (w : owA)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  ow168 w = wz SHDf -> ow192 w = wz SH64 -> ow216 w = wz (pa_SB E + 64) ->
  CERMA RT E C (OFRP w) Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st + 1 <= 41 * e + 6 * ci_c' C + 2 -> CCREDA RT E C Σ 0 st ->
  aevt Σ K (OST E C 0xbc97c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz SH72) xa5 xa6 xa7 (wz f) (wz f) xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX OX KFIN.
  intros Σ st m F fc w xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 E168 E192 E216 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  cbn [ow168 ow192 ow216] in E168, E192, E216. rewrite E168, E192, E216 in FR.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  step. zstep. shz_norm. zstep. if_true. zstep. shz_norm. zstep. if_true.

  step. step. step. zstep. zstep. replace (size + buf) with (buf + size) by (clear; lia). unbox FSB; unbox SHSB. step. box_disj.

  guards3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).

  zstep. pjnorm. zstep. zstep.
  obj_close HSM2 OX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
  - zstep. if_false. apply evt_done.
    eapply aevt_eq; [| eapply (obj_close_byteA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; try reflexivity; slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
    apply evt_done.
    eapply aevt_eq; [| eapply (obj_close_byteA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; try reflexivity; slia.
Qed.

Lemma obj_endA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (w : owA)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
  ow8 w = wz f -> ow16 w = wz f -> ow168 w = wz SHDf -> ow184 w = wz SH72 -> ow192 w = wz SH64 -> ow200 w = wz SH80 -> ow208 w = wz (pa_SB E + 80) ->
  ow216 w = wz (pa_SB E + 64) ->
  CERMA RT E C (OFRP w) Σ st m -> frm0 fc -> sa_size st + 1 <= 41 * e + 6 * ci_c' C + 2 -> CCREDA RT E C Σ 0 st ->
  aevt Σ K (OST E C 0xbc934 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz SH72) xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX OX KFIN.
  intros Σ st m F fc w xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 E8 E16 E168 E184 E192 E200 E208 E216 HSM FRM ACC CR.
  pose proof (cctx_out E D C OK CX) as OUTB. pose proof (SBINVA_cap_pos E m _ (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM)) as C64.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  cbn [ow8 ow16 ow168 ow184 ow192 ow200 ow208 ow216] in E8, E16, E168, E184, E192, E200, E208, E216. rewrite E8, E16, E168, E184, E192, E200, E208, E216 in FR.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  step. zstep. shz_norm. zstep. if_true. zstep. shz_norm. step. step. zstep. if_true.

  step. step. step. zstep. step.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - obj_close HSM2 OX. apply evt_done.
    eapply aevt_eq; [| eapply (obj_tailA Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; try reflexivity; slia.
  -
    zstep. pjnorm. step. step.
    obj_close HSM3 OX. apply evt_done.
    lazymatch type of HSM3 with CERMA _ _ _ ?FRP _ _ _ =>
    eapply (cont_growA RT AF PMc GROW E D C FRP Σ (mkSbA buf size cap hp kk) _ K (2 * cap) 0 0xbc978);
      [exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| clear; lia| clear; lia| reflexivity|] end.
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. clear - Kr ACC OUTB. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.

    apply (aevt_evt RT AF PMc MST). obj_open HSM4 OK CX OX. step. obj_close HSM5 OX. apply evt_done.
    eapply aevt_eq; [| eapply (obj_tailA Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F' fc)]; try eassumption; try pj_st_eq; try reflexivity.
    all: unfold sb_grownA; cbn [sa_size sa_cap]; clear - SZ C64 ACC; lia.
Qed.

Notation OWL x48 x72 x104 x136 x224 x232 :=
  (owK E C f (wz 4294967295) (wz 4294967297) (wz 67240448) x48 (wz (pa_DOC E + 8)) x72 (wz (pa_DOC E)) (wz 72057594037927935) (wz SHD8) x104
       (wz (f + 65)) (wz NOT65) (wz (f + 64)) x136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) x224 x232).
Definition obj_loop_stmtA (fu : nat) : Prop :=
  forall (x cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (x48 x72 x104 x136 x224 x232 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs9 xt3 xt4 xt5 xt6 : word),
    e - x <= Z.of_nat fu -> x < e -> tilesS FIELD x e n cx (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (OFRP (OWL x48 x72 x104 x136 x224 x232)) Σ st m -> frm0 fc -> sb_accA st x cx -> CCREDA RT E C Σ (2 * (e - x)) st ->
    aevt Σ K (OST E C 0xbcaf4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz SH72) xa5 xa6 xa7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) xs5 xs6 (wz x) xs9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                   xt3 xt4 xt5 xt6 F fc m).

Lemma obj_doneA : forall (cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
  tilesS FIELD e e n cx (ci_c' C) ->
  CERMA RT E C (OFRP (owK E C f x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232)) Σ st m -> frm0 fc -> sb_accA st e cx ->
  CCREDA RT E C Σ 0 st ->
  aevt Σ K (OST E C 0xbc934 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz SH72) xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX OX KFIN.
  intros until xt6. intros Ht HSM FRM ACC CR.
  pose proof (tilesS_diag _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ Ht) as EC. unfold sb_accA in ACC.
  eapply (obj_endA Σ st m F fc (owK E C f x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232));
    [reflexivity..| exact HSM| exact FRM| clear - ACC EC; lia| exact CR].
Qed.

Lemma obj_setupA : forall (fu : nat), obj_loop_stmtA fu ->
  forall (x cx n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (x24 x32 x40 x48 x72 x104 x112 x120 x136 x224 x232 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs9 xt3 xt4 xt5 xt6 : word),
    e - x <= Z.of_nat fu -> x < e -> tilesS FIELD x e n cx (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (OFRP (owK E C f x24 x32 x40 x48 (wz (pa_DOC E + 8)) x72 (wz (pa_DOC E)) (wz 72057594037927935) (wz SHD8) x104 x112 x120 (wz (f + 64)) x136
                          (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) x224 x232)) Σ st m ->
    frm0 fc -> sb_accA st x cx -> CCREDA RT E C Σ (2 * (e - x)) st ->
    aevt Σ K (OST E C 0xbcab8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz SH72) xa5 xa6 xa7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) xs5 xs6 (wz x) xs9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                   xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST OK CX OX.
  intros fu KL x cx n Σ st m F fc x24 x32 x40 x48 x72 x104 x112 x120 x136 x224 x232 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs9 xt3 xt4 xt5 xt6
         HF0 HXE Ht HX HCX HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.

  zstep. step. zstep. zstep. zstep. zstep. lstep. step. zstep. pjnorm. step. zstep. lstep. zstep. zstep. lstep.
  rewrite (ZBridge.zb_lxor_ones (f + 65)) in FR by (clear - F0 FLO LB OBQ QT; lia).
  obj_close HSM2 OX. apply evt_done.
  eapply aevt_eq; [| eapply (KL x cx n Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma obj_valueA : forall x x' cx cx', FIELD x x' cx cx' -> 1 <= x -> x' <= e ->
  0 <= pa_T E (x + 1) < 2^64 /\ ae_next (pa_T E (x + 1)) (x + 1) x' /\ x + 1 < x' /\ cx <= cx'.
Proof using OK CX.
  intros x x' cx cx' HF HX HXE. pose proof (ok_wfS E OK) as (_ & SN & _). pose proof (pa_n_32C E OK) as N32. pose proof (cc_e E D C CX) as (_ & _ & EN).
  destruct (obj_fieldA x x' cx cx' HF HX HXE) as (l & c1 & _ & _ & _ & HEL & LT & C5 & CUR & _).
  split; [eapply (elemS_word _ _ _ SN); [exact HEL| clear - HX; lia| clear - HXE EN N32; lia]|].
  split; [eapply (elemS_after _ _ _ SN); [exact HEL| clear - HX; lia| clear - HXE EN N32; lia]|].
  split; [exact LT| clear - C5 CUR; lia].
Qed.

Lemma obj_after_loopA : forall (fu : nat), obj_loop_stmtA fu ->
  forall (x x' cx cx' n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (y48 y72 y136 y224 y232 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 xt5 xt6 : word),
    e - x' <= Z.of_nat fu -> FIELD x x' cx cx' -> x' <= e -> tilesS FIELD x' e n cx' (ci_c' C) -> 2 <= x -> 0 <= cx ->
    CERMA RT E C (OFRP (OWL y48 y72 (wz (x + 1)) y136 y224 y232)) Σ st m -> frm0 fc -> sb_accA st x' cx' -> CCREDA RT E C Σ (2 * (e - x')) st ->
    aevt Σ K (OST E C 0xbd6d4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) xs5 (wz (x + 1)) (wz x) xs9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                   xt3 xt4 xt5 xt6 F fc m).
Proof using AF MST GROW OK CX OX KFIN.
  intros fu KL x x' cx cx' n Σ st m F fc y48 y72 y136 y224 y232 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xt3 xt4 xt5 xt6
         HF0 HF HXE Ht HX HCX HSM FRM ACC CR.
  pose proof (obj_valueA x x' cx cx' HF ltac:(clear - HX; lia) HXE) as (WR & CL & LT & CUR). unfold ae_next in CL.
  pose proof (cc_e E D C CX) as (I1 & IE & EN).
  assert (NEXT : x' <> e -> forall m1 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys5 ys6 ys9 yt3 yt4 yt5 yt6,
    CERMA RT E C (OFRP (OWL y48 y72 (wz (x + 1)) y136 y224 y232)) Σ st m1 ->
    aevt Σ K (OST E C 0xbcaf4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 (wz SH72) ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 ys6 (wz x') ys9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                   yt3 yt4 yt5 yt6 F fc m1)).
  { intros NE; intros. eapply (KL x' cx' n Σ st m1 F fc); try eassumption; clear - HF0 NE HXE LT HX CUR HCX; lia. }
  assert (DONE : x' = e -> forall m1 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys7 ys9 ys10 yt3 yt4 yt5 yt6,
    CERMA RT E C (OFRP (OWL y48 y72 (wz (x + 1)) y136 y224 y232)) Σ st m1 ->
    aevt Σ K (OST E C 0xbc934 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 (wz SH72) ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys7 ys9 ys10 (wz (pa_SB E)) yt3 yt4 yt5 yt6 F fc m1)).
  { intros EE; intros. rewrite EE in Ht, ACC. eapply (obj_doneA cx' n Σ st m1 F fc); try eassumption. eapply CCREDA_le; [exact CR| clear - EE; lia]. }
  set (w := pa_T E (x + 1)) in *. set (t := ttype w) in *.
  assert (TYR : 0 <= t < 256) by (unfold t, ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST).

  step. step. tref_call HSM HSM1 ltac:(clear - HX LT HXE EN; lia).
  let MUc := omuc OX in
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * (x + 1)) ltac:(clear - HX HXE LT EN; lia)) as RDW;
  pose proof (tape_read7_muC RT AF E D C OK CX _ _ _ _ (x + 1) HREF MUc WM ltac:(clear - HX HXE LT EN; lia) WR) as RD7. fold w in RD7. fold t in RD7.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. step. pjnorm. zstep. step. step. step.
  if_cases K1; zify_cond K1; pjnorm_in K1; aeK1 K1 t.
  -
    assert (EX : x' = x + 2) by (clear - CL K1; lia).
    zstep. rewrite <- EX. step. obj_close HSM2 OX. step.
    if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| step; apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
  -
    step. zstep. zstep. step.
    if_cases K2; zify_cond K2; pjnorm_in K2; aeK2 K2 t.
    +
      step. zstep. zstep. step.
      if_cases K3; zify_cond K3; pjnorm_in K3; aeK3 K3 t.
      * assert (EX : x' = x + 2) by (clear - CL K1 K2 K3; lia).
        zstep. rewrite <- EX. step. obj_close HSM2 OX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| step; apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
      *
        assert (EX : x' = Z.land w 4294967295) by (clear - CL K1 K2 K3; lia).
        step. step. obj_close HSM2 OX. tref_call HSM2 HSM3 ltac:(clear - HX LT HXE EN; lia).
        let MUc := omuc OX in
        pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * (x + 1)) ltac:(clear - HX HXE LT EN; lia)) as RDW';
        pose proof (tape_read_muC RT AF E D C OK CX _ _ _ _ (x + 1) HREF MUc WM ltac:(clear - HX HXE LT EN; lia)) as RDT. fold w in RDT.
        zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. step. step. zstep. rewrite <- EX. step. step. step.
        obj_close HSM4 OX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM4]| step; apply evt_done; eapply DONE; [clear - KE; lia| exact HSM4]].
    +
      assert (EX : x' = x + 3) by (clear - CL K1 K2; lia).
      zstep. rewrite <- EX. step. step. obj_close HSM2 OX. step.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| step; apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
Qed.

Lemma obj_loopA : forall fu, obj_loop_stmtA fu.
Proof using AF FDO MST GROW OK CX OX SER OKEY2 KFIN.
  induction fu as [|fu IH]; unfold obj_loop_stmtA;
    intros x cx n Σ st m F fc x48 x72 x104 x136 x224 x232 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs9 xt3 xt4 xt5 xt6
           HF0 HXE Ht HX HCX HSM FRM ACC CR; [exfalso; clear - HF0 HXE; lia|].
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2). pose proof (cctx_out E D C OK CX) as OUTB.
  pose proof (SBINVA_cap_pos E m _ (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM)) as C64.
  destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ Ht ltac:(clear - HXE; lia)) as (x' & cx' & HF & HXE' & Ht').
  destruct (obj_fieldA x x' cx cx' HF ltac:(clear - HX; lia) HXE') as (l & c1 & HTx & HSTR & EC1 & HEL & LT & C5 & CUR & L0).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ Ht') as (CUR' & _).
  unfold sb_accA in ACC.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys5 ys6 ys9 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (OFRP (OWL x48 x72 x104 x136 x224 x232)) Σ5 st5 m5 -> sa_size st5 = size -> size + 1 <= sa_cap st5 -> CCREDA RT E C Σ5 (2 * (e - x)) st5 ->
    aevt Σ5 K (OST E C 0xbcb34 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 (wz SH72) ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 ys6 (wz x) ys9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                    yt3 yt4 yt5 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 F5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys5 ys6 ys9 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_buf sa_cap] in ESZ, ROOM, CR5. subst size5.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM5 OK CX OX.
    let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

    step. zstep. shz_norm. zstep. if_true. zstep. shz_norm. step. zstep. if_true.
    step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

    guards3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as ACCB end.
    pose proof (buf_factsC RT AF E D C OK CX _ _ _ HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in ACCB, APB.
    out_facts APB (buf5 + size) A1 A2 A3 A4 A5; [clear - ROOM SZ; lia|].
    destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).

    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JOIN : forall ya1' ya2' ya3',
      evt bsegs (fun c5 => aevt Σ5 K c5)
          (OST E C 0xbcb94 yra yt0 yt1 yt2 (wz (buf5 + size)) ya1' ya2' ya3' (wz SH72) ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 (wz (pa_DOC E + 8)) (wz x) ys9
               (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F5 fc mm)) end.
    { intros ya1' ya2' ya3'. step. step. pj_store_done.
      obj_close HSM6 OX. apply evt_done. subst c1.
      eapply aevt_eq; [| eapply (OKEY2 E D C f K Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5) _ F5 fc x cx l x' cx' (size + 1) (2 * (e - x)))];
        try eassumption; try pj_st_eq;
        [clear - CUR' CC2; lia| cbn [sa_size]; clear; lia| clear - ACC; lia| clear - ACC OUTB C5 CUR CUR' CC2 HXE' LT HX; lia| clear - HXE'; lia|].
      intros Σ' st' m' F' fc' z48 z72 z136 z224 z232 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs5 zs9 zt3 zt4 zt5 zt6 HSM' FRM' ACC' CR'.
      eapply (obj_after_loopA fu IH x x' cx cx' (n - 1) Σ' st' m' F' fc'); try eassumption; [clear - HF0 LT; lia| eapply CCREDA_le; [exact CR'| clear; lia]]. }
    destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
    - zstep. if_false. apply JOIN.
    - zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
      if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply JOIN. }
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  step. zstep. shz_norm. zstep. if_true. zstep. shz_norm. zstep. if_true.
  step. step. step. zstep. step.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - obj_close HSM2 OX. apply evt_done. eapply (TAIL Σ (mkSbA buf size cap hp kk)); [exact HSM2| reflexivity| cbn [sa_cap]; clear - Kr; lia| exact CR].
  -
    zstep. pjnorm. step. step.
    obj_close HSM3 OX. apply evt_done.
    lazymatch type of HSM3 with CERMA _ _ _ ?FRP _ _ _ =>
    eapply (cont_growA RT AF PMc GROW E D C FRP Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (e - x)) 0xbcb30);
      [exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| clear - HXE; lia| clear; lia| reflexivity|] end.
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. clear - Kr ACC OUTB LT HXE' C5 CUR CUR' CC2 HX HCX EN. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.

    apply (aevt_evt RT AF PMc MST). obj_open HSM4 OK CX OX. step. obj_close HSM5 OX. apply evt_done.
    eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F'); [exact HSM5| reflexivity| unfold sb_grownA; cbn [sa_cap]; clear - SZ C64; lia| exact CR4].
Qed.

Lemma obj_after_firstA : forall (x x' cx cx' n : Z) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xt3 xt4 xt5 xt6 : word),
  FIELD x x' cx cx' -> x' <= e -> tilesS FIELD x' e n cx' (ci_c' C) -> 2 <= x -> 0 <= cx ->
  CERMA RT E C (OFRP (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935) (wz SHD8) y104 y112 y120
                           (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232)) Σ st m ->
  frm0 fc -> sb_accA st x' cx' -> CCREDA RT E C Σ (2 * (e - x')) st ->
  aevt Σ K (OST E C 0xbc88c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) (wz (x + 1)) xs6 xs7 xs9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                 xt3 xt4 xt5 xt6 F fc m).
Proof using AF FDO MST GROW OK CX OX SER OKEY2 KFIN.
  intros x x' cx cx' n Σ st m F fc y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xt3 xt4 xt5 xt6
         HF HXE Ht HX HCX HSM FRM ACC CR.
  pose proof (obj_valueA x x' cx cx' HF ltac:(clear - HX; lia) HXE) as (WR & CL & LT & CUR). unfold ae_next in CL.
  pose proof (cc_e E D C CX) as (I1 & IE & EN).
  assert (NEXT : x' <> e -> forall m1 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys5 ys6 ys9 yt3 yt4 yt5 yt6,
    CERMA RT E C (OFRP (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935) (wz SHD8) y104 y112 y120
                             (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232)) Σ st m1 ->
    aevt Σ K (OST E C 0xbcab8 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 (wz SH72) ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 ys6 (wz x') ys9 (wz PJ_NE_TAB_A) (wz (pa_SB E))
                   yt3 yt4 yt5 yt6 F fc m1)).
  { intros NE; intros. eapply (obj_setupA (Z.to_nat (e - x')) (obj_loopA _) x' cx' n Σ st m1 F fc); try eassumption; clear - NE HXE LT HX CUR HCX; lia. }
  assert (DONE : x' = e -> forall m1 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys7 ys9 ys10 yt3 yt4 yt5 yt6,
    CERMA RT E C (OFRP (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935) (wz SHD8) y104 y112 y120
                             (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232)) Σ st m1 ->
    aevt Σ K (OST E C 0xbc934 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 (wz SH72) ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys7 ys9 ys10 (wz (pa_SB E)) yt3 yt4 yt5 yt6 F fc m1)).
  { intros EE; intros. rewrite EE in Ht, ACC. eapply (obj_doneA cx' n Σ st m1 F fc); try eassumption. eapply CCREDA_le; [exact CR| clear - EE; lia]. }
  set (w := pa_T E (x + 1)) in *. set (t := ttype w) in *.
  assert (TYR : 0 <= t < 256) by (unfold t, ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST).

  step. step. tref_call HSM HSM1 ltac:(clear - HX LT HXE EN; lia).
  let MUc := omuc OX in
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * (x + 1)) ltac:(clear - HX HXE LT EN; lia)) as RDW;
  pose proof (tape_read7_muC RT AF E D C OK CX _ _ _ _ (x + 1) HREF MUc WM ltac:(clear - HX HXE LT EN; lia) WR) as RD7. fold w in RD7. fold t in RD7.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_true. step. pjnorm. zstep. step. step. step.
  if_cases K1; zify_cond K1; pjnorm_in K1; aeK1 K1 t.
  -
    assert (EX : x' = x - 1 + 3) by (clear - CL K1; lia).
    step. zstep. rewrite <- EX. step. obj_close HSM2 OX. step.
    if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
  -
    step. zstep. zstep. zstep. step.
    if_cases K2; zify_cond K2; pjnorm_in K2; aeK2 K2 t.
    +
      step. zstep. zstep. zstep. zstep. step.
      if_cases K3; zify_cond K3; pjnorm_in K3; aeK3 K3 t.
      * assert (EX : x' = x - 1 + 3) by (clear - CL K1 K2 K3; lia).
        step. zstep. rewrite <- EX. step. obj_close HSM2 OX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
      *
        assert (EX : x' = tnext w) by (rewrite <- land_low32; clear - CL K1 K2 K3; lia).
        obj_close HSM2 OX. step. step. tref_call HSM2 HSM3 ltac:(clear - HX LT HXE EN; lia).
        let MUc := omuc OX in
        pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * (x + 1)) ltac:(clear - HX HXE LT EN; lia)) as RDW';
        pose proof (tape_read4_muC RT AF E D C OK CX _ _ _ _ (x + 1) HREF MUc WM ltac:(clear - HX HXE LT EN; lia)) as RD4. fold w in RD4.
        zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_true. zstep. rewrite (zx32_tnext w WR), <- EX. step. step. step.
        obj_close HSM4 OX. step.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM4]| apply evt_done; eapply DONE; [clear - KE; lia| exact HSM4]].
    +
      assert (EX : x' = x - 1 + 4) by (clear - CL K1 K2; lia).
      step. zstep. rewrite <- EX. step. step. obj_close HSM2 OX. step.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply evt_done; eapply NEXT; [clear - KE; lia| exact HSM2]| apply evt_done; eapply DONE; [clear - KE; lia| exact HSM2]].
Qed.

Lemma obj_firstA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (x8 x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xt3 xt4 xt5 xt6 : word),
  CERMA RT E C (OFRP (mkOW x8 x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 (wz SHDf) x176 (wz SH72) (wz SH64)
                            (wz SH80) (wz (pa_SB E + 80)) (wz (pa_SB E + 64)) x224 x232 (wz f))) Σ st m -> frm0 fc ->
  1 <= sa_size st -> sa_size st <= 41 * (ci_i C - 1) + 6 * c0 + 4 -> CCREDA RT E C Σ (2 * (e - ci_i C) - 1) st ->
  aevt Σ K (OST E C 0xbbaac xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz f) (wz f) (wz SH72) xs6 (wz (pa_DOC E)) (wz (ci_i C)) xs10
                 (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF FDO MST GROW OK CX OX SER OKEY1 OKEY2 HTY HNX HT HC0 KFIN.
  intros Σ st m F fc x8 x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232
         xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2). pose proof (cctx_out E D C OK CX) as OUTB.
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT) as (LCC & _).
  assert (WR : 0 <= pa_T E (ci_i C) < 2^64) by (eapply ttype_range; [exact HTY| unfold t_obj; clear; lia]).
  pose proof HTY as HTY'. unfold SjTape.ty, t_obj in HTY'.
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  pose proof (buf_factsC RT AF E D C OK CX Σ _ _ HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  out_facts APB (buf + (size - 1)) A1 A2 A3 A4 A5; [clear - SZ1 SZ; lia|].

  step. step. pj_store_done. gok. zstep. rewrite (land7_mod8_0 (pa_DOC E) D8). gok.
  unbox FSB; unbox SHSB. step. step. box_disj.

  set (w := pa_T E (ci_i C)) in *.
  step. step. obj_close HSM1 OX. tref_call HSM1 HSM2 ltac:(clear - I1 IE EN; lia).
  let MUc := omuc OX in
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * ci_i C) ltac:(clear - I1 IE EN; lia)) as RDW;
  pose proof (tape_read7_muC RT AF E D C OK CX _ _ _ _ (ci_i C) HREF MUc WM ltac:(clear - I1 IE EN; lia) WR) as RD7. fold w in RD7. rewrite HTY' in RD7.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_true. step. pjnorm. zstep. zstep. step. step. step. step.
  if_cases K1; zify_cond K1; [exfalso; cbn in K1; clear - K1; lia| clear K1].

  step. zstep. zstep. zstep. step.
  if_cases K2; zify_cond K2; [clear K2| exfalso; cbn in K2; clear - K2; lia].

  step. zstep. zstep. zstep. zstep. step. step.
  if_cases K3; zify_cond K3; [exfalso; cbn in K3; clear - K3; lia| clear K3].

  obj_close HSM3 OX. step. step. tref_call HSM3 HSM4 ltac:(clear - I1 IE EN; lia).
  let MUc := omuc OX in
  pose proof (shz_tape_muC RT AF E D C OK CX _ _ _ _ HREF MUc WM (pa_TAPE E + 8 * ci_i C) ltac:(clear - I1 IE EN; lia)) as RDW';
  pose proof (tape_read4_muC RT AF E D C OK CX _ _ _ _ (ci_i C) HREF MUc WM ltac:(clear - I1 IE EN; lia)) as RD4. fold w in RD4.
  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_true. zstep. rewrite (zx32_tnext w WR), HNX. step. zstep.
  replace (e + 1 + -1) with e by (clear; lia).
  unbox FSB; unbox SHSB. step. box_disj.
  obj_close HSM5 OX. step.
  if_cases KE; zify_cond KE; pjnorm_in KE.
  -
    apply evt_done. rewrite <- KE in HT.
    pose proof (tilesS_diag _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ HT) as EC.
    eapply aevt_eq; [| eapply (obj_endA Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; try reflexivity;
      [cbn [sa_size]; clear - ACC KE EC LCC CC1; lia| eapply CCREDA_le; [exact CR| clear - IE; lia]].
  - destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT ltac:(clear - KE; lia)) as (x' & cx' & HF & HXE' & Ht').
    destruct (obj_fieldA (ci_i C + 1) x' c0 cx' HF ltac:(clear - I1; lia) HXE') as (l & c1 & HTx & HSTR & EC1 & HEL & LT & C5 & CUR & L0).
    pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ Ht') as (CUR' & _).
    apply evt_done. subst c1.
    eapply aevt_eq; [| eapply (OKEY1 E D C f K Σ (mkSbA buf size cap hp kk) _ F fc (ci_i C + 1) c0 l x' cx' size (2 * (e - ci_i C) - 1))];
      try eassumption; try pj_st_eq;
      [clear - I1; lia| clear - CUR' CC2; lia| cbn [sa_size]; clear; lia| clear - ACC; lia| clear - ACC OUTB C5 CUR CUR' CC2 HXE' LT; lia| clear - HXE'; lia|].
    intros Σ' st' m' F' fc' y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs6 zs7 zs9 zt3 zt4 zt5 zt6
           HSM' FRM' ACC' CR'.
    eapply (obj_after_firstA (ci_i C + 1) x' c0 cx' (n0 - 1) Σ' st' m' F' fc'); try eassumption; [clear - I1; lia| eapply CCREDA_le; [exact CR'| clear; lia]].
Qed.

Lemma obj_openbA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (w : owA)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xt3 xt4 xt5 xt6 : word),
  ow168 w = wz SHDf -> ow184 w = wz SH72 -> ow200 w = wz SH80 -> ow208 w = wz (pa_SB E + 80) -> ow240 w = wz f ->
  CERMA RT E C (OFRP w) Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= 41 * (ci_i C - 1) + 6 * c0 + 3 -> CCREDA RT E C Σ (2 * (e - ci_i C) - 1) st ->
  aevt Σ K (OST E C 0xbba30 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz f) (wz f) (wz SH72) xs6 (wz (pa_DOC E)) (wz (ci_i C)) xs10 (wz (pa_SB E))
                 xt3 xt4 xt5 xt6 F fc m).
Proof using AF FDO MST GROW OK CX OX SER OKEY1 OKEY2 HTY HNX HT HC0 KFIN.
  intros Σ st m F fc w xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xt3 xt4 xt5 xt6 E168 E184 E200 E208 E240 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  cbn [ow168 ow184 ow200 ow208 ow240] in E168, E184, E200, E208, E240. rewrite E168, E184, E200, E208, E240 in FR.

  zstep. step. zstep. pjnorm. zstep. step.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. shz_norm. zstep. if_true. zstep. shz_norm. zstep. if_true.
  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  guards3j.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).

  zstep. pjnorm. zstep. zstep.
  obj_close HSM2 OX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)].
  -
    zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (obj_firstA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc]. step.
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    step. apply evt_done.
    eapply aevt_eq; [| eapply (obj_firstA Σ (mkSbA buf (size + 1) cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma obj_headA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32) (w : owA)
    (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xt3 xt4 xt5 xt6 : word),
  ow168 w = wz SHDf -> ow200 w = wz SH80 -> ow208 w = wz (pa_SB E + 80) ->
  CERMA RT E C (OFRP w) Σ st m -> frm0 fc -> sa_size st <= 41 * (ci_i C - 1) + 6 * c0 + 3 -> CCREDA RT E C Σ (2 * (e - ci_i C) - 1) st ->
  aevt Σ K (MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 (wz (ci_q C)) (wz (ci_b C)) xa0 (wz SH80) xa2 xa3 xa4 xa5 xa6 xa7
                    (wz f) xs3 (wz f) xs5 xs6 (wz (pa_DOC E)) (wz 2147450880) (wz (ci_i C)) xs10 (wz (pa_SB E)) xt3 xt4 xt5 xt6)
               F (wz 0xbb9e4) fc None m (seg_rom bsegs)).
Proof using AF FDO MST GROW OK CX OX SER OKEY1 OKEY2 HTY HNX HT HC0 KFIN.
  intros Σ st m F fc w xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xt3 xt4 xt5 xt6 E168 E200 E208 HSM FRM ACC CR.
  pose proof (cctx_out E D C OK CX) as OUTB. pose proof (SBINVA_cap_pos E m _ (SBINVA_of_CERMA RT E D C _ Σ _ m OK CX HSM)) as C64.
  pose proof (cc_e E D C CX) as (I1 & IE & EN). pose proof (cc_c' E D C CX) as (CC1 & CC2).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT) as (LCC & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.
  cbn [ow168 ow200 ow208] in E168, E200, E208. rewrite E168, E200, E208 in FR.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. clear SHZ.

  zstep. shz_norm. step. zstep. if_true. zstep. zstep. pjnorm. zstep.
  let MUc := omuc OX in pose proof (shz_sb_muC RT AF E D C OK CX Σ _ _ _ HREF MUc WM) as SHZ.
  pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  zstep. shz_norm. zstep. if_true. step. step. zstep. step. step.
  if_cases Kr; zify_cond Kr; pjnorm_in Kr.
  - obj_close HSM2 OX. apply evt_done.
    eapply aevt_eq; [| eapply (obj_openbA Σ (mkSbA buf size cap hp kk) _ F fc)]; try eassumption; try pj_st_eq; try reflexivity.
    all: cbn [sa_size sa_cap]; clear - Kr ACC; lia.
  -
    zstep. pjnorm. step. step.
    obj_close HSM3 OX. apply evt_done.
    lazymatch type of HSM3 with CERMA _ _ _ ?FRP _ _ _ =>
    eapply (cont_growA RT AF PMc GROW E D C FRP Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (e - ci_i C) - 1) 0xbba2c);
      [exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| clear - IE; lia| clear; lia| reflexivity|] end.
    { eapply (cont_req_ok2A RT E D C _ Σ _ _ OK CX HSM3). cbn [sa_cap]. clear - Kr ACC OUTB I1 IE LCC CC2 HC0. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.

    apply (aevt_evt RT AF PMc MST). obj_open HSM4 OK CX OX. step. obj_close HSM5 OX. apply evt_done.
    eapply aevt_eq; [| eapply (obj_openbA Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)) m' F' fc)]; try eassumption; try pj_st_eq; try reflexivity.
    all: unfold sb_grownA; cbn [sa_size sa_cap]; clear - SZ C64 ACC; lia.
Qed.
End Obj.

Theorem obj_proofA : forall RT, art_facts RT -> stack_malloc1z_contract RT -> forall PMc, grow_cpsA RT PMc -> okey1_stmtA RT PMc -> okey2_stmtA RT PMc ->
  forall D, ser_cpsA RT PMc D -> cont_cpsA RT PMc true D.
Proof.
  intros RT AF SM1Z PMc GROW OKEY1 OKEY2 D SER. unfold cont_cpsA.
  intros Σ K E st i e n c c' q ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         FDO MST OK PL INV DR HTY HNX HTE HT HI HJ HC HC' ACC ART0 MI0 ST0 LOQ QT Q16 FRM FR3 FRL LL CR HK.
  pose proof (ok_len E OK) as LEN. pose proof (ok_lo E OK) as LOW. pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _).
  pose proof (ok_sb E OK) as (SB32 & B1 & B2). pose proof (ok_doc E OK) as (D8 & D1 & D2). pose proof (ok_frame E OK) as (F64' & FSEG & FL). pose proof (ok_apart E OK) as AP.
  pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN' & _ & _ & INS).
  pose proof PL as (LVE & INF4 & SPLO).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) true D) _ _ _ _ _ HT) as (LCC & LCC2).
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (pa_n_32C E OK) as N32.
  unfold cont_needA, ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS64 & QF1).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (obj_pro1 q (pa_lo E) (pa_SB E) (pa_DOC E) i ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0);
                   [clear - LOQ; lia| clear - LOW; lia| unfold USTACK_TOP; exact QT| exact Q16| exact CC0| exact MI0]|].
  cbv beta. intros ms1 (m1 & dd & a1' & a2' & DD & B32 & -> & MU1 & WM1 & MI1 & ST1 & FS1). apply evt_done.
  set (b := q - 352 - dd) in *.
  assert (LOB : pa_lo E + ser_needA D <= b) by (unfold ser_needA, PJ_TC_STACK_A, RT_STACK; unfold b; clear - LOQ DD; lia).
  assert (LB : pa_lo E + 65936 <= b) by (unfold b; clear - LOQ DD; lia).
  assert (EU : bv_unsigned (wz b) = b) by (apply unsigned_lit; clear - LB LOW QT DD; unfold b; lia).
  assert (CSEP : forall sp a, aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> sp <= a \/ a < pa_lo E).
  { intros sp a Ha. destruct (aclient_split_c RT AF Σ m sp a ART0 Ha) as [H|H]; [left; exact H| right; clear - H SPLO; lia]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 352) ART0); [clear - SPLO LOQ; lia| | exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. intros Hin. apply Ha. left. clear - Hin QT. unfold USTACK_TOP. lia. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. destruct (CSEP _ _ Ha); clear - H LOQ; lia. }
  destruct (stk_split bsegs m1 _ b _ ST1 ltac:(unfold b; clear - LOQ DD; lia)) as [ST1l ST1h].

  eapply (aevt_smalloc1z RT SM1Z PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pa_lo E));
    [reflexivity| clear - FRL; unfold FRAMES_MAX2, FRAMES_TOT in *; lia| clear - CR PSI0 LIE; lia| exact ART1| exact MI1| | intros HN; exfalso; rewrite HN in INF4; exact INF4|].
  { unfold call_ok. rewrite EU. split; [exact ST1l|]. split; [exact SPLO|]. split; [clear - LB; unfold RT_STACK; lia|].
    split; [unfold b, USTACK_TOP; clear - QT DD; lia| clear - B32; unfold b; Z.div_mod_to_equations; lia]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS SHZ2 FRS1 LV1 SP1 CR1 F0 F64 FTOP.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xbb930) by (clear; lia).
  rewrite fs1 in WRF, WRS, FTOP. change (128 - 8) with 120 in WRF. change (128 / 8) with 16 in WRS.

  assert (INf : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INF1 : In (pa_F E, pa_kF E) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF4).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INf) as (_ & FWIN & _ & F1CH). rewrite fs1, SP1 in FWIN. rewrite fs1 in F1CH.
  assert (FLO : f + 128 <= pa_lo E) by (clear - FWIN SPLO; lia).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 INf) as [_ FSEGf].
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 INf) as [F1SL F1SF]. rewrite fs1 in F1SL, F1SF.
  pose proof (af_fshadow_apart RT AF Σ1 m2 (pa_F E) (pa_kF E) ART2 INF1) as [F4SL F4SF].
  pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat (pa_F E) (pa_kF E) [] (rt_frames RT Σ) ART2 FRS1 INF4) as FF. rewrite fs1 in FF.
  assert (Ef : 8 * (f / 8) = f) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (EF : 8 * (pa_F E / 8) = pa_F E) by (clear - F64'; Z.div_mod_to_equations; lia).
  assert (E128 : (f + 128) / 8 = f / 8 + 16) by (clear - Ef; Z.div_mod_to_equations; lia).
  assert (EFS : (pa_F E + fs_size (pa_kF E)) / 8 = pa_F E / 8 + fs_size (pa_kF E) / 8) by (rewrite EFS64; clear - EF; Z.div_mod_to_equations; lia).
  assert (SFL : f / 8 + 2147450880 + 16 <= pa_lo E) by (clear - Ef FLO LOW F0; lia).

  assert (FRESH : forall sp a, pa_lo E <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (f <= a < f + 128) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
  { intros sp a Hsp Ha. pose proof (newframe_apartI RT AF Σ Σ1 m2 f 1%nat sp a ART2 FRS1 ltac:(rewrite LV1; intros x Hx; exact Hx) SP1 ltac:(clear - Hsp SPLO; lia) Ha) as [N1 N2].
    rewrite fs1 in N1, N2. unfold shad, SHB in N2. rewrite E128 in N2. split; [exact N1| clear - N2; lia]. }

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH2). change (Z.to_nat 24) with 24%nat in FH2.
  pose proof (wr_at_stk m2 (f + 24) 96 (wr_at_sub m2 f 120 (f + 24) 96 WRF ltac:(lia) ltac:(lia) ltac:(lia))) as F1S2.
  replace (f + 24 + 96) with (f + 120) in F1S2 by lia.
  unfold shad, SHB in SHZ2.

  assert (AG12 : forall (P : Z -> Prop), (forall y, P y -> b <= y < q) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). clear - H QT. unfold USTACK_TOP. lia. }
  assert (STb2 : stk bsegs m2 b (q - 104)) by (eapply stk_agree_nw; [exact ST1h|]; apply AG12; intros y Hy; clear - Hy; lia).
  assert (FS2 : rw_cells bsegs m2 (q - 104) (osavedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    by (eapply rw_cells_agree_nw; [exact FS1|]; apply AG12; intros y Hy; unfold osavedA in Hy; cbn [cells_size csize Nat.add] in Hy; unfold b; clear - Hy DD; lia).
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (PRES1 a Ha). apply PRES2. eapply aclient_mono; [exact Ha| intros x Hx; exact Hx| intros x Hx; exact Hx| unfold b; clear - DD; lia]. }
  clear PRES1 PRES2 ST1 ST1l ST1h FS1 MU1 WM1 MI1 ART1 WRF WRS.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (obj_pro2 q b f (pa_lo E) (pa_SB E) (pa_DOC E) i gp v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s10 v3 v4 v5 v6 jh F1 fc m2 F0 FLO SFL Ef);
                   [| clear - LOW; lia| clear - LB; lia| unfold b; clear - DD; lia| unfold USTACK_TOP; exact QT| clear - FSEG B1; ul| clear - B2 FL; lia
                   | clear - HI LIE HJ N32; lia| exact STb2| exact FH2| exact F1S2| exact SHZ2| exact MI2]|].
  { destruct (F1SF f 1%nat INf) as [H|H]; unfold shad, SHB in H; rewrite ?fs1, ?E128 in H; [left| right]; clear - H; lia. }
  cbv beta. intros ms3 (m3 & w & ra' & t0' & a0' & a2'' & a4' & a5' & a6' & -> & MU3 & WM3 & MI3 & E208 & E168 & E200 & FR0w & FRw & GAPw & FHw & F1Sw & SHFw).
  apply evt_done.

  set (C := mkCI q b i e c' (rt_credit RT Σ - 2 * (e - i) - pj_psi (pa_len E) st) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 ((f, 1%nat) :: rt_frames RT Σ) (rt_frames RT Σ) (obj_R_ f) (rt_sp0 RT Σ) m).
  assert (CX : cctxA E D C).
  { constructor; cbn [C ci_q ci_b ci_i ci_e ci_c' ci_R ci_fr ci_fr0 ci_R_ ci_sp0].
    - clear - B32. Z.div_mod_to_equations. lia.
    - unfold b. clear - DD. lia.
    - exact LOB.
    - unfold USTACK_TOP. exact QT.
    - split; [exact SPLO| exact SPW].
    - clear - HI LIE HJ; lia.
    - clear - HC HC' LCC; lia.
    - clear - CR PSI0 LIE; lia.
    - exists [(f, 1%nat)]. reflexivity.
    - exact INF4.
    - cbn [fcount Nat.eqb]. exact FR3.
    - cbn [length]. clear - FRL. lia.
    - exact LL.
    - intros a Ha. unfold obj_R_ in Ha. apply in_R_cons in Ha. rewrite in_R_cons in Ha.
      assert (Ra : f <= a < f + 120 \/ f / 8 + 2147450880 <= a < f / 8 + 2147450896).
      { destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha| right; exact Ha| destruct Ha as (lo & hi & F0' & _); exfalso; exact F0']. }
      clear Ha. split; [| split; [| split]].
      + destruct Ra as [Ra|Ra].
        * left. exists f, 1%nat. split; [left; reflexivity| rewrite fs1; clear - Ra; lia].
        * right. exists f, 1%nat. split; [left; reflexivity| unfold shad, SHB; rewrite fs1, E128; clear - Ra; lia].
      + intros (g & k & IN & R). destruct (FRESH (pa_lo E) a ltac:(clear; lia) ltac:(right; right; right; left; exists g, k; split; [exact IN| exact R])) as [N1 N2].
        clear - Ra N1 N2. lia.
      + intros (g & k & IN & R). destruct (FRESH (pa_lo E) a ltac:(clear; lia) ltac:(right; right; right; right; exists g, k; split; [exact IN| exact R])) as [N1 N2].
        clear - Ra N1 N2. lia.
      + clear - Ra FLO SFL. lia. }
  assert (OX : octxA E C f).
  { constructor; cbn [C ci_q ci_b ci_fr ci_fr0 ci_R_].
    - reflexivity.
    - reflexivity.
    - unfold b. clear - DD. lia.
    - exact B32.
    - split; [exact F0|]. split; [exact F64|]. split; [exact FSEGf| exact FLO].
    - clear - FF. lia.
    - pose proof (F1SF f 1%nat INf) as H. unfold shad, SHB in H. rewrite fs1, E128 in H. clear - H. lia.
    - pose proof (F1SF (pa_F E) (pa_kF E) INF1) as H. unfold shad, SHB in H. rewrite E128 in H. clear - H. lia.
    - pose proof (F4SF f 1%nat INf) as H. unfold shad, SHB in H. rewrite fs1 in H. clear - H. lia. }

  assert (CL3 : forall y, (b <= y < b + 248) \/ (f <= y < f + 24) \/ (f / 8 + 2147450880 <= y < f / 8 + 2147450896) ->
                aclient (rt_live RT Σ1) (rt_frames RT Σ1) b y).
  { intros y [Hy|[Hy|Hy]].
    - left. clear - Hy QT LB DD. unfold b, USTACK_TOP in *. lia.
    - right; right; right; left. exists f, 1%nat. split; [exact INf| rewrite fs1; clear - Hy; lia].
    - right; right; right; right. exists f, 1%nat. split; [exact INf| unfold shad, SHB; rewrite fs1, E128; clear - Hy; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 b ART2); [rewrite SP1; clear - SPLO LB; lia| | exact WM3].
    intros a Ha. apply MU3. cbn [outside]. repeat split; try exact Logic.I; intros Hin; apply Ha; apply CL3; clear - Hin; lia. }
  assert (AG03 : forall (P : Z -> Prop), (forall y, P y -> aclient (rt_live RT Σ) (rt_frames RT Σ) q y) -> agree_on P m m3).
  { intros P HP a Ha. pose proof (HP _ Ha) as CA. rewrite <- (PRES2' a CA). apply MU3.
    destruct (FRESH q _ ltac:(clear - LOQ; lia) CA) as [N1 N2]. destruct (CSEP _ _ CA) as [H|H]; cbn [outside]; unfold b; clear - H N1 N2 LOQ DD; lia. }
  assert (INV3 : SBINVA E m3 st).
  { eapply SBINVA_agree; [exact INV|]. apply AG03. intros y Hy. unfold sbinv_rng in Hy. destruct Hy as [Hy|[Hy|Hy]].
    - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy B1 B2; lia].
    - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. rewrite EFS.
      pose proof INV as (_ & _ & _ & _ & _ & _ & HB). clear - Hy EF EFS64 QF1 B1 B2 SB32. Z.div_mod_to_equations. lia.
    - pose proof INV as (_ & SZ & _ & _ & _ & _ & HB). destruct (sa_heap st) eqn:HP.
      + right; right; left. exists (sa_buf st), (sa_cap st). split; [rewrite LVE; unfold sbchunkA; rewrite HP; left; reflexivity| clear - Hy; lia].
      + destruct HB as (EB & EC & _). right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy EB EC B1 B2; lia]. }
  assert (DR3 : DOCREPA E m3).
  { eapply DOCREPA_agree; [exact DR|]. apply AG03. intros y Hy. unfold docrep_rng in Hy. destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy D1 D2; lia].
    - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. rewrite EFS.
      clear - Hy EF EFS64 QF1 D1 D2 D8. Z.div_mod_to_equations. lia.
    - right; right; left. exists (pa_TAPE E), (pa_NT E). split; [rewrite LVE; apply in_or_app; right; exact INT| clear - Hy TN; lia].
    - right; right; left. exists (pa_SBUF E), (pa_NS E). split; [rewrite LVE; apply in_or_app; right; exact INS| clear - Hy SN'; lia]. }
  pose proof INV3 as (SV3 & SZ3 & (bs3 & BUF3) & (ji3 & INL3) & SBSH3 & PK3 & PH3).
  assert (HSM : CERMA RT E C (obj_frp E C f w obj_shpatA) Σ1 st m3).
  { unfold C. split.
    - unfold CREFA. cbn [ci_fr ci_sp0 ci_q ci_m0 ci_fr0]. split; [exact ART3|]. split; [rewrite LV1; exact LVE|]. split; [exact FRS1|]. split; [exact SP1|].
      split; [exact DR3|]. split; [exact SBSH3|]. split; [exact (conj PK3 PH3)|].
      intros a Ha Ho. apply (AG03 (fun y => aclient (pa_L E) (rt_frames RT Σ) q y)); [| exact Ha].
      intros y Hy. eapply aclient_mono; [exact Hy| rewrite LVE; intros x Hx; apply in_or_app; right; exact Hx| intros x Hx; exact Hx| clear; lia].
    - unfold CCURA. cbn [ci_b ci_q].
      split. { unfold obj_frp. cbn [ci_b ci_q ci_ra ci_s0 ci_s1 ci_s2 ci_s3 ci_s4 ci_s5 ci_s6 ci_s7 ci_s8 ci_s9 ci_s10 ci_s11].
               split; [exact FR0w|]. split; [exact FRw|]. split; [exact GAPw|].
               split. { unfold co_savedA. cbn [ci_ra ci_s0 ci_s1 ci_s2 ci_s3 ci_s4 ci_s5 ci_s6 ci_s7 ci_s8 ci_s9 ci_s10 ci_s11].
                        eapply rw_cells_agree_nw; [exact FS2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. unfold osavedA in Hy. cbn [cells_size csize Nat.add] in Hy.
                        cbn [outside]. unfold b. clear - Hy DD FLO SFL LOQ. repeat split; try exact Logic.I; lia. }
               split; [exact FHw|]. split; [exact F1Sw|]. split; [exact SHFw| reflexivity]. }
      split; [exact SV3|]. split; [exact SZ3|].
      split. { pose proof (stk_of_rw_cells bsegs _ _ _ BUF3) as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by (clear - SZ3; lia). exact S. }
      split. { pose proof (stk_of_rw_cells bsegs _ _ _ INL3) as S. cbn [cells_size csize Nat.add] in S. exact S. }
      split; [exact MI3|].
      eapply stk_agree_nw; [exact ST2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbv beta in Hy. cbn [outside]. clear - Hy FLO SFL.
      repeat split; try exact Logic.I; lia. }

  assert (KFIN : forall (Σ' : rts RT) (st' : sbA) (t0' t1' t2' a0' a1' a2'' a3'' a4'' a5'' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) (ci_q C) ->
    SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' (ci_e C + 1) (ci_c' C) -> pa_live RT Σ' E st' ->
    rt_frames RT Σ' = ci_fr0 C -> rt_sp0 RT Σ' = ci_sp0 C -> ci_R C + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
    rt_pres_fp (pa_L E) (ci_fr0 C) (ci_q C) [(pa_SB E, pa_SB E + 88)] (ci_m0 C) m' ->
    aevt RT PMc Σ' K (MS (mkR (ci_ra C) (wz (ci_q C)) (ci_gp C) (wz TPV_A) t0' t1' t2' (ci_s0 C) (ci_s1 C) a0' a1' a2'' a3'' a4'' a5'' a6' a7'
                           (ci_s2 C) (ci_s3 C) (ci_s4 C) (ci_s5 C) (ci_s6 C) (ci_s7 C) (ci_s8 C) (ci_s9 C) (ci_s10 C) (ci_s11 C) t3' t4' t5' t6')
                      F' (ret_pc (ci_ra C)) fc' None m' (seg_rom bsegs))).
  { unfold C. cbn [ci_q ci_ra ci_gp ci_s0 ci_s1 ci_s2 ci_s3 ci_s4 ci_s5 ci_s6 ci_s7 ci_s8 ci_s9 ci_s10 ci_s11 ci_R ci_fr0 ci_sp0 ci_m0 ci_e ci_c'].
    intros Σ' st' y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FRS' SP' CR' PRES'.
    apply (HK Σ' st'); assumption. }
  eapply aevt_eq; [| eapply (obj_headA RT AF PMc FDO MST GROW E D C f K OK CX OX SER OKEY1 OKEY2 n c HTY HNX HT HC KFIN Σ1 st m3 F1 fc w)].
  all: try (unfold C; cbn [ci_b ci_q ci_gp ci_i]; pj_st_eq).
  all: try exact E168; try exact E200; try exact E208; try exact HSM; try exact FRM; try exact ACC.
  unfold CCREDA, C; cbn [ci_R ci_e ci_i]; rewrite CR1; clear; lia.
Qed.
