(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_defsA Atp_h_defsA Atp_h_vkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma annshrink_walk1 : forall (usp V b e c k lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 <= c < 2^63 -> 0 <= k < 2^40 -> b + 16 * k < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a4' a5' : word),
      ms = entry_st (Z_to_bv 64 0xb4f00) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 c)
             (Z_to_bv 64 (b + 16 * k)) (Z_to_bv 64 e) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
      /\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells asegs m1 V (vcells b e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNSHRINK m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 K0 BK (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNSHRINK, e_annotate, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  replace (Z.shiftl k 4) with (16 * k) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| exact VC].
Qed.

Lemma annshrink_walk2 : forall (usp lo : Z) (gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  stk asegs m lo (usp + -16) -> lo <= usp - 16 -> usp < 2^63 ->
  rw_cells asegs m (usp + -16) [C8 s0c; C8 rac] -> mem_inv asegs m ->
  evt asegs (fun ms => ret_st rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m ms /\ ms_fcsr ms = fc /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4f00) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4f00) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO SPH FR MI. pose proof ST as (STa & STb & _).
  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]].
Qed.

Definition des_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Lemma des_walk1 : forall (usp C V b e c lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> 0x6ca000 <= lo -> usp <= C -> C + 8 < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> b <= e < 2^63 -> 0 <= c < 2^63 -> (e - b) mod 16 = 0 ->
  shb_consts m -> x_shz [(usp - 32, usp); (V + 8, V + 16)] m C 8 -> v_shz [(usp - 32, usp); (V + 8, V + 16)] m V ->
  rw_cells asegs m C [C8 (Z_to_bv 64 V)] -> rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a3' : word),
      ms = entry_st (Z_to_bv 64 0xb9220) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) (Z_to_bv 64 V) (Z_to_bv 64 ((e - b) / 16))
             a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNSHRINK m1
      /\ munch [(usp - 32, usp); (V + 8, V + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
      /\ rw_cells asegs m1 (usp + -32) (des_frame s2 s1 s0 ra)
      /\ rw_cells asegs m1 C [C8 (Z_to_bv 64 V)] /\ rw_cells asegs m1 V (vcells b b c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_DESTROY m).
Proof.
  intros until m. intros ST LO GLO UC CH V0 VLO B0 E0 C0 EB16 (G1 & G2) SHX SHZ RC VC MI.
  unfold entry_st, ATPA_DESTROY, VB_ANNSHRINK, vcells, des_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (V + 8, V + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  zstep. zstep. rewrite shr3_div. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHX mm MU' WM' C ltac:(lia)) as RDC; pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. ls. zstep. zstep. zstep.
  rewrite (a_signed_small (e + - b)) by lia. rewrite (Z.shiftr_div_pow2 (e + - b) 4) by lia. change (2 ^ 4) with 16. replace (e + - b) with (e - b) by lia.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; eassumption.
Qed.

Lemma des_walk2 : forall (usp C V lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (fr : list cell) F fc (m : mem),
  0 <= C -> C + 8 < 2^63 -> x_shz [(usp - 32, usp)] m C 8 -> rw_cells asegs m C [C8 (Z_to_bv 64 V)] -> mem_inv asegs m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 0xb9230) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 VB_ANNDEL) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 0xb9220) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb9220) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros UC CH SHX RC MI. unfold VB_ANNDEL.
  pose proof (SHX m (munch_refl _ m) (wmono_refl asegs m) C ltac:(lia)) as RDC.
  assert (ES : bv_unsigned (Z_to_bv 64 (C / 8 + 2147450880)) = C / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma des_walk3 : forall (usp C V b c lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s2c s1c s0c rac : word) (ce : cell) F fc (m : mem),
  stk asegs m lo (usp + -32) -> lo <= usp - 32 -> usp < 2^63 -> 0 <= C -> C + 8 < 2^63 -> 0 < V -> V + 24 < 2^63 -> 0 < b < 2^63 -> b <= c < 2^63 ->
  x_shz [(usp - 32, usp)] m C 8 -> v_shz [(usp - 32, usp)] m V ->
  rw_cells asegs m C [C8 (Z_to_bv 64 V)] -> rw_cells asegs m V [C8 (Z_to_bv 64 b); ce; C8 (Z_to_bv 64 c)] -> csize ce = 8%nat ->
  rw_cells asegs m (usp + -32) (des_frame s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a2' : word),
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3 a4 a5 a6 a7
             s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m
      /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb9230) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb9230) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO SPH UC CH V0 VH B0 C0 SHX SHZ RC VC CE FR MI. unfold e_del, des_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (SHX m (munch_refl _ m) (wmono_refl asegs m) C ltac:(lia)) as RDC.
  pose proof (SHZ m (munch_refl _ m) (wmono_refl asegs m) V ltac:(lia)) as RD0. pose proof (SHZ m (munch_refl _ m) (wmono_refl asegs m) (V + 16) ltac:(lia)) as RD2.
  assert (ES : bv_unsigned (Z_to_bv 64 (C / 8 + 2147450880)) = C / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (VC2 : rw_cells asegs m (V + 16) [C8 (Z_to_bv 64 c)]).
  { change ([C8 (Z_to_bv 64 b); ce; C8 (Z_to_bv 64 c)]) with ([C8 (Z_to_bv 64 b); ce] ++ [C8 (Z_to_bv 64 c)]) in VC.
    apply Sj_stage1_kit.rw_cells_app in VC. destruct VC as [_ X]. cbn [cells_size Nat.add] in X. rewrite CE in X. cbn [csize Nat.add] in X.
    replace (V + Z.of_nat 16) with (V + 16) in X by lia. exact X. }
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep. zstep.
  apply evt_done. eexists. split; [unfold entry_st; cbv delta [mkR]; replace (c + - b) with (c - b) by lia; reflexivity| exact ST].
Qed.

Section Destroy.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold ATPA_DESTROY_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma annshrink_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n v' k : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m V (vcells b (b + v') (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = l1 ++ ann_block b n (16 * k) ++ L0 -> Forall (fun e => fst e <> b) l1 ->
  0 <= v' <= n -> 0 <= k -> 16 * k <= n -> v' mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNSHRINK m)))
    (ann_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo b n v' l1 L0 m).
Proof using AF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V b n v' k l1 L0 lo
    FDO MST -> -> -> VC FOBJ0 LV L1 V0 K0 KN V16 N16 NB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INB : In (b, 16 * k) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; right; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m b (16 * k) ART0 INB) as (B0 & B1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : v_shz [(usp - 16, usp)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (annshrink_walk1 usp V b (b + v') (b + n) k lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  apply (ANN Σ PMc (Z_to_bv 64 0xb4f00) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + 16 * k)) (Z_to_bv 64 (b + v')) a4' a5' a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 b n (16 * k) v' l1 L0 lo FDO MST LV L1);
    try reflexivity; try assumption; try (clear - V0 K0 KN V16 N16 NB; Z.div_mod_to_equations; lia).
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Σ1 & r & Hc2 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb4f00) in Hc2' by lia.
    assert (FR2 : rw_cells asegs m2 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annshrink_walk2 usp lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F2 fc m2 ST2 ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists r, m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Theorem vdestroy_ok : vdestroy_cpsA RT.
Proof using AF RTF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m C V A cap size els L0 lo
    FDO MST -> -> UC CT CM8 RC VR VL LVPOS CAP1 FOBJ0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct VR as (ESZ & SZR & CAPB & A0 & AH & SV & [(C0 & _)|(CP1 & A16 & APOS & EL)]); [lia|].
  unfold vliveA, vblockA in VL. destruct (Z.eqb_spec cap 0) as [|_]; [lia|].
  set (n := 16 * cap) in *.
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INA : In (A, 16 * size) (rt_live RT Σ)) by (rewrite VL; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m A _ ART0 INA) as (_ & AR1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 32, usp); (V + 8, V + 16)]).
  { constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor]. right; right. exists f, kf. cbn [fst snd]. split; [exact INF| lia]. }
  assert (SHX0 : x_shz [(usp - 32, usp); (V + 8, V + 16)] m C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ m' C 8 (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)); ul. }
  assert (SHZ0 : v_shz [(usp - 32, usp); (V + 8, V + 16)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (des_walk1 usp C V A (A + 16 * size) (A + n) lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UC ltac:(ul) ltac:(ul) ltac:(ul) ltac:(subst n; ul) ltac:(subst n; ul) ltac:(subst n; ul)
                ltac:(replace (A + 16 * size - A) with (size * 16) by lia; apply Z.mod_mul; lia) (conj G1 G2) SHX0 SHZ0 RC SV MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & RC1 & VC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  replace ((A + 16 * size - A) / 16) with size in Hc1' by (replace (A + 16 * size - A) with (size * 16) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (VC1' : rw_cells asegs m1 V (vcells A (A + 0) (A + n))) by (rewrite Z.add_0_r; exact VC1).

  apply (annshrink_cps Σ PMc (Z_to_bv 64 0xb9220) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 V) (Z_to_bv 64 size) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
           V A n 0 size [] L0 lo FDO MST eq_refl eq_refl eq_refl VC1' FOBJ1 VL (Forall_nil _));
    [subst n; lia| lia| subst n; lia| reflexivity| subst n; clear - CP1; Z.div_mod_to_equations; lia| subst n; clear - CP1 CAPB; lia
    | exact ART1| exact MI1| rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM
    | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  intros c2 ((Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
  destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (r1 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb9220) in Hc2' by lia. cbn [app] in LV1.
  assert (PR2 : forall a : word, usp - 32 <= bv_unsigned a < USTACK_TOP \/ in_fframe (rt_frames RT Σ) (bv_unsigned a) -> m2 a = m1 a).
  { intros a [Ha|Ha]; apply PRES2; [left; ul| right; right; right; left; exact Ha]. }
  assert (FR2 : rw_cells asegs m2 (usp + -32) (des_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros a Ha. unfold des_frame in Ha. cbn [cells_size csize Nat.add] in Ha. apply PR2. left. ul. }
  assert (RC2 : rw_cells asegs m2 C [C8 (Z_to_bv 64 V)]).
  { apply (rw_cells_agree asegs m1 m2 _ _ RC1); [| exact WM2]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR2. left. ul. }
  assert (VC2 : rw_cells asegs m2 V (vcells A (A + 0) (A + n))).
  { apply (rw_cells_agree asegs m1 m2 _ _ VC1'); [| exact WM2]. intros a Ha. unfold vcells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PR2. right. exists f, kf. split; [exact INF| lia]. }
  pose proof (fobj_pres RT AF Σ Σ1 (rt_live RT Σ) (usp + -32) m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (FPC1 : fp_client RT Σ1 lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHX2 : x_shz [(usp - 32, usp)] m2 C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ1 m' C 8 (art_fp_client RT AF Σ1 m2 m' lo _ ART2 LOW1 FPC1 MU WM)); rewrite ?SP1; ul. }
  assert (SHZ2 : v_shz [(usp - 32, usp)] m2 V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ1 m'); [exact (art_fp_client RT AF Σ1 m2 m' lo _ ART2 LOW1 FPC1 MU WM)|].
    exact (fobj_munch RT AF Σ1 m2 m' lo _ V 24 ART2 LOW1 FPC1 MU FOBJ2). }

  pose proof (des_walk2 usp C V lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 r1 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (des_frame s2 s1 s0 ra) F2 fc2 m2
                ltac:(ul) ltac:(ul) SHX2 RC2 MI2) as W2.
  lazymatch type of W2 with evt asegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.

  apply (anndel_cps RT AF ANN Σ1 PMc (Z_to_bv 64 0xb9230) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 V) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2
           V A n 0 [] L0 lo FDO MST eq_refl eq_refl VC2 FOBJ2 LV1 (Forall_nil _));
    [subst n; lia| reflexivity| subst n; clear - CP1; Z.div_mod_to_equations; lia| subst n; clear - CP1 CAPB; lia
    | exact ART2| exact MI2| rewrite EU2; exact ST2| exact LOW1| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM2
    | split; [unfold VB_ANNDEL; exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
  intros c4 ((Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2) & FC4).
  destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (r2 & m3 & RS4 & (ART3 & MI3 & WM3 & ST3) & PRES3) & FRM3 & Hc4'). clear Hc4.
  destruct RS4 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F3 & fc3 & ->).
  cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite (ret_pc_even 0xb9230) in Hc4' by lia. cbn [app] in LV2. rewrite ann_block_plain in LV2.
  assert (PR3 : forall a : word, usp - 32 <= bv_unsigned a < USTACK_TOP \/ in_fframe (rt_frames RT Σ) (bv_unsigned a) -> m3 a = m2 a).
  { intros a [Ha|Ha]; apply PRES3; [left; ul| right; right; right; left; rewrite FRS1; exact Ha]. }
  assert (FR3 : rw_cells asegs m3 (usp + -32) (des_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m2 m3 _ _ FR2); [| exact WM3]. intros a Ha. unfold des_frame in Ha. cbn [cells_size csize Nat.add] in Ha. apply PR3. left. ul. }
  assert (RC3 : rw_cells asegs m3 C [C8 (Z_to_bv 64 V)]).
  { apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR3. left. ul. }
  assert (VC3 : rw_cells asegs m3 V (vcells A (A + 0) (A + n))).
  { apply (rw_cells_agree asegs m2 m3 _ _ VC2); [| exact WM3]. intros a Ha. unfold vcells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PR3. right. exists f, kf. split; [exact INF| lia]. }
  pose proof (fobj_pres RT AF Σ1 Σ2 (rt_live RT Σ1) (usp + -32) m2 m3 V 24 ART2 FOBJ2 PRES3 ltac:(rewrite FRS2; reflexivity)) as FOBJ3.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
  assert (FPC2 : fp_client RT Σ2 lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHX3 : x_shz [(usp - 32, usp)] m3 C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ2 m' C 8 (art_fp_client RT AF Σ2 m3 m' lo _ ART3 LOW2 FPC2 MU WM)); rewrite ?SP2, ?SP1; ul. }
  assert (SHZ3 : v_shz [(usp - 32, usp)] m3 V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ2 m'); [exact (art_fp_client RT AF Σ2 m3 m' lo _ ART3 LOW2 FPC2 MU WM)|].
    exact (fobj_munch RT AF Σ2 m3 m' lo _ V 24 ART3 LOW2 FPC2 MU FOBJ3). }

  unfold vcells in VC3.
  pose proof (des_walk3 usp C V A (A + n) lo gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 r2 d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
                s2 s1 s0 ra (C8 (Z_to_bv 64 (A + 0))) F3 fc3 m3 ST3 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(subst n; ul)
                SHX3 SHZ3 RC3 VC3 eq_refl FR3 MI3) as W3.
  rewrite <- ESP in W3.
  lazymatch type of W3 with evt asegs _ ?X =>
    assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (a2'' & -> & ST5) & Hc5'). clear Hc5.
  assert (INA2 : In (A, n) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  apply (del_ok RT AF (rf_free RT RTF) Σ2 PMc ra sp gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + n - A)) a2'' d3 d4 d5 d6 d7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 A n lo FDO MST INA2 eq_refl eq_refl ART3 MI3);
    [| exact UOK| exact FRM3| split; [exact Hc5'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM3] |].
  { unfold call_ok. fold usp. split; [exact ST5|]. split; [exact LOW2|]. split; [ul|]. split; [ul| exact SPA]. }
  intros c6 ((Σ3 & v & Hc6 & LV3 & FRS3 & SP3 & CR3) & FC6).

  assert (LV3' : rt_live RT Σ3 = L0).
  { rewrite LV3, LV2. apply live_remove_hd. intros [p k] Hin E. cbn [fst] in E. subst p.
    pose proof (af_live_disj RT AF Σ2 m3 A n A k [] L0 ART3 ltac:(rewrite LV2; reflexivity) Hin). pose proof (LVPOS A k Hin). subst n. lia. }
  apply Hk. split; [| exact FC6]. exists Σ3.
  split; [| split; [exact LV3'| split; [rewrite FRS3, FRS2; exact FRS1| split; [rewrite SP3, SP2; exact SP1| rewrite CR3, CR2; exact CR1]]]].
  eapply ASTA_conseq; [exact Hc6|]. intros ms (m4 & RS6 & AFT & PRES6). exists v, m4. split; [exact RS6|]. split; [exact AFT|].
  intros a Ha Hout. fold usp in Ha. cbn [outside] in Hout. destruct Hout as (Ho & _).
  assert (HaL : aclient (rt_live RT Σ3) (rt_frames RT Σ2) usp (bv_unsigned a)) by (rewrite LV3', FRS2, FRS1; exact Ha).
  pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite VL; intros e He; apply in_or_app; right; exact He| auto| lia])) as SPL.
  rewrite (PRES6 a HaL), (PRES3 a), (PRES2 a), (MU1 a); [reflexivity| | |].
  - cbn [outside]. split; [ul|]. split; [lia| exact I].
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite VL; intros e He; apply in_or_app; right; exact He| auto| lia].
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; apply in_or_app; right; exact He| rewrite FRS1; auto| lia].
Qed.

End Destroy.
