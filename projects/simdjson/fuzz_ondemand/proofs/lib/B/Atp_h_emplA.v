(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Od_hbaseA Sj_hkitB Atp_h_defsA Atp_h_vkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition EF_RET1 : Z := 0x9e56c.
Definition EF_RET2 : Z := 0x9e584.
Definition VB_CTXDTOR : Z := 0x9d308.

Definition xbytes (xd xl : Z) : list byte := cells_bytes [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)].
Lemma xbytes_length : forall xd xl, length (xbytes xd xl) = 16%nat.
Proof. intros. reflexivity. Qed.
Lemma xcells_of_bytes : forall (m : mem) a xd xl, bytes_at bsegs m a (xbytes xd xl) -> wr_at bsegs m a 16 -> rw_cells bsegs m a [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)].
Proof.
  intros m a xd xl HB HW. split; [| cbn [cells_size csize Nat.add]; exact HW].
  split; [cbn; repeat split; exact I|]. exact HB.
Qed.
Lemma xbytes_zero : repeat (Z_to_bv 8 0) (Z.to_nat 16) = xbytes 0 0.
Proof. vm_compute. reflexivity. Qed.

Definition ef_frame (V pos ne : Z) (ra : word) : list cell := [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 pos); C8 (Z_to_bv 64 ne); C8 ra].

Lemma ew1_fast : forall (usp V A size cap lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x679000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < A -> A + 16 * cap < 2^63 -> 0 <= size < cap ->
  shb_consts m -> v_shz [(usp - 32, usp)] m V ->
  rw_cells bsegs m V (vcells A (A + 16 * size) (A + 16 * cap)) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' a3' : word),
      ms = entry_st (Z_to_bv 64 EF_RET1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 1)
             a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNINC m1
      /\ munch [(usp - 32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
      /\ rw_cells bsegs m1 (usp + -32) (ef_frame V (A + 16 * size) (A + 16 * size + 16) ra)
      /\ rw_cells bsegs m1 V (vcells A (A + 16 * size) (A + 16 * cap)) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_EMPLF m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO A0 AH SZ (G1 & G2) SHZ VC MI.
  unfold entry_st, ATPA_EMPLF, VB_ANNINC, EF_RET1, vcells, ef_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep.
  zstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep.
  lstep.
  zstep.
  replace (A + 16 * size + 16) with (A + 16 * size + 16) by lia.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact VC|]. split; assumption.
Qed.

Lemma ew2_fast : forall (usp V e ne lo : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -32) -> 0 <= lo -> usp < 2^63 -> 0 < e < 2^63 -> e mod 8 = 0 ->
  rw_cells bsegs m (usp + -32) (ef_frame V e ne rac) -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 EF_RET2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memset m))
    (MS (mkR (Z_to_bv 64 EF_RET1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 EF_RET1) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO0 SPH EE E8 FR MI. unfold entry_st, e_asan_memset, EF_RET1, EF_RET2, ef_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. rewrite (land7_mod8 e E8). zstep. if_false.
  lstep.
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma ew3_fast : forall (usp V A size cap lo : Z)
    (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -32) -> lo <= usp - 48 -> 0x679000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo -> V mod 8 = 0 ->
  0 < A -> A + 16 * cap < 2^63 -> 0 <= size < cap -> A mod 16 = 0 ->
  shb_consts m -> v_shz [(usp - 48, usp); (V, V + 24)] m V -> x_shz [(usp - 48, usp); (V, V + 24)] m (usp - 32) 24 ->
  rw_cells bsegs m (usp + -32) (ef_frame V (A + 16 * size) (A + 16 * size + 16) rac) ->
  rw_cells bsegs m V (vcells A (A + 16 * size) (A + 16 * cap)) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' a5' : word),
      ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc rac) fc None m1 (seg_rom bsegs)
      /\ munch [(usp - 48, usp); (V, V + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 V (vcells A (A + 16 * (size + 1)) (A + 16 * cap)))
    (MS (mkR (Z_to_bv 64 EF_RET2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 EF_RET2) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO V8 A0 AH SZ A16 (G1 & G2) SHZ XSH FR VC MI.
  unfold EF_RET2, VB_CTXDTOR, ef_frame, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 48, usp); (V, V + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; lia).
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  lstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep.
  zstep.
  zstep.

  zstep. carve_frame 16%nat ST.
  lazymatch goal with H : rw_cells bsegs _ (usp + -48) [CB 16 _] |- _ => rename H into FR2 end.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR2; [| reflexivity].
  cbn [mk_CB_cells app] in FR2.
  repeat match type of FR2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR2; clearbody j end.
  lstep.
  zstep. zstep. zstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (XSH mm MU' WM' (usp - 32) ltac:(lia)) as RS0; pose proof (XSH mm MU' WM' (usp - 32 + 8) ltac:(lia)) as RS1;
    pose proof (XSH mm MU' WM' (usp - 32 + 16) ltac:(lia)) as RS2; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  replace (usp - 32) with (usp + -32) in RS0 by lia. replace (usp - 32 + 8) with (usp + -24) in RS1 by lia. replace (usp - 32 + 16) with (usp + -16) in RS2 by lia.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep.
  zstep. rewrite (land7_mod8 (V + 8) ltac:(Z.div_mod_to_equations; lia)). zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (XSH mm MU' WM' (usp - 32 + 16) ltac:(lia)) as RS2' end.
  replace (usp - 32 + 16) with (usp + -16) in RS2' by lia.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_true.
  zstep. zstep. release_frame FR2 ST (usp + -32). zstep.

  zstep. zstep. release_frame FR ST usp. zstep.
  replace (A + 16 * size + 16) with (A + 16 * (size + 1)) in * by lia.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Section Emplf.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold ATPA_PUSH_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem emplf_ok : emplf_cpsA RT.
Proof using AF RTF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V A cap size els L0 lo
    FDO MST -> -> VR VL LPOS LT FOBJ0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_range RT AF Σ m f kf ART0 INF) as (_ & _ & _ & FLV).
  destruct VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK). unfold zlength in ELS. unfold vliveA in VL.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (FPC0 : fp_client RT Σ lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp RT AF Σ m lo _ V ART0 LOW FPC0 FOBJ0) as SHZ0.
  destruct BLK as [[C0 _]|(C1 & A16 & APOS & BE)]; [lia|].
  assert (VB : vblockA A cap size = ann_block A (16 * cap) (16 * size)).
  { unfold vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite VB in VL.
  assert (INA : In (A, 16 * size) (rt_live RT Σ)) by (rewrite VL; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INA) as (_ & A1 & ASEG).

  pose proof (ew1_fast usp V A size cap lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) APOS AH ltac:(lia) (conj G1 G2) SHZ0 SV MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X0 =>
    assert (W1' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC0 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC0 MU1 FOBJ0) as FOBJ1.

  unfold EF_RET1 in Hc1'.
  apply (anninc_cps RT AF ANN Σ PMc (Z_to_bv 64 0x9e56c) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 1)
           a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 V A (16 * cap) (16 * size) 1 L0 lo FDO MST eq_refl eq_refl eq_refl VC1 FOBJ1 VL
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) ltac:(lia) ART1 MI1);
    [rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; exact SPA2| exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  intros c2 ((Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
  destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (r2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0x9e56c) in Hc2' by lia.
  cbn [app] in LV1. replace (16 * size + 16 * 1) with (16 * (size + 1)) in LV1 by lia.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (INA1 : In (A, 16 * (size + 1)) (rt_live RT Σ1)) by (rewrite LV1; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ1 m2 A (16 * (size + 1)) ART2 INA1) as (_ & A2 & _).
  assert (INF1 : In (f, kf) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
  assert (CLV1 : forall sp' x, V <= x < V + 24 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros sp' x Hx. right; right; right; left. exists f, kf. split; [exact INF1| lia]. }

  assert (FR2 : rw_cells bsegs m2 (usp + -32) (ef_frame V (A + 16 * size) (A + 16 * size + 16) ra)).
  { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
    intros x Hx. unfold ef_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

  pose proof (ew2_fast usp V (A + 16 * size) (A + 16 * size + 16) lo gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1 r2 b1 b2 b3 b4 b5 b6 b7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(lia)
                ltac:(clear - A16 SZC; Z.div_mod_to_equations; lia) FR2 MI2) as W2.
  unfold EF_RET1 in W2.
  lazymatch type of W2 with evt bsegs _ ?X0 =>
    assert (W2' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c2' Hc2''.

  pose proof (af_acc_live RT AF Σ1 m2 A (16 * (size + 1)) ART2 INA1) as [WRA2 ACA2].
  unfold EF_RET2 in Hc2''.
  apply ((rf_asan_memset RT RTF) Σ1 PMc (Z_to_bv 64 0x9e584) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1
           (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 0) (Z_to_bv 64 16) b3 b4 b5 b6 b7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m2 (A + 16 * size) 16 (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia));
    [| exact ART2| exact MI2| | split; [exact Hc2''| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c2' Hc2''); intros ms0 <-; exact FRM2] |].
  { unfold checked_dst. rewrite EU2.
    split; [intros _; split; [exact (acc_sub bsegs m2 A (16 * (size + 1)) (A + 16 * size) 16 ACA2 ltac:(lia) ltac:(lia))| left; exists A, (16 * (size + 1)); split; [exact INA1| lia]]|].
    split; [| exact (wr_at_sub m2 A (16 * (size + 1)) (A + 16 * size) 16 WRA2 ltac:(lia) ltac:(lia) ltac:(lia))].
    intros i Hi. right; right; left. exists A, (16 * (size + 1)). split; [exact INA1| lia]. }
  { unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2]. }
  intros c3 (Hc3 & FC3).
  destruct (ASTA_unpack_f RT Σ1 _ _ c3 Hc3 FC3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3) & FRM3 & Hc3'). clear Hc3.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite xbytes_zero in BY3.
  rewrite (ret_pc_even 0x9e584) in Hc3' by lia.

  assert (LV1' : exists l1, rt_live RT Σ1 = l1 ++ (A, 16 * (size + 1)) :: L0).
  { rewrite LV1. unfold ann_block. destruct (Z.eqb_spec (16 * (size + 1)) (16 * cap)) as [E|NE].
    - exists []. cbn. rewrite <- E. reflexivity.
    - exists [(A, ann_g1 (16 * cap)); (A, ann_g2 (16 * cap))]. reflexivity. }
  destruct LV1' as (l1 & LV1').
  assert (SUBL : forall e, In e L0 -> In e (l1 ++ L0)) by (intros e He; apply in_or_app; right; exact He).
  assert (FPV1 : fp_client RT Σ1 lo [(usp - 48, usp); (V, V + 24)]).
  { constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor]. right; right. exists f, kf. cbn [fst snd]. split; [exact INF1| lia]. }
  assert (VC3 : rw_cells bsegs m3 V (vcells A (A + 16 * size) (A + 16 * cap))).
  { apply (rw_cells_agree bsegs m2 m3 _ _); [apply (rw_cells_agree bsegs m1 m2 _ _ VC1); [| exact WM2]| | exact WM3].
    - apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx.
      right; right; right; left. exists f, kf. split; [exact INF| lia].
    - apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [apply CLV1; lia|]. pose proof (af_frames_range RT AF Σ1 m2 f kf ART2 INF1) as (_ & _ & _ & FLV1). destruct (FLV1 _ _ INA1); lia. }
  assert (FR3 : rw_cells bsegs m3 (usp + -32) (ef_frame V (A + 16 * size) (A + 16 * size + 16) ra)).
  { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3).
    intros x Hx. unfold ef_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| ul]. }
  pose proof (fobj_pres_ex_live RT AF Σ1 Σ1 _ _ _ _ A (16 * (size + 1)) m2 m3 V 24 ART2 (fobj_pres RT AF Σ Σ1 _ _ m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) PRES3 ltac:(auto) eq_refl INA1 ltac:(lia) ltac:(lia)) as FOBJ3.
  pose proof (af_client_consts RT AF Σ1 m3 ART3) as (G1' & G2' & _).

  pose proof (ew3_fast usp V A size cap lo gp (Z_to_bv 64 TPVB) v0 v1 v2 s0 s1 (Z_to_bv 64 (A + 16 * size)) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 ra
                F3 fc3 m3 ST3 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) V8 APOS AH ltac:(lia) A16 (conj G1' G2')
                (v_shz_of_fp RT AF Σ1 m3 lo _ V ART3 LOW1 FPV1 FOBJ3)
                (x_shz_of_fp RT AF Σ1 m3 lo _ (usp - 32) 24 ART3 LOW1 FPV1 ltac:(ul) ltac:(lia) ltac:(ul))
                FR3 VC3 MI3) as W3.
  unfold EF_RET2 in W3.
  lazymatch type of W3 with evt bsegs _ ?X0 =>
    assert (W3' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & a0' & a1' & a2'' & a3'' & a4' & a5' & -> & MU4 & WM4 & MI4 & ST4 & VC4) & Hc4'). clear Hc4.
  pose proof (art_fp_client RT AF Σ1 m3 m4 lo _ ART3 LOW1 FPV1 MU4 WM4) as ART4.

  apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c4 Hc4'); intros ms0 <-; exact FRM3].
  exists Σ1.
  split; [| split; [| split; [exact FRS1| split; [exact SP1| exact CR1]]]].
  + eapply ASTA_conseq; [exact Hc4'|]. intros ms <-. exists a0', m4.
    split; [rewrite ESP; unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [exact ART4| split; [exact MI4| fold usp; exact ST4]]|].
    split.
    *
      intros a Ha Hout. fold usp in Ha. cbn [outside] in Hout. destruct Hout as [HO _].
      assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite VL; apply in_or_app; right; exact He| auto| lia]. }
      assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -32) (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; apply in_or_app; right; exact He| intros e He; rewrite FRS1; exact He| lia]. }
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
      pose proof (chunk_apart RT AF Σ1 m2 _ A (16 * (size + 1)) L0 L0 usp (bv_unsigned a) ART2 LV1' SUBL ltac:(rewrite SP1; ul) ltac:(rewrite FRS1; exact Ha)) as NIN.
      rewrite (MU4 a); [| cbn [outside]; split; [ul| split; [exact HO| exact I]]].
      rewrite (PRES3 a Ha1 ltac:(lia)). rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha0); auto; lia].
      apply MU1. cbn [outside]. split; [ul| exact I].
    *
      unfold vrepA. split; [unfold zlength; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|].
      split; [exact VC4|]. right. split; [exact C1|]. split; [exact A16|]. split; [exact APOS|].
      rewrite velts_app. cbn [velts fst snd]. apply Sj_stage1_kit.rw_cells_app. rewrite velts_size.
      replace (A + Z.of_nat (16 * length els)) with (A + 16 * size) by lia. split.
      --
         apply (rw_cells_agree_nw bsegs m1 m4 _ _); [apply (rw_cells_agree bsegs m m1 _ _ BE); [| exact WM1]|].
         { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. rewrite velts_size in Hx. cbn [outside]. split; [ul| exact I]. }
         intros a Ha. cbv beta in Ha. rewrite velts_size in Ha.
         rewrite (MU4 a); [| cbn [outside]; split; [ul| split; [destruct (FLV _ _ INA); lia| exact I]]].
         rewrite (PRES3 a); [| right; right; left; exists A, (16 * (size + 1)); split; [exact INA1| lia]| lia].
         apply PRES2. right; right; left. exists A, (16 * size). split; [exact INA| lia].
      --
         apply xcells_of_bytes.
         ++ apply (bytes_at_agree bsegs m3 m4 _ _ BY3). intros a Ha. rewrite xbytes_length in Ha. cbv beta in Ha.
            pose proof (af_frames_range RT AF Σ1 m2 f kf ART2 INF1) as (_ & _ & _ & FLV1). destruct (FLV1 _ _ INA1) as [D|D];
            (rewrite (MU4 a); [reflexivity| cbn [outside]; split; [ul| split; [lia| exact I]]]).
         ++ apply (wr_at_sub m4 A (16 * (size + 1)) (A + 16 * size) 16); [| lia| lia| lia].
            exact (proj1 (af_acc_live RT AF Σ1 m4 A (16 * (size + 1)) ART4 INA1)).
  +
    unfold vliveA, vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite LV1. reflexivity.
Qed.

End Emplf.
