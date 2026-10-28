(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition OPNEW_A : Z := 0x167848.
Definition OPDEL_A : Z := 0x10afec.

Lemma opnew_walkA : forall (usp n lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> usp < 2^63 -> 1 <= n < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (wz 0x167864) (wz (usp + -16)) gp tp t0 t1 t2 (wz n) s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
      /\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc OPNEW_A m).
Proof.
  intros until m. intros ST LO SPH N MI.
  unfold entry_st, OPNEW_A, e_malloc.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep.
  replace (Z.b2z (n <? 1)) with 0 by (destruct (Z.ltb_spec n 1); [lia| reflexivity]). rewrite Z.add_0_r.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma opnew_walkB : forall (usp p lo : Z) (gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  stk bsegs m lo (usp + -16) -> lo <= usp - 16 -> usp < 2^63 -> 0 < p < 2^64 ->
  rw_cells bsegs m (usp + -16) [C8 s0c; C8 rac] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ret_st rac (wz usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz p) m ms /\ ms_fcsr ms = fc /\ stk bsegs m lo usp)
    (MS (mkR (wz 0x167864) (wz (usp + -16)) gp tp t0 t1 t2 s0x s1 (wz p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x167864) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO SPH P FR MI.
  pose proof ST as (STa & STb & _).
  zstep. if_cases K; zify_cond K; [| exfalso; lia].
  zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]].
Qed.

Lemma fs1 : fs_size 1 = 128.
Proof. reflexivity. Qed.
Lemma fs1s : forall f, shad (f + fs_size 1) = shad f + 16.
Proof. intros f. rewrite fs1. unfold shad. replace (f + 128) with (f + 16 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.
Ltac oclient_tac :=
  first [ left; unfold USTACK_TOP in *; lia
        | right; right; left; match goal with H : In (?p, ?n) (rt_live _ _) |- _ => exists p, n; split; [exact H| lia] end
        | right; right; right; left; match goal with H : In (?f, ?k) (rt_frames _ _) |- _ => exists f, k; split; [exact H| rewrite ?fs1; lia] end
        | right; right; right; right; match goal with H : In (?f, ?k) (rt_frames _ _) |- _ =>
            exists f, k; split; [exact H| rewrite ?fs1s, ?fs1; unfold shad, SHB in *; lia] end ].

Section ObjKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma newframe_apartI : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 17592186044416 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold SHB in *; ul). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; (unfold SHB in *; unfold SHB in *; ul).
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. (unfold SHB in *; unfold SHB in *; ul).
  - destruct H as (p & n & Hin & Hp). apply LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
      (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

Lemma aevt_icall : forall Σ K ms (Q : config -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) Q ->
  (forall c, Q c -> exists (Σ' : rts RT) (Pm : machine_state -> Prop), ASTA RT Σ' PMc Pm c /\ forall ms', Pm ms' -> aevt RT PMc Σ' K ms') ->
  aevt RT PMc Σ K ms.
Proof.
  intros Σ K ms Q HC HK. unfold aevt. eapply cps_seq; [exact HC|].
  intros T c Hc Hk. destruct (HK c Hc) as (Σ' & Pm & HA & HP).
  destruct (ASTA_unpack RT Σ' PMc Pm c HA) as (ms' & H1 & H2). exact (HP ms' H1 T c H2 Hk).
Qed.

Lemma aevt_switch : forall (Σ Σ' : rts RT) (K : config -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> aevt RT PMc Σ' K ms -> aevt RT PMc Σ K ms.
Proof.
  intros Σ Σ' K ms HA HM H T c Hc Hk. exact (H T c (ASTA_switch RT Σ Σ' PMc (eq ms) c Hc HA HM) Hk).
Qed.

Lemma ret_stF_inv : forall fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms (P : machine_state -> Prop),
  ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms ->
  (forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F',
     P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  P ms.
Proof.
  intros until P. intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & ->) H. apply H.
Qed.

Lemma aevt_memsetP : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d n : Z) (cb : byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned cb) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst RT Σ m sp d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' ->
     bytes_at bsegs m' d (repeat cb (Z.to_nat n)) ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_asan_memset) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hn CD ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_asan_memset RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d n cb lo FDO MST E0 E1 E2 Hd Hn CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma aevt_memcpyP : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d (Z.of_nat (length bs)) m m' ->
     bytes_at bsegs m' d bs ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hs Hn SRC CS CD DJ ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_asan_memcpy RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d s bs lo FDO MST E0 E1 E2 Hd Hs Hn SRC CS CD DJ ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma aevt_memmoveP : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d (Z.of_nat (length bs)) m m' ->
     bytes_at bsegs m' d bs ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_asan_memmove) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_asan_memmove RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d s bs lo FDO MST E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma aevt_memchrP : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at bsegs m s buf -> memchr_ok s cz n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) ->
  checked_src RT Σ m sp lo s (memchr_chk cz n buf) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (memchr_res s cz n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memchr) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 E1 E2 Hs Hc Hn SRC MOK OFF CS ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_memchr RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m s cz n buf lo FDO MST E0 E1 E2 Hs Hc Hn SRC MOK OFF CS ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

Lemma aevt_strlenP : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  a0 = Z_to_bv 64 s ->
  bytes_at bsegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src RT Σ m sp lo s (Z.of_nat (length str) + 1) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_strlen) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 SB NIN LS SL Hs OFF CS ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_strlen RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m s str slack lo FDO MST E0 SB NIN LS SL Hs OFF CS ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

Section ObjKit2.
Hypothesis RC2 : rt_contracts2 RT.

Lemma aevt_memcmpW : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^40 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     (r = Z_to_bv 64 0 <-> bp = bq) ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memcmp) fc None m (seg_rom bsegs)).
Proof using RC2 FDO MST.
  intros until lo. intros E0 E1 E2 LEN Hp Hq NZ LS BP BQ CP CQ ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc2_memcmp_wide RT RC2 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m p q bp bq lo FDO MST E0 E1 E2 LEN Hp Hq NZ LS BP BQ CP CQ ART0 MI0 COK).
  - intros c (r & HR & HQ). unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' HR RA PR).
Qed.

Lemma aevt_memcmp0 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memcmp) fc None m (seg_rom bsegs)).
Proof using RC2 FDO MST.
  intros until lo. intros E2 ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc2_memcmp_zero RT RC2 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST E2 ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

Lemma aevt_memmove2P : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d (Z.of_nat (length bs)) m m' ->
     bytes_at bsegs m' d bs ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memmove2) fc None m (seg_rom bsegs)).
Proof using RC2 FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc2_memmove2 RT RC2 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d s bs lo FDO MST E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma aevt_smalloc1 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 1 - 8) -> wr_at bsegs m' (shad f) (fs_size 1 / 8) ->
     rt_frames RT Σ' = (f, 1%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 1 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_stack_malloc_1) fc None m (seg_rom bsegs)).
Proof using RC2 FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK TOPC HK.
  eapply aevt_icall.
  - exact (rc2_stack_malloc_1 RT RC2 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.
End ObjKit2.

Lemma aevt_opnew : forall Σ K (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (usp n lo : Z),
  1 <= n <= 0x20001000 -> tp = Z_to_bv 64 0x6abde8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  (forall (Σ' : rts RT) (p : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> wmono bsegs m m' -> stk bsegs m' lo usp ->
     rt_pres (rt_live RT Σ) (rt_frames RT Σ) usp m m' ->
     wr_at bsegs m' p n -> acc bsegs m' p n ->
     rt_live RT Σ' = (p, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - mcost n -> 0 < p -> p mod 16 = 0 -> p + n < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 OPNEW_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until lo. intros N ETP LV CR ART0 MI0 ST0 LOR SPT SPA SP16 HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (opnew_walkA usp n lo ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0); [ul| ul| lia| exact MI0]|].
  cbv beta. intros ms (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 16) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).
  unfold aevt. eapply cps_seq.
  { apply (rc_malloc RT RC Σ PMc (wz 0x167864) (wz (usp + -16)) gp tp t0 t1 t2 (wz n) s1 (wz n)
             a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo FDO MST N eq_refl ETP LV CR ART1 MI1).
    - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
      replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SP16.
    - unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul. }
  intros T c2 (Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) Hk.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
  rewrite EU2 in ST2, PRES2.
  rewrite (ret_pc_even 0x167864) in Hc2' by lia.
  assert (FR2 : rw_cells bsegs m2 (usp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
  pose proof (opnew_walkB usp p lo gp tp u0 u1 u2 (wz n) s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                u3 u4 u5 u6 s0 ra F2 fc m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) FR2 MI2) as W2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (RS3 & FC3 & ST3) & Hc3'). clear Hc3.
  destruct RS3 as (v0 & v1 & v2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->). cbn in FC3. subst fc3.
  refine (HK Σ1 p v0 v1 v2 w1 w2 w3 w4 w5 w6 w7 v3 v4 v5 v6 F3 m2 ART2 MI2 (wmono_trans _ _ _ _ WM1 WM2) ST3 _ WR2 ACC2 LV1 FRS1 SP1 CR1 P0 P16 PTOP T c3 Hc3' Hk).
  intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  rewrite (PRES2 a), (MU1 a); [reflexivity| |].
  - cbn [outside]. split; [ul| exact I].
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma aevt_opdel : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n lo : Z),
  In (p, n) (rt_live RT Σ) -> tp = Z_to_bv 64 0x6abde8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  (forall (Σ' : rts RT) (v : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 OPDEL_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until lo. intros HIN ETP ART0 MI0 COK UOK HK.
  apply (aevt_evt RT AF PMc MST).
  change OPDEL_A with e_del.
  eapply evt_cut; [apply (del_walk ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)|].
  cbv beta. intros ms <-. apply evt_done.
  unfold aevt. eapply cps_seq.
  { exact (rc_free RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
             FDO MST HIN eq_refl ETP ART0 MI0 COK UOK). }
  intros T c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1) Hk.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & RA2 & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
  exact (HK Σ1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 RA2 PRES2 LV1 FRS1 SP1 CR1 T c2 Hc2' Hk).
Qed.

End ObjKit.
