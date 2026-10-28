(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel ImpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_hkit4A Atp_hkit5A Pj_rtkA Pj_defsA Pj_os_defsA Imp_hdefsA Imp_oss_defsA Imp_str_growA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma le1_smallZ : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Section OV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold OSS_OV_STACK_A, OSS_PB_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma aevt_memsetS : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
               F (Z_to_bv 64 e_memset) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hn CD ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (rc_memset RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d n cb lo FDO MST E0 E1 E2 Hd Hn CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma append_longA : forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (lo P A alloc sz n q fO : Z) (kO : nat) (bs : list byte)
    (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rt_live RT Σ = (A, alloc) :: L -> In (fO, kO) (rt_frames RT Σ) -> fO <= P -> P + 24 <= fO + fs_size kO - 8 -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m P [C8 (wz (alloc + 1)); C8 (wz sz); C8 (wz A)] -> alloc mod 16 = 0 ->
  rw_cells bsegs m A [CB (Z.to_nat alloc) bs] -> 1 <= n -> 0 <= sz -> sz + n <= alloc - 1 -> alloc < 2^32 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + 80 + RT_STACK <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' P [C8 (wz (alloc + 1)); C8 (wz (sz + n)); C8 (wz A)] -> (exists bs', rw_cells bsegs m' A [CB (Z.to_nat alloc) bs']) ->
     rt_pres_fp L (rt_frames RT Σ) q [(P + 8, P + 16)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz P) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz P) (wz n) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_APPEND_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until m. intros LVE INF FLO FHI LOW LOR REP M16 BLK N1 SZ0 ROOM AL32 ART0 MI ST LOQ QT Q16 HK.
  unfold OSS_APPEND_A, RT_STACK in *.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_live_range RT AF Σ m A alloc ART0 ltac:(rewrite LVE; left; reflexivity)) as (A0 & ATOP & _).
  pose proof (FLIVE A alloc ltac:(rewrite LVE; left; reflexivity)) as PA.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 96) by (destruct ST; ul).
  assert (UQ80 : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; ul).
  assert (LBS : length bs = Z.to_nat alloc) by (destruct BLK as [[[HLx _] _] _]; exact HLx).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLA : forall sp x, A <= x < A + alloc -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
  { intros sp x Hx. right; right; left. exists A, alloc. split; [rewrite LVE; left; reflexivity| lia]. }
  assert (CSEP : forall a, aclient L (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; right; exact He| intros e He; exact He| lia]. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 10 lstep. lstep.
  lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| clear Kc].
  lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx _ _ _ REP) as RD end. rewrite unsigned_lit in RD by ul.
  lstep. lstep. lstep. rewrite ?zxb_u, ?u8_lit, long_byte0 by (clear - M16; Z.div_mod_to_equations; lia). lstep. if_true.

  lstep. rewrite ?(unsigned_lit (alloc + 1)), ?(Z.mod_small (alloc + 1)) by ul. rewrite long_capmask by (clear - M16 A0 ATOP SP0R ROOM SZ0 N1; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; Z.div_mod_to_equations; lia).
  lstep. lstep. rewrite ?(Z.mod_small (alloc + 1)) by ul.
  replace (Z.land (alloc + 1) 1) with 1 by (rewrite land1_mod2; clear - M16; Z.div_mod_to_equations; lia).
  lstep. if_false. lstep. lstep. lstep.
  if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by ul; ul].

  lstep. if_false. lstep. lstep. lstep. lstep. lstep. lstep. lstep.

  lstep. apply evt_done.
  lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 80) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU. cbn [outside]. split; [| exact I]. destruct (CSEP _ Ha); ul. }
  pose proof (af_acc_live RT AF Σ m1 A alloc ART1 ltac:(rewrite LVE; left; reflexivity)) as [WRA ACCA].
  assert (CD : checked_dst RT Σ m1 (Z_to_bv 64 (q + -80)) (A + sz) n).
  { unfold checked_dst. rewrite UQ80. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m1 A alloc); [exact ACCA| lia| lia]|]. left. exists A, alloc. split; [rewrite LVE; left; reflexivity| lia].
    - intros i Hi. apply CLA. lia.
    - apply (wr_at_sub m1 A alloc); [exact WRA| lia| lia| lia]. }
  assert (COK : call_ok RT Σ m1 (Z_to_bv 64 (q + -80)) lo).
  { unfold call_ok. rewrite UQ80. split; [exact ST|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
  clear MU WM.
  eapply (aevt_memsetS Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (A + sz) n (Z_to_bv 8 0) lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) CD ART1 ltac:(assumption) COK).
  intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite UQ80 in ST2, PRES2.
  rewrite (ret_pc_even 0x11c148) by lia.
  assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -80 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (A <= x < A + alloc)) /\ ~ (A + sz <= x < A + sz + n)) -> agree_on Q m1 m2).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES2; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLA; exact H]. }
  assert (FR2 : rw_cells bsegs m2 (q + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| ul]. }
  assert (REP2 : rw_cells bsegs m2 P [C8 (Z_to_bv 64 (alloc + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)]).
  { eapply rw_cells_agree_nw; [exact REP|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia|]. clear - Hx PA FHI FLO SZ0 ROOM N1. lia. }

  destruct (rw_cells_CB_atA _ _ _ _ sz BLK ltac:(lia)) as [B1 B23].
  destruct (rw_cells_CB_atA _ _ _ _ n B23 ltac:(cbn; lia)) as [B2 B3]. clear B23 B2.
  assert (B1' : rw_cells bsegs m2 A [CB (Z.to_nat sz) (firstn (Z.to_nat sz) bs)]).
  { eapply rw_cells_agree_nw; [exact B1|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [do 2 right; lia| lia]. }
  lazymatch type of B3 with rw_cells _ _ _ ?cs => assert (B3' : rw_cells bsegs m2 (A + sz + n) cs)
    by (eapply rw_cells_agree_nw; [exact B3|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [do 2 right; lia| lia]) end.
  clear B1 B3 BLK.
  assert (B2' : rw_cells bsegs m2 (A + sz) [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]).
  { pose proof (rw_cells_CB_intro m2 (A + sz) _ BY2) as X. rewrite repeat_length in X. apply X.
    rewrite Z2Nat.id by lia. apply (wr_at_sub m2 A alloc); [exact (wr_at_transport bsegs m1 m2 A alloc WRA WM2)| lia| lia| lia]. }

  clear BY2. apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (P + 8, P + 16); (A + sz + n, A + sz + n + 1)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
  pose proof (rw_cells_C8_read1_g bsegs m2 _ _ _ REP2) as RD2. rewrite unsigned_lit in RD2 by ul.
  lstep. lstep. rewrite ?zxb_u, ?u8_lit, long_byte0 by (clear - M16; Z.div_mod_to_equations; lia). lstep. if_true. clear RD2.
  lstep. lstep.

  apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [1; (Z.to_nat alloc - Z.to_nat sz - Z.to_nat n - 1)]%nat) in B3'; [| cbn; lia]. cbn [mk_CB_cells app] in B3'.
  forget_junk B3'. remember (Z.to_nat alloc - Z.to_nat sz - Z.to_nat n - 1)%nat as k3 eqn:EK3 in B3'.
  replace (Z_to_bv 64 (A + (sz + n))) with (Z_to_bv 64 (A + sz + n)) by (f_equal; lia).
  set (pe := A + sz + n) in *.
  lstep.
  subst pe.

  pose proof (rw_cells_joinA _ _ _ _ _ B1' B2' ltac:(cbn [cells_size csize]; lia)) as B12. cbn [app] in B12.
  pose proof (rw_cells_joinA _ _ _ _ _ B12 B3' ltac:(cbn [cells_size csize Nat.add]; lia)) as B123. cbn [app] in B123. clear B1' B2' B12 B3'.
  lazymatch type of B123 with rw_cells _ _ _ ?cs =>
    pose proof (rw_cells_merge bsegs _ _ [] cs [] ltac:(rewrite app_nil_l, app_nil_r; exact B123)) as BALL end.
  clear B123. cbn [cells_size csize cells_bytes cbytes app] in BALL.
  lazymatch type of BALL with rw_cells _ _ _ [CB ?k ?bsx] => replace k with (Z.to_nat alloc) in BALL by lia; set (bn' := bsx) in BALL; clearbody bn' end.

  lstep. do 10 lstep. lstep. release_frame FR2 ST2 q. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  apply evt_done. eapply HK.
  - apply (art_client_write RT AF Σ m2 m9 (q + -80) ART2 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia|]. split; [| exact I].
    intros Hin. apply Ha. apply CLA. lia.
  - assumption.
  - exact ST2.
  - exact REP2.
  - eexists. exact BALL.
  - intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRES1 a Ha). rewrite <- (PRES2 a).
    + apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [lia|]. split; [| exact I].
      pose proof (fresh_apart_l RT AF Σ m2 [(A, alloc)] L A alloc q (bv_unsigned a) ART2 LVE ltac:(left; reflexivity) ltac:(ul) Ha). lia.
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; right; exact He| intros e He; exact He| lia].
    + pose proof (fresh_apart_l RT AF Σ m2 [(A, alloc)] L A alloc q (bv_unsigned a) ART2 LVE ltac:(left; reflexivity) ltac:(ul) Ha). lia.
Qed.

Section WithPB.
Hypothesis PB : push_backA_cps RT PMc.

Theorem overflowA_proof : overflowA_cps RT PMc.
Proof using AF RC RC2 FDO MST PB.
  unfold overflowA_cps. intros until m. intros FDO' MST' LVE LPOS INF OIN LOW LOR INV SH FULL HL CM CR8 ART0 MI ST LOQ QT Q16 LVB CR HK.
  pose proof OIN as (FLO & FHI & AL16).
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct INV as (PUTC & REP & NUM).
  pose proof (OSNUMA_cap24 len st NUM) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB. pose proof (OSNUMA_k len st HL NUM) as KB.
  unfold OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK in LOQ. unfold OSS_OVERFLOW_A. unfold USTACK_TOP in QT.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 96) by (destruct ST; ul).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; ul).
  assert (UQ80 : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; ul).
  destruct PUTC as (PUTC & (hm & HMC & HMR) & (j108 & MODE)). unfold sb_cellsA in PUTC.
  set (cap := oa_cap st) in *. set (D := oa_data st) in *. set (lim := oa_lim st) in *.
  pose proof NUM as (WB & K0 & CAPB & HB). change (oa_lim st) with lim in WB. rewrite FULL in PUTC, HMR.
  assert (LIMR : 22 <= lim < cap) by (subst lim cap; unfold oa_lim in *; destruct (oa_heap st); [lia| destruct HB as [EC _]; unfold IMP_SCAP0 in EC; lia]).
  assert (M16 : oa_heap st = true -> cap mod 16 = 0).
  { intros HP. unfold STRREPA in REP. rewrite HP in REP. destruct REP as (_ & _ & _ & _ & X). exact X. }
  assert (DR : 0 < D /\ D + cap <= lo).
  { unfold STRREPA in REP. destruct (oa_heap st) eqn:HP.
    - destruct REP as (_ & _ & D0 & _). pose proof (af_live_range RT AF Σ m D cap ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as (_ & R1 & _). lia.
    - destruct REP as (_ & _ & ED). destruct HB as [EC _]. subst D cap. rewrite ED. unfold IMP_SCAP0 in EC. lia. }
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CSEP : forall a, aclient L (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pj_hide REP.
  lstep. carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 10 lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| clear Kc].

  lstep. lstep. lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by ul; ul].

  lstep. lstep. lstep. lstep. if_true.

  do 7 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  pj_unhide REP.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 80) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : rt_pres L (rt_frames RT Σ) q m m1).
  { intros a Ha. apply MU. cbn [outside]. split; [| exact I]. destruct (CSEP _ Ha); ul. }
  assert (REP1 : STRREPA m1 O st).
  { apply (STRREPA_agree m m1 O st REP); [lia|]. apply (agree_of_munch _ _ _ _ MU). intros x [Hx|[HP' Hx]]; cbn [outside]; (split; [| exact I]); [lia|]. subst D cap. lia. }
  assert (SH1 : OSHADOWA m1 O).
  { apply (OSHADOWA_agree m m1 O SH). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. split; [| exact I].
    pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT. lia. }
  clear REP SH MU WM.
  apply evt_done.
  eapply (PB Σ K L st len lo O (q + -80) fO kO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 FDO MST LVE LPOS INF OIN LOW LOR REP1 NUM SH1 FULL HL CM ART1 ltac:(assumption) ST
            ltac:(unfold OSS_PB_STACK_A, RT_STACK; lia) ltac:(ul) ltac:(clear - Q16; Z.div_mod_to_equations; lia) LVB CR).
  intros Σ1 NEW u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 m2 ART2 MI2 ST2 R3 (bn & NEWC) N0 N16 NTOP C16 SH2 LV1 FRS1 SP1 CR1 PRES2.
  rewrite (ret_pc_even 0x121558) by lia.
  change (oa_cap st) with cap in R3, NEWC, NTOP, C16, LV1, CR1. change (oa_lim st) with lim in R3.
  assert (NB : NEW + 2 * cap < 2^47) by (clear - NTOP SP0R; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).

  assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -80 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 72 <= x < O + 96)) -> agree_on Q m1 m2).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES2; [| cbn [outside]; split; [exact HN| exact I]].
    destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -80) cs)
    by (eapply rw_cells_agree_nw; [exact FR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| ul]) end.
  lazymatch type of PUTC with rw_cells _ _ _ ?cs => assert (PUTC2 : rw_cells bsegs m2 (O + 8) cs)
    by (eapply rw_cells_agree_nw; [exact PUTC|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (HMC2 : rw_cells bsegs m2 (O + 96) [C8 (Z_to_bv 64 hm)])
    by (eapply rw_cells_agree_nw; [exact HMC|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (MODE2 : rw_cells bsegs m2 (O + 104) [CB 4 mode16; CB 4 j108])
    by (eapply rw_cells_agree_nw; [exact MODE|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (PRES02 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 72 <= bv_unsigned a < O + 96) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1 a Ha). apply PRES2; [| cbn [outside]; split; [exact Ho| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
  clear AG2 FR PUTC HMC MODE PRES2 ST MI ART1 REP1 SH1 PRES1.
  pose proof (af_frames_range RT AF Σ1 m2 fO kO ART2 ltac:(rewrite FRS1; exact INF)) as (_ & _ & _ & FLV1).
  pose proof (FLV1 NEW (2 * cap) ltac:(rewrite LV1; left; reflexivity)) as PN. rewrite <- EFSZ in PN. clear FLV1.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
  lstep.
  pose proof (rw_cells_C8_read1_g bsegs m2 _ _ _ R3) as RD. rewrite unsigned_lit in RD by ul.
  lstep. lstep. lstep. rewrite ?zxb_u, ?u8_lit, long_byte0 by (clear - C16; Z.div_mod_to_equations; lia). lstep. if_true. clear RD.

  lstep. rewrite ?(unsigned_lit (2 * cap + 1)), ?(Z.mod_small (2 * cap + 1)) by ul. rewrite long_capmask by (clear - C16 CAP24 CM CMB; Z.div_mod_to_equations; lia).
  lstep. lstep. rewrite ?(Z.mod_small (2 * cap + 1)) by ul. replace (Z.land (2 * cap + 1) 1) with 1 by (rewrite land1_mod2; clear - C16; Z.div_mod_to_equations; lia). lstep. if_false.
  lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| clear Kc].

  lstep. lstep. lstep. lstep.
  try replace (Z_to_bv 64 (2 * cap + -1 + - (lim + 1))) with (Z_to_bv 64 (2 * cap - lim - 2)) by (f_equal; lia).
  try replace (Z_to_bv 64 (2 * cap + -1 - (lim + 1))) with (Z_to_bv 64 (2 * cap - lim - 2)) by (f_equal; lia).
  apply evt_done. clear MU WM.
  eapply (append_longA Σ1 K L lo (O + 72) NEW (2 * cap) (lim + 1) (2 * cap - lim - 2) (q + -80) fO kO bn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m2 LV1
            ltac:(rewrite FRS1; exact INF) ltac:(lia) ltac:(lia) ltac:(rewrite SP1; exact LOW) LOR R3 C16 NEWC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ART2 MI2 ST2
            ltac:(unfold RT_STACK; lia) ltac:(ul) ltac:(clear - Q16; Z.div_mod_to_equations; lia)).
  intros w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F2 m3 ART3 MI3 ST3 REP3 (bn3 & NEWC3) PRES3.
  rewrite (ret_pc_even 0x1215c0) by lia.
  replace (lim + 1 + (2 * cap - lim - 2)) with (2 * cap - 1) in REP3 by lia.
  assert (AG3 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -80 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 80 <= x < O + 88)) -> agree_on Q m2 m3).
  { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES3; [rewrite FRS1| cbn [outside]; split; [clear - HN; lia| exact I]].
    destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
  lazymatch type of FR2 with rw_cells _ _ _ ?cs => assert (FR3 : rw_cells bsegs m3 (q + -80) cs)
    by (eapply rw_cells_agree_nw; [exact FR2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| ul]) end.
  lazymatch type of PUTC2 with rw_cells _ _ _ ?cs => assert (PUTC3 : rw_cells bsegs m3 (O + 8) cs)
    by (eapply rw_cells_agree_nw; [exact PUTC2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
  assert (HMC3 : rw_cells bsegs m3 (O + 96) [C8 (Z_to_bv 64 hm)])
    by (eapply rw_cells_agree_nw; [exact HMC2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (MODE3 : rw_cells bsegs m3 (O + 104) [CB 4 mode16; CB 4 j108])
    by (eapply rw_cells_agree_nw; [exact MODE2|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
  assert (SH3 : OSHADOWA m3 O).
  { apply (OSHADOWA_agree m2 m3 O SH2). apply AG3. intros x Hx. pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF. rewrite <- EFSZ in FSELF.
    split; [do 2 right; lia| clear - Hx SHO FSELF FLO FHI; lia]. }
  assert (PRES03 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 72 <= bv_unsigned a < O + 96) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (PRES02 a Ha Ho). apply PRES3; [rewrite FRS1| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
  clear AG3 FR2 PUTC2 HMC2 MODE2 PRES3 PRES02 ST2 MI2 ART2 SH2 R3 NEWC.

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 80, q); (O + 8, O + 112); (NEW, NEW + 2 * cap)]%Z m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
  lstep. pose proof (rw_cells_C8_read1_g bsegs m3 _ _ _ REP3) as RD. rewrite unsigned_lit in RD by ul.
  lstep. lstep. rewrite ?zxb_u, ?u8_lit, long_byte0 by (clear - C16; Z.div_mod_to_equations; lia). lstep. if_false. clear RD.

  lstep. lstep. lstep. lstep. lstep. if_true.

  lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
  if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by ul; ul].

  lstep. lstep. lstep. lstep. lstep. if_false.

  lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| clear Kc]. lstep.
  replace (D + lim - D) with lim in * by lia.

  destruct (rw_cells_CB_atA _ _ _ _ lim NEWC3 ltac:(lia)) as [NPRE NREST].
  apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [1; (Z.to_nat (2 * cap) - Z.to_nat lim - 1)]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
  forget_junk NREST. forget_junk NPRE. clear NEWC3.
  remember (Z.to_nat (2 * cap) - Z.to_nat lim - 1)%nat as k3 eqn:EK3 in NREST.
  set (pn := NEW + lim) in *.
  zstep. rewrite le1_smallZ by lia. mem_after_store.
  subst pn.
  pose proof (rw_cells_joinA _ _ _ _ _ NPRE NREST ltac:(cbn [cells_size csize]; lia)) as BA2. clear NPRE NREST.
  lazymatch type of BA2 with rw_cells _ _ _ (?cs1 ++ ?cs2) =>
    pose proof (rw_cells_merge bsegs _ _ [] (cs1 ++ cs2) [] ltac:(rewrite app_nil_l, app_nil_r; exact BA2)) as NEWC4 end.
  clear BA2. cbn [cells_size csize cells_bytes cbytes app] in NEWC4.
  lazymatch type of NEWC4 with rw_cells _ _ _ [CB ?k ?bsx] => replace k with (Z.to_nat (2 * cap)) in NEWC4 by lia; set (bn' := bsx) in NEWC4; clearbody bn' end.

  lstep. lstep. lstep. do 10 lstep. lstep. release_frame FR3 ST3 q. lstep.
  replace (Z.land c 255) with c by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m3 fO kO ART3 ltac:(rewrite FRS1; exact INF)) NEW (2 * cap) ltac:(rewrite LV1; left; reflexivity)) as PSH. rewrite <- EFSZ in PSH.
  pose proof (proj2 (af_fshadow_apart RT AF Σ1 m3 fO kO ART3 ltac:(rewrite FRS1; exact INF)) fO kO ltac:(rewrite FRS1; exact INF)) as FSELF. rewrite <- EFSZ in FSELF.
  pose proof (fframe_ranges RT AF Σ1 m3 fO kO ART3 ltac:(rewrite FRS1; exact INF)) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ, SP1 in SHT.
  apply evt_done. eapply (HK Σ1 NEW).
  - apply (art_client_write RT AF Σ1 m3 m9 (q + -80) ART3 ltac:(rewrite SP1; ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; rewrite FRS1; apply CLF; lia|]. split; [| exact I].
    intros Hin. apply Ha. right; right; left. exists NEW, (2 * cap). split; [rewrite LV1; left; reflexivity| lia].
  - assumption.
  - exact ST3.
  -
    unfold SBINVA', PUTCELLSA, STRREPA, sb_cellsA, oa_grown, oa_lim. cbn [oa_data oa_cap oa_heap oa_k oa_w].
    change (oa_cap st) with cap. rewrite FULL.
    replace (NEW + (lim + 1)) with (NEW + lim + 1) by lia. replace (NEW + (2 * cap - 1)) with (NEW + (2 * cap - 1)) by lia.
    split; [| split].
    + split; [exact PUTC3|]. split; [exists (NEW + lim + 1); split; [exact HMC3| lia]| exists j108; exact MODE3].
    + split; [exact REP3|]. split; [eexists; exact NEWC4|]. split; [exact N0|]. split; [exact N16| exact C16].
    + pose proof (OSNUMA_grown len st NEW HL NUM FULL CM M16) as X. unfold oa_grown in X. rewrite FULL in X. exact X.
  - apply (OSHADOWA_agree m3 m9 O SH3). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. clear - Hx SHO SHT FSELF PSH LOW LOQ FLO FHI.
    split; [lia|]. split; [lia|]. split; [lia| exact I].
  - exact NTOP.
  - exact LV1.
  - exact FRS1.
  - exact SP1.
  - exact CR1.
  - intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRES03 a Ha ltac:(lia)). apply MU. cbn [outside].
    split; [destruct (CSEP _ Ha); lia|]. split; [lia|]. split; [| exact I].
    exact (fresh_apart_l RT AF Σ1 m3 [(NEW, 2 * cap)] L NEW (2 * cap) q (bv_unsigned a) ART3 LV1 ltac:(left; reflexivity) ltac:(rewrite SP1; ul) ltac:(rewrite FRS1; exact Ha)).
Qed.
End WithPB.
End OV.
