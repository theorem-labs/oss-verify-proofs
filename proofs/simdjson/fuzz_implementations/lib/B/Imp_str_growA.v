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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_hkit4A Atp_hkit5A Pj_rtkA Pj_defsA Pj_os_defsA Imp_hdefsA Imp_oss_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | bytes_at _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r | |- ?G => idtac "GOAL" G end; fail "PROBE".

Lemma zxb_any : forall x, zxb (Z_to_bv 8 x) = Z_to_bv 64 (x mod 256).
Proof. intros x. unfold zxb. f_equal; rewrite ?Z_to_bv_unsigned; reflexivity. Qed.
Lemma u8_lit : forall x, bv_unsigned (Z_to_bv 8 x) = x mod 256.
Proof. intros x. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma zxb_u : forall x, bv_unsigned (zxb (Z_to_bv 8 x)) = x mod 256.
Proof.
  intros x. rewrite zxb_any. rewrite unsigned_lit; [reflexivity|].
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia.
Qed.

Lemma live_remove_second : forall p z b c (L : list (Z * Z)), p <> b -> (forall e, In e L -> fst e <> b) ->
  live_remove b ((p, z) :: (b, c) :: L) = (p, z) :: L.
Proof.
  intros p z b c L NE HL. unfold live_remove. cbn.
  replace (p =? b) with false by (symmetry; apply Z.eqb_neq; exact NE). rewrite Z.eqb_refl. cbn.
  f_equal. exact (live_remove_none L b HL).
Qed.

Section PB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold OSS_PB_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma pb_tailA : forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q fO : Z) (kO : nat) (oldD olda : Z) (src : list byte)
    (cra gp cs0 cs1 a2 a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (xra xt0 xt1 xt2 xa1 xs4 xt3 xt4 xt5 xt6 : word),
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  OSNUMA len st -> OSHADOWA m O -> oa_w st = oa_lim st -> 0 <= len <= SJ_PADMAX -> 2 * oa_cap st <= PJ_CAPMAX len ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo (q + -64) -> lo + OSS_PB_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost (2 * oa_cap st) <= rt_credit RT Σ ->
  rw_cells bsegs m (q + -64) [C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
  rt_pres L (rt_frames RT Σ) q m0 m ->
  rw_cells bsegs m oldD [CB (Z.to_nat (oa_lim st)) src] ->
  (if oa_heap st
   then oldD = oa_data st /\ olda = oa_cap st /\ rw_cells bsegs m (O + 72) [C8 (wz (oa_cap st + 1)); C8 (wz (oa_cap st - 1)); C8 (wz oldD)]
        /\ (exists jr, rw_cells bsegs m (oldD + (oa_cap st - 1)) [CB 1 jr]) /\ 0 < oldD /\ oldD mod 16 = 0 /\ oa_cap st mod 16 = 0
   else oldD = O + 73 /\ olda = 23 /\ oa_cap st = IMP_SCAP0 /\ rw_cells bsegs m (O + 72) [C1 (Z_to_bv 8 44)] /\ (exists j1, rw_cells bsegs m (O + 95) [CB 1 j1])) ->
  (forall (Σ' : rts RT) (NEW : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' (O + 72) [C8 (wz (2 * oa_cap st + 1)); C8 (wz (oa_lim st + 1)); C8 (wz NEW)] ->
     (exists bs, rw_cells bsegs m' NEW [CB (Z.to_nat (2 * oa_cap st)) bs]) -> 0 < NEW -> NEW mod 16 = 0 -> NEW + 2 * oa_cap st <= rt_sp0 RT Σ - STACK_WIN ->
     (2 * oa_cap st) mod 16 = 0 -> OSHADOWA m' O ->
     rt_live RT Σ' = (NEW, 2 * oa_cap st) :: L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - mcost (2 * oa_cap st) <= rt_credit RT Σ' ->
     rt_pres_fp L (rt_frames RT Σ) q [(O + 72, O + 96)] m0 m' ->
     aevt RT PMc Σ' K (MS (mkR cra (wz q) gp (wz TPV_A) t0' t1' t2' cs0 cs1 a0' a1' a2' a3' a4' a5' a6' a7' cs2 cs3 cs4 cs5 cs6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc cra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR xra (wz (q + -64)) gp (wz TPV_A) xt0 xt1 xt2 (wz 0) (wz (O + 72)) (wz (oa_lim st)) xa1 a2 a3 a4 a5 a6 a7
                        (wz oldD) (wz (2 * oa_cap st)) xs4 (wz olda) cs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
               F (wz 0x11bf38) fc None m (seg_rom bsegs)).
Proof using AF RC RC2 FDO MST.
  intros until xt6. intros LVE LPOS INF (FLO & FHI & AL16) LOW LOR NUM SH FULL HL CM ART0 MI ST LOQ QT Q16 LVB CR FR PRES0 OLD CASE HK.
  unfold OSS_PB_STACK_A, RT_STACK in LOQ.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & FSZ0 & SHB0 & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (OSNUMA_cap24 len st NUM) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  set (cap := oa_cap st) in *. set (n := oa_lim st) in *.
  assert (NR : 22 <= n /\ n + 1 <= 2 * cap /\ n < cap) by (subst n cap; unfold oa_lim, IMP_SCAP0 in *; destruct (oa_heap st); [destruct CASE as (_ & _ & _); lia| destruct CASE as (_ & _ & -> & _); lia]).
  assert (Q0 : 0 <= q - 80) by (destruct ST; ul).
  assert (UQ64 : bv_unsigned (wz (q + -64)) = q + -64) by (apply unsigned_lit; ul).
  assert (Z1 : 1 <= 2 * cap <= 0x20001000) by lia.

  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CLD : forall sp x, oldD <= x < oldD + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
  { intros sp x Hx. destruct (oa_heap st) eqn:HP.
    - destruct CASE as (ED & _). right; right; left. exists (oa_data st), cap. split; [rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity| subst cap n; unfold oa_lim in *; rewrite HP in *; lia].
    - destruct CASE as (ED & _). apply CLF. subst n; unfold oa_lim in *; rewrite HP in *. lia. }
  assert (OLDR : 0 < oldD /\ oldD + n + 1 <= lo).
  { destruct (oa_heap st) eqn:HP.
    - destruct CASE as (ED & _ & _ & _ & D0 & _). pose proof (af_live_range RT AF Σ m (oa_data st) cap ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as (_ & R1 & _).
      subst cap n; unfold oa_lim in *; rewrite HP in *. lia.
    - destruct CASE as (ED & _). subst n; unfold oa_lim in *; rewrite HP in *. lia. }

  assert (CSEP : forall a, aclient L (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. lstep. lstep.
  apply evt_done. clear MU WM.
  eapply (aevt_opnew RT AF RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (q + -64) (2 * cap) lo Z1 eq_refl
            ltac:(lia) CR ART0 MI ST LOW ltac:(ul) ltac:(ul) ltac:(clear - Q16; Z.div_mod_to_equations; lia)).
  intros Σ1 p v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 ART2 MI2 WM2 ST2 PRES2 WR2 ACC2 LV1 FRS1 SP1 CR1 P0 P16 PTOP.
  rewrite (ret_pc_even 0x11bf44) by lia.
  pose proof (af_live_range RT AF Σ1 m2 p (2 * cap) ART2 ltac:(rewrite LV1; left; reflexivity)) as (_ & PZ & _). rewrite SP1 in PZ.

  assert (FRESH : forall sp a, lo <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (p <= a < p + 2 * cap)).
  { intros sp a Hsp Ha. apply (fresh_apart_l RT AF Σ1 m2 [(p, 2 * cap)] (rt_live RT Σ) p (2 * cap) sp a ART2 LV1 ltac:(left; reflexivity) ltac:(rewrite SP1; lia)).
    rewrite FRS1. exact Ha. }

  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> (q + -64 <= x < q) \/ (oldD <= x < oldD + n) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))
                                                  \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + cap)) -> agree_on P m m2).
  { intros P HP a Ha. apply PRES2. destruct (HP _ Ha) as [H|[H|[H|[H|[HP' H]]]]].
    - left. ul. - apply CLD. exact H. - apply CLF. exact H. - apply CLS. exact H.
    - right; right; left. exists (oa_data st), cap. split; [rewrite LVE; unfold oachunk; rewrite HP'; left; reflexivity| lia]. }
  assert (FR2 : rw_cells bsegs m2 (q + -64) [C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra]).
  { eapply rw_cells_agree_nw; [exact FR|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (OLD2 : rw_cells bsegs m2 oldD [CB (Z.to_nat n) src]).
  { eapply rw_cells_agree_nw; [exact OLD|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia. right; left. lia. }
  assert (SH2 : OSHADOWA m2 O).
  { apply (OSHADOWA_agree m m2 O SH). apply AG2. intros x Hx. do 3 right; left. lia. }
  assert (CASE2 : if oa_heap st
     then oldD = oa_data st /\ olda = cap /\ rw_cells bsegs m2 (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 oldD)]
          /\ (exists jr, rw_cells bsegs m2 (oldD + (cap - 1)) [CB 1 jr]) /\ 0 < oldD /\ oldD mod 16 = 0 /\ cap mod 16 = 0
     else oldD = O + 73 /\ olda = 23 /\ cap = IMP_SCAP0 /\ rw_cells bsegs m2 (O + 72) [C1 (Z_to_bv 8 44)] /\ (exists j1, rw_cells bsegs m2 (O + 95) [CB 1 j1])).
  { destruct (oa_heap st) eqn:HP.
    - destruct CASE as (E1 & E2 & R3 & (jr & JR) & D0 & D16 & C16). refine (conj E1 (conj E2 (conj _ (conj _ (conj D0 (conj D16 C16)))))).
      + eapply rw_cells_agree_nw; [exact R3|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia.
      + exists jr. eapply rw_cells_agree_nw; [exact JR|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 4 right. split; [reflexivity|].
        subst oldD n. unfold oa_lim in *. rewrite HP in *. lia.
    - destruct CASE as (E1 & E2 & E3 & R1 & (j1 & J1)). refine (conj E1 (conj E2 (conj E3 (conj _ _)))).
      + eapply rw_cells_agree_nw; [exact R1|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia.
      + exists j1. eapply rw_cells_agree_nw; [exact J1|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia. }
  assert (PRES02 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha. rewrite <- (PRES0 a Ha). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
  clear AG2 PRES2 FR OLD SH CASE ST MI ART0 PRES0.

  pose proof OLD2 as OLDB. apply rw_cells_bytes_at in OLDB. cbn [cells_bytes cbytes] in OLDB. rewrite app_nil_r in OLDB.
  assert (LSRC : Z.of_nat (length src) = n) by (destruct OLD2 as [[[HLn _] _] _]; cbn in HLn; lia).
  assert (ACCS : acc bsegs m2 oldD n).
  { destruct (oa_heap st) eqn:HP.
    - destruct CASE2 as (-> & _). apply (acc_sub bsegs m2 (oa_data st) cap); [| lia| subst n; unfold oa_lim; rewrite HP; lia].
      apply (proj2 (af_acc_live RT AF Σ1 m2 (oa_data st) cap ART2 ltac:(rewrite LV1, LVE; unfold oachunk; rewrite HP; right; left; reflexivity))).
    - destruct CASE2 as (-> & _). apply (acc_sub bsegs m2 O (8 * Z.of_nat 33)); [| lia| cbn; subst n; unfold oa_lim; rewrite HP; lia].
      apply (acc_zero_run bsegs m2 O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SH2]. }
  assert (RCS : rng_class RT Σ1 oldD n).
  { destruct (oa_heap st) eqn:HP.
    - destruct CASE2 as (-> & _). left. exists (oa_data st), cap. split; [rewrite LV1, LVE; unfold oachunk; rewrite HP; right; left; reflexivity| subst n; unfold oa_lim; rewrite HP; lia].
    - destruct CASE2 as (-> & _). right; left. exists fO, kO. rewrite FRS1, <- EFSZ. split; [exact INF| subst n; unfold oa_lim; rewrite HP; lia]. }
  assert (CS : checked_src RT Σ1 m2 (Z_to_bv 64 (q + -64)) lo oldD (Z.of_nat (length src))).
  { unfold checked_src. rewrite UQ64, LSRC. split; [intros _; split; [exact ACCS| exact RCS]| left; lia]. }
  assert (CD : checked_dst RT Σ1 m2 (Z_to_bv 64 (q + -64)) p (Z.of_nat (length src))).
  { unfold checked_dst. rewrite UQ64, LSRC. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m2 _ _ _ _ ACC2); lia|]. left. exists p, (2 * cap). split; [rewrite LV1; left; reflexivity| lia].
    - intros i Hi. right; right; left. exists p, (2 * cap). split; [rewrite LV1; left; reflexivity| lia].
    - apply (wr_at_sub m2 p (2 * cap)); [exact WR2| lia| lia| lia]. }
  assert (COK : call_ok RT Σ1 m2 (Z_to_bv 64 (q + -64)) lo).
  { unfold call_ok. rewrite UQ64, SP1. split; [exact ST2|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
  lstep. lstep. lstep. lstep.
  apply evt_done. clear MU WM.
  replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length src))) by (rewrite LSRC; reflexivity).
  eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m2 p oldD src lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(lia) OLDB CS CD ART2 MI2 COK).
  intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m3 (ART3 & MI3 & WM3 & ST3) PRES3 BY3. rewrite UQ64 in ST3, PRES3. rewrite LSRC in PRES3.
  rewrite (ret_pc_even 0x11bf54) by lia.
  replace (Z_to_bv 64 (Z.of_nat (length src))) with (Z_to_bv 64 n) by (rewrite LSRC; reflexivity).

  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> (q + -64 <= x < q) \/ (oldD <= x < oldD + n) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))
                                                  \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + cap)) -> agree_on P m2 m3).
  { intros P HP a Ha. pose proof (HP _ Ha) as HX. apply PRES3.
    - rewrite FRS1. destruct HX as [H|[H|[H|[H|[HP' H]]]]].
      + left. ul.
      + apply (aclient_mono _ _ _ _ _ _ _ (CLD (q + -64) _ H)); [rewrite LV1; intros e He; right; exact He| intros e He; exact He| lia].
      + apply CLF. exact H. + apply CLS. exact H.
      + right; right; left. exists (oa_data st), cap. split; [rewrite LV1, LVE; unfold oachunk; rewrite HP'; right; left; reflexivity| lia].
    - destruct HX as [H|[H|[H|[H|[HP' H]]]]]; [ul| | | |].
      + pose proof (FRESH (q + -64) _ ltac:(ul) (CLD (q + -64) _ H)). lia.
      + pose proof (FRESH (q + -64) _ ltac:(ul) (CLF (rt_live RT Σ) (q + -64) _ H)). lia.
      + pose proof (FRESH (q + -64) _ ltac:(ul) (CLS (rt_live RT Σ) (q + -64) _ H)). lia.
      + pose proof (FRESH (q + -64) (bv_unsigned a) ltac:(ul) ltac:(right; right; left; exists (oa_data st), cap; split; [rewrite LVE; unfold oachunk; rewrite HP'; left; reflexivity| lia])). lia. }
  assert (FR3 : rw_cells bsegs m3 (q + -64) [C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra]).
  { eapply rw_cells_agree_nw; [exact FR2|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (OLD3 : rw_cells bsegs m3 oldD [CB (Z.to_nat n) src]).
  { eapply rw_cells_agree_nw; [exact OLD2|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia. right; left. lia. }
  assert (SH3 : OSHADOWA m3 O).
  { apply (OSHADOWA_agree m2 m3 O SH2). apply AG3. intros x Hx. do 3 right; left. lia. }
  assert (CASE3 : if oa_heap st
     then oldD = oa_data st /\ olda = cap /\ rw_cells bsegs m3 (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 oldD)]
          /\ (exists jr, rw_cells bsegs m3 (oldD + (cap - 1)) [CB 1 jr]) /\ 0 < oldD /\ oldD mod 16 = 0 /\ cap mod 16 = 0
     else oldD = O + 73 /\ olda = 23 /\ cap = IMP_SCAP0 /\ rw_cells bsegs m3 (O + 72) [C1 (Z_to_bv 8 44)] /\ (exists j1, rw_cells bsegs m3 (O + 95) [CB 1 j1])).
  { destruct (oa_heap st) eqn:HP.
    - destruct CASE2 as (E1 & E2 & R3 & (jr & JR) & D0 & D16 & C16). refine (conj E1 (conj E2 (conj _ (conj _ (conj D0 (conj D16 C16)))))).
      + eapply rw_cells_agree_nw; [exact R3|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia.
      + exists jr. eapply rw_cells_agree_nw; [exact JR|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 4 right. split; [reflexivity|].
        subst oldD n. unfold oa_lim in *. rewrite HP in *. lia.
    - destruct CASE2 as (E1 & E2 & E3 & R1 & (j1 & J1)). refine (conj E1 (conj E2 (conj E3 (conj _ _)))).
      + eapply rw_cells_agree_nw; [exact R1|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia.
      + exists j1. eapply rw_cells_agree_nw; [exact J1|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 2 right; left. lia. }
  assert (PRES03 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> m3 a = m0 a).
  { intros a Ha. rewrite <- (PRES02 a Ha). apply PRES3.
    - rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1, LVE; intros e He; right; apply in_or_app; right; exact He| intros e He; exact He| lia].
    - pose proof (FRESH q (bv_unsigned a) ltac:(ul) (aclient_mono _ _ _ (rt_live RT Σ) (rt_frames RT Σ) q _ Ha ltac:(rewrite LVE; intros e He; apply in_or_app; right; exact He) ltac:(intros e He; exact He) ltac:(lia))). lia. }

  pose proof (wr_at_transport bsegs m2 m3 p (2 * cap) WR2 WM3) as WR3.
  destruct (wr_at_rw_CB m3 p (2 * cap) WR3 ltac:(lia)) as (bn3 & NEWC3).
  clear AG3 PRES3 BY3 FR2 OLD2 SH2 CASE2 PRES02 OLDB ACCS RCS CS CD COK ST2 MI2 ART2 WM2 WM3 ACC2 WR2.
  assert (C16 : (2 * cap) mod 16 = 0).
  { destruct (oa_heap st); [destruct CASE3 as (_ & _ & _ & _ & _ & _ & M16)| destruct CASE3 as (_ & _ & EC & _); rewrite EC; unfold IMP_SCAP0]; Z.div_mod_to_equations; lia. }

  assert (TAIL : forall (Σy : rts RT) (my : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word) (Fy : bvmap 5 word) (ja jb jc bn : list byte),
    rt_live RT Σy = (p, 2 * cap) :: L -> rt_frames RT Σy = rt_frames RT Σ -> rt_sp0 RT Σy = rt_sp0 RT Σ -> rt_credit RT Σ - mcost (2 * cap) <= rt_credit RT Σy ->
    ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo (q + -64) ->
    rw_cells bsegs my (O + 72) [CB 8 ja; CB 8 jb; CB 8 jc] -> rw_cells bsegs my p [CB (Z.to_nat (2 * cap)) bn] -> OSHADOWA my O ->
    rw_cells bsegs my (q + -64) [C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 72 <= bv_unsigned a < O + 96) -> my a = m0 a) ->
    aevt RT PMc Σy K (MS (mkR yra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV_A) yt0 yt1 yt2 (Z_to_bv 64 0) (Z_to_bv 64 (O + 72)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                               (Z_to_bv 64 oldD) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 n) (Z_to_bv 64 olda) (Z_to_bv 64 p) s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                          Fy (Z_to_bv 64 0x11bf68) fc None my (seg_rom bsegs))).
  { intros Σy my yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 Fy ja jb jc bn LVy FRSy SPy CRy ARTy MIy STy HDR NEWC SHy FRy PRESy.
    clear CASE3 OLD3 FR3 SH3 PRES03 NEWC3 WR3 ART3 MI3 ST3.
    pose proof (af_frames_range RT AF Σy my fO kO ARTy ltac:(rewrite FRSy; exact INF)) as (_ & _ & _ & FLVy).
    pose proof (FLVy p (2 * cap) ltac:(rewrite LVy; left; reflexivity)) as PO. rewrite <- EFSZ in PO. clear FLVy.
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q); (O + 72, O + 96); (p, p + 2 * cap)]%Z my) as MU. pose proof (wmono_refl bsegs my) as WM.

    lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    rewrite lor1_even in HDR by (clear - CAP24; Z.div_mod_to_equations; lia).

    destruct (rw_cells_CB_atA _ _ _ _ n NEWC ltac:(lia)) as [NPRE NREST].
    apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [1; 1; (Z.to_nat (2 * cap) - Z.to_nat n - 2)]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
    forget_junk NREST. forget_junk NPRE. clear NEWC.
    remember (Z.to_nat (2 * cap) - Z.to_nat n - 2)%nat as k3 eqn:EK3 in NREST.
    set (pn := p + n) in *.
    lstep. lstep.
    subst pn.
    pose proof (rw_cells_joinA _ _ _ _ _ NPRE NREST ltac:(cbn [cells_size csize]; lia)) as BA2. clear NPRE NREST.
    lazymatch type of BA2 with rw_cells _ _ _ (?cs1 ++ ?cs2) =>
      pose proof (rw_cells_merge bsegs _ _ [] (cs1 ++ cs2) [] ltac:(rewrite app_nil_l, app_nil_r; exact BA2)) as BA3 end.
    clear BA2. cbn [cells_size csize cells_bytes cbytes app] in BA3.
    lazymatch type of BA3 with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat (2 * cap)) in BA3 by lia; set (bn' := bs) in BA3; clearbody bn' end.

    do 8 lstep. lstep. release_frame FRy STy q. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    pose proof (proj1 (af_fshadow_apart RT AF Σy my fO kO ARTy ltac:(rewrite FRSy; exact INF)) p (2 * cap) ltac:(rewrite LVy; left; reflexivity)) as PSH. rewrite <- EFSZ in PSH.
    apply evt_done. eapply HK.
    - apply (art_client_write RT AF Σy my m9 (q + -64) ARTy ltac:(rewrite SPy; ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
      split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; rewrite FRSy; apply CLF; lia|]. split; [| exact I].
      intros Hin. apply Ha. right; right; left. exists p, (2 * cap). split; [rewrite LVy; left; reflexivity| lia].
    - assumption.
    - exact STy.
    - exact HDR.
    - eexists. exact BA3.
    - exact P0.
    - exact P16.
    - exact PZ.
    - exact C16.
    - apply (OSHADOWA_agree my m9 O SHy). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. clear - Hx SHO SHT FSELF PSH LOW LOQ FLO FHI.
      split; [lia|]. split; [lia|]. split; [lia| exact I].
    - exact LVy.
    - exact FRSy.
    - exact SPy.
    - exact CRy.
    - intros a Ha Ho. cbn [outside] in Ho. rewrite <- (PRESy a Ha ltac:(lia)). apply MU. cbn [outside].
      split; [destruct (CSEP _ Ha); lia|]. split; [lia|]. split; [| exact I].
      exact (FRESH q (bv_unsigned a) ltac:(ul) (aclient_mono _ _ _ (rt_live RT Σ) (rt_frames RT Σ) q _ Ha ltac:(rewrite LVE; intros e He; apply in_or_app; right; exact He) ltac:(intros e He; exact He) ltac:(lia))). }

  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q)]%Z m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
  lstep.
  destruct (oa_heap st) eqn:HP.
  -
    destruct CASE3 as (ED & EA & R3 & _ & D0 & D16 & M16). subst olda.
    lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; clear - Kc M16 CAP24; Z.div_mod_to_equations; lia| clear Kc].
    lstep. lstep. lstep.
    apply evt_done. clear MU WM.
    assert (INB : In (oldD, cap) (rt_live RT Σ1)) by (rewrite LV1, LVE, ED; unfold oachunk; rewrite HP; right; left; reflexivity).
    eapply (aevt_opdel RT AF RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m3 oldD cap lo INB eq_refl ART3 MI3).
    { unfold call_ok. rewrite UQ64, SP1. split; [exact ST3|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
    { unfold unwind_ok. rewrite UQ64, unsigned_lit by lia. left. lia. }
    intros Σ2 v u0 u1 u2 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 F3 m4 (ART4 & MI4 & ST4) PRES4 LV2 FRS2 SP2 CR2.
    rewrite UQ64 in ST4, PRES4. rewrite (ret_pc_even 0x11bf68) by lia.
    assert (LV2' : rt_live RT Σ2 = (p, 2 * cap) :: L).
    { rewrite LV2, LV1, LVE, ED. unfold oachunk. rewrite HP. cbn [app]. rewrite <- ED. apply live_remove_second.
      - intros E0. apply (FRESH lo oldD ltac:(lia) (CLD lo oldD ltac:(lia))). lia.
      - intros [b c] Hin Eb. cbn [fst] in Eb. subst b.
        destruct (af_live_disj RT AF Σ1 m3 oldD cap oldD c [(p, 2 * cap)] L ART3
                    ltac:(rewrite LV1, LVE, ED; unfold oachunk; rewrite HP; reflexivity) ltac:(apply in_or_app; right; exact Hin)) as [X|X].
        + pose proof (af_live_range RT AF Σ1 m3 oldD c ART3 ltac:(rewrite LV1, LVE; unfold oachunk; rewrite HP; right; apply in_or_app; right; exact Hin)) as (Y & _). lia.
        + pose proof (LPOS oldD c Hin). lia. }

    assert (AG4 : forall P : Z -> Prop, (forall x, P x -> (q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ)) \/ (p <= x < p + 2 * cap)) -> agree_on P m3 m4).
    { intros P HPP a Ha. apply PRES4. rewrite FRS1. destruct (HPP _ Ha) as [H|[H|[H|H]]]; [left; ul| apply CLF; exact H| apply CLS; exact H|].
      right; right; left. exists p, (2 * cap). split; [rewrite LV2'; left; reflexivity| lia]. }
    merge_at R3 0%nat 1%nat. merge_at R3 1%nat 1%nat. merge_at R3 2%nat 1%nat.
    eapply (TAIL Σ2 m4); [exact LV2'| rewrite FRS2; exact FRS1| rewrite SP2; exact SP1| rewrite CR2, CR1; lia| exact ART4| exact MI4| exact ST4| | | | |].
    + eapply rw_cells_agree_nw; [exact R3|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
    + eapply rw_cells_agree_nw; [exact NEWC3|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia. do 3 right. lia.
    + apply (OSHADOWA_agree m3 m4 O SH3). apply AG4. intros x Hx. do 2 right; left. lia.
    + eapply rw_cells_agree_nw; [exact FR3|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
    + intros a Ha Ho. rewrite <- (PRES03 a Ha). apply PRES4. rewrite FRS1.
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV2'; intros e He; right; exact He| intros e He; exact He| lia].
  -
    destruct CASE3 as (ED & EA & EC & R1 & (j1 & J1)). subst olda.
    lstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
    apply evt_done. clear MU WM.

    subst oldD. replace (Z.to_nat n) with 22%nat in OLD3 by (subst n; unfold oa_lim; rewrite HP; reflexivity).
    pose proof (rw_cells_joinA _ _ _ _ _ R1 OLD3 ltac:(cbn [app cells_size csize Nat.add]; lia)) as R12. cbn [app] in R12.
    pose proof (rw_cells_joinA _ _ _ _ _ R12 J1 ltac:(cbn [app cells_size csize Nat.add]; lia)) as R3. clear R1 J1 OLD3 R12. cbn [app] in R3.
    merge_at R3 0%nat 3%nat.
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8;8;8]%nat) in R3; [|reflexivity]. cbn [mk_CB_cells app] in R3.
    eapply (TAIL Σ1 m3); [rewrite LV1, LVE; unfold oachunk; rewrite HP; reflexivity| exact FRS1| exact SP1| lia| exact ART3| exact MI3| exact ST3| exact R3| exact NEWC3| exact SH3| exact FR3|].
    intros a Ha Ho. exact (PRES03 a Ha).
Qed.

Theorem push_backA_proof : push_backA_cps RT PMc.
Proof using AF RC RC2 FDO MST.
  unfold push_backA_cps. intros until m. intros FDO' MST' LVE LPOS INF OIN LOW LOR REP NUM SH FULL HL CM ART0 MI ST LOQ QT Q16 LVB CR HK.
  pose proof OIN as (FLO & FHI & AL16).
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (OSNUMA_cap24 len st NUM) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB.
  unfold OSS_PB_STACK_A, RT_STACK in LOQ. unfold OSS_PUSH_BACK_A.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 80) by (destruct ST; ul).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; ul).
  pose proof NUM as (WB & K0 & CAPB & HB). unfold oa_lim in WB, FULL.

  assert (PRO : forall m1, munch [(q - 64, q)] m m1 -> wmono bsegs m m1 ->
            ART RT Σ m1 /\ rt_pres L (rt_frames RT Σ) q m m1 /\ agree_on (fun x => x < lo) m m1).
  { intros m1 MU WM. split; [| split].
    - apply (art_client_write RT AF Σ m m1 (q - 64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul.
    - intros a Ha. apply MU. cbn [outside]. split; [| exact I].
      destruct (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 (aclient_mono _ _ _ (rt_live RT Σ) (rt_frames RT Σ) q _ Ha ltac:(rewrite LVE; intros e He; apply in_or_app; right; exact He) ltac:(intros e He; exact He) ltac:(lia))); lia.
    - intros a Ha. apply MU. cbn [outside]. split; [lia| exact I]. }
  destruct (oa_heap st) eqn:HP.
  -
    unfold STRREPA in REP. rewrite HP in REP. destruct REP as (R3 & (bs & BLK) & D0 & D16 & M16).
    pose proof (af_live_range RT AF Σ m (oa_data st) (oa_cap st) ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as (_ & DTOP & _).
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

    do 8 lstep. lstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx _ _ _ R3) as RD end. rewrite unsigned_lit in RD by lia.
    lstep. lstep. rewrite ?zxb_u, ?u8_lit, long_byte0 by (clear - M16; Z.div_mod_to_equations; lia). lstep. lstep. if_true.

    lstep. lstep. lstep. rewrite ?(unsigned_lit (oa_cap st + 1)) by lia. rewrite long_capmask by (clear - M16 CAP24 CAPB CMB; Z.div_mod_to_equations; lia). lstep. lstep.
    if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| clear Kc].

    lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| clear Kc].
    lstep. lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| clear Kc].
    lstep. lstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite (Z.mod_small ((oa_cap st + -1) * 2)) by lia.
    replace (Z.lor ((oa_cap st + -1) * 2) 7) with (2 * oa_cap st - 1) by (rewrite lor_low3 by lia; clear - CAP24 M16; Z.div_mod_to_equations; lia).

    lstep. lstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
    lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
    lstep. lstep.
    replace (Z_to_bv 64 (2 * oa_cap st - 1 + 1)) with (Z_to_bv 64 (2 * oa_cap st)) by (f_equal; lia).
    replace (Z_to_bv 64 (oa_cap st + -1 + 1)) with (Z_to_bv 64 (oa_cap st)) by (f_equal; lia).
    replace (Z_to_bv 64 (oa_cap st + -1)) with (Z_to_bv 64 (oa_lim st)) by (unfold oa_lim; rewrite HP; f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (PRO m1 MU WM) as (ART1 & PRES1 & AGL).
    destruct (rw_cells_CB_atA _ _ _ _ (oa_cap st - 1) BLK ltac:(lia)) as [OLD JR].
    apply evt_done.
    eapply (pb_tailA Σ K L st len lo O q fO kO (oa_data st) (oa_cap st) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m1);
      [exact LVE| exact LPOS| exact INF| exact OIN| exact LOW| exact LOR| exact NUM| | unfold oa_lim; rewrite HP; exact FULL| exact HL| exact CM| exact ART1| assumption| exact ST
      | unfold OSS_PB_STACK_A, RT_STACK; lia| exact QT| exact Q16| exact LVB| exact CR| exact FR| exact PRES1| | | exact HK].
    + apply (OSHADOWA_agree m m1 O SH). intros a Ha. apply AGL. pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT.
      unfold shad in *. clear - Ha SHT LOW FLO FHI. Z.div_mod_to_equations. lia.
    + unfold oa_lim. rewrite HP. exact OLD.
    + rewrite HP. split; [reflexivity|]. split; [reflexivity|]. split; [exact R3|]. split; [| split; [exact D0| split; [exact D16| exact M16]]].
      eexists. replace (Z.to_nat (oa_cap st) - Z.to_nat (oa_cap st - 1))%nat with 1%nat in JR by lia. exact JR.
  -
    unfold STRREPA in REP. rewrite HP in REP. destruct REP as (R1 & (bs & R23) & ED). destruct HB as [EC EK].
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

    do 8 lstep. lstep.

    lstep. lstep. rewrite ?zxb_u, ?u8_lit. change (Z.land (44 mod 256) 1) with 0. lstep. lstep. if_false.

    lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit, ?u8_lit in Kc by lia; cbn in Kc; lia| clear Kc].
    lstep. lstep. lstep. lstep. lstep.
    replace (Z_to_bv 64 48) with (Z_to_bv 64 (2 * oa_cap st)) by (rewrite EC; reflexivity).
    replace (Z_to_bv 64 22) with (Z_to_bv 64 (oa_lim st)) by (unfold oa_lim; rewrite HP; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (PRO m1 MU WM) as (ART1 & PRES1 & AGL).
    destruct (rw_cells_CB_atA _ _ _ _ 22 R23 ltac:(lia)) as [OLD J1]. replace (O + 73 + 22) with (O + 95) in J1 by lia.
    apply evt_done.
    eapply (pb_tailA Σ K L st len lo O q fO kO (O + 73) 23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m1);
      [exact LVE| exact LPOS| exact INF| exact OIN| exact LOW| exact LOR| exact NUM| | unfold oa_lim; rewrite HP; exact FULL| exact HL| exact CM| exact ART1| assumption| exact ST
      | unfold OSS_PB_STACK_A, RT_STACK; lia| exact QT| exact Q16| exact LVB| exact CR| exact FR| exact PRES1| | | exact HK].
    + apply (OSHADOWA_agree m m1 O SH). intros a Ha. apply AGL. pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT.
      unfold shad in *. clear - Ha SHT LOW FLO FHI. Z.div_mod_to_equations. lia.
    + unfold oa_lim. rewrite HP. exact OLD.
    + rewrite HP. split; [reflexivity|]. split; [reflexivity|]. split; [exact EC|]. split; [exact R1|]. eexists. exact J1.
Qed.
End PB.
