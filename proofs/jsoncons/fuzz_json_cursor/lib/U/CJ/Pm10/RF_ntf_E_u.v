(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_malloc_free_u F_malloc_fast_u MallocModel_B_u F_ntf_B_u F_ntf_C_u F_ntf_E_u MallocKit_A3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import RMallocRep_u RMallocTree_u RMallocKit_B_u RMallocKit_B3_u RF_ntf_A_u RF_ntf_C_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa98c8) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some g ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa98c0) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  st1.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (1010704 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (1010704 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  a2 = pw st (active st sc) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa983c) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (1010704, 1010704 + 928)]%Z m) as MU.

  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.

  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.

  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (1010704 + 80 + 8 * sc)) with (Z_to_bv 64 (1010704 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }

  st1. if_cases K; zify_cond K.
  -
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  -
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. pose_ceil. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    pose proof MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (Z_to_bv 64 (1010704 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (1010704 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
  le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof.
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa992c) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv rsegs m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa98c8) fc None m (seg_rom rsegs)).
Proof.
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB. pose_ceil.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.

  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono rsegs m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).

  st1. if_cases K; zify_cond K.
  -
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  -
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].

    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (1010704 + 80 + 8 * sc)) with (Z_to_bv 64 (1010704 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.

    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. pose_ceil. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.

      st1.

      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }

      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.

      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

      st1. st1. st1.

      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    +
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
End CEIL_WRAP_1.

