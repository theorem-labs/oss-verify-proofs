(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import F_malloc_free MallocModel_B F_ntf_B F_ntf_C.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | first [ cbn [cells_wf cell_wf meta_cells ctx_head_cells ctx_tail_cells rctx_head_cells]; solve [repeat split] | cbn; tauto ]]);
    clear MUq WMq CH end.

From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a0 a2 a3 a5 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xc210c) fc None m' (seg_rom usegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells usegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv usegs m -> meta_slot st g -> 0 <= sc < 48 ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  (active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
  qa_facts st sc g ->
  rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt usegs (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc1ef0) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  unfold RCTX, OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.

  st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.

  pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
  st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
  replace (Z_to_bv 64 (1109496 + sc * 8 + 80)) with (wa (1109496 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
  st1. clear RDA.

  st1. if_cases K; zify_cond K.
  {
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
    unfold qpath_st. rewrite HA, optr_eqb_refl.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
  assert (HA : active st sc <> Some g).
  { intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
  destruct (GNP HA) as [GN GP].
  assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
  { unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
    replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
  rewrite QS. clear QS K.

  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  clear CH.

  st1. destruct (active st sc) as [hd|] eqn:HD.
  -
    destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
    assert (NEh : hd <> g) by congruence.
    pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.

    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
    set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
    assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).

    rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1. clear CHh.

    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
    assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).

    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
    st1. clear CH. st1.

    rmeta_open (conc st hd) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
    assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
      rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
      unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
  -
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (1109496, 1109496 + 928)]%Z m) as MU.

    st1.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.

    pose proof MRb as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok usegs _ _ (actives stB) sc (Z_to_bv 64 (1109496 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
        by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
      pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
    end.
    assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3 SOK.

    pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
      pose proof (length_le8 (pw stB (Some g))) as L8;
      apply (rw_cells_frame usegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
      apply (stk_write usegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
      apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
      apply (wmono_write usegs _ mX (wa A) bs) in WM;
      lazymatch goal with HI : mem_inv usegs mX |- _ =>
        apply (mem_inv_store usegs mX (wa A) bs) in HI;
        [| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok usegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
      end;
      remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
    end.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.
End WithCeiling0.
