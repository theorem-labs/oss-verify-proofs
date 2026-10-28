(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rmrep_set_bounce {HGW : HasGuard} {HCEIL : HasCeiling} : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity; try (left; reflexivity).
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write rsegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

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

Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Lemma rconc_meta_inj {HGW : HasGuard} {HCEIL : HasCeiling} : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & _ & WR & DJ & _).
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

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; LiaTuning.ctauto]);
    clear MUq WMq CH end.

Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Lemma rmrep_regroup {HGW : HasGuard} {HCEIL : HasCeiling} : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof.
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). pose proof WF as (RS & CE & WR & DJ & WA & WG).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP, RVMLOCK in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

Lemma rmrep_set_group_ai {HGW : HasGuard} {HCEIL : HasCeiling} : forall st m m' b g ai0 ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

Lemma rmrep_ctr_byte_read {HGW : HasGuard} {HCEIL : HasCeiling} : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes rsegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof.
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read rsegs m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

