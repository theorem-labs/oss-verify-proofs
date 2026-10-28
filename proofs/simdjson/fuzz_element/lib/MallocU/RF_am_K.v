(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rbytes_at_zeros_sub m A n off k :
  bytes_at usegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at usegs m (A + off) (zeros k).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma rrw_cells_of_zeros m A n off cs :
  bytes_at usegs m A (zeros n) -> wr_at usegs m A (Z.of_nat n) ->
  cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
  rw_cells usegs m (A + off) cs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.

Lemma rmrep_set_area_next : forall st m m' a ar p,
  rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
  munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st a) [C8 (wz (a_check ar + bv_unsigned rr_secret)); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
  rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' a ar p MR Ha Hp MU WM CH.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  assert (AG : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells usegs m' A cs).
  { intros A cs H HD. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
    intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  -   split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  -   destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    unfold rmrep_ctx. change (rctx_head_cells st') with (rctx_head_cells st). change (actives st') with (actives st).
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    change (ctx_tail_cells st') with (ctx_tail_cells st).
    split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
    split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    apply AG; [exact C6| cbn; unfold RCTX; lia].
  -   destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
    split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. split; [apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia]|]. apply AG; [exact G6| cbn; lia].
  -   intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
    destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
      split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
      * apply AG; [exact A3| cbn; lia].
    + rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
      destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
      assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
        - rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
          assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
          Z.div_mod_to_equations. lia.
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
      change (pw st' (a_next ar')) with (pw st (a_next ar')).
      split; [apply AG; [exact A1| cbn; lia]|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
      * apply AG; [exact A3| cbn; lia].
  -   intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
    rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
    cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
  -   intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
    + eapply wr_at_transport; [exact HWr| exact WM].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
      eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; pose proof (round_up_pg_ge (r_len r)); lia).
      assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

Lemma rmrep_new_area : forall st m (p : aptr) r chk,
  rmrep st m -> (s_areas st) !! p = None ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  rw_cells usegs m (conc st p) [C8 (wz (chk + bv_unsigned rr_secret)); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
  (forall k, 0 <= k < NSLOTS -> rw_cells usegs m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
  rw_cells usegs m (conc st p + 4064) [CB 32 (zeros 32)] ->
  rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
    + exists r. repeat split; assumption.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - exact CX.
  - exact GL.
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
    destruct (decide (a' = p)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
      split; [exact HDR|]. split; [| exact PAD].
      intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
  - exact GR.
  - exact SH.
Qed.

Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
  rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
  0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None ->
  conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
    destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
    + rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
      assert (NEo : snd ak <> snd p).
      { intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
      Z.div_mod_to_equations. lia.
    + pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
  - destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
    assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
    pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
    assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
    pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.
End WithCeiling0.

