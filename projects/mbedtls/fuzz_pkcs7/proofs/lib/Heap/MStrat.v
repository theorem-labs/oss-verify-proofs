(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv KStep MI_Kit MI_Inv MI_List MI_WAMeta MI_WAMeta2 MReach.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MStrat () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.MI_WAMeta.carve_rest"; "shift"; "acount"; "OSSVerify.KrLib.Heap.Malloc.NSLOTS"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "UND"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.MReach.sreach"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.am_finish"; "Stdlib.ZArith.BinInt.Z.add"; "MA"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.Heap.Malloc.am_after_brk"; "OSSVerify.KrLib.Heap.MI_WAMeta2.am_init"; "STRAT.am_silent_post"; "STRAT.am_carve_post"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.Malloc.M"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.of_nat"; "GB"; "SLOT.RB"; "SLOT.RN"; "OSSVerify.KrLib.Heap.Malloc.alloc_slot"; "OSSVerify.KrLib.Heap.Malloc.lay_none"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.malloc_small_ctrl"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "QF"; "OSSVerify.KrLib.Heap.Malloc.cmalloc"; "QS"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition UND (st : mstate) : Prop := forall m, m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0.

(* [comment removed for export] *)
Definition AMI (st : mstate) : Prop :=
  0 <= c_meta_alloc_shift (ctx st) <= 13 /\ 0 <= c_avail_meta_count (ctx st).

(* [comment removed for export] *)
Definition MA : Z := 2 ^ 26.

Lemma UND_data st st' : (forall x, data_of (MR st' x) = data_of (MR st x)) -> UND st -> UND st'.
Proof.
  intros H U m. specialize (H m). apply data_of_eq in H. destruct (U m) as [A F]. ddestruct H as (_ & -> & -> & _). auto.
Qed.

Lemma UND_metas st st' : s_metas st' = s_metas st -> UND st -> UND st'.
Proof. intros H U m. unfold MR. rewrite (get_meta_rec_ext st st' m H). apply U. Qed.

Lemma UND_upd_links st m f : (forall r, data_of (f r) = data_of r) -> UND st -> UND (upd_meta m f st).
Proof. intros Hf. apply UND_data. intros x. apply data_upd_links. exact Hf. Qed.

Lemma UND_dequeue st h m : UND st -> UND (dequeue h m st).
Proof. apply UND_data. intros x. apply dequeue_data. Qed.

Lemma UND_queue_st st h g : UND st -> UND (queue_st h g st).
Proof. apply UND_data. intros x. apply queue_data. Qed.

Lemma UND_put_meta0 st g : UND st -> UND (put_meta g meta0 st).
Proof. intros U m. unfold MR. rewrite get_meta_rec_put. destruct (aptr_eqb m g); [cbn; auto| apply U]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_undef {R} (t : M R) : Prop := exists u k, t = SVis (EUndef u) k.

Lemma guard_cases {R} tag (c : bool) (k bail : M R) : guard tag c k bail = k \/ is_undef (guard tag c k bail).
Proof. unfold guard. destruct c; [left; reflexivity| right; eexists _, _; reflexivity]. Qed.

Lemma queue_cases {R} h g st (k : mstate -> M R) bail :
  queue h g st k bail = k (queue_st h g st) \/ is_undef (queue h g st k bail).
Proof.
  unfold queue. destruct (optr_eqb (m_next (get_meta_rec st g)) None); [| right; eexists _, _; reflexivity].
  destruct (optr_eqb (m_prev (get_meta_rec st g)) None); [| right; eexists _, _; reflexivity].
  left. unfold guard, queue_st, q_link, q_single. destruct (get_head st h); reflexivity.
Qed.

Ltac ta_finish st2 m2 U2 :=
  rewrite Z.land_0_l; cbn [Z.eqb]; cbv iota beta;
  first [ destruct (negb (optr_eqb (m_next (get_meta_rec st2 m2)) (Some m2)));
          [ destruct (m_next (get_meta_rec st2 m2)) | destruct (m_mem (get_meta_rec st2 m2)) ] ];
  cbv iota beta;
  lazymatch goal with |- is_undef (activate_group ?m3 ?st3 _ _) =>
     let U3 := fresh "U" in
     assert (U3 : UND st3) by (first [exact U2 | apply (UND_metas st2); [rewrite ?s_metas_set_group_active_idx, ?s_metas_set_active; reflexivity| exact U2]]);
     let A := fresh "A" in let F := fresh "F" in
     destruct (U3 m3) as [A F]; unfold MR in A, F;
     unfold activate_group; rewrite A; cbn [Z.eqb]; unfold guard at 1; rewrite F, Z.land_0_l; cbn [Z.eqb negb];
     unfold guard; eexists _, _; reflexivity
  end.

(* [comment removed for export] *)
Lemma try_avail_cases {R} sc st (k : mstate -> Z -> M R) bail :
  UND st ->
  (exists st', try_avail sc st k bail = k st' 0 /\ UND st' /\ s_ctx st' = s_ctx st
              \/ try_avail sc st k bail = k st' 0 /\ UND st' /\ exists m, st' = dequeue (LActive sc) m st)
  \/ is_undef (try_avail sc st k bail).
Proof.
  intros U. unfold try_avail.
  destruct (active st sc) as [m|] eqn:Ea; [| left; exists st; left; auto].
  destruct (U m) as [Am Fm]. unfold MR in Am, Fm. rewrite Am. cbn [Z.eqb negb].
  rewrite Fm. cbn [Z.eqb].
  set (st1 := dequeue (LActive sc) m st).
  assert (U1 : UND st1) by (apply UND_dequeue; exact U).
  destruct (active st1 sc) as [m1|] eqn:Ea1.
  2:{ left. exists st1. right. split; [reflexivity|]. split; [exact U1|]. exists m. reflexivity. }
  right. cbv zeta.
  destruct (U1 m1) as [A1 F1]. unfold MR in A1, F1. rewrite F1.
  destruct ((0 =? mask_upto (m_last_idx (get_meta_rec st1 m1))) && negb (m_freeable (get_meta_rec st1 m1) =? 0)).
  - destruct (m_next (get_meta_rec st1 m1)) as [mn|].
    + cbv iota beta. destruct (U1 mn) as [_ Fn]. unfold MR in Fn. rewrite Fn.
      assert (U2 : UND (set_active sc (Some mn) st1)) by (apply (UND_metas st1); [reflexivity| exact U1]).
      ta_finish (set_active sc (Some mn) st1) mn U2.
    + cbv iota beta. ta_finish st1 m1 U1.
  - cbv iota beta. ta_finish st1 m1 U1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shift (st : mstate) : Z := c_meta_alloc_shift (ctx st).
Definition acount (st : mstate) : Z := c_avail_meta_count (ctx st).

Lemma am_take_cases {R} st (k : mstate -> optr -> M R) bail :
  UND st ->
  (exists st1 m, am_take st k bail = k st1 (Some m) /\ UND st1 /\ shift st1 = shift st /\ acount st1 = acount st - 1
                 /\ s_regions st1 = s_regions st)
  \/ is_undef (am_take st k bail).
Proof.
  intros U. unfold am_take. destruct (c_avail_meta (ctx st)) as [m|]; [| right; eexists _, _; reflexivity].
  left. eexists _, m. split; [reflexivity|]. split; [| split; [reflexivity| split; reflexivity]].
  apply UND_upd_links; [intros r; reflexivity|]. apply (UND_metas st); [reflexivity| exact U].
Qed.

Lemma carve_rest_facts s p : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "(0.(1.(2.$3.(4.$5.$6.$7.$8.)(9.$5.$6.$:.$7.$8.$;.)$<.)(=.(>.O2.O1.))(=.O2.))(0.(1.$7.(?.(>.O2.O1.))(?.O2.))(0.(1.$7.(10.(>.O2.O1.))$11.)(1.(2.$5.$6.$:.$12.)(13.(>.O2.O1.))(13.O2.)))))")
(* [comment removed for export] *).
Proof. unfold carve_rest, shift, acount, ctx. destruct (c_meta_area_tail (s_ctx s)); cbn; repeat split; reflexivity. Qed.

Lemma am_carve_cases {R} st p (k : mstate -> optr -> M R) bail :
  UND st ->
  (exists st1 m, am_carve st p k bail = k st1 (Some m) /\ UND st1 /\ shift st1 = shift st /\ acount st1 = NSLOTS - 1
                 /\ s_regions st1 = s_regions st)
  \/ is_undef (am_carve st p k bail).
Proof.
  intros U. rewrite am_carve_eq.
  dpose (carve_rest_facts (adv st p) p) as (M1 & S1 & C1 & R1).
  destruct (am_take_cases (carve_rest (adv st p) p) k bail) as [(st1 & m & E & U1 & S2 & C2 & R2)|Hu].
  - apply (UND_metas (adv st p)); [exact M1|]. apply (UND_metas st); [reflexivity| exact U].
  - left. dexists st1, m. split; [exact E|]. split; [exact U1|].
    split; [rewrite S2, S1; reflexivity|]. split; [rewrite C2, C1; reflexivity| rewrite R2, R1; reflexivity].
  - right. exact Hu.
Qed.

Section STRAT.
Context {R : Type}.
Variable Q : R -> Prop.

(* [comment removed for export] *)
#[using="Type"] Lemma am_finish_strat B N st nu (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O4.)P,(15.=O6.)P,Pst1,$16.Pm,$3.P,(14.R2.)P,(1.$7.(?.R3.)(?.O4.))P,(1.$7.(10.R4.)(17.$11.+1.))(18.VR,VQ,O6.O5.A2.O2.R5.(19.$3.R4.))(18.VR,VQ,O6.O5.(1:.VR,O4.O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U HB HK. unfold am_finish.
  destruct (c_avail_meta_areas (ctx st)) as [p|]; [| constructor; exact HB].
  assert (CARVE : sreach Q B N (am_carve st p k bail)).
  { destruct (am_carve_cases st p k bail U) as [(st1 & m & -> & U1 & S1 & C1 & _)|(u & k' & ->)]; [| constructor; exact HB].
    apply HK; auto. }
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu); [| exact CARVE].
  replace B with (B + 0) by lia. replace N with (N + 0)%nat by lia.
  eapply (sr_vis Q B N _ _ 0 0%nat _ (ks_mprotect (conc st p))); [exact HB|].
  intros z ->. cbn [mprotect_answer_ok Z.eqb negb orb]. exact CARVE.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma am_after_brk_strat B N st nu (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O4.)P,(0.(15.=(?.O4.))(15.(?.O4.)+=.))P,(15.=O6.)P,Pst1,$16.Pm,$3.P,(14.R2.)P,(0.(15.=(?.R3.))(15.(?.R3.)(1;.(?.O4.)+1.)))P,(1.$7.(10.R4.)(17.$11.+1.))(18.VR,VQ,O6.O5.A2.O2.R5.(19.$3.R4.))(18.VR,VQ,(1;.O6.$1<.)(1=.O5.#1.)(1>.VR,O4.O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U SH HB HK. unfold am_after_brk.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx st))).
    assert (Hn : 2 <= n <= 2 ^ 14).
    { subst n. rewrite Z.shiftl_mul_pow2 by (unfold shift in SH; lia). unfold shift in SH.
      split; [| change (2 ^ 14) with (2 * 2 ^ 13); apply Z.mul_le_mono_nonneg_l; [lia| apply Z.pow_le_mono_r; lia]].
      pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx st)) ltac:(lia) ltac:(lia)). lia. }
    assert (Hlen : 0 < n * PGSZ /\ mmap_len (n * PGSZ) <= MA).
    { unfold PGSZ, MA. split; [lia|]. rewrite mmap_len_of_aligned; [nia| lia| apply Z.mod_mul; lia]. }
    destruct Hlen as [Hl0 Hml].
    eapply sreach_mono; [eapply (sr_vis Q B N _ _ (mmap_len (n * PGSZ)) 1%nat _ (ks_mmap_ok (n * PGSZ) PROT_NONE Hl0 ltac:(unfold MA in Hml; lia))); [exact HB|]| auto| lia| lia].
    intros z Hz. destruct (negb (mmap_answer_ok (s_ceil st) (live_ranges st) (n * PGSZ) z)); [apply sreach_bad_answer; exact HB|].
    rewrite Hz. destruct (new_region RKMeta z (n * PGSZ) st) as [st1 rid] eqn:Enr.
    apply am_finish_strat; [| exact HB|].
    + apply (UND_metas st); [| exact U]. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1. reflexivity.
    + intros st2 m U2 S2 C2. apply HK; [exact U2| | exact C2].
      rewrite S2. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1. unfold shift, ctx in *. cbn -[Z.add Z.mul Z.sub]. lia.
  - eapply (sreach_mono Q Q B N (B + MA) (N + 1)%nat); [apply am_finish_strat; [exact U| exact HB|]| auto| unfold MA; lia| lia].
    intros st1 m U1 S1 C1. apply HK; [exact U1| rewrite S1; lia| exact C1].
Qed.

(* [comment removed for export] *)
Definition am_body {T} (st : mstate) (k : mstate -> optr -> M T) (bail : M T) : M T :=
  match c_free_meta_head (ctx st) with
  | Some m => k (dequeue LFree m st) (Some m)
  | None =>
    if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else
    let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
    if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
      match c_brk (ctx st) with
      | BrkUntried =>
        SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
            else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))
      | BrkLive rid off =>
        let old := conc st (rid, off) in
        let new := old + PGSZ in
        SVis (EBrk new) (fun r =>
          if negb (brk_answer_ok old new r) then bad_answer bail else
          if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
          else if negb (brk_pages_ok st old PGSZ) then bad_answer bail
          else
            let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
            let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                          (set_avail_meta_areas (Some (rid, off))
                                          (set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
            am_after_brk st2 false k bail)
      | BrkDead => am_after_brk st true k bail
      end
    else am_after_brk st true k bail
  end.

#[using="Type"] Lemma alloc_meta_eq {T} st (k : mstate -> optr -> M T) bail : alloc_meta st k bail = am_body (am_init st) k bail.
Proof. reflexivity. Qed.

#[using="Type"] Lemma am_init_facts st : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "(0.(1.(2.$3.(4.$5.$6.$7.$8.)(9.$5.$6.$:.$7.$8.$;.)$<.)(=.(1?.O1.))(=.O1.))(0.(1.$7.(?.(1?.O1.))(?.O1.))(0.(1.$7.(10.(1?.O1.))(10.O1.))(1.(2.$5.$6.$:.$12.)(13.(1?.O1.))(13.O1.)))))")
(* [comment removed for export] *).
Proof. unfold am_init, shift, acount, ctx. destruct (c_init_done (s_ctx st) =? 0); repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition am_silent_post (st st1 : mstate) : Prop :=
  UND st1 /\ shift st1 = shift st /\ acount st - 1 <= acount st1.
Definition am_carve_post (st st1 : mstate) : Prop :=
  UND st1 /\ 0 <= shift st1 <= shift st + 1 /\ acount st1 = NSLOTS - 1.

#[using="Type"] Lemma alloc_meta_strat B N st (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O3.)P,(0.(15.=(?.O3.))(15.(?.O3.)+=.))P,(15.=O5.)P,Pst1,$16.Pm,$3.P,(20.O3.R2.)(18.VR,VQ,(1;.O5.$1<.)(1=.O4.#1.)A2.O2.R3.(19.$3.R2.))P,Pst1,$16.Pm,$3.P,(21.O3.R2.)(18.VR,VQ,O5.O4.A2.O2.R3.(19.$3.R2.))(18.VR,VQ,(1;.O5.$1<.)(1=.O4.#1.)(22.VR,O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U SH HB KS KC. rewrite alloc_meta_eq.
  dpose (am_init_facts st) as (IM & IS & IC & IR). set (st0 := am_init st) in *.
  assert (U0 : UND st0) by (apply (UND_metas st); [exact IM| exact U]).
  assert (HB' : 0 <= B + MA) by (unfold MA; lia).
  assert (AFTER : forall s nu, UND s -> shift s = shift st0 -> sreach Q (B + MA) (N + 1)%nat (am_after_brk s nu k bail)).
  { intros s nu Us Ss. apply am_after_brk_strat; [exact Us| rewrite Ss, IS; exact SH| exact HB|].
    intros st1 m U1 S1 C1. apply KC. split; [exact U1|]. split; [rewrite <- IS, <- Ss; exact S1| exact C1]. }
  unfold am_body.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { apply KS. split; [apply UND_dequeue; exact U0|]. unfold shift, acount, ctx in *. autorewrite with mst. rewrite IS, IC. split; [reflexivity| lia]. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx st0)) 0) as [C0|C0]; cbn [negb].
  2:{ destruct (am_take_cases st0 k bail U0) as [(st1 & m & -> & U1 & S1 & C1 & _)|(u & k' & ->)]; [| constructor; exact HB'].
      apply KS. split; [exact U1|]. split; [rewrite S1; exact IS| rewrite C1, IC; lia]. }
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && _); [| apply AFTER; [exact U0| reflexivity]].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - (* [comment removed for export] *)
    replace (B + MA) with ((B + MA) + 0) by lia. replace (N + 1)%nat with ((N + 1) + 0)%nat by lia.
    eapply (sr_vis Q _ _ _ _ 0 0%nat _ (ks_brk 0)); [exact HB'|]. intros cur _.
    destruct (brk0_answer_ok cur) eqn:Hcur; cbn [negb]; [| apply sreach_bad_answer; exact HB'].
    assert (Hnew : 0 < round_up_pg cur + 2 * PGSZ).
    { unfold brk0_answer_ok in Hcur. apply andb_prop in Hcur as [Hcur _]. apply andb_prop in Hcur as [Hcur _]. apply Z.ltb_lt in Hcur.
      pose proof (round_up_pg_ge cur). unfold PGSZ. lia. }
    replace (B + MA) with ((B + MA) + 0) by lia. replace (N + 1)%nat with ((N + 1) + 0)%nat by lia.
    eapply (sr_vis Q _ _ _ _ 0 0%nat _ (ks_brk _)); [exact HB'|]. intros z [Hz|Hz]; [lia|].
    destruct (negb (brk_answer_ok cur _ z)); [apply sreach_bad_answer; exact HB'|].
    rewrite (proj2 (Z.eqb_neq _ _) Hz). cbn [negb]. apply AFTER; [| reflexivity]. apply (UND_metas st0); [reflexivity| exact U0].
  - apply AFTER; [exact U0| reflexivity].
  - (* [comment removed for export] *)
    replace (B + MA) with ((B + MA) + 0) by lia. replace (N + 1)%nat with ((N + 1) + 0)%nat by lia.
    eapply (sr_vis Q _ _ _ _ 0 0%nat _ (ks_brk _)); [exact HB'|]. intros z Hz.
    destruct (negb (brk_answer_ok _ _ z)); [apply sreach_bad_answer; exact HB'|].
    destruct (Z.eqb_spec z (conc st0 (rid, off) + PGSZ)) as [Ez|Nz]; cbn [negb].
    + destruct Hz as [Hz|Hz]; [| contradiction]. 
      replace (brk_pages_ok st0 (conc st0 (rid, off)) PGSZ) with false; [apply sreach_bad_answer; exact HB'|].
      symmetry. unfold brk_pages_ok. replace (0 <? conc st0 (rid, off)) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in Hz; lia). reflexivity.
    + apply AFTER; [| reflexivity]. apply (UND_metas st0); [reflexivity| exact U0].
Qed.

#[using="Type"] Lemma alloc_meta_silent B N st (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O3.)P,(23.=(10.O3.))P,(15.=O5.)P,Pst1,$16.Pm,$3.P,(20.O3.R2.)(18.VR,VQ,O5.O4.A2.O2.R3.(19.$3.R2.))(18.VR,VQ,O5.O4.(22.VR,O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U HC HB KS. rewrite alloc_meta_eq.
  dpose (am_init_facts st) as (IM & IS & IC & IR). set (st0 := am_init st) in *.
  assert (U0 : UND st0) by (apply (UND_metas st); [exact IM| exact U]).
  unfold am_body.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { apply KS. split; [apply UND_dequeue; exact U0|]. unfold shift, acount, ctx in *. autorewrite with mst. rewrite IS, IC. split; [reflexivity| lia]. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx st0)) 0) as [C0|C0]; cbn [negb].
  { exfalso. unfold acount in IC, HC. rewrite C0 in IC. lia. }
  destruct (am_take_cases st0 k bail U0) as [(st1 & m & -> & U1 & S1 & C1 & _)|(u & k' & ->)]; [| constructor; exact HB].
  apply KS. split; [exact U1|]. split; [rewrite S1; exact IS| rewrite C1, IC; lia].
Qed.
End STRAT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_bound (l : list Z) n lo hi d : lo <= d <= hi -> Forall (fun x => lo <= x <= hi) l -> lo <= nth n l d <= hi.
Proof.
  intros Hd H. destruct (Nat.lt_ge_cases n (length l)) as [LT|GE].
  - apply (proj1 (List.Forall_nth (fun x => lo <= x <= hi) l) H). exact LT.
  - rewrite nth_overflow by exact GE. exact Hd.
Qed.

Lemma size_class_total sc : 0 <= size_class sc <= 8191.
Proof.
  unfold size_class. apply nth_bound; [lia|]. eapply List.Forall_impl; [| apply MI_Arith.size_classes_bounds]. cbn beta. intros; lia.
Qed.

Lemma small_cnt_total sc i : 0 <= small_cnt sc i <= 31.
Proof.
  unfold small_cnt. apply nth_bound; [lia|].
  unfold small_cnt_tab. generalize (Z.to_nat sc) as n. intros n.
  do 9 (destruct n as [|n]; [cbn [nth]; repeat constructor; lia|]). cbn [nth]. destruct n; constructor.
Qed.

Lemma med_cnt_total i : 0 <= med_cnt i <= 32.
Proof. unfold med_cnt. apply nth_bound; [lia|]. unfold med_cnt_tab. repeat constructor; lia. Qed.

Lemma halve_even_total F : forall c u, 0 <= c -> 0 <= halve_even F c u <= c.
Proof.
  induction F as [|F IH]; intros c u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even c && (u <? 4 * c)); [|lia]. rewrite Z.shiftr_div_pow2 by lia.
  specialize (IH (c / 2 ^ 1) u ltac:(apply Z.div_pos; lia)). change (2 ^ 1) with 2 in *.
  pose proof (Z.div_le_upper_bound c 2 c ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma halve_big_total F : forall c sz, 0 <= c -> 0 <= halve_big F c sz <= c.
Proof.
  induction F as [|F IH]; intros c sz Hc; cbn [halve_big]; [lia|].
  destruct (65536 * UNIT <=? sz * c); [|lia]. rewrite Z.shiftr_div_pow2 by lia.
  specialize (IH (c / 2 ^ 1) sz ltac:(apply Z.div_pos; lia)). change (2 ^ 1) with 2 in *.
  pose proof (Z.div_le_upper_bound c 2 c ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma small_cnt_pick_total sc u : 0 <= small_cnt_pick sc u <= 31.
Proof.
  unfold small_cnt_pick. pose proof (small_cnt_total sc 0). pose proof (small_cnt_total sc 1). pose proof (small_cnt_total sc 2).
  destruct (negb _); [lia|]. destruct (negb _); lia.
Qed.

Lemma land_4095_bound y : 0 <= Z.land y 4095 <= 4095.
Proof.
  rewrite KArith.land_4095. pose proof (Z.mod_pos_bound y 4096 ltac:(lia)). lia.
Qed.

Lemma round_up_pg_bound x : x <= round_up_pg x <= x + 4095.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with 4095. pose proof (land_4095_bound (-x)). lia. Qed.

(* [comment removed for export] *)
Definition GB : Z := 2 ^ 26 + 2 ^ 20.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac zeta1 :=
  lazymatch goal with
  | |- sreach ?Q ?B ?N (let x := ?e in @?body x) => let x0 := fresh x in pose (x0 := e); change (sreach Q B N (body x0)); cbv beta
  end.

Lemma mul_bound a b A B' : 0 <= a <= A -> 0 <= b <= B' -> 0 <= a * b <= A * B'.
Proof. intros. nia. Qed.

Section SLOT.
Context {R : Type}.
Variable Q : R -> Prop.
Definition RB (c : bool) : Z := GB + (if c then MA else 0).
Definition RN (c : bool) : nat := (1 + (if c then 1 else 0))%nat.

#[using="Type"] Lemma alloc_slot_fail f : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "Pc,$24.Pst,$16.Psc,$7.Preq,$7.Pk,P,$16.P,$7.(25.VR,)Pbail,(25.VR,)PB,$7.PN,$26.P,(27.O1.#40.)P,(14.R8.)P,P,(1.$24.R:.$28.)(0.(15.=(?.R:.))(15.(?.R:.)+=.))P,P,(1.$24.R;.$29.)(15.(2:.O1.)(10.R;.))P,(15.=R9.)P,(15.(1;.R:.+2014.)$2;.)P,(15.=R8.)P,Pst',$16.(18.VR,VQ,R:.R9.A2.R<.R1.-1.)(18.VR,VQ,(1;.R:.(2<.R10.))(1=.R9.(2=.R10.))(2>.VR,$2?.O1.R?.R>.R=.R<.R;.))")
(* [comment removed for export] *).
Proof.
  induction f as [|f IH]; intros c st sc req k bail B N Hf U SH CNT Hreq HreqB HB HK.
  { cbn [alloc_slot]. constructor. unfold RB, GB, MA; destruct c; lia. }
  assert (HRB : 0 <= B + RB c) by (unfold RB, GB, MA; destruct c; lia).
  cbn [alloc_slot].
  lazymatch goal with |- sreach _ _ _ (try_avail _ _ ?K _) =>
  destruct (try_avail_cases sc st K bail U) as [(st1 & HTA)|(u & k' & ->)] end.
  2:{ constructor. exact HRB. }
  lazymatch goal with |- sreach _ _ _ (try_avail _ _ ?K _) =>
    assert (HTA' : try_avail sc st K bail = K st1 0 /\ UND st1 /\ shift st1 = shift st /\ acount st1 = acount st) end.
  { destruct HTA as [(E & U1 & CX)|(E & U1 & mq & Est1)]; (split; [exact E|]); (split; [exact U1|]);
      unfold shift, acount, ctx; rewrite ?CX, ?Est1; autorewrite with mst; split; reflexivity. }
  clear HTA. ddestruct HTA' as (-> & U1 & S1 & C1). cbn [Z.eqb negb].
  cbv beta delta [alloc_group]. zeta1.
  (* [comment removed for export] *)
  match goal with |- sreach _ _ _ (alloc_meta _ ?K3 _) => set (KG := K3) end.
  assert (CONT : forall (c' : bool) st2 m, UND st2 -> (c' = true -> 0 <= shift st2 <= 13) -> (c' = false -> Z.of_nat f <= acount st2) ->
            sreach Q (B + RB c') (N + RN c')%nat (KG st2 (Some m))).
  { intros c' st2 m U2 SH2 CNT2. assert (HRB' : 0 <= B + RB c') by (unfold RB, GB, MA; destruct c'; lia).
    subst KG. cbv beta iota. zeta1. zeta1. zeta1. zeta1.
    pose proof (size_class_total sc) as Bsz.
    assert (Bcnt : 0 <= cnt <= 32).
    { subst cnt. destruct (sc <? 9); [pose proof (small_cnt_pick_total sc usage0); lia|].
      pose proof (med_cnt_total (Z.land sc 3)) as M1. pose proof (halve_even_total 8 (med_cnt (Z.land sc 3)) usage0 ltac:(lia)) as M2.
      pose proof (halve_big_total 8 (halve_even 8 (med_cnt (Z.land sc 3)) usage0) size ltac:(lia)). lia. }
    assert (Bcnt0 : 0 <= cnt0 <= 32) by (subst cnt0; destruct (_ && _); lia).
    pose proof (mul_bound size cnt0 (UNIT * 8191) 32 ltac:(subst size; unfold UNIT; lia) Bcnt0) as Bsc.
    lazymatch goal with |- sreach _ _ _ (if ?b then _ else _) => destruct b end.
    - (* [comment removed for export] *)
      zeta1. zeta1. zeta1. zeta1. zeta1.
      lazymatch goal with |- sreach _ _ _ (match ?p with _ => _ end) => destruct p as [cnt2 needed0] eqn:Ep end.
      assert (Hnd : 0 < needed0 /\ mmap_len needed0 <= GB).
      { assert (Bcnt1 : 0 <= cnt1 <= 32) by (subst cnt1; repeat (destruct (_ && _)); lia).
        pose proof (mul_bound size cnt1 (UNIT * 8191) 32 ltac:(subst size; unfold UNIT; lia) Bcnt1) as Bsc1.
        pose proof (round_up_pg_bound (size * cnt1 + UNIT)) as R1. pose proof (round_up_pg_bound (req + IB + UNIT)) as R2.
        assert (Hn0 : needed0 = needed \/ needed0 = round_up_pg (req + IB + UNIT)).
        { destruct (negb nosmall && (cnt1 <=? 7)); [cbv zeta in Ep; match type of Ep with context [if ?b then _ else _] => destruct b end|]; injection Ep as <- <-; auto. }
        assert (Hp : 0 < needed0 /\ needed0 + 4096 <= GB) by (subst needed; unfold UNIT, IB, GB in *; destruct Hn0 as [-> | ->]; lia).
        pose proof (mmap_len_bound needed0 ltac:(lia)). lia. }
      replace (B + RB c') with ((B + RB c') + 0) by lia. replace (N + RN c')%nat with ((N + RN c') + 0)%nat by lia.
      eapply (sr_vis Q _ _ _ _ 0 0%nat _ (ks_mmap_fail needed0 PROT_RW)); [exact HRB'|].
      intros z Hz. destruct (negb (mmap_answer_ok _ _ needed0 z)); [apply sreach_bad_answer; exact HRB'|].
      rewrite Hz. rewrite free_meta_eq. eapply sreach_mono; [apply HK| auto| unfold RB, GB, MA; destruct c'; lia| lia].
    - (* [comment removed for export] *)
      zeta1. apply IH; [lia| exact U2| exact SH2| exact CNT2| unfold UNIT, IB; lia| unfold UNIT, IB, GB in *; lia| exact HB|].
      intros st'. cbn [Z.ltb]. rewrite free_meta_eq. apply HK. }
  destruct c.
  - replace (B + RB true) with ((B + GB) + MA) by (unfold RB; lia). replace (N + RN true)%nat with ((N + 1) + 1)%nat by (unfold RN; lia).
    apply (alloc_meta_strat Q (B + GB) (N + 1)%nat st1 KG bail U1 ltac:(rewrite S1; apply SH; reflexivity) ltac:(unfold GB; lia)).
    + (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT true st2 m U2 ltac:(intros _; rewrite S2, S1; apply SH; reflexivity) ltac:(discriminate)) as X.
      unfold RB, RN in X. rewrite <- Z.add_assoc, <- Nat.add_assoc. exact X.
    + (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT false st2 m U2 ltac:(discriminate) ltac:(intros _; rewrite C2; unfold NSLOTS; lia)) as X.
      unfold RB, RN in X. rewrite ?Z.add_0_r, ?Nat.add_0_r in X. exact X.
  - cbn [RB RN]. rewrite ?Z.add_0_r, ?Nat.add_0_r.
    apply (alloc_meta_silent Q (B + GB) (N + 1)%nat st1 KG bail U1 ltac:(rewrite C1; specialize (CNT eq_refl); lia) ltac:(unfold GB; lia)).
    (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT false st2 m U2 ltac:(discriminate) ltac:(intros _; specialize (CNT eq_refl); rewrite <- C1 in CNT; lia)) as X.
    cbn [RB RN] in X. rewrite ?Z.add_0_r, ?Nat.add_0_r in X. exact X.
Qed.

#[using="Type"] Lemma ag_tail_queue B N st sc m p cnt ai (k : mstate -> Z -> M R) bail :
  0 <= B -> (forall st', sreach Q B N (k st' 0)) ->
  sreach Q B N (ag_tail lay_none st sc m p cnt ai (fun st2 go =>
     match go with
     | Some g => queue (LActive sc) g (upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2) (fun st4 => k st4 0) bail
     | None => k st2 (-1)
     end)).
Proof.
  intros HB HK. cbv beta delta [ag_tail]. cbn [lh_hdr lay_none]. cbv zeta. cbv beta iota.
  match goal with |- sreach _ _ _ (queue ?h ?g ?s ?kk ?bb) => destruct (queue_cases h g s kk bb) as [-> |(u & k' & ->)] end;
    [apply HK| constructor; exact HB].
Qed.

#[using="Type"] Lemma alloc_slot_ok f : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "Pc,$24.Pst,$16.Psc,$7.Preq,$7.Pk,P,$16.P,$7.(25.VR,)Pbail,(25.VR,)PB,$7.PN,$26.P,(27.O1.#40.)P,(14.R8.)P,P,(1.$24.R:.$28.)(0.(15.=(?.R:.))(15.(?.R:.)+=.))P,P,(1.$24.R;.$29.)(15.(2:.O1.)(10.R;.))P,(15.=R9.)P,(15.(1;.R:.+2014.)$2;.)P,(15.=R8.)P,Pst',$16.(18.VR,VQ,R:.R9.A2.R<.R1.=)(18.VR,VQ,(1;.R:.(2<.R10.))(1=.R9.(2=.R10.))(2>.VR,$2?.O1.R?.R>.R=.R<.R;.))")
(* [comment removed for export] *).
Proof.
  induction f as [|f IH]; intros c st sc req k bail B N Hf U SH CNT Hreq HreqB HB HK.
  { cbn [alloc_slot]. constructor. unfold RB, GB, MA; destruct c; lia. }
  assert (HRB : 0 <= B + RB c) by (unfold RB, GB, MA; destruct c; lia).
  cbn [alloc_slot].
  lazymatch goal with |- sreach _ _ _ (try_avail _ _ ?K _) =>
  destruct (try_avail_cases sc st K bail U) as [(st1 & HTA)|(u & k' & ->)] end.
  2:{ constructor. exact HRB. }
  lazymatch goal with |- sreach _ _ _ (try_avail _ _ ?K _) =>
    assert (HTA' : try_avail sc st K bail = K st1 0 /\ UND st1 /\ shift st1 = shift st /\ acount st1 = acount st) end.
  { destruct HTA as [(E & U1 & CX)|(E & U1 & mq & Est1)]; (split; [exact E|]); (split; [exact U1|]);
      unfold shift, acount, ctx; rewrite ?CX, ?Est1; autorewrite with mst; split; reflexivity. }
  clear HTA. ddestruct HTA' as (-> & U1 & S1 & C1). cbn [Z.eqb negb].
  cbv beta delta [alloc_group]. zeta1.
  match goal with |- sreach _ _ _ (alloc_meta _ ?K3 _) => set (KG := K3) end.
  assert (CONT : forall (c' : bool) st2 m, UND st2 -> (c' = true -> 0 <= shift st2 <= 13) -> (c' = false -> Z.of_nat f <= acount st2) ->
            sreach Q (B + RB c') (N + RN c')%nat (KG st2 (Some m))).
  { intros c' st2 m U2 SH2 CNT2. assert (HRB' : 0 <= B + RB c') by (unfold RB, GB, MA; destruct c'; lia).
    subst KG. cbv beta iota. zeta1. zeta1. zeta1. zeta1.
    pose proof (size_class_total sc) as Bsz.
    assert (Bcnt : 0 <= cnt <= 32).
    { subst cnt. destruct (sc <? 9); [pose proof (small_cnt_pick_total sc usage0); lia|].
      pose proof (med_cnt_total (Z.land sc 3)) as M1. pose proof (halve_even_total 8 (med_cnt (Z.land sc 3)) usage0 ltac:(lia)) as M2.
      pose proof (halve_big_total 8 (halve_even 8 (med_cnt (Z.land sc 3)) usage0) size ltac:(lia)). lia. }
    assert (Bcnt0 : 0 <= cnt0 <= 32) by (subst cnt0; destruct (_ && _); lia).
    pose proof (mul_bound size cnt0 (UNIT * 8191) 32 ltac:(subst size; unfold UNIT; lia) Bcnt0) as Bsc.
    lazymatch goal with |- sreach _ _ _ (if ?b then _ else _) => destruct b end.
    - (* [comment removed for export] *)
      zeta1. zeta1. zeta1. zeta1. zeta1.
      lazymatch goal with |- sreach _ _ _ (match ?p with _ => _ end) => destruct p as [cnt2 needed0] eqn:Ep end.
      assert (Hnd : 0 < needed0 /\ mmap_len needed0 <= GB).
      { assert (Bcnt1 : 0 <= cnt1 <= 32) by (subst cnt1; repeat (destruct (_ && _)); lia).
        pose proof (mul_bound size cnt1 (UNIT * 8191) 32 ltac:(subst size; unfold UNIT; lia) Bcnt1) as Bsc1.
        pose proof (round_up_pg_bound (size * cnt1 + UNIT)) as R1. pose proof (round_up_pg_bound (req + IB + UNIT)) as R2.
        assert (Hn0 : needed0 = needed \/ needed0 = round_up_pg (req + IB + UNIT)).
        { destruct (negb nosmall && (cnt1 <=? 7)); [cbv zeta in Ep; match type of Ep with context [if ?b then _ else _] => destruct b end|]; injection Ep as <- <-; auto. }
        assert (Hp : 0 < needed0 /\ needed0 + 4096 <= GB) by (subst needed; unfold UNIT, IB, GB in *; destruct Hn0 as [-> | ->]; lia).
        pose proof (mmap_len_bound needed0 ltac:(lia)). lia. }
      eapply (sreach_mono Q Q (B + (RB c' - GB) + mmap_len needed0) (N + (RN c' - 1) + 1)%nat); [| auto| unfold RB; destruct c'; lia| unfold RN; destruct c'; lia].
      eapply (sr_vis Q _ _ _ _ _ 1%nat _ (ks_mmap_ok needed0 PROT_RW ltac:(lia) ltac:(unfold GB in Hnd; lia))); [unfold RB, MA; destruct c'; lia|].
      intros z Hz. destruct (negb (mmap_answer_ok _ _ needed0 z)); [apply sreach_bad_answer; unfold RB, MA; destruct c'; lia|].
      rewrite Hz. destruct (new_region RKGroup z needed0 st0) as [st3 rid]. cbv zeta. unfold tail.
      eapply sreach_mono; [apply ag_tail_queue; [exact HB| exact HK]| auto| unfold RB, MA; destruct c'; lia| lia].
    - (* [comment removed for export] *)
      zeta1. apply IH; [lia| exact U2| exact SH2| exact CNT2| unfold UNIT, IB; lia| unfold UNIT, IB, GB in *; lia| exact HB|].
      intros st'. cbn [Z.ltb]. destruct (active st' j) as [g|]; [| constructor; exact HB]. cbv zeta. unfold tail.
      apply ag_tail_queue; [exact HB| exact HK]. }
  destruct c.
  - replace (B + RB true) with ((B + GB) + MA) by (unfold RB; lia). replace (N + RN true)%nat with ((N + 1) + 1)%nat by (unfold RN; lia).
    apply (alloc_meta_strat Q (B + GB) (N + 1)%nat st1 KG bail U1 ltac:(rewrite S1; apply SH; reflexivity) ltac:(unfold GB; lia)).
    + (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT true st2 m U2 ltac:(intros _; rewrite S2, S1; apply SH; reflexivity) ltac:(discriminate)) as X.
      unfold RB, RN in X. rewrite <- Z.add_assoc, <- Nat.add_assoc. exact X.
    + (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT false st2 m U2 ltac:(discriminate) ltac:(intros _; rewrite C2; unfold NSLOTS; lia)) as X.
      unfold RB, RN in X. rewrite ?Z.add_0_r, ?Nat.add_0_r in X. exact X.
  - cbn [RB RN]. rewrite ?Z.add_0_r, ?Nat.add_0_r.
    apply (alloc_meta_silent Q (B + GB) (N + 1)%nat st1 KG bail U1 ltac:(rewrite C1; specialize (CNT eq_refl); lia) ltac:(unfold GB; lia)).
    (intros st2 m dd_H; ddestruct dd_H as (U2 & S2 & C2)). pose proof (CONT false st2 m U2 ltac:(discriminate) ltac:(intros _; specialize (CNT eq_refl); rewrite <- C1 in CNT; lia)) as X.
    cbn [RB RN] in X. rewrite ?Z.add_0_r, ?Nat.add_0_r in X. exact X.
Qed.
End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TOP.
Context {R : Type}.

#[using="Type"] Lemma lowbit_0 : lowbit 0 = 0. Proof. reflexivity. Qed.

#[using="Type"] Lemma malloc_small_ctrl_fail (Q : R -> Prop) st n (k : mstate -> option (aptr * Z) -> M R) bail B N : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O6.)P,(0.(15.=(?.O6.))(15.(?.O6.)+=.))P,(15.=O5.)P,(15.(1;.O5.+2014.)$2;.)P,(15.=O2.)P,Pst',$16.(18.VR,O7.O2.O1.A2.O4.R1.(30.(31.$3.$7.)))(18.VR,O7.(1;.O2.(1;.$2;.$1<.))(1=.O1.#2.)(32.VR,$2?.O6.O5.O4.O3.))")
(* [comment removed for export] *).
Proof.
  intros U SH Hn HnB HB HK. cbv beta delta [malloc_small_ctrl]. zeta1. zeta1. zeta1. zeta1. zeta1.
  lazymatch goal with |- sreach _ _ _ (let first := lowbit ?mk in _) =>
    assert (Hmask : mk = 0) by (subst mk; lazymatch goal with |- match ?g0 with _ => _ end = 0 => destruct g0 as [gp|]; [apply (proj1 (U gp))| reflexivity] end);
    rewrite Hmask end.
  zeta1. lazymatch goal with H := lowbit 0 |- _ => subst H end. rewrite lowbit_0. cbn [Z.eqb negb].
  lazymatch goal with |- sreach _ _ _ (match ?g0 with _ => _ end) => rename g0 into gact end.
  assert (X : sreach Q (B + RB true) (N + RN true)%nat
    (alloc_slot lay_none FUEL st sc0 n (fun st1 idx => if idx <? 0 then k st1 None
        else match active st1 sc0 with Some gp => k st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail)).
  { apply alloc_slot_fail; [unfold FUEL; lia| exact U| intros _; exact SH| discriminate| exact Hn| exact HnB| exact HB|].
    intros st'. cbn [Z.ltb]. apply HK. }
  unfold RB, RN in X. cbn [Nat.add] in X. destruct gact; exact X.
Qed.

#[using="Type"] Lemma malloc_small_ctrl_ok (Q : R -> Prop) st n (k : mstate -> option (aptr * Z) -> M R) bail B N : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O6.)P,(0.(15.=(?.O6.))(15.(?.O6.)+=.))P,(15.=O5.)P,(15.(1;.O5.+2014.)$2;.)P,(15.=O2.)P,Pst',$16.Pg,$3.Pidx,$7.(18.VR,O7.O2.O1.A2.O4.R3.(19.(31.$3.$7.)(33.$3.$7.R2.R1.)))(18.VR,O7.(1;.O2.(1;.$2;.$1<.))(1=.O1.#2.)(32.VR,$2?.O6.O5.O4.O3.))")
(* [comment removed for export] *).
Proof.
  intros U SH Hn HnB HB HK. cbv beta delta [malloc_small_ctrl]. zeta1. zeta1. zeta1. zeta1. zeta1.
  lazymatch goal with |- sreach _ _ _ (let first := lowbit ?mk in _) =>
    assert (Hmask : mk = 0) by (subst mk; lazymatch goal with |- match ?g0 with _ => _ end = 0 => destruct g0 as [gp|]; [apply (proj1 (U gp))| reflexivity] end);
    rewrite Hmask end.
  zeta1. lazymatch goal with H := lowbit 0 |- _ => subst H end. rewrite lowbit_0. cbn [Z.eqb negb].
  lazymatch goal with |- sreach _ _ _ (match ?g0 with _ => _ end) => rename g0 into gact end.
  assert (X : sreach Q (B + RB true) (N + RN true)%nat
    (alloc_slot lay_none FUEL st sc0 n (fun st1 idx => if idx <? 0 then k st1 None
        else match active st1 sc0 with Some gp => k st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail)).
  { apply alloc_slot_ok; [unfold FUEL; lia| exact U| intros _; exact SH| discriminate| exact Hn| exact HnB| exact HB|].
    intros st'. cbn [Z.ltb]. destruct (active st' sc0); [apply HK| constructor; exact HB]. }
  unfold RB, RN in X. cbn [Nat.add] in X. destruct gact; exact X.
Qed.

End TOP.

Definition QF (r : mstate * option cptr) : Prop := snd r = None.
Definition QS (r : mstate * option cptr) : Prop := snd r <> None.

Lemma size_overflows_small n : n < 2 ^ 62 -> size_overflows n = false.
Proof. intros. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Theorem cmalloc_sreach_fail cs n : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O2.)P,(0.(15.=(?.O2.))(15.(?.O2.)+=.))P,(15.=O1.)P,(15.(1;.O1.+2014.)$2;.)(18.(31.$16.(34.$35.))$36.(1;.$2;.$1<.)#2.(37.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U SH Hn HnB. unfold cmalloc.
  replace (GB + MA) with ((GB + MA) + 0) by lia. replace 2%nat with (2 + 0)%nat by lia.
  eapply (sreach_bind (fun r : mstate * option (aptr * Z) => snd r = None)); [| lia|].
  2:{ (intros dd_H; ddestruct dd_H as [st1 [[g idx]|]]; intros Hr); cbn in Hr; [discriminate|]. constructor; [reflexivity| lia]. }
  unfold malloc_core. rewrite size_overflows_small by (unfold GB in HnB; lia).
  destruct (MMAP_THRESHOLD <=? n).
  - replace (GB + MA) with ((GB + MA) + 0) by lia. replace 2%nat with (2 + 0)%nat by lia.
    eapply (sr_vis _ _ _ _ _ 0 0%nat _ (ks_mmap_fail (n + IB + UNIT) PROT_RW)); [unfold GB, MA; lia|].
    intros z Hz. destruct (negb (mmap_answer_ok _ _ _ z)); [apply sreach_bad_answer; unfold GB, MA; lia|].
    rewrite Hz. constructor; [reflexivity| unfold GB, MA; lia].
  - replace (GB + MA) with (0 + (GB + MA)) by lia. change 2%nat with (0 + 2)%nat.
    apply malloc_small_ctrl_fail; auto; [lia|]. intros st'. constructor; [reflexivity| lia].
Qed.

Theorem cmalloc_sreach_ok cs n : ltac2:(CDefT.buildp (gd_tbl_MStrat ()) "P,(14.O2.)P,(0.(15.=(?.O2.))(15.(?.O2.)+=.))P,(15.=O1.)P,(15.(1;.O1.+2014.)$2;.)(18.(31.$16.(34.$35.))$38.(1;.$2;.$1<.)#2.(37.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros U SH Hn HnB. unfold cmalloc.
  replace (GB + MA) with ((GB + MA) + 0) by lia. replace 2%nat with (2 + 0)%nat by lia.
  eapply (sreach_bind (fun r : mstate * option (aptr * Z) => snd r <> None)); [| lia|].
  2:{ (intros dd_H; ddestruct dd_H as [st1 [[g idx]|]]; intros Hr); cbn in Hr; [| congruence]. constructor; [unfold QS; cbn [snd]; discriminate| lia]. }
  unfold malloc_core. rewrite size_overflows_small by (unfold GB in HnB; lia).
  destruct (MMAP_THRESHOLD <=? n).
  - pose proof (mmap_len_bound (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as Hml.
    apply (sreach_mono (fun r : mstate * option (aptr * Z) => snd r <> None) _ ((0 + MA) + mmap_len (n + IB + UNIT)) ((0 + 1) + 1)%nat); [| auto| unfold GB, IB, UNIT in *; lia| lia].
    eapply (sr_vis _ _ _ _ _ _ 1%nat _ (ks_mmap_ok (n + IB + UNIT) PROT_RW ltac:(unfold IB, UNIT; lia) ltac:(unfold GB, IB, UNIT in *; lia))); [unfold MA; lia|].
    intros z Hz. destruct (negb (mmap_answer_ok _ _ _ z)); [apply sreach_bad_answer; unfold MA; lia|].
    rewrite Hz. destruct (new_region RKGroup z (n + IB + UNIT) cs) as [st1 rid] eqn:Enr. cbv zeta.
    apply alloc_meta_strat.
    + apply (UND_metas cs); [| exact U]. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1. unfold step_seq. destruct (c_seq _ =? 255); reflexivity.
    + apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1. unfold shift, ctx in *. unfold step_seq. destruct (c_seq _ =? 255); cbn -[Z.add Z.mul Z.sub]; exact SH.
    + lia.
    + intros st3 m _. cbv beta iota zeta. apply sr_ret; [cbn [snd]; discriminate| unfold MA; lia].
    + intros st3 m _. cbv beta iota zeta. apply sr_ret; [cbn [snd]; discriminate| lia].
  - replace (GB + MA) with (0 + (GB + MA)) by lia. change 2%nat with (0 + 2)%nat.
    apply malloc_small_ctrl_ok; auto; [lia|]. intros st' g idx. constructor; [unfold QS; cbn [snd]; discriminate| lia].
Qed.
