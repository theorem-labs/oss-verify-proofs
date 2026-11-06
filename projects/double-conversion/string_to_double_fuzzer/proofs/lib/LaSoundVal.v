(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem LaStep LaCheck LaSem LaWf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF.
Open Scope Z_scope.

Module LASV.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma two64z_eq : two64z = 2 ^ 64. Proof. reflexivity. Qed.
Lemma two63z_eq : two63z = 2 ^ 63. Proof. reflexivity. Qed.
Lemma two64_eq : LXL.two64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma two63_eq : LXL.two63 = 2 ^ 63. Proof. reflexivity. Qed.
Lemma two32_eq : LXL.two32 = 2 ^ 32. Proof. reflexivity. Qed.
Lemma two31_eq : LXL.two31 = 2 ^ 31. Proof. reflexivity. Qed.

Lemma w64_eq_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> w64 a = w64 b.
Proof. intros a b H. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. exact H. Qed.

Lemma w64_unsigned : forall a, bv_unsigned (w64 a) = a mod 2 ^ 64.
Proof. intros. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.

Lemma w64_of_unsigned : forall w : word, w64 (bv_unsigned w) = w.
Proof. intros. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma snorm_mod : forall k, snorm k mod 2 ^ 64 = k mod 2 ^ 64.
Proof.
  intros k. unfold snorm. rewrite two64z_eq.
  destruct (Z.leb (- two63z) k &&& Z.ltb k two63z)%bool; [reflexivity|].
  destruct (Z.leb two63z (k mod 2 ^ 64)) eqn:E.
  - replace (k mod 2 ^ 64 - 2 ^ 64) with (k mod 2 ^ 64 + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
  - apply Z.mod_mod. lia.
Qed.

Lemma w64_snorm : forall k, w64 (snorm k) = w64 k.
Proof. intros. apply w64_eq_mod. apply snorm_mod. Qed.

Lemma alit_ok : forall rho z, val_ok rho (alit z) (w64 z).
Proof. intros. unfold alit, val_ok. rewrite lconst_sound. symmetry. apply w64_snorm. Qed.

Lemma alit_ok' : forall rho z w, w = w64 z -> val_ok rho (alit z) w.
Proof. intros; subst; apply alit_ok. Qed.

Lemma aval_lit_sound : forall rho v z w, aval_lit v = Some z -> val_ok rho v w -> w = w64 z.
Proof.
  intros rho v z w H Hv. destruct v as [|l| |]; cbn in H; try discriminate.
  cbn in Hv. rewrite (is_const_sound rho l z H) in Hv. exact Hv.
Qed.

Lemma alit_below : forall z n, aval_below (alit z) n = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma uexact_unsigned : forall rho C l w, ctx_ok rho C -> uexact C l = true -> w = w64 (evl rho l) -> bv_unsigned w = evl rho l.
Proof.
  intros rho C l w HC Hu Hw. subst. rewrite w64_unsigned.
  pose proof (in_range_sound rho C l 0 LXL.two64 HC Hu). rewrite two64_eq in H. apply Z.mod_small. lia.
Qed.
Lemma sexact_signed : forall rho C l w, ctx_ok rho C -> sexact C l = true -> w = w64 (evl rho l) -> bv_signed w = evl rho l.
Proof.
  intros rho C l w HC Hs Hw. subst. unfold w64. rewrite Z_to_bv_signed.
  pose proof (in_range_sound rho C l (- LXL.two63) LXL.two63 HC Hs). rewrite two63_eq in H.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 64) with (2 ^ 63). rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VS (rho : valuation) (st : astate) : Prop :=
  ctx_ok rho (s_ctx st) /\ ctx_below (s_ctx st) (s_next st) = true.

Definition vext (rho : valuation) (st : astate) (rho' : valuation) (st' : astate) : Prop :=
  agree (s_next st) rho rho' /\ (s_next st <= s_next st')%nat /\
  s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_stk st' = s_stk st /\ s_arrs st' = s_arrs st /\
  s_abs st' = s_abs st /\ s_resv st' = s_resv st /\ s_depth st' = s_depth st /\ s_pcache st' = s_pcache st /\ s_pay st' = s_pay st /\
  s_frames st' = s_frames st.

Lemma vext_refl : forall rho st, vext rho st rho st.
Proof. intros. unfold vext. repeat split; auto using agree_refl. Qed.

(* [comment removed for export] *)
Lemma gc_facts_vext : forall rho st, vext rho st rho (gc_facts st).
Proof.
  intros rho st. pose proof (LAWF.gc_facts_same st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _ & E12).
  unfold vext. rewrite E3. repeat split; auto using agree_refl.
Qed.
Lemma gc_facts_VS : forall rho st, VS rho st -> VS rho (gc_facts st).
Proof.
  intros rho st [H1 H2]. split; [apply LAWF.gc_facts_ctx_ok; exact H1|].
  pose proof (LAWF.gc_facts_same st) as (_ & _ & E3 & _). rewrite E3. apply LAWF.gc_facts_ctx_below. exact H2.
Qed.

Lemma vext_trans : forall rho st rho' st' rho'' st'',
  vext rho st rho' st' -> vext rho' st' rho'' st'' -> vext rho st rho'' st''.
Proof.
  intros rho st rho' st' rho'' st'' (A1 & N1 & P1 & R1 & S1 & Ar1 & Ab1 & Rv1 & D1 & Pc1 & Py1 & F1) (A2 & N2 & P2 & R2 & S2 & Ar2 & Ab2 & Rv2 & D2 & Pc2 & Py2 & F2).
  unfold vext. repeat split; try congruence; [|lia].
  eapply agree_trans; [exact N1 | exact A1 | exact A2].
Qed.

Lemma evalt_agree : forall n rho rho' ts, tsyms_below ts n = true -> agree n rho rho' -> evalt rho' ts = evalt rho ts.
Proof.
  intros n rho rho' ts. induction ts as [|[x k] r IH]; cbn -[Z.add Z.mul Nat.ltb]; intros Hb Ha; [reflexivity|].
  apply andb_prop in Hb as [Hx Hr]. apply Nat.ltb_lt in Hx. rewrite (Ha x Hx), IH; auto.
Qed.
Lemma evl_agree : forall n rho rho' l, lin_below l n = true -> agree n rho rho' -> evl rho' l = evl rho l.
Proof. intros. unfold evl. rewrite (evalt_agree n rho rho') by assumption. reflexivity. Qed.

Lemma val_ok_agree : forall n rho rho' v w, aval_below v n = true -> agree n rho rho' -> val_ok rho v w -> val_ok rho' v w.
Proof.
  intros n rho rho' v w Hb Ha Hv. destruct v as [|l|neg k a b|a b]; cbn in *; [exact I| | |].
  - rewrite (evl_agree n rho rho') by assumption. exact Hv.
  - apply andb_prop in Hb as [Hba Hbb]. unfold cmp_holds in *.
    rewrite !(evl_agree n rho rho') by assumption. exact Hv.
  - apply andb_prop in Hb as [Hba Hbb]. rewrite !(evl_agree n rho rho') by assumption. exact Hv.
Qed.

Lemma ctx_ok_agree : forall n rho rho' C, ctx_below C n = true -> agree n rho rho' -> ctx_ok rho C -> ctx_ok rho' C.
Proof.
  intros n rho rho' C Hb Ha [HF HB]. unfold ctx_below in Hb. apply andb_prop in Hb as [HbF HbB].
  rewrite forallb_forall in HbF, HbB. split.
  - apply Forall_forall. intros f Hf. rewrite (evl_agree n rho rho'); auto. exact (proj1 (Forall_forall _ _) HF f Hf).
  - intros x. destruct (Nat.lt_ge_cases x n) as [Hx|Hx].
    + rewrite (Ha x Hx). apply HB.
    + (* [comment removed for export] *)
      assert (Hk : forall b, (forall y, In y (map fst b) -> (y < n)%nat) -> bget b x = itop).
      { induction b as [|[y i] r IH]; cbn; intros Hy; [reflexivity|].
        destruct (Nat.eqb_spec x y); [exfalso; specialize (Hy y (or_introl eq_refl)); lia|].
        apply IH. intros z Hz. apply Hy. right; exact Hz. }
      rewrite Hk; [apply itop_sound|]. intros y Hy. apply in_map_iff in Hy as ([y' i] & <- & Hin).
      specialize (HbB _ Hin). cbn in HbB. apply Nat.ltb_lt in HbB. exact HbB.
Qed.

(* [comment removed for export] *)
Lemma fresh_sound : forall rho st i v,
  VS rho st -> in_itv v i ->
  exists rho', rho' (s_next st) = v /\ vext rho st rho' (snd (fresh st i)) /\ VS rho' (snd (fresh st i))
              /\ fst (fresh st i) = s_next st /\ s_next (snd (fresh st i)) = S (s_next st).
Proof.
  intros rho st i v [HC HB] Hi.
  set (x := s_next st). set (rho' := fun y => if Nat.eqb y x then v else rho y).
  assert (Ha : agree x rho rho').
  { intros y Hy. unfold rho'. destruct (Nat.eqb_spec y x); [subst; lia|reflexivity]. }
  exists rho'. split; [unfold rho'; rewrite Nat.eqb_refl; reflexivity|].
  split; [|split; [split|split; reflexivity]].
  - unfold vext; cbn. repeat split; auto.
  - (* [comment removed for export] *)
    pose proof (ctx_ok_agree x rho rho' _ HB Ha HC) as HC'.
    apply set_bound_sound; [exact HC'|]. unfold rho'; rewrite Nat.eqb_refl. exact Hi.
  - cbn. apply set_bound_below; [eapply ctx_below_mono; [|exact HB]; lia | lia].
Qed.

Lemma fresh_val_sound : forall rho st i v,
  VS rho st -> in_itv v i ->
  exists rho', vext rho st rho' (snd (fresh_val st i)) /\ VS rho' (snd (fresh_val st i))
              /\ val_ok rho' (fst (fresh_val st i)) (w64 v)
              /\ aval_below (fst (fresh_val st i)) (s_next (snd (fresh_val st i))) = true.
Proof.
  intros rho st i v HVS Hi.
  destruct (fresh_sound rho st i v HVS Hi) as (rho' & Hx & Hext & HVS' & Hfst & Hnext).
  unfold fresh_val. destruct (fresh st i) as [x st'] eqn:E. cbn in *. subst x.
  exists rho'. split; [exact Hext|]. split; [exact HVS'|]. split.
  - cbn. rewrite lvar_sound, Hx. reflexivity.
  - rewrite Hnext. change (lin_below (lvar (s_next st)) (S (s_next st)) = true). apply lvar_below. lia.
Qed.

(* [comment removed for export] *)
Lemma learn_sound : forall rho st l,
  VS rho st -> lin_below l (s_next st) = true -> 0 <= evl rho l ->
  vext rho st rho (learn st l) /\ VS rho (learn st l).
Proof.
  intros rho st l [HC HB] Hl Hpos. split.
  - unfold vext, learn; cbn. repeat split; auto using agree_refl.
  - split; cbn; [apply add_fact_sound; assumption | apply add_fact_below; assumption].
Qed.

Lemma learn_eq_sound : forall rho st l,
  VS rho st -> lin_below l (s_next st) = true -> evl rho l = 0 ->
  vext rho st rho (learn_eq st l) /\ VS rho (learn_eq st l).
Proof.
  intros rho st l HVS Hl H0. unfold learn_eq.
  destruct (learn_sound rho st l HVS Hl ltac:(lia)) as [E1 V1].
  destruct (learn_sound rho (learn st l) (lneg l) V1 ltac:(cbn; apply lneg_below; exact Hl) ltac:(rewrite lneg_sound; lia)) as [E2 V2].
  split; [eapply vext_trans; eauto | exact V2].
Qed.

Lemma learn_all_sound : forall rho ls st,
  VS rho st -> Forall (fun l => lin_below l (s_next st) = true /\ 0 <= evl rho l) ls ->
  vext rho st rho (learn_all st ls) /\ VS rho (learn_all st ls).
Proof.
  intros rho ls. induction ls as [|l r IH]; intros st HVS HF; cbn.
  - split; [apply vext_refl | exact HVS].
  - apply Forall_cons_iff in HF as [[Bl Hl] Hr].
    destruct (learn_sound rho st l HVS Bl Hl) as [E1 V1].
    assert (N1 : s_next (learn st l) = s_next st) by reflexivity.
    destruct (IH (learn st l) V1 ltac:(rewrite N1; exact Hr)) as [E2 V2].
    split; [eapply vext_trans; [exact E1 | exact E2] | exact V2].
Qed.

Lemma link_facts_sound : forall rho rho' n0 C nb k x y b,
  ctx_ok rho C -> agree n0 rho rho' -> lin_below x n0 = true -> lin_below y n0 = true ->
  rho' b = (if xorb nb (cmp_holds rho k x y) then 1 else 0) ->
  Forall (fun l => 0 <= evl rho' l) (link_facts C nb k x y b).
Proof.
  intros rho rho' n0 C nb k x y b HC AG Bx By Hb.
  assert (EX : evl rho' x = evl rho x) by (eapply evl_agree; eauto).
  assert (EY : evl rho' y = evl rho y) by (eapply evl_agree; eauto).
  unfold link_facts.
  set (e := if nb then laddc (lneg (lvar b)) 1 else lvar b).
  assert (He : evl rho' e = (if cmp_holds rho k x y then 1 else 0)).
  { subst e. destruct nb; [rewrite laddc_sound, lneg_sound, lvar_sound, Hb | rewrite lvar_sound, Hb]; destruct (cmp_holds rho k x y); reflexivity. }
  set (ne := laddc (lneg e) 1).
  assert (Hne : evl rho' ne = 1 - (if cmp_holds rho k x y then 1 else 0)).
  { subst ne. rewrite laddc_sound, lneg_sound, He. lia. }
  destruct k.
  - (* [comment removed for export] *) cbn [cmp_holds] in He, Hne.
    pose proof (lrange_ok rho C (lsub y x) HC) as [R1 R2].
    destruct (lrange C (lsub y x)) as [lo hi]. cbn in R1, R2. rewrite lsub_sound in R1, R2.
    apply Forall_app; split.
    + destruct lo as [l0|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, laddc_sound, lscale_sound, lsub_sound, EX, EY, Hne.
      destruct (Z.ltb_spec (evl rho x) (evl rho y)); lia.
    + destruct hi as [h|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, lscale_sound, lsub_sound, EX, EY, He.
      destruct (Z.ltb_spec (evl rho x) (evl rho y)); lia.
  - (* [comment removed for export] *) cbn [cmp_holds] in He, Hne.
    pose proof (lrange_ok rho C (lsub y x) HC) as [R1 R2].
    destruct (lrange C (lsub y x)) as [lo hi]. cbn in R1, R2. rewrite lsub_sound in R1, R2.
    apply Forall_app; split.
    + destruct lo as [l0|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, laddc_sound, lscale_sound, lsub_sound, EX, EY, Hne.
      destruct (Z.ltb_spec (evl rho x) (evl rho y)); lia.
    + destruct hi as [h|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, lscale_sound, lsub_sound, EX, EY, He.
      destruct (Z.ltb_spec (evl rho x) (evl rho y)); lia.
  - (* [comment removed for export] *) cbn [cmp_holds] in He, Hne.
    destruct (in_range C (lsub x y) (1 - two64) two64) eqn:IR; [|constructor].
    pose proof (in_range_sound rho C _ _ _ HC IR) as RG. rewrite lsub_sound in RG. unfold two64, LXL.two64 in RG.
    pose proof (lrange_ok rho C (lsub x y) HC) as [R1 R2].
    destruct (lrange C (lsub x y)) as [lo hi]. cbn in R1, R2. rewrite lsub_sound in R1, R2.
    rewrite two64z_eq in He, Hne.
    assert (CEQ : Z.eqb (evl rho x mod 2 ^ 64) (evl rho y mod 2 ^ 64) = Z.eqb (evl rho x - evl rho y) 0).
    { destruct (Z.eqb_spec (evl rho x - evl rho y) 0) as [E0|NE].
      - apply Z.eqb_eq. f_equal. lia.
      - apply Z.eqb_neq. intros EQ.
        assert (HM : (evl rho x - evl rho y) mod 2 ^ 64 = 0).
        { rewrite Zminus_mod, EQ, Z.sub_diag. reflexivity. }
        apply Z.mod_divide in HM as [q Hq]; [|lia]. assert (q = 0) by nia. subst q. lia. }
    rewrite CEQ in He, Hne.
    repeat (apply Forall_app; split).
    + destruct hi as [h|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, lscale_sound, lsub_sound, EX, EY, Hne. destruct (Z.eqb_spec (evl rho x - evl rho y) 0); nia.
    + destruct lo as [l0|]; [|constructor]. constructor; [|constructor].
      rewrite lsub_sound, lsub_sound, lscale_sound, EX, EY, Hne. destruct (Z.eqb_spec (evl rho x - evl rho y) 0); nia.
    + destruct lo as [l0|]; [|constructor]. destruct (Z.leb_spec 0 l0); [|constructor]. constructor; [|constructor].
      rewrite ladd_sound, laddc_sound, lsub_sound, EX, EY, He. destruct (Z.eqb_spec (evl rho x - evl rho y) 0); lia.
    + destruct hi as [h|]; [|constructor]. destruct (Z.leb_spec h 0); [|constructor]. constructor; [|constructor].
      rewrite ladd_sound, laddc_sound, lneg_sound, lsub_sound, EX, EY, He. destruct (Z.eqb_spec (evl rho x - evl rho y) 0); lia.
Qed.


Lemma learn_all_next : forall st ls, s_next (learn_all st ls) = s_next st.
Proof. intros st ls. revert st. induction ls as [|l r IH]; intros st; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma link_facts_below : forall C nb k x y b n,
  lin_below x n = true -> lin_below y n = true -> (b < n)%nat ->
  forall l, In l (link_facts C nb k x y b) -> lin_below l n = true.
Proof.
  intros C nb k x y b n Bx By Hb l Hin. unfold link_facts in Hin.
  assert (Be : lin_below (if nb then laddc (lneg (lvar b)) 1 else lvar b) n = true).
  { destruct nb; [apply laddc_below; apply lneg_below|]; apply lvar_below; exact Hb. }
  assert (Bne : lin_below (laddc (lneg (if nb then laddc (lneg (lvar b)) 1 else lvar b)) 1) n = true).
  { apply laddc_below; apply lneg_below; exact Be. }
  destruct k;
    repeat match goal with
    | H : In _ (match ?c with _ => _ end) |- _ => destruct c
    | H : In _ (if ?c then _ else _) |- _ => destruct c
    | H : In _ (_ ++ _) |- _ => apply in_app_iff in H as [H|H]
    | H : In _ [_] |- _ => destruct H as [<-|[]]
    | H : In _ [] |- _ => destruct H
    end;
    repeat first [ apply lsub_below | apply ladd_below | apply laddc_below | apply lscale_below | apply lneg_below | exact Bx | exact By | exact Be | exact Bne ].
Qed.

(* [comment removed for export] *)
Lemma bool_fresh_sound : forall rho st (facts : sym -> list lin) (v : Z) (w : word),
  VS rho st -> 0 <= v <= 1 -> w = w64 v ->
  (forall rho', rho' (s_next st) = v -> agree (s_next st) rho rho' ->
      Forall (fun l => lin_below l (S (s_next st)) = true /\ 0 <= evl rho' l) (facts (s_next st))) ->
  exists rho', let p := (let (r, st1) := fresh st (Itv (Some 0) (Some 1)) in (LV (lvar r), learn_all st1 (facts r))) in
     vext rho st rho' (snd p) /\ VS rho' (snd p) /\ val_ok rho' (fst p) w /\ aval_below (fst p) (s_next (snd p)) = true.
Proof.
  intros rho st facts v w HVS Hv Hw HF.
  destruct (fresh_sound rho st (Itv (Some 0) (Some 1)) v HVS ltac:(unfold in_itv; cbn; lia)) as (rho' & Hx & Hext & HVS' & Hfst & Hnext).
  destruct (fresh st (Itv (Some 0) (Some 1))) as [r st1] eqn:Hfr. cbn [fst snd] in Hfst, Hnext, Hext, HVS' |- *. subst r.
  pose proof (HF rho' Hx (proj1 Hext)) as LB. rewrite <- Hnext in LB.
  destruct (learn_all_sound rho' _ st1 HVS' LB) as [E2 V2].
  exists rho'. split; [eapply vext_trans; [exact Hext | exact E2]|]. split; [exact V2|]. split.
  - cbn. rewrite lvar_sound, Hx, Hw. reflexivity.
  - cbn [aval_below]. rewrite learn_all_next, Hnext. apply lvar_below. lia.
Qed.

(* [comment removed for export] *)
Lemma log2_up_bound : forall a h, 0 <= a <= h -> a < 2 ^ Z.log2_up (h + 1).
Proof.
  intros a h H. destruct (Z.eq_dec h 0) as [->|Hn]; [change (2 ^ Z.log2_up (0 + 1)) with 1; lia|].
  pose proof (Z.log2_up_spec (h + 1) ltac:(lia)) as [_ H2]. lia.
Qed.
Lemma lt_pow2_of_log2 : forall x k, 0 <= k -> 0 < x -> Z.log2 x < k -> x < 2 ^ k.
Proof.
  intros x k Hk Hx H. pose proof (Z.log2_spec x Hx) as [_ H2].
  eapply Z.lt_le_trans; [exact H2|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma log2_lt_of_lt_pow2 : forall x k, 0 <= k -> 0 < x -> x < 2 ^ k -> Z.log2 x < k.
Proof.
  intros x k Hk Hx H. pose proof (Z.log2_spec x Hx) as [H1 _].
  destruct (Z.lt_ge_cases (Z.log2 x) k); [assumption|].
  exfalso. assert (2 ^ k <= 2 ^ Z.log2 x) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma lxor_below_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> Z.lxor a b <= 2 ^ k - 1.
Proof.
  intros a b k Ha Hb. destruct (Z.lt_ge_cases k 0) as [Hk|Hk]; [rewrite Z.pow_neg_r in Ha by lia; lia|].
  enough (Z.lxor a b < 2 ^ k) by lia.
  destruct (Z.eq_dec a 0) as [->|Haz]; [rewrite Z.lxor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hbz]; [rewrite Z.lxor_0_r; lia|].
  pose proof (proj2 (Z.lxor_nonneg a b) ltac:(split; intros; lia)) as Hnn.
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|Hnz]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply lt_pow2_of_log2; [lia | lia |].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt; apply log2_lt_of_lt_pow2; lia.
Qed.
Lemma lor_below_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> Z.lor a b <= 2 ^ k - 1.
Proof.
  intros a b k Ha Hb. destruct (Z.lt_ge_cases k 0) as [Hk|Hk]; [rewrite Z.pow_neg_r in Ha by lia; lia|].
  enough (Z.lor a b < 2 ^ k) by lia.
  destruct (Z.eq_dec a 0) as [->|Haz]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hbz]; [rewrite Z.lor_0_r; lia|].
  assert (Hnn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (Hnz : Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia).
  apply lt_pow2_of_log2; [lia | lia |].
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply log2_lt_of_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma val_ok_01 : forall rho neg k a b w,
  val_ok rho (CV neg k a b) w -> exists z, w = w64 z /\ 0 <= z <= 1.
Proof.
  intros rho neg k a b w Hv. cbn in Hv. exists (if xorb neg (cmp_holds rho k a b) then 1 else 0).
  split; [exact Hv|]. destruct (xorb _ _); lia.
Qed.

Lemma degrade_sound : forall rho st v w,
  VS rho st -> val_ok rho v w -> aval_below v (s_next st) = true ->
  exists rho', vext rho st rho' (snd (degrade st v)) /\ VS rho' (snd (degrade st v))
              /\ val_ok rho' (fst (degrade st v)) w /\ aval_below (fst (degrade st v)) (s_next (snd (degrade st v))) = true.
Proof.
  intros rho st v w HVS Hv Hb. unfold degrade. destruct v as [|l|neg k a b|a b].
  - destruct (fresh_val_sound rho st itv_u64 (bv_unsigned w) HVS) as (rho' & Hext & HVS' & Hval & Hbel).
    { pose proof (u64_range w). unfold itv_u64, in_itv; cbn. unfold two64, LXL.two64. lia. }
    exists rho'. split; [exact Hext|]. split; [exact HVS'|]. split; [rewrite w64_of_unsigned in Hval; exact Hval | exact Hbel].
  - exists rho. cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [exact Hv|]. exact Hb.
  - destruct (val_ok_01 rho neg k a b w Hv) as (z & Hw & Hz).
    cbn in Hv. cbn [aval_below] in Hb. apply andb_prop in Hb as [Ba Bb].
    destruct (fresh_sound rho st (Itv (Some 0) (Some 1)) z HVS ltac:(unfold in_itv; cbn; lia)) as (rho' & Hx & Hext & HVS' & Hfst & Hnext).
    destruct (fresh st (Itv (Some 0) (Some 1))) as [bx st1] eqn:Hfr. cbn [fst snd] in Hfst, Hnext, Hext, HVS' |- *. subst bx.
    assert (AG : agree (s_next st) rho rho') by exact (proj1 Hext).
    assert (Hz' : z = (if xorb neg (cmp_holds rho k a b) then 1 else 0)).
    { rewrite Hw in Hv. pose proof (f_equal bv_unsigned Hv) as U. rewrite !w64_unsigned in U.
      rewrite Z.mod_small in U by lia. rewrite Z.mod_small in U by (destruct (xorb _ _); lia). exact U. }
    pose proof (link_facts_sound rho rho' (s_next st) (s_ctx st) neg k a b (s_next st) (proj1 HVS) AG Ba Bb ltac:(rewrite Hx; exact Hz')) as LF.
    assert (LB : Forall (fun l => lin_below l (s_next st1) = true /\ 0 <= evl rho' l) (link_facts (s_ctx st) neg k a b (s_next st))).
    { apply Forall_forall. intros l Hin. split; [| exact (proj1 (Forall_forall _ _) LF l Hin)].
      rewrite Hnext. apply (link_facts_below (s_ctx st) neg k a b (s_next st) (S (s_next st))); [ | | | exact Hin].
      - eapply lin_below_mono; [|exact Ba]. idtac "G1"; match goal with |- ?g => idtac g end. lia.
      - eapply lin_below_mono; [|exact Bb]. lia.
      - idtac "G3"; match goal with |- ?g => idtac g end. lia. }
    destruct (learn_all_sound rho' _ st1 HVS' LB) as [E2 V2].
    exists rho'. cbn [fst snd]. split; [eapply vext_trans; [exact Hext | exact E2]|]. split; [exact V2|]. split.
    + cbn. rewrite lvar_sound, Hx, Hw, Hz'. reflexivity.
    + cbn [aval_below]. erewrite learn_all_next, Hnext. apply lvar_below. lia.
  - (* [comment removed for export] *)
    cbn in Hv. apply andb_prop in Hb as [Ba Bb].
    assert (GEN : forall i, in_itv (bv_unsigned w) i ->
              exists rho', vext rho st rho' (snd (fresh_val st i)) /\ VS rho' (snd (fresh_val st i)) /\
                          val_ok rho' (fst (fresh_val st i)) w /\ aval_below (fst (fresh_val st i)) (s_next (snd (fresh_val st i))) = true).
    { intros i Hi. destruct (fresh_val_sound rho st i (bv_unsigned w) HVS Hi) as (rho' & Hext & HVS' & Hval & Hbel).
      exists rho'. split; [exact Hext|]. split; [exact HVS'|]. split; [rewrite w64_of_unsigned in Hval; exact Hval | exact Hbel]. }
    destruct (ihi (lrange (s_ctx st) a)) as [ha|] eqn:Eha; [|apply GEN; apply itop_sound].
    destruct (ihi (lrange (s_ctx st) b)) as [hb|] eqn:Ehb; [|apply GEN; apply itop_sound].
    destruct (uexact (s_ctx st) a &&& uexact (s_ctx st) b &&& Z.leb 0 ha &&& Z.leb 0 hb)%bool eqn:E; [|apply GEN; apply itop_sound].
    apply GEN. apply andb_prop in E as [E Hhb]. apply andb_prop in E as [E Hha]. apply andb_prop in E as [Ua Ub].
    apply Z.leb_le in Hha. apply Z.leb_le in Hhb.
    pose proof (uexact_unsigned rho _ a _ (proj1 HVS) Ua eq_refl) as Hua.
    pose proof (uexact_unsigned rho _ b _ (proj1 HVS) Ub eq_refl) as Hub.
    pose proof (lrange_ok rho (s_ctx st) a (proj1 HVS)) as [_ Ha2]. rewrite Eha in Ha2.
    pose proof (lrange_ok rho (s_ctx st) b (proj1 HVS)) as [_ Hb2]. rewrite Ehb in Hb2.
    rewrite Hv, bv_xor_unsigned, Hua, Hub. unfold in_itv; cbn [ilo ihi].
    pose proof (u64_range (w64 (evl rho a))) as Ra. pose proof (u64_range (w64 (evl rho b))) as Rb. rewrite Hua in Ra. rewrite Hub in Rb.
    set (k := Z.max (Z.log2_up (ha + 1)) (Z.log2_up (hb + 1))).
    assert (Hka : evl rho a < 2 ^ k).
    { eapply Z.lt_le_trans; [apply log2_up_bound; split; [lia|exact Ha2]|]. apply Z.pow_le_mono_r; [lia|apply Z.le_max_l]. }
    assert (Hkb : evl rho b < 2 ^ k).
    { eapply Z.lt_le_trans; [apply log2_up_bound; split; [lia|exact Hb2]|]. apply Z.pow_le_mono_r; [lia|apply Z.le_max_r]. }
    split.
    + apply (proj2 (Z.lxor_nonneg _ _)). split; intros; lia.
    + apply lxor_below_pow2; lia.
Qed.


(* [comment removed for export] *)
Lemma lin_litC_sound : forall rho C l c, ctx_ok rho C -> lin_litC C l = Some c -> evl rho l = c.
Proof.
  intros rho C l c HC H. unfold lin_litC in H. destruct (is_const l) as [c'|] eqn:K.
  - injection H; intros <-. apply is_const_sound; exact K.
  - pose proof (lrange_ok rho C l HC) as Hi.
    destruct (lrange C l) as [[a|] [b|]]; try discriminate.
    destruct (Z.eqb_spec a b); [|discriminate]. injection H; intros <-. destruct Hi as [H1 H2]; cbn in H1, H2. lia.
Qed.
Lemma aval_litC_sound : forall rho C v z w, ctx_ok rho C -> aval_litC C v = Some z -> val_ok rho v w -> w = w64 z.
Proof.
  intros rho C v z w HC H Hv. destruct v as [|l| |]; cbn in H; try discriminate.
  cbn in Hv. rewrite (lin_litC_sound rho C l z HC H) in Hv. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma two64I_eq : LAI.two64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma uview_sound : forall rho C l l', ctx_ok rho C -> uview C l = Some l' ->
  w64 (evl rho l') = w64 (evl rho l) /\ 0 <= evl rho l' < 2 ^ 64.
Proof.
  intros rho C l l' HC H. unfold uview in H.
  destruct (uexact C l) eqn:U.
  - injection H; intros <-. split; [reflexivity|]. unfold uexact in U. pose proof (in_range_sound rho C l 0 LXL.two64 HC U). rewrite two64_eq in H0. lia.
  - destruct (in_range C l (- LXL.two63) 0) eqn:R; [|discriminate]. injection H; intros <-.
    pose proof (in_range_sound rho C l _ _ HC R). rewrite two63_eq in H0. rewrite laddc_sound, two64I_eq. split; [|lia].
    apply w64_eq_mod. rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma uview_unsigned : forall rho C l l' w, ctx_ok rho C -> uview C l = Some l' -> w = w64 (evl rho l) -> bv_unsigned w = evl rho l'.
Proof.
  intros rho C l l' w HC H Hw. destruct (uview_sound rho C l l' HC H) as [E R]. subst w. rewrite <- E, w64_unsigned. apply Z.mod_small. lia.
Qed.
Lemma uview_below : forall C l l' n, uview C l = Some l' -> lin_below l n = true -> lin_below l' n = true.
Proof.
  intros C l l' n H Hl. unfold uview in H. destruct (uexact C l); [injection H; intros <-; exact Hl|].
  destruct (in_range C l _ 0); [|discriminate]. injection H; intros <-. apply laddc_below; exact Hl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition galign (rho : valuation) : Prop :=
  (rho SYM_SP0 mod 16 = 0 /\ rho SYM_DATA mod 16 = 0) /\
  (rho SYM_SP0 = 32 * rho SYM_S32 + rho SYM_R32 /\ rho SYM_DATA = 16 * rho SYM_D16 /\ (rho SYM_R32 = 0 \/ rho SYM_R32 = 16)).
Lemma talign16_sound : forall rho ts, galign rho -> talign16 ts = true -> (evalt rho ts) mod 16 = 0.
Proof.
  intros rho ts [[GS GD] _]. induction ts as [|[x k] r IH]; cbn -[Z.mul Z.add Z.modulo]; intros H; [reflexivity|].
  apply andb_prop in H as [Hx Hr]. specialize (IH Hr).
  assert (Hx0 : rho x mod 16 = 0).
  { apply orb_prop in Hx as [Hx|Hx]; apply Nat.eqb_eq in Hx; subst; assumption. }
  rewrite Z.add_mod, <- Z.mul_mod_idemp_r, Hx0, Z.mul_0_r, IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eqb_mod_sub : forall u v, (u mod 2 ^ 64 =? v mod 2 ^ 64) = ((u - v) mod 2 ^ 64 =? 0).
Proof.
  intros u v. destruct (Z.eqb_spec (u mod 2 ^ 64) (v mod 2 ^ 64)) as [E|E]; destruct (Z.eqb_spec ((u - v) mod 2 ^ 64) 0) as [F|F]; try reflexivity; exfalso.
  - apply F. rewrite Zminus_mod, E, Z.sub_diag. reflexivity.
  - apply E. apply Z.mod_divide in F; [|lia]. destruct F as [q Hq].
    replace u with (v + q * 2 ^ 64) by lia. rewrite Z.mod_add; [reflexivity|lia].
Qed.
Lemma decide_base_sound : forall rho C k x y b, ctx_ok rho C -> decide_base C k x y = Some b -> cmp_holds rho k x y = b.
Proof.
  intros rho C k x y b HC H. unfold decide_base in H. destruct k; cbn [cmp_holds].
  - pose proof (decide_ge0_sound rho C _ b HC H) as [H1 H2]. rewrite laddc_sound, lsub_sound in H1, H2.
    destruct b; [specialize (H1 eq_refl) | specialize (H2 eq_refl)]; destruct (Z.ltb_spec (evl rho x) (evl rho y)); try reflexivity; lia.
  - pose proof (decide_ge0_sound rho C _ b HC H) as [H1 H2]. rewrite laddc_sound, lsub_sound in H1, H2.
    destruct b; [specialize (H1 eq_refl) | specialize (H2 eq_refl)]; destruct (Z.ltb_spec (evl rho x) (evl rho y)); try reflexivity; lia.
  - rewrite two64z_eq. set (d := lsub x y) in H.
    assert (Hd : evl rho d = evl rho x - evl rho y) by (unfold d; apply lsub_sound).
    rewrite eqb_mod_sub, <- Hd.
    assert (GE1 : decide_ge0 C (laddc d (-1)) = Some true -> 1 <= evl rho d).
    { intros E. pose proof (proj1 (decide_ge0_sound rho C _ _ HC E) eq_refl). rewrite laddc_sound in H0. lia. }
    assert (LE1 : decide_ge0 C (laddc (lneg d) (-1)) = Some true -> evl rho d <= -1).
    { intros E. pose proof (proj1 (decide_ge0_sound rho C _ _ HC E) eq_refl). rewrite laddc_sound, lneg_sound in H0. lia. }
    assert (EQ0 : (entails C d None &&& entails C (lneg d) None)%bool = true -> evl rho d = 0).
    { intros E. apply andb_prop in E as [E1 E2]. pose proof (entails_sound rho C _ None HC E1). pose proof (entails_sound rho C _ None HC E2).
      rewrite lneg_sound in H1. lia. }
    assert (CASE_EQ : forall b', (if (entails C d None &&& entails C (lneg d) None)%bool then Some true else None) = Some b' ->
                      (evl rho d mod 2 ^ 64 =? 0) = b').
    { intros b' Hb. destruct (entails C d None &&& entails C (lneg d) None)%bool eqn:E3; [|discriminate].
      injection Hb; intros <-. rewrite (EQ0 eq_refl). reflexivity. }
    destruct (is_const d) as [c|] eqn:K.
    + injection H; intros <-. rewrite (is_const_sound rho d c K). reflexivity.
    + destruct (in_range C d (1 - LAI.two64) LAI.two64) eqn:R; [|apply CASE_EQ; exact H].
      pose proof (in_range_sound rho C d _ _ HC R) as HR. rewrite two64I_eq in HR.
      destruct (decide_ge0 C (laddc d (-1))) as [[|]|] eqn:E1.
      * injection H; intros <-. specialize (GE1 eq_refl). rewrite Z.mod_small by lia. destruct (Z.eqb_spec (evl rho d) 0); [lia|reflexivity].
      * destruct (decide_ge0 C (laddc (lneg d) (-1))) as [[|]|] eqn:E2; [|apply CASE_EQ; exact H|apply CASE_EQ; exact H].
        injection H; intros <-. specialize (LE1 eq_refl).
        replace (evl rho d) with ((evl rho d + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia. destruct (Z.eqb_spec (evl rho d + 2 ^ 64) 0); [lia|reflexivity].
      * destruct (decide_ge0 C (laddc (lneg d) (-1))) as [[|]|] eqn:E2; [|apply CASE_EQ; exact H|apply CASE_EQ; exact H].
        injection H; intros <-. specialize (LE1 eq_refl).
        replace (evl rho d) with ((evl rho d + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia. destruct (Z.eqb_spec (evl rho d + 2 ^ 64) 0); [lia|reflexivity].
Qed.

Lemma cv_lit_sound : forall rho C v w, ctx_ok rho C -> val_ok rho v w -> val_ok rho (cv_lit C v) w.
Proof.
  intros rho C v w HC Hv. destruct v as [| |n k a b|]; cbn [cv_lit]; try exact Hv.
  destruct (decide_base C k a b) as [bb|] eqn:D; [|exact Hv].
  cbn in Hv. rewrite (decide_base_sound rho C k a b bb HC D) in Hv. apply alit_ok'. rewrite Hv. destruct (xorb n bb); reflexivity.
Qed.
Lemma cv_lit_below : forall C v n, aval_below v n = true -> aval_below (cv_lit C v) n = true.
Proof.
  intros C v n H. destruct v as [| |nn k a b|]; cbn [cv_lit]; try exact H.
  destruct (decide_base C k a b); [apply alit_below | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VOK (rho : valuation) (st : astate) (p : aval * astate) (rho' : valuation) (w : word) : Prop :=
  vext rho st rho' (snd p) /\ VS rho' (snd p) /\ val_ok rho' (fst p) w /\ aval_below (fst p) (s_next (snd p)) = true.

Lemma VOK_top : forall rho st w, VS rho st -> VOK rho st (Top, st) rho w.
Proof. intros rho st w HVS. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [exact I|reflexivity]. Qed.

Lemma VOK_lit : forall rho st z w, VS rho st -> w = w64 z -> VOK rho st (alit z, st) rho w.
Proof. intros. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [assumption|]. split; [apply alit_ok'; assumption | apply alit_below]. Qed.

Lemma VOK_lv : forall rho st l w, VS rho st -> lin_below l (s_next st) = true -> w = w64 (evl rho l) -> VOK rho st (LV l, st) rho w.
Proof. intros. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [assumption|]. split; [exact H1 | exact H0]. Qed.

Lemma VOK_fresh : forall rho st i v w, VS rho st -> in_itv v i -> w = w64 v -> exists rho', VOK rho st (fresh_val st i) rho' w.
Proof.
  intros rho st i v w HVS Hi Hw. destruct (fresh_val_sound rho st i v HVS Hi) as (rho' & A & B & C & D).
  exists rho'. unfold VOK. subst w. split; [exact A|]. split; [exact B|]. split; [exact C|exact D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma add_w64 : forall x y, alu64 ALU_ADD (w64 x) (w64 y) = w64 (x + y).
Proof.
  intros. rewrite alu_add. unfold v_add. apply w64_eq_mod. rewrite !w64_unsigned.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma sub_w64 : forall x y, alu64 ALU_SUB (w64 x) (w64 y) = w64 (x - y).
Proof.
  intros. rewrite alu_sub. unfold v_sub. apply w64_eq_mod. rewrite !w64_unsigned.
  rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma sll_w64 : forall x k, alu64 ALU_SLL (w64 x) (w64 k) = w64 (2 ^ (k mod 64) * x).
Proof.
  intros. rewrite alu_sll. unfold v_sll. apply w64_eq_mod. rewrite !w64_unsigned.
  assert (Hk : (k mod 2 ^ 64) mod 64 = k mod 64).
  { apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity. }
  rewrite Hk. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  rewrite Z.mul_mod_idemp_l by lia. f_equal. lia.
Qed.
Lemma srl_w64 : forall (a : word) k, alu64 ALU_SRL a (w64 k) = w64 (bv_unsigned a / 2 ^ (k mod 64)).
Proof.
  intros. rewrite alu_srl. unfold v_srl. apply w64_eq_mod. rewrite !w64_unsigned.
  assert (Hk : (k mod 2 ^ 64) mod 64 = k mod 64) by (apply Z.mod_mod_divide; exists (2 ^ 58); reflexivity).
  rewrite Hk, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma sra_w64 : forall (a : word) k, alu64 ALU_SRA a (w64 k) = w64 (bv_signed a / 2 ^ (k mod 64)).
Proof.
  intros. rewrite alu_sra. unfold v_sra. apply w64_eq_mod. rewrite !w64_unsigned.
  assert (Hk : (k mod 2 ^ 64) mod 64 = k mod 64) by (apply Z.mod_mod_divide; exists (2 ^ 58); reflexivity).
  rewrite Hk, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma mul_w64 : forall x y, mul_div M_MUL (w64 x) (w64 y) = w64 (x * y).
Proof.
  intros. rewrite m_mul. unfold v_mul. apply w64_eq_mod. rewrite !w64_unsigned.
  rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
Lemma and_w64_unsigned : forall (a b : word), bv_unsigned (alu64 ALU_AND a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof.
  intros. rewrite alu_and. unfold v_and. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). apply Z_land_range; apply u64_range.
Qed.
Lemma or_w64_unsigned : forall (a b : word), bv_unsigned (alu64 ALU_OR a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof.
  intros. rewrite alu_or. unfold v_or. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). apply Z_lor_range; apply u64_range.
Qed.
Lemma xor_w64_unsigned : forall (a b : word), bv_unsigned (alu64 ALU_XOR a b) = Z.lxor (bv_unsigned a) (bv_unsigned b).
Proof.
  intros. rewrite alu_xor. unfold v_xor. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). apply Z_lxor_range; apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.lt_ge_cases n 64) as [L|G].
  - replace (2 ^ 64 - 1 - x) with (Z.lnot x + 1 * 2 ^ 64) by (unfold Z.lnot; lia).
    rewrite <- (Z.mod_pow2_bits_low (Z.lnot x + 1 * 2 ^ 64) 64 n L), Z.mod_add, Z.mod_pow2_bits_low, Z.lnot_spec by lia.
    destruct (Z.ltb_spec n 64); [|lia]. destruct (Z.testbit x n); reflexivity.
  - destruct (Z.ltb_spec n 64); [lia|]. rewrite Bool.xorb_false_r.
    assert (T : forall y, 0 <= y < 2 ^ 64 -> Z.testbit y n = false).
    { intros y Hy. destruct (Z.eq_dec y 0) as [->|NE]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|].
      assert (Z.log2 y < 64) by (apply Z.log2_lt_pow2; lia). lia. }
    rewrite !T by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma xor_m1_w64 : forall x, alu64 ALU_XOR (w64 x) (w64 (-1)) = w64 (- x - 1).
Proof.
  intros x. apply bv_eq. rewrite xor_w64_unsigned, !w64_unsigned.
  change ((-1) mod 2 ^ 64) with (Z.ones 64).
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)).
  rewrite lxor_ones64 by lia.
  replace (- x - 1) with ((2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite <- (Z.mod_small (2 ^ 64 - 1 - x mod 2 ^ 64) (2 ^ 64)) by lia.
  rewrite (Zminus_mod_idemp_r (2 ^ 64 - 1) x). reflexivity.
Qed.
Lemma xor_0_w64 : forall (a : word), alu64 ALU_XOR a (w64 0) = a.
Proof. intros a. apply bv_eq. rewrite xor_w64_unsigned, w64_unsigned, Z.mod_0_l, Z.lxor_0_r by lia. reflexivity. Qed.
Lemma xor_comm_w64 : forall (a b : word), alu64 ALU_XOR a b = alu64 ALU_XOR b a.
Proof. intros. apply bv_eq. rewrite !xor_w64_unsigned. apply Z.lxor_comm. Qed.
Lemma or_0_w64 : forall (a : word), alu64 ALU_OR a (w64 0) = a.
Proof. intros a. apply bv_eq. rewrite or_w64_unsigned, w64_unsigned, Z.mod_0_l, Z.lor_0_r by lia. reflexivity. Qed.
Lemma or_comm_w64 : forall (a b : word), alu64 ALU_OR a b = alu64 ALU_OR b a.
Proof. intros. apply bv_eq. rewrite !or_w64_unsigned. apply Z.lor_comm. Qed.
Lemma and_m1_w64 : forall (a : word), alu64 ALU_AND a (w64 (-1)) = a.
Proof.
  intros a. apply bv_eq. rewrite and_w64_unsigned, w64_unsigned. change ((-1) mod 2 ^ 64) with (Z.ones 64).
  rewrite Z.land_ones by lia. pose proof (u64_range a). apply Z.mod_small. lia.
Qed.
Lemma and_comm_w64 : forall (a b : word), alu64 ALU_AND a b = alu64 ALU_AND b a.
Proof. intros. apply bv_eq. rewrite !and_w64_unsigned. apply Z.land_comm. Qed.

Lemma lit_alu_ok : forall rho op x y, val_ok rho (alit (lit_alu op x y)) (alu64 op (w64 x) (w64 y)).
Proof.
  intros. unfold lit_alu. apply alit_ok'. unfold LAI.uw, LAI.w64. unfold w64 at 3. rewrite w64_snorm. fold w64.
  symmetry. apply w64_of_unsigned.
Qed.
Lemma lit_aluw_ok : forall rho op x y,
  val_ok rho (alit (lit_aluw op x y)) (sext 64 (alu32 op (low32 (w64 x)) (low32 (w64 y)))).
Proof.
  intros. unfold lit_aluw. apply alit_ok'. unfold LAI.uw, LAI.w64. unfold w64 at 3. rewrite w64_snorm. fold w64.
  symmetry. apply w64_of_unsigned.
Qed.
Lemma lit_md_ok : forall rho op x y, val_ok rho (alit (lit_md op x y)) (mul_div op (w64 x) (w64 y)).
Proof.
  intros. unfold lit_md. apply alit_ok'. unfold LAI.uw, LAI.w64. unfold w64 at 3. rewrite w64_snorm. fold w64.
  symmetry. apply w64_of_unsigned.
Qed.
Lemma lit_mdw_ok : forall rho op x y,
  val_ok rho (alit (lit_mdw op x y)) (sext 64 (mul_div op (low32 (w64 x)) (low32 (w64 y)))).
Proof.
  intros. unfold lit_mdw. apply alit_ok'. unfold LAI.uw, LAI.w64. unfold w64 at 3. rewrite w64_snorm. fold w64.
  symmetry. apply w64_of_unsigned.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma VOK_after : forall rho st rho1 st1 p rho' w,
  vext rho st rho1 st1 -> VOK rho1 st1 p rho' w -> VOK rho st p rho' w.
Proof.
  intros rho st rho1 st1 p rho' w He (A & B & C & D). unfold VOK.
  split; [eapply vext_trans; eauto|]. split; [exact B|]. split; [exact C|exact D].
Qed.

Lemma vext_val : forall rho st rho' st' v w,
  vext rho st rho' st' -> aval_below v (s_next st) = true -> val_ok rho v w ->
  val_ok rho' v w /\ aval_below v (s_next st') = true.
Proof.
  intros rho st rho' st' v w (A & N & _) Hb Hv. split.
  - eapply val_ok_agree; eauto.
  - eapply aval_below_mono; eauto.
Qed.

Lemma vext_lin : forall rho st rho' st' l,
  vext rho st rho' st' -> lin_below l (s_next st) = true ->
  evl rho' l = evl rho l /\ lin_below l (s_next st') = true.
Proof.
  intros rho st rho' st' l (A & N & _) Hb. split.
  - eapply evl_agree; eauto.
  - eapply lin_below_mono; eauto.
Qed.

Lemma vext_ctx : forall rho st rho' st', vext rho st rho' st' -> VS rho' st' -> ctx_ok rho' (s_ctx st').
Proof. intros rho st rho' st' _ [H _]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tdiv_sound : forall rho ts m, m <> 0 -> tdivisible ts m = true -> m * evalt rho (tdiv ts m) = evalt rho ts.
Proof.
  intros rho ts m Hm. induction ts as [|[x k] r IH]; cbn -[Z.mul Z.add Z.eqb Z.modulo Z.div]; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  rewrite Z.mul_add_distr_l, IH by exact H2.
  pose proof (Z.div_mod k m Hm) as Hdm. rewrite H1, Z.add_0_r in Hdm.
  rewrite Z.mul_assoc, <- Hdm. reflexivity.
Qed.

Lemma ldiv_sound : forall rho l m, m <> 0 -> ldivisible l m = true -> m * evl rho (ldiv l m) = evl rho l.
Proof.
  intros rho [c ts] m Hm H. unfold ldivisible, ldiv, evl in *; cbn -[Z.mul Z.add Z.eqb Z.modulo Z.div] in *.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  rewrite Z.mul_add_distr_l, (tdiv_sound rho ts m Hm H2).
  pose proof (Z.div_mod c m Hm) as Hdm. rewrite H1, Z.add_0_r in Hdm. lia.
Qed.

Lemma tdiv_below : forall ts m n, tsyms_below ts n = true -> tsyms_below (tdiv ts m) n = true.
Proof.
  induction ts as [|[x k] r IH]; cbn -[Nat.ltb]; intros m n H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn. apply IH. exact H2.
Qed.
Lemma ldiv_below : forall l m n, lin_below l n = true -> lin_below (ldiv l m) n = true.
Proof. intros [c ts] m n; unfold lin_below, ldiv; cbn; apply tdiv_below. Qed.

Lemma find_floor_sound : forall rho C fs l m v, ctx_ok rho C -> find_floor C fs l m = Some v ->
  0 <= evl rho l - m * rho v /\ evl rho l - m * rho v <= m - 1.
Proof.
  intros rho C fs l m v HC. induction fs as [|f r IH]; intros H; [discriminate|]. cbn [find_floor] in H.
  destruct (lt (lsub l f)) as [|[v0 cc] [|t2 r2]] eqn:E; try (apply IH; exact H).
  match type of H with context [if ?b then _ else _] => destruct b eqn:B; [|apply IH; exact H] end.
  injection H; intros <-.
  apply andb_prop in B as [B B2]. apply andb_prop in B as [B B1].
  pose proof (entails12_sound rho C _ HC B1) as H1. pose proof (entails12_sound rho C _ HC B2) as H2.
  rewrite lsub_sound, lscale_sound, lvar_sound in H1. rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound in H2. lia.
Qed.
Lemma find_floor_below : forall C fs l m v n,
  forallb (fun f => lin_below f n) fs = true -> lin_below l n = true -> find_floor C fs l m = Some v -> (v < n)%nat.
Proof.
  intros C fs l m v n HF Hl. induction fs as [|f r IH]; intros H; [discriminate|]. cbn [find_floor] in H.
  change (forallb (fun f => lin_below f n) (f :: r)) with (lin_below f n &&& forallb (fun f => lin_below f n) r)%bool in HF.
  apply andb_prop in HF as [Hf Hr]. specialize (IH Hr).
  pose proof (lsub_below l f n Hl Hf) as B.
  destruct (lt (lsub l f)) as [|[v0 cc] [|t2 r2]] eqn:E; try (apply IH; exact H).
  match type of H with context [if ?b then _ else _] => destruct b; [|apply IH; exact H] end.
  injection H; intros <-.
  unfold lin_below in B. rewrite E in B. cbn -[Nat.ltb] in B. apply andb_prop in B as [B _]. apply Nat.ltb_lt in B. exact B.
Qed.
(* [comment removed for export] *)
Lemma scale_subst_sound : forall rho C l, galign rho -> ctx_ok rho C -> evl rho (scale_subst C l) = evl rho l.
Proof.
  intros rho C l [_ (GS & GD & _)] HC. unfold scale_subst. apply lsubst_sound. intros x.
  destruct (Nat.eqb_spec x SYM_SP0) as [->|NS].
  - destruct (sp_res C) as [r|] eqn:E; [|reflexivity]. unfold sp_res in E.
    rewrite laddc_sound, lscale_sound, lvar_sound. rewrite <- (lin_litC_sound rho C (lvar SYM_R32) r HC E), lvar_sound. exact GS.
  - destruct (Nat.eqb_spec x SYM_DATA) as [->|ND]; [|reflexivity]. rewrite lscale_sound, lvar_sound. exact GD.
Qed.
Lemma lin1_below : forall x k n, (x < n)%nat -> lin_below (Lin 0 [(x, k)]) n = true.
Proof. intros x k n H. unfold lin_below. cbn -[Nat.ltb]. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.
Lemma scale_subst_below : forall C l n, (NGLOB <= n)%nat -> lin_below l n = true -> lin_below (scale_subst C l) n = true.
Proof.
  intros C l n Hn Hl. unfold scale_subst, lsubst. apply laddc_below.
  revert Hl. unfold lin_below at 1. generalize (lt l) as ts. induction ts as [|[x k] r IH]; intros H; [reflexivity|].
  cbn -[Nat.ltb Nat.eqb] in H. apply andb_prop in H as [Hx Hr]. apply Nat.ltb_lt in Hx. cbn [tsubst].
  apply ladd_below; [|apply IH; exact Hr].
  destruct (Nat.eqb x SYM_SP0).
  - destruct (sp_res C); [|apply lin1_below; exact Hx].
    apply lscale_below; apply laddc_below; apply lscale_below; apply lvar_below; unfold SYM_S32, NGLOB in *; lia.
  - destruct (Nat.eqb x SYM_DATA); [|apply lin1_below; exact Hx].
    apply lscale_below; apply lscale_below; apply lvar_below; unfold SYM_D16, NGLOB in *; lia.
Qed.
Lemma unscale_sound : forall rho C l, galign rho -> ctx_ok rho C -> evl rho (unscale C l) = evl rho l.
Proof.
  intros rho C l [_ (GS & GD & _)] HC. unfold unscale.
  set (cs := lcoef SYM_S32 l). set (cd := lcoef SYM_D16 l).
  set (l1 := if (negb (Z.eqb cs 0) &&& Z.eqb (cs mod 32) 0)%bool then _ else _).
  assert (E1 : evl rho l1 = evl rho l).
  { subst l1. destruct (negb (Z.eqb cs 0) &&& Z.eqb (cs mod 32) 0)%bool eqn:B; [|reflexivity].
    apply andb_prop in B as [_ B]. apply Z.eqb_eq in B.
    destruct (sp_res C) as [r|] eqn:E; [|reflexivity]. unfold sp_res in E.
    rewrite ladd_sound, lsub_sound, !lscale_sound, laddc_sound, !lvar_sound.
    rewrite <- (lin_litC_sound rho C (lvar SYM_R32) r HC E), lvar_sound. rewrite GS.
    pose proof (Z.div_mod cs 32 ltac:(lia)). nia. }
  destruct (negb (Z.eqb cd 0) &&& Z.eqb (cd mod 16) 0)%bool eqn:B2; [|exact E1].
  apply andb_prop in B2 as [_ B2]. apply Z.eqb_eq in B2.
  rewrite ladd_sound, lsub_sound, !lscale_sound, !lvar_sound, E1, GD. pose proof (Z.div_mod cd 16 ltac:(lia)). nia.
Qed.
Lemma unscale_below : forall C l n, (NGLOB <= n)%nat -> lin_below l n = true -> lin_below (unscale C l) n = true.
Proof.
  intros C l n Hn Hl. unfold unscale.
  set (cs := lcoef SYM_S32 l). set (cd := lcoef SYM_D16 l).
  set (l1 := if (negb (Z.eqb cs 0) &&& Z.eqb (cs mod 32) 0)%bool then _ else _).
  assert (B1 : lin_below l1 n = true).
  { subst l1. destruct (negb (Z.eqb cs 0) &&& Z.eqb (cs mod 32) 0)%bool; [|exact Hl].
    destruct (sp_res C) as [r|]; [|exact Hl].
    apply ladd_below; [apply lsub_below; [exact Hl | apply lscale_below; apply lvar_below; unfold SYM_S32, NGLOB in *; lia]|].
    apply lscale_below; apply laddc_below; apply lvar_below; unfold SYM_SP0, NGLOB in *; lia. }
  destruct (negb (Z.eqb cd 0) &&& Z.eqb (cd mod 16) 0)%bool; [|exact B1].
  apply ladd_below; [apply lsub_below; [exact B1 | apply lscale_below; apply lvar_below; unfold SYM_D16, NGLOB in *; lia]|].
  apply lscale_below; apply lvar_below; unfold SYM_DATA, NGLOB in *; lia.
Qed.
Lemma tsplit_div_sound : forall rho ts m, m <> 0 ->
  let (q, r) := tsplit_div ts m in m * evalt rho q + evalt rho r = evalt rho ts.
Proof.
  intros rho ts m Hm. induction ts as [|[x c] rest IH]; cbn -[Z.mul Z.add Z.eqb Z.modulo Z.div]; [lia|].
  destruct (tsplit_div rest m) as [q r]. destruct (Z.eqb_spec (c mod m) 0) as [E|E]; cbn -[Z.mul Z.add Z.modulo Z.div].
  - pose proof (Z.div_mod c m Hm). lia.
  - lia.
Qed.
Lemma lsplit_div_sound : forall rho l m, 0 < m ->
  let (q, r) := lsplit_div l m in m * evl rho q + evl rho r = evl rho l.
Proof.
  intros rho [c ts] m Hm. unfold lsplit_div. cbn [lt lc]. pose proof (tsplit_div_sound rho ts m ltac:(lia)) as H.
  destruct (tsplit_div ts m) as [q r]. unfold evl; cbn -[Z.mul Z.add Z.modulo Z.div]. pose proof (Z.div_mod c m ltac:(lia)). lia.
Qed.
Lemma tsplit_div_below : forall ts m n, tsyms_below ts n = true -> let (q, r) := tsplit_div ts m in tsyms_below q n = true /\ tsyms_below r n = true.
Proof.
  induction ts as [|[x c] rest IH]; intros m n H; cbn -[Nat.ltb Z.eqb Z.modulo Z.div]; [split; reflexivity|].
  cbn -[Nat.ltb] in H. apply andb_prop in H as [Hx Hr]. specialize (IH m n Hr). destruct (tsplit_div rest m) as [q r]. destruct IH as [IH1 IH2].
  destruct (Z.eqb (c mod m) 0); cbn -[Nat.ltb]; rewrite ?Hx, ?IH1, ?IH2; split; reflexivity.
Qed.
Lemma lsplit_div_below : forall l m n, lin_below l n = true -> lin_below (fst (lsplit_div l m)) n = true /\ lin_below (snd (lsplit_div l m)) n = true.
Proof.
  intros [c ts] m n H. unfold lsplit_div, lin_below in *; cbn [lt] in *. pose proof (tsplit_div_below ts m n H) as T.
  destruct (tsplit_div ts m) as [q r]. cbn. exact T.
Qed.
Lemma lsplit_div_r_const : forall l m c, 0 < m -> is_const (snd (lsplit_div l m)) = Some c -> 0 <= c < m.
Proof.
  intros [c0 ts] m c Hm H. unfold lsplit_div in H. cbn [lt lc] in H. destruct (tsplit_div ts m) as [q r]. cbn [snd] in H.
  unfold is_const in H. cbn in H. destruct r; [|discriminate]. injection H; intros <-. apply Z.mod_pos_bound. exact Hm.
Qed.

Lemma shr_floor_sound : forall rho st l k ri,
  galign rho -> VS rho st -> (NGLOB <= s_next st)%nat -> lin_below l (s_next st) = true -> 0 <= k ->
  in_itv (evl rho l / 2 ^ k) ri ->
  exists rho', VOK rho st (shr_floor st l k ri) rho' (w64 (evl rho l / 2 ^ k)).
Proof.
  intros rho st l0 k ri GA HVS HNG Hl0 Hk Hri. unfold shr_floor.
  assert (Hm : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
  assert (Hmpos : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  set (l := if Z.leb k 5 then scale_subst (s_ctx st) l0 else l0).
  assert (Hev0 : evl rho l = evl rho l0).
  { unfold l. destruct (Z.leb k 5); [apply scale_subst_sound; [exact GA | exact (proj1 HVS)] | reflexivity]. }
  assert (Hl : lin_below l (s_next st) = true).
  { unfold l. destruct (Z.leb k 5); [apply scale_subst_below; [exact HNG | exact Hl0] | exact Hl0]. }
  rewrite <- Hev0 in Hri |- *. clearbody l. clear Hev0 Hl0 l0.
  destruct (ldivisible l (2 ^ k)) eqn:Hd.
  - exists rho. apply VOK_lv; [exact HVS | apply ldiv_below; exact Hl |].
    f_equal. pose proof (ldiv_sound rho l (2 ^ k) Hm Hd).
    rewrite <- H. rewrite Z.mul_comm, Z.div_mul by exact Hm. reflexivity.
  - pose proof (lsplit_div_sound rho l (2 ^ k) Hmpos) as SP. pose proof (lsplit_div_below l (2 ^ k) (s_next st) Hl) as [Bq Br].
    destruct (lsplit_div l (2 ^ k)) as [q r] eqn:ESP. cbn [fst snd] in Bq, Br.
    destruct (is_const r) as [c|] eqn:Kr.
    { (* [comment removed for export] *)
      pose proof (lsplit_div_r_const l (2 ^ k) c Hmpos) as RC. rewrite ESP in RC. cbn [snd] in RC. specialize (RC Kr).
      pose proof (is_const_sound rho r c Kr) as Erc.
      exists rho. apply VOK_lv; [exact HVS | exact Bq |]. f_equal. symmetry.
      apply Z.div_unique_pos with (r := c); lia. }
    destruct (find_floor (s_ctx st) (cfacts (s_ctx st)) r (2 ^ k)) as [fv|] eqn:Hff.
    { (* [comment removed for export] *)
      destruct (find_floor_sound rho (s_ctx st) (cfacts (s_ctx st)) r (2 ^ k) fv (proj1 HVS) Hff) as [F1 F2].
      assert (Bv : (fv < s_next st)%nat).
      { pose proof (proj2 HVS) as CB. unfold ctx_below in CB. apply andb_prop in CB as [CF _].
        eapply find_floor_below; [exact CF | exact Br | exact Hff]. }
      exists rho. apply VOK_lv; [exact HVS | apply ladd_below; [exact Bq | apply lvar_below; exact Bv] |].
      f_equal. rewrite ladd_sound, lvar_sound. symmetry. apply Z.div_unique_pos with (r := evl rho r - 2 ^ k * rho fv); lia. }
    set (v := evl rho r / 2 ^ k).
    assert (Hri' : in_itv v (itv_div (lrange (s_ctx st) r) (2 ^ k))).
    { unfold v. pose proof (lrange_ok rho (s_ctx st) r (proj1 HVS)) as [LO HI]. unfold itv_div, in_itv. cbn [ilo ihi].
      destruct (ilo (lrange (s_ctx st) r)) as [a|]; destruct (ihi (lrange (s_ctx st) r)) as [b|]; cbn [option_map] in *;
        repeat split; try (apply Z.div_le_mono; lia); exact I. }
    destruct (fresh_sound rho st _ v HVS Hri') as (rho1 & Hx & He1 & HVS1 & Hfst & Hn1).
    destruct (fresh st (itv_div (lrange (s_ctx st) r) (2 ^ k))) as [x st1] eqn:Ef. cbn [fst snd] in *. subst x.
    assert (Hr1 : lin_below r (s_next st1) = true) by (rewrite Hn1; eapply lin_below_mono; [|exact Br]; lia).
    assert (Hq1 : lin_below q (s_next st1) = true) by (rewrite Hn1; eapply lin_below_mono; [|exact Bq]; lia).
    assert (Hv1 : lin_below (lvar (s_next st)) (s_next st1) = true) by (rewrite Hn1; apply lvar_below; lia).
    assert (Hevr : evl rho1 r = evl rho r) by (eapply evl_agree; [exact Br | destruct He1 as [A _]; exact A]).
    assert (Hevq : evl rho1 q = evl rho q) by (eapply evl_agree; [exact Bq | destruct He1 as [A _]; exact A]).
    set (f1 := lsub r (lscale (2 ^ k) (lvar (s_next st)))).
    set (f2 := laddc (lsub (lscale (2 ^ k) (lvar (s_next st))) r) (2 ^ k - 1)).
    assert (Hf1b : lin_below f1 (s_next st1) = true) by (unfold f1; apply lsub_below; [exact Hr1 | apply lscale_below; exact Hv1]).
    assert (Hf2b : lin_below f2 (s_next st1) = true) by (unfold f2; apply laddc_below; apply lsub_below; [apply lscale_below; exact Hv1 | exact Hr1]).
    pose proof (Z.mul_div_le (evl rho r) (2 ^ k) Hmpos) as Hle.
    pose proof (Z.mul_succ_div_gt (evl rho r) (2 ^ k) Hmpos) as Hgt.
    assert (Hf1 : 0 <= evl rho1 f1).
    { unfold f1. rewrite lsub_sound, lscale_sound, lvar_sound, Hx, Hevr. unfold v. lia. }
    destruct (learn_sound rho1 st1 f1 HVS1 Hf1b Hf1) as [He2 HVS2].
    assert (Hf2 : 0 <= evl rho1 f2).
    { unfold f2. rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound, Hx, Hevr. unfold v. lia. }
    assert (Hf2b' : lin_below f2 (s_next (learn st1 f1)) = true) by exact Hf2b.
    destruct (learn_sound rho1 (learn st1 f1) f2 HVS2 Hf2b' Hf2) as [He3 HVS3].
    exists rho1. unfold VOK. cbn [fst snd].
    split; [eapply vext_trans; [exact He1 | eapply vext_trans; [exact He2 | exact He3]]|].
    split; [exact HVS3|]. split.
    + cbn. rewrite ladd_sound, lvar_sound, Hx, Hevq. f_equal. unfold v.
      symmetry. apply Z.div_unique_pos with (r := evl rho r - 2 ^ k * (evl rho r / 2 ^ k)); lia.
    + cbn -[lin_below]. change (lin_below (ladd q (lvar (s_next st))) (s_next st1) = true). apply ladd_below; [exact Hq1 | exact Hv1].
Qed.

(* [comment removed for export] *)
Lemma e2_bounds_ok : forall rho C l f acc, ctx_ok rho C -> In f (cfacts C) -> in_itv (evl rho l) acc ->
  in_itv (evl rho l) (e2_bounds C l f acc).
Proof.
  intros rho C l f acc HC Hf Hacc. unfold e2_bounds. destruct (lshare f l); [|exact Hacc].
  assert (Hf0 : 0 <= evl rho f) by (destruct HC as [HF _]; exact (proj1 (Forall_forall _ _) HF f Hf)).
  assert (GEN : forall ks a, in_itv (evl rho l) a -> Forall (fun k => 0 <= k) ks ->
            in_itv (evl rho l) (fold_left (fun a k => imeet a (Itv (ilo (litv (cb C) (lsub l (lscale k f)))) (ihi (litv (cb C) (ladd l (lscale k f)))))) ks a)).
  { induction ks as [|k ks IH]; intros a Ha Hks; cbn [fold_left]; [exact Ha|]. inversion Hks; subst.
    apply IH; [|assumption]. apply imeet_sound; [exact Ha|].
    pose proof (litv_sound rho (cb C) (lsub l (lscale k f)) (proj2 HC)) as [L1 _].
    pose proof (litv_sound rho (cb C) (ladd l (lscale k f)) (proj2 HC)) as [_ U2].
    rewrite lsub_sound, lscale_sound in L1. rewrite ladd_sound, lscale_sound in U2.
    assert (Hkf : 0 <= k * evl rho f) by (apply Z.mul_nonneg_nonneg; assumption).
    unfold in_itv; cbn [ilo ihi]. split.
    - destruct (ilo (litv (cb C) (lsub l (lscale k f)))) as [lo|]; [lia | exact I].
    - destruct (ihi (litv (cb C) (ladd l (lscale k f)))) as [hi|]; [lia | exact I]. }
  apply GEN; [exact Hacc|]. unfold e2_scales. repeat apply Forall_cons; try apply Forall_nil; lia.
Qed.
Lemma lrange2_ok : forall rho C l, ctx_ok rho C -> in_itv (evl rho l) (lrange2 C l).
Proof.
  intros rho C l HC. unfold lrange2.
  assert (GEN : forall fs a, (forall f, In f fs -> In f (cfacts C)) -> in_itv (evl rho l) a ->
            in_itv (evl rho l) (fold_left (fun a f => e2_bounds C l f a) fs a)).
  { induction fs as [|f fs IH]; intros a Hsub Ha; cbn [fold_left]; [exact Ha|].
    apply IH; [intros g Hg; apply Hsub; right; exact Hg|]. apply e2_bounds_ok; [exact HC | apply Hsub; left; reflexivity | exact Ha]. }
  apply GEN; [intros f Hf; exact Hf | apply lrange_ok; exact HC].
Qed.

(* [comment removed for export] *)
Lemma table_span_in_sound : forall rho C ts l lo hi, ctx_ok rho C -> table_span_in C ts l = Some (lo, hi) -> lo <= evl rho l <= hi.
Proof.
  intros rho C ts l lo hi HC. induction ts as [|t rest IH]; intros H; [discriminate|]. cbn [table_span_in] in H.
  destruct (Z.ltb_spec 0 (tb_stride t)) as [Hs|Hs].
  - destruct (ldivisible (laddc (laddc l (- tb_base t)) (- (lc (laddc l (- tb_base t)) mod tb_stride t))) (tb_stride t)) eqn:Hd; [|exact (IH H)].
    match type of H with context [if ?b then _ else _] => destruct b eqn:HE end; [|exact (IH H)].
    injection H; intros <- <-. apply andb_prop in HE as [E1 E2].
    pose proof (entails_sound rho _ _ None HC E1) as H1. pose proof (entails_sound rho _ _ None HC E2) as H2.
    rewrite laddc_sound, lneg_sound in H2.
    pose proof (ldiv_sound rho _ (tb_stride t) ltac:(lia) Hd) as Hq. rewrite !laddc_sound in Hq.
    set (idx := evl rho (ldiv _ _)) in *.
    (* [comment removed for export] *)
    match goal with |- _ + ?o <= _ <= _ => match type of Hq with _ = _ + - _ + - ?o' => change o' with o in Hq end end.
    assert (0 <= tb_stride t * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (tb_stride t * idx <= tb_stride t * (tb_count t - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
  - exact (IH H).
Qed.
Lemma table_span_sound : forall rho U C l lo hi, ctx_ok rho C -> table_span U C l = Some (lo, hi) -> lo <= evl rho l <= hi.
Proof. intros rho U C l lo hi HC H. unfold table_span in H. eapply table_span_in_sound; eauto. Qed.

Lemma table_floor_sound : forall rho st l k lo hi,
  VS rho st -> lin_below l (s_next st) = true -> 0 <= k -> lo <= evl rho l <= hi ->
  exists rho', VOK rho st (table_floor st l k lo hi) rho' (w64 (evl rho l / 2 ^ k)).
Proof.
  intros rho st r k lo hi HVS Br Hk Hlh. unfold table_floor.
  assert (Hmpos : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  set (v := evl rho r / 2 ^ k).
  assert (Hri' : in_itv v (Itv (Some (lo / 2 ^ k)) (Some (hi / 2 ^ k)))).
  { unfold v, in_itv. cbn [ilo ihi]. split; apply Z.div_le_mono; lia. }
  destruct (fresh_sound rho st _ v HVS Hri') as (rho1 & Hx & He1 & HVS1 & Hfst & Hn1).
  destruct (fresh st (Itv (Some (lo / 2 ^ k)) (Some (hi / 2 ^ k)))) as [x st1] eqn:Ef. cbn [fst snd] in *. subst x.
  assert (Hr1 : lin_below r (s_next st1) = true) by (rewrite Hn1; eapply lin_below_mono; [|exact Br]; lia).
  assert (Hv1 : lin_below (lvar (s_next st)) (s_next st1) = true) by (rewrite Hn1; apply lvar_below; lia).
  assert (Hevr : evl rho1 r = evl rho r) by (eapply evl_agree; [exact Br | destruct He1 as [A _]; exact A]).
  set (f1 := lsub r (lscale (2 ^ k) (lvar (s_next st)))).
  set (f2 := laddc (lsub (lscale (2 ^ k) (lvar (s_next st))) r) (2 ^ k - 1)).
  assert (Hf1b : lin_below f1 (s_next st1) = true) by (unfold f1; apply lsub_below; [exact Hr1 | apply lscale_below; exact Hv1]).
  assert (Hf2b : lin_below f2 (s_next st1) = true) by (unfold f2; apply laddc_below; apply lsub_below; [apply lscale_below; exact Hv1 | exact Hr1]).
  pose proof (Z.mul_div_le (evl rho r) (2 ^ k) Hmpos) as Hle.
  pose proof (Z.mul_succ_div_gt (evl rho r) (2 ^ k) Hmpos) as Hgt.
  assert (Hf1 : 0 <= evl rho1 f1).
  { unfold f1. rewrite lsub_sound, lscale_sound, lvar_sound, Hx, Hevr. unfold v. lia. }
  destruct (learn_sound rho1 st1 f1 HVS1 Hf1b Hf1) as [He2 HVS2].
  assert (Hf2 : 0 <= evl rho1 f2).
  { unfold f2. rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound, Hx, Hevr. unfold v. lia. }
  assert (Hf2b' : lin_below f2 (s_next (learn st1 f1)) = true) by exact Hf2b.
  destruct (learn_sound rho1 (learn st1 f1) f2 HVS2 Hf2b' Hf2) as [He3 HVS3].
  exists rho1. unfold VOK. cbn [fst snd].
  split; [eapply vext_trans; [exact He1 | eapply vext_trans; [exact He2 | exact He3]]|].
  split; [exact HVS3|]. split.
  + cbn. rewrite lvar_sound, Hx. reflexivity.
  + cbn -[lin_below]. change (lin_below (lvar (s_next st)) (s_next st1) = true). exact Hv1.
Qed.

(* [comment removed for export] *)
Lemma and_lowlit_sound : forall rho C x j z, galign rho -> ctx_ok rho C -> 0 <= j -> and_lowlit C x j = Some z ->
  (evl rho x) mod 2 ^ j = z /\ 0 <= z < 2 ^ j.
Proof.
  intros rho C x j z GA HC Hj H. unfold and_lowlit in H.
  match type of H with context [if ?b then _ else _] => destruct b eqn:HF; [|discriminate] end.
  rewrite <- (scale_subst_sound rho C x GA HC).
  remember (scale_subst C x) as l eqn:El. clear El.
  injection H; intros <-.
  assert (Hm : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  split; [|apply Z.mod_pos_bound; exact Hm].
  destruct l as [c ts]. unfold evl; cbn [lt lc] in *.
  assert (T : (evalt rho ts) mod 2 ^ j = 0).
  { revert HF. induction ts as [|[y k] r IH]; cbn -[Z.mul Z.add Z.modulo Z.eqb]; intros HF; [reflexivity|].
    apply andb_prop in HF as [Hk Hr]. apply Z.eqb_eq in Hk. cbn [snd] in Hk.
    rewrite Z.add_mod, <- Z.mul_mod_idemp_l, Hk, Z.mul_0_l, (IH Hr) by lia. reflexivity. }
  rewrite Z.add_mod by lia. rewrite T. rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma half32 : bv_half_modulus 32 = 2 ^ 31. Proof. reflexivity. Qed.
Lemma bv_swrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros. apply bv_swrap_small. rewrite half32. lia. Qed.
Lemma bv_swrap32_range : forall z, - 2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof. intros. pose proof (bv_swrap_in_range 32 z). rewrite half32 in H. lia. Qed.

Lemma norm32_sound : forall rho st r w,
  VS rho st -> lin_below r (s_next st) = true -> w = w64 (bv_swrap 32 (evl rho r)) ->
  exists rho', VOK rho st (norm32 st r) rho' w.
Proof.
  intros rho st r w HVS Hr Hw. unfold norm32. destruct (sexact32 (s_ctx st) r) eqn:E.
  - exists rho. apply VOK_lv; [exact HVS | exact Hr |].
    pose proof (in_range_sound rho _ r _ _ (proj1 HVS) E). rewrite two31_eq in H.
    rewrite Hw. f_equal. apply bv_swrap32_small. lia.
  - eapply VOK_fresh; [exact HVS | | exact Hw]. unfold itv_s32, in_itv; cbn [ilo ihi].
    pose proof (bv_swrap32_range (evl rho r)). unfold LAI.two31. rewrite two31_eq. lia.
Qed.

End LASV.
