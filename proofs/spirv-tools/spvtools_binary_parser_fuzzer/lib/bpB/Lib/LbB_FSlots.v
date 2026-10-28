(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMem BCells BArr BLFrame BStep BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Conv LbB_FKit LbB_PmBase.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint lword (log : list sentry) (b : expr) (k : Z) : option (option expr) :=
  match log with
  | [] => None
  | SE a w v :: rest =>
      if (expr_eqb (a_base a) b && (a_off a <? k + 8) && (k <? a_off a + Z.of_nat w))%bool then
        if (Z.eqb (a_off a) k && Nat.eqb w 8)%bool then Some (Some v) else Some None
      else lword rest b k
  end.

Definition smiss (b : expr) (k : Z) (e : sentry) : Prop :=
  expr_eqb (a_base (e_addr e)) b = true -> a_off (e_addr e) + Z.of_nat (e_width e) <= k \/ k + 8 <= a_off (e_addr e).

Lemma lword_some : forall log b k v, lword log b k = Some (Some v) ->
  exists pre post, log = pre ++ SE (SA b k) 8 v :: post /\ Forall (smiss b k) pre.
Proof.
  induction log as [|[a w v'] rest IH]; intros b k v H; cbn [lword] in H; [discriminate|].
  destruct ((expr_eqb (a_base a) b && (a_off a <? k + 8) && (k <? a_off a + Z.of_nat w))%bool) eqn:E1.
  - destruct ((Z.eqb (a_off a) k && Nat.eqb w 8)%bool) eqn:E2; [|discriminate].
    injection H as <-. apply andb_true_iff in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Nat.eqb_eq in E3.
    apply andb_true_iff in E1 as [E1 _]. apply andb_true_iff in E1 as [E1 _]. apply expr_eqb_true in E1.
    exists [], rest. split; [| constructor]. destruct a as [ab ao]. cbn in E1, E2. subst. reflexivity.
  - destruct (IH b k v H) as (pre & post & Ep & Fp). exists (SE a w v' :: pre), post. split; [rewrite Ep; reflexivity|].
    constructor; [| exact Fp]. intros Eb. cbn [e_addr e_width] in *. rewrite Eb in E1. cbn in E1.
    apply andb_false_iff in E1 as [E1|E1]; [apply Z.ltb_ge in E1 | apply Z.ltb_ge in E1]; lia.
Qed.

Lemma edenot_wclosed : forall E E' e, wclosed e = true -> (forall n, (32 <= n <= 40)%N -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros E E' e. induction e; cbn [wclosed edenot]; intros Hc HE; try discriminate; try reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. apply N.leb_le in H1. apply N.leb_le in H2. apply HE. lia.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
Qed.

Lemma Eseed_world : forall R vs n, (32 <= n)%N ->
  ev (HLib.Eseed R vs) n = nth (N.to_nat n - 32) vs (Z_to_bv 64 0).
Proof.
  intros R vs n Hn. unfold HLib.Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [lia | reflexivity].
Qed.

Definition omiss (E : env) (b : expr) (y n : Z) (e : sentry) : Prop :=
  expr_eqb (a_base (e_addr e)) b = false -> estart E (e_addr e) + Z.of_nat (e_width e) <= y \/ y + n <= estart E (e_addr e).

Lemma lword_none_lbyte : forall log b k i, lword log b k = None -> 0 <= i < 8 -> lbyte log b (k + i) = None.
Proof.
  induction log as [|[a w v'] rest IH]; intros b k i H Hi; cbn [lword lbyte] in *; [reflexivity|].
  destruct ((expr_eqb (a_base a) b && (a_off a <? k + 8) && (k <? a_off a + Z.of_nat w))%bool) eqn:E1.
  - destruct ((Z.eqb (a_off a) k && Nat.eqb w 8)%bool); discriminate.
  - destruct (expr_eqb (a_base a) b) eqn:Eb; cbn [andb] in *.
    + destruct ((a_off a <=? k + i) && (k + i <? a_off a + Z.of_nat w))%bool eqn:E2; [| exact (IH b k i H Hi)].
      exfalso. apply andb_true_iff in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
      apply andb_false_iff in E1 as [E1|E1]; [apply Z.ltb_ge in E1 | apply Z.ltb_ge in E1]; lia.
    + exact (IH b k i H Hi).
Qed.

Lemma rdn_slot_none : forall segs E M log b k,
  log_flat E log -> Forall (omiss E b (bv_unsigned (edenot E b) + k) 8) log -> lword log b k = None ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 <= 2 ^ 64 ->
  PropExec.rdn segs (mem_denot E M log) (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) 8
  = PropExec.rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) 8.
Proof.
  intros segs E M log b k Hf HO HN H0 H1. apply PropExec.rdn_ext.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. lia.
  - intros x Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap, bv_modulus in Hx. cbn [Z.of_N] in Hx. rewrite Z.mod_small in Hx by lia.
    set (i := bv_unsigned x - (bv_unsigned (edenot E b) + k)).
    assert (Hi : 0 <= i < 8) by (subst i; lia).
    pose proof (mem_denot_lbyte E M log b (k + i) Hf) as K.
    assert (HM : Forall (lmiss E b (bv_unsigned (edenot E b) + (k + i))) log).
    { eapply Forall_impl; [| exact HO]. intros e He. unfold lmiss. destruct (expr_eqb (a_base (e_addr e)) b) eqn:Eb; [left; reflexivity|].
      right. destruct (He Eb); [left | right]; lia. }
    specialize (K HM ltac:(lia)). rewrite (lword_none_lbyte log b k i HN Hi) in K.
    replace x with (Z_to_bv 64 (bv_unsigned (edenot E b) + (k + i))); [exact K|].
    apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. subst i. lia.
Qed.

Lemma rdn_slot_some : forall segs E M log b k v,
  log_flat E log -> Forall (omiss E b (bv_unsigned (edenot E b) + k) 8) log -> lword log b k = Some (Some v) ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 <= 2 ^ 64 ->
  PropExec.rdn segs (mem_denot E M log) (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) 8
  = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros segs E M log b k v Hf HO HS H0 H1.
  destruct (lword_some log b k v HS) as (pre & post & -> & Fp).
  assert (Ha : adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k)).
  { unfold adenot, v_addi. cbn [a_base a_off]. reflexivity. }
  rewrite <- Ha. apply LbB_Conv.rdn_mem_denot_hit; [exact Hf|].
  apply Forall_forall. intros e He.
  assert (HO' : omiss E b (bv_unsigned (edenot E b) + k) 8 e).
  { apply (proj1 (Forall_forall _ _) HO). apply in_app_iff. left. exact He. }
  assert (HS' : smiss b k e) by exact (proj1 (Forall_forall _ _) Fp e He).
  unfold estart at 2 3. cbn [a_base a_off]. replace (Z.of_nat 8) with 8 by reflexivity.
  unfold omiss, smiss in *. destruct (expr_eqb (a_base (e_addr e)) b) eqn:Eb.
  - pose proof (expr_eqb_true _ _ Eb) as Eab. destruct (HS' eq_refl) as [L|L]; [left | right];
      unfold estart; rewrite Eab; lia.
  - destruct (HO' eq_refl); [left | right]; lia.
Qed.

Fixpoint upd_slots (log : list sentry) (b : expr) (tbl : list (Z * expr)) : list (Z * expr) :=
  match tbl with
  | [] => []
  | (k, e) :: t =>
      match lword log b k with
      | None => (k, e) :: upd_slots log b t
      | Some (Some v) => if wclosed v then (k, v) :: upd_slots log b t else upd_slots log b t
      | Some None => upd_slots log b t
      end
  end.
Fixpoint add_slots (log : list sentry) (b : expr) (ks : list Z) : list (Z * expr) :=
  match ks with
  | [] => []
  | k :: t =>
      match lword log b k with
      | Some (Some v) => if wclosed v then (k, v) :: add_slots log b t else add_slots log b t
      | _ => add_slots log b t
      end
  end.

Lemma rw_C8_of_rdn : forall m A x, 0 <= A -> A + 8 <= 2 ^ 64 ->
  PropExec.rdn asegs m (Z_to_bv 64 A) 8 = Some (word_to_le_bytes 8 x) -> wr_at asegs m A 8 ->
  rw_cells asegs m A [C8 x].
Proof.
  intros m A x H0 H1 HR HW. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8.
    apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; cbn; lia |].
    rewrite CatExec.length_N_to_le_bytes. exact HR.
  - exact HW.
Qed.

Lemma rdn_of_rw_C8 : forall m A x, rw_cells asegs m A [C8 x] -> PropExec.rdn asegs m (Z_to_bv 64 A) 8 = Some (word_to_le_bytes 8 x).
Proof.
  intros m A x RW. pose proof (rw_cells_read asegs m A [C8 x] 0 (C8 x) RW eq_refl) as K.
  cbn [csize cbytes] in K. rewrite Z.add_0_r in K. unfold wa in K. rewrite LbB_Conv.rdn_of_ov in K. unfold le8 in K. exact K.
Qed.

Section Slots.
  Context {HCEIL : HeapCeil}.
  Variable H : BsIface.asr.

  Lemma slots_mem_denot : forall (w : pmwA H) m R0 tbl E log ks,
    slots_ok w m R0 tbl -> log_flat E log ->
    bv_unsigned (edenot E (EVar WV_S1)) = wa_s1 w ->
    (forall n, (32 <= n <= 40)%N -> ev E n = ev (HLib.Eseed R0 (wenv_vals w)) n) ->
    (forall k, In k (map fst tbl ++ ks) -> Forall (omiss E (EVar WV_S1) (wa_s1 w + k) 8) log) ->
    (forall k, In k (map fst tbl ++ ks) -> 0 <= wa_s1 w + k /\ wa_s1 w + k + 8 <= 2 ^ 64) ->
    (forall k, In k ks -> wr_at asegs m (wa_s1 w + k) 8) ->
    slots_ok w (mem_denot E m log) R0 (upd_slots log (EVar WV_S1) tbl ++ add_slots log (EVar WV_S1) ks).
  Proof.
    intros w m R0 tbl E log ks SL Hf Hb HE HO HR HW. unfold slots_ok in *. apply Forall_app. split.
    - induction tbl as [|[k e] t IH]; cbn [upd_slots]; [constructor|].
      inversion SL as [|? ? SL0 SL1]; subst. cbn [fst snd] in SL0.
      assert (HO0 : Forall (omiss E (EVar WV_S1) (wa_s1 w + k) 8) log) by (apply HO; left; reflexivity).
      assert (HR0 : 0 <= wa_s1 w + k /\ wa_s1 w + k + 8 <= 2 ^ 64) by (apply HR; left; reflexivity).
      assert (IHt : Forall (fun ke => rw_cells asegs (mem_denot E m log) (wa_s1 w + fst ke)
                               [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) (upd_slots log (EVar WV_S1) t)).
      { apply IH; [exact SL1 | intros k' Hk'; apply HO; right; exact Hk' | intros k' Hk'; apply HR; right; exact Hk'].
        }
      rewrite <- Hb in HO0.
      destruct (lword log (EVar WV_S1) k) as [[v|]|] eqn:EW.
      + destruct (wclosed v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn [fst snd].
        apply rw_C8_of_rdn; [lia | lia | |].
        * rewrite <- Hb. rewrite (rdn_slot_some asegs E m log (EVar WV_S1) k v Hf HO0 EW ltac:(lia) ltac:(lia)).
          rewrite (edenot_wclosed E (HLib.Eseed R0 (wenv_vals w)) v WC HE). reflexivity.
        * destruct SL0 as [_ W0].
          destruct W0 as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
      + exact IHt.
      + constructor; [| exact IHt]. cbn [fst snd].
        apply rw_C8_of_rdn; [lia | lia | |].
        * rewrite <- Hb. rewrite (rdn_slot_none asegs E m log (EVar WV_S1) k Hf HO0 EW ltac:(lia) ltac:(lia)).
          rewrite Hb. apply rdn_of_rw_C8. exact SL0.
        * destruct SL0 as [_ W0]. destruct W0 as (W1 & W2 & W3). split; [lia|]. split; [lia|].
          intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
    - clear SL. induction ks as [|k t IH]; cbn [add_slots]; [constructor|].
      assert (HO0 : Forall (omiss E (EVar WV_S1) (wa_s1 w + k) 8) log) by (apply HO; apply in_app_iff; right; left; reflexivity).
      assert (HR0 : 0 <= wa_s1 w + k /\ wa_s1 w + k + 8 <= 2 ^ 64) by (apply HR; apply in_app_iff; right; left; reflexivity).
      assert (IHt : Forall (fun ke => rw_cells asegs (mem_denot E m log) (wa_s1 w + fst ke)
                               [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) (add_slots log (EVar WV_S1) t)).
      { apply IH; [ intros k' Hk'; apply HO; apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; exact Hk'
                  | intros k' Hk'; apply HR; apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; exact Hk'
                  | intros k' Hk'; apply HW; right; exact Hk' ]. }
      rewrite <- Hb in HO0.
      destruct (lword log (EVar WV_S1) k) as [[v|]|] eqn:EW; [| exact IHt | exact IHt].
      destruct (wclosed v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn [fst snd].
      apply rw_C8_of_rdn; [lia | lia | |].
      + rewrite <- Hb. rewrite (rdn_slot_some asegs E m log (EVar WV_S1) k v Hf HO0 EW ltac:(lia) ltac:(lia)).
        rewrite (edenot_wclosed E (HLib.Eseed R0 (wenv_vals w)) v WC HE). reflexivity.
      + pose proof (HW k ltac:(left; reflexivity)) as (W1 & W2 & W3). split; [lia|]. split; [lia|].
        intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
  Qed.
End Slots.

Section BSlots.
  Context {HCEIL : HeapCeil}.
  Variable H : BsIface.asr.

  Lemma bslots_mem_denot : forall (w : pmwA H) (b : expr) (B : Z) m R0 tbl E log ks,
    Forall (fun ke => rw_cells asegs m (B + fst ke) [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) tbl -> log_flat E log ->
    bv_unsigned (edenot E b) = B ->
    (forall n, (32 <= n <= 40)%N -> ev E n = ev (HLib.Eseed R0 (wenv_vals w)) n) ->
    (forall k, In k (map fst tbl ++ ks) -> Forall (omiss E b (B + k) 8) log) ->
    (forall k, In k (map fst tbl ++ ks) -> 0 <= B + k /\ B + k + 8 <= 2 ^ 64) ->
    (forall k, In k ks -> wr_at asegs m (B + k) 8) ->
    Forall (fun ke => rw_cells asegs (mem_denot E m log) (B + fst ke) [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))])
      (upd_slots log b tbl ++ add_slots log b ks).
  Proof.
    intros w b B m R0 tbl E log ks SL Hf Hb HE HO HR HW. apply Forall_app. split.
    - induction tbl as [|[k e] t IH]; cbn [upd_slots]; [constructor|].
      apply Forall_cons_iff in SL as [SL0 SL1]. cbn [fst snd] in SL0.
      assert (HO0 : Forall (omiss E b (B + k) 8) log) by (apply HO; left; reflexivity).
      assert (HR0 : 0 <= B + k /\ B + k + 8 <= 2 ^ 64) by (apply HR; left; reflexivity).
      assert (IHt : Forall (fun ke => rw_cells asegs (mem_denot E m log) (B + fst ke)
                               [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) (upd_slots log b t)).
      { apply IH; [exact SL1 | intros k' Hk'; apply HO; right; exact Hk' | intros k' Hk'; apply HR; right; exact Hk'].
        }
      rewrite <- Hb in HO0.
      destruct (lword log b k) as [[v|]|] eqn:EW.
      + destruct (wclosed v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn [fst snd].
        apply rw_C8_of_rdn; [lia | lia | |].
        * rewrite <- Hb. rewrite (rdn_slot_some asegs E m log b k v Hf HO0 EW ltac:(lia) ltac:(lia)).
          rewrite (edenot_wclosed E (HLib.Eseed R0 (wenv_vals w)) v WC HE). reflexivity.
        * destruct SL0 as [_ W0].
          destruct W0 as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
      + exact IHt.
      + constructor; [| exact IHt]. cbn [fst snd].
        apply rw_C8_of_rdn; [lia | lia | |].
        * rewrite <- Hb. rewrite (rdn_slot_none asegs E m log b k Hf HO0 EW ltac:(lia) ltac:(lia)).
          rewrite Hb. apply rdn_of_rw_C8. exact SL0.
        * destruct SL0 as [_ W0]. destruct W0 as (W1 & W2 & W3). split; [lia|]. split; [lia|].
          intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
    - clear SL. induction ks as [|k t IH]; cbn [add_slots]; [constructor|].
      assert (HO0 : Forall (omiss E b (B + k) 8) log) by (apply HO; apply in_app_iff; right; left; reflexivity).
      assert (HR0 : 0 <= B + k /\ B + k + 8 <= 2 ^ 64) by (apply HR; apply in_app_iff; right; left; reflexivity).
      assert (IHt : Forall (fun ke => rw_cells asegs (mem_denot E m log) (B + fst ke)
                               [C8 (edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) (add_slots log b t)).
      { apply IH; [ intros k' Hk'; apply HO; apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; exact Hk'
                  | intros k' Hk'; apply HR; apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; exact Hk'
                  | intros k' Hk'; apply HW; right; exact Hk' ]. }
      rewrite <- Hb in HO0.
      destruct (lword log b k) as [[v|]|] eqn:EW; [| exact IHt | exact IHt].
      destruct (wclosed v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn [fst snd].
      apply rw_C8_of_rdn; [lia | lia | |].
      + rewrite <- Hb. rewrite (rdn_slot_some asegs E m log b k v Hf HO0 EW ltac:(lia) ltac:(lia)).
        rewrite (edenot_wclosed E (HLib.Eseed R0 (wenv_vals w)) v WC HE). reflexivity.
      + pose proof (HW k ltac:(left; reflexivity)) as (W1 & W2 & W3). split; [lia|]. split; [lia|].
        intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
  Qed.
End BSlots.

Lemma rw_cells_C8s : forall m xs A, 0 <= A -> A + 8 * Z.of_nat (length xs) <= 2 ^ 64 ->
  (forall i x, nth_error xs i = Some x -> rw_cells asegs m (A + 8 * Z.of_nat i) [C8 x]) ->
  rw_cells asegs m A (map C8 xs).
Proof.
  intros m xs. induction xs as [|x xs IH]; intros A H0 H1 HX.
  - split; [split; [cbn; exact I|] |].
    + cbn [cells_bytes]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - change (map C8 (x :: xs)) with ([C8 x] ++ map C8 xs). apply rw_cells_app. split.
    + specialize (HX 0%nat x eq_refl). rewrite Z.add_0_r in HX. exact HX.
    + cbn [cells_size csize]. apply IH; [lia | cbn [length] in H1; lia |].
      intros i y Hy. specialize (HX (S i) y Hy). replace (A + Z.of_nat (8 + 0) + 8 * Z.of_nat i) with (A + 8 * Z.of_nat (S i)) by lia.
      exact HX.
Qed.

Lemma omiss_of_sym : forall E b y n log wins,
  forallb (fun se => (expr_eqb (a_base (e_addr se)) b || sym_inside wins se)%bool) log = true ->
  Forall (fun iv : Z * Z => snd iv <= y \/ y + n <= fst iv) (num_wins E wins) ->
  Forall (omiss E b y n) log.
Proof.
  intros E b y n log wins Hb Hw. apply Forall_forall. intros se Hse Hne.
  pose proof (proj1 (forallb_forall _ _) Hb se Hse) as K. cbn in K. rewrite Hne in K. cbn in K.
  pose proof (sym_inside_sound E wins se K) as I.
  clear Hb K Hse. induction (num_wins E wins) as [|[lo hi] t IH]; cbn in I; [contradiction|].
  inversion Hw as [|? ? Hw0 Hw1]; subst. cbn in Hw0.
  destruct I as [I|I]; [| exact (IH Hw1 I)]. destruct Hw0; [left | right]; lia.
Qed.

Fixpoint lfield (log : list sentry) (b : expr) (k : Z) (w : nat) : option (option expr) :=
  match log with
  | [] => None
  | SE a w' v :: rest =>
      if (expr_eqb (a_base a) b && (a_off a <? k + Z.of_nat w) && (k <? a_off a + Z.of_nat w'))%bool then
        if (Z.eqb (a_off a) k && Nat.eqb w' w)%bool then Some (Some v) else Some None
      else lfield rest b k w
  end.

Definition fmiss (b : expr) (k : Z) (w : nat) (e : sentry) : Prop :=
  expr_eqb (a_base (e_addr e)) b = true -> a_off (e_addr e) + Z.of_nat (e_width e) <= k \/ k + Z.of_nat w <= a_off (e_addr e).

Lemma lfield_some : forall log b k w v, lfield log b k w = Some (Some v) ->
  exists pre post, log = pre ++ SE (SA b k) w v :: post /\ Forall (fmiss b k w) pre.
Proof.
  induction log as [|[a w' v'] rest IH]; intros b k w v H; cbn [lfield] in H; [discriminate|].
  destruct ((expr_eqb (a_base a) b && (a_off a <? k + Z.of_nat w) && (k <? a_off a + Z.of_nat w'))%bool) eqn:E1.
  - destruct ((Z.eqb (a_off a) k && Nat.eqb w' w)%bool) eqn:E2; [|discriminate].
    injection H as <-. apply andb_true_iff in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Nat.eqb_eq in E3.
    apply andb_true_iff in E1 as [E1 _]. apply andb_true_iff in E1 as [E1 _]. apply expr_eqb_true in E1.
    exists [], rest. split; [| constructor]. destruct a as [ab ao]. cbn in E1, E2. subst. reflexivity.
  - destruct (IH b k w v H) as (pre & post & Ep & Fp). exists (SE a w' v' :: pre), post. split; [rewrite Ep; reflexivity|].
    constructor; [| exact Fp]. intros Eb. cbn [e_addr e_width] in *. rewrite Eb in E1. cbn in E1.
    apply andb_false_iff in E1 as [E1|E1]; [apply Z.ltb_ge in E1 | apply Z.ltb_ge in E1]; lia.
Qed.

Lemma lfield_none_lbyte : forall log b k w i, lfield log b k w = None -> 0 <= i < Z.of_nat w -> lbyte log b (k + i) = None.
Proof.
  induction log as [|[a w' v'] rest IH]; intros b k w i H Hi; cbn [lfield lbyte] in *; [reflexivity|].
  destruct ((expr_eqb (a_base a) b && (a_off a <? k + Z.of_nat w) && (k <? a_off a + Z.of_nat w'))%bool) eqn:E1.
  - destruct ((Z.eqb (a_off a) k && Nat.eqb w' w)%bool); discriminate.
  - destruct (expr_eqb (a_base a) b) eqn:Eb; cbn [andb] in *.
    + destruct ((a_off a <=? k + i) && (k + i <? a_off a + Z.of_nat w'))%bool eqn:E2; [| exact (IH b k w i H Hi)].
      exfalso. apply andb_true_iff in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
      apply andb_false_iff in E1 as [E1|E1]; [apply Z.ltb_ge in E1 | apply Z.ltb_ge in E1]; lia.
    + exact (IH b k w i H Hi).
Qed.

Lemma rdn_field_none : forall segs E M log b k w,
  log_flat E log -> Forall (omiss E b (bv_unsigned (edenot E b) + k) (Z.of_nat w)) log -> lfield log b k w = None ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + Z.of_nat w <= 2 ^ 64 ->
  PropExec.rdn segs (mem_denot E M log) (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) w
  = PropExec.rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) w.
Proof.
  intros segs E M log b k w Hf HO HN H0 H1. apply PropExec.rdn_ext.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E b) + k) (2 ^ 64) ltac:(lia)).
    destruct w as [|w']; [lia|]. rewrite Z.mod_small by lia. lia.
  - intros x Hx. assert (HM0 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) = bv_unsigned (edenot E b) + k).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      destruct w as [|w']; [cbn in Hx; lia|]. rewrite Z.mod_small by lia. reflexivity. }
    rewrite HM0 in Hx.
    set (i := bv_unsigned x - (bv_unsigned (edenot E b) + k)).
    assert (Hi : 0 <= i < Z.of_nat w) by (subst i; lia).
    pose proof (mem_denot_lbyte E M log b (k + i) Hf) as K.
    assert (HM : Forall (lmiss E b (bv_unsigned (edenot E b) + (k + i))) log).
    { eapply Forall_impl; [| exact HO]. intros e He. unfold lmiss. destruct (expr_eqb (a_base (e_addr e)) b) eqn:Eb; [left; reflexivity|].
      right. destruct (He Eb); [left | right]; lia. }
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    specialize (K HM ltac:(lia)). rewrite (lfield_none_lbyte log b k w i HN Hi) in K.
    replace x with (Z_to_bv 64 (bv_unsigned (edenot E b) + (k + i))); [exact K|].
    apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. subst i. lia.
Qed.

Lemma rdn_field_some : forall segs E M log b k w v,
  log_flat E log -> Forall (omiss E b (bv_unsigned (edenot E b) + k) (Z.of_nat w)) log -> lfield log b k w = Some (Some v) ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + Z.of_nat w <= 2 ^ 64 ->
  PropExec.rdn segs (mem_denot E M log) (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) w
  = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros segs E M log b k w v Hf HO HS H0 H1.
  destruct (lfield_some log b k w v HS) as (pre & post & -> & Fp).
  assert (Ha : adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k)).
  { unfold adenot, v_addi. cbn [a_base a_off]. reflexivity. }
  rewrite <- Ha. apply LbB_Conv.rdn_mem_denot_hit; [exact Hf|].
  apply Forall_forall. intros e He.
  assert (HO' : omiss E b (bv_unsigned (edenot E b) + k) (Z.of_nat w) e).
  { apply (proj1 (Forall_forall _ _) HO). apply in_app_iff. left. exact He. }
  assert (HS' : fmiss b k w e) by exact (proj1 (Forall_forall _ _) Fp e He).
  unfold estart at 2 3. cbn [a_base a_off].
  unfold omiss, fmiss in *. destruct (expr_eqb (a_base (e_addr e)) b) eqn:Eb.
  - pose proof (expr_eqb_true _ _ Eb) as Eab. destruct (HS' eq_refl) as [L|L]; [left | right];
      unfold estart; rewrite Eab; lia.
  - destruct (HO' eq_refl); [left | right]; lia.
Qed.

Definition sval (E : env) (log : list sentry) (b : expr) (k : Z) (w : nat) (old : Z) : Z :=
  match lfield log b k w with
  | Some (Some v) => bv_unsigned (edenot E v)
  | _ => old
  end.
Definition field_ok (log : list sentry) (b : expr) (k : Z) (w : nat) : bool :=
  match lfield log b k w with Some None => false | _ => true end.

Lemma sval_none : forall E log b k w old, lfield log b k w = None -> sval E log b k w old = old.
Proof. intros E log b k w old H. unfold sval. rewrite H. reflexivity. Qed.

Lemma fld_field_after : forall E M log b B k w old,
  log_flat E log -> bv_unsigned (edenot E b) = B ->
  Forall (omiss E b (B + k) (Z.of_nat w)) log -> field_ok log b k w = true ->
  0 <= B + k -> B + k + Z.of_nat w <= 2 ^ 64 ->
  CRep.fld ASEGS M (B + k) w old ->
  CRep.fld ASEGS (mem_denot E M log) (B + k) w (sval E log b k w old).
Proof.
  intros E M log b B k w old Hf HB HO Hok H0 H1 F. subst B. unfold sval, field_ok in *. unfold CRep.fld in *.
  destruct (lfield log b k w) as [[v|]|] eqn:EL.
  - rewrite (rdn_field_some ASEGS E M log b k w v Hf HO EL H0 H1). rewrite Z_to_bv_bv_unsigned. reflexivity.
  - discriminate.
  - rewrite (rdn_field_none ASEGS E M log b k w Hf HO EL H0 H1). exact F.
Qed.

Lemma wbytes_defined : forall bs m (a x : word), m x <> None -> wbytes m a bs x <> None.
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. destruct (bv_eqb x a); [discriminate | exact Hx].
Qed.

Lemma mem_denot_defined : forall E M log x, M x <> None -> mem_denot E M log x <> None.
Proof.
  intros E M log. induction log as [|[a w v] rest IH]; intros x Hx; cbn [mem_denot]; [exact Hx|].
  apply wbytes_defined. apply IH. exact Hx.
Qed.
