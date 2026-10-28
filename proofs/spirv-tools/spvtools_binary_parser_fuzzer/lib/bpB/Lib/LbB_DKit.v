(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMem BCells BArr BLFrame BStep BellsX BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BLPropExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_FKit LbB_Call.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

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

Definition omiss (E : env) (b : expr) (y n : Z) (e : sentry) : Prop :=
  expr_eqb (a_base (e_addr e)) b = false -> estart E (e_addr e) + Z.of_nat (e_width e) <= y \/ y + n <= estart E (e_addr e).

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

Definition wenv (W : list word) : env := HLib.Eseed bvmap_empty W.

Fixpoint wcl (k : N) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => (32 <=? n)%N && (n <? k)%N
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => wcl k a && wcl k b
  | EExt _ _ _ a => wcl k a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_wcl : forall E E' k e, wcl k e = true -> (forall n, (32 <= n < k)%N -> ev E n = ev E' n) ->
  edenot E e = edenot E' e.
Proof.
  intros E E' k e. induction e; cbn [wcl edenot]; intros Hc HE; try discriminate; try reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. apply N.leb_le in H1. apply N.ltb_lt in H2. apply HE. lia.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
Qed.

Definition wbound (W : list word) : N := (32 + N.of_nat (length W))%N.

Lemma Eseed_wenv : forall R W X n, (32 <= n < wbound W)%N -> ev (HLib.Eseed R (W ++ X)) n = ev (wenv W) n.
Proof.
  intros R W X n Hn. unfold wbound in Hn. unfold wenv, HLib.Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [lia|]. rewrite app_nth1 by lia. reflexivity.
Qed.

Definition fent : Type := (Z * nat * expr)%type.

Definition ftbl (W : list word) (B : Z) (m : mem) (tbl : list fent) : Prop :=
  Forall (fun f => match f with (k, w, e) =>
             rw_cells asegs m (B + k) [CB w (word_to_le_bytes w (edenot (wenv W) e))] end) tbl.

Definition fkeys (tbl : list fent) : list (Z * nat) := map (fun f => match f with (k, w, _) => (k, w) end) tbl.

Definition fin (lo hi : Z) (ks : list (Z * nat)) : bool :=
  forallb (fun kw => (lo <=? fst kw) && (fst kw + Z.of_nat (snd kw) <=? hi) && (1 <=? snd kw)%nat && (snd kw <=? 8)%nat)%bool ks.

Lemma fin_In : forall lo hi ks k w, fin lo hi ks = true -> In (k, w) ks -> lo <= k /\ k + Z.of_nat w <= hi /\ (1 <= w <= 8)%nat.
Proof.
  intros lo hi ks k w H Hi. pose proof (proj1 (forallb_forall _ _) H (k, w) Hi) as K. cbn [fst snd] in K.
  apply andb_true_iff in K as [K K4]. apply andb_true_iff in K as [K K3]. apply andb_true_iff in K as [K1 K2].
  apply Z.leb_le in K1. apply Z.leb_le in K2. apply Nat.leb_le in K3. apply Nat.leb_le in K4. lia.
Qed.

Lemma fkeys_In : forall tbl k w e, In (k, w, e) tbl -> In (k, w) (fkeys tbl).
Proof. intros tbl k w e H. unfold fkeys. apply in_map_iff. exists (k, w, e). split; [reflexivity | exact H]. Qed.

Lemma ftbl_In : forall W B m tbl k w e, ftbl W B m tbl -> In (k, w, e) tbl ->
  rw_cells asegs m (B + k) [CB w (word_to_le_bytes w (edenot (wenv W) e))].
Proof. intros W B m tbl k w e H Hi. exact (proj1 (Forall_forall _ _) H (k, w, e) Hi). Qed.

Lemma ftbl_app : forall W B m t1 t2, ftbl W B m t1 -> ftbl W B m t2 -> ftbl W B m (t1 ++ t2).
Proof. intros W B m t1 t2 A C. apply Forall_app. split; assumption. Qed.

Lemma ftbl_nil : forall W B m, ftbl W B m [].
Proof. intros. constructor. Qed.

Lemma rw_CB_of_rdn : forall m A (w : nat) x, 0 <= A -> A + Z.of_nat w <= 2 ^ 64 ->
  PropExec.rdn asegs m (Z_to_bv 64 A) w = Some (word_to_le_bytes w x) -> wr_at asegs m A (Z.of_nat w) ->
  rw_cells asegs m A [CB w (word_to_le_bytes w x)].
Proof.
  intros m A w x H0 H1 HR HW. split; [split|].
  - cbn. split; [apply length_Z_to_le_bytes | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_of_rdn; [lia | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia |].
    unfold word_to_le_bytes in *. rewrite length_Z_to_le_bytes. exact HR.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma rdn_of_rw_CB : forall m A (w : nat) x, rw_cells asegs m A [CB w (word_to_le_bytes w x)] ->
  PropExec.rdn asegs m (Z_to_bv 64 A) w = Some (word_to_le_bytes w x).
Proof.
  intros m A w x RW. pose proof (rw_cells_read asegs m A [CB w (word_to_le_bytes w x)] 0 (CB w (word_to_le_bytes w x)) RW eq_refl) as K.
  cbn [csize cbytes] in K. rewrite Z.add_0_r in K. unfold wa in K. rewrite LbB_Conv.rdn_of_ov in K. exact K.
Qed.

Lemma wr_at_of_rw_CB : forall m A (w : nat) bs, rw_cells asegs m A [CB w bs] -> wr_at asegs m A (Z.of_nat w).
Proof. intros m A w bs [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. exact HW. Qed.

Lemma fld_of_ftbl : forall W B m tbl k w e v, ftbl W B m tbl -> In (k, w, e) tbl -> edenot (wenv W) e = Z_to_bv 64 v ->
  CRep.fld ASEGS m (B + k) w v.
Proof.
  intros W B m tbl k w e v H Hi He. pose proof (ftbl_In W B m tbl k w e H Hi) as RW. rewrite He in RW.
  unfold CRep.fld. exact (rdn_of_rw_CB m (B + k) w (Z_to_bv 64 v) RW).
Qed.

Fixpoint fupd (log : list sentry) (b : expr) (k0 : N) (tbl : list fent) : list fent :=
  match tbl with
  | [] => []
  | (k, w, e) :: t =>
      match lfield log b k w with
      | None => (k, w, e) :: fupd log b k0 t
      | Some (Some v) => if wcl k0 v then (k, w, v) :: fupd log b k0 t else fupd log b k0 t
      | Some None => fupd log b k0 t
      end
  end.
Fixpoint fadd (log : list sentry) (b : expr) (k0 : N) (ks : list (Z * nat)) : list fent :=
  match ks with
  | [] => []
  | (k, w) :: t =>
      match lfield log b k w with
      | Some (Some v) => if wcl k0 v then (k, w, v) :: fadd log b k0 t else fadd log b k0 t
      | _ => fadd log b k0 t
      end
  end.

Lemma omiss_sub : forall E b y n y' n' log, Forall (omiss E b y n) log -> y <= y' -> y' + n' <= y + n ->
  Forall (omiss E b y' n') log.
Proof.
  intros E b y n y' n' log H H1 H2. eapply Forall_impl; [| exact H]. intros e He Hne.
  destruct (He Hne); [left | right]; lia.
Qed.

Lemma wr_at_mem_denot : forall E m log A n, wr_at asegs m A n -> wr_at asegs (mem_denot E m log) A n.
Proof.
  intros E m log A n (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply LbB_Conv.wmono_mem_denot. apply W3. exact Hi.
Qed.

Lemma ftbl_run : forall W B m tbl E log b lo hi ks,
  ftbl W B m tbl -> log_flat E log -> bv_unsigned (edenot E b) = B ->
  (forall n, (32 <= n < wbound W)%N -> ev E n = ev (wenv W) n) ->
  Forall (omiss E b (B + lo) (hi - lo)) log ->
  fin lo hi (fkeys tbl ++ ks) = true -> 0 <= B + lo -> B + hi <= 2 ^ 64 ->
  (forall k w, In (k, w) ks -> wr_at asegs m (B + k) (Z.of_nat w)) ->
  ftbl W B (mem_denot E m log) (fupd log b (wbound W) tbl ++ fadd log b (wbound W) ks).
Proof.
  intros W B m tbl E log b lo hi ks H Hf Hb HE HO Hfin H0 H1 HW.
  assert (HF : forall k w, In (k, w) (fkeys tbl ++ ks) -> lo <= k /\ k + Z.of_nat w <= hi /\ (1 <= w <= 8)%nat)
    by (intros k w Hk; exact (fin_In lo hi _ k w Hfin Hk)).
  apply ftbl_app.
  - clear HW. induction tbl as [|[[k w] e] t IH]; cbn [fupd]; [constructor|].
    apply Forall_cons_iff in H as [H0' H1']. cbn beta iota in H0'.
    assert (IHt : ftbl W B (mem_denot E m log) (fupd log b (wbound W) t)).
    { apply IH; [exact H1' | |].
      - unfold fin in *. cbn [fkeys map app forallb] in Hfin. apply andb_true_iff in Hfin as [_ Hfin]. exact Hfin.
      - intros k' w' Hk'. apply HF. cbn [fkeys map app]. right. exact Hk'. }
    destruct (HF k w ltac:(cbn [fkeys map app]; left; reflexivity)) as (Hk1 & Hk2 & Hw).
    assert (HO0 : Forall (omiss E b (bv_unsigned (edenot E b) + k) (Z.of_nat w)) log) by (rewrite Hb; eapply omiss_sub; [exact HO | lia | lia]).
    destruct (lfield log b k w) as [[v|]|] eqn:EW.
    + destruct (wcl (wbound W) v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn beta iota.
      apply rw_CB_of_rdn; [lia | lia | |].
      * rewrite <- Hb. rewrite (rdn_field_some asegs E m log b k w v Hf HO0 EW ltac:(lia) ltac:(lia)).
        rewrite (edenot_wcl E (wenv W) (wbound W) v WC HE). reflexivity.
      * apply wr_at_mem_denot. exact (wr_at_of_rw_CB _ _ _ _ H0').
    + exact IHt.
    + constructor; [| exact IHt]. cbn beta iota.
      apply rw_CB_of_rdn; [lia | lia | |].
      * rewrite <- Hb. rewrite (rdn_field_none asegs E m log b k w Hf HO0 EW ltac:(lia) ltac:(lia)).
        rewrite Hb. apply rdn_of_rw_CB. exact H0'.
      * apply wr_at_mem_denot. exact (wr_at_of_rw_CB _ _ _ _ H0').
  - clear H. induction ks as [|[k w] t IH]; cbn [fadd]; [constructor|].
    assert (IHt : ftbl W B (mem_denot E m log) (fadd log b (wbound W) t)).
    { apply IH.
      - unfold fin in *. rewrite forallb_app in *. apply andb_true_iff in Hfin as [Ha Hb']. cbn [forallb] in Hb'.
        apply andb_true_iff in Hb' as [_ Hb']. rewrite Ha, Hb'. reflexivity.
      - intros k' w' Hk'. apply HW. right. exact Hk'.
      - intros k' w' Hk'. apply HF. apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; exact Hk'. }
    destruct (HF k w ltac:(apply in_app_iff; right; left; reflexivity)) as (Hk1 & Hk2 & Hw).
    assert (HO0 : Forall (omiss E b (bv_unsigned (edenot E b) + k) (Z.of_nat w)) log) by (rewrite Hb; eapply omiss_sub; [exact HO | lia | lia]).
    destruct (lfield log b k w) as [[v|]|] eqn:EW; [| exact IHt | exact IHt].
    destruct (wcl (wbound W) v) eqn:WC; [| exact IHt]. constructor; [| exact IHt]. cbn beta iota.
    apply rw_CB_of_rdn; [lia | lia | |].
    + rewrite <- Hb. rewrite (rdn_field_some asegs E m log b k w v Hf HO0 EW ltac:(lia) ltac:(lia)).
      rewrite (edenot_wcl E (wenv W) (wbound W) v WC HE). reflexivity.
    + apply wr_at_mem_denot. apply HW. left. reflexivity.
Qed.

Definition fkn (b : expr) (tbl : list fent) : list kentry :=
  map (fun f => match f with (k, w, e) => KWord (SA b k) w e end) tbl.

Definition fwcl (k0 : N) (tbl : list fent) : bool := forallb (fun f => match f with (_, _, e) => wcl k0 e end) tbl.

Lemma ftbl_kn : forall W B m tbl E b lo hi,
  ftbl W B m tbl -> bv_unsigned (edenot E b) = B ->
  (forall n, (32 <= n < wbound W)%N -> ev E n = ev (wenv W) n) ->
  fwcl (wbound W) tbl = true -> fin lo hi (fkeys tbl) = true -> 0 <= B + lo -> B + hi <= 2 ^ 64 ->
  know_ok asegs E m (fkn b tbl).
Proof.
  intros W B m tbl E b lo hi H Hb HE Hc Hfin H0 H1. unfold know_ok, fkn. apply Forall_map.
  apply Forall_forall. intros [[k w] e] Hi.
  pose proof (ftbl_In W B m tbl k w e H Hi) as RW.
  destruct (fin_In lo hi _ k w Hfin (fkeys_In tbl k w e Hi)) as (Hk1 & Hk2 & Hw).
  pose proof (proj1 (forallb_forall _ _) Hc (k, w, e) Hi) as Hce. cbn beta iota in Hce.
  cbn [kentry_ok]. split; [lia|].
  assert (Hs : estart E (SA b k) = B + k) by (unfold estart; cbn [a_base a_off]; rewrite Hb; reflexivity).
  split; [unfold flat; rewrite Hs; lia|].
  rewrite (adenot_of_estart E (SA b k) (B + k) Hs ltac:(lia)).
  rewrite (edenot_wcl E (wenv W) (wbound W) e Hce HE).
  exact (rdn_of_rw_CB m (B + k) w _ RW).
Qed.

Lemma ftbl_munch : forall W B m m' tbl Wn lo hi,
  ftbl W B m tbl -> munch Wn m m' -> wmono asegs m m' ->
  fin lo hi (fkeys tbl) = true -> disjoint_from Wn (B + lo) (hi - lo) ->
  ftbl W B m' tbl.
Proof.
  intros W B m m' tbl Wn lo hi H MU WM Hfin HD. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) H (k, w, e) Hi) as RW. cbn beta iota in RW |- *.
  destruct (fin_In lo hi _ k w Hfin (fkeys_In tbl k w e Hi)) as (Hk1 & Hk2 & Hw).
  eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
  cbn [cells_size csize]. rewrite Nat.add_0_r.
  eapply disjoint_from_sub; [exact HD | lia | lia].
Qed.

Lemma aclient_range_sub {HCEIL : HeapCeil} : forall (H : asr) LB SP A n A' n', aclient_range H LB SP A n ->
  A <= A' -> A' + n' <= A + n -> aclient_range H LB SP A' n'.
Proof.
  intros H LB SP A n A' n' HR H1 H2. unfold aclient_range in *.
  destruct HR as [R|[R|[(b & Hb & R1 & R2)|[(b & Hb & R1 & R2)|[R|[R|R]]]]]].
  - left. lia.
  - right. left. intros a Ha. apply R. lia.
  - right. right. left. exists b. split; [exact Hb | lia].
  - right. right. right. left. exists b. split; [exact Hb | lia].
  - right. right. right. right. left. lia.
  - right. right. right. right. right. left. lia.
  - right. right. right. right. right. right. lia.
Qed.

Lemma ftbl_apres {HCEIL : HeapCeil} : forall (H : asr) LB SP W B m m' tbl lo hi,
  ftbl W B m tbl -> apres H LB SP m m' ->
  fin lo hi (fkeys tbl) = true -> aclient_range H LB SP (B + lo) (hi - lo) ->
  ftbl W B m' tbl.
Proof.
  intros H LB SP W B m m' tbl lo hi HT AP Hfin HC. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) HT (k, w, e) Hi) as RW. cbn beta iota in RW |- *.
  destruct (fin_In lo hi _ k w Hfin (fkeys_In tbl k w e Hi)) as (Hk1 & Hk2 & Hw).
  eapply (apres_rw_cells H); [exact AP | exact RW |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
  eapply aclient_range_sub; [exact HC | lia | lia].
Qed.

Definition fdrop (o n : Z) (tbl : list fent) : list fent :=
  List.filter (fun f => match f with (k, w, _) => (k + Z.of_nat w <=? o) || (o + n <=? k) end) tbl.

Lemma fdrop_sub : forall o n tbl f, In f (fdrop o n tbl) -> In f tbl.
Proof. intros o n tbl f H. unfold fdrop in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma ftbl_munch_drop : forall W B m m' tbl Wn lo hi o n,
  ftbl W B m tbl -> munch ((B + o, B + o + n) :: Wn) m m' -> wmono asegs m m' ->
  fin lo hi (fkeys tbl) = true -> disjoint_from Wn (B + lo) (hi - lo) -> 0 <= n ->
  ftbl W B m' (fdrop o n tbl).
Proof.
  intros W B m m' tbl Wn lo hi o n H MU WM Hfin HD Hn. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) H (k, w, e) (fdrop_sub o n tbl _ Hi)) as RW. cbn beta iota in RW |- *.
  destruct (fin_In lo hi _ k w Hfin (fkeys_In tbl k w e (fdrop_sub o n tbl _ Hi))) as (Hk1 & Hk2 & Hw).
  unfold fdrop in Hi. apply filter_In in Hi as [_ Hk]. apply orb_true_iff in Hk.
  eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
  cbn [cells_size csize]. rewrite Nat.add_0_r. cbn [disjoint_from]. split.
  - destruct Hk as [Hk|Hk]; [apply Z.leb_le in Hk | apply Z.leb_le in Hk]; lia.
  - eapply disjoint_from_sub; [exact HD | lia | lia].
Qed.

Fixpoint zents (o : Z) (j : nat) : list fent :=
  match j with O => [] | S j' => (o, 8%nat, ELit 0) :: zents (o + 8) j' end.

Lemma ftbl_zeros : forall W B m o (j : nat),
  rw_cells asegs m (B + o) [CB (8 * j) (repeat (Z_to_bv 8 0) (8 * j))] -> ftbl W B m (zents o j).
Proof.
  intros W B m o j. revert o. induction j as [|j IH]; intros o RW; cbn [zents]; [constructor|].
  replace (8 * S j)%nat with (8 + 8 * j)%nat in RW by lia.
  rewrite repeat_app in RW.
  assert (RW2 : rw_cells asegs m (B + o) [CB 8 (repeat (Z_to_bv 8 0) 8); CB (8 * j) (repeat (Z_to_bv 8 0) (8 * j))]).
  { destruct RW as [[Hwf Hb] Hw]. split; [split|].
    - cbn. rewrite !repeat_length. tauto.
    - cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r in Hb |- *. exact Hb.
    - cbn [cells_size csize] in Hw |- *. rewrite Nat.add_0_r in Hw. replace (8 + (8 * j + 0))%nat with (8 + 8 * j)%nat by lia. exact Hw. }
  change [CB 8 (repeat (Z_to_bv 8 0) 8); CB (8 * j) (repeat (Z_to_bv 8 0) (8 * j))]
    with ([CB 8 (repeat (Z_to_bv 8 0) 8)] ++ [CB (8 * j) (repeat (Z_to_bv 8 0) (8 * j))]) in RW2.
  apply rw_cells_app in RW2 as [R1 R2]. constructor.
  - cbn beta iota. replace (word_to_le_bytes 8 (edenot (wenv W) (ELit 0))) with (repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity).
    exact R1.
  - cbn [cells_size csize] in R2. replace (B + o + Z.of_nat (8 + 0)) with (B + (o + 8)) in R2 by lia. exact (IH (o + 8) R2).
Qed.

Definition rtbl (W : list word) (R : bvmap 5 word) (RT : list (reg * expr)) : Prop :=
  Forall (fun re => PropExec.getr R (fst re) = edenot (wenv W) (snd re)) RT.

Definition rtbl_okb (k0 : N) (RT : list (reg * expr)) : bool :=
  forallb (fun re => (wcl k0 (snd re) && negb (bv_eqb (fst re) 0%bv))%bool) RT.

Lemma regs_ok_of_rtbl : forall W X R RT, rtbl W R RT -> rtbl_okb (wbound W) RT = true ->
  regs_ok (HLib.Eseed R (W ++ X)) (HLib.srs sr_id RT) R.
Proof.
  intros W X R RT HT Hok. apply HLib.regs_ok_srs; [apply HLib.regs_ok_seed|].
  unfold rtbl, rtbl_okb in *. rewrite Forall_forall in *. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hok (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Kc Kr]. split.
  - intros ->. discriminate Kr.
  - pose proof (HT (r, e) Hin) as HTe. cbn [fst snd] in HTe. rewrite HTe.
    symmetry. apply (edenot_wcl _ _ (wbound W)); [exact Kc|]. intros n Hn. apply Eseed_wenv. exact Hn.
Qed.

Definition rtbl_chk (k0 : N) (sr : list expr) (RT : list (reg * expr)) : bool :=
  forallb (fun re => (expr_eqb (sr_get sr (fst re)) (snd re) && wcl k0 (snd re))%bool) RT.

Lemma rtbl_of_run : forall W X R sr R' RT,
  regs_ok (HLib.Eseed R (W ++ X)) sr R' -> rtbl_chk (wbound W) sr RT = true -> rtbl W R' RT.
Proof.
  intros W X R sr R' RT HR Hc. unfold rtbl, rtbl_chk in *. apply Forall_forall. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hc (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Ke Kc]. apply expr_eqb_eq in Ke.
  rewrite (HR r), Ke. apply (edenot_wcl _ _ (wbound W)); [exact Kc|]. intros n Hn. apply Eseed_wenv. exact Hn.
Qed.

Lemma rtbl_In : forall W R RT r e, rtbl W R RT -> In (r, e) RT -> PropExec.getr R r = edenot (wenv W) e.
Proof. intros W R RT r e H Hi. exact (proj1 (Forall_forall _ _) H (r, e) Hi). Qed.

Lemma rtbl_app : forall W R RT1 RT2, rtbl W R RT1 -> rtbl W R RT2 -> rtbl W R (RT1 ++ RT2).
Proof. intros W R RT1 RT2 A C. apply Forall_app. split; assumption. Qed.

Definition rsub (ks : list reg) (RT : list (reg * expr)) : bool :=
  forallb (fun re => existsb (fun r => bv_eqb r (fst re)) ks) RT.

Lemma rtbl_keep : forall W R R' RT ks, rtbl W R RT -> rsub ks RT = true ->
  (forall r, In r ks -> PropExec.getr R' r = PropExec.getr R r) -> rtbl W R' RT.
Proof.
  intros W R R' RT ks HT Hs HK. unfold rtbl, rsub in *. apply Forall_forall. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hs (r, e) Hin) as K. cbn [fst snd] in *.
  apply existsb_exists in K as (r' & Hr' & Eq). unfold bv_eqb in Eq. apply Z.eqb_eq in Eq. apply bv_eq in Eq. subst r'.
  rewrite (HK r Hr'). exact (proj1 (Forall_forall _ _) HT (r, e) Hin).
Qed.

Definition KEPT : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma omiss_of_two : forall E b1 b2 wl1 wh1 wl2 wh2 log y n,
  forallb (sym_inside [(b1, wl1, wh1); (b2, wl2, wh2)]) log = true ->
  (bv_unsigned (edenot E b2) + wh2 <= y \/ y + n <= bv_unsigned (edenot E b2) + wl2) ->
  Forall (omiss E b1 y n) log.
Proof.
  intros E b1 b2 wl1 wh1 wl2 wh2 log y n Hs HD. apply Forall_forall. intros se Hse Hne.
  pose proof (proj1 (forallb_forall _ _) Hs se Hse) as K. cbn [sym_inside] in K.
  unfold sym_in1 in K. rewrite Hne in K. cbn [andb orb] in K. rewrite orb_false_r in K.
  apply andb_true_iff in K as [K K2]. apply andb_true_iff in K as [K0 K1].
  apply expr_eqb_true in K0. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold estart. rewrite K0. lia.
Qed.

Lemma num_wins_two : forall E b1 b2 wl1 wh1 wl2 wh2,
  num_wins E [(b1, wl1, wh1); (b2, wl2, wh2)]
  = [(bv_unsigned (edenot E b1) + wl1, bv_unsigned (edenot E b1) + wh1); (bv_unsigned (edenot E b2) + wl2, bv_unsigned (edenot E b2) + wh2)].
Proof. reflexivity. Qed.

Section DKRun.
  Variable W : list word.
  Variables (b1 b2 : expr) (B1 B2 wl1 wh1 wl2 wh2 : Z).
  Hypothesis Hc1 : wcl (wbound W) b1 = true.
  Hypothesis Hc2 : wcl (wbound W) b2 = true.
  Hypothesis HB1 : bv_unsigned (edenot (wenv W) b1) = B1.
  Hypothesis HB2 : bv_unsigned (edenot (wenv W) b2) = B2.
  Hypothesis HW1 : 0 <= B1 + wl1 /\ wl1 <= wh1 /\ B1 + wh1 <= 2 ^ 64.
  Hypothesis HW2 : 0 <= B2 + wl2 /\ wl2 <= wh2 /\ B2 + wh2 <= 2 ^ 64.
  Hypothesis WDJ : B1 + wh1 <= B2 + wl2 \/ B2 + wh2 <= B1 + wl1.
  Variable P : mem -> Prop.
  Hypothesis P_step : forall m m', P m -> munch [(B1 + wl1, B1 + wh1); (B2 + wl2, B2 + wh2)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> P m'.

  Lemma dk_run : forall (Q : machine_state -> Prop) R F pc fc m ro RT SF DF X kst fuel stops scr nx SSr scs scr' RT' ks1 ks2,
    rfull R -> rtbl W R RT -> rtbl_okb (wbound W) RT = true ->
    ftbl W B1 m SF -> ftbl W B2 m DF -> P m -> mem_inv asegs m ->
    fwcl (wbound W) SF = true -> fwcl (wbound W) DF = true ->
    fin wl1 wh1 (fkeys SF ++ ks1) = true -> fin wl2 wh2 (fkeys DF ++ ks2) = true ->
    (forall k w, In (k, w) ks1 -> wr_at asegs m (B1 + k) (Z.of_nat w)) ->
    (forall k w, In (k, w) ks2 -> wr_at asegs m (B2 + k) (Z.of_nat w)) ->
    know_ok asegs (HLib.Eseed R (W ++ X)) m kst ->
    sym_exec asegs fuel true stops scr (SS pc (HLib.srs sr_id RT) [] (kst ++ fkn b1 SF ++ fkn b2 DF) nx) [] = (SSr, scs, scr') ->
    scs_denot asegs m (HLib.Eseed R (W ++ X)) scs ->
    forallb (sym_inside [(b1, wl1, wh1); (b2, wl2, wh2)]) (s_log SSr) = true ->
    rtbl_chk (wbound W) (s_regs SSr) RT' = true ->
    (forall R' m', rfull R' -> rtbl W R' RT' ->
        ftbl W B1 m' (fupd (s_log SSr) b1 (wbound W) SF ++ fadd (s_log SSr) b1 (wbound W) ks1) ->
        ftbl W B2 m' (fupd (s_log SSr) b2 (wbound W) DF ++ fadd (s_log SSr) b2 (wbound W) ks2) ->
        P m' -> mem_inv asegs m' -> munch [(B1 + wl1, B1 + wh1); (B2 + wl2, B2 + wh2)] m m' -> wmono asegs m m' ->
        evt asegs Q (MS R' F (Z_to_bv 64 (s_pc SSr)) fc None m' ro)) ->
    evt asegs Q (MS R F (Z_to_bv 64 pc) fc None m ro).
  Proof.
    intros Q R F pc fc m ro RT SF DF X kst fuel stops scr nx SSr scs scr' RT' ks1 ks2
           RF HT Hok F1 F2 HP MI Hc1' Hc2' Hf1 Hf2 HWk1 HWk2 HK Hex Hsc Hin Hrt K.
    set (E := HLib.Eseed R (W ++ X)).
    assert (HE : forall n, (32 <= n < wbound W)%N -> ev E n = ev (wenv W) n) by (intros n Hn; apply Eseed_wenv; exact Hn).
    assert (EB1 : bv_unsigned (edenot E b1) = B1) by (rewrite (edenot_wcl E (wenv W) (wbound W) b1 Hc1 HE); exact HB1).
    assert (EB2 : bv_unsigned (edenot E b2) = B2) by (rewrite (edenot_wcl E (wenv W) (wbound W) b2 Hc2 HE); exact HB2).
    pose proof (regs_ok_of_rtbl W X R RT HT Hok) as HR.
    assert (Hfin1 : fin wl1 wh1 (fkeys SF) = true) by (unfold fin in *; rewrite forallb_app in Hf1; apply andb_true_iff in Hf1; tauto).
    assert (Hfin2 : fin wl2 wh2 (fkeys DF) = true) by (unfold fin in *; rewrite forallb_app in Hf2; apply andb_true_iff in Hf2; tauto).
    assert (HKall : know_ok asegs E m (kst ++ fkn b1 SF ++ fkn b2 DF)).
    { unfold know_ok. apply Forall_app. split; [exact HK|]. apply Forall_app. split.
      - eapply (ftbl_kn W B1 m SF E b1 wl1 wh1); [exact F1 | exact EB1 | exact HE | exact Hc1' | exact Hfin1 | lia | lia].
      - eapply (ftbl_kn W B2 m DF E b2 wl2 wh2); [exact F2 | exact EB2 | exact HE | exact Hc2' | exact Hfin2 | lia | lia]. }
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (HLib.srs sr_id RT) _ nx SSr scs scr' E m ro R
                Hex HR HKall Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    eapply blk_then; [exact Hms | exact RF |]. intros RF'.
    assert (MU : munch [(B1 + wl1, B1 + wh1); (B2 + wl2, B2 + wh2)] m (mem_denot E m (s_log SSr))).
    { rewrite <- EB1, <- EB2. rewrite <- num_wins_two. apply munch_sym; [exact Hlf | exact Hin]. }
    pose proof (wmono_mem_denot E m (s_log SSr)) as WM.
    pose proof (msteps_mem_inv asegs _ _ Hms MI) as MI'. cbn [ms_mem] in MI'.
    apply K; [exact RF' | eapply rtbl_of_run; [exact HR' | exact Hrt] | | | eapply P_step; eassumption | exact MI' | exact MU | exact WM].
    - eapply (ftbl_run W B1 m SF E (s_log SSr) b1 wl1 wh1 ks1); [exact F1 | exact Hlf | exact EB1 | exact HE | | exact Hf1 | lia | lia | exact HWk1].
      eapply omiss_of_two; [exact Hin | rewrite EB2; lia].
    - eapply (ftbl_run W B2 m DF E (s_log SSr) b2 wl2 wh2 ks2); [exact F2 | exact Hlf | exact EB2 | exact HE | | exact Hf2 | lia | lia | exact HWk2].
      eapply (omiss_of_two E b2 b1 wl2 wh2 wl1 wh1); [| rewrite EB1; lia].
      apply forallb_forall. intros se Hse. pose proof (proj1 (forallb_forall _ _) Hin se Hse) as K0.
      cbn [sym_inside] in *. rewrite orb_false_r in *. apply orb_true_iff in K0. apply orb_true_iff. tauto.
  Qed.
End DKRun.

Definition regs_all : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Definition wtbl (k0 : N) (sr : list expr) : list (reg * expr) :=
  List.filter (fun re => wcl k0 (snd re)) (map (fun r => (r, sr_get sr r)) regs_all).

Definition kw_eqb (x y : Z * nat) : bool := (Z.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y))%bool.

Fixpoint newkeys (b : expr) (log : list sentry) (acc : list (Z * nat)) : list (Z * nat) :=
  match log with
  | [] => acc
  | SE a w _ :: t =>
      if expr_eqb (a_base a) b && negb (existsb (kw_eqb (a_off a, w)) acc) then newkeys b t ((a_off a, w) :: acc)
      else newkeys b t acc
  end.
Definition nkeys (b : expr) (log : list sentry) (tbl : list fent) : list (Z * nat) :=
  List.filter (fun kw => negb (existsb (kw_eqb kw) (fkeys tbl))) (newkeys b log []).

Definition kfix (stops : list Z) (pc : Z) (sr : list expr) (kb : list kentry) : list kentry :=
  skipn (length kb) (kn_fix 80 stops (SCR [] [] []) pc sr kb 60).

Definition ipost (R1 F : bvmap 5 word) (fc : bv 32) (d n spc : Z) (res : list byte) (m1 : mem) : machine_state -> Prop :=
  fun ms' => exists R2 m2, ms' = MS R2 F (ret_pc (PropExec.getr R1 1)) fc None m2 (BLPropExec.seg_rom asegs) /\ rfull R2
     /\ (forall r, In r (10%bv :: KEPT) -> PropExec.getr R2 r = PropExec.getr R1 r)
     /\ munch [(d, d + n); (spc - AINTRIN_STACK, spc)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ ACONST m2
     /\ rw_cells asegs m2 d [CB (Z.to_nat n) res] /\ stk asegs m2 (spc - AINTRIN_STACK) spc.

Section Intrin.
  Context {HCEIL : HeapCeil}.

  Lemma memset_icpt_u : forall R1 F fc m1 (d n c lo : Z) junk,
    rfull R1 -> PropExec.getr R1 10 = Z_to_bv 64 d -> PropExec.getr R1 11 = Z_to_bv 64 c -> PropExec.getr R1 12 = Z_to_bv 64 n ->
    0 <= c < 256 -> 0 <= d -> 0 <= n -> d + n < 2 ^ 64 ->
    rw_cells asegs m1 d [CB (Z.to_nat n) junk] -> accessible m1 d n -> shvis m1 d (d + n) ->
    stk asegs m1 lo (bv_unsigned (PropExec.getr R1 2)) -> aceil <= lo -> lo <= bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK ->
    mem_inv asegs m1 -> ACONST m1 -> n <= 2 ^ 40 -> in_app_mem d (d + n) -> aconst_ok (d, d + n) ->
    (d + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= d) ->
    evt asegs (ipost R1 F fc d n (bv_unsigned (PropExec.getr R1 2)) (poison_bytes (Z.to_nat n) c) m1)
        (MS R1 F (Z_to_bv 64 AMEMSET_STUB) fc None m1 (BLPropExec.seg_rom asegs)).
  Proof.
    intros R1 F fc m1 d n c lo junk RF H10 H11 H12 Hc Hd Hn Hdn DST ACC SV ST CE LO MI AC N40 INM AOK DJ.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF).
    assert (Ud : bv_unsigned (PropExec.getr R1 10) = d) by (rewrite H10; apply unsigned_lit; lia).
    assert (Un : bv_unsigned (PropExec.getr R1 12) = n) by (rewrite H12; apply unsigned_lit; lia).
    eapply evt_mono; [eapply (memset_icpt_ok (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5) (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15) (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30) (PropExec.getr R1 31) F fc m1 c junk lo); rewrite ?Ud, ?Un; eassumption|].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MU & WM & MI' & ST' & CB & AC').
    rewrite Ud, Un in *.
    exists (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) t0' t1' t2'
                (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) a1' a2' a3' a4' a5' a6' a7'
                (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22)
                (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                t3' t4' t5' t6'), m'.
    split; [exact E'|]. split; [apply rfull_mkR|]. split.
    { intros r Hr. cbn [In KEPT] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact AC'|]. split; [exact CB|].
    destruct ST' as (S0 & S1 & S). split; [lia|]. split; [lia|]. intros a Ha. apply S. unfold AINTRIN_STACK in *. lia.
  Qed.

  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma asan_memset_u : forall R1 F fc m1 (d n c lo : Z) junk,
    rfull R1 -> PropExec.getr R1 10 = Z_to_bv 64 d -> PropExec.getr R1 11 = Z_to_bv 64 c -> PropExec.getr R1 12 = Z_to_bv 64 n ->
    0 <= c < 256 -> 0 <= d -> 0 <= n -> d + n < 2 ^ 64 ->
    rw_cells asegs m1 d [CB (Z.to_nat n) junk] -> accessible m1 d n -> shvis m1 d (d + n) ->
    stk asegs m1 lo (bv_unsigned (PropExec.getr R1 2)) -> aceil <= lo -> lo <= bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK ->
    mem_inv asegs m1 -> ACONST m1 -> n <= 2 ^ 40 -> in_app_mem d (d + n) -> aconst_ok (d, d + n) ->
    (d + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= d) ->
    evt asegs (ipost R1 F fc d n (bv_unsigned (PropExec.getr R1 2)) (poison_bytes (Z.to_nat n) c) m1)
        (MS R1 F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (BLPropExec.seg_rom asegs)).
  Proof.
    intros R1 F fc m1 d n c lo junk RF H10 H11 H12 Hc Hd Hn Hdn DST ACC SV ST CE LO MI AC N40 INM AOK DJ.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF).
    assert (Ud : bv_unsigned (PropExec.getr R1 10) = d) by (rewrite H10; apply unsigned_lit; lia).
    assert (Un : bv_unsigned (PropExec.getr R1 12) = n) by (rewrite H12; apply unsigned_lit; lia).
    eapply evt_mono; [eapply ((ah_memset H HH) (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5) (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15) (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30) (PropExec.getr R1 31) F fc m1 c junk lo); rewrite ?Ud, ?Un; eassumption|].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MU & WM & MI' & ST' & CB & AC').
    rewrite Ud, Un in *.
    exists (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) t0' t1' t2'
                (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) a1' a2' a3' a4' a5' a6' a7'
                (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22)
                (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                t3' t4' t5' t6'), m'.
    split; [exact E'|]. split; [apply rfull_mkR|]. split.
    { intros r Hr. cbn [In KEPT] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact AC'|]. split; [exact CB|].
    destruct ST' as (S0 & S1 & S). split; [lia|]. split; [lia|]. intros a Ha. apply S. unfold AINTRIN_STACK in *. lia.
  Qed.

  Lemma asan_memcpy_u : forall R1 F fc m1 (d sa n lo : Z) src junk,
    rfull R1 -> PropExec.getr R1 10 = Z_to_bv 64 d -> PropExec.getr R1 11 = Z_to_bv 64 sa -> PropExec.getr R1 12 = Z_to_bv 64 n ->
    0 <= d -> 0 <= sa -> 0 <= n -> d + n < 2 ^ 64 -> sa + n < 2 ^ 64 ->
    bytes_at asegs m1 sa src -> length src = Z.to_nat n ->
    rw_cells asegs m1 d [CB (Z.to_nat n) junk] -> (sa + n <= d \/ d + n <= sa) ->
    accessible m1 sa n -> accessible m1 d n -> shvis m1 sa (sa + n) -> shvis m1 d (d + n) ->
    stk asegs m1 lo (bv_unsigned (PropExec.getr R1 2)) -> aceil <= lo -> lo <= bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK ->
    mem_inv asegs m1 -> ACONST m1 -> n <= 2 ^ 40 -> in_app_mem sa (sa + n) -> in_app_mem d (d + n) -> aconst_ok (d, d + n) ->
    (d + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= d) -> (sa + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= sa) ->
    evt asegs (ipost R1 F fc d n (bv_unsigned (PropExec.getr R1 2)) src m1)
        (MS R1 F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (BLPropExec.seg_rom asegs)).
  Proof.
    intros R1 F fc m1 d sa n lo src junk RF H10 H11 H12 Hd Hsa Hn Hdn Hsn SRC LEN DST SEP ACS ACD SVS SVD ST CE LO MI AC N40 INS IND AOK DJ DJS.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF).
    assert (Ud : bv_unsigned (PropExec.getr R1 10) = d) by (rewrite H10; apply unsigned_lit; lia).
    assert (Us : bv_unsigned (PropExec.getr R1 11) = sa) by (rewrite H11; apply unsigned_lit; lia).
    assert (Un : bv_unsigned (PropExec.getr R1 12) = n) by (rewrite H12; apply unsigned_lit; lia).
    eapply evt_mono; [eapply ((ah_memcpy H HH) (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5) (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15) (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30) (PropExec.getr R1 31) F fc m1 src junk lo); rewrite ?Ud, ?Us, ?Un; eassumption|].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MU & WM & MI' & ST' & CB & SB' & AC').
    rewrite Ud, Un in *.
    exists (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) t0' t1' t2'
                (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) a1' a2' a3' a4' a5' a6' a7'
                (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22)
                (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                t3' t4' t5' t6'), m'.
    split; [exact E'|]. split; [apply rfull_mkR|]. split.
    { intros r Hr. cbn [In KEPT] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact AC'|]. split; [exact CB|].
    destruct ST' as (S0 & S1 & S). split; [lia|]. split; [lia|]. intros a Ha. apply S. unfold AINTRIN_STACK in *. lia.
  Qed.
End Intrin.

Lemma rw_CB_len : forall m A (w : nat) bs, rw_cells asegs m A [CB w bs] -> length bs = w.
Proof. intros m A w bs [[Hwf _] _]. cbn in Hwf. tauto. Qed.

Lemma firstn_len_app : forall (T : Type) (l1 l2 : list T) (n : nat), length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof. intros T l1 l2 n <-. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [length firstn app]. rewrite IH. reflexivity. Qed.

Lemma rw_CB_byte : forall m A (w : nat) bs (j : nat), rw_cells asegs m A [CB w bs] -> (j < w)%nat ->
  rw_cells asegs m (A + Z.of_nat j) [CB 1 [nth j bs (Z_to_bv 8 0)]].
Proof.
  intros m A w bs j RW Hj.
  pose proof (rw_CB_len m A w bs RW) as L.
  destruct (rw_cells_CB_split asegs m A w j bs RW ltac:(lia)) as [_ R2].
  destruct (rw_cells_CB_split asegs m (A + Z.of_nat j) (w - j) 1 (skipn j bs) R2 ltac:(lia)) as [R3 _].
  replace (A + Z.of_nat j) with (A + Z.of_nat j) in R3 by lia.
  assert (E : firstn 1 (skipn j bs) = [nth j bs (Z_to_bv 8 0)]).
  { assert (Hj' : (j < length bs)%nat) by lia. clear - Hj'. revert j Hj'.
    induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
    destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
  rewrite E in R3. exact R3.
Qed.

Lemma byte_roundtrip : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
  intros b. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite unsigned_lit by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Definition bsplit (k : Z) (w : nat) (bs : list byte) : list fent :=
  map (fun j => (k + Z.of_nat j, 1%nat, ELit (bv_unsigned (nth j bs (Z_to_bv 8 0))))) (seq 0 w).

Definition fsplit1 (o n : Z) (f : fent) : list fent :=
  match f with
  | (k, w, ELit z) =>
      if ((k <? o + n) && (o <? k + Z.of_nat w) && negb ((o <=? k) && (k + Z.of_nat w <=? o + n)))%bool
      then bsplit k w (word_to_le_bytes w (Z_to_bv 64 z)) else [f]
  | _ => [f]
  end.

Definition fsplit (o n : Z) (tbl : list fent) : list fent := flat_map (fsplit1 o n) tbl.

Lemma ftbl_bsplit : forall W B m k w bs, rw_cells asegs m (B + k) [CB w bs] -> ftbl W B m (bsplit k w bs).
Proof.
  intros W B m k w bs RW. unfold ftbl, bsplit. apply Forall_forall. intros f Hf.
  apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn beta iota.
  cbn [edenot]. rewrite byte_roundtrip. replace (B + (k + Z.of_nat j)) with (B + k + Z.of_nat j) by lia.
  apply rw_CB_byte with (w := w); [exact RW | lia].
Qed.

Lemma ftbl_fsplit : forall W B m o n tbl, ftbl W B m tbl -> ftbl W B m (fsplit o n tbl).
Proof.
  intros W B m o n tbl H. unfold ftbl, fsplit in *. apply Forall_forall. intros f Hf.
  apply in_flat_map in Hf as (g & Hg & Hf). pose proof (proj1 (Forall_forall _ _) H g Hg) as RW.
  destruct g as [[k w] e]. cbn beta iota in RW.
  destruct e; cbn [fsplit1] in Hf; try (destruct Hf as [<-|[]]; exact RW).
  match type of Hf with In _ (if ?c then _ else _) => destruct c end.
  - cbn [edenot] in RW. exact (proj1 (Forall_forall _ _) (ftbl_bsplit W B m k w _ RW) f Hf).
  - destruct Hf as [<-|[]]. exact RW.
Qed.

Fixpoint zents1 (o : Z) (j : nat) : list fent :=
  match j with O => [] | S j' => (o, 1%nat, ELit 0) :: zents1 (o + 1) j' end.

Lemma ftbl_zeros1 : forall W B m o (j : nat),
  rw_cells asegs m (B + o) [CB j (repeat (Z_to_bv 8 0) j)] -> ftbl W B m (zents1 o j).
Proof.
  intros W B m o j. revert o. induction j as [|j IH]; intros o RW; cbn [zents1]; [constructor|].
  destruct (rw_cells_CB_split asegs m (B + o) (S j) 1 _ RW ltac:(lia)) as [R1 R2].
  constructor.
  - cbn beta iota. replace (word_to_le_bytes 1 (edenot (wenv W) (ELit 0))) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
    exact R1.
  - cbn [skipn repeat] in R2. replace (S j - 1)%nat with j in R2 by lia.
    replace (B + o + Z.of_nat 1) with (B + (o + 1)) in R2 by lia. exact (IH (o + 1) R2).
Qed.

Lemma ftbl_zres : forall W B m d n (j : nat), n = Z.of_nat (8 * j) ->
  rw_cells asegs m d [CB (Z.to_nat n) (BsShadow.poison_bytes (Z.to_nat n) 0)] -> ftbl W B m (zents (d - B) j).
Proof.
  intros W B m d n j -> RW. rewrite Nat2Z.id in RW. unfold BsShadow.poison_bytes in RW.
  apply ftbl_zeros. replace (B + (d - B)) with d by lia. exact RW.
Qed.

Lemma ftbl_zres1 : forall W B m d n,
  0 <= n -> rw_cells asegs m d [CB (Z.to_nat n) (BsShadow.poison_bytes (Z.to_nat n) 0)] -> ftbl W B m (zents1 (d - B) (Z.to_nat n)).
Proof.
  intros W B m d n Hn RW. unfold BsShadow.poison_bytes in RW.
  apply ftbl_zeros1. replace (B + (d - B)) with d by lia. exact RW.
Qed.

Lemma ftbl_prefix : forall W B m d (n w : nat) e rest,
  rw_cells asegs m d [CB n (word_to_le_bytes w (edenot (wenv W) e) ++ rest)] -> (w <= n)%nat ->
  ftbl W B m [(d - B, w, e)].
Proof.
  intros W B m d n w e rest RW Hw.
  destruct (rw_cells_CB_split asegs m d n w _ RW Hw) as [R1 _].
  rewrite firstn_len_app in R1 by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
  constructor; [| constructor]. cbn beta iota. replace (B + (d - B)) with d by lia. exact R1.
Qed.

Definition fabove (o : Z) (tbl : list fent) : list fent :=
  List.filter (fun f => match f with (k, _, _) => o <=? k end) tbl.

Lemma ftbl_fabove : forall W B m o tbl, ftbl W B m tbl -> ftbl W B m (fabove o tbl).
Proof.
  intros W B m o tbl H. unfold ftbl, fabove in *. apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _].
  exact (proj1 (Forall_forall _ _) H f Hf).
Qed.

Lemma fin_fabove : forall o tbl hi, fin (-8192) hi (fkeys tbl) = true -> fin o hi (fkeys (fabove o tbl)) = true.
Proof.
  intros o tbl hi H. unfold fin in *. apply forallb_forall. intros [k w] Hk.
  unfold fkeys, fabove in Hk. apply in_map_iff in Hk as ([[k' w'] e] & E & Hf). cbn in E. injection E as <- <-.
  apply filter_In in Hf as [Hf Ho]. apply Z.leb_le in Ho.
  assert (Hin : In (k', w') (fkeys tbl)) by (unfold fkeys; apply in_map_iff; exists (k', w', e); split; [reflexivity | exact Hf]).
  pose proof (proj1 (forallb_forall _ _) H (k', w') Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [K K4]. apply andb_true_iff in K as [K K3]. apply andb_true_iff in K as [K1 K2].
  rewrite K2, K3, K4. rewrite (proj2 (Z.leb_le o k') Ho). reflexivity.
Qed.

Definition fent_eqb (x y : fent) : bool :=
  match x, y with (k1, w1, e1), (k2, w2, e2) => (Z.eqb k1 k2 && Nat.eqb w1 w2 && expr_eqb e1 e2)%bool end.
Definition fent_in (x : fent) (tbl : list fent) : bool := existsb (fent_eqb x) tbl.

Lemma fent_in_In : forall x tbl, fent_in x tbl = true -> In x tbl.
Proof.
  intros [[k w] e] tbl. unfold fent_in. induction tbl as [|[[k' w'] e'] t IH]; cbn [existsb]; [discriminate|].
  intros Hb. apply orb_true_iff in Hb as [Hb|Hb]; [|right; exact (IH Hb)].
  left. unfold fent_eqb in Hb. apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply expr_eqb_eq in H3. subst. reflexivity.
Qed.

Lemma fld_tbl : forall W B m tbl k w e (j : nat) v a,
  ftbl W B m tbl -> fent_in (k, w, e) tbl = true -> (j <= w)%nat ->
  firstn j (word_to_le_bytes w (edenot (wenv W) e)) = word_to_le_bytes j (Z_to_bv 64 v) -> a = B + k ->
  CRep.fld ASEGS m a j v.
Proof.
  intros W B m tbl k w e j v a H Hin Hj Hb ->.
  pose proof (ftbl_In W B m tbl k w e H (fent_in_In _ _ Hin)) as RW.
  destruct (rw_cells_CB_split asegs m (B + k) w j _ RW Hj) as [R1 _]. rewrite Hb in R1.
  unfold CRep.fld. exact (rdn_of_rw_CB m (B + k) j (Z_to_bv 64 v) R1).
Qed.

Lemma fld_of_4bytes : forall W B m tbl k e0 e1 e2 e3 v a, ftbl W B m tbl ->
  fent_in (k, 1%nat, e0) tbl = true -> fent_in (k + 1, 1%nat, e1) tbl = true ->
  fent_in (k + 2, 1%nat, e2) tbl = true -> fent_in (k + 3, 1%nat, e3) tbl = true ->
  word_to_le_bytes 1 (edenot (wenv W) e0) ++ word_to_le_bytes 1 (edenot (wenv W) e1) ++
  word_to_le_bytes 1 (edenot (wenv W) e2) ++ word_to_le_bytes 1 (edenot (wenv W) e3) = word_to_le_bytes 4 (Z_to_bv 64 v) ->
  a = B + k -> CRep.fld ASEGS m a 4 v.
Proof.
  intros W B m tbl k e0 e1 e2 e3 v a H I0 I1 I2 I3 Hb ->.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I0)) as R0.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I1)) as R1.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I2)) as R2.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I3)) as R3.
  replace (B + (k + 1)) with (B + k + Z.of_nat 1) in R1 by lia.
  pose proof (rw_cells_CB_join asegs m (B + k) 1 1 _ _ R0 R1) as J1.
  replace (B + (k + 2)) with (B + k + Z.of_nat (1 + 1)) in R2 by lia.
  pose proof (rw_cells_CB_join asegs m (B + k) (1 + 1) 1 _ _ J1 R2) as J2.
  replace (B + (k + 3)) with (B + k + Z.of_nat (1 + 1 + 1)) in R3 by lia.
  pose proof (rw_cells_CB_join asegs m (B + k) (1 + 1 + 1) 1 _ _ J2 R3) as J3.
  rewrite <- !app_assoc in J3. rewrite Hb in J3. cbn [Nat.add] in J3.
  unfold CRep.fld. exact (rdn_of_rw_CB m (B + k) 4 (Z_to_bv 64 v) J3).
Qed.

Lemma fld_zero_range : forall W B m tbl k (n : nat), ftbl W B m tbl ->
  forallb (fun j => fent_in (k + Z.of_nat j, 1%nat, ELit 0) tbl) (seq 0 n) = true ->
  forall i, 0 <= i < Z.of_nat n -> CRep.fld ASEGS m (B + k + i) 1 0.
Proof.
  intros W B m tbl k n H Hb i Hi.
  assert (Hj : In (Z.to_nat i) (seq 0 n)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hb _ Hj) as K. cbv beta in K. rewrite Z2Nat.id in K by lia.
  eapply (fld_tbl W B m tbl (k + i) 1 (ELit 0) 1); [exact H | exact K | lia | vm_compute; reflexivity | lia].
Qed.
