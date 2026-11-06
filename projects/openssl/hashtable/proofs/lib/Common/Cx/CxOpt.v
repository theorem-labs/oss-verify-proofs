(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition phantom_vis : expr * expr := (ELit 0, ELit 8).
Definition is_phantom_vis (p : expr * expr) : bool :=
  match p with (ELit 0, ELit 8) => true | _ => false end.

Definition with_vis (cs : acs) (v : list (expr * expr)) (ab : Z) : acs :=
  ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) v (a_ghost cs) ab (a_brk cs) (a_fd cs) (a_tidset cs).

Fixpoint remove_nth {T} (i : nat) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => r
  | y :: r, S i' => y :: remove_nth i' r
  end.

(* [comment removed for export] *)
Definition node_opt_absent (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit i] => Some (with_maps cs (list_insert_nth (Z.to_nat i) absent_entry (a_maps cs)))
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_vis_dup (LIMIT : Z) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit i; ELit j] =>
      match nth_error (a_vis cs) (Z.to_nat j) with
      | Some x =>
          match xhi (kn cs) (snd x) with
          | Some nhi =>
              if Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT
              then Some (with_vis cs (list_insert_nth (Z.to_nat i) x (a_vis cs)) (a_abytes cs + vis_cost nhi))
              else None
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_vis_move (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit i; ELit j] =>
      match nth_error (a_vis cs) (Z.to_nat i) with
      | Some x => Some (with_vis cs (list_insert_nth (Z.to_nat j) x (remove_nth (Z.to_nat i) (a_vis cs))) (a_abytes cs))
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Lemma list_insert_nth_split : forall {T} (i : nat) (x : T) (l : list T),
  exists l1 l2, l = l1 ++ l2 /\ list_insert_nth i x l = l1 ++ x :: l2.
Proof.
  intros T i. induction i as [|i IH]; intros x l.
  - exists [], l. split; reflexivity.
  - destruct l as [|y r]; cbn [list_insert_nth].
    + exists [], []. split; reflexivity.
    + destruct (IH x r) as (l1 & l2 & E1 & E2). exists (y :: l1), l2. split; [rewrite E1; reflexivity | rewrite E2; reflexivity].
Qed.

Lemma existsb_insert_nth : forall {T} (f : T -> bool) (i : nat) (x : T) (l : list T),
  f x = false -> existsb f (list_insert_nth i x l) = existsb f l.
Proof.
  intros T f i x l Hx. destruct (list_insert_nth_split i x l) as (l1 & l2 & E1 & E2).
  rewrite E2, E1, !existsb_app. cbn [existsb]. rewrite Hx. reflexivity.
Qed.

Lemma In_list_insert_nth' : forall {T} (i : nat) (x y : T) (l : list T),
  In y (list_insert_nth i x l) -> y = x \/ In y l.
Proof.
  intros T i x y l H. destruct (list_insert_nth_split i x l) as (l1 & l2 & E1 & E2).
  rewrite E2 in H. rewrite E1. apply in_app_iff in H as [H|[H|H]]; [right; apply in_or_app; left; exact H | left; symmetry; exact H | right; apply in_or_app; right; exact H].
Qed.


Lemma remove_nth_split : forall {T} (i : nat) (l : list T) (x : T),
  nth_error l i = Some x -> exists l1 l2, l = l1 ++ x :: l2 /\ remove_nth i l = l1 ++ l2.
Proof.
  intros T i. induction i as [|i IH]; intros l x H; destruct l as [|y r]; cbn [nth_error] in H; try discriminate H.
  - injection H as ->. exists [], r. split; reflexivity.
  - destruct (IH r x H) as (l1 & l2 & E1 & E2). exists (y :: l1), l2. cbn [remove_nth]. split; [rewrite E1; reflexivity | rewrite E2; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_absent_lit (m : amap) : bool :=
  match m with AM (ELit 0) (ELit 8) KRW => true | _ => false end.
Definition present (ms : list amap) : list amap := List.filter (fun m => negb (is_absent_lit m)) ms.
Definition len_pos (k : list kentry) (m : amap) : bool :=
  match xlo k (am_len m) with Some lo => Z.leb 4096 lo | None => false end.
Definition base_pos (k : list kentry) (m : amap) : bool :=
  match xlo k (am_base m) with Some lo => Z.ltb 0 lo | None => false end.
(* [comment removed for export] *)
Definition ent_present (k : list kentry) (m : amap) : bool := (len_pos k m || base_pos k m)%bool.
Definition ledger_pos (k : list kentry) (ms : list amap) : bool := forallb (ent_present k) ms.
Definition ledger_opt (k : list kentry) (ms : list amap) : bool := forallb (fun m => is_absent_lit m || ent_present k m)%bool ms.

Lemma is_absent_lit_eq : forall m, is_absent_lit m = true -> m = absent_entry.
Proof.
  intros [b n kd] H. unfold is_absent_lit in H.
  destruct b as [zb| | | | | | |]; try discriminate H. destruct zb; try discriminate H.
  destruct n as [zn| | | | | | |]; try discriminate H.
  destruct zn as [|p|p]; try discriminate H. do 4 (destruct p as [p|p|]; try discriminate H).
  destruct kd; try discriminate H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma maps_match_exact_sem : forall E ms l,
  no_fog ms = true -> Forall (fun m => 4096 <= uE E (am_len m) \/ 0 < uE E (am_base m)) ms ->
  maps_match E ms l -> l = map (amap_den E) ms.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf Hp HM; cbn [maps_match] in HM; [exact HM|].
  unfold no_fog in Hnf. cbn [forallb] in Hnf. apply andb_prop in Hnf as [Hm0 Hr]. apply negb_true_iff in Hm0. rewrite Hm0 in HM.
  pose proof (Forall_inv Hp) as Hpos. cbv beta in Hpos.
  destruct HM as [(_ & L0 & B0 & _)|(l' & -> & HM')]; [exfalso; clear - L0 B0 Hpos; lia|].
  cbn [map]. f_equal. exact (IH l' Hr (Forall_inv_tail Hp) HM').
Qed.

(* [comment removed for export] *)
Lemma maps_match_Forall : forall E ms l (P : word * word -> Prop),
  no_fog ms = true -> maps_match E ms l -> (forall m, In m ms -> P (amap_den E m)) -> Forall P l.
Proof.
  intros E ms l P Hnf HM HP. apply Forall_forall. intros iv Hiv.
  destruct (maps_match_elem E ms l iv HM Hiv) as (m & Hm & [(_ & ->)|(Hf & _)]); [exact (HP m Hm)|].
  exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X. cbv beta in X. rewrite Hf in X. discriminate.
Qed.

(* [comment removed for export] *)
Definition ledger_exact (E : env) (ms : list amap) : Prop :=
  no_fog ms = true /\ Forall (fun m => 4096 <= uE E (am_len m) \/ 0 < uE E (am_base m)) ms.
Lemma ledger_exact_nf : forall E ms, ledger_exact E ms -> no_fog ms = true.
Proof. intros E ms H. exact (proj1 H). Qed.
Lemma maps_exact_D1 : forall E ms l, ledger_exact E ms -> maps_match E ms l -> l = map (amap_den E) ms.
Proof. intros E ms l [H1 H2] HM. exact (maps_match_exact_sem E ms l H1 H2 HM). Qed.

Section Exact.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.
Variable k : list kentry.
Hypothesis HK : know_ok segs E M k.

Lemma len_pos_sound : forall m, len_pos k m = true -> 4096 <= uE E (am_len m).
Proof.
  intros m H. unfold len_pos in H. destruct (xlo k (am_len m)) as [lo|] eqn:Hx; [|discriminate].
  apply Z.leb_le in H. pose proof (xlo_sound segs E M k (am_len m) lo HK Hx) as X. unfold uE. clear - H X. lia.
Qed.

Lemma base_pos_sound : forall m, base_pos k m = true -> 0 < uE E (am_base m).
Proof.
  intros m H. unfold base_pos in H. destruct (xlo k (am_base m)) as [lo|] eqn:Hx; [|discriminate].
  apply Z.ltb_lt in H. pose proof (xlo_sound segs E M k (am_base m) lo HK Hx) as X. unfold uE. clear - H X. lia.
Qed.

Lemma ent_present_sound : forall m, ent_present k m = true -> 4096 <= uE E (am_len m) \/ 0 < uE E (am_base m).
Proof.
  intros m H. unfold ent_present in H. apply orb_prop in H as [H|H]; [left; exact (len_pos_sound m H) | right; exact (base_pos_sound m H)].
Qed.

Lemma ledger_pos_sound : forall ms, ledger_pos k ms = true -> Forall (fun m => 4096 <= uE E (am_len m) \/ 0 < uE E (am_base m)) ms.
Proof.
  intros ms H. apply Forall_forall. intros m Hm. apply ent_present_sound. exact (proj1 (forallb_forall _ _) H m Hm).
Qed.

Lemma ledger_exact_intro : forall ms, no_fog ms = true -> ledger_pos k ms = true -> ledger_exact E ms.
Proof. intros ms H1 H2. split; [exact H1 | exact (ledger_pos_sound ms H2)]. Qed.

(* [comment removed for export] *)
Lemma maps_match_exact_pos : forall ms l,
  no_fog ms = true -> ledger_pos k ms = true -> maps_match E ms l -> l = map (amap_den E) ms.
Proof.
  intros ms l Hnf Hp HM. exact (maps_match_exact_sem E ms l Hnf (ledger_pos_sound ms Hp) HM).
Qed.

(* [comment removed for export] *)
Lemma maps_match_present : forall ms l,
  no_fog ms = true -> ledger_opt k ms = true ->
  Forall (fun iv : word * word => bv_unsigned (snd iv) mod 4096 = 0) l ->            (* [comment removed for export] *)
  maps_match E ms l -> l = map (amap_den E) (present ms).
Proof.
  intros ms. induction ms as [|m ms IH]; intros l Hnf Hp Hl HM; cbn [maps_match] in HM; [exact HM|].
  unfold no_fog in Hnf. cbn [forallb] in Hnf, Hp. apply andb_prop in Hnf as [Hm0 Hr]. apply andb_prop in Hp as [Hp0 Hpr].
  apply negb_true_iff in Hm0. rewrite Hm0 in HM. unfold present. cbn [List.filter]. fold (present ms).
  destruct (is_absent_lit m) eqn:Hab; cbn [negb].
  - (* [comment removed for export] *)
    destruct HM as [(_ & _ & _ & HM')|(l' & -> & HM')]; [exact (IH l Hr Hpr Hl HM')|].
    exfalso. apply is_absent_lit_eq in Hab. subst m. apply Forall_inv in Hl.
    unfold amap_den, absent_entry in Hl. cbn [snd am_len edenot] in Hl. rewrite u64_lit in Hl by lia. discriminate Hl.
  - cbn [orb] in Hp0. pose proof (ent_present_sound m Hp0) as Hpos.
    destruct HM as [(_ & L0 & B0 & _)|(l' & -> & HM')]; [exfalso; clear - L0 B0 Hpos; lia|].
    cbn [map]. f_equal. apply (IH l' Hr Hpr); [exact (Forall_inv_tail Hl) | exact HM'].
Qed.
End Exact.

(* [comment removed for export] *)
Lemma maps_match_present_rev : forall E ms l,
  no_fog ms = true -> l = map (amap_den E) (present ms) -> maps_match E ms l.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf ->; [reflexivity|].
  unfold no_fog in Hnf. cbn [forallb] in Hnf. apply andb_prop in Hnf as [Hm0 Hr]. apply negb_true_iff in Hm0.
  cbn [maps_match]. rewrite Hm0. unfold present. cbn [List.filter]. fold (present ms).
  destruct (is_absent_lit m) eqn:Hab; cbn [negb].
  - left. apply is_absent_lit_eq in Hab. subst m. unfold uE, absent_entry. cbn [am_kind am_len am_base edenot]. rewrite !u64_lit by lia.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact (IH _ Hr eq_refl).
  - right. exists (map (amap_den E) (present ms)). split; [reflexivity | exact (IH _ Hr eq_refl)].
Qed.

Lemma maps_match_exact_rev : forall E ms l,
  no_fog ms = true -> l = map (amap_den E) ms -> maps_match E ms l.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf ->; [reflexivity|].
  unfold no_fog in Hnf. cbn [forallb] in Hnf. apply andb_prop in Hnf as [Hm0 Hr]. apply negb_true_iff in Hm0.
  cbn [maps_match map]. rewrite Hm0. right. exists (map (amap_den E) ms). split; [reflexivity | exact (IH _ Hr eq_refl)].
Qed.

(* [comment removed for export] *)
Definition node_vis_phantom (A : atable) (LIMIT : Z) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [] => vis_add A LIMIT cs (ELit 0) (ELit 8) (kimg_clip A (kn cs))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint dedup_phantom (seen : bool) (v : list (expr * expr)) : list (expr * expr) :=
  match v with
  | [] => []
  | p :: r => if is_phantom_vis p then (if seen then dedup_phantom true r else p :: dedup_phantom true r)
              else p :: dedup_phantom seen r
  end.
Definition unpad (cs : acs) : acs :=
  ACS (a_ss cs) (present (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (dedup_phantom false (a_vis cs)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition node_unpad (args : list expr) (cs : acs) : option acs :=
  match args with [] => Some (unpad cs) | _ => None end.

(* [comment removed for export] *)
Definition opt_xn (A : atable) (LIMIT : Z) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 44%nat => node_opt_absent args cs
  | 45%nat => node_vis_phantom A LIMIT args cs
  | 46%nat => node_unpad args cs
  | 47%nat => node_vis_dup LIMIT args cs
  | 48%nat => node_vis_move args cs
  | _ => None
  end.

Lemma is_phantom_vis_eq : forall p, is_phantom_vis p = true -> p = phantom_vis.
Proof.
  intros [b n] H. unfold is_phantom_vis in H.
  destruct b as [zb| | | | | | |]; try discriminate H. destruct zb; try discriminate H.
  destruct n as [zn| | | | | | |]; try discriminate H.
  destruct zn as [|p|p]; try discriminate H. do 4 (destruct p as [p|p|]; try discriminate H). reflexivity.
Qed.

Lemma maps_match_unpad : forall E ms l,
  Forall (fun iv : word * word => bv_unsigned (snd iv) mod 4096 = 0) l -> maps_match E ms l -> maps_match E (present ms) l.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hl HM; [exact HM|].
  unfold present. cbn [List.filter]. fold (present ms). cbn [maps_match] in HM.
  destruct (is_absent_lit m) eqn:Hab; cbn [negb].
  - apply is_absent_lit_eq in Hab. subst m. change (is_fog absent_entry) with false in HM. cbv iota in HM.
    destruct HM as [(_ & _ & _ & HM)|(l' & -> & HM)]; [exact (IH l Hl HM)|].
    exfalso. apply Forall_inv in Hl. unfold amap_den, absent_entry in Hl. cbn [snd am_len edenot] in Hl. rewrite u64_lit in Hl by lia. discriminate Hl.
  - cbn [maps_match]. destruct (is_fog m).
    + destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; exact (IH l Hl HM) | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hs | exact (IH l' (Forall_inv_tail Hl) HM)].
    + destruct HM as [(K0 & L0 & B0 & HM)|(l' & -> & HM)]; [left; split; [exact K0|]; split; [exact L0|]; split; [exact B0 | exact (IH l Hl HM)] | right].
      exists l'. split; [reflexivity | exact (IH l' (Forall_inv_tail Hl) HM)].
Qed.

(* [comment removed for export] *)
Lemma existsb_mid : forall {T} (f : T -> bool) l1 x l2, existsb f (l1 ++ x :: l2) = (f x || existsb f (l1 ++ l2))%bool.
Proof. intros. rewrite !existsb_app. cbn [existsb]. destruct (existsb f l1), (f x); reflexivity. Qed.

Lemma existsb_dedup : forall (f : expr * expr -> bool) v seen,
  (existsb f (dedup_phantom seen v) || (seen && f phantom_vis))%bool = (existsb f v || (seen && f phantom_vis))%bool.
Proof.
  intros f v. induction v as [|p r IH]; intros seen; [reflexivity|]. cbn [dedup_phantom existsb].
  destruct (is_phantom_vis p) eqn:Hp.
  - apply is_phantom_vis_eq in Hp. subst p. destruct seen.
    + specialize (IH true). cbn [andb] in IH |- *. destruct (f phantom_vis); [rewrite !orb_true_r; reflexivity|]. rewrite !orb_false_r in IH |- *. cbn [orb]. exact IH.
    + specialize (IH true). cbn [existsb andb] in IH |- *. destruct (f phantom_vis); [reflexivity|]. rewrite !orb_false_r in IH |- *. cbn [orb]. exact IH.
  - cbn [existsb]. rewrite <- !orb_assoc, (IH seen). reflexivity.
Qed.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Local Notation CSOK := (cs_ok SEGS A LIMIT SINV argH ISP FS0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cs_ok_insert_absent : forall E cs R FULL model i,
  CSOK E cs R FULL model -> CSOK E (with_maps cs (list_insert_nth i absent_entry (a_maps cs))) R FULL model.
Proof.
  intros E cs R FULL model i HC.
  set (ms' := list_insert_nth i absent_entry (a_maps cs)).
  assert (Hsub : forall m, In m ms' -> m = absent_entry \/ In m (a_maps cs)) by (intros m Hm; exact (In_list_insert_nth' _ _ _ _ Hm)).
  assert (HM : maps_match E ms' (vm_maps (m_vmmaps model))) by (apply list_insert_nth_absent; exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  assert (HMr : Mr A argH E (with_maps cs ms') model FULL = Mr A argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (with_maps cs ms') = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *)
    apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_holes0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. destruct Hk; discriminate.
    + exact (proj1 (Forall_forall _ _) co_none0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_kinds0 m Hm Hk).
Qed.

Theorem node_opt_absent_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_opt_absent args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_opt_absent in Hn.
  destruct args as [|[i| | | | | | |] [|]]; try discriminate Hn.
  injection Hn as <-.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  apply cs_ok_insert_absent. exact HC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis SHADOW_ok : shadow_ok A.

Local Notation HS0 := (fun _ : nat => @None acs).
Local Notation XN0 := (fun (_ : nat) (_ : list expr) (_ : acs) => @None acs).
Local Notation XE0 := (fun (_ : nat) (_ : list expr) (_ : acs) => @None (Z * list spiece * acs)).
Local Notation XB0 := (fun (_ : nat) (_ : list expr) (_ : acs) => @None (acs * acs)).

Lemma page_allowedb_flat : forall E (l : list (expr * expr)) (p : word),
  page_allowedb (flat_map (allow1 A E) l) p = existsb (fun x => page_allowedb (allow1 A E x) p) l.
Proof.
  intros E l p. induction l as [|x r IH]; [reflexivity|]. cbn [flat_map existsb].
  unfold page_allowedb in *. rewrite existsb_app, IH. reflexivity.
Qed.

Lemma allow1_nonneg : forall E x, 0 <= A_bytes (allow1 A E x).
Proof.
  intros E x. unfold allow1, sh_lo, sh_hi. cbn [A_bytes fst snd].
  pose proof (bv_unsigned_in_range _ (edenot E (fst x))) as R1. pose proof (bv_unsigned_in_range _ (edenot E (snd x))) as R2. unfold uE.
  set (a := bv_unsigned (edenot E (fst x))) in *. set (n := bv_unsigned (edenot E (snd x))) in *.
  pose proof (pagedown_le a) as P1. pose proof (pageup_ge (a + n)) as P2.
  pose proof (pagedown_le (shadow_off A + a / 8)) as P3. pose proof (pageup_ge (shadow_off A + (a + n) / 8)) as P4.
  assert (D : a / 8 <= (a + n) / 8) by (apply Z.div_le_mono; lia).
  clear - R1 R2 P1 P2 P3 P4 D. lia.
Qed.

Lemma A_bytes_flat_mid : forall E l1 x l2 gh,
  A_bytes (flat_map (allow1 A E) ((l1 ++ x :: l2) ++ gh)) = A_bytes (allow1 A E x) + A_bytes (flat_map (allow1 A E) ((l1 ++ l2) ++ gh)).
Proof.
  intros E l1 x l2 gh. rewrite <- !app_assoc, !flat_map_app. cbn [app flat_map]. rewrite !A_bytes_app. lia.
Qed.

Lemma A_bytes_dedup : forall E gh v seen,
  A_bytes (flat_map (allow1 A E) (dedup_phantom seen v ++ gh)) <= A_bytes (flat_map (allow1 A E) (v ++ gh)).
Proof.
  intros E gh v. induction v as [|p r IH]; intros seen; [cbn [dedup_phantom]; lia|]. cbn [dedup_phantom].
  destruct (is_phantom_vis p); [destruct seen|].
  - cbn [app flat_map]. rewrite A_bytes_app. pose proof (allow1_nonneg E p). pose proof (IH true). lia.
  - cbn [app flat_map]. rewrite !A_bytes_app. pose proof (IH true). lia.
  - cbn [app flat_map]. rewrite !A_bytes_app. pose proof (IH seen). lia.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_vis_change : forall E cs R FULL model v' ab',
  CSOK E cs R FULL model ->
  (forall z, in_vis E (with_vis cs v' ab') z = in_vis E cs z) ->
  (forall z, in_sh A E (with_vis cs v' ab') z = in_sh A E cs z) ->
  A_bytes (allowA A E (with_vis cs v' ab')) <= ab' ->
  eager_used model + A_bytes (allowA A E (with_vis cs v' ab')) <= vm_limit (m_vmmaps model) ->
  (forall p : word, page_allowedb (allowA A E cs) p = true -> page_allowedb (allowA A E (with_vis cs v' ab')) p = true) ->
  CSOK E (with_vis cs v' ab') R FULL model.
Proof.
  intros E cs R FULL model v' ab' HC Hv Hs Hab Hbud Hpg.
  set (cs' := with_vis cs v' ab') in *.
  assert (HH : hid A argH E cs' model = hid A argH E cs model).
  { apply functional_extensionality. intros a. unfold hid, vis, in_allow. rewrite Hv, Hs. reflexivity. }
  assert (HMr : Mr A argH E cs' model FULL = Mr A argH E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
  destruct HC; constructor; try assumption.
  - (* [comment removed for export] *) rewrite HMr. exact co_know0.
  - (* [comment removed for export] *) destruct co_minv0 as [N1 N2 N3 N4 N5]. constructor; try assumption. intros p Hp. exact (Hpg p (N3 p Hp)).
  - (* [comment removed for export] *) intros a H1 H2 H3 H4 H5. rewrite HH in H1. exact (co_zero0 a H1 H2 H3 H4 H5).
Qed.

Lemma in_orb_absorb : forall {T} (f : T -> bool) x l, In x l -> (f x || existsb f l)%bool = existsb f l.
Proof.
  intros T f x l Hin. destruct (f x) eqn:Hx; [|reflexivity]. cbn [orb]. symmetry. apply existsb_exists. exists x. split; assumption.
Qed.

(* [comment removed for export] *)
Theorem node_vis_dup_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_vis_dup LIMIT args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_vis_dup in Hn.
  destruct args as [|[i| | | | | | |] [|[j| | | | | | |] [|]]]; try discriminate Hn.
  destruct (nth_error (a_vis cs) (Z.to_nat j)) as [x|] eqn:Hx; [|discriminate].
  destruct (xhi (kn cs) (snd x)) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end.
  injection Hn as <-. apply Z.leb_le in Hb.
  assert (Hrefl : forall y, env_agree y E E) by (intros y; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  pose proof (nth_error_In _ _ Hx) as Hin.
  destruct (list_insert_nth_split (Z.to_nat i) x (a_vis cs)) as (l1 & l2 & E1 & E2).
  pose proof (xhi_sound SEGS E _ (kn cs) (snd x) nhi (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hnhi) as Hn'.
  pose proof (allow1_cost A HS0 XN0 XE0 XB0 SHADOW_ok 0%nat E (fst x) (snd x) nhi Hn') as Hcost. rewrite <- surjective_pairing in Hcost.
  assert (HAB : A_bytes (allowA A E (with_vis cs (list_insert_nth (Z.to_nat i) x (a_vis cs)) (a_abytes cs + vis_cost nhi)))
                = A_bytes (allow1 A E x) + A_bytes (allowA A E cs)).
  { unfold allowA, with_vis. cbn [a_vis a_ghost]. rewrite E2, A_bytes_flat_mid, <- E1. reflexivity. }
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC) as HE. pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as HAB0.
  apply cs_ok_vis_change; [exact HC | | | | |].
  - intros z. unfold in_vis, with_vis. cbn [a_vis]. match goal with |- existsb ?f _ = _ => set (F := f) end. rewrite E2, existsb_mid, <- E1. exact (in_orb_absorb F x _ Hin).
  - intros z. unfold in_sh, with_vis. cbn [a_vis]. match goal with |- existsb ?f _ = _ => set (F := f) end. rewrite E2, existsb_mid, <- E1. exact (in_orb_absorb F x _ Hin).
  - rewrite HAB. lia.
  - rewrite HAB. lia.
  - intros p Hp. unfold allowA, with_vis in *. cbn [a_vis a_ghost] in *. rewrite page_allowedb_flat in *. rewrite E2.
    rewrite <- app_assoc. cbn [app]. rewrite existsb_mid. rewrite app_assoc, <- E1, Hp. apply orb_true_r.
Qed.

(* [comment removed for export] *)
Theorem node_vis_move_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_vis_move args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_vis_move in Hn.
  destruct args as [|[i| | | | | | |] [|[j| | | | | | |] [|]]]; try discriminate Hn.
  destruct (nth_error (a_vis cs) (Z.to_nat i)) as [x|] eqn:Hx; [|discriminate].
  injection Hn as <-.
  assert (Hrefl : forall y, env_agree y E E) by (intros y; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  destruct (remove_nth_split (Z.to_nat i) (a_vis cs) x Hx) as (l1 & l2 & E1 & E2).
  destruct (list_insert_nth_split (Z.to_nat j) x (remove_nth (Z.to_nat i) (a_vis cs))) as (m1 & m2 & F1 & F2).
  rewrite E2 in F1.
  assert (HAB : A_bytes (allowA A E (with_vis cs (list_insert_nth (Z.to_nat j) x (remove_nth (Z.to_nat i) (a_vis cs))) (a_abytes cs)))
                = A_bytes (allowA A E cs)).
  { unfold allowA, with_vis. cbn [a_vis a_ghost]. rewrite F2, A_bytes_flat_mid, <- F1. rewrite E1, A_bytes_flat_mid. reflexivity. }
  pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as HAB0.
  pose proof (minv_budget _ _ (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as HB0.
  apply cs_ok_vis_change; [exact HC | | | | |].
  - intros z. unfold in_vis, with_vis. cbn [a_vis]. rewrite F2, existsb_mid, <- F1. rewrite E1, existsb_mid. reflexivity.
  - intros z. unfold in_sh, with_vis. cbn [a_vis]. rewrite F2, existsb_mid, <- F1. rewrite E1, existsb_mid. reflexivity.
  - rewrite HAB. exact HAB0.
  - rewrite HAB. exact HB0.
  - intros p Hp. unfold allowA, with_vis in *. cbn [a_vis a_ghost] in *. rewrite page_allowedb_flat in *. rewrite F2.
    rewrite <- app_assoc. cbn [app]. rewrite existsb_mid. rewrite app_assoc, <- F1.
    rewrite E1, <- app_assoc in Hp. cbn [app] in Hp. rewrite existsb_mid, app_assoc in Hp. exact Hp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis ZONE_ok : zone_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.

Lemma vis_add_shape0 : forall cs b n k cs2, vis_add A LIMIT cs b n k = Some cs2 ->
  pc cs2 = pc cs /\ a_vis cs2 = (b, n) :: a_vis cs /\ a_ghost cs2 = a_ghost cs.
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn].
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. repeat split; reflexivity.
Qed.

Theorem node_vis_phantom_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_vis_phantom A LIMIT args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_vis_phantom in Hn.
  destruct args as [|? ?]; [|discriminate Hn].
  destruct (vis_add_shape0 _ _ _ _ _ Hn) as (Hpc & Hvis & Hgh).
  assert (Hrefl : forall y, env_agree y E E) by (intros y; split; [intros; reflexivity | reflexivity]).
  rewrite <- Hpc. apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  apply (vis_add_sound SEGS A LIMIT HS0 XN0 XE0 XB0 HULL_ok SHADOW_ok ZONE_ok SINV argH ISP argH_high FS0 0%nat
           E cs (ELit 0) (ELit 8) (kimg_clip A (kn cs)) cs' R FULL model Hn HC).
  (* [comment removed for export] *)
  unfold Mr. apply (know_ok_unhide SEGS A E (hid A argH E cs model) (hid A argH E cs' model) FULL (kimg_clip A (kn cs))).
  - apply (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH ISP argH_high).
  - apply kimg_clip_in_hull.
  - intros a Ha. unfold hid in Ha |- *. apply orb_true_iff in Ha. apply orb_true_iff.
    destruct Ha as [Ha|Ha]; [left; exact Ha|]. right. apply negb_true_iff in Ha. apply negb_true_iff.
    destruct (vis A E cs model a) eqn:Hv; [|reflexivity]. exfalso.
    rewrite (vis_mono A E cs cs' model a) in Ha; [discriminate | | exact Hv].
    intros z Hz. unfold in_allow, in_vis, in_sh in Hz |- *. rewrite Hvis. cbn [existsb].
    apply orb_true_iff in Hz. apply orb_true_iff. destruct Hz as [Hz|Hz]; [left|right]; apply orb_true_iff; right; exact Hz.
  - intros a Ha. apply (hid_hull A HULL_ok argH ISP argH_high). exact Ha.
  - unfold kimg_clip. apply know_ok_filter. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cs_ok_present : forall E cs R FULL model,
  CSOK E cs R FULL model -> CSOK E (with_maps cs (present (a_maps cs))) R FULL model.
Proof.
  intros E cs R FULL model HC.
  assert (HBND : Forall (fun iv : word * word => bv_unsigned (snd iv) mod 4096 = 0) (vm_maps (m_vmmaps model))).
  { eapply Forall_impl; [|exact (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC)]. intros iv (_ & _ & H & _). exact H. }
  assert (SUB : forall m, In m (present (a_maps cs)) -> In m (a_maps cs)) by (intros m Hm; unfold present in Hm; apply filter_In in Hm as [Hm _]; exact Hm).
  assert (HMr : Mr A argH E (with_maps cs (present (a_maps cs))) model FULL = Mr A argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (with_maps cs (present (a_maps cs))) = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply maps_match_unpad; [exact HBND | exact co_maps0].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm. exact (proj1 (Forall_forall _ _) co_holes0 m (SUB m Hm)).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm. exact (proj1 (Forall_forall _ _) co_none0 m (SUB m Hm)).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm. exact (proj1 (Forall_forall _ _) co_kinds0 m (SUB m Hm)).
Qed.

Theorem cs_ok_unpad : forall E cs R FULL model,
  CSOK E cs R FULL model -> CSOK E (unpad cs) R FULL model.
Proof.
  intros E cs R FULL model HC.
  change (unpad cs) with (with_vis (with_maps cs (present (a_maps cs))) (dedup_phantom false (a_vis cs)) (a_abytes cs)).
  pose proof (cs_ok_present E cs R FULL model HC) as HC1.
  pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as HAB0.
  pose proof (minv_budget _ _ (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as HB0.
  assert (HAB : A_bytes (allowA A E (with_vis (with_maps cs (present (a_maps cs))) (dedup_phantom false (a_vis cs)) (a_abytes cs))) <= A_bytes (allowA A E cs)).
  { unfold allowA, with_vis, with_maps. cbn [a_vis a_ghost]. apply A_bytes_dedup. }
  apply cs_ok_vis_change; [exact HC1 | | | | |].
  - intros z. unfold in_vis, with_vis, with_maps. cbn [a_vis]. match goal with |- existsb ?f _ = _ => pose proof (existsb_dedup f (a_vis cs) false) as X end.
    cbn [andb] in X. rewrite !orb_false_r in X. exact X.
  - intros z. unfold in_sh, with_vis, with_maps. cbn [a_vis]. match goal with |- existsb ?f _ = _ => pose proof (existsb_dedup f (a_vis cs) false) as X end.
    cbn [andb] in X. rewrite !orb_false_r in X. exact X.
  - cbn [a_abytes with_vis]. lia.
  - lia.
  - intros p Hp. unfold allowA, with_vis, with_maps in *. cbn [a_vis a_ghost] in *. rewrite page_allowedb_flat in *.
    rewrite existsb_app in *. match goal with |- (existsb ?f _ || _)%bool = true => pose proof (existsb_dedup f (a_vis cs) false) as X end.
    cbn [andb] in X. rewrite !orb_false_r in X. rewrite X. exact Hp.
Qed.

Theorem node_unpad_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_unpad args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_unpad in Hn.
  destruct args as [|? ?]; [|discriminate Hn]. injection Hn as <-.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  apply cs_ok_unpad. exact HC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem opt_xn_sound : ext_stmt SEGS A nx0 LIMIT (opt_xn A LIMIT) SINV argH ISP FS0.
Proof.
  intros id args. unfold opt_xn.
  do 44 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ Hn; discriminate Hn|]).
  destruct id as [|id]; [exact (node_opt_absent_sound args)|].
  destruct id as [|id]; [exact (node_vis_phantom_sound args)|].
  destruct id as [|id]; [exact (node_unpad_sound args)|].
  destruct id as [|id]; [exact (node_vis_dup_sound args)|].
  destruct id as [|id]; [exact (node_vis_move_sound args)|].
  intros cs cs' E R FULL model T _ _ Hn; discriminate Hn.
Qed.
End Sound.
