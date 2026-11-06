(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec TargetSpec SymExec3 SymExec3Sound SymPlan SymPlanSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint nocase (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmit _ _ s' => nocase s'
  | SAlt2 a b => nocase a && nocase b
  | SCase _ _ _ _ => false
  end.

Lemma t_eq_emit : forall evs T T', t_eq T T' -> t_eq (t_emit evs T) (t_emit evs T').
Proof.
  intros evs T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.

Lemma t_eq_alt2 : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
  intros A A' B B' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctest : Type := (expr * Z * bool)%type.

Fixpoint stest (tests : list ctest) (e : expr) (mid : Z) : option bool :=
  match tests with
  | [] => None
  | (e', mid', b) :: rest => if (expr_eqb e e' && Z.eqb mid mid')%bool then Some b else stest rest e mid
  end.

Fixpoint sresolve (tests : list ctest) (s : shape) : option shape :=
  match s with
  | SNil => Some SNil
  | SExit c => Some (SExit c)
  | SEmit fd bs s' => match sresolve tests s' with Some s'' => Some (SEmit fd bs s'') | None => None end
  | SAlt2 a b =>
      match sresolve tests a, sresolve tests b with
      | Some a', Some b' => Some (SAlt2 a' b')
      | _, _ => None
      end
  | SCase e mid s1 s2 =>
      match stest tests e mid with
      | Some true => sresolve tests s1
      | Some false => sresolve tests s2
      | None => None
      end
  end.

Definition ctest_ok (E : env) (t : ctest) : Prop :=
  let '(e, mid, b) := t in Z.leb (bv_unsigned (edenot E e)) mid = b.

Lemma stest_sound : forall E tests e mid b,
  Forall (ctest_ok E) tests -> stest tests e mid = Some b ->
  Z.leb (bv_unsigned (edenot E e)) mid = b.
Proof.
  intros E tests e mid b HT. induction HT as [|[[e' mid'] b'] rest Ht HT IH]; cbn [stest]; intros H; [discriminate|].
  destruct (expr_eqb e e' && (mid =? mid'))%bool eqn:Eq.
  - apply andb_prop in Eq as [E1 E2]. apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. subst e' mid'.
    injection H as <-. exact Ht.
  - apply IH. exact H.
Qed.

Theorem sresolve_sound : forall E fs tests s s',
  Forall (ctest_ok E) tests -> sresolve tests s = Some s' ->
  t_eq (sd E fs s) (sd E fs s').
Proof.
  intros E fs tests s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros s' HT H; cbn [sresolve] in H.
  - injection H as <-. apply t_eq_refl.
  - injection H as <-. apply t_eq_refl.
  - destruct (sresolve tests s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [sd].
    apply t_eq_emit. apply IH; [exact HT | reflexivity].
  - destruct (sresolve tests a) as [a'|] eqn:Ha; [|discriminate].
    destruct (sresolve tests b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [sd].
    apply t_eq_alt2; [apply IHa | apply IHb]; first [exact HT | reflexivity].
  - destruct (stest tests e mid) as [tb|] eqn:Ht; [|discriminate].
    pose proof (stest_sound E tests e mid tb HT Ht) as Hv. cbn [sd]. rewrite Hv.
    destruct tb; [apply IH1 | apply IH2]; assumption.
Qed.

Lemma sresolve_nocase : forall tests s s', sresolve tests s = Some s' -> nocase s' = true.
Proof.
  intros tests s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros s' H; cbn [sresolve] in H.
  - injection H as <-. reflexivity.
  - injection H as <-. reflexivity.
  - destruct (sresolve tests s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [nocase]. apply IH. reflexivity.
  - destruct (sresolve tests a) as [a'|] eqn:Ha; [|discriminate].
    destruct (sresolve tests b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [nocase].
    rewrite (IHa a' eq_refl), (IHb b' eq_refl). reflexivity.
  - destruct (stest tests e mid) as [[|]|]; [apply IH1 | apply IH2 | discriminate]; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sev : Type := SW (fd b : Z) | SX (code : Z).

Definition sev_eqb (x y : sev) : bool :=
  match x, y with
  | SW f a, SW g b => Z.eqb f g && Z.eqb a b
  | SX c, SX d => Z.eqb c d
  | _, _ => false
  end.

Lemma sev_eqb_eq : forall x y, sev_eqb x y = true -> x = y.
Proof.
  intros [f a|c] [g b|d] H; cbn in H; try discriminate.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint paths (s : shape) : list (list sev) :=
  match s with
  | SNil => [[]]
  | SExit c => [[SX c]]
  | SEmit fd bs s' => map (fun p => map (SW fd) bs ++ p) (paths s')
  | SAlt2 a b => paths a ++ paths b
  | SCase _ _ a b => paths a ++ paths b
  end.

Fixpoint prefixb (p q : list sev) : bool :=
  match p, q with
  | [], _ => true
  | _ :: _, [] => false
  | x :: p', y :: q' => sev_eqb x y && prefixb p' q'
  end.

Definition sub_paths (P Q : list (list sev)) : bool :=
  forallb (fun p => existsb (fun q => prefixb p q) Q) P.

Definition shape_equiv (s1 s2 : shape) : bool :=
  sub_paths (paths s1) (paths s2) && sub_paths (paths s2) (paths s1).

Definition sev_ev (fs : Fs.Fs) (v : sev) : event :=
  match v with
  | SW fd b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)
  | SX c => ExitEv (Z_to_bv 64 c) fs
  end.
Definition events (fs : Fs.Fs) (p : list sev) : list event := map (sev_ev fs) p.

Lemma paths_ne : forall s, paths s <> [].
Proof.
  induction s; cbn [paths]; try discriminate.
  - destruct (paths s); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
Qed.

Lemma Wz_events : forall fs fd bs, Wz fd bs = events fs (map (SW fd) bs).
Proof. intros fs fd bs. unfold Wz, events. rewrite map_map. reflexivity. Qed.

Lemma is_prefix_app_l {A} : forall (l a b : list A), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]]. Qed.

(* [comment removed for export] *)
Theorem sd_paths : forall E fs s, nocase s = true ->
  forall tr, sd E fs s tr <-> exists p, In p (paths s) /\ is_prefix tr (events fs p).
Proof.
  intros E fs s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros Hnc tr; cbn [nocase] in Hnc; try discriminate; cbn [sd paths].
  - unfold t_nil. split.
    + intros ->. exists []. split; [left; reflexivity | exact I].
    + intros (p & [<-|[]] & Hp). apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_exit, t_emit, t_nil. split.
    + intros [Hp | (tr' & -> & ->)]; exists [SX c]; (split; [left; reflexivity|]); [exact Hp | cbn; auto].
    + intros (p & [<-|[]] & Hp). left. exact Hp.
  - specialize (IH Hnc). unfold t_emit. rewrite (Wz_events fs). split.
    + intros [Hp | (tr' & -> & HT)].
      * destruct (paths s) as [|p0 P] eqn:EP; [exfalso; exact (paths_ne s EP)|].
        exists (map (SW fd) bs ++ p0). split; [apply in_map; left; reflexivity|].
        unfold events in *. rewrite map_app. apply is_prefix_app_r. exact Hp.
      * apply IH in HT as (p & Hin & Hp). exists (map (SW fd) bs ++ p). split; [apply in_map; exact Hin|].
        unfold events in *. rewrite map_app. apply is_prefix_app_l. exact Hp.
    + intros (q & Hin & Hq). apply in_map_iff in Hin as (p & <- & Hin).
      unfold events in Hq. rewrite map_app in Hq. apply is_prefix_app_split in Hq as [Hq | (b' & -> & Hq)].
      * left. exact Hq.
      * right. exists b'. split; [reflexivity|]. apply IH. exists p. split; [exact Hin | exact Hq].
  - apply andb_prop in Hnc as [Ha Hb]. specialize (IHa Ha). specialize (IHb Hb). unfold t_alt2. split.
    + intros [H|H]; [apply IHa in H | apply IHb in H]; destruct H as (p & Hin & Hp); exists p; split;
        [apply in_app_iff; left; exact Hin | exact Hp | apply in_app_iff; right; exact Hin | exact Hp].
    + intros (p & Hin & Hp). apply in_app_iff in Hin as [Hin|Hin]; [left; apply IHa | right; apply IHb]; exists p; split; assumption.
Qed.

Lemma prefixb_sound : forall fs p q, prefixb p q = true -> is_prefix (events fs p) (events fs q).
Proof.
  intros fs p. induction p as [|x p IH]; intros q H; cbn [prefixb] in H.
  - apply is_prefix_nil.
  - destruct q as [|y q]; [discriminate|]. apply andb_prop in H as [H1 H2]. apply sev_eqb_eq in H1. subst y.
    cbn. split; [reflexivity | apply IH; exact H2].
Qed.

Lemma sub_paths_sound : forall E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  sub_paths (paths s1) (paths s2) = true -> forall tr, sd E fs s1 tr -> sd E fs s2 tr.
Proof.
  intros E fs s1 s2 H1 H2 HS tr Htr.
  apply (sd_paths E fs s1 H1) in Htr as (p & Hin & Hp).
  unfold sub_paths in HS. rewrite forallb_forall in HS. specialize (HS p Hin).
  apply existsb_exists in HS as (q & Hq & Hpq).
  apply (sd_paths E fs s2 H2). exists q. split; [exact Hq|].
  eapply is_prefix_trans; [exact Hp | apply prefixb_sound; exact Hpq].
Qed.

Theorem shape_equiv_sound : forall E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  shape_equiv s1 s2 = true -> t_eq (sd E fs s1) (sd E fs s2).
Proof.
  intros E fs s1 s2 H1 H2 HE tr. unfold shape_equiv in HE. apply andb_prop in HE as [HA HB].
  split; apply sub_paths_sound; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition starget (calls : nat) (npos cm : bool) : shape :=
  let succ := SEmit 1 (concat (repeat [48; 10] calls)) (SExit 0) in
  if npos then SAlt2 (SExit (if cm then 0 else 2)) succ else succ.

Lemma starget_nocase : forall calls npos cm, nocase (starget calls npos cm) = true.
Proof. intros calls [|] cm; reflexivity. Qed.

Lemma Wz_zero_lines : forall calls, Wz 1 (concat (repeat [48; 10] calls)) = W 1 (zero_lines calls).
Proof.
  induction calls as [|c IH]; [reflexivity|]. cbn [repeat concat zero_lines app]. unfold Wz, W in *. cbn [map]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition calls_of (content : list byte) : nat :=
  if (hdr_cfglen content =? 0)%Z then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4)).
Definition npos_of (content : list byte) : bool := (0 <? hdr_paylen content)%Z.
Definition cm_of (content : list byte) : bool := (128 <=? hdr_b1 content)%Z.

Lemma counting_cm : forall content, (32768 <=? hdr_cfg content)%Z = cm_of content.
Proof.
  intros content. unfold cm_of, hdr_cfg, hdr_b0, hdr_b1.
  pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
  change (bv_modulus 8) with 256%Z in B0, B1.
  destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0))));
    [apply Z.leb_le | apply Z.leb_gt]; lia.
Qed.

Theorem starget_sound : forall E fs content,
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  t_eq (sd E fs (starget (calls_of content) (npos_of content) (cm_of content))) (t_target content fs).
Proof.
  intros E fs content Hlen.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  unfold t_target. rewrite counting_cm. fold (hdr_cfglen content).
  assert (EC : match Z.to_nat (hdr_cfglen content) with
               | 0%nat => 1%nat
               | S _ => S (Z.to_nat (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4))
               end = calls_of content).
  { unfold calls_of. destruct (Z.eqb_spec (hdr_cfglen content) 0) as [E0|E0].
    - rewrite E0. reflexivity.
    - destruct (Z.to_nat (hdr_cfglen content)) eqn:En; [lia | reflexivity]. }
  rewrite !EC.
  unfold starget, npos_of, hdr_paylen.
  destruct (length content - 6 - Z.to_nat (hdr_cfglen content))%nat eqn:EP.
  - replace (0 <? Z.of_nat (length content) - 6 - hdr_cfglen content)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [sd]. rewrite Wz_zero_lines. apply t_eq_refl.
  - replace (0 <? Z.of_nat (length content) - 6 - hdr_cfglen content)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [sd]. apply t_eq_alt2; [|rewrite Wz_zero_lines; apply t_eq_refl].
    unfold exit_code. destruct (cm_of content); apply t_eq_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

Lemma XC_denot : forall E content,
  eb E 0 = content -> (2 < length content)%nat ->
  bv_unsigned (edenot E XC) = (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4)%Z.
Proof.
  intros E content Hb Hlen. unfold XC. cbn [edenot]. rewrite Hb.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  assert (BV : blob_val false content 2 1 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))).
  { unfold blob_val, blob_bytes. f_equal.
    destruct content as [|c0 [|c1 [|c2 rest]]]; cbn [length] in Hlen; try lia.
    change (Z.to_nat 2) with 2%nat. cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l. apply Z.lor_0_r. }
  rewrite BV. rewrite alu_and. unfold v_and. rewrite (u_small (bv_unsigned (nth 2 content (Z_to_bv 8 0)))) by lia.
  change (bv_unsigned (Z_to_bv 64 3)) with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)). rewrite u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition tests_of (cfg0 : bool) (c : Z) (cm : bool) : list ctest :=
  [(EVar 5, 0, cfg0); (XC, 0, (c - 1 <=? 0)%Z); (XC, 1, (c - 1 <=? 1)%Z); (XC, 2, (c - 1 <=? 2)%Z);
   (EVar 7, 127, negb cm)].

Definition variant_ok (npos : bool) (s : shape) (cfg0 : bool) (c : Z) (cm : bool) : bool :=
  match sresolve (tests_of cfg0 c cm) s with
  | Some s' => shape_equiv s' (starget (if cfg0 then 1%nat else Z.to_nat c) npos cm)
  | None => false
  end.

(* [comment removed for export] *)
Definition class_shape_ok (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun cfg0 => forallb (fun c => variant_ok npos s cfg0 c cm) [1; 2; 3; 4]%Z)
                             [true; false]) [true; false].

(* [comment removed for export] *)
Theorem class_shape_sound : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  class_shape_ok (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB Hlen HC.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (cfg0 := (hdr_cfglen content =? 0)%Z). set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  (* [comment removed for export] *)
  assert (V : variant_ok (npos_of content) s cfg0 c cm = true).
  { unfold class_shape_ok in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    specialize (HC cfg0 ltac:(destruct cfg0; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of cfg0 c cm) s) as [s'|] eqn:Hs; [|discriminate].
  (* [comment removed for export] *)
  assert (TT : Forall (ctest_ok E) (tests_of cfg0 c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite u_small by lia. unfold cfg0. destruct (Z.eqb_spec (hdr_cfglen content) 0); [apply Z.leb_le | apply Z.leb_gt]; lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace (if cfg0 then 1%nat else Z.to_nat c) with (calls_of content).
  - apply starget_sound. exact Hlen.
  - unfold calls_of, cfg0, c. destruct (hdr_cfglen content =? 0)%Z; [reflexivity|].
    rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
