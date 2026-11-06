(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanNodesWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import XWD.
Open Scope Z_scope.

Section FPW. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ss_eqb_eq : forall x y, ss_eqb x y = true -> x = y.
Proof.
  intros [p1 r1 l1 k1 n1 v1] [p2 r2 l2 k2 n2 v2] H. unfold ss_eqb in H. cbn [s_pc s_regs s_log s_know s_next s_resv] in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  destruct l1; [|destruct l2; discriminate]. destruct l2; [|discriminate].
  destruct v1; [discriminate|]. destruct v2; [discriminate|].
  repeat match goal with
         | X : list_eqb kentry_eqb _ _ = true |- _ => apply (list_eqb_eq kentry_eqb kentry_eqb_eq) in X
         | X : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in X
         | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X
         | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X
         end. subst. reflexivity.
Qed.

Lemma acs_eqb_eq : forall x y, acs_eqb x y = true -> x = y.
Proof.
  intros [s1 m1 t1 y1 e1 v1 g1 ab1 b1 f1 d1] [s2 m2 t2 y2 e2 v2 g2 ab2 b2 f2 d2] H. unfold acs_eqb in H.
  cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply ss_eqb_eq in H.
  repeat match goal with
         | X : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in X
         | X : list_eqb pair_eqb _ _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in X
         | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X
         | X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X
         | X : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in X
         | X : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in X
         end. subst. reflexivity.
Qed.

Lemma srepl_log : forall c t cs, s_log (a_ss (srepl c t cs)) = [].
Proof. reflexivity. Qed.
Lemma srepls_log : forall J e ts cs, s_log (a_ss cs) = [] -> s_log (a_ss (srepls J e ts cs)) = [].
Proof. intros J e ts. induction ts as [|t r IH]; intros cs H; [exact H|]. cbn [srepls]. apply IH. reflexivity. Qed.
Lemma srepls_pc : forall J e ts cs, pc (srepls J e ts cs) = pc cs.
Proof. intros J e ts. induction ts as [|t r IH]; intros cs; [reflexivity|]. cbn [srepls]. rewrite IH. reflexivity. Qed.
Lemma srepls_nxt : forall J e ts cs, nxt (srepls J e ts cs) = nxt cs.
Proof. intros J e ts. induction ts as [|t r IH]; intros cs; [reflexivity|]. cbn [srepls]. rewrite IH. reflexivity. Qed.
(* [comment removed for export] *)
Lemma srepl_at_log : forall c t sel cs, s_log (a_ss cs) = [] -> s_log (a_ss (srepl_at c t sel cs)) = [].
Proof.
  intros c t sel cs H. unfold srepl_at.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [a_ss]; try exact H; reflexivity.
Qed.
Lemma srepl_at_pc : forall c t sel cs, pc (srepl_at c t sel cs) = pc cs.
Proof.
  intros c t sel cs. unfold srepl_at.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Lemma srepl_sels_log : forall c t sels cs, s_log (a_ss cs) = [] -> s_log (a_ss (srepl_sels c t sels cs)) = [].
Proof.
  intros c t sels. unfold srepl_sels. induction sels as [|sel r IH]; intros cs H; [exact H|]. cbn [fold_left].
  apply IH. apply srepl_at_log. exact H.
Qed.
Lemma srepl_sels_pc : forall c t sels cs, pc (srepl_sels c t sels cs) = pc cs.
Proof.
  intros c t sels. unfold srepl_sels. induction sels as [|sel r IH]; intros cs; [reflexivity|]. cbn [fold_left].
  rewrite IH. apply srepl_at_pc.
Qed.
Lemma srepls_pos_log : forall J e ts sels cs, s_log (a_ss cs) = [] -> s_log (a_ss (srepls_pos J e ts sels cs)) = [].
Proof. intros J e ts sels. induction ts as [|t r IH]; intros cs H; [exact H|]. cbn [srepls_pos]. apply IH. apply srepl_sels_log. exact H. Qed.
Lemma srepls_pos_pc : forall J e ts sels cs, pc (srepls_pos J e ts sels cs) = pc cs.
Proof. intros J e ts sels. induction ts as [|t r IH]; intros cs; [reflexivity|]. cbn [srepls_pos]. rewrite IH. apply srepl_sels_pc. Qed.

(* [comment removed for export] *)
Lemma A_bytes_perm : forall l l', Permutation l l' -> A_bytes l = A_bytes l'.
Proof.
  intros l l' H. induction H; cbn [A_bytes]; try lia.
Qed.
Lemma existsb_perm : forall {T} (f : T -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros T f l l' H. destruct (existsb f l) eqn:E1; destruct (existsb f l') eqn:E2; try reflexivity.
  - apply existsb_exists in E1 as (x & Hx & Hf). assert (X : existsb f l' = true) by (apply existsb_exists; exists x; split; [exact (Permutation_in _ H Hx) | exact Hf]). congruence.
  - apply existsb_exists in E2 as (x & Hx & Hf). assert (X : existsb f l = true) by (apply existsb_exists; exists x; split; [exact (Permutation_in _ (Permutation_sym H) Hx) | exact Hf]). congruence.
Qed.
Lemma MInv_perm : forall l l' m, Permutation l l' -> MInv l m -> MInv l' m.
Proof.
  intros l l' m HP [N1 N2 N3 N4 N5]. constructor; try assumption.
  - intros p Hp. unfold page_allowedb. rewrite <- (existsb_perm _ _ _ HP). exact (N3 p Hp).
  - rewrite <- (A_bytes_perm _ _ HP). exact N5.
Qed.
Lemma list_insert_nth_perm : forall {T} i (x : T) l, Permutation (list_insert_nth i x l) (x :: l).
Proof.
  intros T i. induction i as [|i IH]; intros x l; destruct l as [|y l]; cbn [list_insert_nth]; try reflexivity.
  eapply Permutation_trans; [apply perm_skip; exact (IH x l)|]. apply perm_swap.
Qed.
Lemma remove_nth_perm : forall {T} i (l : list T) p, nth_error l i = Some p -> Permutation l (p :: remove_nth i l).
Proof.
  intros T i l p H. unfold remove_nth.
  assert (E : l = firstn i l ++ p :: skipn (S i) l).
  { revert l H. induction i as [|i IH]; intros l H; destruct l as [|y l]; cbn in H |- *; try discriminate.
    - injection H as ->. reflexivity.
    - f_equal. apply IH. exact H. }
  rewrite E at 1. apply Permutation_sym, Permutation_middle.
Qed.

Section WF.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.
Variable FS0 : Fs.Fs.
Hypothesis NX0_7 : nx0_ok nx0.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

(* [comment removed for export] *)
Lemma cs_ok_with_vis : forall E cs R FULL model v' ab' extra,
  cs_ok SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model ->
  Permutation v' (extra ++ a_vis cs) ->
  Forall (fun p => bv_unsigned (edenot E (snd p)) = 0) extra ->
  A_bytes (flat_map (allow1 A E) extra) + a_abytes cs <= ab' ->
  eager_used model + A_bytes (allowA A E cs) + A_bytes (flat_map (allow1 A E) extra) <= LIMIT ->
  cs_ok SEGS A LIMIT SINV argH LINV FS0 E (with_vis cs v' ab') R FULL model.
Proof.
  intros E cs R FULL model v' ab' extra HC HP Hz Hab Hlim.
  set (cs' := with_vis cs v' ab').
  assert (HIA : in_allow A E cs' = in_allow A E cs).
  { apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold cs'. cbn [with_vis a_vis].
    rewrite !(existsb_perm _ _ _ HP), !existsb_app.
    assert (X1 : existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool extra = false).
    { apply not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Hf).
      pose proof (proj1 (Forall_forall _ _) Hz p Hp) as Hp0. unfold uE in Hf. rewrite Hp0 in Hf.
      apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia. }
    assert (X2 : existsb (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool extra = false).
    { apply not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Hf).
      pose proof (proj1 (Forall_forall _ _) Hz p Hp) as Hp0. unfold sh_lo, sh_hi, uE in Hf. rewrite Hp0, Z.add_0_r in Hf.
      apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia. }
    rewrite X1, X2. reflexivity. }
  assert (HH : hid A argH E cs' model = hid A argH E cs model).
  { apply functional_extensionality. intros a. unfold hid, vis. rewrite HIA. reflexivity. }
  assert (HMr : Mr A argH E cs' model FULL = Mr A argH E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
  assert (HAP : Permutation (allowA A E cs') (allowA A E cs ++ flat_map (allow1 A E) extra)).
  { unfold allowA, cs'. cbn [with_vis a_vis a_ghost]. rewrite <- flat_map_app.
    apply Permutation_flat_map. eapply Permutation_trans; [apply Permutation_app_tail; exact HP|].
    replace ((extra ++ a_vis cs) ++ a_ghost cs) with (extra ++ (a_vis cs ++ a_ghost cs)) by (rewrite app_assoc; reflexivity).
    apply Permutation_app_comm. }
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC) as HE.
  pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as HAB0.
  pose proof HAP as HAP2.
  assert (HAB : A_bytes (allowA A E cs') <= ab').
  { rewrite (A_bytes_perm _ _ HAP2), A_bytes_app. cbn [cs' with_vis a_abytes]. lia. }
  destruct HC; constructor; rewrite ?HMr;
    cbn [cs' with_vis a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - apply (MInv_perm _ _ _ (Permutation_sym HAP2)). apply MInv_app_r; [exact co_minv0|].
    rewrite A_bytes_app. rewrite co_limit0. lia.
  - intros a H1 H2 H3 H4 H5. rewrite HH in H1. exact (co_zero0 a H1 H2 H3 H4 H5).
Qed.

Lemma env_agree_refl0 : forall b E, env_agree b E E.
Proof. intros b E. split; [intros; reflexivity | reflexivity]. Qed.

Lemma xhi_zero : forall E M k e, know_ok SEGS E M k -> xhi k e = Some 0 -> bv_unsigned (edenot E e) = 0.
Proof. intros E M k e HK H. pose proof (xhi_sound SEGS E M k e 0 HK H) as X. pose proof (u64_range (edenot E e)). lia. Qed.

Lemma allow1_cost0 : forall E b n, bv_unsigned (edenot E n) = 0 -> A_bytes (allow1 A E (b, n)) <= vis_cost 0.
Proof.
  intros E b n Hn. unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi, uE. cbn [fst snd]. rewrite Hn, Z.add_0_r.
  pose proof (pageup_minus_pagedown (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b)) ltac:(lia)) as G1.
  pose proof (pageup_minus_pagedown (shadow_off A + bv_unsigned (edenot E b) / 8) (shadow_off A + bv_unsigned (edenot E b) / 8) ltac:(lia)) as G2.
  lia.
Qed.

(* [comment removed for export] *)
Lemma node_visdummy_inv : forall cs args cs', node_visdummy LIMIT cs args = Some cs' ->
  exists i b s, args = [ELit i; b; s] /\ xhi (kn cs) s = Some 0 /\ a_eager cs + a_abytes cs + vis_cost 0 <= LIMIT
    /\ cs' = with_vis cs (list_insert_nth (Z.to_nat i) (b, s) (a_vis cs)) (a_abytes cs + vis_cost 0).
Proof.
  intros cs args cs' H. unfold node_visdummy in H.
  repeat (match type of H with
          | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
          end).
  destruct (xhi (kn cs) e0) as [h|] eqn:Hx; [|rewrite !andb_false_r, andb_false_l in H; discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  repeat match goal with
         | X : Z.leb _ LIMIT = true |- _ => apply Z.leb_le in X
         | X : Z.eqb h 0 = true |- _ => apply Z.eqb_eq in X; subst h
         end.
  eexists _, _, _. split; [reflexivity|]. split; [exact Hx|]. split; [assumption | reflexivity].
Qed.

Theorem node_visdummy_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_visdummy LIMIT cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
  destruct (node_visdummy_inv cs args cs' Hn) as (i & b & s & -> & Hx & Hlim & ->). clear Hn.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xhi_zero E _ (kn cs) s HK Hx) as Hs0.
  assert (Hc1 : A_bytes (flat_map (allow1 A E) [(b, s)]) <= vis_cost 0).
  { cbn [flat_map]. rewrite app_nil_r. apply allow1_cost0. exact Hs0. }
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC) as HE.
  pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as HAB0.
  apply (Hk E R FULL model (conj (env_agree_refl0 _ _) (env_agree_refl0 _ _))); [|reflexivity].
  apply (cs_ok_with_vis E cs R FULL model _ _ [(b, s)] HC).
  - apply list_insert_nth_perm.
  - constructor; [exact Hs0 | constructor].
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma node_kdisjempty_inv : forall cs args cs', node_kdisjempty cs args = Some cs' ->
  exists a1 n1 a2 n2 b1 o1 b2, args = [a1; n1; a2; n2] /\ split_lit a1 = (b1, o1) /\ split_lit a2 = (b2, 0)
    /\ 0 <= o1 /\ xhi (kn cs) b2 = Some 0 /\ xhi (kn cs) n2 = Some 0
    /\ cs' = add_kn cs [KDisj (SA b1 o1) n1 (SA b2 0) n2].
Proof.
  intros cs args cs' H. unfold node_kdisjempty in H.
  repeat (match type of H with
          | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
          end).
  destruct (split_lit e) as [b1 o1] eqn:H1. destruct (split_lit e1) as [b2 o2] eqn:H2.
  destruct (xhi (kn cs) b2) as [h1|] eqn:Hb; [|rewrite ?andb_false_r, ?andb_false_l in H; discriminate].
  destruct (xhi (kn cs) e2) as [h2|] eqn:Hn2; [|rewrite ?andb_false_r, ?andb_false_l in H; discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  repeat match goal with
         | X : Z.leb 0 o1 = true |- _ => apply Z.leb_le in X
         | X : Z.eqb o2 0 = true |- _ => apply Z.eqb_eq in X; subst o2
         | X : Z.eqb h1 0 = true |- _ => apply Z.eqb_eq in X; subst h1
         | X : Z.eqb h2 0 = true |- _ => apply Z.eqb_eq in X; subst h2
         end.
  exists e, e0, e1, e2, b1, o1, b2. repeat split; assumption.
Qed.

Theorem node_kdisjempty_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_kdisjempty cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
  destruct (node_kdisjempty_inv cs args cs' Hn) as (a1 & n1 & a2 & n2 & b1 & o1 & b2 & -> & _ & _ & Ho1 & Hb2 & Hn2 & ->). clear Hn.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xhi_zero E _ (kn cs) b2 HK Hb2) as Z2. pose proof (xhi_zero E _ (kn cs) n2 HK Hn2) as Zn.
  apply (Hk E R FULL model (conj (env_agree_refl0 _ _) (env_agree_refl0 _ _))); [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. right. unfold estart, elenZ. cbn [a_base a_off]. rewrite Z2, Zn.
  pose proof (u64_range (edenot E b1)). lia.
Qed.

(* [comment removed for export] *)
Lemma node_visperm_inv : forall cs args cs', node_visperm cs args = Some cs' ->
  exists i j p, args = [ELit i; ELit j] /\ nth_error (a_vis cs) (Z.to_nat i) = Some p
    /\ cs' = with_vis cs (list_insert_nth (Z.to_nat j) p (remove_nth (Z.to_nat i) (a_vis cs))) (a_abytes cs).
Proof.
  intros cs args cs' H. unfold node_visperm in H.
  repeat (match type of H with
          | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
          end).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (nth_error (a_vis cs) (Z.to_nat z)) as [p|] eqn:Hp; [|discriminate].
  injection H as <-. exists z, z0, p. repeat split; assumption.
Qed.

Theorem node_visperm_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_visperm cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
  destruct (node_visperm_inv cs args cs' Hn) as (i & j & p & -> & Hp & ->). clear Hn.
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as HL. pose proof (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HM.
  pose proof (minv_budget _ _ HM) as HB.
  apply (Hk E R FULL model (conj (env_agree_refl0 _ _) (env_agree_refl0 _ _))); [|reflexivity].
  apply (cs_ok_with_vis E cs R FULL model _ _ [] HC).
  - cbn [app]. eapply Permutation_trans; [apply list_insert_nth_perm|]. apply Permutation_sym. apply remove_nth_perm. exact Hp.
  - constructor.
  - cbn [flat_map A_bytes]. lia.
  - cbn [flat_map A_bytes]. rewrite <- HL. lia.
Qed.

(* [comment removed for export] *)
Lemma node_gen_inv : forall cs args cs', node_gen nx0 cs args = Some cs' ->
  exists e lo hi ts l h, args = e :: ELit lo :: ELit hi :: ts /\ fresh_ok nx0 cs = true
    /\ acs_eqb (inst (srepls (nxt cs) e ts cs) (nxt cs) e) (inst cs (nxt cs) e) = true
    /\ xlo (kn cs) e = Some l /\ xhi (kn cs) e = Some h /\ lo <= l /\ h <= hi
    /\ cs' = bump (add_kn (srepls (nxt cs) e ts cs) [KRange (EVar (nxt cs)) lo hi]) 1.
Proof.
  intros cs args cs' H. unfold node_gen in H.
  repeat (match type of H with
          | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
          end).
  destruct (xlo (kn cs) e) as [xl|] eqn:Hl; [|rewrite ?andb_false_r in H; discriminate].
  destruct (xhi (kn cs) e) as [xh|] eqn:Hh; [|rewrite ?andb_false_r in H; discriminate].
  cbv beta iota in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  repeat match goal with
         | X : (_ && _)%bool = true |- _ => apply andb_prop in X as [?X1 ?X2]
         end.
  repeat match goal with
         | X : Z.leb _ xl = true |- _ => apply Z.leb_le in X
         | X : Z.leb xh _ = true |- _ => apply Z.leb_le in X
         end.
  eexists _, _, _, _, xl, xh. split; [reflexivity|]. split; [assumption|]. split; [assumption|].
  split; [exact Hl|]. split; [exact Hh|]. split; [assumption|]. split; [assumption|]. reflexivity.
Qed.

Theorem node_gen_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_gen nx0 cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
  destruct (node_gen_inv cs args cs' Hn) as (e & lo & hi & ts & l & h & -> & Hf & Heq & Hl & Hh & Hlo & Hhi & ->). clear Hn.
  apply acs_eqb_eq in Heq.
  pose proof (fresh_ok_parts nx0 cs Hf) as (_ & _ & _ & _ & _ & _ & Fle).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) e l HK Hl) as Bl. pose proof (xhi_sound SEGS E _ (kn cs) e h HK Hh) as Bh.
  set (J := nxt cs) in *. set (cs1 := srepls J e ts cs) in *.
  set (E' := upd E J (edenot E e)).
  assert (Hlog : s_log (a_ss cs1) = []) by (apply srepls_log; exact (co_log _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  assert (Hag : env_agree J E E') by apply upd_agree.
  assert (HC0 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E (inst cs J e) R FULL model).
  { apply (proj2 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E J e cs R FULL model Fle
                    (co_log _ _ _ _ _ _ _ _ _ _ _ _ HC))).
    exact (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E E' cs R FULL model Hag Hf HC). }
  assert (HC1 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E' cs1 R FULL model).
  { apply (proj1 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E J e cs1 R FULL model Fle Hlog)).
    rewrite Heq. exact HC0. }
  assert (Hpc : pc cs = pc (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)).
  { unfold bump, add_kn, set_kn, with_ss. cbn [a_ss s_pc]. unfold cs1. rewrite <- (srepls_pc J e ts cs). reflexivity. }
  rewrite Hpc.
  apply (Hk E' R FULL model (conj (env_agree_le _ _ E E' Hag Fle) Hag)); [|reflexivity].
  assert (HC2 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E' (add_kn cs1 [KRange (EVar J) lo hi]) R FULL model).
  { unfold add_kn. apply cs_ok_set_kn; [exact HC1|]. constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1)].
    cbn [kentry_ok]. cbn [edenot]. unfold E'. rewrite upd_at. lia. }
  destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_genp_inv : forall cs args cs', node_genp nx0 cs args = Some cs' ->
  exists e lo hi ts sels l h, fresh_ok nx0 cs = true
    /\ acs_eqb (inst (srepls_pos (nxt cs) e ts sels cs) (nxt cs) e) (inst cs (nxt cs) e) = true
    /\ xlo (kn cs) e = Some l /\ xhi (kn cs) e = Some h /\ lo <= l /\ h <= hi
    /\ cs' = bump (add_kn (srepls_pos (nxt cs) e ts sels cs) [KRange (EVar (nxt cs)) lo hi]) 1.
Proof.
  intros cs args cs' H. unfold node_genp in H.
  repeat (match type of H with
          | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
          end).
  destruct (split_sep args) as [[ts sels]|]; [|discriminate].
  destruct (xlo (kn cs) e) as [xl|] eqn:Hl; [|rewrite ?andb_false_r in H; discriminate].
  destruct (xhi (kn cs) e) as [xh|] eqn:Hh; [|rewrite ?andb_false_r in H; discriminate].
  cbv beta iota in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  repeat match goal with
         | X : (_ && _)%bool = true |- _ => apply andb_prop in X as [?X1 ?X2]
         end.
  repeat match goal with
         | X : Z.leb _ xl = true |- _ => apply Z.leb_le in X
         | X : Z.leb xh _ = true |- _ => apply Z.leb_le in X
         end.
  eexists _, _, _, ts, sels, xl, xh. split; [assumption|]. split; [eassumption|].
  split; [exact Hl|]. split; [exact Hh|]. split; [eassumption|]. split; [eassumption|]. reflexivity.
Qed.

Theorem node_genp_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_genp nx0 cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
  destruct (node_genp_inv cs args cs' Hn) as (e & lo & hi & ts & sels & l & h & Hf & Heq & Hl & Hh & Hlo & Hhi & ->). clear Hn.
  apply acs_eqb_eq in Heq.
  pose proof (fresh_ok_parts nx0 cs Hf) as (_ & _ & _ & _ & _ & _ & Fle).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) e l HK Hl) as Bl. pose proof (xhi_sound SEGS E _ (kn cs) e h HK Hh) as Bh.
  set (J := nxt cs) in *. set (cs1 := srepls_pos J e ts sels cs) in *.
  set (E' := upd E J (edenot E e)).
  assert (Hlog : s_log (a_ss cs1) = []) by (apply srepls_pos_log; exact (co_log _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  assert (Hag : env_agree J E E') by apply upd_agree.
  assert (HC0 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E (inst cs J e) R FULL model).
  { apply (proj2 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E J e cs R FULL model Fle
                    (co_log _ _ _ _ _ _ _ _ _ _ _ _ HC))).
    exact (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E E' cs R FULL model Hag Hf HC). }
  assert (HC1 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E' cs1 R FULL model).
  { apply (proj1 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E J e cs1 R FULL model Fle Hlog)).
    rewrite Heq. exact HC0. }
  assert (Hpc : pc cs = pc (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)).
  { unfold bump, add_kn, set_kn, with_ss. cbn [a_ss s_pc]. unfold cs1. rewrite <- (srepls_pos_pc J e ts sels cs). reflexivity. }
  rewrite Hpc.
  apply (Hk E' R FULL model (conj (env_agree_le _ _ E E' Hag Fle) Hag)); [|reflexivity].
  assert (HC2 : cs_ok SEGS A LIMIT SINV argH LINV FS0 E' (add_kn cs1 [KRange (EVar J) lo hi]) R FULL model).
  { unfold add_kn. apply cs_ok_set_kn; [exact HC1|]. constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1)].
    cbn [kentry_ok]. cbn [edenot]. unfold E'. rewrite upd_at. lia. }
  destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.


(* [comment removed for export] *)
Lemma xinside0_sound' : forall E M kn b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M kn -> xinside0 kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z /\ (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2)%Z.
Proof.
  intros E M kn b1 k1 n1 b2 k2 n2 Hkn H0. unfold xinside0 in H0.
  lazymatch type of H0 with (if ?c then _ else _) = _ => destruct c eqn:H1; [|discriminate] end. rename H0 into H2.
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H1) as HA. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H2) as HB.
  cbn [xt_den] in HA, HB. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma kdisj_relB0_sound : forall E M allkn kn b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M allkn -> know_ok SEGS E M kn -> kdisj_relB0 (AX2B.mkbc allkn) kn b1 k1 n1 b2 k2 n2 = true ->
  kentry_ok SEGS E M (KDisj (SA b1 k1) n1 (SA b2 k2) n2).
Proof.
  intros E M allkn kn b1 k1 n1 b2 k2 n2 Hall Hkn. induction kn as [|K rest IH]; cbn [kdisj_relB0]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [| | | | | | |[c1 o1] m1 [c2 o2] m2| |]; try (apply IH; assumption).
  rewrite !AX2B.xinside0B_eqf in H. cbn [kentry_ok] in HK |- *.
  destruct (xinside0 allkn b1 k1 n1 c1 o1 m1) eqn:X1; destruct (xinside0 allkn b2 k2 n2 c2 o2 m2) eqn:X2;
  destruct (xinside0 allkn b1 k1 n1 c2 o2 m2) eqn:X3; destruct (xinside0 allkn b2 k2 n2 c1 o1 m1) eqn:X4;
  cbn in H; try (apply IH; assumption);
  repeat match goal with
         | X : xinside0 _ _ _ _ _ _ _ = true |- _ => apply (xinside0_sound' E M allkn) in X; [|exact Hall]
         end;
  unfold estart in *; cbn [a_base a_off] in *; lia.
Qed.
Lemma kdisj_relB_sound : forall E M allkn kn b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M allkn -> know_ok SEGS E M kn -> kdisj_relB (AX2B.mkbc allkn) kn b1 k1 n1 b2 k2 n2 = true ->
  kentry_ok SEGS E M (KDisj (SA b1 k1) n1 (SA b2 k2) n2).
Proof.
  intros E M allkn kn b1 k1 n1 b2 k2 n2 Hall Hkn H. apply (kdisj_relB0_sound E M allkn kn b1 k1 n1 b2 k2 n2 Hall Hkn).
  unfold kdisj_relB in H. revert H.
  destruct (kdisj_pass1B (AX2B.mkbc allkn) kn b1 k1 n1 b2 k2 n2) eqn:P1; intros H.
  - exact (kdisj_pass1B_rel0 _ _ _ _ _ _ _ _ P1).
  - exact H.
Qed.

Lemma kdisj_batch_sound : forall E M allkn nx args l,
  know_ok SEGS E M allkn -> kdisj_batch (AX2B.mkbc allkn) allkn nx args = Some l -> know_ok SEGS E M l.
Proof.
  intros E M allkn nx args. remember (length args) as L eqn:HL. revert args HL.
  induction L as [L IH] using (well_founded_induction lt_wf); intros args HL l HK H.
  destruct args as [|b1 [|[k1| | | | | | |] [|n1 [|b2 [|[k2| | | | | | |] [|n2 rest]]]]]]; cbn [kdisj_batch] in H;
    try discriminate H.
  - injection H as <-. constructor.
  - destruct (_ && _ && _ && _)%bool; [|discriminate H].
    destruct (kdisj_relB _ _ b1 k1 n1 b2 k2 n2) eqn:Hv; [|discriminate H].
    destruct (kdisj_batch _ _ nx rest) as [l'|] eqn:Hr; [|discriminate H]. injection H as <-.
    constructor; [exact (kdisj_relB_sound E M allkn allkn _ _ _ _ _ _ HK HK Hv)|].
    exact (IH (length rest) ltac:(cbn in HL; lia) rest eq_refl l' HK Hr).
Qed.

Theorem node_kdisjrel_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_kdisjrel cs args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_kdisjrel in Hn.
  destruct args as [|x r]; [discriminate Hn|].
  destruct (kdisj_batch _ (kn cs) (nxt cs) (x :: r)) as [l|] eqn:Hb; [|discriminate Hn]. injection Hn as <-.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  apply (Hk E R FULL model (conj (env_agree_refl0 _ _) (env_agree_refl0 _ _))); [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [|exact HK].
  exact (kdisj_batch_sound E _ (kn cs) (nxt cs) (x :: r) l HK Hb).
Qed.


Theorem xwd_xn_sound : forall id args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (XWD.xn nx0 LIMIT id args).
Proof.
  intros id args. unfold XWD.xn.
  destruct (Nat.eqb id 206). { apply node_gen_sound. }
  destruct (Nat.eqb id 207). { apply node_visdummy_sound. }
  destruct (Nat.eqb id 208). { apply node_kdisjempty_sound. }
  destruct (Nat.eqb id 209). { apply node_visperm_sound. }
  destruct (Nat.eqb id 216). { apply node_genp_sound. }
  destruct (Nat.eqb id 218). { apply node_kdisjrel_sound. }
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End WF.
End FPW.
