(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceABx As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b BatFxQ_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvFreePure_b BatInvRepX_b
     BatRecycle1_b BatRecycle2C_b BatRecycle3L_b BatRecycle5A_b BatRecycle5I_b BatRecycle5T_b BatRecycle5C_b BatRecycle5D_b BatInvRecycleA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition art_dsec : art_sec := SEC 0 0 0 0 false.
Definition art_sec_step (e : art_rel) (l : list art_sec) : list art_sec :=
  match e with RES mb _ _ _ _ => art_swap_remove art_dsec (art_bl_idx mb (map art_sec_b l)) l | _ => l end.
Definition art_sec_rcy (work : list art_rel) (l : list art_sec) : list art_sec := fold_left (fun l e => art_sec_step e l) work l.

Lemma art_sec_rcy_b : forall work cls l, rg_bl (art_rel_steps work (RG cls (map art_sec_b l))) = map art_sec_b (art_sec_rcy work l).
Proof.
  induction work as [|e r IH]; intros cls l; [reflexivity|]. unfold art_rel_steps, art_sec_rcy in *. cbn [fold_left].
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step art_sec_step rg_cls rg_bl]; try apply IH.
  rewrite <- (art_swap_remove_map _ _ art_sec_b art_dsec). apply IH.
Qed.

Lemma art_bl_idx_sec : forall (l : list art_sec) mb, In mb (map sc_map l) -> exists s0, nth_error l (art_bl_idx mb (map art_sec_b l)) = Some s0 /\ sc_map s0 = mb.
Proof.
  induction l as [|s r IH]; intros mb Hin; [destruct Hin|]. cbn [map art_bl_idx]. cbn [art_sec_b fst]. destruct (Z.eqb_spec (sc_map s) mb) as [E|NE].
  - exists s. split; [reflexivity|exact E].
  - destruct Hin as [E|Hin]; [contradiction|]. exact (IH mb Hin).
Qed.

Lemma art_swap_remove_nodup : forall (A B : Type) (f : A -> B) (d : A) i l, List.NoDup (map f l) -> List.NoDup (map f (art_swap_remove d i l)).
Proof.
  intros A B f d i l ND. rewrite art_swap_remove_map. rewrite (NoDup_nth_error) in ND |- *. intros j1 j2 Hj1 E.
  rewrite art_swap_remove_length in Hj1. rewrite length_map in Hj1.
  assert (Hj2 : (j2 < length (map f l) - 1)%nat).
  { destruct (Nat.lt_ge_cases j2 (length (map f l) - 1)) as [H|H]; [exact H|]. exfalso.
    rewrite (proj2 (nth_error_None (art_swap_remove (f d) i (map f l)) j2)) in E by (rewrite art_swap_remove_length; exact H).
    apply nth_error_None in E. rewrite art_swap_remove_length, length_map in E. lia. }
  rewrite !art_swap_remove_nth in E by (rewrite ?length_map in *; assumption).
  assert (B1 : ((if (j1 =? i)%nat then (length (map f l) - 1)%nat else j1) < length (map f l))%nat) by (rewrite length_map in *; destruct (j1 =? i)%nat; lia).
  pose proof (ND _ _ B1 E) as EJ. rewrite length_map in *.
  destruct (Nat.eqb_spec j1 i) as [E1|E1]; destruct (Nat.eqb_spec j2 i) as [E2|E2]; lia.
Qed.

Lemma art_swap_remove_gone : forall (A B : Type) (f : A -> B) (d : A) i l x, List.NoDup (map f l) -> (i < length l)%nat -> In x (art_swap_remove d i l) -> f x <> f (nth i l d).
Proof.
  intros A B f d i l x ND Hi Hx E. destruct (In_nth_error _ _ Hx) as (j & Hj).
  assert (Hjl : (j < length l - 1)%nat) by (rewrite <- (art_swap_remove_length _ d i l); apply nth_error_Some; rewrite Hj; discriminate).
  rewrite art_swap_remove_nth in Hj by exact Hjl. set (j' := if (j =? i)%nat then (length l - 1)%nat else j) in *.
  assert (NEj : j' <> i) by (unfold j'; destruct (Nat.eqb_spec j i) as [E1|E1]; lia).
  rewrite NoDup_nth_error in ND. apply NEj. apply ND; [rewrite length_map; unfold j'; destruct (j =? i)%nat; lia|].
  rewrite !nth_error_map, Hj. rewrite (nth_error_nth' l d Hi). cbn. f_equal. exact E.
Qed.

Definition art_rel_mb (e : art_rel) : option Z := match e with RES mb _ _ _ _ => Some mb | _ => None end.

Lemma art_sec_rcy_in : forall work l s, In s (art_sec_rcy work l) -> In s l.
Proof.
  induction work as [|e r IH]; intros l s H; [exact H|]. unfold art_sec_rcy in *. cbn [fold_left] in H. apply IH in H.
  destruct e; cbn [art_sec_step] in H; try exact H. exact (art_swap_remove_in _ _ _ _ _ H).
Qed.

Lemma art_sec_rcy_nodup : forall work l, List.NoDup (map sc_map l) -> List.NoDup (map sc_map (art_sec_rcy work l)).
Proof.
  induction work as [|e r IH]; intros l ND; [exact ND|]. unfold art_sec_rcy in *. cbn [fold_left]. apply IH.
  destruct e; cbn [art_sec_step]; try exact ND. apply art_swap_remove_nodup. exact ND.
Qed.

Lemma art_sec_rcy_notin : forall work l s mb, List.NoDup (map sc_map l) -> In s (art_sec_rcy work l) -> In (Some mb) (map art_rel_mb work) -> In mb (map sc_map l) -> sc_map s <> mb.
Proof.
  induction work as [|e r IH]; intros l s mb ND Hs Hmb Hl; [destruct Hmb|]. unfold art_sec_rcy in *. cbn [fold_left] in Hs. cbn [map] in Hmb.
  destruct Hmb as [Ee|Hmb].
  - destruct e as [c w d b1 n|mb0 ms m b1 n|wb]; cbn [art_rel_mb] in Ee; try discriminate Ee. injection Ee as ->. cbn [art_sec_step] in Hs.
    apply art_sec_rcy_in in Hs. destruct (art_bl_idx_sec l mb Hl) as (s0 & Hn & Es0).
    pose proof (art_swap_remove_gone _ _ sc_map art_dsec _ l s ND ltac:(apply nth_error_Some; rewrite Hn; discriminate) Hs) as NE.
    rewrite (nth_error_nth _ _ art_dsec Hn) in NE. rewrite Es0 in NE. exact NE.
  - set (l1 := art_sec_step e l) in *. destruct (in_dec Z.eq_dec mb (map sc_map l1)) as [X|X].
    + apply (IH l1 s mb); [|exact Hs|exact Hmb|exact X]. unfold l1. destruct e; cbn [art_sec_step]; try exact ND. apply art_swap_remove_nodup. exact ND.
    + intros E. apply X. rewrite <- E. apply in_map. exact (art_sec_rcy_in r l1 s Hs).
Qed.

Lemma art_mb_key : forall work mb, In (Some mb) (map art_rel_mb work) -> In (0, mb) (map art_rel_key work).
Proof.
  induction work as [|e r IH]; intros mb H; [destruct H|]. cbn [map] in *. destruct H as [E|H]; [left|right; exact (IH mb H)].
  destruct e; cbn [art_rel_mb art_rel_key] in *; try discriminate E. injection E as ->. reflexivity.
Qed.

Lemma art_sec_rcy_keep : forall work l s, In s l -> ~ In (Some (sc_map s)) (map art_rel_mb work) ->
  (forall mb, In (Some mb) (map art_rel_mb work) -> In mb (map sc_map l)) -> List.NoDup (map art_rel_key work) -> List.NoDup (map sc_map l) -> In s (art_sec_rcy work l).
Proof.
  induction work as [|e r IH]; intros l s Hs NI ALL NDw ND; [exact Hs|]. unfold art_sec_rcy in *. cbn [fold_left]. cbn [map] in NI, ALL, NDw.
  inversion NDw as [|? ? Hn NDr]; subst.
  assert (ND1 : List.NoDup (map sc_map (art_sec_step e l))) by (destruct e; cbn [art_sec_step]; try exact ND; apply art_swap_remove_nodup; exact ND).
  assert (Hs1 : In s (art_sec_step e l)).
  { destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_sec_step]; try exact Hs. cbn [art_rel_mb] in NI, ALL.
    destruct (art_bl_idx_sec l mb (ALL mb (or_introl eq_refl))) as (s0 & Hn0 & Es0).
    apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn0; discriminate|exact Hs|]. rewrite (nth_error_nth _ _ art_dsec Hn0). intros E. apply NI. left. rewrite E, Es0. reflexivity. }
  apply IH; [exact Hs1|intros X; apply NI; right; exact X| |exact NDr|exact ND1].
  intros mb Hmb. pose proof (ALL mb (or_intror Hmb)) as Hl. apply in_map_iff in Hl. destruct Hl as (s1 & Es1 & Hs1l).
  destruct e as [c w d b1 n|mb0 ms m b1 n|wb]; cbn [art_sec_step]; try (rewrite <- Es1; apply in_map; exact Hs1l).
  cbn [art_rel_mb art_rel_key] in Hn, ALL. destruct (art_bl_idx_sec l mb0 (ALL mb0 (or_introl eq_refl))) as (s0 & Hn0 & Es0).
  rewrite <- Es1. apply in_map. apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn0; discriminate|exact Hs1l|].
  rewrite (nth_error_nth _ _ art_dsec Hn0). intros E. apply Hn. rewrite <- Es0, <- E, Es1. exact (art_mb_key r mb Hmb).
Qed.

Lemma art_sec_rcy_len : forall work l, (length (art_sec_rcy work l) <= length l)%nat.
Proof.
  induction work as [|e r IH]; intros l; [cbn; lia|]. unfold art_sec_rcy in *. cbn [fold_left]. specialize (IH (art_sec_step e l)).
  destruct e; cbn [art_sec_step] in *; try exact IH. rewrite art_swap_remove_length in IH. lia.
Qed.

(* [comment removed for export] *)
Lemma art_steps_au : forall work G c, cl_au (rg_cls (art_rel_steps work G) c) = cl_au (rg_cls G c) /\ cl_mu (rg_cls (art_rel_steps work G) c) = cl_mu (rg_cls G c)
  /\ cl_mfa (rg_cls (art_rel_steps work G) c) = cl_mfa (rg_cls G c).
Proof.
  induction work as [|e r IH]; intros G c; [repeat split|]. unfold art_rel_steps in *. cbn [fold_left]. destruct (IH (art_rel_step e G) c) as (E1 & E2 & E3). rewrite E1, E2, E3.
  destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls]; [|repeat split|].
  - destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same; exact (art_cls_dealloc_au c0 w0 (rg_cls G c0))|rewrite art_cls_upd_other by exact NE; repeat split].
  - destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same; exact (art_cls_dealloc_au 24 wb0 (rg_cls G 24))|rewrite art_cls_upd_other by exact NE; repeat split].
Qed.

Lemma art_steps_in : forall work G c w, art_rg_ok G -> art_rels_pre G work -> 1 <= c <= 30 ->
  (In w (cl_cache (rg_cls (art_rel_steps work G) c) ++ cl_free (rg_cls (art_rel_steps work G) c))
   <-> In w (cl_cache (rg_cls G c) ++ cl_free (rg_cls G c)) \/ In (c, w) (map art_rel_key work)).
Proof.
  induction work as [|e r IH]; intros G c w OK PRE Hc; [cbn; tauto|]. destruct PRE as (Pe & Pr). unfold art_rel_steps in *. cbn [fold_left map].
  rewrite (IH (art_rel_step e G) c w (art_rg_ok_step e G OK Pe) Pr Hc). destruct OK as (CK & _).
  destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_key art_rel_pre] in *.
  - destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE].
    + rewrite art_cls_upd_same. rewrite (art_cls_dealloc_in c0 w0 (rg_cls G c0) w (CK c0 Hc0) ltac:(lia)).
      split; [intros [[->|H]|H]; [right; left; reflexivity|left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; right; exact H|left; left; injection E as ->; reflexivity|right; exact H]].
    + rewrite art_cls_upd_other by exact NE. split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
  - split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
  - destruct (Z.eq_dec c 24) as [->|NE].
    + rewrite art_cls_upd_same. rewrite (art_cls_dealloc_in 24 wb0 (rg_cls G 24) w (CK 24 ltac:(lia)) ltac:(lia)).
      split; [intros [[->|H]|H]; [right; left; reflexivity|left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; right; exact H|left; left; injection E as ->; reflexivity|right; exact H]].
    + rewrite art_cls_upd_other by exact NE. split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
Qed.

Lemma art_steps_total : forall work G c, art_rg_ok G -> art_rels_pre G work -> 1 <= c <= 30 ->
  Z.of_nat (length (cl_cache (rg_cls (art_rel_steps work G) c))) + Z.of_nat (length (cl_free (rg_cls (art_rel_steps work G) c)))
  <= Z.of_nat (length (cl_cache (rg_cls G c))) + Z.of_nat (length (cl_free (rg_cls G c))) + Z.of_nat (length work).
Proof.
  induction work as [|e r IH]; intros G c OK PRE Hc; [cbn; lia|]. destruct PRE as (Pe & Pr). unfold art_rel_steps in *. cbn [fold_left length].
  specialize (IH (art_rel_step e G) c (art_rg_ok_step e G OK Pe) Pr Hc). destruct OK as (CK & _).
  destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_pre] in *.
  - destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same in IH|rewrite art_cls_upd_other in IH by exact NE; lia].
    pose proof (art_cls_dealloc_total c0 w0 (rg_cls G c0) (CK c0 Hc0) ltac:(lia)). lia.
  - lia.
  - destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same in IH|rewrite art_cls_upd_other in IH by exact NE; lia].
    pose proof (art_cls_dealloc_total 24 wb0 (rg_cls G 24) (CK 24 ltac:(lia)) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma art_live_app_unmap : forall log mb ms, art_live (log ++ art_flush_events mb ms ++ [AMunmap mb ms]) = List.filter (fun p => negb (fst p =? mb)) (art_live log).
Proof.
  intros log mb ms. rewrite app_assoc, art_live_snoc. cbn [art_ev_live]. f_equal.
  unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms); [rewrite art_live_snoc; reflexivity|rewrite app_nil_r; reflexivity].
Qed.

Lemma art_live_rcy : forall work log p, In p (art_live (log ++ art_rels_events work)) <-> In p (art_live log) /\ ~ In (Some (fst p)) (map art_rel_mb work).
Proof.
  induction work as [|e r IH]; intros log p.
  - unfold art_rels_events. cbn [flat_map map In]. rewrite app_nil_r. tauto.
  - change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r). rewrite app_assoc, IH. cbn [map In].
    destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events art_rel_mb]; rewrite ?app_nil_r.
    + split; [intros (H1 & H2); split; [exact H1|intros [X|X]; [discriminate X|exact (H2 X)]]|intros (H1 & H2); split; [exact H1|intros X; apply H2; right; exact X]].
    + rewrite art_live_app_unmap, filter_In. rewrite negb_true_iff, Z.eqb_neq.
      split; [intros ((H1 & H0) & H2); split; [exact H1|intros [X|X]; [injection X as X; apply H0; symmetry; exact X|exact (H2 X)]]
             |intros (H1 & H2); split; [split; [exact H1|intros X; apply H2; left; rewrite X; reflexivity]|intros X; apply H2; right; exact X]].
    + split; [intros (H1 & H2); split; [exact H1|intros [X|X]; [discriminate X|exact (H2 X)]]|intros (H1 & H2); split; [exact H1|intros X; apply H2; right; exact X]].
Qed.

(* [comment removed for export] *)
Definition art_key_in (work : list art_rel) (c w : Z) : bool := existsb (fun e => (fst (art_rel_key e) =? c) && (snd (art_rel_key e) =? w)) work.
Definition art_st_rcy (work : list art_rel) (st : Z -> Z -> art_cst) (c w : Z) : art_cst := if art_key_in work c w then CFree else st c w.
Lemma art_key_in_spec : forall work c w, art_key_in work c w = true <-> In (c, w) (map art_rel_key work).
Proof.
  intros work c w. unfold art_key_in. rewrite existsb_exists. split.
  - intros (e & He & E). apply andb_true_iff in E. destruct E as (E1 & E2). apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply in_map_iff. exists e. split; [|exact He].
    destruct (art_rel_key e) as [a b]. cbn [fst snd] in *. subst. reflexivity.
  - intros H. apply in_map_iff in H. destruct H as (e & E & He). exists e. split; [exact He|]. rewrite E. cbn [fst snd]. rewrite !Z.eqb_refl. reflexivity.
Qed.
