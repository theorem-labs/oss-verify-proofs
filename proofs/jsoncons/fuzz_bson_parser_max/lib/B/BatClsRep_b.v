(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).

Lemma art_refill_need : forall c, 1 <= c <= 30 -> AsanTab.class_size c * Z.of_nat (art_refill_n c) <= 65536 /\ (1 <= art_refill_n c <= 8)%nat.
Proof.
  intros c Hc.
  assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 30)) -> AsanTab.class_size x * Z.of_nat (art_refill_n x) <= 65536 /\ (1 <= art_refill_n x <= 8)%nat).
  { intros x Hx. cbn [map seq In] in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; split; [discriminate|split; apply Nat.leb_le; reflexivity]|]). destruct Hx. }
  apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma art_cptr_lt : forall sz au w, 0 < sz -> au <= 3758096384 -> art_cptr_ok sz au w -> 0 <= w < 2 ^ 28.
Proof. intros sz au w Hsz Hau (H0 & H1 & _). lia. Qed.

Lemma art_cptr_mono : forall sz au au' w, au <= au' -> art_cptr_ok sz au w -> art_cptr_ok sz au' w.
Proof. intros sz au au' w H (H0 & H1 & H2). repeat split; [exact H0|lia|exact H2]. Qed.

(* [comment removed for export] *)
Lemma art_region_rep_upd : forall spb ris c mx mx' (cl cl' : art_cls) (M M' : word -> option byte) (W : list (Z * Z)),
  let fa := spb + c * 2 ^ 32 + 3758096384 in
  let r := ris + 128 * c in
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 2 ^ 29 < 2 ^ 64 -> 4 * Z.of_nat (length (cl_free cl)) <= 2 ^ 29 ->
  cl_mfa cl' = cl_mfa cl -> cl_au cl' = cl_au cl -> cl_mu cl' = cl_mu cl -> cl_nfr cl' = cl_nfr cl ->
  (length (cl_free cl') <= length (cl_free cl))%nat -> (forall j, (j < length (cl_free cl'))%nat -> nth j (cl_free cl') 0 = nth j (cl_free cl) 0) ->
  art_region_rep spb ris c mx cl M -> mem_grows M M' -> art_agree W M M' ->
  art_gap W (r + 24) 40 -> art_gap W (r + 80) 8 -> art_gap W fa (4 * Z.of_nat (length (cl_free cl'))) ->
  cellA M' r 8 mx' -> cellA M' (r + 16) 8 (Z.of_nat (length (cl_free cl'))) -> cellA M' (r + 72) 8 (cl_na cl') ->
  art_region_rep spb ris c mx' cl' M'.
Proof.
  intros spb ris c mx mx' cl cl' M M' W fa r Hr Hr' Hfa Hfa' Hnf Emfa Eau Emu Enfr Hlen Hnth RR G A G24 G80 GFA Cmx Cnf Cna.
  destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa.
  unfold art_region_rep. fold r fa. rewrite Emfa, Eau, Emu, Enfr.
  assert (T : forall a (n : nat) v, r + 24 <= a -> a + Z.of_nat n <= r + 64 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G24|lia|lia]|lia|lia|exact C]. }
  split; [exact Cmx|]. split; [exact Cnf|].
  split; [apply T; [lia|cbn; lia|exact Rmfa]|]. split; [apply T; [lia|cbn; lia|exact Rau]|]. split; [apply T; [lia|cbn; lia|exact Ram]|].
  split; [apply T; [lia|cbn; lia|exact Rmu]|]. split; [apply T; [lia|cbn; lia|exact Rmm]|].
  split; [exact Cna|].
  split. { apply (art_cell_tr W M M'); [exact A|exact G80|lia|cbn; lia|exact Rnfr]. }
  split. { intros j Hj. rewrite (Hnth j Hj). pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. pose proof (proj1 (Nat2Z.inj_le _ _) Hlen) as Hl'.
           apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|apply Rfa; lia]. }
  split; [eapply wr_grows; [exact G|exact Wr]|]. split; [eapply wr_grows; [exact G|exact Wfa]|eapply wr_grows; [exact G|exact Wu]].
Qed.

Lemma art_NoDup_map_in : forall (A B : Type) (f : A -> B) (l : list A),
  List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof.
  intros A B f l H. induction H as [|a l Hna Hnd IH]; intros Inj; cbn; [constructor|]. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy). apply Hna. rewrite (Inj a y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
  - apply IH. intros x y Hx Hy. apply Inj; right; assumption.
Qed.

(* [comment removed for export] *)
Lemma art_carved_in : forall au sz new w, In w (art_carved au sz new) -> exists i, 0 <= i < Z.of_nat new /\ w = (au + i * sz) / 16.
Proof.
  intros au sz new w H. unfold art_carved in H. apply in_map_iff in H. destruct H as (k & E & Hk). apply in_seq in Hk.
  exists (Z.of_nat new - 1 - Z.of_nat k). split; [lia|]. symmetry. exact E.
Qed.

Lemma art_div16_mul : forall sz k, sz mod 16 = 0 -> (sz * k) / 16 * 16 = sz * k.
Proof.
  intros sz k H. assert (E : sz = 16 * (sz / 16)). { pose proof (Z.div_mod sz 16 ltac:(lia)) as D. rewrite H in D. lia. }
  rewrite E at 1. replace (16 * (sz / 16) * k) with ((sz / 16 * k) * 16) by lia. rewrite Z_div_mult by lia. rewrite E at 2. lia.
Qed.

Lemma art_cls_ok_populate : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  cl_mu cl + 262144 <= 3758096384 -> art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912 ->
  art_cls_ok c (art_cls_populate c cl).
Proof.
  intros c cl Hc OK Room1 Room2.
  destruct OK as (Hlc & (Hau0 & Haumu) & Hrem0 & (km & Emu) & (ka & Eau) & Hmu3 & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & Hnd).
  destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
  set (sz := AsanTab.class_size c) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
  set (new := art_cls_new c cl) in *.
  assert (Enew : cl_mu cl + 262144 - cl_au cl = sz * new + (cl_mu cl + 262144 - cl_au cl) mod sz) by (unfold new, art_cls_new; fold sz; apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound (cl_mu cl + 262144 - cl_au cl) sz ltac:(lia)) as Hrem.
  set (rem := (cl_mu cl + 262144 - cl_au cl) mod sz) in *.
  assert (Hnew : 1 <= new). { destruct (Z_lt_le_dec new 1) as [Lt|Ge]; [|exact Ge]. exfalso. assert (sz * new <= 0) by nia. lia. }
  assert (Hka : 0 <= ka) by nia.
  unfold art_cls_ok, art_cls_populate. cbn [cl_cache cl_free cl_au cl_mu cl_mfa]. fold sz nf new.
  assert (Elen : Z.of_nat (length (cl_free cl ++ art_carved (cl_au cl) sz (Z.to_nat new))) = nf + new).
  { rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
  split; [exact Hlc|]. split; [nia|]. split; [nia|].
  split; [exists (km + 1); lia|]. split; [exists (ka + new); nia|]. split; [exact Room1|].
  split. { unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl); [exists kf; exact Emfa|]. exists ((4 * (nf + new) + 262143) / 262144). lia. }
  split. { split; [|exact Room2]. unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl); [exact Hmfa0|].
           assert (0 <= (4 * (nf + new) + 262143) / 262144) by (apply Z.div_pos; unfold nf; lia). lia. }
  split. { rewrite Elen. unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl) eqn:E; [apply Z.leb_le in E; exact E|].
           pose proof (Z.div_mod (4 * (nf + new) + 262143) 262144 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (4 * (nf + new) + 262143) 262144 ltac:(lia)) as R. lia. }
  assert (Hcar : forall w, In w (art_carved (cl_au cl) sz (Z.to_nat new)) -> exists i, 0 <= i < new /\ 16 * w = sz * (ka + i)).
  { intros w Hw. apply art_carved_in in Hw. destruct Hw as (i & Hi & Ew). rewrite Z2Nat.id in Hi by lia. exists i. split; [exact Hi|].
    rewrite Ew, Eau. replace (sz * ka + i * sz) with (sz * (ka + i)) by lia. pose proof (art_div16_mul sz (ka + i) Hsz16). lia. }
  split.
  { rewrite app_assoc. apply Forall_app. split.
    - eapply Forall_impl; [|exact Hfor]. intros w Hw. eapply art_cptr_mono; [|exact Hw]. nia.
    - apply Forall_forall. intros w Hw. destruct (Hcar w Hw) as (i & Hi & Ew). unfold art_cptr_ok. split; [nia|]. split; [nia|]. exists (ka + i). exact Ew. }
  rewrite app_assoc. apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. apply List.NoDup_app; [exact Hnd| |].
  - unfold art_carved. apply art_NoDup_map_in; [apply seq_NoDup|]. intros x y Hx Hy E. apply in_seq in Hx. apply in_seq in Hy.
    assert (Ex : ((cl_au cl + (Z.of_nat (Z.to_nat new) - 1 - Z.of_nat x) * sz) / 16) * 16 = sz * (ka + (new - 1 - Z.of_nat x))).
    { rewrite Z2Nat.id by lia. rewrite Eau. replace (sz * ka + (new - 1 - Z.of_nat x) * sz) with (sz * (ka + (new - 1 - Z.of_nat x))) by lia. apply art_div16_mul. exact Hsz16. }
    assert (Ey : ((cl_au cl + (Z.of_nat (Z.to_nat new) - 1 - Z.of_nat y) * sz) / 16) * 16 = sz * (ka + (new - 1 - Z.of_nat y))).
    { rewrite Z2Nat.id by lia. rewrite Eau. replace (sz * ka + (new - 1 - Z.of_nat y) * sz) with (sz * (ka + (new - 1 - Z.of_nat y))) by lia. apply art_div16_mul. exact Hsz16. }
    rewrite E in Ex. rewrite Ex in Ey. assert (ka + (new - 1 - Z.of_nat x) = ka + (new - 1 - Z.of_nat y)) by (apply (Z.mul_reg_l _ _ sz); lia). lia.
  - intros w Hw Hw'. destruct (Hcar w Hw') as (i & Hi & Ew).
    pose proof (proj1 (Forall_forall _ _) Hfor w Hw) as (W0 & W1 & _). nia.
Qed.

Lemma art_cls_ok_take : forall c cl (n : nat), art_cls_ok c cl -> cl_cache cl = [] -> (n <= length (cl_free cl))%nat -> (n <= 16)%nat ->
  art_cls_ok c (art_cls_take n cl).
Proof.
  intros c cl n OK Ec Hn Hn16.
  destruct OK as (Hlc & Hau & Hrem0 & Hmu & Hau' & Hmu3 & Hmfa & Hmfa' & Hnf4 & Hfor & Hnd).
  rewrite Ec in Hfor, Hnd. cbn [app] in Hfor, Hnd.
  unfold art_cls_ok, art_cls_take. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
  set (k := (length (cl_free cl) - n)%nat).
  assert (P : Permutation (cl_free cl) (skipn k (cl_free cl) ++ firstn k (cl_free cl))).
  { rewrite <- (firstn_skipn k (cl_free cl)) at 1. apply Permutation_app_comm. }
  split; [rewrite length_skipn; unfold k; lia|]. split; [exact Hau|]. split; [exact Hrem0|]. split; [exact Hmu|]. split; [exact Hau'|]. split; [exact Hmu3|].
  split; [exact Hmfa|]. split; [exact Hmfa'|].
  split. { rewrite length_firstn. lia. }
  split. { eapply Permutation_Forall; [exact P|exact Hfor]. }
  apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. eapply Permutation_NoDup; [exact P|exact Hnd].
Qed.
