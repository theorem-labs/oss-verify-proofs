From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem printf_facts_c check_round_trip_c.
Import ListNotations.
Open Scope Z_scope.

Definition pieces (f : list Z) : list pf_piece := match pf_parse f with Some p => p | None => [] end.

Definition ps_tw : list pf_piece := Eval vm_compute in pieces fmt_tw.
Definition ps_tx : list pf_piece := Eval vm_compute in pieces fmt_tx.
Definition ps_t1 : list pf_piece := Eval vm_compute in pieces fmt_t1.
Definition ps_t2 : list pf_piece := Eval vm_compute in pieces fmt_t2.
Definition ps_t3 : list pf_piece := Eval vm_compute in pieces fmt_t3.
Definition ps_t1x : list pf_piece := Eval vm_compute in pieces fmt_t1x.

Lemma parse_tw : pf_parse fmt_tw = Some ps_tw. Proof. vm_compute. reflexivity. Qed.
Lemma parse_tx : pf_parse fmt_tx = Some ps_tx. Proof. vm_compute. reflexivity. Qed.
Lemma parse_t1 : pf_parse fmt_t1 = Some ps_t1. Proof. vm_compute. reflexivity. Qed.
Lemma parse_t2 : pf_parse fmt_t2 = Some ps_t2. Proof. vm_compute. reflexivity. Qed.
Lemma parse_t3 : pf_parse fmt_t3 = Some ps_t3. Proof. vm_compute. reflexivity. Qed.
Lemma parse_t1x : pf_parse fmt_t1x = Some ps_t1x. Proof. vm_compute. reflexivity. Qed.

Lemma text_tw : forall zu, pf_text ps_tw [APtr zu] = Some (txt_whole zu).
Proof. intros zu. reflexivity. Qed.

Lemma text_tx : forall zu, pf_text ps_tx [APtr zu] = Some (txt_wholex zu).
Proof. intros zu. reflexivity. Qed.

Lemma pps_ok : forall (zu : list Z) k, (k <= length zu)%nat ->
  (0 <=? Z.of_nat k) && (Z.of_nat k <=? Z.of_nat (length zu)) = true.
Proof. intros zu k H. apply andb_true_iff. split; apply Z.leb_le; lia. Qed.

Lemma text_t1 : forall zu k, (k <= length zu)%nat ->
  pf_text ps_t1 [AInt (Z.of_nat k); APtr zu; APtr (skipn k zu)] = Some (txt_t1 zu k).
Proof.
  intros zu k H. cbn [ps_t1 pf_text]. rewrite (pps_ok zu k H). cbn [option_map]. rewrite Nat2Z.id.
  unfold txt_t1, tail_lv2. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma text_t2 : forall zu k, (k <= length zu)%nat ->
  pf_text ps_t2 [AInt (Z.of_nat k); APtr zu; APtr (skipn k zu)] = Some (txt_t2 zu k).
Proof.
  intros zu k H. cbn [ps_t2 pf_text]. rewrite (pps_ok zu k H). cbn [option_map]. rewrite Nat2Z.id.
  unfold txt_t2, tail_lv2. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma text_t3 : forall zu k, (k <= length zu)%nat ->
  pf_text ps_t3 [AInt (Z.of_nat k); APtr zu; APtr (skipn k zu)] = Some (txt_t3 zu k).
Proof.
  intros zu k H. cbn [ps_t3 pf_text]. rewrite (pps_ok zu k H). cbn [option_map]. rewrite Nat2Z.id.
  unfold txt_t3, tail_lv2. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma text_t1x : forall zu k, (k <= length zu)%nat ->
  pf_text ps_t1x [AInt (Z.of_nat k); APtr zu; APtr (skipn k zu)] = Some (txt_t1x zu k).
Proof.
  intros zu k H. cbn [ps_t1x pf_text]. rewrite (pps_ok zu k H). cbn [option_map]. rewrite Nat2Z.id.
  unfold txt_t1x, tail_lv2. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma len_whole : forall zu, length (txt_whole zu) = (length zu + 22)%nat.
Proof. intros zu. unfold txt_whole, tail_lv2. cbn [length]. rewrite length_app. cbn [length]. lia. Qed.
Lemma len_wholex : forall zu, length (txt_wholex zu) = (length zu + 23)%nat.
Proof. intros zu. unfold txt_wholex, tail_lv2. cbn [length]. rewrite length_app. cbn [length]. lia. Qed.

Lemma len_split : forall (zu : list Z) k, (k <= length zu)%nat -> (length (firstn k zu) + length (skipn k zu) = length zu)%nat.
Proof. intros zu k H. rewrite length_firstn, length_skipn. lia. Qed.

Lemma len_t1 : forall zu k, (k <= length zu)%nat -> length (txt_t1 zu k) = (length zu + 38)%nat.
Proof. intros zu k H. unfold txt_t1, tail_lv2. rewrite !length_app. cbn [length]. pose proof (len_split zu k H). lia. Qed.
Lemma len_t2 : forall zu k, (k <= length zu)%nat -> length (txt_t2 zu k) = (length zu + 35)%nat.
Proof. intros zu k H. unfold txt_t2, tail_lv2. rewrite !length_app. cbn [length]. pose proof (len_split zu k H). lia. Qed.
Lemma len_t3 : forall zu k, (k <= length zu)%nat -> length (txt_t3 zu k) = (length zu + 36)%nat.
Proof. intros zu k H. unfold txt_t3, tail_lv2. rewrite !length_app. cbn [length]. pose proof (len_split zu k H). lia. Qed.
Lemma len_t1x : forall zu k, (k <= length zu)%nat -> length (txt_t1x zu k) = (length zu + 39)%nat.
Proof. intros zu k H. unfold txt_t1x, tail_lv2. rewrite !length_app. cbn [length]. pose proof (len_split zu k H). lia. Qed.

Lemma nz_app : forall a b : list Z, Forall (fun c => 0 < c < 256) a -> Forall (fun c => 0 < c < 256) b ->
  Forall (fun c => 0 < c < 256) (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. auto. Qed.

Lemma nz_lit : forall l : list Z, forallb (fun c => (0 <? c) && (c <? 256)) l = true -> Forall (fun c => 0 < c < 256) l.
Proof.
  intros l H. rewrite Forall_forall. rewrite forallb_forall in H. intros x Hx. specialize (H x Hx).
  apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma nz_skip : forall (zu : list Z) k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (skipn k zu).
Proof. intros zu k H. rewrite Forall_forall in *. intros x Hx. apply H. rewrite <- (firstn_skipn k zu). apply in_or_app. right. exact Hx. Qed.

Lemma nz_first : forall (zu : list Z) k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (firstn k zu).
Proof. intros zu k H. rewrite Forall_forall in *. intros x Hx. apply H. rewrite <- (firstn_skipn k zu). apply in_or_app. left. exact Hx. Qed.

Ltac nz_solve := unfold txt_whole, txt_wholex, txt_t1, txt_t2, txt_t3, txt_t1x, tail_lv2;
  repeat first [ apply nz_app | apply Forall_cons; [lia|] | apply nz_skip | apply nz_first | assumption
               | apply nz_lit; reflexivity ].

Lemma nz_whole : forall zu, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_whole zu).
Proof. intros zu H. nz_solve. Qed.
Lemma nz_wholex : forall zu, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_wholex zu).
Proof. intros zu H. nz_solve. Qed.
Lemma nz_t1 : forall zu k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_t1 zu k).
Proof. intros zu k H. nz_solve. Qed.
Lemma nz_t2 : forall zu k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_t2 zu k).
Proof. intros zu k H. nz_solve. Qed.
Lemma nz_t3 : forall zu k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_t3 zu k).
Proof. intros zu k H. nz_solve. Qed.
Lemma nz_t1x : forall zu k, Forall (fun c => 0 < c < 256) zu -> Forall (fun c => 0 < c < 256) (txt_t1x zu k).
Proof. intros zu k H. nz_solve. Qed.
