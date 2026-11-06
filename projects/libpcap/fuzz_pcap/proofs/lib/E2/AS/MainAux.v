(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import BootState.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require Import MainExport.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ivs_apart_sep : forall l, ivs_apart l -> ivs_sep l.
Proof.
  induction l as [|[b n] l IH]; intros HA i j p q Hij Hi Hj; [destruct i; discriminate|].
  cbn [ivs_apart] in HA. destruct HA as [HF HA].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as <-. cbn [fst snd].
    exact (proj1 (Forall_forall _ _) HF q (nth_error_In _ _ Hj)).
  - cbn [nth_error] in Hi. exact (IH HA i j p q ltac:(lia) Hi Hj).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Forall_maps_subtract : forall (P : Z -> Z -> Prop) l lo hi,
  ivs_wf l ->
  (forall b e b' e', P b e -> b <= b' -> e' <= e -> P b' e') ->
  Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) l ->
  Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (maps_subtract l lo hi).
Proof.
  intros P l lo hi Hwf Hmono HF. apply Forall_forall. intros q Hq.
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & H1 & H2 & _).
  exact (Hmono _ _ _ _ (proj1 (Forall_forall _ _) HF r Hr) H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aallowed_range : forall shoff V vis bn (p : word),
  In bn vis -> pagedown (zv V (fst bn)) <= bv_unsigned p -> bv_unsigned p + 4096 <= pageup (zv V (fst bn) + zv V (snd bn)) ->
  aallowed (allow_of shoff V vis) p.
Proof.
  intros shoff V vis bn p Hin H1 H2. unfold aallowed, allow_of.
  exists (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))). split; [|cbn [fst snd]; lia].
  apply in_flat_map. exists bn. split; [exact Hin|]. left. reflexivity.
Qed.

Lemma aallowed_shadow : forall shoff V vis bn (p : word),
  In bn vis -> pagedown (shoff + zv V (fst bn) / 8) <= bv_unsigned p ->
  bv_unsigned p + 4096 <= pageup (shoff + (zv V (fst bn) + zv V (snd bn)) / 8) ->
  aallowed (allow_of shoff V vis) p.
Proof.
  intros shoff V vis bn p Hin H1 H2. unfold aallowed, allow_of.
  exists (pagedown (shoff + zv V (fst bn) / 8), pageup (shoff + (zv V (fst bn) + zv V (snd bn)) / 8)). split; [|cbn [fst snd]; lia].
  apply in_flat_map. exists bn. split; [exact Hin|]. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_allowedb_incl : forall (A A' : list (Z * Z)) (p : word),
  Forall (fun iv => exists iv', In iv' A' /\ fst iv' <= fst iv /\ snd iv <= snd iv') A ->
  page_allowedb A p = true -> aallowed A' p.
Proof.
  intros A A' p HF H. unfold page_allowedb in H. apply existsb_exists in H as (iv & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
  destruct (proj1 (Forall_forall _ _) HF iv Hin) as (iv' & Hin' & L1 & L2).
  exists iv'. split; [exact Hin'| lia].
Qed.

(* [comment removed for export] *)
Definition vis_cost (shoff : Z) (V : nat -> Z) (bn : zexp * zexp) : Z :=
  let b := zv V (fst bn) in let n := zv V (snd bn) in
  (pageup (b + n) - pagedown b) + (pageup (shoff + (b + n) / 8) - pagedown (shoff + b / 8)).

Lemma ivz_bytes_app : forall A B, ivz_bytes (A ++ B) = ivz_bytes A + ivz_bytes B.
Proof. induction A as [|iv A IH]; intros B; cbn [ivz_bytes app]; [lia| rewrite IH; lia]. Qed.

Lemma ivz_bytes_allow_of : forall shoff V vis,
  ivz_bytes (allow_of shoff V vis) = fold_right (fun bn acc => vis_cost shoff V bn + acc) 0 vis.
Proof.
  intros shoff V vis. unfold allow_of. induction vis as [|bn vis IH]; [reflexivity|].
  cbn [flat_map fold_right]. rewrite ivz_bytes_app, IH. unfold vis_cost. cbn [ivz_bytes fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_cost_aligned : forall shoff V bn,
  shoff mod 4096 = 0 -> 0 <= zv V (fst bn) -> 0 <= zv V (snd bn) ->
  zv V (fst bn) mod 4096 = 0 -> zv V (snd bn) mod 4096 = 0 ->
  vis_cost shoff V bn <= zv V (snd bn) + zv V (snd bn) / 8 + 8192.
Proof.
  intros shoff V bn Hs Hb Hn Ab An. unfold vis_cost, pagedown, pageup. cbv zeta.
  set (b := zv V (fst bn)) in *. set (n := zv V (snd bn)) in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition psym1 (f : pfact) : list pfact :=
  match f with
  | PDisj a1 n1 a2 n2 => [PDisj a2 n2 a1 n1]
  | PDisjS a1 n1 a2 n2 => [PDisjS a2 n2 a1 n1]
  | _ => []
  end.
Definition psym (l : list pfact) : list pfact := flat_map psym1 l.

Lemma psym_ok : forall V l, Forall (pfact_ok V) l -> Forall (pfact_ok V) (psym l).
Proof.
  intros V l HF. apply Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
  pose proof (proj1 (Forall_forall _ _) HF f Hf) as Hok.
  destruct f; cbn [psym1 In] in Hg; try contradiction; destruct Hg as [<-|[]]; cbn [pfact_ok] in *; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zexp_eqb_refl : forall x, zexp_eqb x x = true.
Proof. induction x; cbn; rewrite ?IHx1, ?IHx2; try reflexivity; [apply Z.eqb_refl | apply Nat.eqb_refl]. Qed.

(* [comment removed for export] *)
Definition led_pair (e1 e2 : lentry) : list pfact :=
  match e1, e2 with
  | LMap b1 n1 _, LMap b2 n2 _ => if zexp_eqb b1 b2 then [] else [PDisj b1 n1 b2 n2]
  | _, _ => []
  end.
Definition all_pairs (l : list lentry) : list pfact := flat_map (fun e1 => flat_map (led_pair e1) l) l.

Definition led_iv (V : nat -> Z) (e : lentry) : word * word :=
  match e with LMap b n _ => (wa (zv V b), wa n) | LFog _ => (wa 0, wa 0) end.
Definition led_ok (V : nat -> Z) (e : lentry) : Prop :=
  match e with LMap b n _ => 0 <= zv V b < 2 ^ 64 /\ 0 <= n < 2 ^ 64 | LFog _ => False end.

Lemma all_pairs_ok : forall V (l : list lentry) (maps : list (word * word)),
  maps = List.map (led_iv V) l -> Forall (led_ok V) l -> ivs_sep maps -> Forall (pfact_ok V) (all_pairs l).
Proof.
  intros V l maps -> HOK HS. apply Forall_forall. intros f Hf.
  apply in_flat_map in Hf as (e1 & H1 & Hf). apply in_flat_map in Hf as (e2 & H2 & Hf).
  pose proof (proj1 (Forall_forall _ _) HOK e1 H1) as O1. pose proof (proj1 (Forall_forall _ _) HOK e2 H2) as O2.
  destruct e1 as [b1 n1 k1|]; [|destruct O1]. destruct e2 as [b2 n2 k2|]; [|destruct O2].
  cbn [led_pair] in Hf. destruct (zexp_eqb b1 b2) eqn:EB; [destruct Hf|]. destruct Hf as [<-|[]].
  cbn [led_ok] in O1, O2. destruct O1 as [OB1 ON1]. destruct O2 as [OB2 ON2].
  apply In_nth_error in H1 as [i Hi]. apply In_nth_error in H2 as [j Hj].
  assert (NE : i <> j).
  { intros ->. rewrite Hi in Hj. injection Hj as -> _ _. rewrite zexp_eqb_refl in EB. discriminate. }
  pose proof (map_nth_error (led_iv V) _ _ Hi) as Mi. pose proof (map_nth_error (led_iv V) _ _ Hj) as Mj. cbn [led_iv] in Mi, Mj.
  assert (U : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (wa z) = z).
  { intros z Hz. unfold wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. }
  cbn [pfact_ok].
  destruct (Nat.lt_ge_cases i j) as [L|L].
  - pose proof (HS i j _ _ L Mi Mj) as D. cbn [fst snd] in D. rewrite !U in D by assumption. exact D.
  - pose proof (HS j i _ _ ltac:(lia) Mj Mi) as D. cbn [fst snd] in D. rewrite !U in D by assumption. tauto.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ivs_apart_sep : forall l, ivs_apart l -> ivs_sep l.
Proof.
  induction l as [|[b n] l IH]; intros HA i j p q Hij Hi Hj; [destruct i; discriminate|].
  cbn [ivs_apart] in HA. destruct HA as [HF HA].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as <-. cbn [fst snd].
    exact (proj1 (Forall_forall _ _) HF q (nth_error_In _ _ Hj)).
  - cbn [nth_error] in Hi. exact (IH HA i j p q ltac:(lia) Hi Hj).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Forall_maps_subtract : forall (P : Z -> Z -> Prop) l lo hi,
  ivs_wf l ->
  (forall b e b' e', P b e -> b <= b' -> e' <= e -> P b' e') ->
  Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) l ->
  Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (maps_subtract l lo hi).
Proof.
  intros P l lo hi Hwf Hmono HF. apply Forall_forall. intros q Hq.
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & H1 & H2 & _).
  exact (Hmono _ _ _ _ (proj1 (Forall_forall _ _) HF r Hr) H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aallowed_range : forall shoff V vis bn (p : word),
  In bn vis -> pagedown (zv V (fst bn)) <= bv_unsigned p -> bv_unsigned p + 4096 <= pageup (zv V (fst bn) + zv V (snd bn)) ->
  aallowed (allow_of shoff V vis) p.
Proof.
  intros shoff V vis bn p Hin H1 H2. unfold aallowed, allow_of.
  exists (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))). split; [|cbn [fst snd]; lia].
  apply in_flat_map. exists bn. split; [exact Hin|]. left. reflexivity.
Qed.

Lemma aallowed_shadow : forall shoff V vis bn (p : word),
  In bn vis -> pagedown (shoff + zv V (fst bn) / 8) <= bv_unsigned p ->
  bv_unsigned p + 4096 <= pageup (shoff + (zv V (fst bn) + zv V (snd bn)) / 8) ->
  aallowed (allow_of shoff V vis) p.
Proof.
  intros shoff V vis bn p Hin H1 H2. unfold aallowed, allow_of.
  exists (pagedown (shoff + zv V (fst bn) / 8), pageup (shoff + (zv V (fst bn) + zv V (snd bn)) / 8)). split; [|cbn [fst snd]; lia].
  apply in_flat_map. exists bn. split; [exact Hin|]. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_allowedb_incl : forall (A A' : list (Z * Z)) (p : word),
  Forall (fun iv => exists iv', In iv' A' /\ fst iv' <= fst iv /\ snd iv <= snd iv') A ->
  page_allowedb A p = true -> aallowed A' p.
Proof.
  intros A A' p HF H. unfold page_allowedb in H. apply existsb_exists in H as (iv & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
  destruct (proj1 (Forall_forall _ _) HF iv Hin) as (iv' & Hin' & L1 & L2).
  exists iv'. split; [exact Hin'| lia].
Qed.

(* [comment removed for export] *)
Definition vis_cost (shoff : Z) (V : nat -> Z) (bn : zexp * zexp) : Z :=
  let b := zv V (fst bn) in let n := zv V (snd bn) in
  (pageup (b + n) - pagedown b) + (pageup (shoff + (b + n) / 8) - pagedown (shoff + b / 8)).

Lemma ivz_bytes_app : forall A B, ivz_bytes (A ++ B) = ivz_bytes A + ivz_bytes B.
Proof. induction A as [|iv A IH]; intros B; cbn [ivz_bytes app]; [lia| rewrite IH; lia]. Qed.

Lemma ivz_bytes_allow_of : forall shoff V vis,
  ivz_bytes (allow_of shoff V vis) = fold_right (fun bn acc => vis_cost shoff V bn + acc) 0 vis.
Proof.
  intros shoff V vis. unfold allow_of. induction vis as [|bn vis IH]; [reflexivity|].
  cbn [flat_map fold_right]. rewrite ivz_bytes_app, IH. unfold vis_cost. cbn [ivz_bytes fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_cost_aligned : forall shoff V bn,
  shoff mod 4096 = 0 -> 0 <= zv V (fst bn) -> 0 <= zv V (snd bn) ->
  zv V (fst bn) mod 4096 = 0 -> zv V (snd bn) mod 4096 = 0 ->
  vis_cost shoff V bn <= zv V (snd bn) + zv V (snd bn) / 8 + 8192.
Proof.
  intros shoff V bn Hs Hb Hn Ab An. unfold vis_cost, pagedown, pageup. cbv zeta.
  set (b := zv V (fst bn)) in *. set (n := zv V (snd bn)) in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition psym1 (f : pfact) : list pfact :=
  match f with
  | PDisj a1 n1 a2 n2 => [PDisj a2 n2 a1 n1]
  | PDisjS a1 n1 a2 n2 => [PDisjS a2 n2 a1 n1]
  | _ => []
  end.
Definition psym (l : list pfact) : list pfact := flat_map psym1 l.

Lemma psym_ok : forall V l, Forall (pfact_ok V) l -> Forall (pfact_ok V) (psym l).
Proof.
  intros V l HF. apply Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
  pose proof (proj1 (Forall_forall _ _) HF f Hf) as Hok.
  destruct f; cbn [psym1 In] in Hg; try contradiction; destruct Hg as [<-|[]]; cbn [pfact_ok] in *; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zexp_eqb_refl : forall x, zexp_eqb x x = true.
Proof. induction x; cbn; rewrite ?IHx1, ?IHx2; try reflexivity; [apply Z.eqb_refl | apply Nat.eqb_refl]. Qed.

(* [comment removed for export] *)
Definition led_pair (e1 e2 : lentry) : list pfact :=
  match e1, e2 with
  | LMap b1 n1 _, LMap b2 n2 _ => if zexp_eqb b1 b2 then [] else [PDisj b1 n1 b2 n2]
  | _, _ => []
  end.
Definition all_pairs (l : list lentry) : list pfact := flat_map (fun e1 => flat_map (led_pair e1) l) l.

Definition led_iv (V : nat -> Z) (e : lentry) : word * word :=
  match e with LMap b n _ => (wa (zv V b), wa n) | LFog _ => (wa 0, wa 0) end.
Definition led_ok (V : nat -> Z) (e : lentry) : Prop :=
  match e with LMap b n _ => 0 <= zv V b < 2 ^ 64 /\ 0 <= n < 2 ^ 64 | LFog _ => False end.

Lemma all_pairs_ok : forall V (l : list lentry) (maps : list (word * word)),
  maps = List.map (led_iv V) l -> Forall (led_ok V) l -> ivs_sep maps -> Forall (pfact_ok V) (all_pairs l).
Proof.
  intros V l maps -> HOK HS. apply Forall_forall. intros f Hf.
  apply in_flat_map in Hf as (e1 & H1 & Hf). apply in_flat_map in Hf as (e2 & H2 & Hf).
  pose proof (proj1 (Forall_forall _ _) HOK e1 H1) as O1. pose proof (proj1 (Forall_forall _ _) HOK e2 H2) as O2.
  destruct e1 as [b1 n1 k1|]; [|destruct O1]. destruct e2 as [b2 n2 k2|]; [|destruct O2].
  cbn [led_pair] in Hf. destruct (zexp_eqb b1 b2) eqn:EB; [destruct Hf|]. destruct Hf as [<-|[]].
  cbn [led_ok] in O1, O2. destruct O1 as [OB1 ON1]. destruct O2 as [OB2 ON2].
  apply In_nth_error in H1 as [i Hi]. apply In_nth_error in H2 as [j Hj].
  assert (NE : i <> j).
  { intros ->. rewrite Hi in Hj. injection Hj as -> _ _. rewrite zexp_eqb_refl in EB. discriminate. }
  pose proof (map_nth_error (led_iv V) _ _ Hi) as Mi. pose proof (map_nth_error (led_iv V) _ _ Hj) as Mj. cbn [led_iv] in Mi, Mj.
  assert (U : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (wa z) = z).
  { intros z Hz. unfold wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. }
  cbn [pfact_ok].
  destruct (Nat.lt_ge_cases i j) as [L|L].
  - pose proof (HS i j _ _ L Mi Mj) as D. cbn [fst snd] in D. rewrite !U in D by assumption. exact D.
  - pose proof (HS j i _ _ ltac:(lia) Mj Mi) as D. cbn [fst snd] in D. rewrite !U in D by assumption. tauto.
Qed.
End TwB.
