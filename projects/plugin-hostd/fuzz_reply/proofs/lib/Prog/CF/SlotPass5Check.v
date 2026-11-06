(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 188 of its 239 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass5A.v, with its module paths and module names changed; 957 of its 1013 lines of code are new or changed and 183 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c relay_remove_b_c SlotInv SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_instance_gone_b_c RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma g5_prefixb : forall P b, prefixb P b = has_prefix (bzs P) (bzs b).
Proof.
  intros P b. unfold prefixb, has_prefix. rewrite bzs_length.
  replace (firstn (length P) (bzs b)) with (bzs (firstn (length P) b)) by (unfold bzs; symmetry; apply firstn_map).
  destruct (list_eqb (bzs (firstn (length P) b)) (bzs P)) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r. apply Nat.leb_le. apply list_eqb_true in E.
  apply (f_equal (@length Z)) in E. rewrite !bzs_length, length_firstn in E. lia.
Qed.

Lemma g5_has_prefix_app : forall pre x y, has_prefix pre x = true -> has_prefix pre (x ++ y) = true.
Proof.
  intros pre x y H. unfold has_prefix in *. apply list_eqb_true in H.
  assert (L : (length pre <= length x)%nat).
  { apply (f_equal (@length Z)) in H. rewrite length_firstn in H. lia. }
  rewrite firstn_app. replace (length pre - length x)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, H. apply list_eqb_refl.
Qed.

Lemma g5_end_ok : forall P x, prefixb P x = true ->
  (Nat.leb 4 (length (x ++ END4)) && list_eqb (bzs (skipn (length (x ++ END4) - 4) (x ++ END4))) (bzs END4) &&
   prefixb P (x ++ END4)) = true /\
  firstn (length (x ++ END4) - 4) (x ++ END4) = x.
Proof.
  intros P x H. destruct (end_line_ok x) as [C1 C2]. rewrite prefixb_nil, andb_true_r in C1.
  rewrite g5_prefixb in H. rewrite (g5_prefixb P (x ++ END4)), bzs_app, (g5_has_prefix_app _ _ _ H), andb_true_r.
  split; assumption.
Qed.

Lemma g5_want_app : forall P a b, want_of P (a ++ b) = (want_of P a + want_of P b)%nat.
Proof.
  intros P a b. induction a as [|r a IH]; [reflexivity|]. cbn [app]. rewrite !want_of_cons, IH.
  destruct (prefixb P (snd r)); reflexivity.
Qed.

Lemma g5_want_drop : forall P rs i, (i < length rs)%nat ->
  want_of P rs = ((if prefixb P (snd (nth i rs (0%Z, []))) then 1 else 0) + want_of P (drop_nth i rs))%nat.
Proof.
  intros P rs i H. unfold drop_nth.
  transitivity (want_of P (firstn i rs ++ nth i rs (0, []) :: skipn (S i) rs));
    [f_equal; exact (split_at rs i (0, []) H)|].
  rewrite !g5_want_app, want_of_cons. destruct (prefixb P (snd (nth i rs (0, [])))); lia.
Qed.

Lemma g5_want_zero : forall P rs, (forall r, In r rs -> prefixb P (snd r) = false) -> want_of P rs = 0%nat.
Proof.
  intros P rs. induction rs as [|r rs IH]; intros H; [reflexivity|].
  rewrite want_of_cons, (H r (or_introl eq_refl)). apply IH. intros r' Hr'. apply H. right. exact Hr'.
Qed.

Lemma g5_bzs_split : forall (a d : list byte) (z : list Z), bzs d = bzs a ++ z -> exists d', d = a ++ d' /\ bzs d' = z.
Proof.
  induction a as [|b a IH]; intros d z H; [exists d; split; [reflexivity | exact H]|].
  destruct d as [|c d]; unfold bzs in H; cbn [map app] in H; [discriminate|]. injection H as H1 H2.
  destruct (IH d z H2) as (d' & -> & H3). exists d'. split; [cbn [app]; f_equal; apply bz_inj; exact H1 | exact H3].
Qed.

Lemma g5_end4_bzs : bzs END4 = [32; 101; 110; 100].
Proof. unfold END4, bzs. cbn [map]. rewrite !bz_lit by lia. reflexivity. Qed.

Lemma g5_end4_nz : ~ In (Z_to_bv 8 0) END4.
Proof.
  unfold END4. cbn [In]. intros X.
  repeat (destruct X as [X | X]; [apply (f_equal bz) in X; rewrite !bz_lit in X by lia; discriminate|]).
  exact X.
Qed.

Lemma g5_ends : forall (P : list byte) (E : list (list Z)) (rs : list (Z * list byte)) (d : list byte) (z : list Z),
  NoDup E -> NoDup (rtexts rs) ->
  (forall y, In y E <-> In y (rtexts rs) /\ has_prefix (bzs P) y = true) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  bzs d = concat (map (fun x => x ++ END5Z) E) ++ z ->
  exists rs' ds, ends_run P rs d (want_of P rs) =
    Some (rs', ds, Z.of_nat (length (concat (map (fun x => x ++ END5Z) E)))).
Proof.
  intros P E. induction E as [|x E IH]; intros rs d z NE NR HS NZ HD.
  - assert (W : want_of P rs = 0%nat).
    { apply g5_want_zero. intros r Hr. destruct (prefixb P (snd r)) eqn:Pr; [|reflexivity]. exfalso.
      apply (proj2 (HS (bzs (snd r)))). split; [|rewrite <- g5_prefixb; exact Pr].
      unfold rtexts. apply (in_map (fun r => bzs (snd r))). exact Hr. }
    rewrite W. exists rs, []. reflexivity.
  - apply NoDup_ListNoDup in NE. inversion NE as [|? ? NX NE']; subst. apply NoDup_ListNoDup in NE'.
    destruct (proj1 (HS x) (or_introl eq_refl)) as [Ix Px].
    destruct (In_nth (rtexts rs) x [] Ix) as (i0 & Li0 & Ni0).
    assert (Li0' : (i0 < length rs)%nat) by (unfold rtexts in Li0; rewrite length_map in Li0; exact Li0).
    rewrite (nth_rtexts rs i0 Li0') in Ni0.
    set (xb := snd (nth i0 rs (0, []))) in *.
    assert (Ixb : In (bzs xb) (rtexts rs)) by (rewrite Ni0; exact Ix).
    destruct (find_text_some xb rs Ixb) as (i & F & Li & Ni).
    assert (NZx : ~ In (Z_to_bv 8 0) xb).
    { rewrite Forall_forall in NZ. apply NZ. apply nth_In. exact Li0'. }
    assert (Pxb : prefixb P xb = true) by (rewrite g5_prefixb, Ni0; exact Px).
    assert (Pi : prefixb P (snd (nth i rs (0, []))) = true) by (rewrite g5_prefixb, Ni; rewrite <- g5_prefixb; exact Pxb).
    assert (HD' : bzs d = bzs ((xb ++ END4) ++ [Z_to_bv 8 0]) ++ (concat (map (fun x => x ++ END5Z) E) ++ z)).
    { rewrite HD. cbn [map concat]. rewrite !bzs_app, g5_end4_bzs, bzs_zero, Ni0. unfold END5Z.
      rewrite <- !app_assoc. reflexivity. }
    destruct (g5_bzs_split _ _ _ HD') as (d' & -> & HD2).
    rewrite <- (app_assoc (xb ++ END4) [Z_to_bv 8 0] d'). cbn [app].
    rewrite (g5_want_drop P rs i Li), Pi. cbn [Nat.add ends_run].
    assert (NZX : ~ In (Z_to_bv 8 0) (xb ++ END4)).
    { rewrite in_app_iff. intros [X | X]; [exact (NZx X) | exact (g5_end4_nz X)]. }
    rewrite (split_nul_app _ _ NZX). cbv beta iota zeta.
    destruct (g5_end_ok P xb Pxb) as [C1 C2]. rewrite C1, C2, F. cbv beta iota zeta.
    assert (LRi : (i < length (rtexts rs))%nat) by (unfold rtexts; rewrite length_map; exact Li).
    assert (NT : nth i (rtexts rs) [] = x) by (rewrite (nth_rtexts rs i Li), Ni; exact Ni0).
    assert (NR' : NoDup (rtexts (drop_nth i rs))).
    { apply NoDup_ListNoDup. rewrite rtexts_drop. pose proof (proj1 (NoDup_ListNoDup _) NR) as NR0.
      rewrite (split_at (rtexts rs) i [] LRi) in NR0. apply NoDup_remove_1 in NR0. exact NR0. }
    assert (HS' : forall y, In y E <-> In y (rtexts (drop_nth i rs)) /\ has_prefix (bzs P) y = true).
    { intros y. rewrite rtexts_drop, (in_drop_split (rtexts rs) i [] y NR LRi), NT. split.
      - intros HY. destruct (proj1 (HS y) (or_intror HY)) as [H1 H2].
        split; [split; [exact H1|] | exact H2]. intros ->. exact (NX HY).
      - intros [[H1 H2] H3]. destruct (proj2 (HS y) (conj H1 H3)) as [HY | HY]; [congruence | exact HY]. }
    assert (NZ' : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (drop_nth i rs)).
    { rewrite (split_at rs i (0, []) Li) in NZ. apply Forall_app in NZ. destruct NZ as [N1 N2].
      inversion N2 as [|? ? _ N3]; subst. unfold drop_nth. apply Forall_app. split; assumption. }
    destruct (IH (drop_nth i rs) d' z NE' NR' HS' NZ' HD2) as (rs' & ds & ER). rewrite ER.
    exists rs', (nth i rs (0, []) :: ds). f_equal. f_equal. f_equal.
    cbn [map concat]. rewrite !length_app. unfold END5Z. change (length END4) with 4%nat.
    assert (LX : length xb = length x) by (rewrite <- Ni0, bzs_length; reflexivity).
    cbn [length]. rewrite LX. lia.
Qed.

Lemma g5_ends_gei : forall (P : list byte) pre (ks : list (list Z)) (H : hlist) (d : list byte) (z : list Z),
  bzs P = pre -> NoDup ks -> NoDup (texts H) -> same_set ks (texts H) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H) ->
  bzs d = concat (map (fun x => x ++ END5Z) (fst (gei pre ks))) ++ z ->
  exists rs' ds, ends_run P (hl_recs H) d (want_of P (hl_recs H)) =
    Some (rs', ds, Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei pre ks)))))).
Proof.
  intros P pre ks H d z HP NK NH SS NZ HD. pose proof (gei_ok pre ks (proj1 (NoDup_ListNoDup _) NK)) as G.
  destruct (gei pre ks) as [E0 H0]. cbn [fst] in HD |- *. destruct G as (NE & _ & _ & SE & _).
  apply (g5_ends P E0 (hl_recs H) d z (proj2 (NoDup_ListNoDup _) NE) NH); [|exact NZ | exact HD].
  intros y. rewrite (SE y), filter_In, (SS y), HP. reflexivity.
Qed.

Lemma g5_digits : forall f x acc, 0 <= x -> Forall (fun z => 48 <= z <= 57) acc ->
  Forall (fun z => 48 <= z <= 57) (pf_digits f x acc) /\ (length (pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc Hx Ha; cbn [pf_digits]; [split; [exact Ha | lia]|].
  destruct (x <? 10) eqn:E.
  - apply Z.ltb_lt in E. split; [constructor; [cbv beta; lia | exact Ha] | cbn [length]; lia].
  - apply Z.ltb_ge in E.
    assert (D : 0 <= x / 10) by (apply Z.div_pos; lia).
    assert (M : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
    destruct (IH (x / 10) ((48 + x mod 10) :: acc) D ltac:(constructor; [cbv beta; lia | exact Ha])) as [F L].
    split; [exact F | cbn [length] in L; lia].
Qed.

Lemma g5_dec : forall v, Forall (fun z => 45 <= z <= 57) (pf_dec v) /\ (length (pf_dec v) <= 12)%nat.
Proof.
  intros v. unfold pf_dec. destruct (v <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (g5_digits 11 (- v) [] ltac:(lia) (Forall_nil _)) as [F L].
    split; [constructor; [cbv beta; lia | refine (Forall_impl _ _ F); intros a Ha; lia] | cbn [length] in *; lia].
  - apply Z.ltb_ge in E. destruct (g5_digits 11 v [] E (Forall_nil _)) as [F L].
    split; [refine (Forall_impl _ _ F); intros a Ha; lia | cbn [length] in *; lia].
Qed.

Lemma g5_pre_ok : forall ID,
  Forall (fun z => 0 < z < 256) (instance_prefix ID) /\ (length (instance_prefix ID) <= 27)%nat.
Proof.
  intros ID. destruct (g5_dec ID) as [F L]. unfold instance_prefix. split.
  - apply Forall_app. split; [unfold K_GESTURE; repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil|].
    apply Forall_app. split; [repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil|].
    apply Forall_app. split; [refine (Forall_impl _ _ F); intros a Ha; lia|].
    repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.
  - rewrite !length_app. unfold K_GESTURE. cbn [length]. lia.
Qed.

Lemma g5_pre_bytes : forall ID,
  bzs (pf_bytes (instance_prefix ID)) = instance_prefix ID /\ ~ In (Z_to_bv 8 0) (pf_bytes (instance_prefix ID)) /\
  (length (pf_bytes (instance_prefix ID)) <= 27)%nat.
Proof.
  intros ID. destruct (g5_pre_ok ID) as [F L]. unfold pf_bytes.
  split; [apply bzs_lits; unfold zrange; refine (Forall_impl _ _ F); intros a Ha; lia|].
  split; [|rewrite length_map; exact L].
  intros X. apply in_map_iff in X. destruct X as (z & Ez & Hz). rewrite Forall_forall in F.
  specialize (F z Hz). apply (f_equal bz) in Ez. rewrite !bz_lit in Ez by lia. lia.
Qed.

Lemma g5_prefix : forall segs mem SP ID T (rest : list byte),
  T = instance_prefix ID ->
  bytes_at segs mem (SP + 40) (pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])) ->
  bytes_at segs mem (SP + 40 + Z.of_nat (length (firstn (Z.to_nat (48 - 1)) T)) + 1) rest ->
  Z.of_nat (length (firstn (Z.to_nat (48 - 1)) T)) + 1 + Z.of_nat (length rest) = 48 ->
  SP mod 8 = 0 -> 0 <= SP -> SP + 88 <= 2 ^ 63 ->
  let P := pf_bytes (instance_prefix ID) in
  let PLEN := Z.of_nat (length P + 1 + length rest) in
  bytes_at segs mem (SP + 40) (P ++ Z_to_bv 8 0 :: rest) /\ ~ In (Z_to_bv 8 0) P /\ bzs P = instance_prefix ID /\
  (- (SP + 40 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length rest) /\
  SP <= SP + 40 /\ SP + 40 + PLEN <= 2 ^ 63 /\
  (SP + 32) mod 8 = 0 /\ SP <= SP + 32 /\ SP + 32 + 8 <= 2 ^ 63 /\
  (SP + 32 + 8 <= SP + 40 \/ SP + 40 + PLEN <= SP + 32).
Proof.
  intros segs mem SP ID T rest -> B1 B2 L48 A8 S0 S63. cbv zeta.
  destruct (g5_pre_ok ID) as [_ L27]. destruct (g5_pre_bytes ID) as (BZ & NZ & _).
  change (Z.to_nat (48 - 1)) with 47%nat in B1, B2, L48.
  rewrite firstn_all2 in B1, B2, L48 by lia.
  unfold pf_bytes in B1. rewrite map_app in B1. cbn [map] in B1. fold (pf_bytes (instance_prefix ID)) in B1.
  assert (LP : length (pf_bytes (instance_prefix ID)) = length (instance_prefix ID)) by apply length_map.
  rewrite LP. split.
  - change (Z_to_bv 8 0 :: rest) with ([Z_to_bv 8 0] ++ rest). rewrite app_assoc. apply bytes_at_app.
    split; [exact B1|].
    replace (SP + 40 + Z.of_nat (length (pf_bytes (instance_prefix ID) ++ [Z_to_bv 8 0])))
      with (SP + 40 + Z.of_nat (length (instance_prefix ID)) + 1); [exact B2|].
    rewrite length_app, LP. cbn [length]. lia.
  - split; [exact NZ|]. split; [exact BZ|].
    pose proof (Z.mod_pos_bound (- (SP + 40 + Z.of_nat (length (instance_prefix ID)) + 1)) 8 ltac:(lia)).
    repeat split; lia.
Qed.

Lemma g5_skipn_cons : forall {X} (l : list X) j d, (j < length l)%nat -> skipn j l = nth j l d :: skipn (S j) l.
Proof.
  intros X l. induction l as [|a l IH]; intros [|j] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma g5_firstn_S : forall {X} (l : list X) j d, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros X l. induction l as [|a l IH]; intros [|j] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma g5_concat_split : forall (L : list (list Z)) j, concat L = concat (firstn j L) ++ concat (skipn j L).
Proof. intros L j. rewrite <- concat_app, firstn_skipn. reflexivity. Qed.

Lemma g5_nth_le : forall (L : list (list Z)) j, (j < length L)%nat ->
  (length (concat (firstn j L)) + length (nth j L []) <= length (concat L))%nat.
Proof.
  intros L j H. rewrite (g5_concat_split L j), (g5_skipn_cons L j [] H), length_app. cbn [concat].
  rewrite length_app. lia.
Qed.

Lemma g5_skip_at : forall segsz j (LB : list byte), (j < length segsz)%nat -> bzs LB = concat segsz ->
  bzs (skipn (length (concat (firstn j segsz))) LB) = nth j segsz [] ++ concat (skipn (S j) segsz).
Proof.
  intros segsz j LB H HB. unfold bzs. rewrite <- skipn_map. fold (bzs LB). rewrite HB.
  rewrite (g5_concat_split segsz j), skipn_len_app, (g5_skipn_cons segsz j [] H). reflexivity.
Qed.

Lemma g5_skip_in : forall segsz j (LB : list byte) (a b : list Z) (y : nat),
  (j < length segsz)%nat -> bzs LB = concat segsz -> nth j segsz [] = a ++ b -> length a = y ->
  bzs (skipn (Z.to_nat (Z.of_nat (length (concat (firstn j segsz))) + Z.of_nat y)) LB) =
  b ++ concat (skipn (S j) segsz).
Proof.
  intros segsz j LB a b y H HB Hs Hy. rewrite <- Nat2Z.inj_add, Nat2Z.id.
  replace (length (concat (firstn j segsz)) + y)%nat with (y + length (concat (firstn j segsz)))%nat by lia.
  rewrite <- skipn_skipn. unfold bzs at 1. rewrite <- skipn_map. fold (bzs (skipn (length (concat (firstn j segsz))) LB)).
  rewrite (g5_skip_at segsz j LB H HB), Hs, <- app_assoc, <- Hy. apply skipn_len_app.
Qed.

Definition g5_at (gn : Z) (segsz : list (list Z)) (j : nat) : Z :=
  if gn =? 0 then Z.of_nat (length (concat (firstn j segsz))) else 0.

Lemma g5_at_le : forall gn segsz j,
  0 <= g5_at gn segsz j <= (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0).
Proof.
  intros gn segsz j. unfold g5_at. destruct (gn =? 0); [|lia].
  rewrite (g5_concat_split segsz j). rewrite length_app. lia.
Qed.

Lemma g5_at_step : forall gn segsz j, (j < length segsz)%nat ->
  g5_at gn segsz (S j) = g5_at gn segsz j + (if gn =? 0 then Z.of_nat (length (nth j segsz [])) else 0).
Proof.
  intros gn segsz j H. unfold g5_at. destruct (gn =? 0); [|reflexivity].
  rewrite (g5_firstn_S segsz j [] H), concat_app, length_app. cbn [concat]. rewrite app_nil_r. lia.
Qed.

Lemma g5_at_all : forall gn segsz,
  g5_at gn segsz (length segsz) = if gn =? 0 then Z.of_nat (length (concat segsz)) else 0.
Proof. intros gn segsz. unfold g5_at. rewrite firstn_all. reflexivity. Qed.

Definition g5_segs (pre : list Z) (es : list rentry) (hs : list (hsrc * nat)) (kss : list (list (list Z)))
    : list (list Z) :=
  map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj)) (nth i kss []))
      (seq 0 (length es)).

Definition g5_src (e : rentry) (h h' : hsrc) : hsrc := if re_eof e =? 0 then h' else h.

Lemma g5_segs_len : forall pre es hs kss, length (g5_segs pre es hs kss) = length es.
Proof. intros pre es hs kss. unfold g5_segs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma g5_segs_nth : forall pre es hs kss j, (j < length es)%nat ->
  nth j (g5_segs pre es hs kss) [] =
  gone_segment pre (entry_lines (nth j es no_entry) (nth j hs no_hj)) (nth j kss []).
Proof.
  intros pre es hs kss j H. unfold g5_segs.
  set (f := fun i : nat => gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj)) (nth i kss [])).
  rewrite (nth_indep (map f (seq 0 (length es))) [] (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma g5_exp : forall (e : rentry) (hj : hsrc * nat) (h' : hsrc),
  hl_recs (hs_expected (fst hj)) = [] ->
  (re_eof e = 0 -> map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected (fst hj))) ++
     map (map (Z_to_bv 8)) (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj))))) ->
  map snd (hl_recs (hs_expected (g5_src e (fst hj) h'))) = map (map (Z_to_bv 8)) (entry_lines e hj) /\
  Forall zrange (entry_lines e hj).
Proof.
  intros e hj h' HE HM. unfold g5_src, entry_lines. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
  - rewrite (HM E0), HE. split; [reflexivity | apply dc_lines_range].
  - rewrite HE. split; [reflexivity | constructor].
Qed.

Lemma g5_bstream : forall (E : hlist) Ls, map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  bzs (bstream E) = with_nul Ls /\ length (bstream E) = length (with_nul Ls).
Proof.
  intros E Ls HM HR. pose proof (bstream_bzs E Ls HM HR) as BE. split; [exact BE|].
  rewrite <- bzs_length, BE. reflexivity.
Qed.

Lemma g5_tot0 : forall gn cl br dd (live : bool) (segsz : list (list Z)), (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (concat segsz))) ->
  (live = true -> gn = 0 /\ length (concat segsz) <> 0%nat) /\
  (live = false -> gn = 0 -> length (concat segsz) = 0%nat).
Proof.
  intros gn cl br dd live segsz G0 G1 G2 HL.
  pose proof (dc_live gn cl br dd (Z.of_nat (length (concat segsz))) G0 G1 G2) as LV. rewrite <- HL in LV.
  split.
  - intros ->. symmetry in LV. apply andb_true_iff in LV as [L1 L2]. apply Z.eqb_eq in L1.
    apply negb_true_iff, Z.eqb_neq in L2. split; [exact L1 | lia].
  - intros -> ->. rewrite Z.eqb_refl, andb_true_l in LV.
    destruct (Z.of_nat (length (concat segsz)) =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | discriminate].
Qed.

Lemma g5_seg_nil : forall segsz j pre Ls ks, length (concat segsz) = 0%nat -> (j < length segsz)%nat ->
  nth j segsz [] = gone_segment pre Ls ks ->
  with_nul Ls = [] /\ concat (map (fun x => x ++ END5Z) (fst (gei pre ks))) = [] /\ concat (skipn (S j) segsz) = [].
Proof.
  intros segsz j pre Ls ks T0 HJ HS. pose proof (g5_nth_le segsz j HJ) as NL. rewrite HS in NL.
  unfold gone_segment in NL. rewrite length_app in NL.
  pose proof T0 as T1. rewrite (g5_concat_split segsz (S j)), length_app in T1.
  split; [apply length_zero_iff_nil; lia|]. split; apply length_zero_iff_nil; lia.
Qed.

Lemma g5_stream : forall gn cl br dd (live : bool) (segsz : list (list Z)) (LB ob : list byte) (nout' : word) j pre Ls ks
    (E : hlist),
  (gn = 0 \/ gn = 1) -> (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (concat segsz))) ->
  bzs LB = concat segsz -> ob = (if live then LB else []) ->
  bv_unsigned nout' = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  (j < length segsz)%nat -> nth j segsz [] = gone_segment pre Ls ks ->
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  0 <= g5_at gn segsz j <= bv_unsigned nout' /\
  (gn = 0 -> exists rest, skipn (Z.to_nat (g5_at gn segsz j)) ob = bstream E ++ rest).
Proof.
  intros gn cl br dd live segsz LB ob nout' j pre Ls ks E G0 G1 G2 HL HB -> HN HJ HS HM HR.
  rewrite HN. split; [apply g5_at_le|]. intros Hg.
  destruct (g5_bstream E Ls HM HR) as [BE LBE].
  destruct (g5_tot0 gn cl br dd live segsz G0 G1 G2 HL) as [T1 T2].
  subst gn. unfold g5_at. rewrite Z.eqb_refl, Nat2Z.id.
  destruct live.
  - assert (X : bzs (skipn (length (concat (firstn j segsz))) LB) =
                bzs (bstream E) ++ (concat (map (fun x => x ++ END5Z) (fst (gei pre ks))) ++ concat (skipn (S j) segsz))).
    { rewrite (g5_skip_at segsz j LB HJ HB), HS, BE. unfold gone_segment. rewrite <- app_assoc. reflexivity. }
    destruct (g5_bzs_split _ _ _ X) as (d' & E1 & _). exists d'. exact E1.
  - destruct (g5_seg_nil segsz j pre Ls ks (T2 eq_refl eq_refl) HJ HS) as (W0 & _ & _).
    assert (B0 : bstream E = []) by (apply length_zero_iff_nil; rewrite LBE, W0; reflexivity).
    rewrite B0, skipn_nil. exists []. reflexivity.
Qed.

Lemma g5_ends_pre : forall gn cl br dd (live : bool) (segsz : list (list Z)) (LB ob : list byte) (nout' : word) j
    (P : list byte) pre Ls ks
    (E H : hlist),
  (gn = 0 \/ gn = 1) -> (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (concat segsz))) ->
  bzs LB = concat segsz -> ob = (if live then LB else []) ->
  bv_unsigned nout' = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  (j < length segsz)%nat -> nth j segsz [] = gone_segment pre Ls ks ->
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  bzs P = pre -> NoDup ks -> NoDup (texts H) -> same_set ks (texts H) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H) ->
  0 <= (if gn =? 0 then g5_at gn segsz j + Z.of_nat (length (bstream E)) else g5_at gn segsz j) <= bv_unsigned nout' /\
  (gn = 0 -> exists rs' ds,
     ends_run P (hl_recs H)
       (skipn (Z.to_nat (if gn =? 0 then g5_at gn segsz j + Z.of_nat (length (bstream E)) else g5_at gn segsz j)) ob)
       (want_of P (hl_recs H)) =
     Some (rs', ds, Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei pre ks))))))).
Proof.
  intros gn cl br dd live segsz LB ob nout' j P pre Ls ks E H G0 G1 G2 HL HB -> HN HJ HS HM HR HP NK NH SS NZ.
  destruct (g5_bstream E Ls HM HR) as [BE LBE].
  destruct (g5_tot0 gn cl br dd live segsz G0 G1 G2 HL) as [T1 T2].
  rewrite HN. destruct (Z.eqb_spec gn 0) as [Hg|Hg].
  - subst gn. unfold g5_at. rewrite Z.eqb_refl.
    pose proof (g5_nth_le segsz j HJ) as NL. rewrite HS in NL. unfold gone_segment in NL. rewrite length_app in NL.
    split; [lia|]. intros _.
    destruct live.
    + assert (X : bzs (skipn (Z.to_nat (Z.of_nat (length (concat (firstn j segsz))) + Z.of_nat (length (bstream E)))) LB) =
                  concat (map (fun x => x ++ END5Z) (fst (gei pre ks))) ++ concat (skipn (S j) segsz)).
      { apply (g5_skip_in segsz j LB (with_nul Ls)); [exact HJ | exact HB | exact HS | symmetry; exact LBE]. }
      exact (g5_ends_gei P pre ks H _ _ HP NK NH SS NZ X).
    + destruct (g5_seg_nil segsz j pre Ls ks (T2 eq_refl eq_refl) HJ HS) as (_ & G5 & _).
      rewrite skipn_nil. apply (g5_ends_gei P pre ks H [] [] HP NK NH SS NZ). rewrite G5. reflexivity.
  - unfold g5_at. rewrite (proj2 (Z.eqb_neq gn 0) Hg). split; [lia|]. intros X. contradiction.
Qed.

Lemma g5_step : forall gn cl br dd (live : bool) (segsz : list (list Z)) (LB ob : list byte) (nout' : word) j
    (P : list byte) pre Ls ks
    (E H H' : hlist) (ds : list (Z * list byte)) (c : Z),
  (gn = 0 \/ gn = 1) -> (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (concat segsz))) ->
  bzs LB = concat segsz -> ob = (if live then LB else []) ->
  bv_unsigned nout' = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  (j < length segsz)%nat -> nth j segsz [] = gone_segment pre Ls ks ->
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  bzs P = pre -> NoDup ks -> NoDup (texts H) -> same_set ks (texts H) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H) ->
  ((gn <> 0 /\ hl_recs H' = filter (fun r => negb (prefixb P (snd r))) (hl_recs H) /\
    ds = filter (fun r => prefixb P (snd r)) (hl_recs H) /\ c = 0) \/
   (gn = 0 /\ ends_run P (hl_recs H)
      (skipn (Z.to_nat (if gn =? 0 then g5_at gn segsz j + Z.of_nat (length (bstream E)) else g5_at gn segsz j)) ob)
      (want_of P (hl_recs H)) = Some (hl_recs H', ds, c))) ->
  (if gn =? 0 then g5_at gn segsz j + Z.of_nat (length (bstream E)) else g5_at gn segsz j) + c = g5_at gn segsz (S j).
Proof.
  intros gn cl br dd live segsz LB ob nout' j P pre Ls ks E H H' ds c G0 G1 G2 HL HB HO HN HJ HS HM HR HP NK NH SS NZ HC.
  destruct HC as [(Hg & _ & _ & ->) | (Hg & ER)].
  - unfold g5_at. rewrite (proj2 (Z.eqb_neq gn 0) Hg). lia.
  - destruct (g5_ends_pre gn cl br dd live segsz LB ob nout' j P pre Ls ks E H G0 G1 G2 HL HB HO HN HJ HS HM HR HP NK NH SS NZ)
      as [_ X]. destruct (X Hg) as (rs' & ds' & ER'). rewrite ER in ER'. injection ER' as _ _ ->.
    subst gn. rewrite (g5_at_step 0 segsz j HJ), Z.eqb_refl, HS. destruct (g5_bstream E Ls HM HR) as [_ LBE].
    unfold gone_segment. rewrite LBE, length_app. lia.
Qed.

Lemma g5_done : forall gn (segsz : list (list Z)) (nout' : word),
  nout' = Z_to_bv 64 (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  nout' = Z_to_bv 64 (g5_at gn segsz (length segsz)) /\ (length segsz = 0%nat -> nout' = Z_to_bv 64 0).
Proof.
  intros gn segsz nout' ->. rewrite g5_at_all. split; [reflexivity|]. intros L0.
  destruct segsz as [|s segsz]; [|discriminate]. destruct (gn =? 0); reflexivity.
Qed.

Lemma g5_held_set : forall ks K (H0 H2 E : hlist) Ls,
  same_set ks (upds (keys_texts K) Ls) -> same_set (keys_texts K) (texts H0) ->
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  texts H2 = upds (texts H0) (texts E) -> same_set ks (texts H2).
Proof.
  intros ks K H0 H2 E Ls S1 S2 HM HR HT. rewrite HT, (texts_lines E Ls HM HR).
  eapply same_set_trans; [exact S1|]. apply upds_same_set. exact S2.
Qed.

Lemma g5_filter_len : forall {X} (f : X -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros X f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

Lemma g5_upd_count : forall G l, (length (upd G l) <= length G + (if is_begin l then 1 else 0))%nat.
Proof.
  intros G l. unfold upd, is_begin. destruct (gesture l) as [[[|] x]|].
  - destruct (existsb (list_eqb x) G); [lia|]. rewrite length_app. cbn [length]. lia.
  - pose proof (g5_filter_len (fun y => negb (list_eqb x y)) G). lia.
  - lia.
Qed.

Lemma g5_upds_count : forall ls G, (length (upds G ls) <= length G + count_begin ls)%nat.
Proof.
  induction ls as [|l ls IH]; intros G; [cbn; lia|].
  unfold upds in *. cbn [fold_left]. rewrite count_begin_cons.
  pose proof (IH (upd G l)) as I1. pose proof (g5_upd_count G l) as I2. destruct (is_begin l); lia.
Qed.

Lemma g5_held_n : forall (H H2 E : hlist), texts H2 = upds (texts H) (texts E) ->
  hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 22 -> hl_n H2 < 2 ^ 26.
Proof.
  intros H H2 E HT HB. pose proof (g5_upds_count (texts E) (texts H)) as C. rewrite <- HT in C.
  unfold texts, hl_n in *. rewrite !length_map in C. lia.
Qed.

Lemma g5_forall2_nth : forall {X Y} (R : X -> Y -> Prop) l1 l2 dx dy, Forall2 R l1 l2 ->
  forall j, (j < length l1)%nat -> R (nth j l1 dx) (nth j l2 dy).
Proof.
  intros X Y R l1 l2 dx dy H. induction H as [|x y l1 l2 Hxy H IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [exact Hxy|]. cbn [nth]. apply IH. lia.
Qed.

Lemma g5_in_combine : forall {X Y} (l1 : list X) (l2 : list Y) j dx dy, length l2 = length l1 -> (j < length l1)%nat ->
  In (nth j l1 dx, nth j l2 dy) (combine l1 l2).
Proof.
  intros X Y l1 l2 j dx dy HL Hj. rewrite <- combine_nth by (symmetry; exact HL). apply nth_In.
  rewrite length_combine, HL. lia.
Qed.

Lemma g5_nd_app : forall {X} (a b : list X) x, List.NoDup (a ++ b) -> In x a -> In x b -> False.
Proof.
  intros X a. induction a as [|y a IH]; intros b x ND Ha Hb; [destruct Ha|].
  cbn [app] in ND. inversion ND as [|? ? N1 N2]; subst. destruct Ha as [<-|Ha].
  - apply N1. apply in_or_app. right. exact Hb.
  - exact (IH b x N2 Ha Hb).
Qed.

Lemma g5_in_concat_nth : forall {X Y} (g : X -> list Y) (l : list X) d k x, (k < length l)%nat ->
  In x (g (nth k l d)) -> In x (concat (map g l)).
Proof.
  intros X Y g l d k x Hk Hx. apply in_concat. exists (g (nth k l d)). split; [|exact Hx].
  apply in_map. apply nth_In. exact Hk.
Qed.

Lemma g5_concat_nodup : forall {X Y} (g : X -> list Y) (l : list X) d j k x,
  List.NoDup (concat (map g l)) -> (j < length l)%nat -> (k < length l)%nat -> j <> k ->
  In x (g (nth j l d)) -> In x (g (nth k l d)) -> False.
Proof.
  intros X Y g l d. induction l as [|a l IH]; intros j k x ND Hj Hk Hne Xj Xk; cbn [length] in Hj; [lia|].
  cbn [map concat] in ND. cbn [length] in Hk.
  destruct j as [|j]; destruct k as [|k]; cbn [nth] in Xj, Xk; [lia| | |].
  - apply (g5_nd_app _ _ x ND Xj). exact (g5_in_concat_nth g l d k x ltac:(lia) Xk).
  - apply (g5_nd_app _ _ x ND Xk). exact (g5_in_concat_nth g l d j x ltac:(lia) Xj).
  - apply NoDup_app_remove_l in ND. exact (IH j k x ND ltac:(lia) ltac:(lia) ltac:(lia) Xj Xk).
Qed.

Lemma g5_find_lt : forall y rs i, find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [find_text] in H; [discriminate|].
  destruct (list_eqb (bzs (snd r)) (bzs y)); [injection H as <-; cbn [length]; lia|].
  destruct (find_text y rs) as [i'|] eqn:F; cbn [option_map] in H; [|discriminate].
  injection H as <-. specialize (IH i' eq_refl). cbn [length]. lia.
Qed.

Lemma g5_firstn_incl : forall {X} n (l : list X), incl (firstn n l) l.
Proof.
  intros X n. induction n as [|n IH]; intros [|a l] x Hx; cbn [firstn In] in Hx; try contradiction.
  destruct Hx as [<-|Hx]; [left; reflexivity | right; exact (IH l x Hx)].
Qed.

Lemma g5_skipn_incl : forall {X} n (l : list X), incl (skipn n l) l.
Proof.
  intros X n. induction n as [|n IH]; intros [|a l] x Hx; cbn [skipn In] in Hx; try contradiction;
    [exact Hx | right; exact (IH l x Hx)].
Qed.

Lemma g5_drop_incl : forall i (rs : list (Z * list byte)), incl (drop_nth i rs) rs.
Proof.
  intros i rs x Hx. unfold drop_nth in Hx. apply in_app_or in Hx as [Hx|Hx];
    [exact (g5_firstn_incl i rs x Hx) | exact (g5_skipn_incl (S i) rs x Hx)].
Qed.

Lemma g5_ends_incl : forall P w rs d rs' ds c, ends_run P rs d w = Some (rs', ds, c) -> incl ds rs.
Proof.
  intros P w. induction w as [|w IH]; intros rs d rs' ds c H; cbn [ends_run] in H.
  - injection H as _ <- _. intros x [].
  - destruct (split_nul d) as [[l d']|]; [|discriminate]. cbv zeta in H.
    destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4) l)) (bzs END4) && prefixb P l);
      [|discriminate].
    destruct (find_text (firstn (length l - 4) l) rs) as [i|] eqn:F; [|discriminate].
    destruct (ends_run P (drop_nth i rs) d' w) as [[[rs1 ds1] c1]|] eqn:ER; [|discriminate].
    injection H as _ <- _. intros x [<-|Hx].
    + apply nth_In. exact (g5_find_lt _ _ _ F).
    + apply (g5_drop_incl i rs). exact (IH _ _ _ _ _ ER x Hx).
Qed.

Lemma g5_sfilter_incl : forall (f : Z * list byte -> bool) (l : list (Z * list byte)), incl (filter f l) l.
Proof.
  intros f l. induction l as [|a l IH]; intros x Hx; [exact Hx|]. cbn in Hx.
  repeat match type of Hx with context [if ?b then _ else _] => destruct b end;
    [destruct Hx as [<-|Hx]; [left; reflexivity | right; exact (IH x Hx)] | right; exact (IH x Hx)].
Qed.

Lemma g5_ds_incl : forall gn P (H H' : hlist) (ds : list (Z * list byte)) c d w,
  ((gn <> 0 /\ hl_recs H' = filter (fun r => negb (prefixb P (snd r))) (hl_recs H) /\
    ds = filter (fun r => prefixb P (snd r)) (hl_recs H) /\ c = 0) \/
   (gn = 0 /\ ends_run P (hl_recs H) d w = Some (hl_recs H', ds, c))) ->
  incl ds (hl_recs H).
Proof.
  intros gn P H H' ds c d w [(_ & _ & -> & _)|(_ & ER)].
  - apply g5_sfilter_incl.
  - exact (g5_ends_incl P w _ _ _ _ _ ER).
Qed.

Lemma g5_hit : forall fd es, op5_hit fd es <> 0 ->
  exists k, (k < length es)%nat /\ re_fd (nth k es no_entry) = fd /\ re_eof (nth k es no_entry) = 0.
Proof.
  intros fd es. induction es as [|e es IH]; intros H; cbn [op5_hit] in H; [lia|].
  destruct (Z.eqb_spec (re_fd e) fd) as [E1|E1].
  - exists 0%nat. cbn [length nth]. split; [lia|]. split; [exact E1|].
    destruct (Z.eqb_spec (re_eof e) 0) as [E2|E2]; [exact E2 | lia].
  - destruct (IH H) as (k & Hk & K1 & K2). exists (S k). cbn [length nth]. split; [lia|]. split; assumption.
Qed.

Lemma g5_nodup_nth : forall {X Y} (f : X -> Y) (l : list X) d i i', NoDup (map f l) ->
  (i < length l)%nat -> (i' < length l)%nat -> f (nth i l d) = f (nth i' l d) -> i = i'.
Proof.
  intros X Y f l d i i' H Hi Hi' E. apply NoDup_ListNoDup in H.
  assert (L : length (map f l) = length l) by apply length_map.
  apply (proj1 (NoDup_nth (map f l) (f d)) H i i'); [lia | lia | rewrite !map_nth; exact E].
Qed.

Definition g5_w (l : list (list Z)) : Z := Z.of_nat (length (concat (map (fun x => x ++ END5Z) l))).

Lemma g5_w_cons : forall x l, g5_w (x :: l) = Z.of_nat (length x) + 5 + g5_w l.
Proof. intros x l. unfold g5_w. cbn [map concat]. rewrite !length_app. change (length END5Z) with 5%nat. lia. Qed.

Lemma g5_w_app : forall a b, g5_w (a ++ b) = g5_w a + g5_w b.
Proof. intros a b. unfold g5_w. rewrite map_app, concat_app, length_app. lia. Qed.

Lemma g5_w_nonneg : forall l, 0 <= g5_w l.
Proof. intros l. unfold g5_w. lia. Qed.

Lemma g5_w_perm : forall a b, Permutation a b -> g5_w a = g5_w b.
Proof. intros a b P. induction P; rewrite ?g5_w_cons; lia. Qed.

Lemma g5_w_remove_mono : forall x b, g5_w (remove (list_eq_dec Z.eq_dec) x b) <= g5_w b.
Proof.
  intros x b. induction b as [|y b IH]; [cbn [remove]; lia|]. cbn [remove].
  destruct (list_eq_dec Z.eq_dec x y); rewrite ?g5_w_cons; lia.
Qed.

Lemma g5_w_remove : forall x b, In x b -> Z.of_nat (length x) + 5 + g5_w (remove (list_eq_dec Z.eq_dec) x b) <= g5_w b.
Proof.
  intros x b. induction b as [|y b IH]; intros H; [destruct H|]. cbn [remove].
  destruct (list_eq_dec Z.eq_dec x y) as [<-|Ne].
  - rewrite g5_w_cons. pose proof (g5_w_remove_mono x b). lia.
  - destruct H as [H|H]; [congruence|]. rewrite !g5_w_cons. pose proof (IH H). lia.
Qed.

Lemma g5_w_incl : forall a b, List.NoDup a -> incl a b -> g5_w a <= g5_w b.
Proof.
  induction a as [|x a IH]; intros b ND HI; [change (g5_w []) with 0; apply g5_w_nonneg|].
  inversion ND as [|? ? NX ND']; subst.
  assert (Xb : In x b) by (apply HI; left; reflexivity).
  assert (HI' : incl a (remove (list_eq_dec Z.eq_dec) x b)).
  { intros y Hy. apply in_in_remove; [intros ->; exact (NX Hy) | apply HI; right; exact Hy]. }
  pose proof (IH _ ND' HI') as I1. pose proof (g5_w_remove x b Xb) as I2. rewrite g5_w_cons. lia.
Qed.

Definition g5_bk (l : list Z) : list (list Z) :=
  match gesture l with Some (GBegin, x) => [x] | _ => [] end.

Fixpoint g5_bks (ls : list (list Z)) : list (list Z) :=
  match ls with [] => [] | l :: ls' => g5_bk l ++ g5_bks ls' end.

Lemma g5_upd_incl : forall G l, incl (upd G l) (G ++ g5_bk l).
Proof.
  intros G l y Hy. unfold upd, g5_bk in *. destruct (gesture l) as [[[|] x]|].
  - apply upd_in_begin in Hy. apply in_or_app. destruct Hy as [Hy| ->]; [left; exact Hy | right; left; reflexivity].
  - apply upd_in_end in Hy. apply in_or_app. left. exact (proj1 Hy).
  - rewrite app_nil_r. exact Hy.
Qed.

Lemma g5_upds_incl : forall ls G, incl (upds G ls) (G ++ g5_bks ls).
Proof.
  induction ls as [|l ls IH]; intros G y Hy; unfold upds in *; cbn [fold_left g5_bks] in *.
  - rewrite app_nil_r. exact Hy.
  - apply IH in Hy. apply in_app_or in Hy as [Hy|Hy].
    + apply g5_upd_incl in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
        [left; exact Hy | right; apply in_or_app; left; exact Hy].
    + apply in_or_app. right. apply in_or_app. right. exact Hy.
Qed.

Lemma g5_bk_w : forall l, g5_w (g5_bk l) <= Z.of_nat (length l) + 1.
Proof.
  intros l. unfold g5_bk, gesture. cbv zeta.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l));
    [|change (g5_w []) with 0; lia].
  destruct (last_space_from 0 l) as [j|]; [|change (g5_w []) with 0; lia].
  destruct (Nat.ltb 13 j); [|change (g5_w []) with 0; lia].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:EB.
  - apply list_eqb_true in EB. rewrite g5_w_cons. change (g5_w []) with 0.
    assert (LS : length (skipn (S j) l) = 5%nat) by (rewrite EB; reflexivity). rewrite length_skipn in LS.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); change (g5_w []) with 0; lia.
Qed.

Lemma g5_bks_w : forall ls, g5_w (g5_bks ls) <= Z.of_nat (length (with_nul ls)).
Proof.
  induction ls as [|l ls IH]; [change (g5_w (g5_bks [])) with 0; cbn; lia|].
  cbn [g5_bks]. rewrite g5_w_app, with_nul_cons_len. pose proof (g5_bk_w l). lia.
Qed.

Lemma g5_seg_le : forall pre (ks : list (list Z)) K Ls,
  NoDup ks -> same_set ks (upds (keys_texts K) Ls) ->
  Z.of_nat (length (gone_segment pre Ls ks)) <= keys_total K + 2 * Z.of_nat (length (with_nul Ls)).
Proof.
  intros pre ks K Ls ND SS. unfold gone_segment. rewrite length_app, Nat2Z.inj_add.
  change (Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei pre ks)))))) with (g5_w (fst (gei pre ks))).
  apply NoDup_ListNoDup in ND.
  pose proof (gei_ok pre ks ND) as G. destruct (gei pre ks) as [E0 H0]. destruct G as (_ & _ & PE & _). cbn [fst].
  pose proof (g5_w_perm _ _ PE) as W1. rewrite g5_w_app in W1. pose proof (g5_w_nonneg H0).
  assert (W2 : g5_w ks <= g5_w (keys_texts K ++ g5_bks Ls)).
  { apply g5_w_incl; [exact ND|]. intros y Hy. apply g5_upds_incl. apply SS. exact Hy. }
  rewrite g5_w_app in W2.
  assert (W3 : g5_w (keys_texts K) = keys_total K) by (unfold g5_w; rewrite concat_end5_len, <- keys_total_texts; reflexivity).
  pose proof (g5_bks_w Ls). lia.
Qed.

Lemma g5_tot_le : forall pre (ps : list (rentry * (hsrc * nat))) kss,
  Forall2 (fun p ks => Z.of_nat (length (gone_segment pre (entry_lines (fst p) (snd p)) ks)) <= 2 * pair_cost (fst p) (snd p))
    ps kss ->
  gone_tot pre ps kss <= 2 * fold_right Z.add 0 (map (fun q => pair_cost (fst q) (snd q)) ps).
Proof. intros pre ps kss H. induction H as [|p ks ps kss Hp H IH]; cbn [gone_tot map fold_right]; lia. Qed.

Lemma g5_forall2_of_nth : forall {X Y} (R : X -> Y -> Prop) l1 l2 dx dy, length l1 = length l2 ->
  (forall j, (j < length l1)%nat -> R (nth j l1 dx) (nth j l2 dy)) -> Forall2 R l1 l2.
Proof.
  intros X Y R l1. induction l1 as [|x l1 IH]; intros [|y l2] dx dy HL HN; cbn [length] in HL; try discriminate;
    constructor.
  - exact (HN 0%nat ltac:(cbn [length]; lia)).
  - apply (IH l2 dx dy ltac:(lia)). intros j Hj. exact (HN (S j) ltac:(cbn [length]; lia)).
Qed.

Lemma g5_forall2_in : forall {X Y} (R : X -> Y -> Prop) l1 l2 x y, Forall2 R l1 l2 -> In (x, y) (combine l1 l2) -> R x y.
Proof.
  intros X Y R l1 l2 x y H. induction H as [|a b l1 l2 Hab H IH]; intros Hin; [destruct Hin|].
  cbn [combine] in Hin. destruct Hin as [E|Hin]; [injection E as -> ->; exact Hab | exact (IH Hin)].
Qed.

Lemma g5_nozero : forall l, ~ In (Z_to_bv 8 0) l -> nozero (bzs l).
Proof.
  intros l H. unfold nozero, bzs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
  intros E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in E. rewrite E.
  reflexivity.
Qed.

Lemma g5_bytes_eq : forall segs m a (l1 l2 : list byte), bytes_at segs m a l1 -> bytes_at segs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros segs m a l1 l2 (_ & _ & B1) (_ & _ & B2) HL.
  apply (nth_ext l1 l2 (Z_to_bv 8 0) (Z_to_bv 8 0) HL). intros k Hk.
  pose proof (B1 k Hk) as E1. rewrite (B2 k ltac:(lia)) in E1.
  assert (Hk2 : (k < length l2)%nat) by lia.
  rewrite (nth_error_nth' l1 (Z_to_bv 8 0) Hk), (nth_error_nth' l2 (Z_to_bv 8 0) Hk2) in E1.
  injection E1 as E1. symmetry. exact E1.
Qed.

Lemma g5_le4_inj : forall a b, 0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 -> le4 (Z_to_bv 64 a) = le4 (Z_to_bv 64 b) -> a = b.
Proof.
  intros a b Ha Hb H. apply (f_equal bytes_le_to_Z) in H. rewrite !bytes_le_to_Z_le4 in H.
  rewrite !unsigned_lit in H by lia. rewrite !Z.mod_small in H by lia. exact H.
Qed.

Lemma g5_src_held : forall (e : rentry) (h h' : hsrc), (re_eof e = 0 -> hs_held h' = hs_held h) ->
  hs_held (g5_src e h h') = hs_held h.
Proof. intros e h h' H. unfold g5_src. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [exact (H E0) | reflexivity]. Qed.

Lemma g5_consumed : forall (h : hsrc) (E' H' H'' : hlist), hl_recs E' = [] ->
  hl_recs (hs_expected (set_held (set_exp_held h E' H') H'')) = [] /\ hs_held (set_held (set_exp_held h E' H') H'') = H''.
Proof. intros h E' H' H'' HE. split; [exact HE | reflexivity]. Qed.

Section G5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.

Lemma g5_words : forall gn cl br dd (live : bool) (segsz : list (list Z)) (LB O junk' ob : list byte)
    (nout out nout' out' : word)
    (OUT' CAP' : Z) L A (m : word -> option byte),
  (gn = 0 \/ gn = 1) -> (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (concat segsz))) ->
  bzs LB = concat segsz -> bv_unsigned nout = 0 -> O = [] ->
  nout' = (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (concat segsz))) else nout) ->
  out' = (if live then Z_to_bv 64 OUT' else out) -> ob = (if live then LB else []) ->
  (live = false -> OUT' = bv_unsigned out) ->
  (live = true -> bv_unsigned nout + Z.of_nat (length (concat segsz)) <= CAP' /\ In (OUT', CAP') (blocks L A) /\
     fresh_block Bm OUT' CAP' /\ bytes_at (ms_segs Bm) m OUT' (O ++ LB ++ junk')) ->
  nout' = Z_to_bv 64 (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) /\
  bv_unsigned nout' = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) /\
  bv_unsigned out' = OUT' /\ Z.of_nat (length ob) = bv_unsigned nout' /\
  bytes_at (ms_segs Bm) m (bv_unsigned out') ob /\
  (ob = [] \/ exists CO, bv_unsigned nout' <= CO /\ In (bv_unsigned out', CO) (blocks L A) /\
     fresh_block Bm (bv_unsigned out') CO).
Proof.
  intros gn cl br dd live segsz LB O junk' ob nout out nout' out' OUT' CAP' L A m G0 G1 G2 HL HB HN HO EN EO EB HNL HLV.
  subst nout' out' ob.
  destruct (g5_tot0 gn cl br dd live segsz G0 G1 G2 HL) as [T1 T2].
  assert (LL : Z.of_nat (length LB) = Z.of_nat (length (concat segsz))) by (rewrite <- HB, bzs_length; reflexivity).
  pose proof (dc_ob_bytes Bm m live LB O junk' out OUT' (fun E => proj2 (proj2 (proj2 (HLV E)))) HO HNL) as BY.
  destruct live.
  - destruct (T1 eq_refl) as [Hg TZ]. subst gn. rewrite Z.eqb_refl.
    destruct (HLV eq_refl) as (C1 & C2 & C3 & _).
    pose proof C3 as (F1 & F2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as AC.
    assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (concat segsz)))) =
                 Z.of_nat (length (concat segsz))) by (rewrite HN; rewrite unsigned_lit by lia; lia).
    rewrite U1, (fresh_unsigned Bm OUT' CAP' C3 ltac:(lia)).
    split; [rewrite HN; f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact LL|].
    split; [exact BY|]. right. exists CAP'. rewrite HN in C1. split; [lia|]. split; [exact C2 | exact C3].
  - assert (T0 : (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) = 0).
    { destruct (Z.eqb_spec gn 0) as [Hg|Hg]; [rewrite (T2 eq_refl Hg); reflexivity | reflexivity]. }
    rewrite T0, <- (HNL eq_refl). split; [apply bv_eq; rewrite HN; symmetry; apply unsigned_lit; lia|].
    split; [exact HN|]. split; [reflexivity|]. split; [rewrite HN; reflexivity|].
    split; [exact BY | left; reflexivity].
Qed.

Lemma g5_held_nz : forall L A mem HA h, src_at Bm L A mem HA h ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h)).
Proof.
  intros L A mem HA h (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
  destruct LH as (_ & _ & _ & _ & _ & RS). eapply Forall_impl; [|exact RS].
  intros r (_ & _ & _ & NZ & _). exact (proj1 (NZ eq_refl)).
Qed.

Lemma g5_counts : forall L A mem t (es : list rentry) hjs (e : rentry) (hj : hsrc * nat) (h' : hsrc) k n,
  Forall (entry_ok Bm L A mem) es -> In (e, hj) (combine es hjs) -> pair_ok Bm L A mem t e hj ->
  slot_cost es hjs <= k -> k <= n -> n < INPUT_MAX ->
  (re_eof e = 0 -> map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected (fst hj))) ++
     map (map (Z_to_bv 8)) (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj)))) /\
     hs_held h' = hs_held (fst hj)) ->
  NoDup (texts (hs_held (g5_src e (fst hj) h'))) /\ hl_n (hs_expected (g5_src e (fst hj) h')) < 2 ^ 26 /\
  hl_n (hs_held (g5_src e (fst hj) h')) + Z.of_nat (count_begin (texts (hs_expected (g5_src e (fst hj) h')))) < 2 ^ 22.
Proof.
  intros L A mem t es hjs e [h i] h' k n HF Hin HP Hc Hk Hn HD. cbn [fst] in *.
  unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP.
  destruct HP as (SRC & _ & _ & SKU & SS & ND & HE0 & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov & _).
  unfold g5_src. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
  - destruct (HD E0) as [HM HH]. destruct (SKU E0) as [Hsk HU].
    destruct (dc_counts Bm L A mem es hjs e h h' i k n HF Hin Hc Hk Hn SS ND HE0 Hov Hsk HU HM HH) as (_ & _ & C3 & C4 & C5).
    split; [exact C3|]. split; [exact C4 | exact C5].
  - cbv iota. split; [exact ND|]. unfold hl_n at 1. rewrite HE0. split; [cbn; lia|].
    unfold texts. rewrite HE0. cbn [map].
    assert (NN : Forall (fun e0 => 0 <= re_used e0) es).
    { apply Forall_forall. intros e0 He0. rewrite Forall_forall in HF.
      destruct (HF e0 He0) as (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia. }
    assert (EOK : entry_ok Bm L A mem e).
    { rewrite Forall_forall in HF. apply HF. exact (in_combine_l _ _ _ _ Hin). }
    destruct EOK as (_ & _ & _ & _ & _ & _ & HUl & _ & _ & _ & _ & _ & _ & NDk & KF).
    assert (KF' : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
    { rewrite Forall_forall in KF |- *. intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & (K14 & _) & _). exact K14. }
    pose proof (p4_held_len (re_keys e) (hs_held h) ND SS) as HLn.
    assert (W0 : Z.of_nat (length (with_nul [])) <= (if re_skip e =? 0 then re_used e else 0) +
                 Z.of_nat (length (pending_stream h))) by (cbn; destruct (re_skip e =? 0); lia).
    unfold INPUT_MAX in Hn.
    destruct (p4_cnl_bound e h i (hs_held h) [] es hjs k Hin NN Hc ltac:(lia) KF' HLn W0) as [C _].
    exact C.
Qed.

Lemma g5_list_blocks : forall L A mem LA l lines x,
  list_at Bm L A mem LA l lines -> In x (list_blocks l) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros L A mem LA l lines x (C & HN & AR & ND1 & ND2 & RS) Hx. unfold list_blocks in Hx.
  apply in_app_or in Hx as [Hx|Hx].
  - revert Hx. destruct (Z.eqb_spec (hl_cap l) 0) as [H0|H0]; intros Hx; [destruct Hx|].
    destruct Hx as [<-|[]].
    destruct AR as [(Hc & _)|(Hc & Hin & _)]; [lia|]. exists (16 * hl_cap l). split; [lia|exact Hin].
  - apply in_map_iff in Hx as (r & <- & Hr). rewrite Forall_forall in RS. destruct (RS r Hr) as (Hin & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia|exact Hin].
Qed.

Lemma g5_src_blocks : forall L A mem HA h x,
  src_at Bm L A mem HA h -> In x (hs_blocks h) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros L A mem HA h x (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND) Hx.
  unfold hs_blocks in Hx. rewrite !in_app_iff in Hx.
  destruct Hx as [Hx|[[<-|[]]|[Hx|Hx]]].
  - exact (g5_list_blocks _ _ _ _ _ _ x LP Hx).
  - exists 6000. split; [lia|exact IN].
  - exact (g5_list_blocks _ _ _ _ _ _ x LE Hx).
  - exact (g5_list_blocks _ _ _ _ _ _ x LH Hx).
Qed.

Lemma g5_out0 : forall G OUT' (es es' : list rentry) (hs' : list hsrc) j h,
  NoDup (G :: OUT' :: concat (map entry_blocks es') ++
         concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) ->
  (j < length es)%nat -> length hs' = length es -> re_eof (nth j es no_entry) = 0 ->
  ~ In OUT' (hs_blocks (nth j hs' h)).
Proof.
  intros G OUT' es es' hs' j h ND Hj HL E0 X. apply (nodup_out_src G OUT' _ _ ND).
  apply in_concat. exists (hs_blocks (nth j hs' h)). split; [|exact X].
  apply in_map_iff. exists (nth j es no_entry, nth j hs' h). cbn [fst snd]. rewrite E0, Z.eqb_refl.
  split; [reflexivity|]. apply g5_in_combine; assumption.
Qed.

Lemma g5_out1 : forall L A mem G OUT OUT' (es es' : list rentry) (hj : list (hsrc * nat)) (hs' : list hsrc) j,
  NoDup (target_addrs G OUT es hj) -> (j < length es)%nat -> length hj = length es ->
  re_eof (nth j es no_entry) <> 0 ->
  src_at Bm L A mem (G_S + SRC_SIZE * Z.of_nat (snd (nth j hj no_hj))) (fst (nth j hj no_hj)) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (concat (map entry_blocks es)) ->
     ~ In q (drained_blocks es hj) ->
     q <> OUT' /\ ~ In q (concat (map entry_blocks es')) /\
     ~ In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')))) ->
  ~ In OUT' (hs_blocks (fst (nth j hj no_hj))).
Proof.
  intros L A mem G OUT OUT' es es' hj hs' j ND Hj HL E1 SRC HK X.
  destruct (g5_src_blocks L A mem _ _ OUT' SRC X) as (m & Hm & Hin).
  unfold target_addrs in ND. apply NoDup_ListNoDup in ND.
  assert (IH : In OUT' (concat (map (fun p => hs_blocks (fst p)) hj)))
    by exact (g5_in_concat_nth (fun p => hs_blocks (fst p)) hj no_hj j OUT' ltac:(lia) X).
  inversion ND as [|? ? N0 ND1]; subst. inversion ND1 as [|? ? N1 ND2]; subst.
  assert (NO : OUT' <> OUT) by (intros ->; apply N1; apply in_or_app; right; exact IH).
  assert (NE : ~ In OUT' (concat (map entry_blocks es))) by (intros Y; exact (g5_nd_app _ _ OUT' ND2 Y IH)).
  assert (ND3 := NoDup_app_remove_l _ _ ND2).
  assert (NDR : ~ In OUT' (drained_blocks es hj)).
  { intros D. unfold drained_blocks in D. apply in_concat in D as (l0 & Hl0 & Hx). apply in_map_iff in Hl0 as (p & <- & Hp).
    destruct (In_nth _ _ (no_entry, no_hj) Hp) as (k & Hk & Ek). rewrite combine_nth in Ek by (symmetry; exact HL).
    rewrite length_combine, HL, Nat.min_id in Hk. rewrite <- Ek in Hx. cbn [fst snd] in Hx.
    destruct (Z.eqb_spec (re_eof (nth k es no_entry)) 0) as [E0|E0]; [|destruct Hx].
    assert (Nk : k <> j) by (intros ->; exact (E1 E0)).
    exact (g5_concat_nodup (fun p => hs_blocks (fst p)) hj no_hj j k OUT' ND3 ltac:(lia) ltac:(lia) (not_eq_sym Nk) X Hx). }
  destruct (HK OUT' m Hin Hm NO NE NDR) as [C _]. exact (C eq_refl).
Qed.

Lemma g5_out_nl : forall L A L' A' (hc : hsrc) (E' H' : hlist) (ob : list byte) NO OUT,
  (ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO /\ ~ In OUT (hs_blocks hc)) ->
  Z.of_nat (length ob) = NO ->
  hl_v E' = hl_v (hs_expected hc) -> hl_cap E' = hl_cap (hs_expected hc) -> hl_recs E' = [] ->
  (forall q m, In (q, m) (blocks L A) -> ~ In q (map fst (hl_recs (hs_expected hc)) ++ list_blocks (hs_held hc)) ->
     In (q, m) (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m ->
     ~ In q (map fst (hl_recs (hs_expected hc)) ++ list_blocks (hs_held hc)) -> ~ In q (list_blocks H')) ->
  ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L' A') /\ fresh_block Bm OUT CO /\
    ~ In OUT (hs_blocks (set_exp_held hc E' H')).
Proof.
  intros L A L' A' hc E' H' ob NO OUT [HO|(CO & C1 & C2 & C3 & C4)] HL EV EC ER K1 K2; [left; exact HO|].
  destruct ob as [|b ob]; [left; reflexivity|]. right. cbn [length] in HL.
  assert (NF : ~ In OUT (map fst (hl_recs (hs_expected hc)) ++ list_blocks (hs_held hc))).
  { intros X. apply in_app_or in X. apply C4. unfold hs_blocks. rewrite !in_app_iff. destruct X as [X|X].
    - right; right; left. unfold list_blocks. apply in_app_iff. right. exact X.
    - right; right; right. exact X. }
  assert (NH : ~ In OUT (list_blocks H')) by (apply (K2 OUT CO C2); [lia | exact NF]).
  exists CO. split; [exact C1|]. split; [exact (K1 OUT CO C2 NF)|]. split; [exact C3|].
  unfold hs_blocks, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held]. rewrite !in_app_iff.
  intros [X|[X|[X|X]]].
  - apply C4. unfold hs_blocks. rewrite !in_app_iff. left. exact X.
  - apply C4. unfold hs_blocks. rewrite !in_app_iff. right; left. exact X.
  - unfold list_blocks in X. rewrite ER, EC, EV in X. cbn [map] in X. rewrite app_nil_r in X.
    apply C4. unfold hs_blocks. rewrite !in_app_iff. right; right; left. unfold list_blocks.
    apply in_app_iff. left. exact X.
  - exact (NH X).
Qed.

Lemma g5_out_se : forall L A L' A' (h : hsrc) (ds : list (Z * list byte)) (ob : list byte) NO OUT,
  (ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO /\ ~ In OUT (hs_blocks h)) ->
  incl ds (hl_recs (hs_held h)) ->
  (forall q m, In (q, m) (blocks L A) -> ~ In q (map fst ds) -> In (q, m) (blocks L' A')) ->
  ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L' A') /\ fresh_block Bm OUT CO.
Proof.
  intros L A L' A' h ds ob NO OUT [HO|(CO & C1 & C2 & C3 & C4)] HI K; [left; exact HO|]. right.
  exists CO. split; [exact C1|]. split; [|exact C3]. apply (K OUT CO C2). intros X.
  apply in_map_iff in X as (r & Er & Hr). apply C4. unfold hs_blocks. rewrite !in_app_iff. right; right; right.
  unfold list_blocks. apply in_app_iff. right. rewrite <- Er. apply in_map. exact (HI r Hr).
Qed.

Lemma g5_disj : forall (ob : list byte) NO OUT L A (h : hsrc),
  (ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO) -> ~ In OUT (hs_blocks h) ->
  ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO /\ ~ In OUT (hs_blocks h).
Proof.
  intros ob NO OUT L A h [HO|(CO & C1 & C2 & C3)] NI; [left; exact HO|]. right. exists CO.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact NI].
Qed.

Lemma g5_match : forall L A mem t (es : list rentry) (hj : list (hsrc * nat)) (fs os : list Z) i k,
  Forall2 (pair_ok Bm L A mem t) es hj -> NoDup (map re_fd es) ->
  (forall p, In p hj -> nth (snd p) fs 0 = hs_fd (fst p)) ->
  (forall i, (i < 4)%nat -> slot_open hj i = false -> nth i os 0 = 0) ->
  (i < 4)%nat -> nth i os 0 <> 0 -> (k < length es)%nat -> nth i fs 0 = re_fd (nth k es no_entry) ->
  snd (nth k hj no_hj) = i.
Proof.
  intros L A mem t es hj fs os i k PA ND HP HO Hi Ho Hk Hf.
  assert (LH : length hj = length es) by (symmetry; exact (Forall2_length PA)).
  destruct (slot_open hj i) eqn:SO; [|exact (False_ind _ (Ho (HO i Hi SO)))].
  unfold slot_open in SO. apply existsb_exists in SO as (q & Hq & Eq). apply Nat.eqb_eq in Eq. subst q.
  apply in_map_iff in Hq as (p & Ep & Hp). destruct (In_nth _ _ no_hj Hp) as (k' & Hk' & Ek').
  rewrite LH in Hk'.
  pose proof (g5_forall2_nth _ _ _ no_entry no_hj PA k' Hk') as PK. rewrite Ek' in PK.
  unfold pair_ok in PK. cbv zeta in PK. destruct PK as (_ & _ & FD & _).
  rewrite <- Ep, (HP p Hp), FD in Hf.
  rewrite <- (g5_nodup_nth re_fd es no_entry k' k ND Hk' Hk Hf), Ek'. exact Ep.
Qed.

Lemma g5_read : forall L A mem t (es : list rentry) (hj : list (hsrc * nat)) (fs os : list Z) i,
  Forall2 (pair_ok Bm L A mem t) es hj -> NoDup (map re_fd es) ->
  (forall p, In p hj -> nth (snd p) fs 0 = hs_fd (fst p)) ->
  (forall i, (i < 4)%nat -> slot_open hj i = false -> nth i os 0 = 0) ->
  (i < 4)%nat -> op5_rec es (nth i fs 0) (nth i os 0) <> 0 ->
  exists k, (k < length es)%nat /\ snd (nth k hj no_hj) = i /\ re_eof (nth k es no_entry) = 0.
Proof.
  intros L A mem t es hj fs os i PA ND HP HO Hi HR. unfold op5_rec in HR.
  destruct (Z.eqb_spec (nth i os 0) 0) as [E0|E0]; [lia|].
  destruct (g5_hit _ _ HR) as (k & Hk & K1 & K2). exists k. split; [exact Hk|]. split; [|exact K2].
  exact (g5_match L A mem t es hj fs os i k PA ND HP HO Hi E0 Hk (eq_sym K1)).
Qed.

Lemma g5_read_cell : forall L A mem i (h : hsrc), ms_segs Bm = rsegs ->
  src_at Bm L A mem (G_S + SRC_SIZE * Z.of_nat i) h -> hl_recs (hs_pending h) = [] ->
  - 2 ^ 31 <= 0 <= 0 /\
  bytes_at rsegs mem (bv_unsigned (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) + 24) (le4 (Z_to_bv 64 0)).
Proof.
  intros L A mem i h SEG HS HP. split; [lia|]. pose proof (dc_read Bm L A mem _ h HS HP) as BY.
  rewrite SEG in BY. unfold SRC_SIZE in BY. pose proof (bytes_at_bound _ _ _ _ BY) as (B0 & B1).
  change (length (le4 (Z_to_bv 64 0))) with 4%nat in B1.
  rewrite unsigned_lit; [exact BY|]. unfold G_S in *. lia.
Qed.

Lemma g5_fin_no : forall L A mem t lv mx (e : rentry) (hj : hsrc * nat),
  entry_ok Bm L A mem e -> pair_ok Bm L A mem t e hj -> re_eof e = 0 -> forall no cap,
  ds_no (drain_fin lv mx no cap e (fst hj)) =
  no + Z.of_nat (length (with_nul (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj)))))).
Proof.
  intros L A mem t lv mx e [h i] EOK HP E0 no cap. cbn [fst].
  unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP. destruct HP as (SRC & _ & _ & SKU & _).
  destruct (SKU E0) as [Hsk HU].
  destruct EOK as (_ & SK & _ & _ & _ & CAPC & UL & UB & UNZ & _).
  apply rma_fin_no.
  - unfold J1, hs_state. cbn [ls_k ls_w]. rewrite Hsk. split; [reflexivity|]. split.
    + intros F0. apply HU. destruct SK as [S|S]; [exact S|]. rewrite <- Hsk, S in F0. discriminate.
    + split; [|apply g5_nozero; exact UNZ].
      unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000. lia.
  - destruct SRC as (_ & _ & _ & _ & _ & LP & _ & OFFD & _).
    destruct LP as (_ & _ & _ & _ & _ & HR).
    unfold rma_pok, drain_init. cbn [ds_off ds_pend].
    destruct OFFD as [(R0 & O0)|(r & rs & ER & OR)].
    + rewrite R0. split; [lia | exact I].
    + rewrite ER in HR |- *. cbn [map]. split; [lia|]. split; [unfold bzs; rewrite length_map; lia|].
      apply Forall_map. apply Forall_forall. intros r' Hr'. apply Forall_inv_tail in HR.
      destruct (proj1 (Forall_forall _ _) HR r' Hr') as (_ & _ & _ & _ & L1). unfold bzs. rewrite length_map.
      exact (L1 eq_refl).
  - lia.
Qed.

Lemma g5_pair_seg : forall L A mem t pre (e : rentry) (hj : hsrc * nat) (ks : list (list Z)),
  entry_ok Bm L A mem e -> pair_ok Bm L A mem t e hj ->
  NoDup ks -> same_set ks (upds (keys_texts (re_keys e)) (entry_lines e hj)) ->
  Z.of_nat (length (gone_segment pre (entry_lines e hj) ks)) <= 2 * pair_cost e hj.
Proof.
  intros L A mem t pre e [h i] ks EOK HP ND SS.
  pose proof (g5_seg_le pre ks (re_keys e) (entry_lines e (h, i)) ND SS) as S.
  unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP. destruct HP as (SRC & _ & _ & SKU & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov & _).
  destruct EOK as (_ & _ & _ & _ & _ & _ & HUl & _).
  pose proof (keys_total_nonneg (re_keys e)) as KN.
  assert (SU : 0 <= (if re_skip e =? 0 then re_used e else 0)) by (destruct (re_skip e =? 0); lia).
  unfold pair_cost. cbn [fst]. unfold entry_lines in S |- *. cbn [fst] in S |- *.
  destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
  - destruct (SKU E0) as [Hsk HU]. pose proof (reads_bound e h Hsk HU Hov HUl) as RB. lia.
  - cbn [with_nul map concat length Z.of_nat] in S. lia.
Qed.

Lemma g5_cap : forall L A mem t lv mx NO CAP CAP' pre (es : list rentry) (hs : list (hsrc * nat))
    (kss : list (list (list Z))) k n,
  Forall (entry_ok Bm L A mem) es -> Forall2 (pair_ok Bm L A mem t) es hs ->
  slot_cost es hs <= k -> k <= n -> n < INPUT_MAX ->
  length kss = length es -> NO = 0 -> CAP <= TBBYTES ->
  (forall i, (i < length es)%nat -> NoDup (nth i kss []) /\
     same_set (nth i kss []) (upds (keys_texts (re_keys (nth i es no_entry))) (entry_lines (nth i es no_entry) (nth i hs no_hj))) /\
     nth i kss [] = ds_H (nth i (gone_states lv mx NO CAP pre es hs)
                              (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))))) ->
  CAP' = gone_cap lv mx NO CAP pre es hs ->
  CAP' <= TBBYTES.
Proof.
  intros L A mem t lv mx NO CAP CAP' pre es hs kss k n HF PA Hc Hk Hn Lk HNO HCAP HKS ->.
  assert (Lh : length hs = length es) by (symmetry; exact (Forall2_length PA)).
  assert (HD : Forall (fun p => re_eof (fst p) = 0 -> forall no cap,
            ds_no (drain_fin lv mx no cap (fst p) (fst (snd p))) =
            no + Z.of_nat (length (with_nul (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))))))
         (combine es hs)).
  { apply Forall_forall. intros [e hj] Hp. cbn [fst snd]. apply (g5_fin_no L A mem t).
    - rewrite Forall_forall in HF. apply HF. exact (in_combine_l _ _ _ _ Hp).
    - exact (g5_forall2_in _ _ _ _ _ PA Hp). }
  pose proof (gone_cap_le lv mx NO CAP pre es hs kss Lh Lk HD
    (fun i Hi => proj2 (proj2 (HKS i Hi)))) as CB.
  rewrite (gone_tot_seq pre es hs kss Lh Lk) in CB.
  assert (T2 : gone_tot pre (combine es hs) kss <= 2 * slot_cost es hs).
  { unfold slot_cost. apply g5_tot_le. apply (g5_forall2_of_nth _ _ _ (no_entry, no_hj) []).
    - rewrite length_combine, Lh, Lk. apply Nat.min_id.
    - intros j Hj. rewrite length_combine, Lh, Nat.min_id in Hj. rewrite combine_nth by (symmetry; exact Lh).
      cbn [fst snd]. destruct (HKS j Hj) as (ND & SS & _).
      apply (g5_pair_seg L A mem t); [| exact (g5_forall2_nth _ _ _ no_entry no_hj PA j Hj) | exact ND | exact SS].
      rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hj. }
  unfold INPUT_MAX, TBBYTES in *. lia.
Qed.

Lemma g5_slot_words : forall L A mem t nfd G OUT (es : list rentry) (hj : list (hsrc * nat)) (fs os : list Z),
  relay_at Bm L A mem t nfd G OUT es hj ->
  (forall i, (i < 4)%nat ->
     rw_cells (ms_segs Bm) mem (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) ->
  (forall i, (i < 4)%nat -> (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31) ->
  (forall p, In p hj -> nth (snd p) fs 0 = hs_fd (fst p) /\ nth (snd p) os 0 = 1) /\
  (forall i, (i < 4)%nat -> slot_open hj i = false -> nth i os 0 = 0).
Proof.
  intros L A mem t nfd G OUT es hj fs os RA HC HR. destruct RA as (_ & _ & _ & _ & _ & _ & PA & _ & ZH & _).
  assert (LH : length hj = length es) by (symmetry; exact (Forall2_length PA)).
  split.
  - intros p Hp. destruct (In_nth _ _ no_hj Hp) as (k & Hk & Ek). rewrite LH in Hk.
    pose proof (g5_forall2_nth _ _ _ no_entry no_hj PA k Hk) as PK. rewrite Ek in PK.
    unfold pair_ok in PK. cbv zeta in PK. destruct PK as (SRC & Hlt & _).
    destruct SRC as (C & _ & _ & OPEN & FDR & _).
    destruct (HR (snd p) Hlt) as (OR & FR). pose proof (HC (snd p) Hlt) as CS.
    destruct C as ((_ & B1) & _). destruct CS as ((_ & B2) & _). cbn [cells_bytes cbytes] in B1, B2.
    rewrite !bytes_at_app, !length_le4 in B1, B2. destruct B1 as (F1 & O1 & _). destruct B2 as (F2 & O2 & _).
    rewrite OPEN in O1.
    pose proof (g5_bytes_eq _ _ _ _ _ F2 F1 ltac:(rewrite !length_le4; reflexivity)) as EF.
    pose proof (g5_bytes_eq _ _ _ _ _ O2 O1 ltac:(rewrite !length_le4; reflexivity)) as EO.
    split; [exact (g5_le4_inj _ _ FR FDR EF) | apply (g5_le4_inj (nth (snd p) os 0) 1 ltac:(lia) ltac:(lia) EO)].
  - intros i Hi SO. specialize (ZH i Hi SO). destruct ZH as ((_ & B1) & _). cbn [cells_bytes cbytes] in B1.
    rewrite app_nil_r in B1.
    change (nulbytes 96) with (repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 88) in B1.
    rewrite !bytes_at_app in B1. destruct B1 as (_ & Z1 & _). change (length (repeat (Z_to_bv 8 0) 4)) with 4%nat in Z1.
    destruct (HR i Hi) as (OR & _). pose proof (HC i Hi) as CS. destruct CS as ((_ & B2) & _).
    cbn [cells_bytes cbytes] in B2. rewrite !bytes_at_app, !length_le4 in B2. destruct B2 as (_ & O2 & _).
    pose proof (g5_bytes_eq _ _ _ _ _ O2 Z1 ltac:(rewrite length_le4; reflexivity)) as EO.
    change (repeat (Z_to_bv 8 0) 4) with (le4 (Z_to_bv 64 0)) in EO.
    apply (g5_le4_inj (nth i os 0) 0 ltac:(lia) ltac:(lia) EO).
Qed.

End G5.
