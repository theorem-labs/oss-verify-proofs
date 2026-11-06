(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg ShapeLaws Spec BigintSpec HaltsBridge HaltsSpec PhiExtract.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition t_guard (Phi : Prop) (K : TSet) : TSet := fun tr => tr = [] \/ (Phi /\ K tr).

Lemma t_guard_has_nil : forall Phi K, t_guard Phi K [].
Proof. intros. left. reflexivity. Qed.

Lemma t_guard_eq : forall (Phi : Prop) (K : TSet), Phi -> K [] -> t_eq (t_guard Phi K) K.
Proof.
  intros Phi K HPhi HK tr. unfold t_guard. split.
  - intros [-> | [_ H]]; [exact HK | exact H].
  - intros H. right. split; assumption.
Qed.

Lemma t_emit_congr_k : forall (e : list event) (T T' : TSet), t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply (H tr'); exact HT]]).
Qed.

Definition b48 : byte := Z_to_bv 8 48.
Definition b10 : byte := Z_to_bv 8 10.

(* [comment removed for export] *)
Definition succG (Phi : Prop) (calls : nat) (fs : Fs.Fs) : TSet :=
  t_emit (W 1 [b48]) (t_guard Phi (t_emit (W 1 (b10 :: zero_lines (Nat.pred calls))) (t_exit (exit_code 0) fs))).

Lemma zero_lines_S : forall k, zero_lines (S k) = [b48] ++ (b10 :: zero_lines k).
Proof. reflexivity. Qed.

Lemma succG_eq : forall (Phi : Prop) calls fs, Phi -> (1 <= calls)%nat ->
  t_eq (succG Phi calls fs) (t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs)).
Proof.
  intros Phi calls fs HPhi Hc. destruct calls as [|k]; [exfalso; clear - Hc; lia|]. cbn [Nat.pred]. unfold succG. cbn [Nat.pred].
  rewrite zero_lines_S. eapply t_eq_trans; [| apply t_emit_W_app].
  apply t_emit_congr_k. apply t_guard_eq; [exact HPhi | apply t_emit_has_nil].
Qed.


Lemma t_guard_congr : forall (Phi : Prop) K K', t_eq K K' -> t_eq (t_guard Phi K) (t_guard Phi K').
Proof. intros Phi K K' H tr. unfold t_guard. rewrite (H tr). tauto. Qed.

(* [comment removed for export] *)
Lemma iter1_guard_eq : forall (Phi : Prop) K, Phi -> K [] ->
  t_eq (t_emit (W 1 (zero_lines 1)) K) (t_emit (W 1 [b48]) (t_guard Phi (t_emit (W 1 [b10]) K))).
Proof.
  intros Phi K HPhi HK. change (zero_lines 1) with ([b48] ++ [b10]).
  eapply t_eq_trans; [apply t_eq_sym; apply t_emit_W_app |].
  apply t_emit_congr_k. apply t_eq_sym. apply t_guard_eq; [exact HPhi | apply t_emit_has_nil].
Qed.

(* [comment removed for export] *)
Lemma loop_guard_eq : forall (Phi : Prop) n fs, (1 <= n)%nat ->
  t_eq (t_emit (W 1 [b48]) (t_guard Phi (t_emit (W 1 [b10]) (t_emit (W 1 (zero_lines (n - 1))) (t_exit (exit_code 0) fs)))))
       (succG Phi n fs).
Proof.
  intros Phi n fs Hn. unfold succG. apply t_emit_congr_k. apply t_guard_congr.
  eapply t_eq_trans; [apply t_emit_W_app |]. replace ([b10] ++ zero_lines (n - 1)) with (b10 :: zero_lines (Nat.pred n)); [apply (t_eq_refl _)|].
  destruct n as [|m]; [exfalso; clear - Hn; lia|]. cbn [Nat.pred app]. replace (S m - 1)%nat with m by (clear; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition t_bodyG (PhiD : list byte -> Prop) (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? 6)%nat then t_die msg_short fs
  else
    let b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)) in
    let b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)) in
    let b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0)) in
    let cfg := (b0 + 256 * b1)%Z in
    let config_len := Z.to_nat (cfg mod 32768) in
    if (len <? 6 + config_len)%nat then t_die msg_overrun fs
    else
      let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
      succG (PhiD data) calls fs.

(* [comment removed for export] *)
Definition specG (PhiD : list byte -> Prop) (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_die (msg_read_error path) fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_bodyG PhiD data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

(* [comment removed for export] *)
Definition cfgD (data : list byte) : Z := ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768)%Z.
Definition callsD (data : list byte) : nat :=
  match Z.to_nat (cfgD data) with O => 1%nat | _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)) end.
Definition hdr_okD (data : list byte) : Prop :=
  (Z.of_nat (length data) < MAX_INPUT)%Z /\ (6 <= length data)%nat /\ (6 + Z.to_nat (cfgD data) <= length data)%nat.

Lemma callsD_pos : forall data, (1 <= callsD data)%nat.
Proof. intros data. unfold callsD. destruct (Z.to_nat (cfgD data)); clear; lia. Qed.

Lemma t_bodyG_ok : forall PhiD data fs, hdr_okD data -> t_bodyG PhiD data fs = succG (PhiD data) (callsD data) fs.
Proof.
  intros PhiD data fs (H1 & H2 & H3). unfold t_bodyG.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; exact H1).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; exact H2). cbv zeta.
  fold (cfgD data). replace (length data <? 6 + Z.to_nat (cfgD data))%nat with false by (symmetry; apply Nat.ltb_ge; exact H3).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_bodyG_eq : forall PhiD data fs, (hdr_okD data -> PhiD data) -> t_eq (t_bodyG PhiD data fs) (t_body data fs).
Proof.
  intros PhiD data fs HPhi. unfold t_bodyG, t_body.
  destruct (Z.leb_spec0 MAX_INPUT (Z.of_nat (length data))) as [Hr|Hr]; [apply (t_eq_refl _)|].
  destruct (Nat.ltb_spec0 (length data) 6) as [Hs|Hs]; [apply (t_eq_refl _)|]. cbv zeta. fold (cfgD data).
  destruct (Nat.ltb_spec0 (length data) (6 + Z.to_nat (cfgD data))) as [Ho|Ho]; [apply (t_eq_refl _)|].
  change (match Z.to_nat (cfgD data) with O => 1%nat | S _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)) end) with (callsD data).
  apply succG_eq; [| apply callsD_pos]. apply HPhi. split; [lia | split; lia].
Qed.

Lemma list_byte_eqb_iff : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  intros p. induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate | discriminate]); [tauto|].
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 H2]. f_equal; [apply bv_eq; exact H1 | exact H2].
  - intros H. injection H as -> ->. auto.
Qed.

Theorem specG_eq : forall PhiD argv fs,
  (forall a0 path data, argv = [a0; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
     fs_lookup fs path = Some data -> hdr_okD data -> PhiD data) ->
  t_eq (specG PhiD argv fs) (spec argv fs).
Proof.
  intros PhiD argv fs HPhi. unfold specG, spec.
  destruct argv as [| a0 [| path [| x rest]]]; [apply (t_eq_refl _) | apply (t_eq_refl _) | | apply (t_eq_refl _)].
  destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort]; [apply (t_eq_refl _)|].
  destruct (list_byte_eqb path []) eqn:E1; [apply (t_eq_refl _)|].
  destruct (list_byte_eqb path dot_path) eqn:E2; [apply (t_eq_refl _)|].
  destruct (fs_lookup fs path) as [data|] eqn:Hlk; [| apply (t_eq_refl _)].
  apply t_alt2_congr_r. apply t_bodyG_eq. intros Hh. apply (HPhi a0 path data eq_refl); [clear - Hshort; lia | | | exact Hlk | exact Hh].
  - intros E. apply list_byte_eqb_iff in E. rewrite E in E1. discriminate E1.
  - intros E. apply list_byte_eqb_iff in E. rewrite E in E2. discriminate E2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t0 : list event := [WriteEv (Z_to_bv 64 1) b48].

Lemma t0_no_halt : ~ PhiExtract.has_halt_ev t0.
Proof.
  intros (fs & [(code & H) | (sig & H)]); (destruct H as [H | []]; discriminate H).
Qed.

Lemma t0_in_succG : forall Phi calls fs, succG Phi calls fs t0.
Proof. intros. unfold succG, t_emit. left. cbn. split; [reflexivity | exact I]. Qed.

(* [comment removed for export] *)
Lemma first_ev_W2 : forall (msg : list byte) K tr, t_emit (W 2 msg) K (t0 ++ tr) -> msg = [] /\ K (t0 ++ tr).
Proof.
  intros msg K tr [Hp | (tr' & Heq & HK)].
  - exfalso. destruct msg as [|m msg]; cbn in Hp; [exact Hp |]. destruct Hp as [H _].
    injection H as H' _. vm_compute in H'. discriminate H'.
  - destruct msg as [|m msg]; [split; [reflexivity | cbn in Heq; rewrite <- Heq in HK; exact HK] |].
    exfalso. cbn in Heq. injection Heq as H _. vm_compute in H. discriminate H.
Qed.

Lemma t_die_not_t0 : forall msg fs tr, t_die msg fs (t0 ++ tr) -> False.
Proof.
  intros msg fs tr H. unfold t_die in H. apply first_ev_W2 in H as [_ H].
  unfold t_exit, t_emit, t_nil in H. destruct H as [Hp | (tr' & Heq & ->)].
  - cbn in Hp. destruct Hp as [H _]. discriminate H.
  - cbn in Heq. injection Heq as H _. discriminate H.
Qed.

Lemma succG_guard : forall Phi calls fs tr, succG Phi calls fs (t0 ++ tr) -> tr <> [] -> Phi.
Proof.
  intros Phi calls fs tr H Hne. unfold succG, t_emit in H. destruct H as [Hp | (tr' & Heq & HG)].
  - exfalso. cbn in Hp. destruct Hp as [_ Hp]. destruct tr; [exact (Hne eq_refl) | exact Hp].
  - cbn in Heq. injection Heq as ->. destruct HG as [-> | [HPhi _]]; [exfalso; exact (Hne eq_refl) | exact HPhi].
Qed.


(* [comment removed for export] *)
Section LibRuns.
  Variable PhiD : list byte -> Prop.
  Variables a0 path : list byte.
  Variable fs : Fs.Fs.
  Variable data : list byte.
  Hypothesis Hlen : (length path < 4096)%nat.
  Hypothesis Hne : path <> [].
  Hypothesis Hnd : path <> dot_path.
  Hypothesis Hlk : fs_lookup fs path = Some data.
  Hypothesis Hhdr : hdr_okD data.

  Lemma specG_lib : specG PhiD [a0; path] fs = t_alt2 (t_die (msg_cannot_open path) fs) (succG (PhiD data) (callsD data) fs).
  Proof.
    unfold specG. replace (4096 <=? length path)%nat with false by (symmetry; apply Nat.leb_gt; exact Hlen).
    destruct (list_byte_eqb path []) eqn:E1; [exfalso; apply Hne; apply list_byte_eqb_iff in E1; exact E1 |].
    destruct (list_byte_eqb path dot_path) eqn:E2; [exfalso; apply Hnd; apply list_byte_eqb_iff in E2; exact E2 |].
    rewrite Hlk. rewrite (t_bodyG_ok PhiD data fs Hhdr). reflexivity.
  Qed.

  Lemma specG_t0 : specG PhiD [a0; path] fs t0.
  Proof. rewrite specG_lib. right. apply t0_in_succG. Qed.

  Lemma guard_after_specG : PhiExtract.guard_after (specG PhiD [a0; path] fs) t0 (PhiD data).
  Proof.
    intros tr Htr Hne'. rewrite specG_lib in Htr. destruct Htr as [H | H].
    - exfalso. exact (t_die_not_t0 _ _ _ H).
    - exact (succG_guard _ _ _ _ H Hne').
  Qed.
End LibRuns.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Codes.
  Variable S : list word.
  Hypothesis S0 : In (exit_code 0) S.
  Hypothesis S2 : In (exit_code 2) S.

  Lemma codes_ok_guard : forall Phi K, codes_ok S K -> codes_ok S (t_guard Phi K).
  Proof. intros Phi K HK tr code fs' [-> | [_ H]] Hin; [destruct Hin | exact (HK _ _ _ H Hin)]. Qed.
  Lemma nokill_guard : forall Phi K, nokill K -> nokill (t_guard Phi K).
  Proof. intros Phi K HK tr sig fs' [-> | [_ H]] Hin; [destruct Hin | exact (HK _ _ _ H Hin)]. Qed.

  Lemma codes_ok_succG : forall Phi calls fs, codes_ok S (succG Phi calls fs).
  Proof.
    intros. unfold succG. apply codes_ok_emit; [intros code fs' H; exfalso; exact (In_W_not_exit _ _ _ _ H) |].
    apply codes_ok_guard. apply codes_ok_emit; [intros code fs' H; exfalso; exact (In_W_not_exit _ _ _ _ H) |].
    apply codes_ok_exit. exact S0.
  Qed.
  Lemma nokill_succG : forall Phi calls fs, nokill (succG Phi calls fs).
  Proof.
    intros. unfold succG. apply nokill_emit; [intros sig fs' H; exact (In_W_not_kill _ _ _ _ H) |].
    apply nokill_guard. apply nokill_emit; [intros sig fs' H; exact (In_W_not_kill _ _ _ _ H) |].
    apply nokill_exit.
  Qed.

  Lemma codes_ok_bodyG : forall PhiD data fs, codes_ok S (t_bodyG PhiD data fs).
  Proof.
    intros PhiD data fs. unfold t_bodyG.
    destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply codes_ok_die; exact S2 |].
    destruct (length data <? 6)%nat; [apply codes_ok_die; exact S2 |].
    destruct (length data <? _)%nat; [apply codes_ok_die; exact S2 |].
    apply codes_ok_succG.
  Qed.
  Lemma nokill_bodyG : forall PhiD data fs, nokill (t_bodyG PhiD data fs).
  Proof.
    intros PhiD data fs. unfold t_bodyG.
    destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply nokill_die |].
    destruct (length data <? 6)%nat; [apply nokill_die |].
    destruct (length data <? _)%nat; [apply nokill_die |].
    apply nokill_succG.
  Qed.

  Theorem codes_ok_specG : forall PhiD argv fs, codes_ok S (specG PhiD argv fs).
  Proof.
    intros PhiD argv fs. unfold specG.
    destruct argv as [| a0 [| path [| x rest]]]; try (apply codes_ok_die; exact S2).
    destruct (4096 <=? length path)%nat; [apply codes_ok_die; exact S2 |].
    destruct (list_byte_eqb path []); [apply codes_ok_die; exact S2 |].
    destruct (list_byte_eqb path dot_path); [apply codes_ok_alt2; apply codes_ok_die; exact S2 |].
    destruct (fs_lookup fs path); [| apply codes_ok_die; exact S2].
    apply codes_ok_alt2; [apply codes_ok_die; exact S2 | apply codes_ok_bodyG].
  Qed.
  Theorem nokill_specG : forall PhiD argv fs, nokill (specG PhiD argv fs).
  Proof.
    intros PhiD argv fs. unfold specG.
    destruct argv as [| a0 [| path [| x rest]]]; try apply nokill_die.
    destruct (4096 <=? length path)%nat; [apply nokill_die |].
    destruct (list_byte_eqb path []); [apply nokill_die |].
    destruct (list_byte_eqb path dot_path); [apply nokill_alt2; apply nokill_die |].
    destruct (fs_lookup fs path); [| apply nokill_die].
    apply nokill_alt2; [apply nokill_die | apply nokill_bodyG].
  Qed.
End Codes.
End FPX_1.
