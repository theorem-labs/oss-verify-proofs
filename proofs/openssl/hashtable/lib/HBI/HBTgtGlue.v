(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxNodesIOSound CxReblob HBPlanImage HBAtable HBSel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TT0 (E : env) (fs' : Fs.Fs) : TSet := TGT (nb_of E <? 11) (calls_of E) (cnt_of E) fs'.

(* [comment removed for export] *)
Lemma closed_agree : forall e E E', expr_vars_lt 0 e = true -> env_agree NX0 E E' -> uE E e = uE E' e.
Proof. intros e E E' He Hag. unfold uE. rewrite (edenot_agree' 0 E E' e); [reflexivity | | exact He]. destruct Hag as [_ Hb]. split; [intros n Hn; lia | exact Hb]. Qed.
Lemma nb_agree : forall E E', env_agree NX0 E E' -> nb_of E = nb_of E'.
Proof. intros E E' Hag. unfold nb_of, cl_of. rewrite (closed_agree e_cl E E' eq_refl Hag). destruct Hag as [_ Hb]. rewrite Hb. reflexivity. Qed.
Lemma TT0_agree : forall E E' fs0, env_agree NX0 E E' -> TT0 E fs0 = TT0 E' fs0.
Proof.
  intros E E' fs0 Hag. unfold TT0, calls_of, cnt_of, cl_of. rewrite (nb_agree E E' Hag), (closed_agree e_cl E E' eq_refl Hag), (closed_agree e_cm E E' eq_refl Hag), (closed_agree e_b1s E E' eq_refl Hag). reflexivity.
Qed.
Lemma TT0_nil : forall E fs0, TT0 E fs0 [].
Proof. intros E fs0. unfold TT0, TGT. apply t_emit_has_nil. Qed.

(* [comment removed for export] *)
Definition TTK (E : env) (fs' : Fs.Fs) : TSet := TGT false (calls_of E) (cnt_of E) fs'.
Lemma TTK_agree : forall E E' fs0, env_agree NX0 E E' -> TTK E fs0 = TTK E' fs0.
Proof.
  intros E E' fs0 Hag. unfold TTK, calls_of, cnt_of, cl_of. rewrite (closed_agree e_cl E E' eq_refl Hag), (closed_agree e_cm E E' eq_refl Hag), (closed_agree e_b1s E E' eq_refl Hag). reflexivity.
Qed.
Lemma TTK_nil : forall E fs0, TTK E fs0 [].
Proof. intros E fs0. unfold TTK, TGT. apply t_emit_has_nil. Qed.

Lemma W1_line : forall neg, W1 (lineZ neg) = W 1 (line_ht neg).
Proof. intros [|]; reflexivity. Qed.
Lemma W1_lines : forall neg n, W1 (rep (lineZ neg) n) = W 1 (lines_ht neg n).
Proof.
  intros neg n. induction n as [|n IH]; [reflexivity|]. cbn [rep lines_ht]. unfold W1, W in *.
  rewrite !map_app. rewrite IH. f_equal. exact (W1_line neg).
Qed.

(* [comment removed for export] *)
Lemma chunk_same : forall j (c : list byte), AsanPlanSound.APS.chunk j c = chunk j c.
Proof. intros. unfold AsanPlanSound.APS.chunk, chunk, AsanPlanSound.APS.CH, CH. reflexivity. Qed.

Lemma chunk0_small : forall c : list byte, Z.of_nat (length c) <= 65536 -> AsanPlanSound.APS.chunk 0 c = c.
Proof.
  intros c H. unfold AsanPlanSound.APS.chunk. rewrite Nat.mul_0_r. cbn [skipn]. apply firstn_all2.
  apply Nat2Z.inj_le. unfold AsanPlanSound.APS.CH. rewrite Z2Nat.id by lia. exact H.
Qed.

Lemma swrap8_big : forall x, 0 <= x < 256 -> (bv_swrap 8 x mod 2 ^ 64 <=? MAXS) = (x <? 128).
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, MAXS. change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec x 128) as [Hs|Hb].
  - rewrite (Z.mod_small (x + 128) 256) by lia. replace (x + 128 - 128) with x by lia. rewrite (Z.mod_small x 18446744073709551616) by lia. apply Z.leb_le. lia.
  - rewrite <- (Z.mod_unique_pos (x + 128) 256 1 (x - 128)) by lia.
    rewrite <- (Z.mod_unique_pos (x - 128 - 128) 18446744073709551616 (-1) (x - 256 + 18446744073709551616)) by lia.
    apply Z.leb_gt. lia.
Qed.

Section Glue.
  Variable ph : PhdrInfo.
  Variable sp : word. Variable rdraw : EntryDraw. Variable brk0 : word. Variables argv envp : list (list byte). Variables uid hw : word.
  Variable c : list byte.
  #[local] Notation SV := (SINVm ph sp rdraw brk0 argv envp uid hw c).

  Theorem tt0_target : forall E M fs', SV E M -> 6 <= flen c <= 65535 -> 0 <= ION.room c -> t_eq (TT0 E fs') (t_target_ht c fs').
  Proof.
    intros E M fs' HS HF HR.
    assert (Hlen : Z.of_nat (length c) <= 65535) by (unfold flen in HF; lia).
    assert (Hfl : flen c = Z.of_nat (length c)) by (unfold flen; change (2 ^ 26) with 67108864; lia).
    assert (Hb : eb E 32%nat = c).
    { destruct HS as (_ & _ & _ & Hch). specialize (Hch 0%nat). change (JB + 0)%nat with 32%nat in Hch. rewrite Hch. apply chunk0_small. lia. }
    assert (Hb0 : forall i, ION.hbyte i c = byte_at c i) by (intros i; reflexivity).
    assert (Hcl : cl_of E = Z.of_nat (config_len c)).
    { unfold cl_of, e_cl. rewrite CFGX_denot. rewrite Hb. unfold config_len, cfg_word. rewrite !Hb0.
      pose proof (Z.mod_pos_bound (byte_at c 0 + 256 * byte_at c 1) 32768 ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
    assert (Hroom : Z.of_nat (config_len c) <= Z.of_nat (length c) - 6).
    { unfold ION.room, ION.flenZ, ION.cfglen in HR. unfold config_len, cfg_word. rewrite <- !Hb0.
      pose proof (Z.mod_pos_bound (ION.hbyte 0 c + 256 * ION.hbyte 1 c) 32768 ltac:(lia)). rewrite Z2Nat.id by lia. unfold flen in Hfl. change (2 ^ 26) with 67108864 in *. lia. }
    assert (Hnb : nb_of E = Z.of_nat (ht_payload_len c)).
    { unfold nb_of. rewrite Hb, Hcl. unfold ht_payload_len, HDR_MIN. lia. }
    assert (Hneg : (nb_of E <? 11) = ht_neg c).
    { rewrite Hnb. unfold ht_neg. destruct (Nat.ltb_spec (ht_payload_len c) 11); [apply Z.ltb_lt | apply Z.ltb_ge]; lia. }
    assert (Hcalls : calls_of E = ht_calls c).
    { unfold calls_of, ht_calls. rewrite Hcl. destruct (config_len c) as [|n] eqn:Hc; [reflexivity|].
      replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold e_cm. rewrite XCM_denot, Hb, Hb0. pose proof (Z.mod_pos_bound (byte_at c 2) 4 ltac:(lia)). rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity. }
    assert (Hcnt : cnt_of E = (32768 <=? cfg_word c)).
    { unfold cnt_of, e_b1s. rewrite XB1S_denot, Hb, Hb0.
      assert (H1 : 0 <= byte_at c 1 < 256) by (unfold byte_at; pose proof (bv_unsigned_in_range 8 (nth 1 c (Z_to_bv 8 0))) as X; unfold bv_modulus in X; cbn in X; lia).
      assert (H0 : 0 <= byte_at c 0 < 256) by (unfold byte_at; pose proof (bv_unsigned_in_range 8 (nth 0 c (Z_to_bv 8 0))) as X; unfold bv_modulus in X; cbn in X; lia).
      rewrite (swrap8_big _ H1). unfold cfg_word.
      destruct (Z.ltb_spec (byte_at c 1) 128); cbn [negb]; symmetry; [apply Z.leb_gt | apply Z.leb_le]; lia. }
    unfold TT0. rewrite Hneg, Hcalls, Hcnt.
    eapply t_eq_trans; [|exact (t_target_ht_split c fs')].
    unfold TGT. rewrite W1_line.
    replace (ht_calls c - 1)%nat with (Init.Nat.pred (ht_calls c)) by lia. rewrite W1_lines.
    (* [comment removed for export] *)
    apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Theorem ttk_target : forall E M fs', SV E M -> 65536 <= flen c <= 2 ^ 26 - 1 -> t_eq (TTK E fs') (t_target_ht c fs').
  Proof.
    intros E M fs' HS HF.
    assert (Hfl : flen c = Z.of_nat (length c)) by (unfold flen; change (2 ^ 26) with 67108864 in *; unfold flen in HF; lia).
    assert (Hb : eb E 32%nat = AsanPlanSound.APS.chunk 0 c).
    { destruct HS as (_ & _ & _ & Hch). specialize (Hch 0%nat). change (JB + 0)%nat with 32%nat in Hch. exact Hch. }
    assert (Hb0 : forall i, (Z.of_nat i < 65536) -> ION.hbyte i (eb E 32%nat) = byte_at c i).
    { intros i Hi. rewrite Hb, chunk_same.   (* [comment removed for export] *)
      rewrite (hbyte_chunk0 i c Hi). reflexivity. }
    assert (Hcl : cl_of E = Z.of_nat (config_len c)).
    { unfold cl_of, e_cl. rewrite CFGX_denot. rewrite !Hb0 by (cbn; lia). unfold config_len, cfg_word.
      pose proof (Z.mod_pos_bound (byte_at c 0 + 256 * byte_at c 1) 32768 ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
    assert (Hcfg : Z.of_nat (config_len c) <= 32767).
    { unfold config_len, cfg_word. pose proof (Z.mod_pos_bound (byte_at c 0 + 256 * byte_at c 1) 32768 ltac:(lia)). rewrite Z2Nat.id by lia. lia. }
    assert (Hneg : ht_neg c = false).
    { unfold ht_neg, ht_payload_len, HDR_MIN. apply Nat.ltb_ge. unfold flen in HF. change (2 ^ 26) with 67108864 in HF. lia. }
    assert (Hcalls : calls_of E = ht_calls c).
    { unfold calls_of, ht_calls. rewrite Hcl. destruct (config_len c) as [|n] eqn:Hc; [reflexivity|].
      replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold e_cm. rewrite XCM_denot, Hb0 by (cbn; lia). pose proof (Z.mod_pos_bound (byte_at c 2) 4 ltac:(lia)). rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity. }
    unfold TTK. rewrite Hcalls.
    eapply t_eq_trans; [|exact (t_target_ht_split c fs')]. rewrite Hneg.
    unfold TGT. rewrite W1_line.
    replace (ht_calls c - 1)%nat with (Init.Nat.pred (ht_calls c)) by lia. rewrite W1_lines.
    apply t_eq_refl.
  Qed.
End Glue.
