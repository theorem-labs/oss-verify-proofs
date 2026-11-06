(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1rg X1rh X1re X1nv X1rb X1rf X1qt.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section DecodeSafe.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.

Variable KROOM : nat.
Hypothesis Hcal : forall X n m, 0 <= n -> 0 <= m -> n * m < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hnotify : forall X msg, msg_ok msg -> mspec (own X) (spx_notify msg) (fun _ => own X).

Definition sbd_ptrs (s : sbd_state ptr) : list ptr :=
[sbd_g0_mem s; sbd_g1_mem s; sbd_excBuf s; sbd_old_qlsp s; sbd_interp_qlpc s; sbd_pi_gain s; sbd_exc_rms s; sbd_mem_sp s; sbd_blk s].
Fixpoint dec_ptrs (d : dec_state ptr) : list ptr :=
match d with
| DecNB st => [nb_blk st]
| DecSB s low => dec_ptrs low ++ sbd_ptrs s
end.

Definition nb_wf (st : nb_state ptr) : Prop :=
0 <= nb_voc_offset st <= 143 /\ 0 <= nb_submodeID st <= 8 /\ 0 <= nb_pitch_gain_buf_idx st <= 2.
Fixpoint dec_wf (d : dec_state ptr) : Prop :=
match d with DecNB st => nb_wf st | DecSB s low => dec_wf low end.

Definition keeps {A} (X : list ptr) (m : M St A) (Q : A -> Prop) : Prop :=
mspec (own X) m (fun r s mo => own X s mo /\ Q r).

#[using="Type"] Lemma keeps_ret {A} X (a : A) (Q : A -> Prop) : Q a -> keeps X (mret a) Q.
Proof. intros H. unfold keeps. apply mspec_ret. intros s mo Ho. auto. Qed.

#[using="Type"] Lemma keeps_bind {A B} X (m : M St A) (f : A -> M St B) (Q1 : A -> Prop) (Q : B -> Prop) :
keeps X m Q1 -> (forall a, Q1 a -> keeps X (f a) Q) -> keeps X (mbind m f) Q.
Proof. intros Hm Hf. unfold keeps. eapply mspec_bind; [exact Hm|]. intros a. apply mspec_pure. intros Ha. apply Hf. exact Ha. Qed.

#[using="Type"] Lemma keeps_weaken {A} X (m : M St A) (Q Q' : A -> Prop) : keeps X m Q -> (forall a, Q a -> Q' a) -> keeps X m Q'.
Proof. intros Hm HQ. unfold keeps in *. eapply mspec_post; [exact Hm|]. intros a s mo [H1 H2]. auto. Qed.

#[using="Hnotify"] Lemma keeps_notify X msg : msg_ok msg -> keeps X (spx_notify msg) (fun _ => True).
Proof. intros Hm. unfold keeps. eapply mspec_post; [apply Hnotify; exact Hm|]. intros a s mo H. auto. Qed.

#[using="Type"] Lemma keeps_munr_false {A} X (Q : A -> Prop) : False -> keeps X munr Q.
Proof. intros []. Qed.

#[using="Type"] Lemma unpackM_keeps X (b : bits_st ptr) n : bits_ok b -> 0 <= n ->
keeps X (bits_unpack_unsigned_M b n)
(fun r => 0 <= fst r < 2 ^ n /\ bstep n b (snd r) /\
(sb_overflow b = 0 -> bits_pos b + n <= sb_nbBits b -> sb_overflow (snd r) = 0 /\ bits_pos (snd r) = bits_pos b + n)).
Proof.
intros Hok Hn. unfold bits_unpack_unsigned_M. destruct (speex_bits_unpack_unsigned b n) as [v b'] eqn:E.
apply keeps_ret. cbn. exact (unpack_bstep b n v b' Hok Hn E).
Qed.

#[using="Type"] Lemma peekM_keeps X (b : bits_st ptr) : bits_ok b -> keeps X (bits_peek_M b) (fun r => 0 <= fst r <= 1 /\ bstep 0 b (snd r)).
Proof.
intros Hok. unfold bits_peek_M. destruct (speex_bits_peek b) as [v b'] eqn:E. apply keeps_ret. cbn.
exact (peek_bstep b v b' Hok E).
Qed.

#[using="Type"] Lemma advanceM_keeps X (b : bits_st ptr) n : bits_ok b -> (sb_overflow b = 0 -> 0 <= bits_pos b + n) ->
keeps X (bits_advance_M b n) (fun b' => bstep n b b').
Proof. intros Hok Hp. unfold bits_advance_M. apply keeps_ret. apply advance_bstep; auto. Qed.

#[using="Type"] Lemma remainingM_keeps X (b : bits_st ptr) : bits_ok b -> keeps X (bits_remaining_M b) (fun r => r = speex_bits_remaining b).
Proof. intros Hok. unfold bits_remaining_M. apply keeps_ret. reflexivity. Qed.

Definition bsame (b b' : bits_st ptr) : Prop :=
bits_ok b' /\ sb_chars b' = sb_chars b /\ sb_nbBits b' = sb_nbBits b /\ sb_owner b' = sb_owner b /\ sb_buf_size b' = sb_buf_size b.
#[using="Type"] Lemma bstep_bsame k (b b' : bits_st ptr) : bstep k b b' -> bsame b b'.
Proof. intros (O & C & N & W & S & _). unfold bsame. auto. Qed.
#[using="Type"] Lemma bsame_refl (b : bits_st ptr) : bits_ok b -> bsame b b.
Proof. intros H. unfold bsame. auto. Qed.
#[using="Type"] Lemma bsame_trans (b b1 b2 : bits_st ptr) : bsame b b1 -> bsame b1 b2 -> bsame b b2.
Proof. intros (O1 & C1 & N1 & W1 & S1) (O2 & C2 & N2 & W2 & S2). unfold bsame. rewrite C2, N2, W2, S2. auto. Qed.
#[using="Type"] Lemma bsame_ok (b b' : bits_st ptr) : bsame b b' -> bits_ok b'.
Proof. intros (O & _). exact O. Qed.

Local Abbreviation unpackM := (@bits_unpack_unsigned_M St ptr).
Local Abbreviation peekM := (@bits_peek_M St ptr).
Local Abbreviation advanceM := (@bits_advance_M St ptr).
Local Abbreviation remainingM := (@bits_remaining_M St ptr).

Definition consumes X (m : M St (bits_st ptr)) (b : bits_st ptr) : Prop := keeps X m (fun b' => bstep 0 b b').
Definition consumes2 X (m : M St (Z * bits_st ptr)) (b : bits_st ptr) (P : Z -> Prop) : Prop :=
keeps X m (fun r => P (fst r) /\ bstep 0 b (snd r)).

#[using="Type"] Lemma unpack_consumes2 X (b : bits_st ptr) n : bits_ok b -> 0 <= n ->
consumes2 X (unpackM b n) b (fun v => 0 <= v < 2 ^ n).
Proof.
intros Hok Hn. unfold consumes2. eapply keeps_weaken; [apply unpackM_keeps; auto|].
intros [v b'] (Hv & Hs & _). cbn in *. split; [exact Hv|]. eapply bstep_le; [exact Hn| exact Hs].
Qed.

#[using="Type"] Lemma bits_pos_nonneg (b : bits_st ptr) : bits_ok b -> 0 <= bits_pos b.
Proof. intros H. unfold bits_ok, bits_pos in *. lia. Qed.

#[using="Type"] Lemma bstep_ok k (b b' : bits_st ptr) : bstep k b b' -> bits_ok b'.
Proof. intros (O & _). exact O. Qed.
#[using="Type"] Lemma bstep_nb k (b b' : bits_st ptr) : bstep k b b' -> sb_nbBits b' = sb_nbBits b.
Proof. intros (_ & _ & N & _). exact N. Qed.
#[using="Type"] Lemma bstep_pos k (b b' : bits_st ptr) : bstep k b b' -> sb_overflow b' = 0 -> bits_pos b + k <= bits_pos b'.
Proof. intros (_ & _ & _ & _ & _ & _ & P). exact P. Qed.
#[using="Type"] Lemma bstep00 (b b1 b2 : bits_st ptr) : bstep 0 b b1 -> bstep 0 b1 b2 -> bstep 0 b b2.
Proof. intros H1 H2. eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia. Qed.

#[using="Type"] Lemma speex_default_user_handler_spec X (b : bits_st ptr) : bits_ok b ->
consumes2 X (speex_default_user_handler unpackM advanceM b) b (fun r => r = 0).
Proof.
intros Hok. unfold speex_default_user_handler, consumes2.
eapply keeps_bind; [apply (unpack_consumes2 X b 4 Hok); lia|]. intros [rq b1] [Hrq Hs1]; cbn in Hrq, Hs1.
eapply keeps_bind.
{ apply advanceM_keeps; [exact (bstep_ok _ _ _ Hs1)|]. intros _. pose proof (bits_pos_nonneg b1 (bstep_ok _ _ _ Hs1)). lia. }
intros b2 Hs2. apply keeps_ret. cbn. split; [reflexivity|].
eapply bstep_le; [| eapply bstep_trans; [exact Hs1| exact Hs2]]. lia.
Qed.

#[using="Type"] Lemma speex_std_stereo_request_handler_spec X (b : bits_st ptr) : bits_ok b ->
consumes2 X (speex_std_stereo_request_handler unpackM b) b (fun r => r = 0).
Proof.
intros Hok. unfold speex_std_stereo_request_handler, consumes2.
eapply keeps_bind; [apply (unpack_consumes2 X b 1 Hok); lia|]. intros [v1 b1] [_ Hs1]; cbn in Hs1.
eapply keeps_bind; [apply (unpack_consumes2 X b1 5 (bstep_ok _ _ _ Hs1)); lia|]. intros [v2 b2] [_ Hs2]; cbn in Hs2.
eapply keeps_bind; [apply (unpack_consumes2 X b2 2 (bstep_ok _ _ _ Hs2)); lia|]. intros [v3 b3] [_ Hs3]; cbn in Hs3.
apply keeps_ret. cbn. split; [reflexivity|].
eapply bstep_le; [| eapply bstep_trans; [exact Hs1| eapply bstep_trans; [exact Hs2| exact Hs3]]]. lia.
Qed.

#[using="Type"] Lemma inband_skip_bits_pos id : 1 <= inband_skip_bits id.
Proof. unfold inband_skip_bits. repeat (destruct (_ <? _)); lia. Qed.

#[using="Type"] Lemma speex_inband_handler_spec X (b : bits_st ptr) cb : bits_ok b ->
consumes2 X (speex_inband_handler unpackM advanceM b cb) b (fun r => r = 0).
Proof.
intros Hok. unfold speex_inband_handler, consumes2.
eapply keeps_bind; [apply (unpack_consumes2 X b 4 Hok); lia|]. intros [id b1] [Hid Hs1]; cbn in Hid, Hs1. cbn.
destruct (cb && (id =? SPEEX_INBAND_STEREO)).
- eapply keeps_weaken; [apply speex_std_stereo_request_handler_spec; exact (bstep_ok _ _ _ Hs1)|].
intros [r b2] [Hr Hs2]; cbn in *. split; [exact Hr|]. eapply bstep_le; [| eapply bstep_trans; [exact Hs1| exact Hs2]]. lia.
- eapply keeps_bind.
{ apply advanceM_keeps; [exact (bstep_ok _ _ _ Hs1)|]. intros _.
pose proof (bits_pos_nonneg b1 (bstep_ok _ _ _ Hs1)). pose proof (inband_skip_bits_pos id). lia. }
intros b2 Hs2. apply keeps_ret. cbn. split; [reflexivity|].
eapply bstep_le; [| eapply bstep_trans; [exact Hs1| exact Hs2]]. pose proof (inband_skip_bits_pos id). lia.
Qed.

#[using="Type"] Lemma lsp_unquant_spec X k (b : bits_st ptr) : bits_ok b -> consumes X (lsp_unquant unpackM k b) b.
Proof.
intros Hok. unfold consumes.
destruct k; cbn.
-   change (keeps X _ _) with
(keeps X (' (id1, b0) <- unpackM b 6 ;; ' (id2, b1) <- unpackM b0 6 ;; ' (id3, b2) <- unpackM b1 6 ;; mret b2) (fun b' => bstep 0 b b')).
eapply keeps_bind; [apply (unpack_consumes2 X b 6 Hok); lia|]. intros [? b1] [_ H1]; cbn in H1.
eapply keeps_bind; [apply (unpack_consumes2 X b1 6 (bstep_ok _ _ _ H1)); lia|]. intros [? b2] [_ H2]; cbn in H2.
eapply keeps_bind; [apply (unpack_consumes2 X b2 6 (bstep_ok _ _ _ H2)); lia|]. intros [? b3] [_ H3]; cbn in H3.
apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H1| eapply bstep_trans; [exact H2| exact H3]]]. lia.
-
eapply keeps_bind; [apply (unpack_consumes2 X b 6 Hok); lia|]. intros [? b1] [_ H1]; cbn in H1.
eapply keeps_bind; [apply (unpack_consumes2 X b1 6 (bstep_ok _ _ _ H1)); lia|]. intros [? b2] [_ H2]; cbn in H2.
eapply keeps_bind; [apply (unpack_consumes2 X b2 6 (bstep_ok _ _ _ H2)); lia|]. intros [? b3] [_ H3]; cbn in H3.
eapply keeps_bind; [apply (unpack_consumes2 X b3 6 (bstep_ok _ _ _ H3)); lia|]. intros [? b4] [_ H4]; cbn in H4.
eapply keeps_bind; [apply (unpack_consumes2 X b4 6 (bstep_ok _ _ _ H4)); lia|]. intros [? b5] [_ H5]; cbn in H5.
apply keeps_ret.
eapply bstep_le; [| eapply bstep_trans; [exact H1| eapply bstep_trans; [exact H2| eapply bstep_trans; [exact H3| eapply bstep_trans; [exact H4| exact H5]]]]]. lia.
-
eapply keeps_bind; [apply (unpack_consumes2 X b 6 Hok); lia|]. intros [? b1] [_ H1]; cbn in H1.
eapply keeps_bind; [apply (unpack_consumes2 X b1 6 (bstep_ok _ _ _ H1)); lia|]. intros [? b2] [_ H2]; cbn in H2.
apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia.
Qed.

#[using="Type"] Lemma pitch_unquant_3tap_spec X par start (b : bits_st ptr) : bits_ok b -> 0 <= ltp_pitch_bits par -> 0 <= ltp_gain_bits par ->
consumes2 X (pitch_unquant_3tap unpackM par start b) b (fun p => start <= p < start + 2 ^ ltp_pitch_bits par).
Proof.
intros Hok Hp Hg. unfold pitch_unquant_3tap, consumes2.
eapply keeps_bind; [apply (unpack_consumes2 X b _ Hok Hp)|]. intros [v b1] [Hv H1]; cbn in Hv, H1.
eapply keeps_bind; [apply (unpack_consumes2 X b1 _ (bstep_ok _ _ _ H1) Hg)|]. intros [g b2] [_ H2]; cbn in H2.
apply keeps_ret. cbn. split; [lia|]. eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia.
Qed.

#[using="Type"] Lemma ltp_unquant_spec X k start (b : bits_st ptr) : bits_ok b ->
match k with LtpPitchUnquant3tap par => 0 <= ltp_pitch_bits par <= 7 /\ 0 <= ltp_gain_bits par | _ => True end ->
consumes2 X (ltp_unquant unpackM k start b) b (fun p => start <= p <= start + 127).
Proof.
intros Hok Hk. destruct k as [|par]; cbn.
- unfold forced_pitch_unquant, consumes2. apply keeps_ret. cbn. split; [lia| apply bstep_refl; exact Hok].
- destruct Hk as [Hp Hg]. unfold consumes2. eapply keeps_weaken; [apply pitch_unquant_3tap_spec; auto; lia|].
intros [p b'] [Hr Hs]; cbn in *. split; [|exact Hs].
assert (2 ^ ltp_pitch_bits par <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2^7) with 128 in H. lia.
Qed.

#[using="Type"] Lemma split_cb_read_spec X n hs sbits : 0 <= sbits -> forall (b : bits_st ptr), bits_ok b ->
consumes X (split_cb_read unpackM n hs sbits b) b.
Proof.
intros Hsb. induction n as [|n IH]; intros b Hok; cbn.
- unfold consumes. apply keeps_ret. apply bstep_refl. exact Hok.
- unfold consumes. eapply keeps_bind with (Q1 := fun b1 => bstep 0 b b1).
+ destruct (negb (hs =? 0)).
* eapply keeps_bind; [apply (unpack_consumes2 X b 1 Hok); lia|]. intros [sg b1] [_ H1]; cbn in H1. apply keeps_ret. exact H1.
* apply keeps_ret. apply bstep_refl. exact Hok.
+ intros b1 H1. eapply keeps_bind; [apply (unpack_consumes2 X b1 sbits (bstep_ok _ _ _ H1) Hsb)|].
intros [ind b2] [_ H2]; cbn in H2. eapply keeps_weaken; [apply IH; exact (bstep_ok _ _ _ H2)|].
intros b3 H3. eapply bstep_le; [| eapply bstep_trans; [exact H1| eapply bstep_trans; [exact H2| exact H3]]]. lia.
Qed.

#[using="Type"] Lemma innovation_unquant_spec X k (b : bits_st ptr) : bits_ok b ->
match k with InnovSplitCbShapeSignUnquant par => 0 <= scb_shape_bits par | _ => True end ->
consumes X (innovation_unquant unpackM k b) b.
Proof.
intros Hok Hk. destruct k as [|par]; cbn.
- unfold noise_codebook_unquant, consumes. apply keeps_ret. apply bstep_refl. exact Hok.
- unfold split_cb_shape_sign_unquant. apply split_cb_read_spec; auto.
Qed.

Definition sm_params_ok (sm : submode) : Prop :=
match sm_ltp_unquant sm with Some (LtpPitchUnquant3tap par) => 0 <= ltp_pitch_bits par <= 7 /\ 0 <= ltp_gain_bits par | _ => True end /\
match sm_innovation_unquant sm with Some (InnovSplitCbShapeSignUnquant par) => 0 <= scb_shape_bits par | _ => True end.

#[using="Type"] Lemma submode_at_In tbl i sm : submode_at tbl i = Some sm -> In (Some sm) tbl.
Proof.
unfold submode_at. destruct (i <? 0); [discriminate|]. intros H.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length tbl)) as [L|L].
- rewrite <- H. apply nth_In. exact L.
- rewrite nth_overflow in H by exact L. discriminate.
Qed.

#[using="Type"] Lemma nb_submodes_params i sm : submode_at nb_submodes i = Some sm -> sm_params_ok sm /\ sm_ltp_unquant sm <> None /\ sm_innovation_unquant sm <> None.
Proof.
intros H. apply submode_at_In in H. cbn in H.
repeat (destruct H as [H|H]; [try discriminate H; injection H as <-; cbn; repeat split; try discriminate; cbn; try lia|]).
destruct H.
Qed.

#[using="Type"] Lemma sb_submodes_params m i sm : submode_at (sbm_submodes m) i = Some sm -> sm_params_ok sm.
Proof.
intros H. apply submode_at_In in H. destruct m; cbn in H;
repeat (destruct H as [H|H]; [try discriminate H; injection H as <-; cbn; repeat split; cbn; try lia|]); destruct H.
Qed.

#[using="Type"] Lemma wb_skip_table_nonneg_at i : 0 <= i < 8 -> 0 <= znth wb_skip_table i.
Proof.
intros Hi. pose proof wb_skip_table_nonneg as F. rewrite Forall_forall in F. apply F. apply znth_range.
unfold zlength. cbn [length wb_skip_table]. lia.
Qed.

#[using="Type"] Lemma nb_skip_wb_layer_spec X (b : bits_st ptr) : bits_ok b -> sb_overflow b = 0 -> bits_pos b + 4 <= sb_nbBits b -> 1 <= bits_pos b ->
keeps X (nb_skip_wb_layer unpackM advanceM b) (fun b' => bstep (-1) b b').
Proof.
intros Hok Hz Hle Hp1. unfold nb_skip_wb_layer, SB_SUBMODE_BITS.
eapply keeps_bind; [apply unpackM_keeps; [exact Hok| lia]|]. intros [sm b1] (Hsm & H1 & Hsucc); cbn in Hsm, H1, Hsucc.
destruct (Hsucc Hz ltac:(lia)) as [Hz1 Hp1'].
eapply keeps_weaken.
- apply advanceM_keeps; [exact (bstep_ok _ _ _ H1)|]. intros _. pose proof (wb_skip_table_nonneg_at sm ltac:(lia)). rewrite Hp1'. lia.
- intros b2 H2. pose proof (wb_skip_table_nonneg_at sm ltac:(lia)).
eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia.
Qed.

Definition search_post (b : bits_st ptr) (r : nb_search_res) : Prop :=
match r with NbReturn _ b' => bsame b b' | NbMode m b' => 0 <= m <= 8 /\ bsame b b' end.

#[using="Type"] Lemma bsame_of_bstep_chain (b b1 b2 : bits_st ptr) k : bsame b b1 -> bstep k b1 b2 -> bsame b b2.
Proof. intros H1 H2. eapply bsame_trans; [exact H1| exact (bstep_bsame _ _ _ H2)]. Qed.

#[using="Hnotify"] Lemma nb_mode_search_spec X st : forall fuel (b : bits_st ptr), bits_ok b -> bmeas b + 1 <= Z.of_nat fuel ->
keeps X (nb_mode_search spx_notify unpackM advanceM remainingM fuel st b) (search_post b).
Proof.
induction fuel as [|fuel IH]; intros b Hok Hfuel.
{ pose proof (bmeas_nonneg b Hok). cbn in Hfuel. lia. }
cbn [nb_mode_search].
eapply keeps_bind; [apply remainingM_keeps; exact Hok|]. intros r ->.
destruct (Z.ltb_spec (speex_bits_remaining b) 5) as [Hr|Hr].
{ apply keeps_ret. cbn. apply bsame_refl. exact Hok. }
destruct (remaining_ge b _ Hok eq_refl ltac:(lia)) as [Hz Hrem].
eapply keeps_bind; [apply unpackM_keeps; [exact Hok| lia]|]. intros [w b1] (Hw & H1 & S1); cbn in Hw, H1, S1.
destruct (S1 Hz ltac:(lia)) as [Hz1 Hp1].

eapply keeps_bind with (Q1 := fun wb => match wb with inl b' => bstep 1 b b' | inr res => search_post b res end).
{ destruct (negb (w =? 0)).
- eapply keeps_bind; [apply nb_skip_wb_layer_spec; [exact (bstep_ok _ _ _ H1)| exact Hz1| rewrite Hp1, (bstep_nb _ _ _ H1); lia| rewrite Hp1; pose proof (bits_pos_nonneg b Hok); lia]|].
intros b2 H2.
eapply keeps_bind; [apply remainingM_keeps; exact (bstep_ok _ _ _ H2)|]. intros r2 ->.
destruct (Z.ltb_spec (speex_bits_remaining b2) 5) as [Hr2|Hr2].
{ apply keeps_ret. cbn. eapply bsame_trans; [exact (bstep_bsame _ _ _ H1)| exact (bstep_bsame _ _ _ H2)]. }
destruct (remaining_ge b2 _ (bstep_ok _ _ _ H2) eq_refl ltac:(lia)) as [Hz2 Hrem2].
eapply keeps_bind; [apply unpackM_keeps; [exact (bstep_ok _ _ _ H2)| lia]|]. intros [w3 b3] (Hw3 & H3 & S3); cbn in Hw3, H3, S3.
destruct (S3 Hz2 ltac:(lia)) as [Hz3 Hp3].
destruct (negb (w3 =? 0)).
+ eapply keeps_bind; [apply nb_skip_wb_layer_spec; [exact (bstep_ok _ _ _ H3)| exact Hz3| rewrite Hp3, (bstep_nb _ _ _ H3); lia| rewrite Hp3; pose proof (bits_pos_nonneg b2 (bstep_ok _ _ _ H2)); lia]|].
intros b4 H4.
eapply keeps_bind; [apply unpackM_keeps; [exact (bstep_ok _ _ _ H4)| lia]|]. intros [w5 b5] (Hw5 & H5 & _); cbn in Hw5, H5.
destruct (negb (w5 =? 0)).
* eapply keeps_bind; [apply keeps_notify; msg_ok_tac|]. intros _ _. apply keeps_ret. cbn.
eapply bsame_of_bstep_chain; [| exact H5]. eapply bsame_of_bstep_chain; [| exact H4].
eapply bsame_of_bstep_chain; [| exact H3]. eapply bsame_of_bstep_chain; [| exact H2]. exact (bstep_bsame _ _ _ H1).
* apply keeps_ret. cbn.
eapply bstep_le; [| eapply bstep_trans; [exact H1| eapply bstep_trans; [exact H2| eapply bstep_trans; [exact H3| eapply bstep_trans; [exact H4| exact H5]]]]]. lia.
+ apply keeps_ret. cbn. eapply bstep_le; [| eapply bstep_trans; [exact H1| eapply bstep_trans; [exact H2| exact H3]]]. lia.
- apply keeps_ret. cbn. exact H1. }
intros [b' | res]; [| intros Hres; apply keeps_ret; exact Hres].
intros H'.
eapply keeps_bind; [apply remainingM_keeps; exact (bstep_ok _ _ _ H')|]. intros r' ->.
destruct (Z.ltb_spec (speex_bits_remaining b') 4) as [Hr'|Hr'].
{ apply keeps_ret. cbn. exact (bstep_bsame _ _ _ H'). }
destruct (remaining_ge b' _ (bstep_ok _ _ _ H') eq_refl ltac:(lia)) as [Hz' Hrem'].
eapply keeps_bind; [apply unpackM_keeps; [exact (bstep_ok _ _ _ H')| lia]|]. intros [m bm] (Hm & Hbm & Sm); cbn in Hm, Hbm, Sm.
destruct (Sm Hz' ltac:(lia)) as [Hzm Hpm].
assert (Hbm5 : bstep 5 b bm) by (eapply bstep_le; [| eapply bstep_trans; [exact H'| exact Hbm]]; lia).

assert (REC : forall b'', bstep 0 bm b'' -> keeps X (nb_mode_search spx_notify unpackM advanceM remainingM fuel st b'') (search_post b)).
{ intros b'' H''. pose proof (bstep_trans _ _ _ _ _ Hbm5 H'') as Hb''.
eapply keeps_weaken; [apply IH; [exact (bstep_ok _ _ _ Hb'')|]|].
- destruct (bmeas_bstep _ _ _ Hok Hb'') as [E|[_ E]]; [rewrite E|].
+ cbn in Hfuel. unfold bmeas in Hfuel. rewrite (proj2 (Z.eqb_eq _ _) Hz) in Hfuel. lia.
+ unfold bmeas in Hfuel |- *. rewrite (proj2 (Z.eqb_eq _ _) Hz) in Hfuel. unfold bmeas in E. rewrite (proj2 (Z.eqb_eq _ _) Hz) in E.
destruct (sb_overflow b'' =? 0); lia.
- intros res Hres. destruct res as [rc bb|mm bb]; cbn in *.
+ eapply bsame_trans; [exact (bstep_bsame _ _ _ Hb'')|]. exact Hres.
+ destruct Hres as [Hmm Hs]. split; [exact Hmm|]. eapply bsame_trans; [exact (bstep_bsame _ _ _ Hb'')| exact Hs]. }
change (2^4) with 16 in Hm.
destruct (Z.eqb_spec m 15) as [->|N15]. { apply keeps_ret. cbn. exact (bstep_bsame _ _ _ Hbm5). }
destruct (Z.eqb_spec m 14) as [->|N14].
{ eapply keeps_bind; [apply speex_inband_handler_spec; exact (bstep_ok _ _ _ Hbm)|]. intros [ret bh] [Hret Hh]; cbn in Hret, Hh. subst ret. cbn.
apply REC. exact Hh. }
destruct (Z.eqb_spec m 13) as [->|N13].
{ eapply keeps_bind; [apply speex_default_user_handler_spec; exact (bstep_ok _ _ _ Hbm)|]. intros [ret bh] [Hret Hh]; cbn in Hret, Hh. subst ret. cbn.
apply REC. exact Hh. }
destruct (Z.ltb_spec 8 m).
{ eapply keeps_bind; [apply keeps_notify; msg_ok_tac|]. intros _ _. apply keeps_ret. cbn. exact (bstep_bsame _ _ _ Hbm5). }
apply keeps_ret. cbn. split; [lia| exact (bstep_bsame _ _ _ Hbm5)].
Qed.

Definition nb_rel (st st' : nb_state ptr) : Prop := nb_blk st' = nb_blk st /\ nb_wf st'.

#[using="Type"] Lemma nb_decode_subframe_spec X sm ol_pitch sub (st : nb_state ptr) (b : bits_st ptr) :
sm_params_ok sm -> sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
nb_wf st -> (nb_submodeID st = 1 -> 17 <= ol_pitch <= 144) -> bits_ok b ->
keeps X (nb_decode_subframe unpackM sm ol_pitch sub st b)
(fun r => nb_rel st (fst r) /\ nb_submodeID (fst r) = nb_submodeID st /\
nb_pitch_gain_buf_idx (fst r) = nb_pitch_gain_buf_idx st /\ bstep 0 b (snd r)).
Proof.
intros [Pl Pi] Hl Hi Hwf Hol Hok. unfold nb_decode_subframe.
destruct (sm_ltp_unquant sm) as [k|]; [|congruence].
eapply keeps_bind; [apply ltp_unquant_spec; [exact Hok| exact Pl]|]. intros [pitch b1] [_ H1]; cbn in H1.
eapply keeps_bind with (Q1 := fun b2 => bstep 0 b b2).
{ destruct (sm_have_subframe_gain sm =? 3).
- eapply keeps_bind; [apply (unpack_consumes2 X b1 3 (bstep_ok _ _ _ H1)); lia|]. intros [q b2] [_ H2]; cbn in H2.
apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia.
- destruct (sm_have_subframe_gain sm =? 1).
+ eapply keeps_bind; [apply (unpack_consumes2 X b1 1 (bstep_ok _ _ _ H1)); lia|]. intros [q b2] [_ H2]; cbn in H2.
apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia.
+ apply keeps_ret. exact H1. }
intros b2 H2.
destruct (sm_innovation_unquant sm) as [ki|]; [|congruence].
eapply keeps_bind; [apply innovation_unquant_spec; [exact (bstep_ok _ _ _ H2)| exact Pi]|]. intros b3 H3.
eapply keeps_bind with (Q1 := fun b4 => bstep 0 b b4).
{ destruct (negb (sm_double_codebook sm =? 0)).
- eapply keeps_weaken; [apply innovation_unquant_spec; [exact (bstep_ok _ _ _ H3)| exact Pi]|].
intros b4 H4. eapply bstep_le; [| eapply bstep_trans; [exact H2| eapply bstep_trans; [exact H3| exact H4]]]. lia.
- apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H2| exact H3]]. lia. }
intros b4 H4.
eapply keeps_bind with (Q1 := fun st' => nb_rel st st' /\ nb_submodeID st' = nb_submodeID st /\
nb_pitch_gain_buf_idx st' = nb_pitch_gain_buf_idx st).
{ destruct (Z.eqb_spec (nb_submodeID st) 1) as [E1|E1].
- specialize (Hol E1). pose proof Hwf as (Hv & Hsid & Hpg).
destruct (voc_loop_inv (nb_voc_offset st) ol_pitch Hv Hol) as (v' & Ev & Hv').
rewrite Ev. apply keeps_ret. unfold nb_rel, nb_wf. cbn. repeat split; auto; lia.
- apply keeps_ret. unfold nb_rel. repeat split; auto; apply Hwf. }
intros st' (Hrel & Hid & Hpg). apply keeps_ret. cbn. split; [exact Hrel|]. split; [exact Hid|]. split; [exact Hpg| exact H4].
Qed.

#[using="Type"] Lemma nb_decode_subframes_spec X sm ol_pitch : sm_params_ok sm -> sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
forall n sub (st : nb_state ptr) (b : bits_st ptr),
nb_wf st -> (nb_submodeID st = 1 -> 17 <= ol_pitch <= 144) -> bits_ok b ->
keeps X (nb_decode_subframes unpackM n sub sm ol_pitch st b)
(fun r => nb_rel st (fst r) /\ nb_submodeID (fst r) = nb_submodeID st /\
nb_pitch_gain_buf_idx (fst r) = nb_pitch_gain_buf_idx st /\ bstep 0 b (snd r)).
Proof.
intros P Hl Hi. induction n as [|n IH]; intros sub st b Hwf Hol Hok; cbn.
- apply keeps_ret. cbn. split; [split; [reflexivity| exact Hwf]|]. split; [reflexivity|]. split; [reflexivity| apply bstep_refl; exact Hok].
- eapply keeps_bind; [apply nb_decode_subframe_spec; auto|]. intros [st1 b1] ([Hb1 Hw1] & Hid1 & Hpg1 & Hs1); cbn in Hb1, Hw1, Hid1, Hpg1, Hs1.
eapply keeps_weaken; [apply IH; [exact Hw1| rewrite Hid1; exact Hol| exact (bstep_ok _ _ _ Hs1)]|].
intros [st2 b2] ([Hb2 Hw2] & Hid2 & Hpg2 & Hs2); cbn in *. split; [split; [congruence| exact Hw2]|].
split; [congruence|]. split; [congruence|]. eapply bstep_le; [| eapply bstep_trans; [exact Hs1| exact Hs2]]. lia.
Qed.

#[using="Type"] Lemma nb_submode1_at : forall sm, submode_at nb_submodes 1 = Some sm -> (sm_lbr_pitch sm =? -1) = false.
Proof. intros sm H. cbn in H. injection H as <-. reflexivity. Qed.

#[using="Hnotify"] Lemma nb_decode_spec X (st : nb_state ptr) (b : bits_st ptr) : nb_wf st -> bits_ok b ->
keeps X (nb_decode spx_notify unpackM advanceM remainingM st b)
(fun r => let '(rc, st', b') := r in nb_rel st st' /\ bsame b b').
Proof.
intros Hwf Hok. unfold nb_decode.
eapply keeps_bind with (Q1 := search_post b).
{ destruct (negb (nb_encode_submode st =? 0)).
- apply nb_mode_search_spec; [exact Hok|]. unfold nb_search_fuel, bmeas.
pose proof Hok as (_ & _ & Hnb & _ & _ & Hp & _). pose proof (bits_pos_nonneg b Hok).
destruct (sb_overflow b =? 0); lia.
- apply keeps_ret. cbn. split; [apply Hwf| apply bsame_refl; exact Hok]. }
intros [rc b0 | m b0].
{ intros Hs. apply keeps_ret. split; [split; [reflexivity| exact Hwf]| exact Hs]. }
intros [Hm Hs0]. cbn beta iota zeta. cbn [nb_submodeID set_nb_submodeID].
destruct (submode_at nb_submodes m) as [sm|] eqn:Esm.
2:{ apply keeps_ret. split; [|exact Hs0]. split; [reflexivity|]. unfold nb_wf in *; cbn. lia. }
pose proof (nb_submodes_params m sm Esm) as (Psm & Hl & Hi).
pose proof (bsame_ok _ _ Hs0) as Hok0.
eapply keeps_bind; [apply lsp_unquant_spec; exact Hok0|]. intros b1 H1.

eapply keeps_bind with (Q1 := fun r => ((sm_lbr_pitch sm =? -1) = false -> 17 <= fst r <= 144) /\ bstep 0 b0 (snd r)).
{ destruct (sm_lbr_pitch sm =? -1) eqn:El; cbn [negb].
- apply keeps_ret. cbn. split; [intros; congruence| exact H1].
- eapply keeps_bind; [apply (unpack_consumes2 X b1 7 (bstep_ok _ _ _ H1)); lia|]. intros [p b2] [Hp H2]; cbn in Hp, H2.
apply keeps_ret. cbn. change (2^7) with 128 in Hp. unfold NB_PITCH_START. split; [lia|].
eapply bstep_le; [| eapply bstep_trans; [exact H1| exact H2]]. lia. }
intros [ol_pitch b2] [Hol H2]; cbn in Hol, H2.
eapply keeps_bind with (Q1 := fun b3 => bstep 0 b0 b3).
{ destruct (negb (sm_forced_pitch_gain sm =? 0)).
- eapply keeps_bind; [apply (unpack_consumes2 X b2 4 (bstep_ok _ _ _ H2)); lia|]. intros [q b3] [_ H3]; cbn in H3.
apply keeps_ret. eapply bstep_le; [| eapply bstep_trans; [exact H2| exact H3]]. lia.
- apply keeps_ret. exact H2. }
intros b3 H3.
eapply keeps_bind; [apply (unpack_consumes2 X b3 5 (bstep_ok _ _ _ H3)); lia|]. intros [qe b4] [_ H4']; cbn in H4'.
pose proof (bstep00 _ _ _ H3 H4') as H4.
set (st1 := set_nb_submodeID st m).
assert (W1 : nb_wf st1 /\ nb_blk st1 = nb_blk st /\ nb_submodeID st1 = m /\ nb_pitch_gain_buf_idx st1 = nb_pitch_gain_buf_idx st).
{ subst st1. unfold nb_wf in *; cbn. repeat split; try lia; reflexivity. }
destruct W1 as (W1 & B1 & I1 & G1).
eapply keeps_bind with (Q1 := fun r => (nb_wf (fst r) /\ nb_blk (fst r) = nb_blk st /\ nb_submodeID (fst r) = m /\
nb_pitch_gain_buf_idx (fst r) = nb_pitch_gain_buf_idx st) /\ bstep 0 b0 (snd r)).
{ destruct (m =? 1).
- eapply keeps_bind; [apply (unpack_consumes2 X b4 4 (bstep_ok _ _ _ H4)); lia|]. intros [extra b5] [_ H5]; cbn in H5.
apply keeps_ret. cbn. split; [| eapply bstep_le; [| eapply bstep_trans; [exact H4| exact H5]]; lia].
unfold nb_wf in *; cbn. repeat split; try lia; auto.
- apply keeps_ret. cbn. split; [| exact H4]. repeat split; auto; apply W1. }
intros [st2 b5] ((W2 & B2 & I2 & G2) & H5); cbn in W2, B2, I2, G2, H5.
set (st3 := if 1 <? nb_submodeID st2 then set_nb_dtx_enabled st2 0 else st2).
assert (W3 : nb_wf st3 /\ nb_blk st3 = nb_blk st /\ nb_submodeID st3 = m /\ nb_pitch_gain_buf_idx st3 = nb_pitch_gain_buf_idx st).
{ subst st3. destruct (1 <? nb_submodeID st2); [| split; [exact W2| repeat split; auto]]. unfold nb_wf in *; cbn. repeat split; try lia; auto. }
destruct W3 as (W3 & B3 & I3 & G3).
eapply keeps_bind.
{ apply nb_decode_subframes_spec; [exact Psm| exact Hl| exact Hi| exact W3| | exact (bstep_ok _ _ _ H5)].
intros E1. apply Hol. apply nb_submode1_at. rewrite <- Esm. rewrite <- I3, E1. reflexivity. }
intros [st4 b6] ([B4 W4] & I4 & G4 & H6); cbn in B4, W4, I4, G4, H6.
apply keeps_ret. split.
- split; [cbn; congruence|]. unfold nb_wf in *; cbn. rewrite G4, G3.
destruct (Z.ltb_spec 2 (nb_pitch_gain_buf_idx st + 1)); lia.
- eapply bsame_trans; [exact Hs0|]. eapply bstep_bsame. eapply bstep_trans; [exact H5| exact H6].
Qed.

Definition dec_rel (d d' : dec_state ptr) : Prop :=
dec_ptrs d' = dec_ptrs d /\ dec_wf d' /\ dec_depth d' = dec_depth d.

#[using="Type"] Lemma dec_rel_refl d : dec_wf d -> dec_rel d d.
Proof. intros H. unfold dec_rel. auto. Qed.
#[using="Type"] Lemma dec_rel_trans d1 d2 d3 : dec_rel d1 d2 -> dec_rel d2 d3 -> dec_rel d1 d3.
Proof. intros (A1 & B1 & C1) (A2 & B2 & C2). unfold dec_rel. rewrite A2, C2. auto. Qed.

#[using="Type"] Lemma nb_decoder_ctl_rel (st : nb_state ptr) r :
nb_blk (snd (nb_decoder_ctl st r)) = nb_blk st /\ (nb_wf st -> nb_wf (snd (nb_decoder_ctl st r))).
Proof. destruct r; cbn; unfold nb_wf; cbn; auto. Qed.

#[using="Type"] Lemma speex_decoder_ctl_rel : forall (d : dec_state ptr) r, dec_wf d -> dec_rel d (snd (speex_decoder_ctl d r)).
Proof.
induction d as [st | st low IH]; intros r Hwf.
- cbn. pose proof (nb_decoder_ctl_rel st r) as [A B]. destruct (nb_decoder_ctl st r) as [v st']; cbn in *.
unfold dec_rel; cbn. rewrite A. auto.
- cbn in Hwf.
assert (G : forall q, dec_rel low (snd (speex_decoder_ctl low q))) by (intros q; apply IH; exact Hwf).
destruct r; cbn [speex_decoder_ctl snd]; try (apply dec_rel_refl; exact Hwf);
try (unfold dec_rel; cbn; split; [reflexivity| split; [exact Hwf| reflexivity]]);
match goal with
| |- context [speex_decoder_ctl low ?q] =>
generalize (G q); destruct (speex_decoder_ctl low q) as [v' low']
end; cbn [fst snd]; intros (A & B & C); unfold dec_rel; cbn; rewrite A; rewrite C;
(split; [reflexivity| split; [exact B| reflexivity]]).
Qed.

#[using="Type"] Lemma ctl_cases (d : dec_state ptr) r : dec_wf d ->
exists v d', speex_decoder_ctl d r = (v, d') /\ dec_rel d d'.
Proof.
intros H. pose proof (speex_decoder_ctl_rel d r H) as R. destruct (speex_decoder_ctl d r) as [v d']. exists v, d'. auto.
Qed.

#[using="Type"] Lemma sb_decode_subframe_spec X sm (b : bits_st ptr) : sm_params_ok sm -> bits_ok b ->
consumes X (sb_decode_subframe unpackM sm b) b.
Proof.
intros [_ Pi] Hok. unfold sb_decode_subframe, consumes.
destruct (sm_innovation_unquant sm) as [k|].
- eapply keeps_bind; [apply (unpack_consumes2 X b 4 Hok); lia|]. intros [qgc b1] [_ H1]; cbn in H1.
eapply keeps_bind; [apply innovation_unquant_spec; [exact (bstep_ok _ _ _ H1)| exact Pi]|]. intros b2 H2.
destruct (negb (sm_double_codebook sm =? 0)).
+ eapply keeps_weaken; [apply innovation_unquant_spec; [exact (bstep_ok _ _ _ H2)| exact Pi]|].
intros b3 H3. eapply bstep00; [exact H1| eapply bstep00; [exact H2| exact H3]].
+ apply keeps_ret. eapply bstep00; [exact H1| exact H2].
- eapply keeps_bind; [apply (unpack_consumes2 X b 5 Hok); lia|]. intros [q b1] [_ H1]; cbn in H1. apply keeps_ret. exact H1.
Qed.

#[using="Type"] Lemma sb_decode_subframes_spec X sm : sm_params_ok sm -> forall n (b : bits_st ptr), bits_ok b ->
consumes X (sb_decode_subframes unpackM n sm b) b.
Proof.
intros P. induction n as [|n IH]; intros b Hok; cbn; unfold consumes.
- apply keeps_ret. apply bstep_refl. exact Hok.
- eapply keeps_bind; [apply sb_decode_subframe_spec; auto|]. intros b1 H1.
eapply keeps_weaken; [apply IH; exact (bstep_ok _ _ _ H1)|]. intros b2 H2. eapply bstep00; eauto.
Qed.

#[using="Type"] Lemma sbd_ptrs_set_submodeID (st : sbd_state ptr) v : sbd_ptrs (set_sbd_submodeID st v) = sbd_ptrs st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma sbd_ptrs_set_first (st : sbd_state ptr) v : sbd_ptrs (set_sbd_first st v) = sbd_ptrs st.
Proof. reflexivity. Qed.

Definition low_decode_ok X (n : nat) : Prop :=
forall (low : dec_state ptr) (b : bits_st ptr) out, dec_depth low = n -> dec_wf low -> bits_ok b ->
keeps X (speex_decode_n spx_notify unpackM peekM advanceM remainingM n low b out)
(fun r => let '(rc, low', b') := r in dec_rel low low' /\ bsame b b').

#[using="Hnotify"] Lemma sb_decode_spec X n (st : sbd_state ptr) (low : dec_state ptr) (b : bits_st ptr) out :
low_decode_ok X n -> dec_depth low = n -> dec_wf low -> bits_ok b ->
keeps X (sb_decode spx_notify unpackM peekM remainingM st low
(speex_decode_n spx_notify unpackM peekM advanceM remainingM n) b out)
(fun r => let '(rc, sl, b') := r in let '(st', low') := sl in
sbd_ptrs st' = sbd_ptrs st /\ dec_rel low low' /\ bsame b b').
Proof.
intros IH Hd Hwf Hok. unfold sb_decode.
destruct (ctl_cases low (CtlSetInnovationSave (out + sbd_frame_size st)) Hwf) as (v1 & low1 & -> & R1).
eapply keeps_bind.
{ apply IH; [| apply R1| exact Hok]. destruct R1 as (_ & _ & C). rewrite C. exact Hd. }
intros [[ret low2] b1] [R2 S1].
destruct (ctl_cases low2 CtlGetDtxStatus ltac:(apply R2)) as (dtx & low3 & -> & R3).
pose proof (dec_rel_trans _ _ _ R1 (dec_rel_trans _ _ _ R2 R3)) as R03.
pose proof (bsame_ok _ _ S1) as Hok1.
destruct (negb (ret =? 0)).
{ apply keeps_ret. split; [reflexivity|]. split; [exact R03| exact S1]. }
eapply keeps_bind with (Q1 := fun sr => let '(st', b') := match sr with inl p => p | inr p => p end in
sbd_ptrs st' = sbd_ptrs st /\ bsame b b').
{ destruct (negb (sbd_encode_submode st =? 0)).
2:{ apply keeps_ret. split; [reflexivity| exact S1]. }
eapply keeps_bind; [apply remainingM_keeps; exact Hok1|]. intros rem ->.
eapply keeps_bind with (Q1 := fun r => bstep 0 b1 (snd r)).
{ destruct (0 <? speex_bits_remaining b1).
- eapply keeps_weaken; [apply peekM_keeps; exact Hok1|]. intros [w b2] [_ H2]. exact H2.
- apply keeps_ret. cbn. apply bstep_refl. exact Hok1. }
intros [wideband b2] H2; cbn in H2.
eapply keeps_bind with (Q1 := fun r => sbd_ptrs (fst r) = sbd_ptrs st /\ bstep 0 b1 (snd r)).
{ destruct (negb (wideband =? 0)).
- eapply keeps_bind; [apply (unpack_consumes2 X b2 1 (bstep_ok _ _ _ H2)); lia|]. intros [w' b3] [_ H3]; cbn in H3.
eapply keeps_bind; [apply (unpack_consumes2 X b3 SB_SUBMODE_BITS (bstep_ok _ _ _ H3)); unfold SB_SUBMODE_BITS; lia|].
intros [id b4] [_ H4]; cbn in H4.
apply keeps_ret. cbn. split; [reflexivity|]. eapply bstep00; [exact H2| eapply bstep00; [exact H3| exact H4]].
- apply keeps_ret. cbn. split; [reflexivity| exact H2]. }
intros [st1 b3] [P1 H3]; cbn in P1, H3.
match goal with |- keeps _ (if ?c then _ else _) _ => destruct c end.
- eapply keeps_bind; [apply keeps_notify; msg_ok_tac|]. intros _ _. apply keeps_ret. split; [exact P1|].
eapply bsame_trans; [exact S1| exact (bstep_bsame _ _ _ H3)].
- apply keeps_ret. split; [exact P1|]. eapply bsame_trans; [exact S1| exact (bstep_bsame _ _ _ H3)]. }
intros [[st1 b2] | [st1 b2]] [P1 S2].
2:{ apply keeps_ret. split; [exact P1|]. split; [exact R03| exact S2]. }
destruct (submode_at (sbm_submodes (sbd_mode st1)) (sbd_submodeID st1)) as [sm|] eqn:Esm.
2:{ apply keeps_ret. split; [rewrite sbd_ptrs_set_first; exact P1|]. split; [exact R03| exact S2]. }
pose proof (sb_submodes_params _ _ _ Esm) as Psm.
destruct (ctl_cases low3 CtlGetPiGain ltac:(apply R3)) as (v4 & low4 & -> & R4).
destruct (ctl_cases low4 CtlGetExc ltac:(apply R4)) as (v5 & low5 & -> & R5).
eapply keeps_bind; [apply lsp_unquant_spec; exact (bsame_ok _ _ S2)|]. intros b3 H3.
eapply keeps_bind; [apply sb_decode_subframes_spec; [exact Psm| exact (bstep_ok _ _ _ H3)]|]. intros b4 H4.
apply keeps_ret. split; [rewrite sbd_ptrs_set_first; exact P1|]. split.
- eapply dec_rel_trans; [exact R03|]. eapply dec_rel_trans; [exact R4| exact R5].
- eapply bsame_trans; [exact S2|]. eapply bstep_bsame. eapply bstep00; [exact H3| exact H4].
Qed.

#[using="Hnotify"] Lemma speex_decode_n_spec X : forall n, low_decode_ok X n.
Proof.
induction n as [|n IH]; intros d b out Hd Hwf Hok.
- destruct d; cbn in Hd; discriminate.
- destruct d as [st | st low]; cbn in Hd; cbn [speex_decode_n].
+ eapply keeps_bind; [apply nb_decode_spec; [exact Hwf| exact Hok]|].
intros [[rc st'] b'] [[Hb Hw] Hs]. apply keeps_ret. split; [|exact Hs]. unfold dec_rel; cbn. rewrite Hb. auto.
+ cbn in Hwf. eapply keeps_bind; [apply sb_decode_spec; [exact IH| lia| exact Hwf| exact Hok]|].
intros [[rc [st' low']] b'] (P & (A & B & C) & S). apply keeps_ret. split; [|exact S].
unfold dec_rel; cbn. rewrite A, P, C. auto.
Qed.

#[using="Hnotify"] Theorem speex_decode_spec X (d : dec_state ptr) (b : bits_st ptr) out : dec_wf d -> bits_ok b ->
keeps X (speex_decode spx_notify unpackM peekM advanceM remainingM d b out)
(fun r => let '(rc, d', b') := r in dec_rel d d' /\ bsame b b').
Proof. intros Hwf Hok. unfold speex_decode. apply speex_decode_n_spec; auto. Qed.

#[using="Hfree"] Lemma free_opt_spec X (o : option ptr) : mspec (own (olist o ++ X)) (free_opt lib_free o) (fun _ => own X).
Proof. destruct o as [p|]; cbn; [apply Hfree| apply mspec_ret; auto]. Qed.

#[using="Hfree"] Lemma speex_decoder_destroy_spec : forall X (d : dec_state ptr),
mspec (own (dec_ptrs d ++ X)) (speex_decoder_destroy lib_free d) (fun _ => own X).
Proof.
intros X d. revert X. induction d as [st | st low IH]; intros X; cbn.
- unfold nb_decoder_destroy. apply Hfree.
- rewrite <- app_assoc. eapply mspec_seq; [apply IH|]. intros _. cbn.
repeat (eapply mspec_seq; [apply Hfree|]; intros _). apply Hfree.
Qed.

Definition init_post (k : nat) X (r : option (dec_state ptr)) : assn St :=
fun s mo => match r with Some d => own (dec_ptrs d ++ X) s mo /\ (dec_wf d /\ (length (dec_ptrs d) <= k)%nat) | None => own X s mo end.

#[using="Type"] Lemma init_post_mono k k' X r s mo : (k <= k')%nat -> init_post k X r s mo -> init_post k' X r s mo.
Proof. intros Hk. unfold init_post. destruct r; [| auto]. intros [H [W L]]. split; [exact H|]. split; [exact W| lia]. Qed.

#[using="Hcal"] Lemma calloc_olist X n m : 0 <= n -> 0 <= m -> n * m < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_calloc n m) (fun r => own (olist r ++ X)).
Proof. intros Hn Hm Hb HR. eapply mspec_post; [apply Hcal; auto|]. intros [p|] s mo H; cbn; exact H. Qed.

#[using="Hcal"] Lemma nb_decoder_init_d_spec X : (length X + 1 <= KROOM)%nat -> mspec (own X) (nb_decoder_init_d lib_calloc) (init_post 1 X).
Proof.
intros HR. unfold nb_decoder_init_d, nb_decoder_init.
eapply mspec_bind with (Q1 := fun r s mo => match r with Some st => own (nb_blk st :: X) s mo /\ st = nb_init_state (nb_blk st) | None => own X s mo end).
{ eapply mspec_bind; [apply Hcal; unfold SIZEOF_DECSTATE, MMAP_THRESHOLD; lia|]. intros [blk|]; apply mspec_ret; intros s mo H; cbn; auto. }
intros [st|]; cbn; apply mspec_ret; intros s mo H; [|exact H]. destruct H as [H E].
split; [exact H|]. cbn. rewrite E. unfold nb_wf, nb_init_state, NB_DEFAULT_SUBMODE; cbn. split; lia.
Qed.

#[using="Hperm"] Lemma own_perm {A} (X Y : list ptr) (m : M St A) Q :
Permutation Y X -> mspec (own Y) m Q -> mspec (own X) m Q.
Proof. intros HP Hm. eapply mspec_pre; [exact Hm|]. intros s mo H. eapply Hperm; [apply Permutation_sym; exact HP| exact H]. Qed.

#[using="Type"] Lemma sbm_sizes_nonneg m : 0 <= sbm_subframeSize m /\ 0 <= sbm_lpcSize m /\ 0 <= Z.quot (sbm_frameSize m) (sbm_subframeSize m).
Proof. destruct m; repeat split; cbv; discriminate. Qed.

Ltac sb_init_fail Rp := apply mspec_munr.

#[using="Hcal Hfree Hperm"] Lemma sb_decoder_init_spec (k : nat) X m low_init :
(forall Y, (length Y + k <= KROOM)%nat -> mspec (own Y) low_init (init_post k Y)) ->
(length X + (k + 9) <= KROOM)%nat ->
mspec (own X) (sb_decoder_init lib_calloc lib_free m low_init) (init_post (k + 9) X).
Proof.
intros Hlow HR. unfold sb_decoder_init.
eapply mspec_bind; [apply Hcal; unfold SIZEOF_SBDECSTATE, MMAP_THRESHOLD; lia|]. intros [blk|].
2:{ apply mspec_ret. intros s mo H. exact H. }
eapply mspec_bind; [apply Hlow; cbn [length]; lia|]. intros [low|]; cbn [init_post].
2:{ apply mspec_munr. }
apply mspec_pure. intros [Hwf Hlen].
destruct (ctl_cases low CtlGetSamplingRate Hwf) as (rate & low1 & E1 & R1). rewrite E1.
destruct (ctl_cases low1 (CtlSetWideband 1) ltac:(apply R1)) as (v2 & low2 & E2 & R2).
cbn beta iota zeta. rewrite E2.
pose proof (dec_rel_trans _ _ _ R1 R2) as (Rp & Rw & Rd).
pose proof (sbm_sizes_nonneg m) as (S1 & S2 & S3).
assert (OL : forall o : option ptr, (length (olist o) <= 1)%nat) by (intros [?|]; cbn; lia).
do 8 (eapply mspec_bind; [apply calloc_olist; [unfold QMF_ORDER; lia| lia| unfold QMF_ORDER, MMAP_THRESHOLD, sbm_lpcSize, sbm_subframeSize, sbm_frameSize; destruct m; cbn; lia|
cbn [length app]; rewrite ?length_app; cbn [length]; repeat match goal with |- context [length (olist ?o)] => pose proof (OL o); generalize dependent (length (olist o)); intros end; lia]|]; intros ?g). cbn beta.
eapply (own_perm _ (dec_ptrs low ++ olist g ++ olist g0 ++ olist g1 ++ olist g2 ++ olist g3 ++ olist g4 ++ olist g5 ++ olist g6 ++ blk :: X));
[perm_solve|].
destruct g as [g|]; [|sb_init_fail Rp]. destruct g0 as [g0|]; [|sb_init_fail Rp]. destruct g1 as [g1|]; [|sb_init_fail Rp].
destruct g2 as [g2|]; [|sb_init_fail Rp]. destruct g3 as [g3|]; [|sb_init_fail Rp]. destruct g4 as [g4|]; [|sb_init_fail Rp].
destruct g5 as [g5|]; [|sb_init_fail Rp]. destruct g6 as [g6|]; [|sb_init_fail Rp].
apply mspec_ret. intros s mo H. cbn [init_post dec_wf dec_ptrs sbd_ptrs]. split; [| split; [exact Rw| rewrite length_app, Rp; cbn [length sbd_ptrs]; lia]].
rewrite Rp. eapply Hperm; [|exact H]. unfold sbd_ptrs. cbn. perm_solve.
Qed.

#[using="Hcal Hfree Hperm"] Theorem speex_decoder_init_spec X m : (length X + 19 <= KROOM)%nat ->
mspec (own X) (speex_decoder_init lib_calloc lib_free m) (init_post 19 X).
Proof.
intros HR. destruct m; cbn [speex_decoder_init].
- eapply mspec_post; [apply nb_decoder_init_d_spec; lia|]. intros r s mo. apply init_post_mono. lia.
- eapply mspec_post; [apply (sb_decoder_init_spec 1); [intros Y HY; apply nb_decoder_init_d_spec; lia| lia]|]. intros r s mo. apply init_post_mono. lia.
- apply (sb_decoder_init_spec 10); [| lia]. intros Y HY. apply (sb_decoder_init_spec 1); [intros Y' HY'; apply nb_decoder_init_d_spec; lia| lia].
Qed.
End DecodeSafe.
