From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_text codec_main_inv
  diginet_personality_of_c text_arg_c check_text_scribble_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The call record of SCRIBBLE_TEXT before the text calls (kind 12, a = the masked u8) and after them
    (kind 9, bytes = what check_text_scribble leaves). *)
Definition k12 (pv dv a : Z) : kcall :=
  mkKcall 12 (fz0 4) pv dv a 0 0 0 (fz0 24) 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0.
Definition k9 (pv dv a : Z) (bs : list byte) : kcall :=
  mkKcall 9 (fz0 4) pv dv a 0 0 0 bs 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0.

(** The record cut around bytes (FP + 0x38, 24 bytes): the 56 bytes before it, from FP, and the 120
    after it, up to in.p. *)
Definition p1 (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
   C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))].
Definition p2 (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

(** The body frame as the two text calls need it: k.bytes, the cursor (in.p, in.n) and text[65] at
    FP + 0xdd each their own range. *)
Lemma rd12_split : forall e m k c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (p1 k) /\
  rw_cells rsegs m (bv_unsigned (e_sp e) + -344) [CB 24 (k_bytes k)] /\
  rw_cells rsegs m (bv_unsigned (e_sp e) + -320) (p2 k) /\
  rw_cells rsegs m (bv_unsigned (e_sp e) + -200)
    [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] /\
  exists tA tj tC,
    rw_cells rsegs m (bv_unsigned (e_sp e) + -184) [CB 5 tA] /\
    rw_cells rsegs m (bv_unsigned (e_sp e) + -179) [CB 65 tj] /\
    rw_cells rsegs m (bv_unsigned (e_sp e) + -114) [CB 10 tC].
Proof.
  intros e m k c rem tl H.
  change (body_cells e k c rem tl) with
    (p1 k ++ [CB 24 (k_bytes k)] ++ p2 k ++
     [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] ++ [CB 80 tl]) in H.
  destruct (rw_cells_app_split _ _ _ _ H) as [H1 H']. clear H.
  change (cells_size (p1 k)) with 56%nat in H'.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 56) with (bv_unsigned (e_sp e) + -344) in H' by lia.
  destruct (rw_cells_app_split _ _ _ _ H') as [H2 H'']. clear H'.
  change (cells_size [CB 24 (k_bytes k)]) with 24%nat in H''.
  replace (bv_unsigned (e_sp e) + -344 + Z.of_nat 24) with (bv_unsigned (e_sp e) + -320) in H'' by lia.
  destruct (rw_cells_app_split _ _ _ _ H'') as [H3 H4]. clear H''.
  change (cells_size (p2 k)) with 120%nat in H4.
  replace (bv_unsigned (e_sp e) + -320 + Z.of_nat 120) with (bv_unsigned (e_sp e) + -200) in H4 by lia.
  destruct (rw_cells_app_split _ _ _ _ H4) as [H5 H6]. clear H4.
  change (cells_size [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)]) with 16%nat in H6.
  replace (bv_unsigned (e_sp e) + -200 + Z.of_nat 16) with (bv_unsigned (e_sp e) + -184) in H6 by lia.
  apply (rw_cells_split_CB rsegs m _ [] 80 tl [] [5; 65; 10]%nat) in H6; [ | reflexivity ].
  change (rw_cells rsegs m (bv_unsigned (e_sp e) + -184)
            ([CB 5 (firstn 5 tl)] ++ [CB 65 (firstn 65 (skipn 5 tl))] ++
             [CB 10 (firstn 10 (skipn 65 (skipn 5 tl)))])) in H6.
  destruct (rw_cells_app_split _ _ _ _ H6) as [H7 H8]. clear H6.
  change (cells_size [CB 5 (firstn 5 tl)]) with 5%nat in H8.
  replace (bv_unsigned (e_sp e) + -184 + Z.of_nat 5) with (bv_unsigned (e_sp e) + -179) in H8 by lia.
  destruct (rw_cells_app_split _ _ _ _ H8) as [H9 H10]. clear H8.
  change (cells_size [CB 65 (firstn 65 (skipn 5 tl))]) with 65%nat in H10.
  replace (bv_unsigned (e_sp e) + -179 + Z.of_nat 65) with (bv_unsigned (e_sp e) + -114) in H10 by lia.
  split; [ exact H1 | ]. split; [ exact H2 | ]. split; [ exact H3 | ]. split; [ exact H5 | ].
  exists (firstn 5 tl), (firstn 65 (skipn 5 tl)), (firstn 10 (skipn 65 (skipn 5 tl))).
  split; [ exact H7 | ]. split; [ exact H9 | exact H10 ].
Qed.

(** And back. *)
Lemma rd12_join : forall e m k c rem tA tj tC,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (p1 k) ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -344) [CB 24 (k_bytes k)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -320) (p2 k) ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -200)
    [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -184) [CB 5 tA] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -179) [CB 65 tj] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -114) [CB 10 tC] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem (tA ++ tj ++ tC)).
Proof.
  intros e m k c rem tA tj tC H1 H2 H3 H5 H7 H9 H10.
  assert (T : rw_cells rsegs m (bv_unsigned (e_sp e) + -184) [CB 80 (tA ++ tj ++ tC)]).
  { assert (J2 : rw_cells rsegs m (bv_unsigned (e_sp e) + -179) ([CB 65 tj] ++ [CB 10 tC])).
    { apply rw_cells_app_join; [ exact H9 | ].
      change (cells_size [CB 65 tj]) with 65%nat.
      replace (bv_unsigned (e_sp e) + -179 + Z.of_nat 65) with (bv_unsigned (e_sp e) + -114) by lia.
      exact H10. }
    assert (J : rw_cells rsegs m (bv_unsigned (e_sp e) + -184) ([CB 5 tA] ++ [CB 65 tj] ++ [CB 10 tC])).
    { apply rw_cells_app_join; [ exact H7 | ].
      change (cells_size [CB 5 tA]) with 5%nat.
      replace (bv_unsigned (e_sp e) + -184 + Z.of_nat 5) with (bv_unsigned (e_sp e) + -179) by lia.
      exact J2. }
    pose proof (rw_cells_merge rsegs m _ [] [CB 5 tA; CB 65 tj; CB 10 tC] [] J) as M.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in M. rewrite app_nil_r in M. exact M. }
  change (body_cells e k c rem (tA ++ tj ++ tC)) with
    (p1 k ++ [CB 24 (k_bytes k)] ++ p2 k ++
     [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] ++ [CB 80 (tA ++ tj ++ tC)]).
  apply rw_cells_app_join; [ exact H1 | ].
  change (cells_size (p1 k)) with 56%nat.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 56) with (bv_unsigned (e_sp e) + -344) by lia.
  apply rw_cells_app_join; [ exact H2 | ].
  change (cells_size [CB 24 (k_bytes k)]) with 24%nat.
  replace (bv_unsigned (e_sp e) + -344 + Z.of_nat 24) with (bv_unsigned (e_sp e) + -320) by lia.
  apply rw_cells_app_join; [ exact H3 | ].
  change (cells_size (p2 k)) with 120%nat.
  replace (bv_unsigned (e_sp e) + -320 + Z.of_nat 120) with (bv_unsigned (e_sp e) + -200) by lia.
  apply rw_cells_app_join; [ exact H5 | ].
  change (cells_size [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)]) with 16%nat.
  replace (bv_unsigned (e_sp e) + -200 + Z.of_nat 16) with (bv_unsigned (e_sp e) + -184) by lia.
  exact T.
Qed.

(** The bytes of a one-block cell list, and its length. *)
Lemma rd12_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[W B] _]. cbn [cells_bytes cbytes cells_wf cell_wf] in W, B.
  rewrite app_nil_r in B. destruct W as [W _]. split; assumption.
Qed.

(** The input bytes from the cursor on. *)
Lemma rd12_bytes_skipn : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
  intros m a bs k H Hk.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H.
  apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma rd12_used_le : forall d, (text_used d <= length d)%nat.
Proof. intros d. unfold text_used, text_len, text_hdr. lia. Qed.

Lemma rd12_pd_range : forall pv dv od, pd_ok pv dv od -> 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64.
Proof. intros pv dv od [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold PERS; lia. Qed.

Lemma rd12_pd_chars : forall pv dv d, pd_ok pv dv (Some d) -> 0 <= d_chars d <= 8.
Proof.
  intros pv dv d [(_ & _ & H) | [(_ & _ & H) | (_ & _ & H)]]; [ discriminate H | .. ];
    injection H as H; subst d; cbv [c24 pc d_chars]; lia.
Qed.

(** k.desk->chars, read at k.desk + 10 in the RELRO tables. *)
Lemma rd12_chars_read : forall m pv dv d, relro_img m -> pd_ok pv dv (Some d) ->
  ov_read_bytes rsegs m (wa (dv + 10)) 1 = Some [b8 (d_chars d)].
Proof.
  intros m pv dv d HR HPD.
  pose proof (desk_bytes_of_pd m pv dv d HR HPD) as B.
  assert (L : Z.of_nat (length (bz [d_dev d; d_strips d; d_chars d; d_counter d])) = 4) by reflexivity.
  pose proof (bytes_at_byte m (dv + 8) _ 2 B ltac:(lia)) as R.
  replace (dv + 8 + 2) with (dv + 10) in R by lia. exact R.
Qed.

Lemma rd12_b8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.

Lemma rd12_chars_reg : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 64 (bv_unsigned (b8 x))) = x.
Proof. intros x Hx. rewrite (rd12_b8_unsigned x Hx). apply unsigned_lit. lia. Qed.

Lemma rd12_zb_bz : forall l, Forall (fun x => 0 <= x < 256) l -> zb (bz l) = l.
Proof.
  intros l H. unfold zb, bz. rewrite map_map.
  transitivity (map (fun x : Z => x) l); [ | apply map_id ].
  apply map_ext_in. intros x Hx. apply rd12_b8_unsigned. rewrite Forall_forall in H. apply H. exact Hx.
Qed.

Lemma rd12_land127 : forall x, 0 <= x -> 0 <= Z.land x 127 < 128.
Proof.
  intros x Hx. rewrite Z.land_comm.
  pose proof (land_lt_pow2 127 x 7 ltac:(change (2 ^ 7) with 128; lia) Hx) as H.
  change (2 ^ 7) with 128 in H. exact H.
Qed.

(** 0x13538 text_arg(&in, text); 0x13544 ld a0 = k.desk; lbu a2 = k.desk->chars;
    check_text_scribble(text, k.bytes, chars); 0x13558 ld s5 = k.p; sw s2 (kind := 9); into ENC9. *)
Lemma rd12_text : text_arg_contract -> check_text_scribble_contract ->
  forall e fuel, env_ok e -> enc9_ok e fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (pv dv a : Z) (d : desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) -> pd_ok pv dv (Some d) -> 0 <= a < 128 -> cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e (k12 pv dv a) c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x13538 m1).
Proof.
  intros CTA CTS e fuel HE EN9 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops
         pv dv a d c rem tl m1 HF HPD Ha HC FR HFR.
  unfold st, body_regs.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof (rd12_pd_range _ _ _ HPD) as [Rpv Rdv].
  pose proof (rd12_pd_chars _ _ _ HPD) as CH.
  destruct HC as (Hc0 & Hr0 & Hcr).
  pose proof (data_of_fr e m1 HE HFR) as DATA.
  assert (DATA' : bytes_at rsegs m1 (bv_unsigned (e_p e) + c) (skipn (Z.to_nat c) (e_data e)))
    by (apply rd12_bytes_skipn; [ exact DATA | lia ]).
  assert (LD : Z.of_nat (length (skipn (Z.to_nat c) (e_data e))) = rem) by (rewrite length_skipn; lia).
  clear DATA.
  remember (skipn (Z.to_nat c) (e_data e)) as dd eqn:Edd. clear Edd.
  pose proof (rd12_used_le dd) as TU.
  destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  destruct (rd12_split e m1 _ c rem tl FR) as (F1 & FB & F2 & FC & tA & tj & tC & T1 & T2 & T3). clear FR.
  unfold p1, k12 in F1. cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta] in F1.
  unfold p2 in F2.
  rewrite <- LD in FC.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  assert (U200 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -200)) = bv_unsigned (e_sp e) + -200)
    by (apply unsigned_lit; lia).
  assert (U179 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -179)) = bv_unsigned (e_sp e) + -179)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
    by (apply unsigned_lit; lia).
  zstep. zstep. zstep.
  unfold text_arg_contract, TEXT_ARG, TEXT_ARG_DEPTH in CTA.
  eapply evt_cut;
    [ eapply CTA with (lo := e_lo e) (p := bv_unsigned (e_p e) + c) (data := dd) (tj := tj)
    | post_call rsegs m1 ].
  { unfold text_arg_pre, TEXT_ARG_DEPTH. rewrite ?USP, ?U200, ?U179.
    split; [ exact FC | ]. split; [ exact DATA' | ]. split; [ exact T2 | ].
    split; [ unfold disj; lia | ]. split; [ unfold disj; lia | ]. split; [ unfold disj; lia | ].
    split; [ lia | ]. split; [ lia | ]. split; [ lia | ].
    split; [ exact HMI | ]. split; [ exact ST | lia ]. }
  rewrite ?USP, ?U200, ?U179 in *.
  try clear DATA'.
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -200) _ |- _ => rename H into FC2 end.
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -179) _ |- _ => rename H into T22 end.
  destruct (rd12_cb_bytes _ _ _ _ T22) as [TBB LTB].
  assert (TB0 : In (b8 0) (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj))
    by (apply in_or_app; right; left; reflexivity).
  remember (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj) as tb eqn:Etb. clear Etb.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rd12_chars_read mm pv dv d (relro_of_munch e mm HE MU) HPD) as RD
  end.
  zstep. zstep. zstep. zstep.
  unfold check_text_scribble_contract, CHECK_TEXT_SCRIBBLE, CHECK_TEXT_SCRIBBLE_DEPTH in CTS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply CTS with (lo := e_lo e) (n := d_chars d) (tb := tb) (cj := fz0 24) | post_call rsegs mm ]
  end.
  { unfold check_text_scribble_pre, CHECK_TEXT_SCRIBBLE_DEPTH. rewrite ?USP, ?U179, ?U344.
    split; [ lia | ].
    split; [ split; [ exact TBB | exact TB0 ] | ].
    split; [ exact FB | ].
    split; [ unfold disj; lia | ].
    split; [ apply rd12_chars_reg; lia | ].
    split; [ lia | ].
    split; [ lia | ]. split; [ lia | ].
    split; [ assumption | ]. split; [ assumption | ]. split; [ lia | ].
    symmetry. apply scribble_agree. }
  rewrite ?USP, ?U179, ?U344 in *.
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -344) _ |- _ => rename H into FB2 end.
  zstep. zstep.
  rewrite <- Z.add_assoc in FC2.
  unfold enc9_ok, st, body_regs in EN9.
  eapply EN9 with (k := k9 pv dv a (bz (scribble_bytes (zb tb) (d_chars d)))) (od := Some d)
                  (c := c + Z.of_nat (text_used dd)) (rem := Z.of_nat (length dd - text_used dd))
                  (tl := tA ++ tb ++ tC).
  - exact HF.
  - reflexivity.
  - exact HPD.
  - unfold rdr_k. cbn [k9 k_kind k_a k_b k_c k_delta k_bytes k_n].
    pose proof (reader_ok_12 (zb tb) a (d_chars d) ltac:(change (2 ^ 32) with 4294967296; lia) ltac:(lia)
                  (bytes_ok_map tb)) as R.
    pose proof R as (_ & _ & _ & _ & _ & RF & _).
    rewrite rd12_zb_bz by exact RF. exact R.
  - reflexivity.
  - reflexivity.
  - unfold cur_ok. lia.
  - exact (rd12_join e _ (k9 pv dv a (bz (scribble_bytes (zb tb) (d_chars d))))
             (c + Z.of_nat (text_used dd)) (Z.of_nat (length dd - text_used dd)) tA tb tC
             F1 FB2 F2 FC2 T1 T22 T3).
  - split; [ exact SV | ]. split; [ eassumption | ]. split; [ exact MU | ]. split; [ exact WM | eassumption ].
Qed.

(** 0x13510 fuzz_u8: ld a0 = in.n; beqz a0 -> 0x13534 (a = 0); else in.p += 1, in.n -= 1,
    a = byte & 0x7f; 0x13534 sw a0 -> k.a. *)
Lemma rd12_u8 : text_arg_contract -> check_text_scribble_contract ->
  forall e fuel, env_ok e -> enc9_ok e fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (pv dv : Z) (d : desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) -> pd_ok pv dv (Some d) -> cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd 12 pv dv) c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x13510 m1).
Proof.
  intros CTA CTS e fuel HE EN9 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops
         pv dv d c rem tl m1 HF HPD HC FR HFR.
  pose proof (rd12_text CTA CTS e fuel HE EN9) as K. unfold st, body_regs in K |- *.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof (rd12_pd_range _ _ _ HPD) as [Rpv Rdv].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  unfold body_cells, k_rd in FR.
  cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
       k_want_rc k_want k_want_len k_want_key k_want_display] in FR.
  zstep. zstep.
  if_cases EZ.
  - zify_cond EZ. subst rem.
    zstep.
    eapply K with (pv := pv) (dv := dv) (a := 0) (d := d) (c := c) (rem := 0) (tl := tl);
      [ exact HF | exact HPD | lia | exact HC | exact FR | ].
    exact (conj SV (conj ST (conj MU (conj WM HMI)))).
  - zify_cond EZ.
    zstep. zstep. zstep. zstep. zstep.
    pose proof (bytes_at_byte _ _ _ c (data_of_munch e _ HE MU) ltac:(lia)) as RB.
    remember (nth (Z.to_nat c) (e_data e) (Z_to_bv 8 0)) as bt eqn:Ebt. clear Ebt.
    zstep. zstep. zstep.
    replace (bv_unsigned (e_p e) + c + 1) with (bv_unsigned (e_p e) + (c + 1)) in FR by lia.
    eapply K with (pv := pv) (dv := dv) (a := Z.land (bv_unsigned bt) 127) (d := d) (c := c + 1)
                  (rem := rem + -1) (tl := tl);
      [ exact HF | exact HPD | apply rd12_land127; apply bv_unsigned_in_range | unfold cur_ok; lia | exact FR | ].
    exact (conj SV (conj ST (conj MU (conj WM HMI)))).
Qed.

(** 0x134f4 bnez s5 (k.p): a NULL k.p takes personality_of(1) and the desk SPEC_C24 (0x1f208), stored
    to k.p and k.desk; then fuzz_u8 at 0x13510. *)
Lemma codec_main_rd12 : S_rd12.
Proof.
  unfold S_rd12. intros CPO CTA CTS e fuel HE EN9.
  pose proof (rd12_u8 CTA CTS e fuel HE EN9) as K. unfold st, body_regs in K.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  change (rd_pc 12) with 0x134f4.
  pose proof (rd12_pd_range _ _ _ HPD) as [Rpv Rdv].
  zstep.
  if_cases EB.
  - zify_cond EB.
    assert (Hd : exists d, od = Some d)
      by (destruct HPD as [(H1 & _ & _) | [(_ & _ & H1) | (_ & _ & H1)]]; [ lia | eauto | eauto ]).
    destruct Hd as [d ->].
    eapply K; [ exact HF | exact HPD | exact HC | exact FR | exact HFR ].
  - zify_cond EB.
    assert (dv = 0 /\ od = None) as [-> ->].
    { destruct HPD as [(_ & H1 & H2) | [(H1 & _ & _) | (H1 & _ & _)]];
        [ split; assumption | unfold PERS in H1; lia | unfold PERS in H1; lia ]. }
    subst pv.
    pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
    pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
    destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
    pose proof ST as [Hlo0 _].
    unfold body_cells, k_rd in FR.
    cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
         k_want_rc k_want k_want_len k_want_key k_want_display] in FR.
    zstep. zstep.
    unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF in CPO.
    eapply evt_cut; [ eapply CPO | ].
    intros ms' (a1x & a2x & ->).
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end.
    match goal with |- context [pers_of ?x] => replace (pers_of x) with PERS by (vm_compute; reflexivity) end.
    zstep. zstep. zstep. zstep.
    eapply K with (pv := PERS) (dv := 0x1f208) (d := c24);
      [ exact HF | right; left; split; [ reflexivity | split; reflexivity ] | exact HC | exact FR | ].
    exact (conj SV (conj ST (conj MU (conj WM HMI)))).
Qed.
