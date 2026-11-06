From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  diginet_scribble_encode_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The definitions and lemmas up to codec_main_enc9 serve ENC10 too (codec_main_enc10.v imports them).
    k with out replaced (what the encoder call writes). *)
Definition set_out (k : kcall) (o : list byte) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) o
          (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

(** The body frame cut around out (FP + 0x7c, 32 bytes). *)
Definition pre_out (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
   C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)].
Definition post_out (e : env) (k : kcall) (c rem : Z) (tl : list byte) : list cell :=
  [C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k));
   C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl].

Lemma body_split_out : forall e m1 k c rem tl,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (pre_out k) /\
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -276) [CB 32 (k_out k)] /\
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -244) (post_out e k c rem tl).
Proof.
  intros e m1 k c rem tl H.
  change (body_cells e k c rem tl) with (pre_out k ++ [CB 32 (k_out k)] ++ post_out e k c rem tl) in H.
  destruct (rw_cells_app_split _ _ _ _ H) as [H1 H23].
  destruct (rw_cells_app_split _ _ _ _ H23) as [H2 H3].
  change (cells_size (pre_out k)) with 124%nat in H23, H2, H3.
  change (cells_size [CB 32 (k_out k)]) with 32%nat in H3.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 124) with (bv_unsigned (e_sp e) + -276) in H2, H3 by lia.
  replace (bv_unsigned (e_sp e) + -276 + Z.of_nat 32) with (bv_unsigned (e_sp e) + -244) in H3 by lia.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma body_join_out : forall e m1 k c rem tl o,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (pre_out k) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -276) [CB 32 o] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -244) (post_out e k c rem tl) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e (set_out k o) c rem tl).
Proof.
  intros e m1 k c rem tl o H1 H2 H3.
  change (body_cells e (set_out k o) c rem tl) with (pre_out k ++ [CB 32 o] ++ post_out e k c rem tl).
  apply rw_cells_app_join; [exact H1|].
  change (cells_size (pre_out k)) with 124%nat.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 124) with (bv_unsigned (e_sp e) + -276) by lia.
  apply rw_cells_app_join; [exact H2|].
  change (cells_size [CB 32 o]) with 32%nat.
  replace (bv_unsigned (e_sp e) + -276 + Z.of_nat 32) with (bv_unsigned (e_sp e) + -244) by lia.
  exact H3.
Qed.

(** The 24 bytes of k.bytes at FP + 0x38. *)
Lemma pre_out_bytes : forall e m1 k,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (pre_out k) ->
  bytes_at rsegs m1 (bv_unsigned (e_sp e) + -344) (k_bytes k).
Proof.
  intros e m1 k H.
  change (pre_out k) with
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))] ++
     [CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)]) in H.
  apply rw_cells_app_split in H. destruct H as [_ [[_ B] _]].
  cbn [cells_size csize Nat.add cells_bytes cbytes] in B.
  apply bytes_at_app in B. destruct B as [B _].
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 56) with (bv_unsigned (e_sp e) + -344) in B by lia.
  exact B.
Qed.

Lemma pd_range : forall pv dv od, pd_ok pv dv od -> 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64.
Proof. intros pv dv od [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold PERS; lia. Qed.

Lemma pd_some_chars : forall pv dv d, pd_ok pv dv (Some d) -> d_chars d <= 8.
Proof.
  intros pv dv d [(_ & _ & H) | [(_ & _ & H) | (_ & _ & H)]]; [discriminate H | ..];
    injection H as H; subst d; cbv [c24 pc d_chars]; lia.
Qed.

(** lw of a u32 field: the sign-extended word is the register form arg_u32 names. *)
Lemma sx32_u32 : forall v, 0 <= v < 2 ^ 32 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (s32 v).
Proof.
  intros v Hv. unfold sx32, s32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota.
  - rewrite Z.mod_small by lia. lia.
  - replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma enc_k_9 : forall k od, k_kind k = 9 -> enc_k k od = scribble_spec od (k_a k) (zb (k_bytes k)).
Proof. intros k od H. unfold enc_k, enc_of_call. rewrite H. reflexivity. Qed.

(** 0x13560 lw a1, k.a; mv a0, s5; addi a2 = &k.bytes; addi a3 = &k.out; jal diginet_scribble_encode;
    0x13574 j JOIN. *)
Lemma codec_main_enc9 : S_enc9.
Proof.
  unfold S_enc9. intros CS e fuel HE JN.
  unfold enc9_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops k od c rem tl m1
         HF HK9 HPD HRD HB HO HC FR HFR.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (pd_range _ _ _ HPD) as [Rp Rd].
  pose proof (relro_of_fr e m1 HE HFR) as HR.
  pose proof (pers_arg_of_pd m1 _ _ _ HR HPD) as PA. clear HR.
  pose proof HRD as (Ha & _ & _ & _ & HL & _).
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in HL; rewrite length_map in HL; exact HL).
  clear HL.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  destruct (body_split_out e m1 k c rem tl FR) as [F1 [F2 F3]]. clear FR.
  pose proof (pre_out_bytes e m1 k F1) as BB.
  unfold pre_out in F1. unfold post_out in F3.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
    by (apply unsigned_lit; lia).
  assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 (k_p k)) = k_p k) by (apply unsigned_lit; lia).
  destruct (scribble_spec od (k_a k) (zb (k_bytes k))) as [rc o] eqn:ES.
  zstep. zstep. zstep. zstep. zstep.
  unfold diginet_scribble_encode_contract, DIGINET_SCRIBBLE_ENCODE, DIGINET_SCRIBBLE_ENCODE_DEPTH in CS.
  eapply evt_cut;
    [ eapply CS with (lo := e_lo e) (pd := od) (addr := k_a k) (cs := k_bytes k) (before := k_out k)
    | post_call rsegs m1 ].
  { unfold diginet_scribble_encode_pre, DIGINET_SCRIBBLE_ENCODE_DEPTH.
    rewrite ?USP, ?U344, ?U276, ?UP.
    split; [ exact PA | ].
    split; [ intros d Hd; subst od; apply (pers_disj e (k_p k) (k_desk k) d); [exact HE | exact HPD | lia | lia] | ].
    split; [ intros d Hd; subst od; pose proof (pd_some_chars _ _ _ HPD); split; [ assumption | rewrite LB; lia ] | ].
    split; [ split; [ lia | apply sx32_u32; lia ] | ].
    split; [ lia | ].
    split; [ exact BB | ].
    split; [ lia | ].
    split; [ exact F2 | ].
    split; [ lia | ]. split; [ lia | ].
    split; [ exact HMI | ]. split; [ exact ST | lia ]. }
  rewrite ?USP, ?U344, ?U276 in *.
  rewrite ES in POST. destruct POST as [HA0 HOUT]. subst.
  zstep.
  rewrite HO in HOUT.
  assert (EK : enc_k (set_out k (cmd_out (fa5 32) o)) od = (rc, o))
    by (rewrite (enc_k_9 (set_out k (cmd_out (fa5 32) o)) od HK9); exact ES).
  replace (Z_to_bv 64 rc) with (Z_to_bv 64 (fst (enc_k (set_out k (cmd_out (fa5 32) o)) od)))
    by (rewrite EK; reflexivity).
  pose proof (body_join_out e _ k c rem tl (cmd_out (fa5 32) o) F1 HOUT F3) as FB.
  unfold join_ok, st, body_regs in JN.
  eapply JN with (k := set_out k (cmd_out (fa5 32) o)) (od := od) (c := c) (rem := rem) (tl := tl);
    [ exact HF | | exact HC | exact FB | ].
  - unfold rec_ok. split; [ change (0 <= k_kind k <= 11); lia | ].
    split; [ exact HPD | ]. split; [ exact HRD | ]. split; [ exact HB | ].
    rewrite EK. reflexivity.
  - split; [ exact SV | ]. split; [ eassumption | ]. split; [ exact MU | ]. split; [ exact WM | eassumption ].
Qed.
