From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  diginet_counter_encode_c LLVMFuzzerTestOneInput_c codec_main_enc9.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The frame cut around out (set_out, pre_out, post_out, body_split_out, body_join_out, pre_out_bytes) and
    pd_range are those of ENC9. *)

Lemma land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma enc_k_10 : forall k od, k_kind k = 10 -> enc_k k od = counter_spec od (zb (k_bytes k)) (k_b k mod 256).
Proof. intros k od H. unfold enc_k, enc_of_call. rewrite H. reflexivity. Qed.

(** 0x13c4c andi a2 = a0 & 0xff; mv a0, s5; addi a1 = &k.bytes; addi a3 = &k.out; jal diginet_counter_encode;
    0x13c60 j JOIN. *)
Lemma codec_main_enc10 : S_enc10.
Proof.
  unfold S_enc10. intros CC e fuel HE JN.
  unfold enc10_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops k od c rem tl m1
         HF HK10 HPD HRD HB HO HC FR HFR.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (pd_range _ _ _ HPD) as [Rp Rd].
  pose proof (relro_of_fr e m1 HE HFR) as HR.
  pose proof (pers_arg_of_pd m1 _ _ _ HR HPD) as PA. clear HR.
  pose proof HRD as (_ & Hb & _ & _ & HL & _ & _ & _ & Hb10 & _).
  specialize (Hb10 HK10).
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
  assert (UB : bv_unsigned (Z_to_bv 64 (k_b k)) = k_b k) by (apply unsigned_lit; lia).
  destruct (counter_spec od (zb (k_bytes k)) (k_b k mod 256)) as [rc o] eqn:ES.
  zstep. zstep. zstep. zstep. zstep.
  unfold diginet_counter_encode_contract, DIGINET_COUNTER_ENCODE, DIGINET_COUNTER_ENCODE_DEPTH in CC.
  eapply evt_cut;
    [ eapply CC with (lo := e_lo e) (pd := od) (dots := k_b k mod 256) (sg := k_bytes k) (before := k_out k)
    | post_call rsegs m1 ].
  { unfold diginet_counter_encode_pre, DIGINET_COUNTER_ENCODE_DEPTH.
    rewrite ?USP, ?U344, ?U276, ?UP, ?UB.
    split; [ exact PA | ].
    split; [ intros d Hd; subst od; apply (pers_disj e (k_p k) (k_desk k) d); [exact HE | exact HPD | lia | lia] | ].
    split; [ intros d Hd; subst od; apply (pers_disj e (k_p k) (k_desk k) d); [exact HE | exact HPD | lia | lia] | ].
    split; [ lia | ].
    split; [ exact BB | ].
    split; [ rewrite LB; lia | ].
    split; [ split; [ change (2 ^ 8) with 256; apply Z.mod_pos_bound; lia | f_equal; apply land255 ] | ].
    split; [ lia | ].
    split; [ exact F2 | ].
    split; [ lia | ]. split; [ lia | ].
    split; [ exact HMI | ]. split; [ exact ST | lia ]. }
  rewrite ?USP, ?U344, ?U276 in *.
  rewrite ES in POST. destruct POST as [HA0 HOUT]. subst.
  zstep.
  rewrite HO in HOUT.
  assert (EK : enc_k (set_out k (cmd_out (fa5 32) o)) od = (rc, o))
    by (rewrite (enc_k_10 (set_out k (cmd_out (fa5 32) o)) od HK10); exact ES).
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
