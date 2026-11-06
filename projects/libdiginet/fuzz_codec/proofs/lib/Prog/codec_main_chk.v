From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_cells codec_main_inv
  check_refusal_c check_range_c check_bytes_c LLVMFuzzerTestOneInput_c codec_main_owe_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** check_refusal's premise: a SYSEX record with function 0x70 never has code 0 (codec_agree.refusal). *)
Lemma chk_refusal_ok : forall k od, k_rc k = fst (enc_k k od) ->
  ~ (k_kind k = 11 /\ k_b k = 0x70 /\ k_rc k = 0).
Proof.
  intros k od Hrc (Hk & Hb & H0). rewrite Hrc in H0. unfold enc_k in H0. rewrite Hk, Hb in H0.
  exact (refusal od (k_a k) 0x70 (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k) eq_refl H0).
Qed.

(** check_range's premises: a failed encoder left out as it was (codec_agree.enc_fail_none), and its code
    is owe()'s (codec_agree.agree_all). *)
Lemma chk_range_ok : forall k od, rec_ok k od -> k_rc k = fst (enc_k k od) -> owe_want_ok k od ->
  (k_rc k <> 0 -> k_out k = k_before k) /\ k_rc k = k_want_rc k.
Proof.
  intros k od HR Hrc [Hwrc _].
  pose proof HR as (_ & _ & _ & Hbe & Hout).
  destruct (enc_agree k od HR) as [EA _].
  split.
  - intros Hne. rewrite Hout, Hbe. rewrite Hrc in Hne. unfold enc_k in *.
    rewrite (enc_fail_none _ _ _ _ _ _ _ _ Hne). reflexivity.
  - rewrite Hrc, Hwrc. exact EA.
Qed.

(** check_bytes's premises on code 0: the command the encoder wrote is owe()'s. *)
Lemma chk_bytes_ok : forall k od, rec_ok k od -> k_rc k = fst (enc_k k od) -> owe_want_ok k od -> k_rc k = 0 ->
  k_want_len k = cmd_len (k_out k) /\ k_want_len k <= 24 /\
  firstn (Z.to_nat (k_want_len k)) (k_out k) = firstn (Z.to_nat (k_want_len k)) (k_want k) /\
  cmd_key (k_out k) = k_want_key k /\ cmd_display (k_out k) = k_want_display k.
Proof.
  intros k od HR Hrc [Hwrc Hw] H0.
  pose proof HR as (_ & _ & _ & _ & Hout).
  destruct (enc_agree k od HR) as [EA ES].
  rewrite Hrc in H0. specialize (ES H0). rewrite EA in H0.
  pose proof (owe_k_wf k od HR H0) as W.
  rewrite H0 in Hw. cbn [Z.eqb] in Hw.
  rewrite Hout, ES.
  destruct (snd (owe_k k od)) as [[bs key] dp]. cbv beta iota in Hw.
  destruct Hw as (Hl & Hf & Hkey & Hdp).
  destruct (cmd_out_fields bs key dp W) as (F1 & F2 & F3 & F4).
  unfold cmd_wf in W. destruct W as (W1 & _).
  split; [ rewrite Hl; exact (eq_sym F1) | ].
  split; [ rewrite Hl; lia | ].
  split; [ rewrite Hl, Nat2Z.id, Hf; exact F2 | ].
  split; [ rewrite Hkey; exact F3 | rewrite Hdp; exact F4 ].
Qed.

Ltac fix_cells_addr e :=
  match goal with |- cells_at _ _ ?A _ =>
    replace A with (bv_unsigned (e_sp e) + -384) by (rewrite ?unsigned_lit by lia; lia) end.

(** 0x14808 addi a0, sp, 0x10; jal check_refusal; addi a0, sp, 0x10; jal check_range; lw a0, k.rc;
    bnez a0 -> LATCH; addi a0, sp, 0x10; jal check_bytes; LATCH 0x14828. *)
Lemma codec_main_chk : S_chk.
Proof.
  unfold S_chk. intros CR CG CB e fuel HE LA.
  unfold chk_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HRC HOWE HC FR HFR.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  pose proof (kwf_of k od HREC HRC HOWE) as KWF.
  pose proof (chk_refusal_ok k od HRC) as KREF.
  destruct (chk_range_ok k od HREC HRC HOWE) as [KR1 KR2].
  pose proof (chk_bytes_ok k od HREC HRC HOWE) as KB.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  unfold check_refusal_contract, CHECK_REFUSAL in CR.
  unfold check_range_contract, CHECK_RANGE, CHECK_RANGE_DEPTH in CG.
  unfold check_bytes_contract, CHECK_BYTES, CHECK_BYTES_DEPTH in CB.
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  pose proof KWF as (Kk & Kp & Kd & Ka & Kb & Kc & Kdl & Kn & Krc & Kwrc & Kwl & Kwk & Kwd).
  (* check_refusal *)
  zstep. zstep.
  eapply evt_cut; [ eapply CR with (k := k) | ].
  { unfold check_refusal_pre. split; [ fix_cells_addr e; exact (body_k_at e m1 k c rem tl FR) | ].
    split; [ exact KWF | exact KREF ]. }
  intros ms' (a0x & a1x & a2x & ->).
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
  (* check_range *)
  zstep. zstep.
  eapply evt_cut; [ eapply CG with (k := k) (lo := e_lo e) | post_call rsegs m1 ].
  { unfold check_range_pre. split; [ fix_cells_addr e; exact (body_k_at e m1 k c rem tl FR) | ].
    split; [ exact KWF | ]. rewrite ?unsigned_lit by lia.
    split; [ lia | ]. split; [ exact HMI | ]. split; [ exact ST | ].
    split; [ unfold CHECK_RANGE_DEPTH; rewrite ?USP; lia | ].
    split; [ exact KR1 | exact KR2 ]. }
  rewrite ?USP in *.
  (* lw a0, k.rc; bnez a0 *)
  zstep.
  rewrite (sx32_lit (k_rc k)) by lia.
  zstep.
  if_cases EZ.
  - zify_cond EZ.
    unfold latch_ok, st, body_regs in LA.
    eapply LA with (k := k) (c := c) (rem := rem) (tl := tl);
      [ exact HF | exact HC | exact FR | exact (conj SV (conj POST (conj MU (conj WM MI)))) ].
  - zify_cond EZ.
    assert (R0 : k_rc k = 0).
    { first [ lia | apply mod64_zero; [lia | exact EZ] ]. }
    destruct (KB R0) as (B1 & B2 & B3 & B4 & B5).
    zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply CB with (k := k) (lo := e_lo e) | post_call rsegs mm ] end.
    { unfold check_bytes_pre. split; [ fix_cells_addr e; exact (body_k_at e _ k c rem tl FR) | ].
      split; [ exact KWF | ]. rewrite ?unsigned_lit by lia.
      split; [ lia | ]. split; [ exact MI | ]. split; [ exact POST | ].
      split; [ unfold CHECK_BYTES_DEPTH; rewrite ?USP; lia | ].
      split; [ exact B1 | ]. split; [ exact B2 | ]. split; [ exact B3 | ]. split; [ exact B4 | exact B5 ]. }
    rewrite ?USP in *.
    unfold latch_ok, st, body_regs in LA.
    eapply LA with (k := k) (c := c) (rem := rem) (tl := tl);
      [ exact HF | exact HC | exact FR | refine (conj SV (conj _ (conj MU (conj WM _)))); eassumption ].
Qed.
