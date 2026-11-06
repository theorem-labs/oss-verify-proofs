From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_main_inv
  codec_main_rdb_lib diginet_jog_encode_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** 0x13bac-0x13bcc: delta composed and stored, diginet_jog_encode(delta, &k.out), j JOIN. *)
Lemma rd4_tail : diginet_jog_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd_cells 4 pv dv inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x13bac m1).
Proof.
  intros CJ e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops inp inn
         pv dv od c rem tl m1 FR HFR HF HPD HC -> ->.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  destruct HFR as (SV & ST & MU & WM & HMI).
  pose proof ST as [Hlo0 _].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  unfold rd_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  unfold LLVM_CODEC_STACK in *.
  do 4 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?x ?y) ?z)] =>
    remember (Z_to_bv 64 (Z.lor (Z.lor x y) z)) as W eqn:EW end.
  clear EW.
  zstep. zstep. zstep. zstep.
  destruct (rw_cells_cut3 _ _ _ 14%nat (CB 32 (fa5 32)) FR eq_refl) as (PRE & OUT & POST). clear FR.
  norm_piece PRE. norm_piece OUT. norm_piece POST.
  replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) in OUT, POST by lia.
  assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  set (dl := bv_swrap 32 (bv_unsigned W)).
  unfold diginet_jog_encode_contract, DIGINET_JOG_ENCODE in CJ.
  call (CJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dl (fa5 32)).
  { unfold diginet_jog_encode_pre. rewrite U276.
    split; [ split; [exact (swrap32_range _) | reflexivity] | ].
    split; [lia|]. split; [exact OUT | exact HMI]. }
  rewrite ?USP, ?U276 in *.
  match goal with H : context [jog_spec dl] |- _ =>
    rewrite (surjective_pairing (jog_spec dl)) in H; cbv beta iota in H; destruct H as [Ea0 OUT2] end.
  rewrite Ea0.
  zstep.
  apply (rw_cells_C4 _ _ _ 52%nat W dl) in PRE; [ | reflexivity | exact (swrap32_mod _) ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  pose proof (rw_cells_join3 _ _ _ _ _ _ _ PRE OUT2 POST) as FJ.
  specialize (FJ ltac:(norm_sizes; lia) ltac:(norm_sizes; lia)).
  set (k := mkKcall 4 (fz0 4) pv dv 0 0 0 dl (fz0 24) 0 0 (fa5 32) (cmd_out (fa5 32) (snd (jog_spec dl)))
                    0 (fz0 24) 0 0 0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FB : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FJ end.
  clear FJ PRE OUT2 POST.
  assert (EK : fst (jog_spec dl) = fst (enc_k k od)) by reflexivity.
  rewrite EK.
  unfold join_ok, st, body_regs in JN.
  eapply JN; [ exact HF | | exact HC | exact FB | exact (conj SV (conj ST (conj MU (conj WM MI)))) ].
  unfold rec_ok. split; [unfold k; cbn; lia|]. split; [exact HPD|]. split.
  { unfold rdr_k, k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
    apply rdr_fz0; try lia; try (intros; discriminate). exact (swrap32_range _). }
  split; reflexivity.
Qed.

Ltac rd4_close Hcur :=
  first [ reflexivity | (unfold cur_ok; lia) | (rewrite Hcur; f_equal; lia) | (f_equal; lia)
        | (rewrite <- Hcur; symmetry; apply Z_to_bv_bv_unsigned) ].

(** 0x13480-0x134f0, 0x13a70-0x13a7c, 0x13ba4-0x13ba8: delta = fuzz_u32 (four fuzz_u8, a missing byte
    reads 0), in.p / in.n advanced by the bytes taken; then the tail. *)
Lemma codec_main_rd4 : S_rd4.
Proof.
  unfold S_rd4. intros CJ e fuel HE JN.
  pose proof (rd4_tail CJ e fuel HE JN) as TL. unfold st, body_regs in TL.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  replace (rd_pc 4) with 0x13480 by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  set (cur := Z_to_bv 64 (bv_unsigned (e_p e) + c)) in FR.
  assert (Hcur : bv_unsigned cur = bv_unsigned (e_p e) + c) by (unfold cur; apply unsigned_lit; lia).
  clearbody cur.
  zstep. zstep.
  if_cases E0.
  { zify_cond E0. do 4 zstep.
    eapply TL with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd4_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 2 zstep.
    eapply TL with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd4_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  if_cases E2.
  { zify_cond E2. do 1 zstep.
    eapply TL with (od := od) (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd4_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte cur c 2. zstep. zstep.
  if_cases E3.
  { zify_cond E3. do 1 zstep.
    eapply TL with (od := od) (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd4_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte cur c 3. zstep. zstep. zstep.
  eapply TL with (od := od) (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd4_close Hcur.
Qed.
